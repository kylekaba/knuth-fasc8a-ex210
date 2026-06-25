#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <unordered_map>
#ifdef _OPENMP
#include <omp.h>
#endif

struct Mat{uint32_t n;std::vector<uint64_t>rp;std::vector<uint32_t>ci;std::vector<uint8_t>a;std::vector<uint64_t>rep;};
static Mat load(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("open "+fn);char magic[8];uint32_t p,z1,z2;uint64_t e;Mat A;f.read(magic,8);f.read((char*)&A.n,4);f.read((char*)&p,4);f.read((char*)&e,8);f.read((char*)&z1,4);f.read((char*)&z2,4);if(std::string(magic,6)!="KMC201"||p!=101)throw std::runtime_error("bad matrix");A.rp.resize(A.n+1);A.ci.resize(e);A.a.resize(e);A.rep.resize(A.n);f.read((char*)A.rp.data(),8*(A.n+1));f.read((char*)A.ci.data(),4*e);f.read((char*)A.a.data(),e);f.read((char*)A.rep.data(),8*A.n);if(!f)throw std::runtime_error("truncated");return A;}
static std::vector<uint8_t> loadvec(const std::string&fn){std::ifstream f(fn,std::ios::binary);uint32_t n;f.read((char*)&n,4);std::vector<uint8_t>v(n);f.read((char*)v.data(),n);return v;}
static void savevec(const std::string&fn,const std::vector<uint8_t>&v,uint32_t pivot){std::ofstream f(fn,std::ios::binary);const char m[8]={'K','M','V','1','0','1',0,0};uint32_t n=v.size();f.write(m,8);f.write((char*)&n,4);f.write((char*)&pivot,4);f.write((char*)v.data(),v.size());}
static inline void mv(const Mat&A,const std::vector<uint8_t>&x,std::vector<uint8_t>&y){
#pragma omp parallel for schedule(static)
    for(int64_t i=0;i<(int64_t)A.n;i++){uint32_t s=0;for(uint64_t k=A.rp[i];k<A.rp[i+1];k++)s+=(uint32_t)A.a[k]*x[A.ci[k]];y[i]=(uint8_t)(s%101);}
}
static inline void mv2(const Mat&A,const std::vector<uint8_t>&x,std::vector<uint8_t>&tmp,std::vector<uint8_t>&y){mv(A,x,tmp);mv(A,tmp,y);}
static uint8_t inv101(uint8_t a){for(uint32_t b=1;b<101;b++)if((uint32_t)a*b%101==1)return b;throw std::runtime_error("inverse zero");}
static std::vector<uint32_t> minpoly(const std::vector<uint8_t>&seq){
    size_t N=seq.size(),L=0,m=1,clen=1,blen=1;uint8_t b=1;
    std::vector<uint8_t>C(N+1),B(N+1),T(N+1);C[0]=B[0]=1;
    for(size_t n=0;n<N;n++){
        uint64_t d=seq[n];for(size_t i=1;i<=L;i++)d+=(uint32_t)C[i]*seq[n-i];uint8_t dd=d%101;
        if(dd==0){m++;continue;}bool jump=2*L<=n;size_t oldclen=clen;if(jump)std::copy(C.begin(),C.begin()+clen,T.begin());
        uint8_t coef=(uint32_t)dd*inv101(b)%101;size_t need=blen+m;if(need>clen){std::fill(C.begin()+clen,C.begin()+need,0);clen=need;}
        for(size_t j=0;j<blen;j++){uint8_t q=(uint32_t)coef*B[j]%101;size_t k=j+m;C[k]=(C[k]>=q?C[k]-q:C[k]+101-q);}
        if(jump){L=n+1-L;std::copy(T.begin(),T.begin()+oldclen,B.begin());blen=oldclen;b=dd;m=1;}else m++;
    }
    // Convert connection C[0]+C[1]E^{-1}+... to the monic ascending annihilator f(x).
    // C[L] may vanish when f has zero constant coefficient, so preserve the formal length L+1.
    std::vector<uint32_t>f(L+1);for(size_t i=0;i<=L;i++){size_t j=L-i;f[i]=(j<clen?C[j]:0);}return f;
}
static uint32_t peval(const std::vector<uint32_t>&c,uint32_t x){uint32_t v=0;for(auto it=c.rbegin();it!=c.rend();++it)v=(v*x+*it)%101;return v;}
static std::vector<uint8_t> poly_apply_M(const Mat&A,const std::vector<uint32_t>&c,const std::vector<uint8_t>&b){std::vector<uint8_t>v(A.n,0),t(A.n),w(A.n);for(auto it=c.rbegin();it!=c.rend();++it){mv2(A,v,t,w);v.swap(w);uint32_t q=*it%101;if(q)for(uint32_t i=0;i<A.n;i++)v[i]=(v[i]+q*b[i])%101;}return v;}
static uint32_t invmod(uint32_t x){for(uint32_t y=1;y<101;y++)if(x*y%101==1)return y;throw std::runtime_error("no inverse");}
int main(int argc,char**argv){std::string dir=argc>1?argv[1]:"data";int terms=argc>2?std::atoi(argv[2]):9000;uint64_t probe_seed=argc>3?std::strtoull(argv[3],nullptr,0):0;Mat A=load(dir+"/blocks/Tall_plus.kmc");auto beta=loadvec(dir+"/blocks/Tall_finish.vec");if(beta.size()!=A.n)throw std::runtime_error("size");uint32_t bare=0;
    std::vector<uint8_t> probe(A.n,0); if(probe_seed){uint64_t z=probe_seed;for(uint32_t i=0;i<A.n;i++){z+=0x9e3779b97f4a7c15ULL;uint64_t q=z;q=(q^(q>>30))*0xbf58476d1ce4e5b9ULL;q=(q^(q>>27))*0x94d049bb133111ebULL;q^=q>>31;probe[i]=q%101;}}
    std::vector<uint8_t>x=beta,t(A.n),y(A.n),seq;seq.reserve(terms);auto t0=std::chrono::steady_clock::now();
    for(int k=0;k<terms;k++){uint32_t sk=0;if(probe_seed){uint64_t ss=0;for(uint32_t i=0;i<A.n;i++){ss+=(uint32_t)probe[i]*x[i];if(ss>(1ULL<<60))ss%=101;}sk=ss%101;}else sk=x[bare];seq.push_back(sk);mv2(A,x,t,y);x.swap(y);if((k+1)%1000==0)std::cerr<<"terms "<<k+1<<" sec "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<<"\n";}
    auto c=minpoly(seq);std::cout<<"degree "<<c.size()-1<<" c0 "<<c[0]<<" f76 "<<peval(c,76)<<"\n";
    std::ofstream pf(dir+"/certs/closed_vector_minpoly_p101.txt");if(!pf)throw std::runtime_error("write minpoly");for(auto q:c)pf<<q<<"\n";
    auto ann=poly_apply_M(A,c,beta);size_t nz=0;for(auto q:ann)nz+=(q!=0);std::cout<<"F(M)beta nonzeros "<<nz<<"\n";if(nz) return 2;
    // Synthetic division F=(x-76)g, ascending coefficients.
    size_t d=c.size()-1;if(d<1||peval(c,76)!=0)throw std::runtime_error("factor absent");std::vector<uint32_t>g(d);g[d-1]=c[d];for(size_t kk=d-1;kk>0;--kk)g[kk-1]=(c[kk]+76*g[kk])%101;if(c[0]!=(101-(76*g[0])%101)%101)throw std::runtime_error("division check");
    {std::ofstream gf(dir+"/certs/visible76.poly",std::ios::binary);if(!gf)throw std::runtime_error("write visible polynomial");const char mm[8]={'K','M','P','1','0','1',0,0};uint32_t glen=g.size();gf.write(mm,8);gf.write((char*)&glen,4);std::vector<uint8_t>gg(glen);for(uint32_t i=0;i<glen;i++)gg[i]=g[i];gf.write((char*)gg.data(),gg.size());}
    auto r=poly_apply_M(A,g,beta);mv2(A,r,t,y);nz=0;for(uint32_t i=0;i<A.n;i++)if(y[i]!=(uint8_t)(76*r[i]%101))nz++;std::cout<<"(M-76)r nonzeros "<<nz<<" r_bare "<<(int)r[bare]<<"\n";if(nz||r[bare]==0)return 3;
    // v=r+50^{-1} A r is a 50-eigenvector.
    mv(A,r,t);uint32_t inv50=invmod(50);std::vector<uint8_t>v(A.n);for(uint32_t i=0;i<A.n;i++)v[i]=(r[i]+inv50*t[i])%101;mv(A,v,y);nz=0;for(uint32_t i=0;i<A.n;i++)if(y[i]!=(uint8_t)(50*v[i]%101))nz++;std::cout<<"(A-50)v nonzeros "<<nz<<" v_bare "<<(int)v[bare]<<"\n";if(nz||v[bare]==0)return 4;
    // Map by representative global vertex into Trel_plus.
    Mat R=load(dir+"/blocks/Trel_plus.kmc");std::unordered_map<uint64_t,uint32_t>pos;pos.reserve(A.n*2);for(uint32_t i=0;i<A.n;i++)pos.emplace(A.rep[i],i);std::vector<uint8_t>vr(R.n);uint32_t pivot=UINT32_MAX;for(uint32_t i=0;i<R.n;i++){auto it=pos.find(R.rep[i]);if(it==pos.end())throw std::runtime_error("rep map");vr[i]=v[it->second];if(vr[i]&&pivot==UINT32_MAX)pivot=i;}
    // redo with correctly sized vector
    std::vector<uint8_t>yr(R.n);mv(R,vr,yr);nz=0;for(uint32_t i=0;i<R.n;i++)if(yr[i]!=(uint8_t)(50*vr[i]%101))nz++;
    std::cout<<"restricted eigenvector nonzeros residual "<<nz<<" pivot "<<pivot<<" value "<<(int)vr[pivot]<<"\n";if(nz||pivot==UINT32_MAX)return 5;
    savevec(dir+"/certs/Trel_plus_eigen50.vec",vr,pivot);
    return 0;
}
