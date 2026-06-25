#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

static constexpr uint32_t P=101;
struct E { uint8_t a,b; };
static uint8_t invp[101];
static inline E add(E x,E y){uint16_t a=x.a+y.a,b=x.b+y.b;return {(uint8_t)(a>=P?a-P:a),(uint8_t)(b>=P?b-P:b)};}
static inline E sub(E x,E y){return {(uint8_t)(x.a>=y.a?x.a-y.a:x.a+P-y.a),(uint8_t)(x.b>=y.b?x.b-y.b:x.b+P-y.b)};}
static inline E mul(E x,E y){uint32_t a=(uint32_t)x.a*y.a+2u*(uint32_t)x.b*y.b;uint32_t b=(uint32_t)x.a*y.b+(uint32_t)x.b*y.a;return {(uint8_t)(a%P),(uint8_t)(b%P)};}
static inline bool zero(E x){return x.a==0&&x.b==0;}
static inline E inv(E x){uint32_t d=((uint32_t)x.a*x.a+P-2u*(uint32_t)x.b*x.b%P)%P;if(!d)throw std::runtime_error("inverse zero");uint32_t q=invp[d];return {(uint8_t)(x.a*q%P),(uint8_t)(x.b?((P-x.b)*q%P):0)};}
static inline E divide(E x,E y){return mul(x,inv(y));}

struct Mat{uint32_t n;std::vector<uint64_t>rp;std::vector<uint32_t>ci;std::vector<uint8_t>a;};
static Mat loadmat(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("open "+fn);char m[8];uint32_t p,z;uint64_t e;Mat A;f.read(m,8);f.read((char*)&A.n,4);f.read((char*)&p,4);f.read((char*)&e,8);f.read((char*)&z,4);f.read((char*)&z,4);A.rp.resize(A.n+1);A.ci.resize(e);A.a.resize(e);f.read((char*)A.rp.data(),8*(A.n+1));f.read((char*)A.ci.data(),4*e);f.read((char*)A.a.data(),e);if(std::string(m,6)!="KMC201"||p!=101||!f)throw std::runtime_error("bad matrix");return A;}
struct Eig{uint32_t n,pivot;std::vector<uint8_t>v;};
static Eig loadeig(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("open eig");char m[8];Eig e;f.read(m,8);f.read((char*)&e.n,4);f.read((char*)&e.pivot,4);e.v.resize(e.n);f.read((char*)e.v.data(),e.n);if(std::string(m,6)!="KMV101"||!f)throw std::runtime_error("bad eig");return e;}
static uint64_t hashfile(const std::string&fn){std::ifstream f(fn,std::ios::binary);uint64_t h=1469598103934665603ULL;char b[65536];while(f){f.read(b,sizeof b);auto n=f.gcount();for(std::streamsize i=0;i<n;i++){h^=(uint8_t)b[i];h*=1099511628211ULL;}}return h;}
static uint64_t sm64(uint64_t&s){uint64_t z=(s+=0x9e3779b97f4a7c15ULL);z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31);}

struct Op{Mat A;bool border=false;Eig eig;uint32_t n=0;
 void apply(const std::vector<E>&x,std::vector<E>&y)const{
#pragma omp parallel for schedule(static)
  for(int64_t ii=0;ii<(int64_t)A.n;ii++){uint32_t i=ii;uint64_t sr=0,si=0;for(uint64_t k=A.rp[i];k<A.rp[i+1];k++){uint32_t c=A.a[k],j=A.ci[k];sr+=c*x[j].a;si+=c*x[j].b;}int ar=(int)(sr%P)-50*(int)x[i].a;int ai=(int)(si%P)-50*(int)x[i].b;if(border){ar+=(int)eig.v[i]*x[A.n].a;ai+=(int)eig.v[i]*x[A.n].b;}ar%=101;ai%=101;if(ar<0)ar+=101;if(ai<0)ai+=101;y[i]={(uint8_t)ar,(uint8_t)ai};}
  if(border)y[A.n]=x[eig.pivot];
 }
};

struct BMResult{uint32_t L;std::vector<E>C;};
static BMResult berlekamp_massey(const std::vector<E>&s,size_t used){
 std::vector<uint8_t>Cr(used+1),Ci(used+1),Br(used+1),Bi(used+1),Tr(used+1),Ti(used+1);Cr[0]=Br[0]=1;size_t clen=1,blen=1,L=0,m=1;E b{1,0};
 for(size_t n=0;n<used;n++){
  uint64_t dr=s[n].a,di=s[n].b;
  for(size_t i=1;i<=L;i++){size_t j=n-i;dr+=(uint32_t)Cr[i]*s[j].a+2u*(uint32_t)Ci[i]*s[j].b;di+=(uint32_t)Cr[i]*s[j].b+(uint32_t)Ci[i]*s[j].a;}
  E d{(uint8_t)(dr%P),(uint8_t)(di%P)};
  if(zero(d)){m++;continue;}
  bool jump=(2*L<=n);size_t old_clen=clen;if(jump){std::copy(Cr.begin(),Cr.begin()+clen,Tr.begin());std::copy(Ci.begin(),Ci.begin()+clen,Ti.begin());}
  E coef=divide(d,b);size_t need=blen+m;if(need>clen){std::fill(Cr.begin()+clen,Cr.begin()+need,0);std::fill(Ci.begin()+clen,Ci.begin()+need,0);clen=need;}
  for(size_t j=0;j<blen;j++){uint32_t pr=(uint32_t)coef.a*Br[j]+2u*(uint32_t)coef.b*Bi[j];uint32_t pi=(uint32_t)coef.a*Bi[j]+(uint32_t)coef.b*Br[j];uint8_t rr=pr%P,ri=pi%P;size_t q=j+m;Cr[q]=(Cr[q]>=rr?Cr[q]-rr:Cr[q]+P-rr);Ci[q]=(Ci[q]>=ri?Ci[q]-ri:Ci[q]+P-ri);}
  if(jump){size_t oldL=L;L=n+1-L;std::copy(Tr.begin(),Tr.begin()+old_clen,Br.begin());std::copy(Ti.begin(),Ti.begin()+old_clen,Bi.begin());blen=old_clen;b=d;m=1;(void)oldL;}else m++;
 }
 while(clen>1&&Cr[clen-1]==0&&Ci[clen-1]==0)clen--;
 if(clen!=L+1)throw std::runtime_error("BM internal degree mismatch "+std::to_string(clen-1)+" vs "+std::to_string(L));
 std::vector<E>C(clen);for(size_t i=0;i<clen;i++)C[i]={Cr[i],Ci[i]};return {(uint32_t)L,std::move(C)};
}
static size_t recurrence_bad(const std::vector<E>&s,const BMResult&r,size_t begin){size_t bad=0;for(size_t n=std::max<size_t>(r.L,begin);n<s.size();n++){uint64_t dr=s[n].a,di=s[n].b;for(size_t i=1;i<=r.L;i++){E c=r.C[i],q=s[n-i];dr+=(uint32_t)c.a*q.a+2u*(uint32_t)c.b*q.b;di+=(uint32_t)c.a*q.b+(uint32_t)c.b*q.a;}if(dr%P||di%P)bad++;}return bad;}
#pragma pack(push,1)
struct Header{char magic[8];uint32_t version,prime,nonresidue,n,lambda,border,pivot,terms,bm_terms,degree;uint64_t seed,matrix_hash,eigen_hash;};
#pragma pack(pop)
static void savecert(const std::string&fn,const Header&h,const std::vector<E>&s,const BMResult&r){std::ofstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("write cert");f.write((char*)&h,sizeof h);f.write((char*)s.data(),2*s.size());f.write((char*)r.C.data(),2*r.C.size());if(!f)throw std::runtime_error("write cert failed");}
int main(int ac,char**av){for(int a=1;a<101;a++)for(int b=1;b<101;b++)if(a*b%101==1){invp[a]=b;break;}if(ac<5){std::cerr<<"usage MATRIX normal|border SEED OUT [EIG]\n";return 1;}std::string mfn=av[1],mode=av[2],out=av[4],efn;uint64_t seed=strtoull(av[3],0,0);Op op;op.A=loadmat(mfn);op.border=mode=="border";if(mode!="normal"&&!op.border)throw std::runtime_error("mode");if(op.border){if(ac<6)throw std::runtime_error("eig missing");efn=av[5];op.eig=loadeig(efn);if(op.eig.n!=op.A.n||op.eig.v[op.eig.pivot]==0)throw std::runtime_error("eig dimensions");}
 op.n=op.A.n+op.border;uint32_t N=op.n,bmterms=2*N,terms=bmterms+32;std::vector<E>dR(N),dL(N),u(N),x(N),dx(N),y(N),s;uint64_t rng=seed;for(uint32_t i=0;i<N;i++){do{dR[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};}while(zero(dR[i]));do{dL[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};}while(zero(dL[i]));u[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};x[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};}s.reserve(terms);auto t0=std::chrono::steady_clock::now();for(uint32_t k=0;k<terms;k++){uint64_t sr=0,si=0;for(uint32_t i=0;i<N;i++){sr+=(uint32_t)u[i].a*x[i].a+2u*(uint32_t)u[i].b*x[i].b;si+=(uint32_t)u[i].a*x[i].b+(uint32_t)u[i].b*x[i].a;}s.push_back({(uint8_t)(sr%P),(uint8_t)(si%P)});
#pragma omp parallel for schedule(static)
  for(int64_t i=0;i<(int64_t)N;i++)dx[i]=mul(dR[i],x[i]);op.apply(dx,y);
#pragma omp parallel for schedule(static)
  for(int64_t i=0;i<(int64_t)N;i++)y[i]=mul(dL[i],y[i]);x.swap(y);if((k+1)%5000==0)std::cerr<<"moments "<<k+1<<"/"<<terms<<" sec "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count()<<"\n";}
 auto tb=std::chrono::steady_clock::now();auto r=berlekamp_massey(s,bmterms);double bmsec=std::chrono::duration<double>(std::chrono::steady_clock::now()-tb).count();size_t bad=recurrence_bad(s,r,bmterms);E constant=r.C[r.L];std::cout<<"n "<<N<<" degree "<<r.L<<" constant "<<(int)constant.a<<"+"<<(int)constant.b<<"t extra_bad "<<bad<<" bm_sec "<<bmsec<<" seed "<<seed<<"\n";
 Header h{};memcpy(h.magic,"KMW2CERT",8);h.version=2;h.prime=101;h.nonresidue=2;h.n=N;h.lambda=50;h.border=op.border;h.pivot=op.border?op.eig.pivot:UINT32_MAX;h.terms=terms;h.bm_terms=bmterms;h.degree=r.L;h.seed=seed;h.matrix_hash=hashfile(mfn);h.eigen_hash=op.border?hashfile(efn):0;savecert(out,h,s,r);return (r.L==N&&!zero(constant)&&bad==0)?0:2;}
