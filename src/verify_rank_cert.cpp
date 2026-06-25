#include <algorithm>
#include <cstdint>
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
struct E{uint8_t a,b;};static uint8_t invp[101];
static inline bool zero(E x){return x.a==0&&x.b==0;}
static inline E mul(E x,E y){return {(uint8_t)(((uint32_t)x.a*y.a+2u*(uint32_t)x.b*y.b)%P),(uint8_t)(((uint32_t)x.a*y.b+(uint32_t)x.b*y.a)%P)};}
static inline E inv(E x){uint32_t d=((uint32_t)x.a*x.a+P-2u*(uint32_t)x.b*x.b%P)%P;if(!d)throw std::runtime_error("inverse zero");uint32_t q=invp[d];return {(uint8_t)(x.a*q%P),(uint8_t)(x.b?((P-x.b)*q%P):0)};}
static inline E divide(E x,E y){return mul(x,inv(y));}
struct Mat{uint32_t n;std::vector<uint64_t>rp;std::vector<uint32_t>ci;std::vector<uint8_t>a;};
static Mat loadmat(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("open "+fn);char m[8];uint32_t p,z;uint64_t e;Mat A;f.read(m,8);f.read((char*)&A.n,4);f.read((char*)&p,4);f.read((char*)&e,8);f.read((char*)&z,4);f.read((char*)&z,4);if(std::string(m,6)!="KMC201"||p!=101)throw std::runtime_error("bad matrix");A.rp.resize(A.n+1);A.ci.resize(e);A.a.resize(e);f.read((char*)A.rp.data(),8*(A.n+1));f.read((char*)A.ci.data(),4*e);f.read((char*)A.a.data(),e);if(!f)throw std::runtime_error("truncated matrix");return A;}
struct Eig{uint32_t n,pivot;std::vector<uint8_t>v;};
static Eig loadeig(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("open "+fn);char m[8];Eig e;f.read(m,8);f.read((char*)&e.n,4);f.read((char*)&e.pivot,4);e.v.resize(e.n);f.read((char*)e.v.data(),e.n);if(std::string(m,6)!="KMV101"||!f)throw std::runtime_error("bad eigenvector");return e;}
static uint64_t hashfile(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("hash open");uint64_t h=1469598103934665603ULL;char b[65536];while(f){f.read(b,sizeof b);auto n=f.gcount();for(std::streamsize i=0;i<n;i++){h^=(uint8_t)b[i];h*=1099511628211ULL;}}return h;}
static uint64_t sm64(uint64_t&s){uint64_t z=(s+=0x9e3779b97f4a7c15ULL);z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL;z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31);}
struct Op{Mat A;bool border=false;Eig eig;uint32_t n=0;void apply(const std::vector<E>&x,std::vector<E>&y)const{
#pragma omp parallel for schedule(static)
 for(int64_t ii=0;ii<(int64_t)A.n;ii++){uint32_t i=ii;uint64_t sr=0,si=0;for(uint64_t k=A.rp[i];k<A.rp[i+1];k++){uint32_t c=A.a[k],j=A.ci[k];sr+=c*x[j].a;si+=c*x[j].b;}int ar=(int)(sr%P)-50*(int)x[i].a,ai=(int)(si%P)-50*(int)x[i].b;if(border){ar+=(int)eig.v[i]*x[A.n].a;ai+=(int)eig.v[i]*x[A.n].b;}ar%=101;ai%=101;if(ar<0)ar+=101;if(ai<0)ai+=101;y[i]={(uint8_t)ar,(uint8_t)ai};}if(border)y[A.n]=x[eig.pivot];}};
struct BMResult{uint32_t L;std::vector<E>C;};
static BMResult bm(const std::vector<E>&s,size_t used){std::vector<uint8_t>Cr(used+1),Ci(used+1),Br(used+1),Bi(used+1),Tr(used+1),Ti(used+1);Cr[0]=Br[0]=1;size_t clen=1,blen=1,L=0,m=1;E b{1,0};for(size_t n=0;n<used;n++){uint64_t dr=s[n].a,di=s[n].b;for(size_t i=1;i<=L;i++){E q=s[n-i];dr+=(uint32_t)Cr[i]*q.a+2u*(uint32_t)Ci[i]*q.b;di+=(uint32_t)Cr[i]*q.b+(uint32_t)Ci[i]*q.a;}E d{(uint8_t)(dr%P),(uint8_t)(di%P)};if(zero(d)){m++;continue;}bool jump=2*L<=n;size_t old=clen;if(jump){std::copy(Cr.begin(),Cr.begin()+clen,Tr.begin());std::copy(Ci.begin(),Ci.begin()+clen,Ti.begin());}E coef=divide(d,b);size_t need=blen+m;if(need>clen){std::fill(Cr.begin()+clen,Cr.begin()+need,0);std::fill(Ci.begin()+clen,Ci.begin()+need,0);clen=need;}for(size_t j=0;j<blen;j++){uint32_t pr=(uint32_t)coef.a*Br[j]+2u*(uint32_t)coef.b*Bi[j],pi=(uint32_t)coef.a*Bi[j]+(uint32_t)coef.b*Br[j];uint8_t rr=pr%P,ri=pi%P;size_t k=j+m;Cr[k]=(Cr[k]>=rr?Cr[k]-rr:Cr[k]+P-rr);Ci[k]=(Ci[k]>=ri?Ci[k]-ri:Ci[k]+P-ri);}if(jump){L=n+1-L;std::copy(Tr.begin(),Tr.begin()+old,Br.begin());std::copy(Ti.begin(),Ti.begin()+old,Bi.begin());blen=old;b=d;m=1;}else m++;}std::vector<E>C(L+1);for(size_t i=0;i<=L;i++)C[i]={(uint8_t)(i<clen?Cr[i]:0),(uint8_t)(i<clen?Ci[i]:0)};return {(uint32_t)L,std::move(C)};}
static size_t recbad(const std::vector<E>&s,const BMResult&r){size_t bad=0;for(size_t n=r.L;n<s.size();n++){uint64_t dr=s[n].a,di=s[n].b;for(size_t i=1;i<=r.L;i++){E c=r.C[i],q=s[n-i];dr+=(uint32_t)c.a*q.a+2u*(uint32_t)c.b*q.b;di+=(uint32_t)c.a*q.b+(uint32_t)c.b*q.a;}bad+=(dr%P||di%P);}return bad;}
#pragma pack(push,1)
struct Header{char magic[8];uint32_t version,prime,nonresidue,n,lambda,border,pivot,terms,bm_terms,degree;uint64_t seed,matrix_hash,eigen_hash;};
#pragma pack(pop)
int main(int ac,char**av){for(int a=1;a<101;a++)for(int b=1;b<101;b++)if(a*b%101==1){invp[a]=b;break;}if(ac<4){std::cerr<<"usage MATRIX CERT EIG_OR_DASH\n";return 1;}std::string mfn=av[1],cfn=av[2],efn=av[3];Mat A=loadmat(mfn);std::ifstream f(cfn,std::ios::binary);if(!f)throw std::runtime_error("open cert");Header h{};f.read((char*)&h,sizeof h);if(std::string(h.magic,8)!="KMW2CERT"||h.version!=2||h.prime!=101||h.nonresidue!=2||h.lambda!=50)throw std::runtime_error("bad cert header");if(h.matrix_hash!=hashfile(mfn))throw std::runtime_error("matrix hash mismatch");Op op;op.A=std::move(A);op.border=h.border;if(op.border){if(efn=="-")throw std::runtime_error("eigenvector required");op.eig=loadeig(efn);if(op.eig.n!=op.A.n||op.eig.pivot!=h.pivot||op.eig.v[op.eig.pivot]==0||h.eigen_hash!=hashfile(efn))throw std::runtime_error("eigenvector metadata/hash");std::vector<E>x(op.A.n),y(op.A.n);for(uint32_t i=0;i<op.A.n;i++)x[i]={op.eig.v[i],0};Op q=op;q.border=false;q.apply(x,y);for(E z:y)if(!zero(z))throw std::runtime_error("eigenvector residual nonzero");}else if(efn!="-")throw std::runtime_error("use - for normal cert");op.n=op.A.n+op.border;if(h.n!=op.n||h.terms!=h.bm_terms+32||h.bm_terms!=2*h.n)throw std::runtime_error("dimension/term mismatch");std::vector<E>stored(h.terms),storedC(h.degree+1);f.read((char*)stored.data(),2*stored.size());f.read((char*)storedC.data(),2*storedC.size());char extra;if(f.read(&extra,1))throw std::runtime_error("trailing certificate bytes");if(!f.eof()&&!f)throw std::runtime_error("truncated cert");
 uint32_t N=op.n;std::vector<E>dR(N),dL(N),u(N),x(N),dx(N),y(N),seq(h.terms);uint64_t rng=h.seed;for(uint32_t i=0;i<N;i++){do{dR[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};}while(zero(dR[i]));do{dL[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};}while(zero(dL[i]));u[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};x[i]={(uint8_t)(sm64(rng)%101),(uint8_t)(sm64(rng)%101)};}
#ifdef _OPENMP
 // A single persistent team avoids creating roughly 2N parallel regions.
 uint64_t sr=0,si=0;
#pragma omp parallel shared(sr,si,x,y,dx,seq)
 {
  for(uint32_t k=0;k<h.terms;k++){
#pragma omp single
   {sr=0;si=0;}
#pragma omp for reduction(+:sr,si) schedule(static)
   for(int64_t ii=0;ii<(int64_t)N;ii++){uint32_t i=(uint32_t)ii;sr+=(uint32_t)u[i].a*x[i].a+2u*(uint32_t)u[i].b*x[i].b;si+=(uint32_t)u[i].a*x[i].b+(uint32_t)u[i].b*x[i].a;}
#pragma omp single
   {seq[k]={(uint8_t)(sr%P),(uint8_t)(si%P)};}
#pragma omp for schedule(static)
   for(int64_t ii=0;ii<(int64_t)N;ii++){uint32_t i=(uint32_t)ii;dx[i]=mul(dR[i],x[i]);}
#pragma omp for schedule(static)
   for(int64_t ii=0;ii<(int64_t)op.A.n;ii++){
    uint32_t i=(uint32_t)ii;uint64_t ar=0,ai=0;for(uint64_t q=op.A.rp[i];q<op.A.rp[i+1];q++){uint32_t c=op.A.a[q],j=op.A.ci[q];ar+=c*dx[j].a;ai+=c*dx[j].b;}
    int rr=(int)(ar%P)-50*(int)dx[i].a,ri=(int)(ai%P)-50*(int)dx[i].b;if(op.border){rr+=(int)op.eig.v[i]*dx[op.A.n].a;ri+=(int)op.eig.v[i]*dx[op.A.n].b;}rr%=101;ri%=101;if(rr<0)rr+=101;if(ri<0)ri+=101;y[i]={(uint8_t)rr,(uint8_t)ri};
   }
#pragma omp single
   {if(op.border)y[op.A.n]=dx[op.eig.pivot];}
#pragma omp for schedule(static)
   for(int64_t ii=0;ii<(int64_t)N;ii++){uint32_t i=(uint32_t)ii;y[i]=mul(dL[i],y[i]);}
#pragma omp single
   {x.swap(y); if((k+1)%5000==0) std::cerr<<"moments "<<(k+1)<<"/"<<h.terms<<"\n";}
  }
 }
#else
 for(uint32_t k=0;k<h.terms;k++){
  uint64_t sr0=0,si0=0;for(uint32_t i=0;i<N;i++){sr0+=(uint32_t)u[i].a*x[i].a+2u*(uint32_t)u[i].b*x[i].b;si0+=(uint32_t)u[i].a*x[i].b+(uint32_t)u[i].b*x[i].a;}seq[k]={(uint8_t)(sr0%P),(uint8_t)(si0%P)};
  for(uint32_t i=0;i<N;i++)dx[i]=mul(dR[i],x[i]);op.apply(dx,y);for(uint32_t i=0;i<N;i++)y[i]=mul(dL[i],y[i]);x.swap(y);if((k+1)%5000==0)std::cerr<<"moments "<<(k+1)<<"/"<<h.terms<<"\n";
 }
#endif
 for(uint32_t k=0;k<h.terms;k++)if(seq[k].a!=stored[k].a||seq[k].b!=stored[k].b)throw std::runtime_error("moment mismatch at "+std::to_string(k));
 auto r=bm(seq,h.bm_terms);if(r.L!=h.degree||r.C.size()!=storedC.size())throw std::runtime_error("BM degree mismatch");for(size_t i=0;i<r.C.size();i++)if(r.C[i].a!=storedC[i].a||r.C[i].b!=storedC[i].b)throw std::runtime_error("BM coefficient mismatch");size_t bad=recbad(seq,r);E c=r.C[r.L];if(r.L!=N||zero(c)||bad)throw std::runtime_error("certificate criterion failed");std::cout<<"PASS "<<(op.border?"border":"nonsingular")<<" certificate: n="<<N<<", degree="<<r.L<<", constant="<<(int)c.a<<"+"<<(int)c.b<<"t, recurrence_bad="<<bad<<"\n";return 0;}
