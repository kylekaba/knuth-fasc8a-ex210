#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif
struct Mat{uint32_t n;std::vector<uint64_t>rp;std::vector<uint32_t>ci;std::vector<uint8_t>a;std::vector<uint64_t>rep;};
static Mat loadmat(const std::string&fn){std::ifstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("open "+fn);char m[8];uint32_t p,z;uint64_t e;Mat A;f.read(m,8);f.read((char*)&A.n,4);f.read((char*)&p,4);f.read((char*)&e,8);f.read((char*)&z,4);f.read((char*)&z,4);if(std::string(m,6)!="KMC201"||p!=101)throw std::runtime_error("bad matrix");A.rp.resize(A.n+1);A.ci.resize(e);A.a.resize(e);A.rep.resize(A.n);f.read((char*)A.rp.data(),8*(A.n+1));f.read((char*)A.ci.data(),4*e);f.read((char*)A.a.data(),e);f.read((char*)A.rep.data(),8*A.n);if(!f)throw std::runtime_error("truncated matrix");return A;}
static void mv(const Mat&A,const std::vector<uint8_t>&x,std::vector<uint8_t>&y){
#pragma omp parallel for schedule(static)
 for(int64_t i=0;i<(int64_t)A.n;i++){uint32_t s=0;for(uint64_t k=A.rp[i];k<A.rp[i+1];k++)s+=(uint32_t)A.a[k]*x[A.ci[k]];y[i]=s%101;}}
static void mv2(const Mat&A,const std::vector<uint8_t>&x,std::vector<uint8_t>&t,std::vector<uint8_t>&y){mv(A,x,t);mv(A,t,y);}
static std::vector<std::vector<uint8_t>> polyMCheckpoints(const Mat&A,const std::vector<uint8_t>&g,const std::vector<uint8_t>&b,uint32_t chunk){std::vector<std::vector<uint8_t>> checkpoints;std::vector<uint8_t>v(A.n),t(A.n),w(A.n);checkpoints.push_back(v);for(uint32_t s=0;s<g.size();s++){mv2(A,v,t,w);v.swap(w);uint8_t q=g[g.size()-1-s];if(q)for(uint32_t i=0;i<A.n;i++)v[i]=(v[i]+(uint32_t)q*b[i])%101;if((s+1)%chunk==0||s+1==g.size())checkpoints.push_back(v);}return checkpoints;}
static void saveCheckpoints(const std::string&fn,uint32_t n,uint32_t steps,uint32_t chunk,const std::vector<std::vector<uint8_t>>&checkpoints){std::ofstream f(fn,std::ios::binary);if(!f)throw std::runtime_error("write "+fn);const char m[8]={'K','M','H','1','0','1',0,0};uint32_t count=checkpoints.size();f.write(m,8);f.write((char*)&n,4);f.write((char*)&steps,4);f.write((char*)&chunk,4);f.write((char*)&count,4);for(const auto&v:checkpoints){if(v.size()!=n)throw std::runtime_error("checkpoint size");f.write((char*)v.data(),v.size());}if(!f)throw std::runtime_error("write checkpoint data");}
struct Eig{uint32_t n,pivot;std::vector<uint8_t>v;};
static Eig loadeig(const std::string&fn){std::ifstream f(fn,std::ios::binary);char m[8];Eig e;f.read(m,8);f.read((char*)&e.n,4);f.read((char*)&e.pivot,4);e.v.resize(e.n);f.read((char*)e.v.data(),e.n);if(std::string(m,6)!="KMV101"||!f)throw std::runtime_error("bad eigenvector");return e;}
int main(int ac,char**av){std::string d=ac>1?av[1]:"data";Mat A=loadmat(d+"/blocks/Tall_plus.kmc"),R=loadmat(d+"/blocks/Trel_plus.kmc");std::ifstream vf(d+"/blocks/Tall_finish.vec",std::ios::binary);uint32_t n;vf.read((char*)&n,4);std::vector<uint8_t>beta(n);vf.read((char*)beta.data(),n);if(n!=A.n||!vf)throw std::runtime_error("finish vector");std::ifstream pf(d+"/certs/visible76.poly",std::ios::binary);char pm[8];uint32_t glen;pf.read(pm,8);pf.read((char*)&glen,4);std::vector<uint8_t>g(glen);pf.read((char*)g.data(),glen);if(std::string(pm,6)!="KMP101"||!pf)throw std::runtime_error("polynomial");
 uint32_t checkpointChunk=1027;auto checkpoints=polyMCheckpoints(A,g,beta,checkpointChunk);auto r=checkpoints.back();if(ac>2)saveCheckpoints(av[2],A.n,g.size(),checkpointChunk,checkpoints);std::vector<uint8_t>t(A.n),y(A.n);mv2(A,r,t,y);size_t bad=0;for(uint32_t i=0;i<A.n;i++)bad+=y[i]!=(uint8_t)(76*r[i]%101);if(bad||r[0]==0)throw std::runtime_error("visible 76 eigenvector check failed");
 mv(A,r,t);std::vector<uint8_t>v(A.n);for(uint32_t i=0;i<A.n;i++)v[i]=(r[i]+99u*t[i])%101; // 50^{-1}=99
 mv(A,v,y);bad=0;for(uint32_t i=0;i<A.n;i++)bad+=y[i]!=(uint8_t)(50*v[i]%101);if(bad||v[0]==0)throw std::runtime_error("visible 50 eigenvector check failed");
 Eig e=loadeig(d+"/certs/Trel_plus_eigen50.vec");if(e.n!=R.n||e.pivot>=e.n||e.v[e.pivot]==0)throw std::runtime_error("eigenvector metadata");std::unordered_map<uint64_t,uint32_t>pos;pos.reserve(A.n*2);for(uint32_t i=0;i<A.n;i++)pos.emplace(A.rep[i],i);for(uint32_t i=0;i<R.n;i++){auto it=pos.find(R.rep[i]);if(it==pos.end()||e.v[i]!=v[it->second])throw std::runtime_error("restricted eigenvector mismatch");}
 std::vector<uint8_t>z(R.n);mv(R,e.v,z);bad=0;for(uint32_t i=0;i<R.n;i++)bad+=z[i]!=(uint8_t)(50*e.v[i]%101);if(bad)throw std::runtime_error("Trel eigen residual");
 std::cout<<"PASS visible factor: degree(g)="<<glen-1<<", r_bare="<<(int)r[0]<<", v_bare="<<(int)v[0]<<", pivot="<<e.pivot<<", pivot_value="<<(int)e.v[e.pivot]<<"\n";
 std::cout<<"Therefore 1-50z divides the reduced closed-tour denominator modulo 101.\n";return 0;}
