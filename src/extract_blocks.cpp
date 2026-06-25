#define main old_knight_generator_main
#include "transfer_generator.cpp"
#undef main
#include <filesystem>
#include <map>
#include <set>
#include <sstream>

static Graph load_graph2(const std::string& fn){
    std::ifstream f(fn,std::ios::binary); if(!f) throw std::runtime_error("cannot open "+fn);
    Graph g; uint64_t n,e; f.read((char*)&n,8); f.read((char*)&e,8);
    g.states.resize(n); g.rowptr.resize(n+1); g.col.resize(e); g.wt.resize(e);
    f.read((char*)g.states.data(),8*n); f.read((char*)g.rowptr.data(),8*(n+1));
    f.read((char*)g.col.data(),4*e); f.read((char*)g.wt.data(),2*e);
    if(!f) throw std::runtime_error("truncated "+fn);
    return g;
}

static State reflect_state(State s,bool open,int m=M){
    int len=(open?1:0)+2*m; int a[16],b[16],perm[16]; decode(s,a,len);
    if(open) perm[0]=0;
    int off=open?1:0;
    for(int c=0;c<2;c++) for(int r=0;r<m;r++) perm[off+c*m+r]=off+c*m+(m-1-r);
    for(int i=0;i<len;i++) b[perm[i]]=(a[i]>=0?perm[a[i]]:a[i]);
    return encode(b,len);
}

struct ModMat{
    uint32_t n=0;
    std::vector<uint64_t> rowptr;
    std::vector<uint32_t> col;
    std::vector<uint8_t> val;
    std::vector<State> rep_state; // canonical encoded-state label for each quotient coordinate
};

static void save_modmat(const ModMat&A,const std::string&fn){
    std::ofstream f(fn,std::ios::binary); if(!f) throw std::runtime_error("cannot write "+fn);
    const char magic[8]={'K','M','C','2','0','1','\0','\0'};
    uint64_t e=A.col.size(); uint32_t p=101,zero=0;
    f.write(magic,8); f.write((char*)&A.n,4); f.write((char*)&p,4); f.write((char*)&e,8); f.write((char*)&zero,4); f.write((char*)&zero,4);
    f.write((char*)A.rowptr.data(),8*A.rowptr.size());
    f.write((char*)A.col.data(),4*A.col.size());
    f.write((char*)A.val.data(),A.val.size());
    f.write((char*)A.rep_state.data(),8*A.rep_state.size());
}

static uint64_t fnv1a_file(const std::string&fn){
    std::ifstream f(fn,std::ios::binary); uint64_t h=1469598103934665603ULL; char buf[1<<16];
    while(f){f.read(buf,sizeof(buf));std::streamsize n=f.gcount();for(std::streamsize i=0;i<n;i++){h^=(unsigned char)buf[i];h*=1099511628211ULL;}}
    return h;
}

static std::vector<uint32_t> sorted_component_vertices(const SCCResult&s,int comp){
    std::vector<uint32_t> v; for(uint32_t i=0;i<s.lab.size();i++) if(s.lab[i]==comp)v.push_back(i); return v;
}

static ModMat reflection_block(const Graph&g,const std::vector<uint32_t>&verts,bool open,bool plus){
    const uint32_t BAD=std::numeric_limits<uint32_t>::max();
    std::unordered_map<State,uint32_t> global_by_state; global_by_state.reserve(verts.size()*2);
    std::vector<uint8_t> in(g.states.size(),0); for(uint32_t v:verts){in[v]=1;global_by_state.emplace(g.states[v],v);}    
    // Canonical representatives, ordered by encoded state for cross-platform determinism.
    std::vector<std::pair<State,uint32_t>> reps;
    for(uint32_t v:verts){State rv=reflect_state(g.states[v],open);auto it=global_by_state.find(rv);if(it==global_by_state.end())throw std::runtime_error("component not reflection invariant");
        if(g.states[v]>rv)continue; bool fixed=(g.states[v]==rv); if(!plus && fixed)continue; reps.emplace_back(g.states[v],v);
    }
    std::sort(reps.begin(),reps.end());
    ModMat A; A.n=(uint32_t)reps.size(); A.rep_state.resize(A.n); A.rowptr.push_back(0);
    std::unordered_map<State,uint32_t> orbit; orbit.reserve(verts.size()*2);
    for(uint32_t q=0;q<A.n;q++){
        uint32_t v=reps[q].second; A.rep_state[q]=reps[q].first; State s=g.states[v],rs=reflect_state(s,open);
        orbit.emplace(s,q); if(plus || rs!=s) orbit.emplace(rs,q);
    }
    for(uint32_t qi=0;qi<A.n;qi++){
        uint32_t i=reps[qi].second; State si=g.states[i],rsi=reflect_state(si,open);
        if(!plus && si==rsi)throw std::runtime_error("fixed row in minus block");
        std::unordered_map<uint32_t,int> acc; acc.reserve((g.rowptr[i+1]-g.rowptr[i])*2+4);
        for(uint64_t k=g.rowptr[i];k<g.rowptr[i+1];k++){
            uint32_t j=g.col[k]; if(!in[j])continue; State sj=g.states[j]; State rsj=reflect_state(sj,open);
            if(!plus && sj==rsj)continue; // antisymmetric coordinates vanish on fixed orbits
            State canon=std::min(sj,rsj); auto it=orbit.find(canon); if(it==orbit.end())throw std::runtime_error("target orbit missing");
            if(plus){acc[it->second]+=g.wt[k];}
            else{
                int sign=(sj==canon)?1:-1; acc[it->second]+=sign*(int)g.wt[k];
            }
        }
        std::vector<std::pair<uint32_t,uint8_t>> row; row.reserve(acc.size());
        for(auto &kv:acc){int x=kv.second%101;if(x<0)x+=101;if(x)row.emplace_back(kv.first,(uint8_t)x);}std::sort(row.begin(),row.end());
        for(auto &e:row){A.col.push_back(e.first);A.val.push_back(e.second);}A.rowptr.push_back(A.col.size());
    }
    return A;
}

static std::vector<uint32_t> all_vertices(const Graph&g){std::vector<uint32_t>v(g.states.size());std::iota(v.begin(),v.end(),0);return v;}

static int comp_of_size(const SCCResult&s,int target,int skip=0){for(int c=0;c<s.ncomp;c++)if(s.size[c]==target){if(skip--==0)return c;}throw std::runtime_error("component size not found");}

static void write_vec_u8(const std::string&fn,const std::vector<uint8_t>&v){std::ofstream f(fn,std::ios::binary);uint32_t n=v.size();f.write((char*)&n,4);f.write((char*)v.data(),v.size());}

int main(int argc,char**argv){
    std::string dir=argc>1?argv[1]:"../data";
    std::filesystem::create_directories(dir+"/blocks");
    Graph T=load_graph2(dir+"/T5.bin"),U=load_graph2(dir+"/U5.bin"),W=load_graph2(dir+"/W5.bin");
    SCCResult st=scc_kosaraju(T),su=scc_kosaraju(U),sw=scc_kosaraju(W);
    int ct=comp_of_size(st,33409), cu1=comp_of_size(su,51112),cu2=comp_of_size(su,47198),cw=comp_of_size(sw,33409);
    auto singleton_ok=[&](const Graph&g,const SCCResult&s,const std::set<int>&big){for(uint32_t i=0;i<g.states.size();i++){int c=s.lab[i];if(big.count(c))continue;if(s.size[c]!=1)throw std::runtime_error("unexpected non-singleton SCC");uint32_t d=0;for(uint64_t k=g.rowptr[i];k<g.rowptr[i+1];k++)if(g.col[k]==i)d=(d+g.wt[k])%101;if(d==50)throw std::runtime_error("singleton eigenvalue 50");}};
    singleton_ok(T,st,{ct}); singleton_ok(U,su,{cu1,cu2});
    std::vector<uint8_t> ft(W.states.size(),0);for(uint32_t i=0;i<W.states.size();i++)if(finish_closed(W.states[i]))ft[i]=1;auto co=coreachable(W,ft);size_t nco=std::accumulate(co.begin(),co.end(),size_t(0));if(nco!=33409)throw std::runtime_error("W coreachable size");for(uint32_t i=0;i<W.states.size();i++)if((bool)co[i]!=(sw.lab[i]==cw))throw std::runtime_error("W coreachable set not giant SCC");
    auto vt=sorted_component_vertices(st,ct),vu1=sorted_component_vertices(su,cu1),vu2=sorted_component_vertices(su,cu2),vw=sorted_component_vertices(sw,cw);
    // Verify W relevant component is literally the same labeled closed transfer as T relevant component.
    std::unordered_map<State,uint32_t> wt;for(uint32_t v:vw)wt.emplace(W.states[v],v);
    size_t mismatch=0;for(uint32_t i:vt){auto it=wt.find(T.states[i]);if(it==wt.end()){mismatch++;continue;}uint32_t wi=it->second;
        std::map<State,uint32_t>a,b;for(uint64_t k=T.rowptr[i];k<T.rowptr[i+1];k++)if(st.lab[T.col[k]]==ct)a[T.states[T.col[k]]]+=T.wt[k];
        for(uint64_t k=W.rowptr[wi];k<W.rowptr[wi+1];k++)if(sw.lab[W.col[k]]==cw)b[W.states[W.col[k]]]+=W.wt[k];if(a!=b)mismatch++;}
    if(mismatch)throw std::runtime_error("Trel/Wrel mismatch count "+std::to_string(mismatch));
    struct Job{std::string name;const Graph*g;std::vector<uint32_t>*v;bool open;};
    std::vector<Job> jobs={{"Trel",&T,&vt,false},{"U1",&U,&vu1,true},{"U2",&U,&vu2,true}};
    std::ofstream manifest(dir+"/blocks/manifest.txt");
    manifest<<"Wrel_is_permutation_similar_to_Trel 1\n";
    for(auto &j:jobs){
        for(bool plus:{true,false}){
            ModMat A=reflection_block(*j.g,*j.v,j.open,plus);std::string nm=j.name+(plus?"_plus":"_minus");std::string fn=dir+"/blocks/"+nm+".kmc";save_modmat(A,fn);
            manifest<<nm<<" n "<<A.n<<" nnz "<<A.col.size()<<" fnv1a64 "<<std::hex<<fnv1a_file(fn)<<std::dec<<"\n";
            std::cout<<nm<<" n="<<A.n<<" nnz="<<A.col.size()<<"\n";
        }
    }
    // Full reachable closed + quotient, plus finish vector and bare-state coordinate, for eigenvector extraction.
    auto va=all_vertices(T);ModMat Tall=reflection_block(T,va,false,true);save_modmat(Tall,dir+"/blocks/Tall_plus.kmc");
    std::vector<uint8_t> finish(Tall.n);uint32_t bareq=UINT32_MAX;
    std::unordered_map<State,uint32_t> tby; for(uint32_t i=0;i<T.states.size();i++)tby.emplace(T.states[i],i);
    for(uint32_t q=0;q<Tall.n;q++){auto it=tby.find(Tall.rep_state[q]);if(it==tby.end())throw std::runtime_error("Tall representative missing");uint32_t i=it->second;uint32_t fv=finish_closed(T.states[i])%101;
        State ri=reflect_state(T.states[i],false);auto jt=tby.find(ri);if(jt==tby.end()||finish_closed(T.states[jt->second])%101!=fv)throw std::runtime_error("finish reflection mismatch");
        finish[q]=(uint8_t)fv;if(T.states[i]==0)bareq=q;
    }
    if(bareq==UINT32_MAX)throw std::runtime_error("bare state not found");
    write_vec_u8(dir+"/blocks/Tall_finish.vec",finish);
    std::ofstream aux(dir+"/blocks/Tall_aux.txt");aux<<"bare_coordinate "<<bareq<<"\n";
    manifest<<"Tall_plus n "<<Tall.n<<" nnz "<<Tall.col.size()<<" fnv1a64 "<<std::hex<<fnv1a_file(dir+"/blocks/Tall_plus.kmc")<<std::dec<<"\n";
    std::cout<<"Tall_plus n="<<Tall.n<<" nnz="<<Tall.col.size()<<" bare="<<bareq<<"\n";
    std::cout<<"Trel/Wrel exact labeled equality verified\n";
}
