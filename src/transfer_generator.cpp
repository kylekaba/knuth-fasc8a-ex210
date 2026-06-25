#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <filesystem>
#include <functional>
#include <iostream>
#include <limits>
#include <numeric>
#include <queue>
#include <random>
#include <string>
#include <stdexcept>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>
#ifdef _OPENMP
#include <omp.h>
#endif

using State = uint64_t;
using Temp = unsigned __int128;
struct TempHash {
    size_t operator()(Temp x) const noexcept {
        uint64_t lo=(uint64_t)x, hi=(uint64_t)(x>>64);
        lo ^= hi + 0x9e3779b97f4a7c15ULL + (lo<<6) + (lo>>2);
        lo ^= lo>>30; lo *= 0xbf58476d1ce4e5b9ULL;
        lo ^= lo>>27; lo *= 0x94d049bb133111ebULL;
        return (size_t)(lo ^ (lo>>31));
    }
};
static constexpr int BARE=-1, INNER=-2;
static constexpr int M=5;

static inline int code_of(int a){ return a==BARE?0:(a==INNER?1:a+2); }
static inline int val_of(int c){ return c==0?BARE:(c==1?INNER:c-2); }
static inline int getv(State s,int i){ return val_of((int)((s>>(4*i))&15)); }
static inline void setv(State &s,int i,int a){ State mask=State(15)<<(4*i); s=(s&~mask)|(State(code_of(a))<<(4*i)); }
static State encode(const int *a,int len){ State s=0; for(int i=0;i<len;i++) s|=State(code_of(a[i]))<<(4*i); return s; }
static void decode(State s,int *a,int len){ for(int i=0;i<len;i++) a[i]=getv(s,i); }
static inline int deg(int a){ return a==BARE?0:(a==INNER?2:1); }
static inline int gett(Temp s,int i){ return val_of((int)((s>>(5*i))&31)); }
static Temp encodet(const int *a,int len){ Temp s=0; for(int i=0;i<len;i++) s|=Temp(code_of(a[i]))<<(5*i); return s; }
static void decodet(Temp s,int *a,int len){ for(int i=0;i<len;i++) a[i]=gett(s,i); }

static State remove_range_temp(Temp st,int len,int lo,int cnt){
    int a[16],b[16],newpos[16]; decodet(st,a,len);
    for(int i=0;i<len;i++) newpos[i]=-1;
    int q=0; for(int i=0;i<len;i++) if(i<lo || i>=lo+cnt) newpos[i]=q++;
    q=0;
    for(int i=0;i<len;i++) if(newpos[i]>=0){
        int x=a[i];
        if(x>=0){ assert(x<len && newpos[x]>=0); x=newpos[x]; }
        b[q++]=x;
    }
    return encode(b,len-cnt);
}

// 0 invalid, 1 ordinary forest edge, 2 closes a cycle.
static int add_edge(int *s,int i,int j){
    int a=s[i],b=s[j];
    if(i==j || a==INNER || b==INNER) return 0;
    if(a==BARE && b==BARE){s[i]=j;s[j]=i;return 1;}
    if(a==BARE && b>=0){int pb=b;s[i]=pb;s[pb]=i;s[j]=INNER;return 1;}
    if(a>=0 && b==BARE){int pa=a;s[j]=pa;s[pa]=j;s[i]=INNER;return 1;}
    int pa=a,pb=b;
    if(pa==j && pb==i){s[i]=s[j]=INNER;return 2;}
    s[pa]=pb;s[pb]=pa;s[i]=s[j]=INNER;return 1;
}

static State remove_range(State st,int len,int lo,int cnt){
    int a[16],b[16],newpos[16]; decode(st,a,len);
    for(int i=0;i<len;i++) newpos[i]=-1;
    int q=0; for(int i=0;i<len;i++) if(i<lo || i>=lo+cnt) newpos[i]=q++;
    q=0;
    for(int i=0;i<len;i++) if(newpos[i]>=0){
        int x=a[i];
        if(x>=0){ assert(newpos[x]>=0); x=newpos[x]; }
        b[q++]=x;
    }
    return encode(b,len-cnt);
}

using Out = std::vector<std::pair<State,uint32_t>>;

static void add_aggregated(std::unordered_map<State,uint32_t>& mp,State s,uint32_t w){
    auto it=mp.find(s); if(it==mp.end()) mp.emplace(s,w); else it->second+=w;
}

static Out stable_closed(State state,int m=M){
    // A,B followed by new bare C. Temporary frontier needs 5-bit entries:
    // partner index 14 has code 16, which does not fit the stable 4-bit format.
    int base[16]; decode(state,base,2*m); for(int i=2*m;i<3*m;i++) base[i]=BARE;
    std::unordered_map<Temp,uint32_t,TempHash> acc,nxt; acc.reserve(128);acc.emplace(encodet(base,3*m),1);
    for(int r=0;r<m;r++){
        nxt.clear(); nxt.reserve(acc.size()*3+8);
        for(auto const &kv:acc){
            int cur[16];decodet(kv.first,cur,3*m); uint32_t w=kv.second;
            int need=2-deg(cur[r]);
            int nb[4],nn=0;
            for(int rr: {r-2,r+2}) if(0<=rr&&rr<m) nb[nn++]=m+rr;
            for(int rr: {r-1,r+1}) if(0<=rr&&rr<m) nb[nn++]=2*m+rr;
            if(need==0){auto it=nxt.find(kv.first);if(it==nxt.end())nxt.emplace(kv.first,w);else it->second+=w;}
            else if(need==1){
                for(int x=0;x<nn;x++){int a[16];std::copy(cur,cur+3*m,a);int typ=add_edge(a,r,nb[x]);if(typ==1){Temp t=encodet(a,3*m);auto it=nxt.find(t);if(it==nxt.end())nxt.emplace(t,w);else it->second+=w;}}
            } else if(need==2){
                for(int x=0;x<nn;x++)for(int y=x+1;y<nn;y++){int a[16];std::copy(cur,cur+3*m,a);int t1=add_edge(a,r,nb[x]);if(t1!=1)continue;int t2=add_edge(a,r,nb[y]);if(t2==1){Temp t=encodet(a,3*m);auto it=nxt.find(t);if(it==nxt.end())nxt.emplace(t,w);else it->second+=w;}}
            }
        }
        acc.swap(nxt); if(acc.empty()) break;
    }
    std::unordered_map<State,uint32_t> out;out.reserve(acc.size());
    for(auto const &kv:acc){bool ok=true;for(int r=0;r<m;r++)if(gett(kv.first,r)!=INNER){ok=false;break;}if(ok)add_aggregated(out,remove_range_temp(kv.first,3*m,0,m),kv.second);}
    Out v;v.reserve(out.size());for(auto &kv:out)v.push_back(kv);std::sort(v.begin(),v.end(),[](auto const&a,auto const&b){return a.first<b.first;});return v;
}

static State closed_to_open(State s,int m=M){
    int a[16],b[16];decode(s,a,2*m);b[0]=BARE;for(int i=0;i<2*m;i++)b[i+1]=(a[i]>=0?a[i]+1:a[i]);return encode(b,1+2*m);
}

static Out stable_open(State state,int target_deg=-1,bool allow_inf=true,int m=M){
    // infinity,A,B,new C; temporary length is 16, so use 5-bit entries.
    int base[16];decode(state,base,1+2*m);for(int i=1+2*m;i<1+3*m;i++)base[i]=BARE;
    std::unordered_map<Temp,uint32_t,TempHash> acc,nxt;acc.reserve(256);acc.emplace(encodet(base,1+3*m),1);
    for(int r=0;r<m;r++){
        int i=1+r;nxt.clear();nxt.reserve(acc.size()*3+8);
        for(auto const &kv:acc){
            int cur[16];decodet(kv.first,cur,1+3*m);uint32_t w=kv.second;
            int need=2-deg(cur[i]);int nb[5],nn=0;
            if(allow_inf && deg(cur[0])<2) nb[nn++]=0;
            for(int rr:{r-2,r+2})if(0<=rr&&rr<m)nb[nn++]=1+m+rr;
            for(int rr:{r-1,r+1})if(0<=rr&&rr<m)nb[nn++]=1+2*m+rr;
            if(need==0){auto it=nxt.find(kv.first);if(it==nxt.end())nxt.emplace(kv.first,w);else it->second+=w;}
            else if(need==1){for(int x=0;x<nn;x++){int a[16];std::copy(cur,cur+1+3*m,a);int typ=add_edge(a,i,nb[x]);if(typ==1){Temp t=encodet(a,1+3*m);auto it=nxt.find(t);if(it==nxt.end())nxt.emplace(t,w);else it->second+=w;}}}
            else if(need==2){for(int x=0;x<nn;x++)for(int y=x+1;y<nn;y++){int a[16];std::copy(cur,cur+1+3*m,a);int t1=add_edge(a,i,nb[x]);if(t1!=1)continue;int t2=add_edge(a,i,nb[y]);if(t2==1){Temp t=encodet(a,1+3*m);auto it=nxt.find(t);if(it==nxt.end())nxt.emplace(t,w);else it->second+=w;}}}
        }
        acc.swap(nxt);if(acc.empty())break;
    }
    std::unordered_map<State,uint32_t> out;out.reserve(acc.size());
    for(auto const &kv:acc){bool ok=true;for(int r=0;r<m;r++)if(gett(kv.first,1+r)!=INNER){ok=false;break;}if(!ok)continue;State t=remove_range_temp(kv.first,1+3*m,1,m);if(target_deg<0||deg(getv(t,0))==target_deg)add_aggregated(out,t,kv.second);}
    Out v;v.reserve(out.size());for(auto &kv:out)v.push_back(kv);std::sort(v.begin(),v.end(),[](auto const&a,auto const&b){return a.first<b.first;});return v;
}

static State drop_inf(State s,int m=M){assert(getv(s,0)==INNER);return remove_range(s,1+2*m,0,1);}

static uint32_t finish_closed(State state,int m=M){
    std::unordered_map<State,uint32_t> acc,nxt;acc.emplace(state,1);uint32_t total=0;
    for(int r=0;r<m;r++){
        nxt.clear();
        for(auto const &kv:acc){int cur[16];decode(kv.first,cur,2*m);int need=2-deg(cur[r]);int nb[2],nn=0;for(int rr:{r-2,r+2})if(0<=rr&&rr<m)nb[nn++]=m+rr;
            auto handle=[&](int x,int y,bool two){int a[16];std::copy(cur,cur+2*m,a);int typ=add_edge(a,r,nb[x]);if(typ==0)return;if(typ==2){bool all=true;for(int k=0;k<2*m;k++)if(a[k]!=INNER){all=false;break;}if(all)total+=kv.second;return;}if(two){typ=add_edge(a,r,nb[y]);if(typ==0)return;if(typ==2){bool all=true;for(int k=0;k<2*m;k++)if(a[k]!=INNER){all=false;break;}if(all)total+=kv.second;return;}}add_aggregated(nxt,encode(a,2*m),kv.second);};
            if(need==0)add_aggregated(nxt,kv.first,kv.second);else if(need==1)for(int x=0;x<nn;x++)handle(x,0,false);else if(need==2)for(int x=0;x<nn;x++)for(int y=x+1;y<nn;y++)handle(x,y,true);
        }
        acc.swap(nxt);
    }
    return total;
}


// Finish an augmented-cycle state containing infinity,A,B without introducing
// another board column.  This is the terminal functional for phases d_inf=0
// and d_inf=1: the missing one or two infinity edges may be selected in the
// last two board columns.  A cycle is accepted only when every retained
// vertex, including infinity, has degree 2.
static uint32_t finish_open(State state,int m=M){
    std::unordered_map<State,uint32_t> acc,nxt; acc.emplace(state,1); uint32_t total=0;
    const int len=1+2*m;
    auto all_inner=[&](int const *a){
        for(int k=0;k<len;k++) if(a[k]!=INNER) return false;
        return true;
    };
    // Process the penultimate column A.  Its forward neighbours are infinity
    // and knight-neighbours in the last column B.
    for(int r=0;r<m;r++){
        const int i=1+r;
        nxt.clear();
        for(auto const &kv:acc){
            int cur[16]; decode(kv.first,cur,len);
            int need=2-deg(cur[i]);
            int nb[3],nn=0;
            if(deg(cur[0])<2) nb[nn++]=0;
            for(int rr:{r-2,r+2}) if(0<=rr&&rr<m) nb[nn++]=1+m+rr;
            auto handle=[&](int x,int y,bool two){
                int a[16]; std::copy(cur,cur+len,a);
                int typ=add_edge(a,i,nb[x]);
                if(typ==0) return;
                if(typ==2){ if(all_inner(a)) total+=kv.second; return; }
                if(two){
                    typ=add_edge(a,i,nb[y]);
                    if(typ==0) return;
                    if(typ==2){ if(all_inner(a)) total+=kv.second; return; }
                }
                add_aggregated(nxt,encode(a,len),kv.second);
            };
            if(need==0) add_aggregated(nxt,kv.first,kv.second);
            else if(need==1) for(int x=0;x<nn;x++) handle(x,0,false);
            else if(need==2) for(int x=0;x<nn;x++) for(int y=x+1;y<nn;y++) handle(x,y,true);
        }
        acc.swap(nxt);
    }
    // Vertices in the final column B are never shifted into the A position.
    // Their only still-unseen possible edge is therefore the edge to infinity.
    // This second terminal loop is essential when an endpoint lies in the
    // board's last column.
    for(int r=0;r<m;r++){
        const int i=1+m+r;
        nxt.clear();
        for(auto const &kv:acc){
            int cur[16]; decode(kv.first,cur,len);
            int need=2-deg(cur[i]);
            if(need==0){ add_aggregated(nxt,kv.first,kv.second); continue; }
            if(need!=1 || deg(cur[0])>=2) continue;
            int a[16]; std::copy(cur,cur+len,a);
            int typ=add_edge(a,i,0);
            if(typ==2){ if(all_inner(a)) total+=kv.second; }
            else if(typ==1) add_aggregated(nxt,encode(a,len),kv.second);
        }
        acc.swap(nxt);
    }
    return total;
}


struct Graph{
    std::vector<State> states;
    std::unordered_map<State,uint32_t> idx;
    std::vector<uint64_t> rowptr;
    std::vector<uint32_t> col;
    std::vector<uint16_t> wt;
};

static Graph bfs_closed(std::vector<State> seeds){
    Graph g;g.states=std::move(seeds);g.idx.reserve(100000);for(uint32_t i=0;i<g.states.size();i++)g.idx.emplace(g.states[i],i);g.rowptr.push_back(0);
    for(size_t p=0;p<g.states.size();p++){
        Out d=stable_closed(g.states[p]);
        for(auto &e:d){auto [it,ins]=g.idx.emplace(e.first,(uint32_t)g.states.size());if(ins)g.states.push_back(e.first);g.col.push_back(it->second);if(e.second>65535)throw std::runtime_error("transition weight overflow");g.wt.push_back((uint16_t)e.second);}
        g.rowptr.push_back(g.col.size());
        if((p+1)%10000==0)std::cerr<<"closed bfs "<<p+1<<" states="<<g.states.size()<<"\n";
    }
    return g;
}

static Graph bfs_u(const std::vector<State>& closed_states){
    Graph g;g.idx.reserve(150000);
    for(size_t i=0;i<closed_states.size();i++){
        Out d=stable_open(closed_to_open(closed_states[i]),1,true);
        for(auto &e:d){auto [it,ins]=g.idx.emplace(e.first,(uint32_t)g.states.size());if(ins)g.states.push_back(e.first);}
    }
    std::cerr<<"U seeds="<<g.states.size()<<"\n";g.rowptr.push_back(0);
    for(size_t p=0;p<g.states.size();p++){
        Out d=stable_open(g.states[p],1,false);
        for(auto&e:d){auto[it,ins]=g.idx.emplace(e.first,(uint32_t)g.states.size());if(ins)g.states.push_back(e.first);g.col.push_back(it->second);if(e.second>65535)throw std::runtime_error("transition weight overflow");g.wt.push_back((uint16_t)e.second);}
        g.rowptr.push_back(g.col.size());if((p+1)%10000==0)std::cerr<<"U bfs "<<p+1<<" states="<<g.states.size()<<"\n";
    }
    return g;
}

static Graph bfs_w(const std::vector<State>& closed_states,const std::vector<State>& u_states){
    Graph g;g.idx.reserve(80000);
    auto ingest=[&](State os){Out d=stable_open(os,2,true);for(auto&e:d){State t=drop_inf(e.first);auto[it,ins]=g.idx.emplace(t,(uint32_t)g.states.size());if(ins)g.states.push_back(t);}};
    for(size_t i=0;i<closed_states.size();i++){ingest(closed_to_open(closed_states[i]));if((i+1)%10000==0)std::cerr<<"W direct seeds from T "<<i+1<<" W="<<g.states.size()<<"\n";}
    for(size_t i=0;i<u_states.size();i++){ingest(u_states[i]);if((i+1)%10000==0)std::cerr<<"W seeds from U "<<i+1<<" W="<<g.states.size()<<"\n";}
    std::cerr<<"W seeds="<<g.states.size()<<"\n";g.rowptr.push_back(0);
    for(size_t p=0;p<g.states.size();p++){
        Out d=stable_closed(g.states[p]);for(auto&e:d){auto[it,ins]=g.idx.emplace(e.first,(uint32_t)g.states.size());if(ins)g.states.push_back(e.first);g.col.push_back(it->second);if(e.second>65535)throw std::runtime_error("transition weight overflow");g.wt.push_back((uint16_t)e.second);}g.rowptr.push_back(g.col.size());
    }
    return g;
}

struct SCCResult{int ncomp;std::vector<int> lab;std::vector<int> size;};
static SCCResult scc_kosaraju(const Graph&g){
    size_t n=g.states.size();std::vector<uint64_t> rptr(n+1,0);for(auto j:g.col)rptr[j+1]++;for(size_t i=1;i<=n;i++)rptr[i]+=rptr[i-1];std::vector<uint32_t> rcol(g.col.size());auto pos=rptr;for(uint32_t i=0;i<n;i++)for(uint64_t k=g.rowptr[i];k<g.rowptr[i+1];k++)rcol[pos[g.col[k]]++]=i;
    std::vector<uint8_t> seen(n,0);std::vector<uint32_t> order;order.reserve(n);
    for(uint32_t root=0;root<n;root++)if(!seen[root]){
        std::vector<std::pair<uint32_t,uint64_t>> st;st.emplace_back(root,g.rowptr[root]);seen[root]=1;
        while(!st.empty()){
            auto &top=st.back();uint32_t v=top.first;uint64_t &k=top.second;
            if(k<g.rowptr[v+1]){uint32_t w=g.col[k++];if(!seen[w]){seen[w]=1;st.emplace_back(w,g.rowptr[w]);}}
            else{order.push_back(v);st.pop_back();}
        }
    }
    std::vector<int> lab(n,-1),sizes;int c=0;
    for(auto it=order.rbegin();it!=order.rend();++it){uint32_t root=*it;if(lab[root]>=0)continue;int sz=0;std::vector<uint32_t> st{root};lab[root]=c;while(!st.empty()){uint32_t v=st.back();st.pop_back();sz++;for(uint64_t k=rptr[v];k<rptr[v+1];k++){uint32_t w=rcol[k];if(lab[w]<0){lab[w]=c;st.push_back(w);}}}sizes.push_back(sz);c++;}
    return {c,std::move(lab),std::move(sizes)};
}

static std::vector<uint8_t> coreachable(const Graph&g,const std::vector<uint8_t>&target){
    size_t n=g.states.size();std::vector<uint64_t> rptr(n+1,0);for(auto j:g.col)rptr[j+1]++;for(size_t i=1;i<=n;i++)rptr[i]+=rptr[i-1];std::vector<uint32_t> rcol(g.col.size());auto pos=rptr;for(uint32_t i=0;i<n;i++)for(uint64_t k=g.rowptr[i];k<g.rowptr[i+1];k++)rcol[pos[g.col[k]]++]=i;
    std::vector<uint8_t> yes=target;std::deque<uint32_t>q;for(uint32_t i=0;i<n;i++)if(yes[i])q.push_back(i);while(!q.empty()){uint32_t v=q.front();q.pop_front();for(uint64_t k=rptr[v];k<rptr[v+1];k++){uint32_t w=rcol[k];if(!yes[w]){yes[w]=1;q.push_back(w);}}}return yes;
}

static void save_graph(const Graph&g,const std::string&prefix){
    std::ofstream f(prefix+".bin",std::ios::binary);uint64_t n=g.states.size(),e=g.col.size();f.write((char*)&n,8);f.write((char*)&e,8);f.write((char*)g.states.data(),8*n);f.write((char*)g.rowptr.data(),8*(n+1));f.write((char*)g.col.data(),4*e);f.write((char*)g.wt.data(),2*e);
}

int main(int argc,char**argv){
    std::string outdir=argc>1?argv[1]:"data"; std::filesystem::create_directories(outdir);
    auto t0=std::chrono::steady_clock::now();
    State bare=0;
    Graph T=bfs_closed({bare});
    std::cout<<"T states "<<T.states.size()<<" edges "<<T.col.size()<<"\n";
    SCCResult st=scc_kosaraju(T);std::vector<int> ts=st.size;std::sort(ts.rbegin(),ts.rend());std::cout<<"T SCC "<<st.ncomp<<" largest";for(int i=0;i<std::min<int>(5,ts.size());i++)std::cout<<" "<<ts[i];std::cout<<"\n";
    Graph U=bfs_u(T.states);std::cout<<"U states "<<U.states.size()<<" edges "<<U.col.size()<<"\n";
    SCCResult su=scc_kosaraju(U);std::vector<int> us=su.size;std::sort(us.rbegin(),us.rend());std::cout<<"U SCC "<<su.ncomp<<" largest";for(int i=0;i<std::min<int>(5,us.size());i++)std::cout<<" "<<us[i];std::cout<<"\n";
    Graph W=bfs_w(T.states,U.states);std::cout<<"W states "<<W.states.size()<<" edges "<<W.col.size()<<"\n";
    SCCResult sw=scc_kosaraju(W);std::vector<int> ws=sw.size;std::sort(ws.rbegin(),ws.rend());std::cout<<"W SCC "<<sw.ncomp<<" largest";for(int i=0;i<std::min<int>(5,ws.size());i++)std::cout<<" "<<ws[i];std::cout<<"\n";
    std::vector<uint8_t> ft(W.states.size(),0);size_t nfin=0;for(size_t i=0;i<W.states.size();i++)if(finish_closed(W.states[i])){ft[i]=1;nfin++;}
    auto wr=coreachable(W,ft);size_t nwrel=std::accumulate(wr.begin(),wr.end(),size_t(0));std::cout<<"W finish states "<<nfin<<" coreachable "<<nwrel<<"\n";
    // Basic singleton-loop diagnostics at 50 and 51.
    auto diag_counts=[&](const Graph&g,const SCCResult&s){int a=0,b=0;for(uint32_t i=0;i<g.states.size();i++)if(s.size[s.lab[i]]==1){unsigned val=0;for(uint64_t k=g.rowptr[i];k<g.rowptr[i+1];k++)if(g.col[k]==i)val=(val+g.wt[k])%101;if(val==50)a++;if(val==51)b++;}return std::pair<int,int>{a,b};};
    auto dt=diag_counts(T,st),du=diag_counts(U,su),dw=diag_counts(W,sw);std::cout<<"singleton loops lambda50/51 T "<<dt.first<<"/"<<dt.second<<" U "<<du.first<<"/"<<du.second<<" W "<<dw.first<<"/"<<dw.second<<"\n";
    save_graph(T,outdir+"/T5");save_graph(U,outdir+"/U5");save_graph(W,outdir+"/W5");
    std::ofstream meta(outdir+"/meta5.txt");meta<<"T "<<T.states.size()<<" "<<T.col.size()<<"\nU "<<U.states.size()<<" "<<U.col.size()<<"\nW "<<W.states.size()<<" "<<W.col.size()<<"\n";
    auto sec=std::chrono::duration<double>(std::chrono::steady_clock::now()-t0).count();std::cout<<"seconds "<<sec<<"\n";
    return 0;
}
