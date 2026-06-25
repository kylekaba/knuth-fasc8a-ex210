#include <cstdint>
#include <iostream>
#include <vector>

// Independent Held--Karp count of Hamiltonian paths on the 5x4 knight graph.
// Directed paths are counted, then divided by two (path reversal).
int main() {
    constexpr int R=5, C=4, N=R*C;
    std::vector<uint32_t> adj(N,0);
    const int dr[8]={1,1,-1,-1,2,2,-2,-2};
    const int dc[8]={2,-2,2,-2,1,-1,1,-1};
    for(int r=0;r<R;r++) for(int c=0;c<C;c++) {
        int v=r*C+c;
        for(int k=0;k<8;k++) {
            int rr=r+dr[k],cc=c+dc[k];
            if(0<=rr&&rr<R&&0<=cc&&cc<C) adj[v]|=uint32_t(1)<<(rr*C+cc);
        }
    }
    const uint32_t S=uint32_t(1)<<N, full=S-1;
    std::vector<uint64_t> dp(size_t(S)*N,0);
    for(int v=0;v<N;v++) dp[(size_t(uint32_t(1)<<v))*N+v]=1;
    for(uint32_t mask=1;mask<S;mask++) {
        uint32_t rem=full^mask;
        for(int v=0;v<N;v++) {
            uint64_t a=dp[size_t(mask)*N+v];
            if(!a) continue;
            uint32_t q=adj[v]&rem;
            while(q) {
                int w=__builtin_ctz(q); q&=q-1;
                dp[size_t(mask|(uint32_t(1)<<w))*N+w]+=a;
            }
        }
    }
    uint64_t directed=0;
    for(int v=0;v<N;v++) directed+=dp[size_t(full)*N+v];
    std::cout << "directed 5x4 Hamiltonian paths = " << directed << "\n";
    std::cout << "undirected 5x4 Hamiltonian paths = " << directed/2 << "\n";
    return directed==164 ? 0 : 1;
}
