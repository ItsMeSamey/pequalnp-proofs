#include <algorithm>
#include <array>
#include <cstdio>
#include <set>
#include <cstdint>
#include <vector>
using namespace std;using M=unsigned long long;using T=array<M,6>;
M flip(M m,int d){for(int j=0;j<6;j++)if(d>>j&1){constexpr M low[]={0x5555555555555555ULL,0x3333333333333333ULL,0x0f0f0f0f0f0f0f0fULL,0x00ff00ff00ff00ffULL,0x0000ffff0000ffffULL,0x00000000ffffffffULL};int k=1<<j;m=((m&low[j])<<k)|((m&~low[j])>>k);}return m;}
int main(){
  struct perm {array<int,6> idx;array<array<M,256>,8> tab;};
  vector<perm> ps;
  array<int,6> idx{0,1,2,3,4,5};do{
    perm p{};p.idx=idx;
    for(int i=0;i<64;i++){int u=0;for(int j=0;j<6;j++)u|=(i>>j&1)<<idx[j];for(int v=0;v<256;v++)if(v>>(i%8)&1)p.tab[i/8][v]|=M(1)<<u;}
    ps.push_back(p);
  }while(next_permutation(idx.begin(),idx.end()));
  set<T> seen;T input;
  while(scanf("%llu %llu %llu %llu %llu %llu",&input[0],&input[1],&input[2],&input[3],&input[4],&input[5])==6){
    array<int,6> weights{},sorted{};for(int j=0;j<6;j++)weights[j]=__builtin_popcountll(input[j]);sorted=weights;sort(sorted.begin(),sorted.end(),greater<int>());T best;best.fill(~M(0));
    for(auto const& p:ps){
      bool ok=true;for(int j=0;j<6;j++)if(weights[j]!=sorted[p.idx[j]])ok=false;if(!ok)continue;T b{};for(int j=0;j<6;j++){M x=input[j];for(int k=0;k<8;k++)b[p.idx[j]]|=p.tab[k][(x>>(8*k))&255];}
      for(int d=0;d<64;d++){T v;bool skip=false;for(int j=0;j<6;j++){v[j]=flip(b[j],d);if(v[j]!=best[j]){if(v[j]>best[j])skip=true;else for(int k=j+1;k<6;k++)v[k]=flip(b[k],d);break;}}if(!skip)best=v;}
    }
    if(seen.insert(best).second)printf("%llu %llu %llu %llu %llu %llu\n",input[0],input[1],input[2],input[3],input[4],input[5]);
  }
}
