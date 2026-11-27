#include <algorithm>
#include <array>
#include <cstdio>
#include <set>
#include <cstdint>
#include <vector>
using namespace std;using M=uint32_t;using T=array<M,5>;
M flip(M m,int d){for(int j=0;j<5;j++)if(d>>j&1){constexpr M low[]={0x55555555,0x33333333,0x0f0f0f0f,0x00ff00ff,0x0000ffff};int k=1<<j;m=((m&low[j])<<k)|((m&~low[j])>>k);}return m;}
int main(){
  struct perm {array<int,5> idx;array<array<M,256>,4> tab;};
  vector<perm> ps;
  array<int,5> idx{0,1,2,3,4};do{
    perm p{};p.idx=idx;
    for(int i=0;i<32;i++){int u=0;for(int j=0;j<5;j++)u|=(i>>j&1)<<idx[j];for(int v=0;v<256;v++)if(v>>(i%8)&1)p.tab[i/8][v]|=M(1)<<u;}
    ps.push_back(p);
  }while(next_permutation(idx.begin(),idx.end()));
  set<T> seen;T input;
  while(scanf("%u %u %u %u %u",&input[0],&input[1],&input[2],&input[3],&input[4])==5){
    T best;best.fill(~M(0));
    for(auto const& p:ps){
      T b{};for(int j=0;j<5;j++){M x=input[j];for(int k=0;k<4;k++)b[p.idx[j]]|=p.tab[k][(x>>(8*k))&255];}
      for(int d=0;d<32;d++){T v;bool skip=false;for(int j=0;j<5;j++){v[j]=flip(b[j],d);if(v[j]!=best[j]){if(v[j]>best[j])skip=true;else for(int k=j+1;k<5;k++)v[k]=flip(b[k],d);break;}}if(!skip)best=v;}
    }
    if(seen.insert(best).second)printf("%u %u %u %u %u\n",input[0],input[1],input[2],input[3],input[4]);
  }
}
