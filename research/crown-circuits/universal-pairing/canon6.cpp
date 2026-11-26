#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <map>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;using A=array<M,6>;
array<M,6> halves;
M flip(M m,int d){for(int j=0;j<6;j++)if(d>>j&1){int k=1<<j;m=((m&~halves[j])<<k)|((m&halves[j])>>k);}return m;}
struct Perm{array<int,6> to;array<array<M,256>,8> tab;};
int main(){
 for(int j=0;j<6;j++)for(int p=0;p<64;p++)if(p>>j&1)halves[j]|=M(1)<<p;
 vector<Perm> maps;array<int,6> idx{0,1,2,3,4,5};do{
  Perm p{};p.to=idx;
  for(int i=0;i<64;i++){int x=0;for(int j=0;j<6;j++)x|=(i>>j&1)<<idx[j];for(int v=0;v<256;v++)if(v>>(i%8)&1)p.tab[i/8][v]|=M(1)<<x;}
  maps.push_back(p);
 }while(next_permutation(idx.begin(),idx.end()));
 set<A> seen;unsigned long long line[6];
 while(scanf("%llu %llu %llu %llu %llu %llu",line,line+1,line+2,line+3,line+4,line+5)==6){
  A in{};copy(line,line+6,in.begin());
  array<int,6> color{};array<array<int,6>,6> infl{};
  for(int i=0;i<6;i++){color[i]=popcount(in[i]);for(int j=0;j<6;j++)infl[i][j]=popcount(in[i]^flip(in[i],1<<j));}
  for(int round=0;round<3;round++){
   array<vector<int>,6> signatures;
   for(int i=0;i<6;i++){
    auto& s=signatures[i];s.push_back(color[i]);vector<array<int,3>> links;
    for(int j=0;j<6;j++)links.push_back({color[j],infl[i][j],infl[j][i]});
    sort(links.begin(),links.end());for(auto e:links)s.insert(s.end(),e.begin(),e.end());
   }
   auto sorted=signatures;sort(sorted.begin(),sorted.end());
   for(int i=0;i<6;i++)color[i]=int(lower_bound(sorted.begin(),sorted.end(),signatures[i])-sorted.begin());
  }
  auto ordered=color;sort(ordered.begin(),ordered.end());
  A best;best.fill(~M(0));
  for(auto const&p:maps){
   bool ok=true;for(int i=0;i<6;i++)if(color[i]!=ordered[p.to[i]]){ok=false;break;}if(!ok)continue;
   A renamed{};for(int i=0;i<6;i++)for(int k=0;k<8;k++)renamed[p.to[i]]|=p.tab[k][(in[i]>>(8*k))&255];
   for(int d=0;d<64;d++){A v{};bool smaller=false;
    for(int j=0;j<6;j++){v[j]=flip(renamed[j],d);if(!smaller&&v[j]>best[j])break;if(v[j]<best[j])smaller=true;if(j==5&&smaller)best=v;}
   }
  }
  if(seen.insert(best).second){for(auto x:line)printf("%llu ",x);puts("");}
 }
}
