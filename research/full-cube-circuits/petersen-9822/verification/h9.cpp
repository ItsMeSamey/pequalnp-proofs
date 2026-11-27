#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>
using namespace std;
using M=uint32_t;
int E[]={6,24,17,33,66,132,264,160,320,288};
int ind[]={42,50,77,108,116,139,201,208,261,276,387,402};
array<M,9> assigned;
vector<M> bases,pairs;
bool edge(int i,int j){return count(begin(E),end(E),(1<<i)|(1<<j));}
bool dfs(int used,int direct,array<M,12> rooms){
 if(used==511)return true;
 vector<M> best;int v=-1;
 for(int i=0;i<9;i++)if(!(used>>i&1)){
  vector<M> ok;
  for(auto x:((direct>>i&1)?bases:pairs)){
   bool good=true;
   for(int j=0;j<9;j++)if(used>>j&1){
    M y=assigned[j];if((((x|y)==~M(0))!=edge(i,j))||!(x&~y)||!(y&~x)){good=false;break;}
   }
   if(good)for(int k=0;k<12;k++)if(!(rooms[k]&((ind[k]>>i&1)?~x:x))){good=false;break;}
   if(good)ok.push_back(x);
  }
  if(ok.empty())return false;
  if(v<0||ok.size()<best.size()){v=i;best=ok;}
 }
 for(M x:best){auto next=rooms;for(int k=0;k<12;k++)next[k]&=(ind[k]>>v&1)?~x:x;
  assigned[v]=x;if(dfs(used|(1<<v),direct,next))return true;}
 return false;
}
void uniq(vector<M>&l){sort(l.begin(),l.end());l.erase(unique(l.begin(),l.end()),l.end());}
int main(){array<M,5>u;int profiles=0,cases=0;
 while(cin>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]){
  ++profiles;bases.clear();pairs.clear();
  for(int j=0;j<5;j++){M h=0;for(int w=0;w<32;w++)if(w>>j&1)h|=M(1)<<w;bases.push_back(h&u[j]);bases.push_back(~h&u[j]);}
  uniq(bases);for(M x:bases)for(M y:bases){M z=x|y;if(z!=~M(0)&&!count(bases.begin(),bases.end(),z))pairs.push_back(z);}uniq(pairs);
  for(int d:ind)if(popcount(unsigned(d))==4){++cases;array<M,12>rooms;rooms.fill(~M(0));if(dfs(0,d,rooms)){cout<<"HIT "<<profiles<<" "<<d;for(auto x:assigned)cout<<" "<<x;cout<<endl;return 1;}}
 }
 cout<<profiles<<" profiles "<<cases<<" cases zero hits"<<endl;
}
