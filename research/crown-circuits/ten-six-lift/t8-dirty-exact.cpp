#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>
using namespace std;
struct Term { int m,v; };
struct Search {
 vector<int> target; int first; int stage[4096],key[4096],volume[4096],close[4096],critical[4096];
 vector<int> bank,helpers,chosen;
 long long banks=0,fronts=0;
 Search(vector<int> T):target(T),first(6-T.size()) {
  for(int m=0;m<4096;m++){
   int v=m;
   for(int j=first;j<6;j++)if(((v>>(2*j))&3)==3)v|=target[j-first];
   close[m]=v;
   stage[m]=0;for(int t:target)stage[m]=2*stage[m]+((m&~t)!=0);
   key[m]=(stage[m]*16+popcount((unsigned)m))*4096+m;
   volume[m]=0;
  }
  for(int m=0;m<4096;m++){
   critical[m]=0;
   if(hit(m,m))continue;
   for(int j=0;j<6;j++){
    int bits=(close[m]>>(2*j))&3;
    if(bits!=1&&bits!=2)continue;
    if(j<first||hit(m|target[j-first],m|target[j-first]))critical[m]|=bits<<(2*j);
   }
  }
  for(int z=0;z<64;z++){
   int blocked=0;
   for(int j=0;j<first;j++)blocked|=1<<(2*j+((z>>j)&1));
   for(int j=5;j>=first;j--)if(blocked&target[j-first])blocked|=1<<(2*j+((z>>j)&1));
   volume[4095^blocked]++;
  }
  for(int b=1;b<4096;b*=2)for(int m=0;m<4096;m++)if(!(m&b))volume[m]+=volume[m|b];
  for(int i=0;i<12;i++)bank.push_back(1<<i);
 }
 bool hit(int a,int b) const {int v=close[a|b];return (v&(v>>1)&(((1<<(2*first))-1)/3))!=0;}
 bool has(int x) const{return find(bank.begin(),bank.end(),x)!=bank.end();}
 array<int,6> stamp(int x) const{
  array<int,6> out{};
  for(int j=0;j<6;j++){
   int a=0,b=0;
   auto add=[&](int m){a=a*2+((m>>(2*j))&1);b=b*2+((m>>(2*j+1))&1);};
   for(int t:target)add(t);for(int m:helpers)add(m);add(x);
   out[j]=min(a,b)*2048+max(a,b);
  }
  sort(out.begin(),out.begin()+first);return out;
 }
 bool receivers(const vector<Term>&t,int first,int left,int space){
  if(!left){
   int used=0,hot=0;for(int t:target)used|=t;
   for(int m:chosen){used|=m;for(int j=this->first;j<6;j++)if(((close[m]>>(2*j))&3)==3)hot|=1<<j;}
   return used==4095 && hot==(64-(1<<this->first));
  }
  for(int i=first;i+left<=(int)t.size();i++){
   if(left*t[i].v>space)break;
   bool ok=true;for(int m:chosen)if(!hit(t[i].m,m)){ok=false;break;}
   if(ok){chosen.push_back(t[i].m);if(receivers(t,i+1,left-1,space-t[i].v))return true;chosen.pop_back();}
  }
  return false;
 }
 bool run(int last){
  banks++;
  vector<int> joins;
  for(int i=0;i<(int)bank.size();i++)for(int j=0;j<i;j++){
   int m=bank[i]|bank[j];if(m!=bank[i]&&m!=bank[j]&&!hit(m,m))joins.push_back(m);
  }
  sort(joins.begin(),joins.end());joins.erase(unique(joins.begin(),joins.end()),joins.end());
  if(all_of(target.begin(),target.end(),[&](int t){return has(t);})){
   vector<int> bysize=joins;sort(bysize.begin(),bysize.end(),[](int a,int b){return popcount((unsigned)a)>popcount((unsigned)b);});
   vector<Term> t;
   for(int m:bysize)if(none_of(t.begin(),t.end(),[&](const Term&a){return (m&a.m)==m;}))t.push_back({m,volume[m]});
   sort(t.begin(),t.end(),[](const Term&a,const Term&b){return a.v<b.v;});
   int total=0,possible=0;for(auto z:t)possible|=critical[z.m];for(int i=0;i<min(8,(int)t.size());i++)total+=t[i].v;
   if(possible==4095&&t.size()>=8&&total<=64){fronts++;if(receivers(t,0,8,64)){printf("H");for(int m:helpers)printf(" %d",m);printf(" R");for(int m:chosen)printf(" %d",m);puts("");return true;}}
  }
  if(helpers.size()==4)return false;
  set<array<int,6>> seen;
  for(int m:joins){
   if(key[m]<=last||has(m))continue;
   if(any_of(target.begin(),target.end(),[&](int t){return !has(t)&&key[t]<key[m];}))continue;
   if(!seen.insert(stamp(m)).second)continue;
   bank.push_back(m);helpers.push_back(m);if(run(key[m]))return true;helpers.pop_back();bank.pop_back();
  }
  return false;
 }
};
int main(int argc,char**argv){
 vector<int>T;for(int i=1;i<argc;i++)T.push_back(atoi(argv[i]));Search S(T);
 bool valid=true;for(int t:T)if(S.hit(t,t))valid=false;
 bool hit=valid&&S.run(-1);for(int t:T)printf("%d ",t);
 printf("valid %d hit %d banks %lld fronts %lld\n",valid,hit,S.banks,S.fronts);
}
