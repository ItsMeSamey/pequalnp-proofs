#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;
array<M,6> half;
M flip(M m,int d){
 for(int j=0;j<6;j++)if(d>>j&1){int k=1<<j;M lo=~half[j];m=((m&lo)<<k)|((m&half[j])>>k);}return m;
}
vector<M> gates,br,mandatory;
int nlabels,maxpaid;
void grow(vector<int> const& stabilizer){
 int d=gates.size();
 if(d==5){
   array<int,64> sig{};for(unsigned p=0;p<64;p++)for(unsigned k=0;k<10;k++)sig[p]|=int(br[k]>>p&1)<<k;
   sort(sig.begin(),sig.end());if(unique(sig.begin(),sig.end())-sig.begin()<nlabels)return;
   for(M x:gates)printf("%llu ",(unsigned long long)x);puts("0");return;
 }
 set<M> pool{0};for(M b:br){auto old=pool;for(M a:old)pool.insert(a|b);}pool.insert(~M(0));
 for(M u:pool)if(u){
  bool fresh=u!=~M(0)&&find(br.begin(),br.end(),u)==br.end()&&find(mandatory.begin(),mandatory.end(),u)==mandatory.end();
  if(fresh&&(int)mandatory.size()>=maxpaid)continue;
  vector<int> next;bool canonical=true;
  for(int s:stabilizer){M w=flip(u,s);if(w<u){canonical=false;break;}if(w==u)next.push_back(s);}
  if(!canonical)continue;
  gates.push_back(u);br.push_back(u&half[d]);br.push_back(u&~half[d]);if(fresh)mandatory.push_back(u);
  grow(next);
  if(fresh)mandatory.pop_back();br.pop_back();br.pop_back();gates.pop_back();
 }
}
int main(int argc,char**argv){
 nlabels=atoi(argv[1]);maxpaid=atoi(argv[2]);
 for(int j=0;j<6;j++)for(int p=0;p<64;p++)if(p>>j&1)half[j]|=M(1)<<p;
 vector<int> group(64);for(int i=0;i<64;i++)group[i]=i;
 grow(group);
}
