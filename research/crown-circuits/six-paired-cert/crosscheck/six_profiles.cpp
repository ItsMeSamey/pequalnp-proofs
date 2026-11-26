#include <cstdlib>
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;
M flip(M m,int d){for(int j=0;j<6;j++)if(d>>j&1){constexpr M low[]={0x5555555555555555ULL,0x3333333333333333ULL,0x0f0f0f0f0f0f0f0fULL,0x00ff00ff00ff00ffULL,0x0000ffff0000ffffULL,0x00000000ffffffffULL};int k=1<<j;m=((m&low[j])<<k)|((m&~low[j])>>k);}return m;}
M half[6];
vector<M> gates,branches;int terminals;
void grow(vector<int> const& stab){
 int j=gates.size();
 if(j==6){
  // Each raw requires a distinct trace; finding it requires a witness
  // visible by the complete set of the split's selected endpoints.
  array<int,64> signatures{};for(int p=0;p<64;p++)for(int s=0;s<12;s++)signatures[p]|=int(branches[s]>>p&1)<<s;
  sort(signatures.begin(),signatures.end());
  if(unique(signatures.begin(),signatures.end())-signatures.begin()<12)return;
  for(auto m:gates)printf("%llu ",(unsigned long long)m);puts("");return;
 }
 set<M> closure{0};for(M b:branches){auto prev=closure;for(M u:prev)closure.insert(u|b);}closure.insert(~M(0));
 for(M u:closure)if(u && (j<terminals ? u==~M(0) : u!=~M(0))){
  vector<int> rest;
  bool min=true;for(int d:stab){M v=flip(u,d);if(v<u){min=false;break;}if(v==u)rest.push_back(d);}
  if(!min)continue;
  branches.push_back(u&half[j]);branches.push_back(u&~half[j]);gates.push_back(u);
  grow(rest);gates.pop_back();branches.pop_back();branches.pop_back();
 }
}
int main(int argc,char**argv){terminals=argc>1?atoi(argv[1]):1;for(int j=0;j<6;j++)for(int i=0;i<64;i++)if(i>>j&1)half[j]|=M(1)<<i;vector<int> group;for(int i=0;i<64;i++)group.push_back(i);grow(group);}
