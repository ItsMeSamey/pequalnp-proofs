#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;using M=uint32_t;
M flip(M m,int d){for(int j=0;j<5;j++)if(d>>j&1){constexpr M low[]={0x55555555,0x33333333,0x0f0f0f0f,0x00ff00ff,0x0000ffff};int k=1<<j;m=((m&low[j])<<k)|((m&~low[j])>>k);}return m;}
M half[5]={0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000};
vector<M> gates,branches;
void grow(vector<int> const& stab){
 int j=gates.size();
 if(j==5){
  // Each raw requires a distinct trace; finding it requires a witness
  // visible by the complete set of the split's selected endpoints.
  array<int,32> signatures{};for(int p=0;p<32;p++)for(int s=0;s<10;s++)signatures[p]|=int(branches[s]>>p&1)<<s;
  sort(signatures.begin(),signatures.end());
  if(unique(signatures.begin(),signatures.end())-signatures.begin()<12)return;
  for(auto m:gates)printf("%u ",m);puts("");return;
 }
 set<M> closure{0};for(M b:branches){auto prev=closure;for(M u:prev)closure.insert(u|b);}closure.insert(~M(0));
 for(M u:closure)if(u){
  vector<int> rest;
  bool min=true;for(int d:stab){M v=flip(u,d);if(v<u){min=false;break;}if(v==u)rest.push_back(d);}
  if(!min)continue;
  branches.push_back(u&half[j]);branches.push_back(u&~half[j]);gates.push_back(u);
  grow(rest);gates.pop_back();branches.pop_back();branches.pop_back();
 }
}
int main(){vector<int> group;for(int i=0;i<32;i++)group.push_back(i);grow(group);}
