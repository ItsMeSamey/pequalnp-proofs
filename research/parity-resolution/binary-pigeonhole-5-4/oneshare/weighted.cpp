#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <unordered_map>
#include <unordered_set>
#include <vector>
using Mask=uint64_t;
using namespace std;
constexpr Mask F=(Mask(1)<<60)-1;
array<Mask,10> labels{};
vector<Mask> qs;
vector<array<array<Mask,256>,8>> transforms;
void initialize(){
 vector<array<int,5>> words;
 array<int,5>w={0,0,1,2,3};do{words.push_back(w);}while(next_permutation(w.begin(),w.end()));
 array<int,60> enc{};array<int,1024> idx{};
 for(int k=0;k<60;k++){
  int a=-1,b=-1;
  for(int i=0;i<5;i++){enc[k]|=words[k][i]<<(2*i);if(!words[k][i]){if(a<0)a=i;else b=i;}}
  idx[enc[k]]=k; labels[b*(b-1)/2+a]|=Mask(1)<<k;
 }
 unordered_set<Mask> splits;
 for(int t=1;t<1024;t++){Mask s=0;for(int k=0;k<60;k++) if(__builtin_parity(t&enc[k])) s|=Mask(1)<<k;
 if(s&&s!=F)splits.insert(min(s,s^F));}
 qs.assign(splits.begin(),splits.end()); sort(qs.begin(),qs.end());assert(qs.size()==255);
 array<int,5> p={0,1,2,3,4};do{array<int,4>h={0,1,2,3};do{
  transforms.emplace_back();auto &tr=transforms.back();
  array<int,60>im{};for(int k=0;k<60;k++){int val=0;for(int i=0;i<5;i++)val|=h[words[k][p[i]]]<<(2*i);im[k]=idx[val];}
  for(int j=0;j<8;j++)for(int v=1;v<256;v++){int l=__builtin_ctz(v)+8*j;tr[j][v]=tr[j][v&(v-1)]|(l<60?Mask(1)<<im[l]:0);}
 }while(next_permutation(h.begin()+1,h.end()));}while(next_permutation(p.begin(),p.end()));
}
int wt[10]; int low(Mask p){int n=0;for(int j=0;j<10;j++)if(labels[j]&p)n+=wt[j];return n;}
struct Bounds{uint8_t lo=0,hi=255;};
unordered_map<Mask,Bounds> cache;
bool can(Mask p,int b){
 int l=low(p);if(l>b)return false;int d=0; for(auto z:labels)d+=bool(z&p); if(d<=1)return true;
 auto it=cache.find(p);if(it!=cache.end()){if(it->second.lo>b)return false;if(it->second.hi<=b)return true;}
 vector<pair<int,Mask>> cand;
 for(Mask q:qs){Mask u=p&q,v=p^u;if(!u||!v)continue;
 int bound=low(u)+low(v);if(bound<=b)cand.emplace_back(bound,min(u,v));}
 sort(cand.begin(),cand.end()); cand.erase(unique(cand.begin(),cand.end()),cand.end());
 for(auto [lb,u]:cand){Mask v=p^u;if(__builtin_popcountll(u)>__builtin_popcountll(v))swap(u,v);
 int mv=low(v);
 for(int c=low(u);c<=b-mv;c++)if(can(u,c)&&can(v,b-c)){auto &r=cache[p];r.hi=min<int>(r.hi,b);return true;}}
 auto &r=cache[p];r.lo=max<int>(r.lo,b+1);return false;
}
int main(){initialize();bool seen[1024]={};for(int g=0;g<1024;g++){if(seen[g])continue;
 array<int,5> pm={0,1,2,3,4};do{int v=0;for(int i=0;i<5;i++)for(int j=0;j<i;j++)if(g>>(i*(i-1)/2+j)&1){int a=max(pm[i],pm[j]),b=min(pm[i],pm[j]);v|=1<<(a*(a-1)/2+b);}seen[v]=true;}while(next_permutation(pm.begin(),pm.end()));
 for(int j=0;j<10;j++)wt[j]=(g>>j&1)?1:4;cache.clear();int k=__builtin_popcount(g),lo=low(F)-1,hi=100;while(hi-lo>1){int b=(hi+lo)/2;if(can(F,b))hi=b;else lo=b;}printf("%d %d %d %d\n",g,k,hi,39+7*k+hi);fflush(stdout);}}
