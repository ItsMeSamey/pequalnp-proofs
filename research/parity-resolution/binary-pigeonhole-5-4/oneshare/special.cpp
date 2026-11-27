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
int low(Mask p){int n=0;for(auto l:labels)n+=bool(l&p);return n;}
struct Bounds{uint8_t lo=0,hi=61;};
unordered_map<Mask,Bounds> cache;
bool can(Mask p,int b){
 int l=low(p);if(l>b)return false;if(l<=1||__builtin_popcountll(p)<=b)return true;
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
void mark(Mask p,unordered_set<Mask>& visited){
 for(auto&tr:transforms){Mask im=0;for(int j=0;j<8;j++)im|=tr[j][(p>>(8*j))&255];visited.insert(im);}
}

Mask permute(Mask p,const array<array<Mask,256>,8>&tr){
 Mask im=0;for(int j=0;j<8;j++)im|=tr[j][(p>>(8*j))&255];return im;
}
unordered_map<Mask,Mask> canonSeen;
Mask canon(Mask p){
 auto it=canonSeen.find(p);if(it!=canonSeen.end())return it->second;
 for(auto&tr:transforms)canonSeen[permute(p,tr)]=p;return p;
}
unordered_map<Mask,Bounds> specCache;
bool special(Mask p,int b){
 if(low(p)>b)return false;
 p=canon(p);if(can(p,b))return true;
 auto it=specCache.find(p);if(it!=specCache.end()){if(it->second.lo>b)return false;if(it->second.hi<=b)return true;}
 // If the special question is at this vertex the subdomain on its YES side
 // ranges over exactly the nonempty proper affine subtraces of p.
 vector<const array<array<Mask,256>,8>*> stabilizer;
 for(auto&tr:transforms)if(permute(p,tr)==p)stabilizer.push_back(&tr);
 unordered_set<Mask> marked{p};vector<Mask> subs{p};
 for(size_t ix=0;ix<subs.size();ix++){
  Mask t=subs[ix];
  if(ix){
   for(int c=low(t);c<=b-low(p^t);c++)if(can(t,c)&&can(p^t,b-c)){
    auto &r=specCache[p];r.hi=min<int>(r.hi,b);return true;
   }
  }
  for(Mask q:qs){Mask a=q&t;for(Mask s:{a,t^a})if(s&&!marked.count(s)){
   subs.push_back(s);for(auto tr:stabilizer)marked.insert(permute(s,*tr));}}
 }
 // An ordinary first query leaves the special question available in one child.
 unordered_set<Mask> sides;
 for(Mask q:qs){Mask a=p&q;for(Mask u:{a,p^a})if(u&&u!=p&&!sides.count(u)){
  for(auto tr:stabilizer)sides.insert(permute(u,*tr));
  Mask v=p^u;for(int c=low(v);c<=b-low(u);c++)
   if(can(v,c)&&special(u,b-c)){auto &r=specCache[p];r.hi=min<int>(r.hi,b);return true;}
 }}
 auto &r=specCache[p];r.lo=max<int>(r.lo,b+1);return false;
}
int main(int argc,char**argv){
 initialize();int cap=argc>1?atoi(argv[1]):21;bool ok=special(F,cap);
 printf("budget %d feasible %d; %zu special cache domains, %zu ordinary cache domains\n",cap,ok,specCache.size(),cache.size());
}
