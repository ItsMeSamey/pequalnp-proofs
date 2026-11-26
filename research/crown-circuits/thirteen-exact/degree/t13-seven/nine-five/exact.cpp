#include <iostream>
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;constexpr M F=~M(0);
M halfs[6]={0xaaaaaaaaaaaaaaaaULL,0xccccccccccccccccULL,0xf0f0f0f0f0f0f0f0ULL,0xff00ff00ff00ff00ULL,0xffff0000ffff0000ULL,0xffffffff00000000ULL};
struct Bank{
 array<M,6> U;
 vector<M> B,W,H,lib,raw;
 M leaf=0;int L=0,ix=0;long long banks=0,fronts=0;
 bool chrono(){
  set<M> known{F};bool go=true;while(go){go=false;
   for(int j=0;j<6;j++)if(known.count(U[j]))for(M b:{U[j]&halfs[j],U[j]&~halfs[j]})if(known.insert(b).second)go=true;
   vector<M> v(known.begin(),known.end());for(auto a:v)for(auto b:v)if(a<b){
    M z=a|b;if((find(W.begin(),W.end(),z)!=W.end()||find(H.begin(),H.end(),z)!=H.end())&&known.insert(z).second)go=true;
   }
  }
  for(auto u:U)if(u&&!known.count(u))return false;for(auto h:H)if(!known.count(h))return false;return true;
 }
 bool fit(vector<M> const& ds,int need,M free){
  if(need==0){
   for(int axis=0;axis<6;axis++)if(U[axis])for(M side:{halfs[axis],~halfs[axis]}){int count=0;for(M d:raw)count+=!(d&~side);if(count<2)return false;}
   for(M w:U)if(w!=F){bool hot=false;for(M d:raw)if(!(w&d)){hot=true;break;}if(!hot)return false;}
   return chrono();
  }
  if((int)ds.size()<need||popcount(free&leaf)<need)return false;
  int volume=0;for(int k=0;k<need;k++)volume+=popcount(ds[k]&leaf);if(volume>popcount(free&leaf))return false;
  for(int i=0;i<=(int)ds.size()-need;i++){
   M d=ds[i];vector<M> next;for(int j=i+1;j<(int)ds.size();j++)if(!(d&ds[j]))next.push_back(ds[j]);
   raw.push_back(d);if(fit(next,need-1,free&~d))return true;raw.pop_back();
  }return false;
 }
 bool pack(){
  vector<M> d;
  for(int i=0;i<(int)lib.size();i++)for(int j=0;j<i;j++){M z=lib[i]|lib[j];if(z==lib[i]||z==lib[j]||z==F)continue;
   if(find(B.begin(),B.end(),z)!=B.end()||find(U.begin(),U.end(),z)!=U.end())continue;
   M x=~z;if(popcount(x&leaf)>L-8)continue;d.push_back(x);
  }
  sort(d.begin(),d.end(),[&](M a,M b){if(popcount(a&leaf)!=popcount(b&leaf))return popcount(a&leaf)<popcount(b&leaf);return a<b;});d.erase(unique(d.begin(),d.end()),d.end());
  vector<M> minimal;for(M x:d){bool ok=true;for(M y:minimal)if((x&y)==y){ok=false;break;}if(ok)minimal.push_back(x);}
  if(minimal.size()<9)return false;
  for(M w:U)if(w!=F){bool exists=false;for(M x:minimal)if(!(w&x))exists=true;if(!exists)return false;}
  ++fronts;return fit(minimal,9,F);
 }
 bool go(int left){
  if(!left){banks++;return pack();}
  auto rank=[](M a,M b){int p=popcount(a),q=popcount(b);return p!=q?p<q:a<b;};
  vector<M> choices;for(int i=0;i<(int)lib.size();i++)for(int j=0;j<i;j++){M z=lib[i]|lib[j];
   if(z==F||(!H.empty()&&!rank(H.back(),z))||find(lib.begin(),lib.end(),z)!=lib.end())continue;choices.push_back(z);}
  sort(choices.begin(),choices.end());choices.erase(unique(choices.begin(),choices.end()),choices.end());
  // A solution may use fewer than the allowed helper budget.
  banks++;if(pack())return true;
  for(M z:choices){H.push_back(z);lib.push_back(z);if(go(left-1))return true;lib.pop_back();H.pop_back();}return false;
 }
 bool init(int minW,int maxW,int minF,int maxF){
  int fs=count(U.begin(),U.end(),F);if(fs<minF||fs>maxF)return false;
  for(int j=0;j<6;j++){B.push_back(U[j]&halfs[j]);B.push_back(U[j]&~halfs[j]);}
  for(M z:U)if(z!=F&&find(B.begin(),B.end(),z)==B.end()&&find(W.begin(),W.end(),z)==W.end())W.push_back(z);
  if(W.size()<minW||W.size()>maxW)return false;
  set<int> sig;for(int p=0;p<64;p++){int s=0;for(int k=0;k<12;k++)s|=(B[k]>>p&1)<<k;if(sig.insert(s).second){leaf|=M(1)<<p;L++;}}
  lib=B;lib.insert(lib.end(),W.begin(),W.end());
  bool ok=go(4-W.size());
  printf("%d %d %zu %lld %lld\n",ix,ok,W.size(),banks,fronts);fflush(stdout);
  if(ok){fprintf(stderr,"WITNESS %d",ix);for(M h:H)fprintf(stderr," %llu",(unsigned long long)h);fprintf(stderr," /");for(M d:raw)fprintf(stderr," %llu",(unsigned long long)~d);fputc('\n',stderr);fflush(stderr);}
  return true;
 }
};
int main(int argc,char**argv){int minW=argc>1?atoi(argv[1]):3,maxW=argc>2?atoi(argv[2]):5,minF=argc>3?atoi(argv[3]):1,maxF=argc>4?atoi(argv[4]):6;
 int i;array<M,6>u;while(cin>>i>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]) {Bank b;b.U=u;b.ix=i;b.init(minW,maxW,minF,maxF);}}
