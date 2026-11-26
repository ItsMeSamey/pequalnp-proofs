#include <cstdio>
#include <cstdint>
#include <vector>
#include <array>
#include <algorithm>
using namespace std;
int par(unsigned x){return __builtin_parity(x);}
bool singleton(int own,int B){
 for(int h=1;h<8;h++){
  int piv[5]={};
  auto add=[&](int x){while(x){int k=31-__builtin_clz(x);if(!piv[k]){piv[k]=x;return;}x^=piv[k];}};
  for(int u=0;u<8;u++){
   if((own>>u&1)&&par(u&h))add((u&h)|8);
   if((B>>(u+8*par(u&h)))&1)add((u&h)|16);
  }
  int x=8;while(x&&piv[31-__builtin_clz(x)])x^=piv[31-__builtin_clz(x)];
  if(!x)return true;
 }
 return false;
}
vector<unsigned> cubes[256];
void precompute(){
 for(int own=1;own<256;own++){
  vector<char> good(65536);
  for(int b=0;b<65536;b++){
   // If an immediate subset works then so does this mask.
   for(int x=b;x&&!good[b];x&=x-1)good[b]|=good[b^(x&-x)];
   if(!good[b])good[b]=singleton(own,b);
  }
  for(int b=0;b<65536;b++)if(!good[b]){
   bool maximal=true;
   for(int x=65535^b;x;x&=x-1)if(!good[b|(x&-x)]){maximal=false;break;}
   if(maximal)cubes[own].push_back(b);
  }
 }
}

struct basis{
 int piv[9]={};
 int reduce(int v){while(v&&piv[31-__builtin_clz(v)])v^=piv[31-__builtin_clz(v)]; return v;}
 void add(int v){v=reduce(v);if(v)piv[31-__builtin_clz(v)]=v;}
};
bool attainable(int own,int opp,int odd,int c){
 vector<pair<int,int>> valid;
 int flexible=0;
 for(int b:cubes[own]){
  int zero=b&255,one=b>>8;
  if(opp&~(zero|one))continue;
  int free=opp&zero&one, fixed=opp&one&~zero;
  if(!free && par(fixed&odd)!=(1^c))continue;
  flexible|=free;
  valid.emplace_back(free,fixed);
 }
 basis B;
 int keep=opp&(~flexible|odd);
 for(auto [free,fixed]: valid){
  int r=fixed&keep;
  int lead=free&-free;
  if(par(fixed&odd)!=(1^c))r|=lead;
  B.add(r|256);
  for(int tail=free^lead;tail;tail&=tail-1)B.add(lead|(tail&-tail));
 }
 int parityOfSignature=0x96; // bits 1,2,4,7
 return !B.reduce(((c?~parityOfSignature:parityOfSignature)&keep)|(c?0:256));
}
int main(){
 precompute();
 int xsum[256]={};
 for(int e=1;e<256;e++)xsum[e]=xsum[e&(e-1)]^__builtin_ctz(e);
 long long profiles=0, checked=0; int total_cubes=0, max_cubes=0;
 for(auto &v:cubes){total_cubes += v.size(); max_cubes=max(max_cubes,(int)v.size());}
 for(int left=1;left<256;left++)for(int right=1;right<256;right++){
  for(int o=left;o;o=(o-1)&left)if(par(o)&&par(xsum[o])){
   bool p1=attainable(right,left,o,1);
   for(int p=right;p;p=(p-1)&right)if(!par(p)&&xsum[p]==xsum[o]){
    profiles++; if(!p1)continue; checked++;
    if(attainable(left,right,p,0)){
     printf("COUNTER supports %d %d odd %d %d\n",left,right,o,p);return 1;
    }
   }
  }
 }
 printf("%d maximal cubes, max %d; %lld profiles; %lld after P1; no counterexample\n",total_cubes,max_cubes,profiles,checked);
}
