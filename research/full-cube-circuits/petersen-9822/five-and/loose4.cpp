#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;using M=uint32_t;
static const array<int,16> mis={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
static const int pos[]={6,24,17,33,66,132,264,528,160,640,576,320,288};
M all; M picked[10];int ng[10],atoms,profile,spare;
long long visited,banks,hit; vector<M>B,U;set<M> primitives;
int count(M m){return popcount(m);}
vector<M> uniq(vector<M>x){sort(x.begin(),x.end());x.erase(unique(x.begin(),x.end()),x.end());return x;}
using Rooms=array<M,16>;
bool allowed(const Rooms& rooms,int v,M m){
 for(int i=0;i<16;i++)if(!(rooms[i]&(mis[i]>>v&1?~m:m)))return false;
 return true;
}
struct Seed{int covered;array<M,10> masks;Rooms rooms;};
vector<Seed> seeds;
bool hall(const Rooms&r){
 for(auto z:r){int n=0;for(auto y:r)if(!(y&~z))n++;if(n>count(z))return false;}
 return true;
}
void seed(int chosen,const Seed& old){
 if(!chosen){seeds.push_back(old);return;}
 int v=countr_zero((unsigned)chosen);
 for(M m:B){
  if(!allowed(old.rooms,v,m))continue;
  auto next=old;next.covered|=1<<v;next.masks[v]=m;
  for(int j=0;j<16;j++)next.rooms[j]&=mis[j]>>v&1?~m:m;
  if(hall(next.rooms))seed(chosen^(1<<v),next);
 }
}
void prepare(int d){
 seeds.clear();Seed s{};s.rooms.fill(all);
 for(int D=0;D<1024;D++)if(popcount(unsigned(D))==d){
  bool ok=true;for(int e:pos)if((D&e)==e)ok=false;
  for(int t=D;t;t=(t-1)&D){
   int n=0;for(int I:mis)if(!(I&t))n++;
   if(n>(32>>popcount(unsigned(t))))ok=false;
  }
  if(ok)seed(D,s);
 }
}
void search(int done,int direct,int d,const Rooms& rooms,const vector<M>&cand,const vector<M>&mandatory){
 visited++;
 if(done==1023){
  if(direct!=d)return;
  int missing=0;for(auto u:mandatory)if(find(picked,picked+10,u)==picked+10)missing++;if(missing>spare)return;
  hit++;
  if(hit==1){cout<<"packing "<<profile<<" d "<<d<<" raw";for(auto x:picked)cout<<" "<<x;cout<<endl;}
  return;
 }
 int left=10-popcount(unsigned(done));int best=-1;vector<M> opts;
 for(int v=0;v<10;v++)if(!(done>>v&1)){
  vector<M> good;
  for(auto m:cand){
   int dd=primitives.count(m);
   if(direct+dd>d||direct+dd+left-1<d)continue;
   if(dd){bool miss=false;for(int k=0;k<10;k++)if((done&ng[v])>>k&1)if(primitives.count(picked[k]))miss=true;if(miss)continue;}
   bool bad=false;
   for(int k=0;k<10;k++)if(done>>k&1){
    M z=picked[k];
    if(!(m&~z)||!(z&~m)||((ng[v]>>k&1)&&((m|z)!=all))){bad=true;break;}
   }
   int neg=0;for(int I:mis)neg+=I>>v&1; if(count(all^m)<neg||count(m)<16-neg)continue;
   if(bad||!allowed(rooms,v,m))continue;
   good.push_back(m);
  }
  if(good.empty())return;
  if(best<0||good.size()<opts.size()){best=v;opts=move(good);}
 }
 for(auto m:opts){
  Rooms r;for(int j=0;j<16;j++)r[j]=rooms[j]&(mis[j]>>best&1?~m:m);
  // Witnesses for distinct maximal independent sets must be different trace atoms.
  bool bad=false;for(auto z:r){int n=0;for(auto y:r)if(!(y&~z))n++;if(n>count(z)){bad=true;break;}}
  if(bad)continue;
  picked[best]=m;search(done|(1<<best),direct+primitives.count(m),d,r,cand,mandatory);
  if(hit)return;
 }
}
void examine(int d,vector<M> help){
 banks++;
 vector<M>lib=B;lib.insert(lib.end(),help.begin(),help.end());
 vector<M>cand=B;
 for(int i=0;i<int(lib.size());i++)for(int j=0;j<i;j++)cand.push_back(lib[i]|lib[j]);
 cand=uniq(cand);cand.erase(remove_if(cand.begin(),cand.end(),[](M v){return !v||v==all;}),cand.end());
 vector<M>w;spare=d-2-int(help.size());
 for(auto x:U)if(x!=all&&find(lib.begin(),lib.end(),x)==lib.end()){

  w.push_back(x);
 }
 w=uniq(w);int missing=0;for(auto x:w)if(!binary_search(cand.begin(),cand.end(),x))missing++;if(missing>spare)return;
 for(const auto &q:seeds){
  if(hit)return;
  copy(q.masks.begin(),q.masks.end(),picked);search(q.covered,d,d,q.rooms,cand,w);
 }
}
int main(int argc,char**argv){
 for(int p:pos)for(int j=0;j<10;j++)if(p>>j&1)ng[j]|=p^(1<<j);
 ifstream f("/workspace/scratch/crown18264/algebra/reverse/canonfive.out");int d=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);
 array<M,5>u;for(profile=0;f>>u[0]>>u[1]>>u[2]>>u[3]>>u[4];profile++){
  if(profile<lo||profile>=hi)continue;
  B={};U={};all=0;set<int>seen;vector<int> reps;for(int p=0;p<32;p++){
   int t=0;for(int j=0;j<5;j++)if(u[j]>>p&1)t|=1<<(2*j+(p>>j&1));
   if(seen.insert(t).second)reps.push_back(p);
  }
  atoms=reps.size();if(atoms<16){cout<<profile<<" atoms "<<atoms<<" excluded"<<endl;continue;}
  all=atoms==32?~M(0):((M(1)<<atoms)-1);
  for(int j=0;j<5;j++){
   M a=0,b=0;for(int i=0;i<atoms;i++){int p=reps[i];if(u[j]>>p&1)(p>>j&1?b:a)|=M(1)<<i;}
   B.push_back(a);B.push_back(b);U.push_back(a|b);
  }
  B=uniq(B);primitives=set<M>(B.begin(),B.end());visited=banks=hit=0;
  prepare(d);if(seeds.empty()){cout<<profile<<" seeds 0 excluded"<<endl;continue;}
  vector<M> c={0};
  for(auto x:B){auto old=c;for(auto y:old)c.push_back(x|y);c=uniq(c);}
  vector<M> cand;for(auto x:c)if(x&&x!=all&&!primitives.count(x))cand.push_back(x);
  for(auto &q:seeds){copy(q.masks.begin(),q.masks.end(),picked);search(q.covered,d,d,q.rooms,cand,{});if(hit)break;}
  cout<<profile<<" atoms "<<atoms<<" seeds "<<seeds.size()<<" banks "<<banks<<" visits "<<visited<<" hits "<<hit<<endl;
 }
}
