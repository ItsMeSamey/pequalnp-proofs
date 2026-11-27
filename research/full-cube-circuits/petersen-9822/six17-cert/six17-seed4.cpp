#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;using M=uint64_t;
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
vector<vector<M>> sym;
void symmetries(const array<M,6>&u,const vector<int>&reps){
 sym.clear();set<M> acts(u.begin(),u.end());
 auto mapped=[](M m,const array<int,64>&perm){M y=0;while(m){int k=countr_zero(m);m&=m-1;y|=M(1)<<perm[k];}return y;};
 vector<M> raw;
 for(int j=0;j<6;j++){M b=0;for(int k=0;k<64;k++)if(k>>j&1)b|=M(1)<<k;raw.push_back(b&u[j]);raw.push_back(~b&u[j]);}
 set<M> bs(raw.begin(),raw.end());
 auto compact=[&](M m){M y=0;for(int k=0;k<int(reps.size());k++)if(m>>reps[k]&1)y|=M(1)<<k;return y;};
 for(int j=0;j<6;j++)for(int l=j;l<6;l++){array<int,64>pi{};
  for(int k=0;k<64;k++)pi[k]=j==l?(k^(1<<j)):((k>>j^k>>l)&1?k^(1<<j)^(1<<l):k);
  bool ok=true;for(auto x:bs)if(!bs.count(mapped(x,pi)))ok=false;for(auto x:acts)if(mapped(x,pi)!=x)ok=false;if(!ok)continue;
  vector<M> sm;for(auto x:B){auto it=find_if(raw.begin(),raw.end(),[&](M v){return compact(v)==x;});sm.push_back(compact(mapped(*it,pi)));}sym.push_back(sm);
 }
}
void seed(int chosen,const Seed& old){
 if(!chosen){seeds.push_back(old);return;}
 int v=countr_zero((unsigned)chosen);
 for(M m:B){
  bool small=true;int ix=lower_bound(B.begin(),B.end(),m)-B.begin();
  for(auto &sm:sym)if(sm[ix]<m){bool fixes=true;for(int k=0;k<10;k++)if(old.covered>>k&1){auto x=old.masks[k];if(sm[lower_bound(B.begin(),B.end(),x)-B.begin()]!=x)fixes=false;}if(fixes)small=false;}
  if(!small||!allowed(old.rooms,v,m))continue;
  auto next=old;next.covered|=1<<v;next.masks[v]=m;
  for(int j=0;j<16;j++)next.rooms[j]&=mis[j]>>v&1?~m:m;
  if(hall(next.rooms))seed(chosen^(1<<v),next);
 }
}
void prepare(int d){
 seeds.clear();Seed s{};s.rooms.fill(all);
 for(int D=0;D<1024;D++)if(popcount(unsigned(D))==d){
  int reflect=0,ga[]={3,2,1,0,4,8,7,6,5,9};for(int i=0;i<10;i++)if(D>>i&1)reflect|=1<<ga[i];if(reflect<D)continue;
  bool ok=true;for(int e:pos)if((D&e)==e)ok=false;
  for(int t=D;t;t=(t-1)&D){
   int n=0;for(int I:mis)if(!(I&t))n++;
   if(n>(64>>popcount(unsigned(t))))ok=false;
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
vector<M>wr,pool4;
int qverts=0;
long long completeSeeds=0;
bool canput(int v,M m,int cover,const Rooms&r,Rooms&rr){
 for(int u=0;u<10;u++)if(cover>>u&1){M other=picked[u];if(!(m&~other)||!(other&~m)||bool((m|other)==all)!=bool(ng[v]>>u&1))return false;}
 for(int j=0;j<16;j++){rr[j]=r[j]&(mis[j]>>v&1?~m:m);if(!rr[j])return false;}
 return hall(rr);
}
void nearseed(int D,int cover,const Rooms& r){
 if(!D){
  completeSeeds++;
  search(cover,4,4,r,pool4,{});
  return;
 }
 int v=countr_zero(unsigned(D));
 Rooms rr;
 for(int k=0;k<int(B.size());k++){
  bool good=true;
  for(auto &sm:sym)if(sm[k]<B[k]){
   bool stable=true;for(int a=0;a<10;a++)if((cover&qverts)>>a&1){M m=picked[a];if(sm[lower_bound(B.begin(),B.end(),m)-B.begin()]!=m)stable=false;}
   if(stable){good=false;break;}
  }
  if(good&&canput(v,B[k],cover,r,rr)){picked[v]=B[k];nearseed(D^(1<<v),cover|(1<<v),rr);if(hit)return;}
 }
}
void named(int k,int D,int cover,const Rooms&r){
 if(k==int(wr.size())){nearseed(D,cover,r);return;}
 Rooms rr;
 for(int v=0;v<10;v++)if(!((D|cover)>>v&1)&&canput(v,wr[k],cover,r,rr)){
  picked[v]=wr[k];named(k+1,D,cover|(1<<v),rr);if(hit)return;
 }
}
void coarseAll(){
 wr={};for(auto x:U)if(x!=all&&!primitives.count(x))wr.push_back(x);wr=uniq(wr);
 vector<M> c={0};for(int d=0;d<4;d++){auto old=c;for(auto x:B)for(auto y:old)c.push_back(x|y);c=uniq(c);}
 for(auto w:wr)if(!binary_search(c.begin(),c.end(),w))return;
 pool4={};for(auto x:c)if(x&&x!=all&&!primitives.count(x))pool4.push_back(x);
 Rooms r;r.fill(all);int ga[]={3,2,1,0,4,8,7,6,5,9};
 for(int D=0;D<1024;D++)if(popcount(unsigned(D))==4){
  bool use=true;int reflect=0;for(int i=0;i<10;i++)if(D>>i&1)reflect|=1<<ga[i];
  for(int e:pos)if((D&e)==e)use=false;
  if(use&&reflect>=D){qverts=D;named(0,D,0,r);if(hit)return;}
 }
}
int main(int argc,char**argv){
 for(int p:pos)for(int j=0;j<10;j++)if(p>>j&1)ng[j]|=p^(1<<j);
 set<int> active;ifstream ledger("size17-allraw-ids.txt");int ix;while(ledger>>ix)active.insert(ix);
 ifstream f("six-all.txt");int d=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);
 array<M,6>u;for(profile=0;f>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5];profile++){
  if(profile<lo||profile>=hi||!active.count(profile))continue;
  B={};U={};all=0;set<int>seen;vector<int> reps;for(int p=0;p<64;p++){
   int t=0;for(int j=0;j<6;j++)if(u[j]>>p&1)t|=1<<(2*j+(p>>j&1));
   if(seen.insert(t).second)reps.push_back(p);
  }
  atoms=reps.size();if(atoms<16){cout<<profile<<" atoms "<<atoms<<" excluded"<<endl;continue;}
  all=atoms==64?~M(0):((M(1)<<atoms)-1);
  for(int j=0;j<6;j++){
   M a=0,b=0;for(int i=0;i<atoms;i++){int p=reps[i];if(u[j]>>p&1)(p>>j&1?b:a)|=M(1)<<i;}
   B.push_back(a);B.push_back(b);U.push_back(a|b);
  }
  B=uniq(B);primitives=set<M>(B.begin(),B.end());visited=banks=hit=0;
  symmetries(u,reps);completeSeeds=0;coarseAll();
  cout<<profile<<" atoms "<<atoms<<" seeds "<<completeSeeds<<" banks "<<banks<<" visits "<<visited<<" hits "<<hit<<endl;
 }
}
