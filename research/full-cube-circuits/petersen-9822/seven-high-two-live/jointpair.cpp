#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;using M=__uint128_t;
ostream& operator<<(ostream& o,M x){if(x>=10)o<<(x/10);return o<<char('0'+x%10);}
istream& operator>>(istream& i,M& x){string s;if(i>>s){x=0;for(char c:s)x=x*10+(c-'0');}return i;}

static const array<int,16> mis={50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773};
static const int pos[]={6,24,17,33,66,132,264,528,160,640,576,320,288};
M all; M picked[10];int ng[10],atoms,profile,spare;
long long visited,banks,hit; vector<M>B,U;set<M> primitives;
int count(M m){return popcount(uint64_t(m))+popcount(uint64_t(m>>64));}
vector<M> uniq(vector<M>x){sort(x.begin(),x.end());x.erase(unique(x.begin(),x.end()),x.end());return x;}
using Rooms=array<M,16>;
bool allowed(const Rooms& rooms,int v,M m){
 for(int i=0;i<16;i++)if(!(rooms[i]&(mis[i]>>v&1?~m:m)))return false;
 return true;
}
struct Seed{int covered;array<M,10> masks;Rooms rooms;};
vector<Seed> seeds;
vector<pair<int,int>> signatureClass[1024];
void initClasses(){
 for(int cover=0;cover<1024;cover++)
  for(int i=0;i<16;i++){
   bool first=true;int n=0;
   for(int j=0;j<16;j++)if(((mis[i]^mis[j])&cover)==0){n++;if(j<i)first=false;}
   if(first)signatureClass[cover].push_back({i,n});
  }
}
bool hall(const Rooms&r,int cover){
 for(auto [i,n]:signatureClass[cover])if(count(r[i])<n)return false;
 return true;
}
vector<vector<M>> sym;
void symmetries(const array<M,7>&u,const vector<int>&reps){
 sym.clear();set<M> acts(u.begin(),u.end());
 auto mapped=[](M m,const array<int,128>&perm){M y=0;while(m){int k=uint64_t(m)?countr_zero(uint64_t(m)):64+countr_zero(uint64_t(m>>64));m&=m-1;y|=M(1)<<perm[k];}return y;};
 vector<M> raw;
 for(int j=0;j<7;j++){M b=0;for(int k=0;k<128;k++)if(k>>j&1)b|=M(1)<<k;raw.push_back(b&u[j]);raw.push_back(~b&u[j]);}
 set<M> bs(raw.begin(),raw.end());
 auto compact=[&](M m){M y=0;for(int k=0;k<int(reps.size());k++)if(m>>reps[k]&1)y|=M(1)<<k;return y;};
 for(int j=0;j<7;j++)for(int l=j;l<7;l++){array<int,128>pi{};
  for(int k=0;k<128;k++)pi[k]=j==l?(k^(1<<j)):((k>>j^k>>l)&1?k^(1<<j)^(1<<l):k);
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
  if(hall(next.rooms,next.covered))seed(chosen^(1<<v),next);
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
bool haveArcDomains=false;
array<set<M>,10> arcDomain;
bool canput(int v,M m,int cover,const Rooms&r,Rooms&rr){
 if(haveArcDomains&&!arcDomain[v].count(m))return false;
 for(int u=0;u<10;u++)if(cover>>u&1){M other=picked[u];if(!(m&~other)||!(other&~m)||bool((m|other)==all)!=bool(ng[v]>>u&1))return false;}
 for(int j=0;j<16;j++){rr[j]=r[j]&(mis[j]>>v&1?~m:m);if(!rr[j])return false;}
 return hall(rr,cover|(1<<v));
}
#include <map>
using Banks=array<uint64_t,256>;
vector<M> granted;
vector<M> universe;
vector<Banks> maskBanks;
vector<vector<M>> helperBanks;
int bankWords;Banks initialBanks{};
bool noBank(const Banks& alive,const Banks& options){
 for(int i=0;i<bankWords;i++)if(alive[i]&options[i])return false;
 return true;
}
vector<M> ordinary; map<M,vector<M>> earlyBranches;
bool widthsFit(){
 int h=2-granted.size();vector<int>demand;
 vector<M> start=B;start.insert(start.end(),granted.begin(),granted.end());
 for(auto w:wr){
  auto available=earlyBranches.at(w);available.insert(available.end(),granted.begin(),granted.end());
  vector<M> inside; for(auto b:available)if(!(b&~w))inside.push_back(b);inside=uniq(inside);
  vector<M> stage={0};int width=0;
  while(width<h+2&&!binary_search(stage.begin(),stage.end(),w)){
   vector<M> next=stage;for(auto a:stage)for(auto b:inside)next.push_back(a|b);
   stage=uniq(next);width++;
  }
  if(!binary_search(stage.begin(),stage.end(),w))return false;
  demand.push_back(max(0,width-2));
 }
 for(unsigned g=1;g<(1u<<wr.size());g++){
  bool disjoint=true;int need=0;
  for(unsigned i=0;i<wr.size();i++)if(g>>i&1){
   need+=demand[i];for(unsigned j=0;j<i;j++)if(g>>j&1){
    M m=wr[i]&wr[j];int n=0;for(auto a:start)if(!(a&~m))n++;
    if(n>=2)disjoint=false;
   }
  }
  if(disjoint&&need>h)return false;
 }
 return true;
}
void library(){
 map<M,Banks> lookup;helperBanks.clear();initialBanks.fill(0);
 vector<M> base=B;base.insert(base.end(),granted.begin(),granted.end());
 vector<M> always=B;
 for(auto x:base)for(auto y:base)if(x!=y&&(x|y)!=all)always.push_back(x|y);
 always=uniq(always);
 struct Goal{M raw;vector<M> base;set<M> pairs;};vector<Goal> goals;
 for(auto w:wr){
  auto e=earlyBranches.at(w);e.insert(e.end(),granted.begin(),granted.end());
  vector<M> hold;for(auto x:e)if(!(x&~w))hold.push_back(x);hold=uniq(hold);
  set<M> pairs;for(auto x:hold)for(auto y:hold)pairs.insert(x|y);
  if(!pairs.count(w))goals.push_back({w,hold,pairs});
 }
 auto add=[&](vector<M> helpers){
  if(helpers.size()+granted.size()>2)return;vector<M> lib=B;lib.insert(lib.end(),granted.begin(),granted.end());lib.insert(lib.end(),helpers.begin(),helpers.end());vector<M> c;
  for(auto &g:goals){
   M x=0,y=0;
   for(auto a:helpers)if(!(a&~g.raw)){if(!x)x=a;else y=a;}
   bool madeX=x&&g.pairs.count(x),madeY=y&&g.pairs.count(y);
   if(!madeX&&!madeY)return;
   if(!madeX&&x)for(auto b:g.base)if((b|y)==x)madeX=true;
   if(!madeY&&y)for(auto b:g.base)if((b|x)==y)madeY=true;
   bool can=madeX&&madeY&&(x|y)==g.raw;
   for(auto b:g.base)if((madeX&&(b|x)==g.raw)||(madeY&&(b|y)==g.raw))can=true;
   if(!can)return;
  }
  for(auto x:helpers)for(auto y:lib)if(x!=y&&(x|y)!=all)c.push_back(x|y);
  c=uniq(c);for(auto w:wr)if(!binary_search(always.begin(),always.end(),w)&&!binary_search(c.begin(),c.end(),w))return;
  int no=helperBanks.size();if(no>=16384)abort();helperBanks.push_back(helpers);
  initialBanks[no/64]|=uint64_t(1)<<(no%64);for(auto x:c)if(!primitives.count(x))lookup[x][no/64]|=uint64_t(1)<<(no%64);
 };
 vector<M> h1;
 vector<M> start=B;start.insert(start.end(),granted.begin(),granted.end());for(auto x:start)for(auto y:start)if(x!=y&&(x|y)!=all&&!primitives.count(x|y)&&!binary_search(wr.begin(),wr.end(),x|y))h1.push_back(x|y);
 h1=uniq(h1);add({});if(granted.size() < 2)
 for(auto x:h1){add({x});if(granted.size()+1 >= 2)continue;vector<M>h2=h1;for(auto z:B)h2.push_back(x|z);
  for(auto y:uniq(h2))if(x!=y&&y!=all&&!primitives.count(y)&&!binary_search(wr.begin(),wr.end(),y)&&(!binary_search(h1.begin(),h1.end(),y)||y>x))add({x,y});
 }
 for(auto x:always)if(!primitives.count(x))lookup[x]=initialBanks;
 banks=helperBanks.size();bankWords=(banks+63)/64;universe.clear();maskBanks.clear();for(auto&[x,b]:lookup){universe.push_back(x);maskBanks.push_back(b);}
}
using Choices=array<vector<int>,10>;
void joint(int cover,const Rooms&r,const Banks&live,const Choices&dom){
 visited++;
 if(cover==1023){
  hit++;cout<<"packing "<<profile<<" raw";for(auto m:picked)cout<<" "<<m;
  for(int k=0;k<bankWords;k++)if(live[k]){int j=k*64+countr_zero(live[k]);cout<<" helpers";for(auto m:helperBanks[j])cout<<" "<<m;break;}cout<<endl;return;
 }
 int best=-1;vector<int>options;
 for(int v=0;v<10;v++)if(!(cover>>v&1)){
  vector<int> available;for(int i:dom[v]){
   M x=universe[i];bool ok=true;
   for(int u=0;u<10;u++)if(cover>>u&1){M y=picked[u];if(!(x&~y)||!(y&~x)||bool((x|y)==all)!=bool(ng[v]>>u&1)){ok=false;break;}}
   if(ok&&allowed(r,v,x)&&!noBank(live,maskBanks[i]))available.push_back(i);
  }
  if(available.empty())return;
  if(best<0||available.size()<options.size()){best=v;options=move(available);}
 }
 for(auto k:options){
  M m=universe[k];Rooms rr;for(int j=0;j<16;j++)rr[j]=r[j]&(mis[j]>>best&1?~m:m);
  if(!hall(rr,cover|(1<<best)))continue;Banks next{};for(int j=0;j<bankWords;j++)next[j]=live[j]&maskBanks[k][j];
  picked[best]=m;joint(cover|(1<<best),rr,next,dom);if(hit)return;
 }
}
using Vec=vector<uint64_t>;
map<pair<M,bool>,Vec> rawDomains;
const Vec& candidatesFor(M m,bool edge){
 int words=(universe.size()+63)/64;
   auto [it,newEntry]=rawDomains.try_emplace({m,edge},Vec());
   if(newEntry){
    Vec &b=it->second;b.assign(words,0);
    for(int k=0;k<int(universe.size());k++){
     M x=universe[k];
     if((x&~m)&&(m&~x)&&bool((x|m)==all)==edge)b[k/64]|=uint64_t(1)<<(k%64);
    }
   }
 return it->second;
}
void jointRoot(int cover,const Rooms&r){
 Choices dom;Rooms rr;
 int words=(universe.size()+63)/64;
 for(int v=0;v<10;v++)if(!(cover>>v&1)){
  Vec poss(words,~uint64_t(0));if(words&&universe.size()%64)poss.back()=(uint64_t(1)<<(universe.size()%64))-1;
  for(int a=0;a<10;a++)if(cover>>a&1){
   M m=picked[a];bool edge=(ng[v]>>a)&1;
   const auto& bits=candidatesFor(m,edge);
   bool any=false;for(int w=0;w<words;w++){poss[w]&=bits[w];any|=bool(poss[w]);}
   if(!any)return;
  }
  for(int w=0;w<words;w++)for(uint64_t b=poss[w];b;b&=b-1){
   int k=64*w+countr_zero(b);if(canput(v,universe[k],cover,r,rr))dom[v].push_back(k);
  }
  if(dom[v].empty())return;
 }
 joint(cover,r,initialBanks,dom);
}
bool futureRawPossible(int cover,int D){
 int words=(universe.size()+63)/64;
 if(!words)return false;
 for(int v=0;v<10;v++)if(!((cover|D)>>v&1)){
  const Vec* test[10];int n=0;
  for(int u=0;u<10;u++)if(cover>>u&1)test[n++]=&candidatesFor(picked[u],(ng[v]>>u)&1);
  if(n<2)continue;
  bool ok=false;
  for(int w=0;w<words&&!ok;w++){
   uint64_t bits=(*test[0])[w];
   for(int i=1;i<n&&bits;i++)bits&=(*test[i])[w];
   ok=bool(bits);
  }
  if(!ok)return false;
 }
 return true;
}
void nearseed(int D,int cover,const Rooms& r){
 if(D && !futureRawPossible(cover,D))return;
 if(!D){
  completeSeeds++;
  jointRoot(cover,r);
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
bool initialAC(){
 haveArcDomains=false;
 vector<M> raw=universe;raw.insert(raw.end(),B.begin(),B.end());raw=uniq(raw);
 int n=raw.size();if(n>128)return true;
 array<M,128> adj{},non{};array<M,10> dom{};
 for(int i=0;i<n;i++){
  for(int j=0;j<n;j++)if((raw[i]&~raw[j])&&(raw[j]&~raw[i])){
   if((raw[i]|raw[j])==all)adj[i]|=M(1)<<j;else non[i]|=M(1)<<j;
  }
  for(int v=0;v<10;v++){
   int lost=0;for(auto I:mis)lost+=bool(I>>v&1);
   if(count(all^raw[i])>=lost && count(raw[i])>=16-lost && count(adj[i])>=popcount((unsigned)ng[v]))dom[v]|=M(1)<<i;
  }
 }
 bool change=true;while(change){
  change=false;
  for(int v=0;v<10;v++){
   M old=dom[v];
   for(M a=old;a;a&=a-1){
    int i=uint64_t(a)?countr_zero(uint64_t(a)):64+countr_zero(uint64_t(a>>64));
    for(int u=0;u<10;u++)if(u!=v&&!((ng[v]>>u&1?adj[i]:non[i])&dom[u])){dom[v]&=~(M(1)<<i);break;}
   }
   if(!dom[v])return false;
   change|=dom[v]!=old;
  }
 }
 for(int v=0;v<10;v++){
  arcDomain[v].clear();for(int i=0;i<n;i++)if(dom[v]>>i&1)arcDomain[v].insert(raw[i]);
 }
 haveArcDomains=true;
 return true;
}

bool quickDirect(int todo,int cover,const Rooms&r){
 if(!todo)return true;
 int v=countr_zero((unsigned)todo);Rooms next;
 for(auto b:B){
  bool ok=true;for(int j=0;j<16;j++){
   next[j]=r[j]&(mis[j]>>v&1?~b:b);
   if(!next[j]){ok=false;break;}
  }
  if(ok&&hall(next,cover|(1<<v))&&quickDirect(todo^(1<<v),cover|(1<<v),next))return true;
 }
 return false;
}
bool directPossible(){
 Rooms r;r.fill(all);
 for(int D=0;D<1024;D++)if(popcount((unsigned)D)==4){
  bool ok=true;for(auto e:pos)if((D&e)==e)ok=false;
  if(ok&&quickDirect(D,0,r))return true;
 }
 return false;
}
void coarseAll(){
 if(!directPossible())return;
 wr={};for(auto x:U)if(x!=all&&!primitives.count(x))wr.push_back(x);wr=uniq(wr);auto mandatory=wr;for(unsigned g=0;g<(1U<<mandatory.size());g++){if(popcount(g)>2)continue;wr.clear();granted.clear();for(unsigned i=0;i<mandatory.size();i++)(g>>i&1?granted:wr).push_back(mandatory[i]);
 bool comparable=false;
 for(auto x:wr)for(auto y:wr)if(x!=y&&!(x&~y))comparable=true;
 if(comparable||!widthsFit())continue;
 library();rawDomains.clear();if(!banks||!initialAC())continue;
 Rooms r;r.fill(all);int ga[]={3,2,1,0,4,8,7,6,5,9};
 for(int D=0;D<1024;D++)if(popcount(unsigned(D))==4){
  bool use=true;int reflect=0;for(int i=0;i<10;i++)if(D>>i&1)reflect|=1<<ga[i];
  for(int e:pos)if((D&e)==e)use=false;
  if(use&&reflect>=D){qverts=D;named(0,D,0,r);if(hit)return;}
 }
}
}
int main(int argc,char**argv){
 initClasses();
 for(int p:pos)for(int j=0;j<10;j++)if(p>>j&1)ng[j]|=p^(1<<j);
 if(argc==1){ifstream f("control4-1.txt");vector<M>h,raw;all=uint64_t(-1);for(int i=0;i<12;i++){M m;f>>m;B.push_back(m);}ordinary.assign(B.begin(),B.begin()+12);B=uniq(B);primitives=set<M>(B.begin(),B.end());for(int i=0;i<3;i++){M m;f>>m;h.push_back(m);}for(int i=0;i<10;i++){M m;f>>m;raw.push_back(m);}helperBanks={h};bankWords=1;initialBanks.fill(0);initialBanks[0]=1;
  vector<M> lib=B;lib.insert(lib.end(),h.begin(),h.end());for(auto x:lib)for(auto y:lib)if(x!=y&&(x|y)!=all&&!primitives.count(x|y))universe.push_back(x|y);universe=uniq(universe);maskBanks.assign(universe.size(),initialBanks);int cover=0;Rooms r;r.fill(all);
  for(int v=0;v<10;v++)if(primitives.count(raw[v])){cover|=1<<v;picked[v]=raw[v];for(int i=0;i<16;i++)r[i]&=mis[i]>>v&1?~raw[v]:raw[v];}
  if(!directPossible()||!initialAC())return 3;jointRoot(cover,r);if(!hit)return 2;cout<<"four-direct six-switch 18-gate control accepted"<<endl;return 0;}
 set<int> active;ifstream ledger("size17-final-six.ids");int ix;while(ledger>>ix)if(ix!=41718)active.insert(ix);
 ifstream f("at-most-two.tsv");int d=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);
 array<M,7>u;for(profile=0;f>>u[0]>>u[1]>>u[2]>>u[3]>>u[4]>>u[5]>>u[6];profile++){
  if(profile<lo||profile>=hi)continue;
  B={};U={};all=0;set<int>seen;vector<int> reps;for(int p=0;p<128;p++){
   int t=0;for(int j=0;j<7;j++)if(u[j]>>p&1)t|=1<<(2*j+(p>>j&1));
   if(seen.insert(t).second)reps.push_back(p);
  }
  atoms=reps.size();if(atoms<16){cout<<profile<<" atoms "<<atoms<<" excluded"<<endl;continue;}
  all=atoms==128?~M(0):((M(1)<<atoms)-1);
  for(int j=0;j<7;j++){
   M a=0,b=0;for(int i=0;i<atoms;i++){int p=reps[i];if(u[j]>>p&1)(p>>j&1?b:a)|=M(1)<<i;}
   B.push_back(a);B.push_back(b);U.push_back(a|b);
  }
  earlyBranches.clear();for(int j=0;j<7;j++)if(u[j]!=~M(0)){
   vector<M> allowed;
   for(int k=0;k<7;k++)if(k!=j){bool dep=false;
    for(int p=0;p<128;p++)if(((u[k]>>p)^(u[k]>>(p^(1<<j))))&1){dep=true;break;}
    if(!dep){allowed.push_back(B[2*k]);allowed.push_back(B[2*k+1]);}
   }
   earlyBranches[U[j]]=uniq(allowed);
  }
  ordinary.assign(B.begin(),B.begin()+12);B=uniq(B);primitives=set<M>(B.begin(),B.end());visited=banks=hit=0;
  symmetries(u,reps);completeSeeds=0;coarseAll();
  cout<<profile<<" atoms "<<atoms<<" seeds "<<completeSeeds<<" banks "<<banks<<" visits "<<visited<<" hits "<<hit<<endl;
 }
}
