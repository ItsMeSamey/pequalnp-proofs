#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
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
using W=__uint128_t; using Domains=array<W,10>;
int low(W x){return uint64_t(x)?countr_zero(uint64_t(x)):64+countr_zero(uint64_t(x>>64));}
int pop(W x){return popcount(uint64_t(x))+popcount(uint64_t(x>>64));}
vector<M> masks;W pairsOK[10][10][120],dirBits;int quota;vector<int>required;
bool ac(Domains &dom){
 bool dirty=true;
 while(dirty){
  dirty=false;int lo=0,hi=0;
  for(auto s:dom){if(!s)return false;lo+=!(s&~dirBits);hi+=bool(s&dirBits);}
  if(lo>quota||hi<quota)return false;
  for(int v=0;v<10;v++){
   W s=dom[v];if(lo==quota&&(s&~dirBits))s&=~dirBits;
   if(hi==quota&&(s&dirBits))s&=dirBits;
   for(int u=0;u<10;u++)if(u!=v){
    W old=s;while(old){int k=low(old);old&=old-1;
     if(!(pairsOK[v][u][k]&dom[u]))s&=~(W(1)<<k);
    }
   }
   if(!s)return false;
   if(s!=dom[v]){dom[v]=s;dirty=true;}
  }
  for(auto i:required){
   W bit=W(1)<<i;int count=0,only=-1;for(int v=0;v<10;v++)if(dom[v]&bit){count++;only=v;}
   if(!count)return false;
   if(count==1&&dom[only]!=bit){dom[only]=bit;dirty=true;}
  }
 }
 return true;
}
void exactSearch(Domains dom){
 visited++;if(!ac(dom))return;
 Rooms r;r.fill(all);int best=-1,width=999;
 for(int v=0;v<10;v++){
  int sz=pop(dom[v]);if(sz==1){M m=masks[low(dom[v])];for(int j=0;j<16;j++)r[j]&=mis[j]>>v&1?~m:m;}
  else if(sz<width){best=v;width=sz;}
 }
 for(auto z:r){if(!z)return;int n=0;for(auto y:r)n+=!(y&~z);if(n>count(z))return;}
 if(best<0){for(int i=0;i<10;i++)picked[i]=masks[low(dom[i])];hit++;return;}
 // A mandatory raw support may have fewer available vertices than any vertex has supports.
 int chk=-1;for(auto idx:required){
  W bit=W(1)<<idx;int n=0;bool done=false;
  for(auto z:dom){if(z==bit)done=true;if(z&bit)n++;}
  if(!done&&n<width){chk=idx;width=n;}
 }
 if(chk>=0){
  W b=W(1)<<chk;for(int v=0;v<10;v++)if(dom[v]&b){auto next=dom;next[v]=b;exactSearch(next);if(hit)return;}
 }else{
  for(W k=dom[best];k;k&=k-1){auto next=dom;next[best]=k&-k;exactSearch(next);if(hit)return;}
 }
}
void beginAC(int d,const vector<M>&cand,const vector<M>&w){
 quota=d;masks=cand;if(masks.size()>120)abort();dirBits=0;required={};
 for(auto x:w){auto it=find(masks.begin(),masks.end(),x);if(it==masks.end())return;required.push_back(it-masks.begin());}
 Domains dom{};
 for(int i=0;i<int(masks.size());i++){
  M m=masks[i];if(primitives.count(m))dirBits|=W(1)<<i;
  for(int v=0;v<10;v++){int n=0;for(int I:mis)n+=I>>v&1;
   if(count(m)>=16-n&&count(all^m)>=n)dom[v]|=W(1)<<i;}
 }
 for(int v=0;v<10;v++)for(int u=0;u<10;u++)if(v!=u){
  int need[4]={};for(int I:mis)need[((I>>v)&1)+2*((I>>u)&1)]++;
  for(int i=0;i<int(masks.size());i++){
   W ok=0;M a=masks[i];for(int j=0;j<int(masks.size());j++){
    M b=masks[j];if((ng[v]>>u&1)&&(a|b)!=all)continue;
    if(count(a&b)<need[0]||count((all^a)&b)<need[1]||count(a&(all^b))<need[2]||count(all^(a|b))<need[3])continue;
    ok|=W(1)<<j;
   }pairsOK[v][u][i]=ok;
  }
 }
 exactSearch(dom);
}
using Dom=array<W,10>;
W compat[2][120],sizes[10];
int nd[10],paircounts[10][10][4];
bool checkRoom(const Rooms&r){for(auto z:r){int n=0;for(auto y:r)n+=!(y&~z);if(n>count(z))return false;}return true;}
void qsolve(int done,int dd,Dom dom,const Rooms&r){
 visited++;
 if(done==1023){if(dd==quota){for(auto k:required)if(find(picked,picked+10,masks[k])==picked+10)return;hit++;}return;}
 int best=-1,width=121,lo=0,hi=0,needed=-1;
 for(int v=0;v<10;v++)if(!(done>>v&1)){
  if(!dom[v])return;lo+=!(dom[v]&~dirBits);hi+=bool(dom[v]&dirBits);
 }
 if(dd+lo>quota||dd+hi<quota)return;
 for(int v=0;v<10;v++)if(!(done>>v&1)){
  W &s=dom[v];if(dd+lo==quota&&(s&~dirBits))s&=~dirBits;if(dd+hi==quota&&(s&dirBits))s&=dirBits;
  if((dd==quota || (s&dirBits))&&pop(s)<width){best=v;width=pop(s);}
 }
 for(int k:required){
  M m=masks[k];bool sat=false;int slots=0;
  for(int v=0;v<10;v++)if(done>>v&1){if(picked[v]==m)sat=true;}else if(dom[v]>>k&1)slots++;
  if(!sat&&(slots==0||dd==quota)&&slots<width){width=slots;needed=k;}
 }
 auto extend=[&](int v,int k){
  M m=masks[k];Rooms rr;
  for(int i=0;i<16;i++){rr[i]=r[i]&(mis[i]>>v&1?~m:m);if(!rr[i])return;}
  if(!checkRoom(rr))return;
  Dom nx=dom;for(int u=0;u<10;u++)if(u!=v&&!(done>>u&1)){
   nx[u]&=compat[ng[v]>>u&1][k];
   for(W p=nx[u];p;p&=p-1){
    int l=low(p);M n=masks[l];int counts[4]={};
    for(int I:mis)counts[2*((I>>v)&1)+((I>>u)&1)]++;
    if(count(m&n)<counts[0]||count(m&~n)<counts[1]||count(n&~m)<counts[2]||count(all&~(m|n))<counts[3])nx[u]&=~(W(1)<<l);
   }
   if(!nx[u])return;
  }
  picked[v]=m;qsolve(done|(1<<v),dd+bool(dirBits>>k&1),nx,rr);
 };
 if(needed>=0){
  for(int v=0;v<10&&!hit;v++)if(!(done>>v&1)&&(dom[v]>>needed&1))extend(v,needed);
 }else for(W s=dom[best];s&&!hit;s&=s-1)extend(best,low(s));
}
void fast(int d,const vector<M>&cand,const vector<M>&must){
 masks=cand;quota=d;dirBits=0;required.clear();
 if(cand.size()>120)abort();
 for(auto x:must){auto p=lower_bound(cand.begin(),cand.end(),x);if(p==cand.end()||*p!=x)return;required.push_back(p-cand.begin());}
 Dom dom{};
 for(int i=0;i<int(cand.size());i++){
  M x=cand[i];W bits=0,non=0;
  if(primitives.count(x))dirBits|=W(1)<<i;
  for(int j=0;j<int(cand.size());j++){M y=cand[j];if(!(x&~y)||!(y&~x))continue;
   if((x|y)==all)bits|=W(1)<<j;else non|=W(1)<<j;
  }
  compat[0][i]=non;compat[1][i]=bits;
  for(int v=0;v<10;v++)if(count(x)>=16-nd[v]&&count(all^x)>=nd[v]&&pop(bits)>=popcount((unsigned)ng[v]))
   dom[v]|=W(1)<<i;
 }
 // Apply conservative edge/nonedge neighborhood consistency before the full search.
 bool change=true;while(change){
  change=false;
  for(int v=0;v<10;v++){
   W s=dom[v];
   for(W it=s;it;it&=it-1){int k=low(it);for(int u=0;u<10;u++)if(u!=v&&!(compat[ng[v]>>u&1][k]&dom[u])){s&=~(W(1)<<k);break;}}
   if(!s)return;if(s!=dom[v]){dom[v]=s;change=true;}
  }
 }
 Rooms r;r.fill(all);
 for(unsigned D=1;D<1024&&!hit;D++){
  if(popcount(D)!=d)continue;
  Dom x=dom;bool ok=true;
  for(int v=0;v<10;v++){
   if(D>>v&1){if(D&ng[v]){ok=false;break;}x[v]&=dirBits;}
   else x[v]&=~dirBits;
   if(!x[v]){ok=false;break;}
  }
  if(ok)qsolve(0,0,x,r);
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
 for(unsigned omit=0;omit<(1u<<w.size());omit++){
   if(popcount(omit)!=min(spare,int(w.size())))continue;
   vector<M> req;for(int i=0;i<int(w.size());i++)if(!(omit>>i&1))req.push_back(w[i]);beginAC(d,cand,req);
   if(hit)return;
  }
}
vector<M> precursor(M goal,const array<M,7>&u,const vector<int>&reps){
 int j=find(U.begin(),U.end(),goal)-U.begin(); vector<M> s;
 for(int k=0;k<7;k++)if(k!=j){
  bool dep=false;for(int p=0;p<128;p++)if(((u[k]>>p)^(u[k]>>(p^(1<<j))))&1){dep=true;break;}
  if(dep)continue;
  M x=0,y=0;for(int i=0;i<int(reps.size());i++){int p=reps[i];if(u[k]>>p&1)(p>>k&1?y:x)|=M(1)<<i;}
  s.push_back(x);s.push_back(y);
 }
 return uniq(s);
}
bool pairable(const vector<M>&s,M goal){for(auto a:s)if(!(a&~goal))for(auto b:s)if((a|b)==goal)return true;return false;}
bool earlyRaw(M goal,const vector<M>&base,const vector<M>&helpers){
 vector<M>s=base;
 for(unsigned round=0;round<helpers.size();round++)for(auto x:helpers){
  if((x&~goal)||find(s.begin(),s.end(),x)!=s.end())continue;
  if(pairable(s,x))s.push_back(x);
 }
 return pairable(s,goal);
}

int main(int argc,char**argv){
 for(int i=0;i<10;i++)for(int I:mis)nd[i]+=I>>i&1;
 for(int p:pos)for(int j=0;j<10;j++)if(p>>j&1)ng[j]|=p^(1<<j);
 if(argc==1){all=uint64_t(-1);B={6148914691236517205ull,12297829382473034410ull,3689348814741910323ull,14757395258967641292ull,1085102592571150095ull,17361641481138401520ull,71777214294589695ull,18374966859414961920ull,281470681808895ull,18446462603027742720ull,4294967295ull,18446744069414584320ull};primitives=set<M>(B.begin(),B.end());fast(3,{18446742978492890880ull,4294967295ull,18446744073456906480ull,18446687779573189836ull,281470681808895ull,71777214294589695ull,18446744073423220462ull,18379189048491114255ull,18389322302273879859ull,18446733035643598325ull},{});if(!hit)return 3;cout<<"18-gate control verified by CSP"<<endl;return 0;}
 ifstream f(argv[4]);int d=atoi(argv[1]),lo=atoi(argv[2]),hi=atoi(argv[3]);
 vector<set<int>> orbits; if(argc>6){ifstream o(argv[6]);string line;while(getline(o,line)){istringstream is(line);int z;set<int> accepted;while(is>>z)accepted.insert(z);orbits.push_back(accepted);}}
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
  B=uniq(B);primitives=set<M>(B.begin(),B.end());visited=banks=hit=0;
  vector<M> w;for(auto x:U)if(x!=all&&!primitives.count(x))w.push_back(x);w=uniq(w);
  vector<vector<M>> early;for(auto x:w)early.push_back(precursor(x,u,reps));
  vector<M> hs{0};
  if(d==3){
   for(auto x:B)for(auto y:B)if(x!=y&&(x|y)!=all&&!primitives.count(x|y))hs.push_back(x|y);
   hs.insert(hs.end(),w.begin(),w.end());
  }
  hs=uniq(hs);
  int hidx=-1;for(auto h:hs){
   hidx++;if(!orbits.empty()&&!orbits.at(profile).count(hidx))continue;if(argc>5&&profile==lo&&hidx<atoi(argv[5]))continue;cout<<"begin "<<profile<<" helper "<<hidx<<" / "<<hs.size()<<endl;
   vector<M>must,optional;if(h)optional.push_back(h);
   bool ok=true;
   for(int i=0;i<int(w.size());i++)if(w[i]!=h){
    if(!earlyRaw(w[i],early[i],optional)){ok=false;break;}
    for(auto x:must)if(!(x&~w[i])||!(w[i]&~x)){ok=false;break;}
    must.push_back(w[i]);
   }
   if(!ok)continue;
   vector<M>lib=B;if(h)lib.push_back(h);vector<M>cand=B;
   for(auto x:lib)for(auto y:lib)if(x!=y&&(x|y)!=all)cand.push_back(x|y);cand=uniq(cand);
   // Each nonprimitive activation is either our one extra union or a paid raw.
   // All original branches and an arbitrary one-helper mask are granted for raw assembly.
   banks++;
   if(argc>=5)fast(d,cand,must);if(hit){cout<<"packing "<<profile<<" h "<<h<<" raw";for(auto m:picked)cout<<" "<<m;cout<<endl;}
   if(hit)break;
  }
  cout<<profile<<" atoms "<<atoms<<" banks "<<banks<<" visits "<<visited<<" hits "<<hit<<endl;
 }
}
