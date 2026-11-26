// Dimension-generic seven-comparator port of algebra/eightfour/full.cpp.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;using Bits=__uint128_t;using Row=vector<unsigned>;
struct Cube {Bits w=0;int size()const{return popcount(uint64_t(w))+popcount(uint64_t(w>>64));}
 Cube join(Cube b)const{return {w|b.w};}bool overlaps(Cube b)const{return w&b.w;}
 bool subset(Cube b)const{return !(w&~b.w);}bool operator==(Cube b)const{return w==b.w;}};
Cube invert(Cube a){return {~a.w};}
struct Candidate{int m;Cube d;int volume,unused;};
bool pack(const vector<Candidate>&a,int i,int k,Cube used,int){
 if(!k)return true;for(;i+k<=int(a.size());i++){if(used.size()+k*a[i].volume>128)return false;
 if(!used.overlaps(a[i].d)&&pack(a,i+1,k-1,used.join(a[i].d),0))return true;}return false;}
struct Oracle{Row t;array<Cube,7>u{};array<Cube,14>b{};
 explicit Oracle(Row r):t(r){for(int s=0;s<128;s++){int q=0;for(int j=6;j>=0;j--)if(j>=int(t.size())||(q&t[j])){
 unsigned pin=2*j+((s>>j)&1);q|=1<<pin;b[pin].w|=Bits(1)<<s;u[j].w|=Bits(1)<<s;}}}};
struct Full:Oracle{
 vector<unsigned> roots,bank,hs,req;vector<Cube> vals;vector<int> fee,freq;array<int,129> hist{};
 vector<unsigned char> inside;int pinmask=0,initialCost=0;
 long long nodes=0,lib=0,eligible=0,front=0,solutions=0;
 Full(Row r):Oracle(r),vals(16384),fee(16384),freq(16384),inside(16384){
  for(int j=0;j<14;j++)bank.push_back(1u<<j);unsigned all=0;for(unsigned v:t)all|=v;
  for(int j=0;j<t.size();j++)if(!(all&(3u<<(2*j)))){roots.push_back(j);pinmask|=3u<<(2*j);}
  req.assign(t.begin(),t.end());sort(req.begin(),req.end());req.erase(unique(req.begin(),req.end()),req.end());
  for(unsigned m=1;m<16384;m++){vals[m]=vals[m&(m-1)].join(b[countr_zero(m)]);if(popcount(m)>7)continue;
   for(auto x:req)if(!(m&~x))inside[m]=true;
   if(inside[m]||popcount(m)<2)continue;
   int d=req.size()+1,n=popcount(all|m);if(n>6+d)continue;
   array<bool,128> seen{};int patterns=0;for(unsigned z=all|m;z;z&=z-1){unsigned bit=z&-z,p=0;for(int i=0;i<d-1;i++)if(req[i]&bit)p|=1u<<i;if(m&bit)p|=1u<<(d-1);if(popcount(p)>1&&!seen[p]){seen[p]=true;++patterns;}}
   if(n+patterns>6+d)continue;int fv=128-vals[m].size();if(fv&&fv<=118)fee[m]=fv;
  }
  for(int i=0;i<14;i++)for(int j=0;j<i;j++)bump(bank[i],bank[j],1);
 }
 void bump(unsigned a,unsigned b,int d){unsigned m=a|b;if(m==a||m==b||!fee[m])return;int prev=freq[m];freq[m]+=d;if(!prev)hist[fee[m]]++;else if(!freq[m])hist[fee[m]]--;}
 bool available(unsigned m){return find(bank.begin(),bank.end(),m)!=bank.end();}
 unsigned exclusive(unsigned m){unsigned x=0;for(auto j:roots){unsigned a=m&(3u<<(2*j));if(popcount(a)==1)x|=a;}return x;}
 bool sizeOk(){int k=11,room=128;for(int i=1;i<=128&&k;i++){int z=min(k,hist[i]);room-=z*i;k-=z;}return !k&&room>=0;}
 array<unsigned,7> stamp(unsigned m){
  array<unsigned,7> s{};for(int j=0;j<7;j++){unsigned a=0,c=0;auto add=[&](unsigned x){a=(a<<1)|((x>>(2*j))&1);c=(c<<1)|((x>>(2*j+1))&1);};
   for(unsigned x:t)add(x);for(unsigned x:hs)add(x);add(m);s[j]=(min(a,c)<<13)|max(a,c);}
  sort(s.begin()+t.size(),s.end());return s;
 }
 void test(){
  lib++;if(!sizeOk())return;eligible++;
  vector<unsigned> all;for(int i=0;i<(int)bank.size();i++)for(int j=0;j<i;j++){unsigned m=bank[i]|bank[j];if(fee[m]&&freq[m])all.push_back(m);}
  sort(all.begin(),all.end());all.erase(unique(all.begin(),all.end()),all.end());
  vector<unsigned> anchor;for(unsigned r:roots){unsigned bits=3u<<(2*r);vector<unsigned> opts;
   for(unsigned m:all)if((m&bits)==bits){bool simple=false;
    for(unsigned x:bank)if((x&bits)!=bits&&u[r].join(vals[x])==vals[m]){simple=true;break;}
    if(!simple)opts.push_back(m);}
   if(opts.empty())return;if(anchor.empty()||opts.size()<anchor.size())anchor=move(opts);
  }
  if(roots.empty())anchor=all;
  for(unsigned k:anchor){Cube kd=invert(vals[k]);vector<Candidate> c;
   for(unsigned m:all){Cube d=invert(vals[m]);if(!d.overlaps(kd))c.push_back({int(m),d,fee[m],0});}
   sort(c.begin(),c.end(),[](auto&a,auto&b){return a.volume!=b.volume?a.volume<b.volume:a.m<b.m;});
   vector<Candidate> keep;for(auto&v:c){bool omit=false;for(auto&z:keep)if(z.d.subset(v.d)){omit=true;break;}if(!omit)keep.push_back(v);}
   if(keep.size()<10)continue;int area=kd.size();for(int i=0;i<10;i++)area+=keep[i].volume;if(area>128)continue;
   front++;if(pack(keep,0,10,kd,0)){solutions++;printf("candidate K %u H",k);for(unsigned x:hs)printf(" %u",x);puts("");fflush(stdout);return;}
  }
 }
 void walk(bool exterior,unsigned last,unsigned covered){
  if(solutions)return;++nodes;int free=5-(int)hs.size(),miss=popcount(unsigned(pinmask)&~covered);
  if(miss>2*free)return;
  if(exterior&&!miss)test();
  if(!exterior){int remaining=0;for(unsigned x:req)remaining+=!available(x);if(remaining+int(roots.size())>free)return;
   if(!remaining)walk(true,0,covered);}
  if(!free)return;
  vector<unsigned> choices;for(int i=0;i<(int)bank.size();i++)for(int j=0;j<i;j++){
   unsigned m=bank[i]|bank[j];if(m==bank[i]||m==bank[j]||available(m)||bool(inside[m])==exterior||popcount(m)*16384u+m<=last)continue;
   if(popcount(unsigned(pinmask)&~(covered|exclusive(m)))>2*(free-1))continue;choices.push_back(m);}
  sort(choices.begin(),choices.end());choices.erase(unique(choices.begin(),choices.end()),choices.end());set<array<unsigned,7>> seen;
  for(unsigned m:choices){if(!seen.insert(stamp(m)).second)continue;
   for(unsigned x:bank)bump(x,m,1);bank.push_back(m);hs.push_back(m);walk(exterior,popcount(m)*16384u+m,covered|exclusive(m));
   hs.pop_back();bank.pop_back();for(unsigned x:bank)bump(x,m,-1);}
 }
};
int main(int argc,char**argv){if(argc<4)return 2;int d=atoi(argv[1]),cost=atoi(argv[3]);ifstream in(argv[2]);int id,c,cap;
while(in>>id>>c>>cap){Row t(d);unsigned all=0;for(unsigned &m:t){in>>m;all|=m;}if(c!=cost||cap<11)continue;
int e=0;for(int j=0;j<d;j++)e+=!(all&(3u<<(2*j)));if(e+c>=5)continue;
Full s(t);s.walk(false,0,0);cout<<id<<" "<<c<<" "<<e<<" "<<s.nodes<<" "<<s.lib<<" "<<s.eligible<<" "<<s.front<<" "<<s.solutions<<endl;}return 0;}
