#include <array>
#include <vector>
#include <iostream>
#include <set>
#include <algorithm>
#include <bit>
using namespace std;
using Family=array<int,8>;
struct Gate{int on,off;};
using State=array<Gate,8>;
vector<Gate> pairs;
set<Family> found;
long long calls;
void solve(State s,int omit) {
 ++calls;
 int best=20, typ=0, bestslot=0;
 Gate row{};
 for (int i=0;i<8;i++){
    auto g=s[i]; if ((g.on&~omit)||(g.off&omit))continue;
    int opts=8191&~(g.on|g.off),n=popcount((unsigned)opts);
    if(!n)return;
    if(n<best){best=n;typ=2;bestslot=i;}
 }
 for(auto r:pairs){
    int choices=0;
    bool done=false;
    for(int i=0;i<8;i++){
      auto g=s[i]; if((g.off&r.on)||(g.on&r.off))continue;
      if(!(r.on&~g.on)&&!(r.off&~g.off)){done=true;break;}
      choices++;
    }
    if(done)continue;
    if(!choices)return;
    if(choices<best){best=choices;typ=1;row=r;}
 }
 if(typ==1){for(int i=0;i<8;i++){auto g=s[i];if((g.off&row.on)||(g.on&row.off))continue;
    auto t=s;t[i].on|=row.on;t[i].off|=row.off;solve(t,omit);}return;}
 if(typ==2){auto &g=s[bestslot];int bits=8191&~(g.on|g.off);
  while(bits){int one=bits&-bits;bits-=one;auto t=s;if(omit&one)t[bestslot].off|=one;else t[bestslot].on|=one;solve(t,omit);
    if(omit&one)g.on|=one;else g.off|=one;}return;}
 for(int i=0;i<8;i++){int free=8191&~(s[i].on|s[i].off);if(!free)continue;int one=free&-free;auto t=s;t[i].on|=one;s[i].off|=one;solve(t,omit);solve(s,omit);return;}
 Family f;for(int i=0;i<8;i++)f[i]=s[i].on;sort(f.begin(),f.end());found.insert(f);
}
int main(){int n;cin>>n;for(int i=0;i<n;i++){Gate g;cin>>g.on>>g.off;pairs.push_back(g);}State s;for(auto &g:s)cin>>g.on>>g.off;int m;while(cin>>m){solve(s,m);cerr<<m<<" "<<calls<<" "<<found.size()<<endl;}for(auto f:found){for(int x:f)cout<<x<<" ";cout<<"\n";}}
