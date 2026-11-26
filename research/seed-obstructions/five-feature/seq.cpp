#include <cstdio>
#include <cstdint>
#include <set>
#include <map>
#include <array>
#include <tuple>
using namespace std;using W=uint32_t;using F=array<W,4>;using K=tuple<int,int,int>;map<K,set<F>> cc;const W FUL=~0u;
W sh(W x,int d){W z=0;for(unsigned j=0;j<32;j++)z|=((x>>(j>>d))&1u)<<j;return z;}
const set<F>& en(int n,int x,int y){K key{n,x,y};if(cc.count(key))return cc.at(key);auto &out=cc[key];if(n+x+y==1){if(n)out.insert({0xaaaaaaaau,0xaaaaaaaau,0xaaaaaaaau,0xaaaaaaaau});if(x)out.insert({0,FUL,0,FUL});if(y)out.insert({0,0,FUL,FUL});return out;}
for(int p=0;p<=n;p++)for(int a=0;a<=x;a++)for(int b=0;b<=y;b++){if(p+a+b==0||p+a+b==n+x+y||K{p,a,b}>K{n-p,x-a,y-b})continue;auto &l=en(p,a,b);auto &r=en(n-p,x-a,y-b);for(auto f:r){for(auto &v:f)v=sh(v,p);for(auto g:l){F v,u;for(int h=0;h<4;h++){v[h]=g[h]|f[h];u[h]=g[h]&f[h];}out.insert(u);out.insert(v);}}}return out;}
int main(){set<F> triples;for(int d=1;d<=5;d++)for(int b=0;b+d<=5;b++)for(int x=0;x<=1;x++)for(int y=0;y<=2;y++){if(!b&&!x&&!y)continue;for(auto f:en(b,x,y))for(auto h:en(d,1,1)){W t=f[1]|(sh(h[1],b)&f[3]);W u=f[0]|(sh(h[2],b)&f[2]);triples.insert({f[0],t,u,(unsigned)(d+b)});}}
for(auto [z,t,u,n]:triples)printf("%u %u %u %u\n",z,t,u,n);fprintf(stderr,"%zu triples\n",triples.size());}
