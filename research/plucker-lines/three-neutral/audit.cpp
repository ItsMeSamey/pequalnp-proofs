#include <cstdio>
#include <vector>
#include <algorithm>
#include <array>
using namespace std;
int parity(int x){return __builtin_parity((unsigned)x);}
void insertMax(vector<int>& v,int a){for(int b:v) if((a&~b)==0)return; v.erase(remove_if(v.begin(),v.end(),[=](int b){return !(b&~a);}),v.end());v.push_back(a);}
vector<int> cubes[256];
void prepare(int own){vector<int> acc{65535};for(int h=1;h<8;++h){vector<int> stage;for(int dual=0;dual<32;++dual){if(!(dual&8))continue; int badown=0,allowed=65535;for(int u=0;u<8;++u){int masked=u&h,entry=parity(masked);if(entry && ((own>>u)&1) && parity(dual&(masked+8)))badown=1;if(parity(dual&(masked+16)))allowed ^=1<<(u+8*entry);}if(!badown)insertMax(stage,allowed);} vector<int> next;for(int s:stage)for(int a:acc)insertMax(next,s&a);acc=next;}cubes[own]=acc;}
struct Profile{int present=0,odd=0,sigxor=0,n=0,cols[16];};
struct Basis{int row[17]={};int red(int x){for(int i=16;i>=0;--i)if((x>>i)&1)x^=row[i];return x;}void put(int x){x=red(x);if(x)row[31-__builtin_clz(x)]=x;}};
int solve(int own,Profile const& p,int c){Basis b;int goal=0;for(int i=0;i<p.n;++i)if((c^parity(p.cols[i]))&1)goal|=1<<i;for(int cube:cubes[own]){int base=0,free=0;bool ok=true;for(int i=0;i<p.n;i++){auto u=p.cols[i];int z=(cube>>u)&1,o=(cube>>(8+u))&1;if(!z&&!o){ok=false;break;}if(!z)base|=1<<i;if(z&&o)free|=1<<i;}if(!ok)continue;int pivot=free&-free;if(parity(base)!=(c^1)){if(!pivot)continue;base^=pivot;}b.put((1<<16)|base);for(int m=free^pivot;m;m&=m-1)b.put(pivot|(m&-m));}return b.red(goal|((1^c)<<16))==0;}
int main(){for(int own=1;own<256;own++)prepare(own);vector<Profile> a[8],b[8];for(int code=1;code<6561;++code){Profile p;int rem=code;for(int u=0;u<8;++u){int k=rem%3;rem/=3;if(k)p.present|=1<<u;if(k&1){p.odd|=1<<u;p.sigxor^=u;}for(int j=0;j<k;++j)p.cols[p.n++]=u;}if(parity(p.sigxor))((p.n&1)?a:b)[p.sigxor].push_back(p);}long long pairs=0,pass=0,lose=0;for(int x=0;x<8;++x)for(auto &p:a[x]){int lhs[256];fill(lhs,lhs+256,-1);for(auto &q:b[x]){pairs++;if(lhs[q.present]<0)lhs[q.present]=solve(q.present,p,1);if(!lhs[q.present])continue;pass++;if(solve(p.present,q,0))lose++;}}printf("pairs=%lld survived first=%lld both=%lld\n",pairs,pass,lose);return lose!=0;}
