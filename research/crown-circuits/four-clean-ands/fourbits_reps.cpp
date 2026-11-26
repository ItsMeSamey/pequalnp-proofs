#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <random>
#include <set>
#include <unordered_set>
#include <vector>
using namespace std;using Code=array<unsigned short,12>;
vector<int>subs;vector<array<uint16_t,16>>sym;set<Code>seen;
long long reps,total;int best=100;mt19937 rng(72164);vector<int>pack;
int R(int n){return rng()%n;}
void solve(Code p){for(auto x:p)printf("%d ",x);puts("");}
void check(){
 total++;Code p;for(int i=0;i<12;i++)p[i]=pack[i];sort(p.begin(),p.end());if(seen.contains(p))return;reps++;
 for(auto&s:sym){Code q;for(int i=0;i<12;i++){int v=0;for(int x=p[i];x;x&=x-1)v|=s[countr_zero((unsigned)x)];q[i]=v;}sort(q.begin(),q.end());seen.insert(q);}
 solve(p);
}
void gen(int idx,int left,int occupied){
 if(!left){check();return;}if(popcount((unsigned)(65535^occupied))<left)return;
 for(int j=idx;j<(int)subs.size();j++)if(!(subs[j]&occupied)){pack.push_back(subs[j]);gen(j+1,left-1,occupied|subs[j]);pack.pop_back();}
}
int main(){
 array<int,4>perm={0,1,2,3};do{for(int flip=0;flip<16;flip++){array<uint16_t,16>x;for(int i=0;i<16;i++){int y=flip;for(int j=0;j<4;j++)if(i>>j&1)y^=1<<perm[j];x[i]=1<<y;}sym.push_back(x);}}while(next_permutation(perm.begin(),perm.end()));
 for(int code=0;code<81;code++){int x=code,p=0,n=0;for(int j=0;j<4;j++,x/=3){if(x%3==1)p|=1<<j;if(x%3==2)n|=1<<j;}int sub=0;for(int t=0;t<16;t++)if((t&p)==p&&!(t&n))sub|=1<<t;if(popcount((unsigned)sub)<=4)subs.push_back(sub);}
 sort(subs.begin(),subs.end(),[](int a,int b){return popcount((unsigned)a)>popcount((unsigned)b);});gen(0,12,0);fprintf(stderr,"done total=%lld reps=%lld best=%d\n",total,reps,best);
}
