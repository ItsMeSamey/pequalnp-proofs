#include <cstdio>
#include <cstdlib>
#include <map>
#include <utility>
using namespace std;
int main(int argc,char** argv){
 int top=argc>1?atoi(argv[1]):7;
 map<int,pair<int,int>> seen;
 for(int n=3;n<=top;++n){
 int m=(n*(n-1))/2-3;
 for(int g=0;g<(1<<m);++g){
 int adj[9]={},j=0;
 for(int v=3;v<n;++v)for(int u=0;u<v;++u,++j)if((g>>j)&1){adj[u]|=1<<v;adj[v]|=1<<u;}
 bool valid = true;
 for(int v=0;v<n;++v) for(int u=0;u<v;++u)
 if((adj[v]>>u&1) && __builtin_popcount(adj[v])>2 && __builtin_popcount(adj[u])>2) valid=false;
 if(!valid) continue;
 int sig=0;
 for(int s=0;s<(1<<n);++s){
 int odds=0;
 for(int v=0;v<n;++v)if((s>>v&1)&&__builtin_parity(s&adj[v]))odds|=1<<v;
 if(odds>>3||!odds)continue;
 int p=s&7,k=odds==3?0:odds==5?1:2;
 sig|=1<<(k+(p==7?3:0));
 }
 seen.emplace(sig,make_pair(n,g));
 }
 fprintf(stderr,"n=%d count=%zu\n",n,seen.size());
 }
 for(auto [s,ng]:seen)printf("%d %d %d\n",s,ng.first,ng.second);
}
