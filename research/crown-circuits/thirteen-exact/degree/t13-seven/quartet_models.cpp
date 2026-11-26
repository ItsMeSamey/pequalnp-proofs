#include <algorithm>
#include <bit>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <set>
#include <vector>
using namespace std;
int p,cap,a,k[12],d[12],rem[12],adj[12];
long long countGraphs, types;
map<vector<int>,long long> hist;
bool valid(){
 int unseen=(1<<p)-1,componentMin=0,sz[12]={};vector<int> parts;
 while(unseen){
  int reached=unseen&-unseen, todo=reached;
  while(todo){int i=countr_zero((unsigned)todo);todo&=todo-1;int add=adj[i]&~reached;reached|=add;todo|=add;}
  unseen&=~reached;
  int size=popcount((unsigned)reached);parts.push_back(size);componentMin+=min(size,2);
  for(int i=0;i<p;i++)if(reached>>i&1)sz[i]=size;
 }
 for(int i=0;i<p;i++){
  if(k[i]+p-int(parts.size())>cap || k[i]+max(2,d[i])>cap)return false;
 }
 int small=0;
 for(int i=0;i<p;i++)if(k[i]==3)small|=1<<i;
 int triples=popcount((unsigned)small);
 if(triples>6)return false;
 int all=(1<<p)-1, quart=all^small;
 bool passed=false;
 for(int branch=1;branch<=all;branch++){
  int priv=all^branch, nb=popcount((unsigned)branch), ns=p-nb;
  if(nb>6 || ns>2*(6-nb))continue;
  int own=0;
  for(int i=0;i<p;i++)if(priv>>i&1)own+=popcount((unsigned)(priv&adj[i]));
  if(own>2)continue;
  int privateQ=priv&quart;
  for(int dirty=privateQ;;dirty=(dirty-1)&privateQ){
   int clean=priv^dirty, nc=popcount((unsigned)clean), disjoint=0, slots=0;
   for(int i=0;i<p;i++)if(clean>>i&1){
    slots+=k[i]; disjoint+=popcount((unsigned)(clean&adj[i]));}
   int outside=13-(slots-disjoint/2), term=nc+(outside>=2);
   bool ok=nc<=6-nb && term<=p-1;
   for(int i=0;i<p;i++)
    if(k[i]+max(2,d[i])+popcount((unsigned)(clean&~(adj[i]|(1<<i))))>cap)ok=false;
   if(ok){
    int graph=0;
    for(int i=0,bit=0;i<p;i++)for(int j=0;j<i;j++,bit++)if(adj[i]>>j&1)graph|=1<<bit;
    static set<vector<int>> seen;
    if(seen.insert({p,graph,quart,branch,dirty}).second)
     fprintf(stderr,"%d %d %d %d %d %d\n",p,graph,clean,branch,quart,dirty);
    hist[{p,triples,popcount((unsigned)(small&branch)),popcount((unsigned)(quart&branch)),popcount((unsigned)dirty)}]++;passed=true;
   }
   if(!dirty)break;
  }
 }
 return passed;
}
void edges(int i){
 while(i<p&&!rem[i])i++;
 if(i==p){if(valid())++countGraphs;return;}
 int cand=0;
 for(int j=i+1;j<p;j++)if(rem[j]&&(k[i]!=2||k[j]!=2))cand|=1<<j;
 if(popcount((unsigned)cand)<rem[i])return;
 for(int s=cand;s;s=(s-1)&cand)if(popcount((unsigned)s)==rem[i]){
  for(int j=i+1;j<p;j++)if(s>>j&1){--rem[j];adj[j]|=1<<i;}
  adj[i]|=s;edges(i+1);adj[i]^=s;
  for(int j=i+1;j<p;j++)if(s>>j&1){++rem[j];adj[j]^=1<<i;}
 }
}
void seq(int i,int sk,int sd,int b,int largest){
 if(sk+3*(p-i)>26)return;
 if(i==p){
  if(sd%2||sk-sd/2>13)return;
  ++types;copy(d,d+p,rem);edges(0);return;
 }
 for(int x=3;x<=min(4,cap-2);x++)for(int y=0;y<=min({x,p-1,cap-x});y++){
  if(i&&(x<k[i-1]||(x==k[i-1]&&y<d[i-1])))continue;
  k[i]=x;d[i]=y;seq(i+1,sk+x,sd+y,b+(x==2),max(largest,x));
 }
}
int main(int argc,char**argv){a=atoi(argv[1]);p=atoi(argv[2]);cap=p+2;seq(0,0,0,0,0);
printf("a%d p%d types %lld decorated graphs %lld\n",a,p,types,countGraphs);
for(auto [parts,c]:hist){for(int v:parts)printf("%d ",v);printf(" %lld\n",c);}}
