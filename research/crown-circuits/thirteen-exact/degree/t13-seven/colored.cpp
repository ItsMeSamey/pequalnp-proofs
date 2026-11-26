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
 bool passed=false;
 for(int mask=small;;mask=(mask-1)&small){
  int b=popcount((unsigned)mask), priv=small^mask, s=triples-b;
  int overlap=0;
  for(int i=0;i<p;i++)if(priv>>i&1)overlap+=popcount((unsigned)(priv&adj[i]));
  overlap/=2;
  int clean=s+int(13-(3*s-overlap)>=2);
  bool star=true;
  for(int i=0;i<p;i++){
   int dead=popcount((unsigned)(priv&~(adj[i]|(1<<i))));
   if(k[i]+max(2,d[i])+dead>cap)star=false;
  }
  if(overlap<=1 && clean<=p-1 && (b || p>triples) && star){
   int graph=0;
   for(int i=0,bit=0;i<p;i++)for(int j=0;j<i;j++,bit++)if(adj[i]>>j&1)graph|=1<<bit;
   static set<vector<int>> seen;
   if(seen.insert({p,graph,priv,mask}).second)fprintf(stderr,"%d %d %d %d\n",p,graph,priv,mask);
   vector<int> row={p,triples,b,(int)parts.size()};hist[row]++;passed=true;
  }
  if(mask==0)break;
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
 for(int x=3;x<=min(5,cap-2);x++)for(int y=0;y<=min({x,p-1,cap-x});y++){
  if(i&&(x<k[i-1]||(x==k[i-1]&&y<d[i-1])))continue;
  k[i]=x;d[i]=y;seq(i+1,sk+x,sd+y,b+(x==2),max(largest,x));
 }
}
int main(int argc,char**argv){a=atoi(argv[1]);p=atoi(argv[2]);cap=p+2;seq(0,0,0,0,0);
printf("a%d p%d types %lld decorated graphs %lld\n",a,p,types,countGraphs);
for(auto [parts,c]:hist){for(int v:parts)printf("%d ",v);printf(" %lld\n",c);}}
