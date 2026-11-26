#include <algorithm>
#include <array>
#include <vector>
#include <set>
#include <random>
#include <cstdio>
using namespace std;
using Rows=array<int,5>;
int binary_rank(Rows n){int b[6]={},k=0;for(int x:n)while(x){int i=31-__builtin_clz(x);if(b[i])x^=b[i];else{b[i]=x;k++;break;}}return k;}
bool exact(const vector<int>& opts,vector<int>& cert,int lower){
 if(cert.size()==5)return true;
 if(opts.size()<(1u<<(5-cert.size()))-1)return false;
 for(int b:opts){
  if(b<lower)continue;
  int upper=1<<(32-__builtin_clz(b));
  cert.push_back(b);
  if(cert.size()==5)return true;
  vector<int> next;
  for(int v:opts)if(v>=upper&&v<(v^b)&&binary_search(opts.begin(),opts.end(),v^b))next.push_back(v);
  if(exact(next,cert,upper))return true;
  cert.pop_back();
 }
 return false;
}
int main(){
 mt19937 rng(93621);
 for(bool split:{false,true}){
 int X=split?4:5, ex=(1<<X),ny=split?7:6;
 set<Rows> charts,seen;
 for(int z=0;z<1<<(4*(X-1));z++){
 Rows a{};for(int i=0;i<X-1;i++){int row=(z>>(4*i))&15;a[i]=row|(__builtin_parity(row)<<4);a[X-1]^=a[i];}
 sort(a.begin()+split,a.begin()+X);
 if(seen.count(a)||binary_rank(a)!=X-1)continue;
 charts.insert(a);array<int,5> pm={0,1,2,3,4};
 do{Rows w{};for(int i=0;i<X;i++)for(int j=0;j<5;j++)w[i]|=((a[i]>>pm[j])&1)<<j;
 sort(w.begin()+split,w.begin()+X);seen.insert(w);
 }while(next_permutation(pm.begin(),pm.end()));
 }
 int solved=0;
 for(auto a:charts){
 int mat[6]={};for(int i=0;i<X;i++)mat[i]=a[i]|(split&&i?64:32);mat[X]=31;
 int q=(ex<<ny)|((1<<ny)-32),r=((ex-1)<<ny)|31;
 vector<bool>D(4096);for(int x=0;x<2*ex;x++)for(int y=0;y<(1<<ny);y++){
 int dc=0,cr=0;for(int i=0;i<=X;i++){if(x>>i&1)dc^=mat[i];cr|=__builtin_parity(mat[i]&y)<<i;}
 if((x&cr)||(y&dc))continue;int v=(x<<ny)|y;if(v!=q)D[v^q]=1;if(v!=r)D[v^r]=1;}
 vector<int> base;for(int i=1;i<4096;i++)if(D[i])base.push_back(i);
 bool ok=false;vector<int> cert;
 for(int attempt=0;attempt<400&&!ok;attempt++){
 vector<int> opts=base,space={0};cert.clear();
 while(!opts.empty()&&cert.size()<5){int b=opts[rng()%opts.size()];cert.push_back(b);int s=space.size();for(int j=0;j<s;j++)space.push_back(space[j]^b);vector<int> next;for(int v:opts){bool good=true;for(int j=s;j<2*s;j++)if(!D[v^space[j]]){good=false;break;}if(good)next.push_back(v);}opts.swap(next);}
 ok=cert.size()==5;}
 if(!ok){cert.clear();ok=exact(base,cert,1);} if(ok)solved++;
 printf("%d %d",split,ok);for(int i=0;i<X;i++)printf(" %d",a[i]);if(ok){printf(" :");for(int v:cert)printf(" %d",v);}puts("");
 }
 fprintf(stderr,"split %d charts %zu pg found %d\n",split,charts.size(),solved);
 }}
