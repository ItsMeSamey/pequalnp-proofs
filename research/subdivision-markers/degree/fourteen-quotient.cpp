#include <array>
#include <algorithm>
#include <vector>
#include <set>
#include <random>
#include <cstdio>
using namespace std;
using R=array<int,6>;
int brank(R rows){int b[5]={},k=0;for(int x:rows)while(x){int i=31-__builtin_clz(x);if(b[i])x^=b[i];else{b[i]=x;k++;break;}}return k;}
int main(){
 mt19937 rng(36091);
 for(int h:{1,3}){
 set<R> seen,charts;
 for(int z=0;z<(1<<20);z++){R n{};for(int i=0;i<5;i++){int v=z>>(4*i)&15;n[i]=v|(__builtin_parity(v)<<4);n[5]^=n[i];}
 sort(n.begin(),n.begin()+h);sort(n.begin()+h,n.end());if(seen.count(n)||brank(n)!=4)continue;
 charts.insert(n);array<int,5> pm={0,1,2,3,4};do{R v{};for(int i=0;i<6;i++)for(int j=0;j<5;j++)v[i]|=((n[i]>>pm[j])&1)<<j;sort(v.begin(),v.begin()+h);sort(v.begin()+h,v.end());seen.insert(v);if(h==3){rotate(v.begin(),v.begin()+3,v.end());seen.insert(v);}}while(next_permutation(pm.begin(),pm.end()));}
 int hits=0;for(auto n:charts){
 int mat[7];for(int i=0;i<6;i++)mat[i]=n[i]|(i<h?32:64);mat[6]=31;
 vector<char>d(16384,0),adj(8192,0);int q=64*128+96,r=63*128+31;
 for(int x=0;x<128;x++)for(int y=0;y<128;y++){int dc=0,cr=0;for(int i=0;i<7;i++){if(x>>i&1)dc^=mat[i];cr|=__builtin_parity(mat[i]&y)<<i;}if((dc&y)||(cr&x))continue;int v=x*128+y;if(v!=q)d[v^q]=1;if(v!=r)d[v^r]=1;}
 vector<int> opts;for(int i=1;i<8192;i++)if(d[i]&&d[i^16383]){adj[i]=1;opts.push_back(i);}
 vector<int> clique;for(int it=0;it<200&&clique.size()<9;it++){
 clique={0};vector<int> cand=opts;while(!cand.empty()&&clique.size()<9){int v=cand[rng()%cand.size()];clique.push_back(v);cand.erase(remove_if(cand.begin(),cand.end(),[&](int u){return !adj[u^v];}),cand.end());}}
 if(clique.size()==9)hits++;printf("%d %d",h,int(clique.size()==9));for(int v:n)printf(" %d",v);if(clique.size()==9){printf(" :");for(int v:clique)printf(" %d",v);}puts("");
 }
 fprintf(stderr,"sector %d: %d of %zu K9\n",h,hits,charts.size());
 }}
