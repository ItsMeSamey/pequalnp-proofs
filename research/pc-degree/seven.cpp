#include <algorithm>
#include <array>
#include <cstdio>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
using U=unsigned;
int par(U x){return __builtin_parity(x);}
int highest(U x){return 31-__builtin_clz(x);}
struct Ring{
 U mon[7][7]={};
 Ring(){int a=8;for(int i=0;i<7;i++)for(int j=i;j<7;j++)mon[i][j]=mon[j][i]=i==j?1u<<(i+1):1u<<a++;}
 bool refutes(vector<U> queue) const{
  U piv[32]={};
  for(size_t f=0;f<queue.size();f++){
   U x=queue[f];while(x&&piv[highest(x)])x^=piv[highest(x)];
   if(x==1)return true;
   if(!x)continue;
   piv[highest(x)]=x;
   if(x<256)for(int j=0;j<7;j++){
    U y=(x&1)?1u<<(j+1):0;
    for(int i=0;i<7;i++)if(x>>(i+1)&1)y^=mon[i][j];
    queue.push_back(y);
   }
  }
  return false;
 }
};
struct Chart{
 array<int,3> forms;
 array<unsigned char,128> label;
};
int main(){
 Ring ring;
 vector<Chart> charts;
 for(int p=0;p<7;p++)for(int q=p+1;q<7;q++)for(int t=q+1;t<7;t++){
  array<int,3> piv={p,q,t};
  vector<pair<int,int>> free;
  for(int i=0;i<3;i++)for(int j=piv[i]+1;j<7;j++)if(j!=q&&j!=t)free.push_back({i,j});
  for(int mask=0;mask<(1<<(int)free.size());mask++){
   Chart chart{};for(int i=0;i<3;i++)chart.forms[i]=1<<piv[i];
   for(int k=0;k<(int)free.size();k++)if(mask>>k&1)chart.forms[free[k].first]|=1<<free[k].second;
   for(int x=0;x<128;x++)for(int i=0;i<3;i++)chart.label[x]|=par(chart.forms[i]&x)<<i;
   charts.push_back(chart);
  }
 }
 long total=0;
 for(int k=1;k<=3;k++){
  int m=7-k;set<int> seen;
  for(int bits=0;bits<1<<(k*m);bits++){
   if(seen.count(bits))continue;
   vector<int> a(k),jp(m);iota(jp.begin(),jp.end(),0);
   for(int i=0;i<k;i++)a[i]=(bits>>(i*m))&((1<<m)-1);
   do{
    vector<int> b(k);
    for(int i=0;i<k;i++)for(int j=0;j<m;j++)b[i]|=((a[i]>>j)&1)<<jp[j];
    sort(b.begin(),b.end());
    do{int h=0;for(int i=0;i<k;i++)h|=b[i]<<(i*m);seen.insert(h);}while(next_permutation(b.begin(),b.end()));
   }while(next_permutation(jp.begin(),jp.end()));
   vector<U> guards(7);int adj[7]={};
   for(int i=0;i<k;i++)for(int j=0;j<m;j++)if(a[i]>>j&1){
    adj[i]|=1<<(k+j);adj[k+j]|=1<<i;
    guards[i]^=ring.mon[i][k+j];guards[k+j]^=ring.mon[i][k+j];
   }
   vector<int> feasible;
   for(int x=0;x<128;x++){
    bool ok=true;for(int i=0;i<7;i++)if((x>>i&1)&&par(x&adj[i]))ok=false;
    if(ok)feasible.push_back(x);
   }
   for(auto &chart:charts){
    int image=0;for(int x:feasible){image|=1<<chart.label[x];if(image==255)break;}
    for(int b=1;b<8;b++)if(!(image>>b&1)){
     auto eq=guards;for(int j=0;j<3;j++)eq.push_back((chart.forms[j]<<1)|((b>>j)&1));
     total++;
     if(!ring.refutes(eq)){
      printf("degree>2 split=%d rows=",k);for(int r:a)printf(" %d",r);
      printf(" forms=");for(int v:chart.forms)printf(" %d",v);printf(" target=%d\n",b);return 0;
     }
    }
   }
  }
  printf("split %d cumulative %ld\n",k,total);fflush(stdout);
 }
 printf("all %zu charts tested\n",charts.size());
}
