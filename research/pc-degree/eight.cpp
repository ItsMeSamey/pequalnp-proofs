#include <algorithm>
#include <array>
#include <cstdio>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
using U=unsigned __int128;
int par(unsigned x){return __builtin_parity(x);}
int highest(U x){
 auto hi=(unsigned long long)(x>>64);
 return hi ? 127-__builtin_clzll(hi):63-__builtin_clzll((unsigned long long)x);
}
struct Ring{
 U mon[8][8]={}, mul[8][37]={};
 int low;
 Ring(int d){
  vector<int> mons; int pos[256]={};
  for(int k=0;k<=d;k++)for(int x=0;x<256;x++)if(__builtin_popcount((unsigned)x)==k){
   pos[x]=mons.size();mons.push_back(x);
  }
  low=d==2?9:37;
  for(int i=0;i<8;i++){
   for(int j=0;j<8;j++)mon[i][j]=U(1)<<pos[(1<<i)|(1<<j)];
   for(int m=0;m<low;m++)mul[i][m]=U(1)<<pos[mons[m]|(1<<i)];
  }
 }
 bool refutes(vector<U> queue) const{
  U piv[96]={};
  for(size_t f=0;f<queue.size();f++){
   U x=queue[f];while(x&&piv[highest(x)])x^=piv[highest(x)];
   if(x==1)return true;
   if(!x)continue;
   int h=highest(x);piv[h]=x;
   if(h<low)for(int j=0;j<8;j++){
    U y=0, v=x;
    while(v){int i=__builtin_ctzll((unsigned long long)v);v&=v-1;y^=mul[j][i];}
    queue.push_back(y);
   }
  }
  return false;
 }
};
struct Chart{
 array<int,3> forms;
 array<unsigned char,256> label;
};
int main(){
 Ring ring(2), degree3(3); long hard=0;
 vector<Chart> charts;
 for(int p=0;p<8;p++)for(int q=p+1;q<8;q++)for(int t=q+1;t<8;t++){
  array<int,3> piv={p,q,t};
  vector<pair<int,int>> free;
  for(int i=0;i<3;i++)for(int j=piv[i]+1;j<8;j++)if(j!=q&&j!=t)free.push_back({i,j});
  for(int mask=0;mask<(1<<(int)free.size());mask++){
   Chart chart{};for(int i=0;i<3;i++)chart.forms[i]=1<<piv[i];
   for(int k=0;k<(int)free.size();k++)if(mask>>k&1)chart.forms[free[k].first]|=1<<free[k].second;
   for(int x=0;x<256;x++)for(int i=0;i<3;i++)chart.label[x]|=par(chart.forms[i]&x)<<i;
   charts.push_back(chart);
  }
 }
 long total=0;
 for(int k=1;k<=4;k++){
  int m=8-k;set<int> seen;
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
   vector<U> guards(8);int adj[8]={};
   for(int i=0;i<k;i++)for(int j=0;j<m;j++)if(a[i]>>j&1){
    adj[i]|=1<<(k+j);adj[k+j]|=1<<i;
    guards[i]^=ring.mon[i][k+j];guards[k+j]^=ring.mon[i][k+j];
   }
   vector<int> feasible;
   for(int x=0;x<256;x++){
    bool ok=true;for(int i=0;i<8;i++)if((x>>i&1)&&par(x&adj[i]))ok=false;
    if(ok)feasible.push_back(x);
   }
   for(auto &chart:charts){
    int image=0;for(int x:feasible){image|=1<<chart.label[x];if(image==255)break;}
    for(int b=1;b<8;b++)if(!(image>>b&1)){
     auto eq=guards;for(int j=0;j<3;j++)eq.push_back((chart.forms[j]<<1)|((b>>j)&1));
     total++;
     if(!ring.refutes(eq)){
      ++hard; if(degree3.refutes(eq))continue;
      printf("degree>3 split=%d rows=",k);for(int r:a)printf(" %d",r);
      printf(" forms=");for(int v:chart.forms)printf(" %d",v);printf(" target=%d\n",b);return 0;
     }
    }
   }
  }
  printf("split %d cumulative %ld degree3 %ld\n",k,total,hard);fflush(stdout);
 }
 printf("all %zu charts tested\n",charts.size());
}
