#include <algorithm>
#include <array>
#include <cmath>
#include <cstdio>
#include <numeric>
#include <vector>
using namespace std;
struct Row {int mask,y;};
int r,D,cap,a[7]; long long ntests=0,nrank=0,uncert=0;
int rank_rows(const vector<Row>& rows){
 int basis[7][7]={};int rank=0;
 for(auto s:rows){int b[7]; for(int i=0;i<r;i++) b[i]=(s.mask>>i&1)?1008:1;
  for(int i=0;i<r;i++)if(b[i]){
   if(!basis[i][i]){copy(b,b+r,basis[i]); rank++;break;}
   int pivot=b[i],d=basis[i][i];for(int j=i;j<r;j++) b[j]=(1009*1009+b[j]*d-pivot*basis[i][j])%1009;
  }
  if(rank==r)break;
 }return rank;
}
bool affine_on(const vector<Row>& rows,int pair,int bit){
 int piv[8]={};for(auto s:rows)if(__builtin_parity(s.mask&pair)==bit){
  int q=1|s.mask|(s.y<<r);
  for(int i=0;i<r;i++)if(q>>i&1){if(!piv[i]){piv[i]=q;q=0;break;}q^=piv[i];}
  if(q)return false;
 }return true;
}
void test(){
 int g=D,odd=0;for(int i=0;i<r;i++){g=gcd(g,a[i]);odd+=a[i]%2;}if(g!=1||(odd!=4&&odd!=6))return;
 ntests++;
 vector<Row> rows;
 for(int m=0;m<1<<r;m+=2){int v=0;for(int i=0;i<r;i++)v+=(m>>i&1)?-a[i]:a[i];if(abs(v)==D)rows.push_back({m,v<0});}
 if(rows.size()<(size_t)r||rank_rows(rows)!=r)return;
 nrank++;
 for(int i=0;i<r;i++)for(int j=i+1;j<r;j++)for(int bit=0;bit<=1;bit++)
  if(affine_on(rows,(1<<i)|(1<<j),bit))return;
 uncert++;
}
void gen(int i,int low){if(i==r){test();return;}for(int x=low;x<=cap;x++){a[i]=x;gen(i+1,x);}}
int main(){for(r=6;r<=7;r++){cap=r==6?6:14;for(D=4;D<=cap;D+=4){ntests=nrank=uncert=0;gen(0,1);printf("r=%d D=%d patterns=%lld fullrank=%lld uncertified=%lld\n",r,D,ntests,nrank,uncert);}}}
