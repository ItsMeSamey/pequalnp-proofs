#include <cstdio>
#include <vector>
#include <array>
#include <algorithm>
#include <bit>
using namespace std;
#include "four.hpp"
using U=unsigned long long;
int main(){
 int f[9],tar[7]{},ext[8192],ok[8192]{};for(int i=0;i<13;i++)ok[1<<i]=1;
 bool primitive[8192]{};int all[13]{};for(int j=0;j<13;j++){for(int d:{0,1,3,9})all[j]|=1<<((j+d)%13);if(j<6){ok[all[j]]=ok[(1<<j)|(1<<(j+1))]=ok[(1<<(j+3))|(1<<((j+9)%13))]=1;}else tar[j-6]=all[j];}
 for(int m=0;m<8192;m++)primitive[m]=ok[m];primitive[0]=true;
 for(int m=0;m<8192;m++){ext[m]=none_of(all,all+13,[&](int t){return !(m&~t);});for(int t:tar)if(!(m&~t))ok[m]=1;}
 while(scanf("%d",f)==1){for(int i=1;i<9;i++)scanf("%d",f+i);
 vector<vector<pair<int,int>>> tests[9];
 for(auto&ts:tests){int n;scanf("%d",&n);ts.resize(n);for(auto&ss:ts){int s;scanf("%d",&s);ss.resize(s);for(auto &[p,n]:ss)scanf("%d%d",&p,&n);}}
 int bound[512]{};
 for(int z=0;z<512;z++)for(int t:tar){
  vector<int> sub;for(int i=0;i<9;i++)if(!(z>>i&1)&&!(f[i]&~t)&&popcount((unsigned)f[i])>=2)sub.push_back(f[i]);
  int c=4;for(int s=0;s<(1<<sub.size());s++){int u=0;for(int i=0;i<sub.size();i++)if(s>>i&1)u|=sub[i];c=min(c,popcount((unsigned)(t^u))+popcount((unsigned)s));}bound[z]+=4-c;
 }
 int own[8192];for(int m=0;m<8192;m++){own[m]=-2;if(primitive[m])own[m]=-1;else for(int i=0;i<9;i++)if(!(m&~f[i]))own[m]=i;}
 U hist[22]{},live[22]{};
 for(int x=0;x<8192;x++){short unsafe[8192]{};
  for(int j=0;j<9;j++)for(auto&ss:tests[j]){int p=0,n=0;for(auto [a,b]:ss){if((x&a)&&!(x&b))continue;p|=a;n|=b;if(p&n)break;}if(p&n)continue;int free=8191&~(p|n);for(int u=free;;u=(u-1)&free){unsafe[p|u]|=1<<j;if(!u)break;}}
  for(int y=x;y<8192;y++){int b=bound[unsafe[y]];hist[b]++;
   if(b>15)continue;
   if(b>=12 && (own[x]==-2||own[y]==-2||(own[x]>=0&&own[x]==own[y]&&(x&y)&&(x&~y)&&(y&~x))))continue;
   live[b]++;int arr[11];copy(f,f+9,arr);arr[9]=x;arr[10]=y;if(!four_ready(arr,11,tar))continue;for(int v:f)printf("%d ",v);printf("%d %d\n",x,y);
  }
 }
 for(int k=0;k<22;k++)if(hist[k])fprintf(stderr,"%d %d %llu %llu\n",f[0],k,hist[k],live[k]);fflush(stderr);
 }
}
