#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
int wt(int v){return popcount((unsigned)v);}
struct Costs{
 array<array<int,16>,5> id{};array<vector<int>,5> best;
 Costs(){for(int d=1;d<=4;d++){
  int N=1<<d;vector<int> nonsingle;
  for(int m=1;m<N;m++)if(wt(m)>1){id[d][m]=1<<nonsingle.size();nonsingle.push_back(m);}
  int z=1<<nonsingle.size();best[d].assign(z,100);
  for(int s=0;s<z;s++){bool good=true;
   for(int m:nonsingle)if(s&id[d][m]){
    bool ready=false;
    for(int a=(m-1)&m;a&&!ready;a=(a-1)&m)if(wt(a)==1||(s&id[d][a]))
     for(int b=(m-1)&m;b;b=(b-1)&m)if((wt(b)==1||(s&id[d][b]))&&(a|b)==m){ready=true;break;}
    if(!ready){good=false;break;}
   }if(good)best[d][s]=wt(s);
  }
  for(int k=0;k<(int)nonsingle.size();k++)for(int s=0;s<z;s++)if(!(s>>k&1))best[d][s]=min(best[d][s],best[d][s|1<<k]);
 }}
};
uint64_t signature(array<int,3> t,int k){
 array<unsigned,7> a;for(int j=0;j<7;j++){int x=0,y=0;int v[4]={t[0],t[1],t[2],k};
  for(int i=0;i<4;i++){if(v[i]>>(2*j)&1)x|=1<<i;if(v[i]>>(2*j+1)&1)y|=1<<i;}
  if(x>y)swap(x,y);a[j]=(x<<4)|y;}
 sort(a.begin()+3,a.end());uint64_t h=0;for(int c:a)h=h<<8|c;return h;
}
#ifndef COST_NO_MAIN
int main(int argc,char**argv){
 if(argc<2)return 2;Costs C;ifstream in(argv[1]);int index;array<int,3>t;
 while(in>>index>>t[0]>>t[1]>>t[2]){
  if(wt(t[0])>4)continue;int d=0,v[3]={},all=t[0]|t[1]|t[2];
  for(int x:t)if(find(v,v+d,x)==v+d)v[d++]=x;
  array<int,8> groups{};for(int j=0;j<14;j++){int p=0;for(int i=0;i<d;i++)if(v[i]>>j&1)p|=1<<i;groups[p]|=1<<j;}
  set<uint64_t> keys;int raw=0;
  for(int k=3;k<16384;k+=4){int r=wt(k&~(t[0]|3));
   if(r<2||wt(t[0])+r>6||wt(k)>7)continue;
   int x=k;for(int i=0;i<3;i++)if((x>>(2*i)&3)==3)x|=t[i];if(x&(x>>1)&0x1540)continue;
   int req=0;for(int p=0;p<(1<<d);p++){if(groups[p]&k)req|=C.id[d+1][p|(1<<d)];if(groups[p]&~k)req|=C.id[d+1][p];}
   int cost=wt(all|k)-(d+1)+C.best[d+1][req];if(cost>6)continue;
   ++raw;keys.insert(signature(t,k));
  }
  cout<<index<<" "<<t[0]<<" "<<t[1]<<" "<<t[2]<<" "<<raw<<" "<<keys.size()<<'\n';
 }
}

#endif
