#include <array>
#include <cstdint>
#include <iostream>
#include <map>
#include <utility>
#include <vector>
using Mask=uint32_t;
constexpr Mask all=(Mask(1)<<31)-1;
int pc(Mask x){return __builtin_popcount(x);}
using Rows=std::array<Mask,31>;
Rows rows,cols;
std::map<std::pair<int,int>,long> count;
long hits[31]={};
int largest=0;
Mask rot(Mask s){return ((s<<1)&all)|(s>>30);}
void walk(const Rows &f,const Rows &g,bool rev,int next,Mask x,Mask y){
  int a=pc(x),b=pc(y);
  if(b<a || (rev && b==a))return;
  if(y){
    Mask recomputed=all;
    for(Mask t=y;t;t&=t-1)recomputed &= ~g[__builtin_ctz(t)];
    if(recomputed==x){
      // Keep one representative in each simultaneous Singer rotation orbit.
      Mask z=x;
      bool leader=true;
      for(int j=1;j<31;j++){z=rot(z);if((z&1) && z<x){leader=false;break;}}
      if(leader){
        count[rev?std::make_pair(b,a):std::make_pair(a,b)]+=31;
        if(a*b>=largest){
          if(a*b>largest){largest=a*b; for(auto &h:hits) h=0;}
          Mask xx=rev?y:x, yy=rev?x:y;
          for(int i=0;i<31;i++)if(xx&(Mask(1)<<i))
            for(int j=0;j<31;j++)if(yy&(Mask(1)<<j))hits[(j+31-i)%31]++;
        }
      }
    }
  }
  if(a==8)return;
  for(int j=next;j<31;j++)
    walk(f,g,rev,j+1,x|(Mask(1)<<j),y & ~f[j]);
}
int main(){
  for(auto &r:rows)std::cin>>r;
  for(int i=0;i<31;i++)for(int j=0;j<31;j++)if(rows[i]&(Mask(1)<<j))cols[j]|=Mask(1)<<i;
  for(int i=0;i<31;i++)if(rot(rows[i])!=rows[(i+1)%31])return 2;
  walk(rows,cols,false,1,1,all & ~rows[0]);
  walk(cols,rows,true,1,1,all & ~cols[0]);
  for(auto [shape,number]:count)std::cout<<shape.first<<" "<<shape.second<<" "<<number<<"\n";
  std::cout<<"largest "<<largest<<" incidence of maximum rectangles per difference";
  for(long h:hits)std::cout<<" "<<h;
  std::cout<<"\n";
}
