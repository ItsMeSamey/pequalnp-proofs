#define main helper_driver_main
#include "helper.cpp"
#undef main
#include <random>
int main(){
 std::mt19937 rng(1931);
 for(int t=0;t<500;t++){Masks d;for(int i=0;i<12;i++)d.push_back(1+(rng()%63));
  for(int k=1;k<7;k++){bool yes=false;
   for(unsigned s=0;s<(1<<12)&&!yes;s++)if(std::popcount(s)==k){
    Mask used=0;bool ok=true;for(int i=0;i<12;i++)if((s>>i)&1){if(d[i]&used){ok=false;break;}used|=d[i];}yes=ok;}
   if(packing(d,k)!=yes)return 1;
  }
 }
 Mask left=0xaaaaaaaaaaaaaaaaULL,right=~left;
 Masks b={left,right};for(int i=0;i<10;i++){Mask bit=Mask(1)<<i;b.push_back((bit&left?left:right)^bit);}
 std::sort(b.begin(),b.end()); Profile positive{b,0};if(!positive.check())return 2;
 Profile negative{{left,right},3};if(negative.check())return 3;
 std::cout<<"3000 exhaustive packing comparisons, positive and negative library controls passed\n";
}
