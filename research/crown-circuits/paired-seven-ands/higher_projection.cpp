#include <array>
#include <bit>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;
int main(int argc,char**argv){
 if(argc<3)return 2;int d=atoi(argv[1]);ifstream in(argv[2]);int id,c,cap;
 vector<int> seen(16384,-1);
 while(in>>id>>c>>cap){vector<int>t(d);for(int&v:t)in>>v;
  int n=0;array<int,14>count{};for(int s=0;s<128;s++){
   int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(s>>j&1));
   if(seen[m]==id)continue;seen[m]=id;++n;
   for(int a=m;a;a&=a-1)++count[countr_zero(static_cast<unsigned>(a))];
  }
  if(n!=cap)return 3;int low=128;for(int v:count)low=min(low,v);
  cout<<id<<" "<<c<<" "<<cap<<" "<<low<<"\n";
 }
}
