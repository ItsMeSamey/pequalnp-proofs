#include <array>
#include <bit>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <vector>
using namespace std;using U=__uint128_t;
int main(int argc,char**argv){if(argc<3)return 2;int d=atoi(argv[1]);ifstream in(argv[2]);int id,c,cap;vector<int>seen(16384,-1);
while(in>>id>>c>>cap){vector<int>t(d);for(int&m:t)in>>m;array<int,14>ct{};array<U,14>b{};int n=0;
for(int s=0;s<128;s++){int m=0;for(int j=6;j>=0;j--)if(j>=d||(m&t[j]))m|=1<<(2*j+(s>>j&1));
 if(seen[m]==id)continue;seen[m]=id;for(int k=m;k;k&=k-1){int j=countr_zero((unsigned)k);++ct[j];b[j]|=U(1)<<n;}++n;}
if(n!=cap)return 3;int least=128;for(int v:ct)least=min(least,v);
auto clash=[&](auto&& self,int start,int rem,U used)->bool{if(!rem)return true;
 for(int j=start;j+rem<=14;j++)if(b[j]&&!(used&b[j])&&self(self,j+1,rem-1,used|b[j]))return true;return false;};
bool impossible=n<11||least<2||clash(clash,0,6,0);cout<<id<<" "<<c<<" "<<n<<" "<<least<<" "<<(!impossible)<<"\n";
}}
