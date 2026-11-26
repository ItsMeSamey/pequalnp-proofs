#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
using namespace std;
using Family=array<int,10>;
int main(int argc,char**argv){
 if(argc<3)return 1;
 ifstream groups(argv[1]);array<array<unsigned short,8192>,24> transforms{};
 for(auto& map:transforms){
   array<int,13> p;
   for(int&x:p)if(!(groups>>x))return 2;
   for(unsigned x=1;x<8192;x++)map[x]=map[x&(x-1)]|(1<<p[countr_zero(x)]);
 }
 int limit=stoi(argv[2]);
 Family f,temp;set<Family> reps;
 int n=0,bound;
 while(cin>>f[0]){
  for(int i=1;i<10;i++)if(!(cin>>f[i]))return 3;
  if(!(cin>>bound))return 4;
  if(bound>limit)continue;
  ++n;
  Family best=f;
  sort(best.begin(),best.end());
  for(auto&pm:transforms){
   for(int i=0;i<10;i++)temp[i]=pm[f[i]];
   sort(temp.begin(),temp.end());
   best=min(best,temp);
  }
  reps.insert(best);
 }
 for(auto&r:reps){for(int x:r)cout<<x<<' ';cout<<'\n';}
 cerr<<"cases "<<n<<" reps "<<reps.size()<<endl;
}
