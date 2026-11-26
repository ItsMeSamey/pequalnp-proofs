#include <vector>
#include <cstdlib>
#include <algorithm>
#include <iostream>
#include <array>
#include <sstream>
#include <string>
using namespace std;
int main(int argc,char**argv){
 int n=argc>1?atoi(argv[1]):10; array<int,7> targets{}; vector<int> raw;
 for(int i=0;i<13;i++)raw.push_back(1<<i);
 for(int j=0;j<6;j++){int a=(1<<j)|(1<<(j+1)),b=(1<<(j+3))|(1<<((j+9)%13));raw.push_back(a);raw.push_back(b);raw.push_back(a|b);}
 for(int j=0;j<7;j++)for(auto d:{0,1,3,9})targets[j]|=1<<((6+j+d)%13);
 string line;
 while(getline(cin,line)){
  istringstream in(line);vector<int> base=raw,f(n);for(int &v:f){if(!(in>>v))return 1;base.push_back(v);}int old=0;in>>old;
  sort(base.begin(),base.end());base.erase(unique(base.begin(),base.end()),base.end());
  array<int,7> c; c.fill(3);
  vector<int> mid;mid.reserve(1500);for(auto x:base)for(auto y:base){if(y>=x)break;mid.push_back(x&y);mid.push_back(x|y);}
  sort(mid.begin(),mid.end());mid.erase(unique(mid.begin(),mid.end()),mid.end());
  for(int j=0;j<7;j++){int t=targets[j];
    if(binary_search(base.begin(),base.end(),t)){c[j]=0;continue;}
    if(binary_search(mid.begin(),mid.end(),t)){c[j]=1;continue;}
    for(int x:base){
      if((x&~t) && (t&~x))continue;
      bool found=false;
      for(int y:mid){if((x&y)==t || (x|y)==t){found=true;break;}}
      if(found){c[j]=2;break;}
    }
  }
  int bound=21;for(int v:c)bound-=v;for(int v:f)cout<<v<<" ";cout<<max(old,bound)<<" "<<bound<<"\n";
 }
}
