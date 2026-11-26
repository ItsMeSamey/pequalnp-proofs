#include <algorithm>
#include <array>
#include <cstdio>
#include <vector>
using namespace std;
constexpr int full=(1<<10)-1,target=full^15;
long long levels[4]={};
bool can(vector<int> const &cl,int k){
 levels[3-k]++;
 if(binary_search(cl.begin(),cl.end(),target))return true;
 if(!k)return false;
 array<bool,1024> seen{};
 for(int i=0;i<(int)cl.size();i++)for(int j=0;j<i;j++){
  int x=cl[i]|cl[j];if(seen[x]||binary_search(cl.begin(),cl.end(),x))continue;
  seen[x]=true;vector<int> next=cl;for(int y:cl)next.push_back(x&y);
  sort(next.begin(),next.end());next.erase(unique(next.begin(),next.end()),next.end());if(can(next,k-1))return true;
 }return false;
}
int main(){array<int,4>w={1,2,4,8};int c=4;for(int a=0;a<4;a++)for(int b=a+1;b<4;b++,c++){w[a]|=1<<c;w[b]|=1<<c;}
 vector<int>cl{0,full};for(int x:w){auto old=cl;for(int v:old)cl.push_back(x&v);}sort(cl.begin(),cl.end());cl.erase(unique(cl.begin(),cl.end()),cl.end());
 bool found=can(cl,3);printf("three_ORs_suffice=%d closures=%lld,%lld,%lld,%lld\n",found,levels[0],levels[1],levels[2],levels[3]);return found;}
