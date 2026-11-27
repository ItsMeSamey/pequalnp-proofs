#include <algorithm>
#include <cassert>
#include <iostream>
#include <vector>
using namespace std;
using Bank=vector<int>; const int F=65535; int target=63,maps[12][65536]; long long visits[5];
vector<int> tests; vector<int> trail; int lastA=-1,lastB=-1;
bool run(const Bank& b,int k,bool root){
 visits[k]++;int good=F;for(int x:b)if((x&target)==target)good&=x;if(good==target)return true;
 if(k==1){for(int x:b)if(((F^x)&good)==target){lastA=x;return true;};
 for(int x:b)if(!(x&good&~target))for(int y:b)if(!(y&good&~target)&&((x|y)&target)==target){lastA=x;lastB=y;return true;};return false;}
 bool old[65536]={},seen[65536]={};for(int x:b)old[x]=true;
 auto step=[&](int h){if(old[h]||seen[h])return false;seen[h]=true;if(root)for(int g=0;g<12;g++)if(maps[g][h]<h)return false;
 Bank v=b;bool has[65536];copy(old,old+2048,has);for(int x:b){int t=x&h;if(!has[t]){has[t]=true;v.push_back(t);}}if(run(v,k-1,false)){trail.push_back(h);return true;}return false;};
 for(int x:b)if(step(F^x))return true;for(int x:b)for(int y:b)if(x<y&&step(x|y))return true;return false;}
int main(){
 for(int i=0;i<6;i++)tests.push_back((1<<i)|(1<<((i+1)%6)));
 auto ind=[](int x){for(int i=0;i<6;i++)if((x&tests[i])==tests[i])return false;return true;};
 for(int x=0;x<64;x++)if(ind(x)){bool maximal=true;for(int j=0;j<6;j++)if(!(x>>j&1)&&ind(x|1<<j))maximal=false;if(maximal)tests.push_back(x);}assert(tests.size()==11);tests.push_back(0);tests.push_back(63);for(int j=0;j<3;j++)tests.push_back(63^(1<<j)^(1<<(j+3)));
 for(int g=0;g<12;g++){int p[16];for(int j=0;j<16;j++){int s=0;for(int i=0;i<6;i++)if(tests[j]>>i&1)s|=1<<((g+(g<6?i:6-i))%6);p[j]=find(tests.begin(),tests.end(),s)-tests.begin();assert(p[j]<16);}for(int h=0;h<=F;h++)for(int j=0;j<16;j++)if(h>>j&1)maps[g][h]|=1<<p[j];}
 Bank b;for(int x=0;x<64;x++){int h=0;for(int j=0;j<16;j++)if((x&tests[j])==x)h|=1<<j;b.push_back(h);}sort(b.begin(),b.end());b.erase(unique(b.begin(),b.end()),b.end());
 target=F^b[b.size()/2];assert(run(b,1,false));target=63;fill(visits,visits+5,0);
 lastA=-1;lastB=-1;cout<<"k4 "<<run(b,4,true)<<" visits";for(auto z:visits)cout<<" "<<z;cout<<" last "<<lastA<<" "<<lastB<<" trail";for(int h:trail)cout<<" "<<h;cout<<endl;}
