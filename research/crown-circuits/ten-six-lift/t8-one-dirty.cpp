#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;
int d,n,dh;unsigned W,dirtyMask,cleanEven,full;int volume[16384];
struct Term{unsigned m;int sz;};
vector<unsigned> bank,hs,chosen;
long long banks=0,fr=0;
bool clash(unsigned a,unsigned b){unsigned m=a|b; if((m&dirtyMask)==dirtyMask)m|=W; return (m&(m>>1)&cleanEven)!=0;}
int width(unsigned m){return popcount(m);}
int id(unsigned m){return ((m&~W)?131072:0)+width(m)*16384+m;}
bool solve(vector<Term>const&ts,int idx,int left,int space){
 if(!left){ unsigned all=W;bool dirty=false;for(auto m:chosen){all|=m;dirty|=(m&dirtyMask)==dirtyMask;}return all==full && dirty;}
 for(int i=idx;i+left<=(int)ts.size();i++){auto [m,z]=ts[i];if(left*z>space)return false;
 bool ok=true;for(auto n:chosen)if(!clash(m,n)){ok=false;break;} if(!ok)continue;
 chosen.push_back(m);if(solve(ts,i+1,left-1,space-z))return true;chosen.pop_back();}return false;
}
array<unsigned,7> stamp(unsigned more){array<unsigned,7>ans{};for(int i=0;i<d;i++){unsigned a=0,b=0;auto f=[&](unsigned m){a=a*2+((m>>(2*i))&1);b=b*2+((m>>(2*i+1))&1);};f(W);for(auto m:hs)f(m);f(more);ans[i]=min(a,b)*256+max(a,b);}sort(ans.begin(),ans.begin()+d-1);return ans;}
bool run(int last){banks++;vector<unsigned> ms;for(int i=0;i<(int)bank.size();i++)for(int j=0;j<i;j++){auto m=bank[i]|bank[j];if(clash(m,m)||m==bank[i]||m==bank[j])continue;ms.push_back(m);}sort(ms.begin(),ms.end(),[](auto a,auto b){return id(a)>id(b);});ms.erase(unique(ms.begin(),ms.end()),ms.end());
 vector<Term> ts;int vol=0;for(auto m:ms){bool incl=false;for(auto z:ts)if((z.m&m)==m){incl=true;break;}if(incl)continue;ts.push_back({m,volume[m]});}
 sort(ts.begin(),ts.end(),[](auto a,auto b){return a.sz<b.sz;});for(int i=0;i<min(n,int(ts.size()));i++)vol+=ts[i].sz; if(find(bank.begin(),bank.end(),W)!=bank.end() && int(ts.size())>=n&&vol<=(1<<d)){fr++;if(solve(ts,0,n,1<<d)){printf("H");for(auto h:hs)printf(" %u",h);printf(" R");for(auto r:chosen)printf(" %u",r);puts("");return true;}}
 if(int(hs.size())==dh)return false;
 set<array<unsigned,7>> seen;reverse(ms.begin(),ms.end());for(auto m:ms){if((m&~W)&&find(bank.begin(),bank.end(),W)==bank.end())continue;if(id(m)<=last||find(bank.begin(),bank.end(),m)!=bank.end()||!seen.insert(stamp(m)).second)continue;hs.push_back(m);bank.push_back(m);if(run(id(m)))return true;bank.pop_back();hs.pop_back();}return false;
}
int main(int argc,char**argv){d=atoi(argv[2]);n=8;dh=4;dirtyMask=3u<<(2*d-2);cleanEven=((1u<<(2*d-2))-1)/3;full=(1u<<(2*d))-1;for(int i=0;i<atoi(argv[1]);i++)W|=1u<<(2*i); for(int z=0;z<(1<<d);z++){unsigned act=0;for(int i=0;i<d-1;i++)act|=1u<<(2*i+((z>>i)&1));if(act&W)act|=1u<<(2*d-2+((z>>(d-1))&1));for(int m=0;m<16384;m++)volume[m]+=!(act&m);}for(int i=0;i<2*d;i++)bank.push_back(1u<<i);bool hit=run(0);printf("hit %d banks %lld fronts %lld\n",hit,banks,fr);}
