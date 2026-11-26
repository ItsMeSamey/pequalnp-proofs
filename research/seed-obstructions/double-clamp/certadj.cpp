#include <cstdio>
#include <vector>
#include <map>
#include <set>
#include <tuple>
#include <array>
#include <cstring>
#include <algorithm>
#include <fstream>
#include <string>
using namespace std;
struct DB{array<int,7> stars;vector<vector<int>> neg[7];short cache[7][128][128];short seen[7][128][128];
 DB(int bad){memset(cache,-1,sizeof(cache));ifstream fin("neg."+to_string(bad));for(int &s:stars)fin>>s;
 for(int t=0;t<7;t++)for(int x=0;x<9;x++){int k;fin>>k;vector<int> w(k);for(int &v:w)fin>>v;neg[t].push_back(w);}}
 int blockers(int t,int a,int b){if(a>b)swap(a,b);auto &mem=cache[t][a][b];if(mem!=-1)return mem;int bad=0,possible=0;for(auto &ns:neg[t]){int witnessed=0;for(int n:ns)if((a&n)&&(b&n))witnessed|=n;bad|=127^witnessed;possible|=witnessed;}seen[t][a][b]=possible;mem=bad;return bad;}
};
int pop(int x){return __builtin_popcount((unsigned)x);}
bool placement(DB &db,int S,int R,int lc,int punct,int A,int B,bool joint,int rescued=0){
 if((joint&&A)||(!joint&&A&&B))lc++;
 int alone[7],paircost[7];int dp[4]={0,99,99,99};for(int t=0;t<7;t++){int T=1<<t;int sibling=127^T;if((A&T)&&pop(A)>1)sibling&=A;if((B&T)&&pop(B)>1)sibling&=B;
 int ag=127,bg=127,avail=0;
 if(A&T){avail|=1;ag=(A^T)&((S&T)?127:(127^S));if(joint)ag&=(R&T)?127:(127^R);}
 if(B&T){avail|=2;bg=(B^T)&((R&T)?127:(127^R));}
 int repair=pop(db.stars[t]&~rescued);
 db.blockers(t,ag,bg);int support=db.seen[t][min(ag,bg)][max(ag,bg)];int credit=(sibling&~support)?0:1;
 alone[t]=4-credit;paircost[t]=99; int next[4]={99,99,99,99};for(int st=0;st<4;st++)if(dp[st]<98)next[st]=dp[st]+4-credit;
 for(int ret=0;ret<4;ret++){if(ret&~avail)continue;int a=(ret&1)?127:ag,b=(ret&2)?127:bg;
 if(db.blockers(t,a,b)&sibling)continue;if(ret==0)alone[t]=min(alone[t],repair);if(ret==1)paircost[t]=repair;
 for(int st=0;st<4;st++)if(!(st&ret))next[st|ret]=min(next[st|ret],dp[st]+repair);}
 copy(next,next+4,dp);}
 if(*min_element(dp,dp+4)<=lc+2)return true;
 if(joint)for(int t=0;t<7;t++)for(int u=0;u<t;u++)if(paircost[t]<99&&paircost[u]<99){
 int ft=bool(S&(1<<t))+2*bool(R&(1<<t)),fu=bool(S&(1<<u))+2*bool(R&(1<<u));const int raw[7]={708,1416,2832,5664,3137,6274,4357};bool opposite=pop(S)==2&&pop(R)==2&&pop(S&R)==1&&((ft==1&&fu==2)||(ft==2&&fu==1))&&!(raw[t]&raw[u]&raw[__builtin_ctz((unsigned)(S&R))]);int cost=opposite?3:max(3,paircost[t]+paircost[u]+2);for(int i=0;i<7;i++)if(i!=t&&i!=u)cost+=alone[i];if(cost<=lc+2)return true;}return false;
}
int main(){map<tuple<int,int,int>,int> covered;{int s,r,a,q;ifstream f("jointpartial");while(f>>s>>r>>a>>q)covered[{s,r,a}]=q;}set<tuple<int,int,int>> jointpass;{int s,r,a;ifstream f("jointgood");while(f>>s>>r>>a)jointpass.emplace(s,r,a);}map<int,DB> all;int s,r,l,p;while(scanf("%d%d%d%d",&s,&r,&l,&p)==4){if(!all.count(p))all.emplace(p,DB(p));auto &db=all.at(p);bool ok=true;
 for(int a=0;a<128&&ok;a++){if(!jointpass.count({s,r,a})&&!placement(db,s,r,l,p,a,0,true,covered[{s,r,a}])){ok=false;break;}for(int b=0;b<128;b++){int inter=a&b;if(inter&&inter!=a&&inter!=b)continue;if(!placement(db,s,r,l,p,a,b,false)){ok=false;break;}}}
 printf("%d %d %d %d %d\n",s,r,l,p,(int)ok);}}
