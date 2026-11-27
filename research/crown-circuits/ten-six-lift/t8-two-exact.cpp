#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdio>
#include <cstdlib>
#include <set>
#include <vector>
using namespace std;
struct Term { int m,v; };
struct Search {
 int w,q,stage[4096],key[4096],volume[4096],close[4096];
 vector<int> bank,helpers,chosen;
 long long banks=0,fronts=0;
 Search(int W,int Q):w(W),q(Q) {
  for(int m=0;m<4096;m++){
   int v=m;
   if((v&768)==768)v|=w;
   if((v&3072)==3072)v|=q;
   close[m]=v;
   stage[m]=((m&~w)==0 ? ((m&~q)==0?0:1) : ((m&~q)==0?2:3));
   key[m]=(stage[m]*16+popcount((unsigned)m))*4096+m;
   int cnt=0;
   for(int z=0;z<64;z++){
    int blocked=0;
    for(int j=0;j<4;j++)blocked|=1<<(2*j+((z>>j)&1));
    if(blocked&q)blocked|=1<<(10+((z>>5)&1));
    if(blocked&w)blocked|=1<<(8+((z>>4)&1));
    cnt+=!(blocked&m);
   }
   volume[m]=cnt;
  }
  for(int i=0;i<12;i++)bank.push_back(1<<i);
 }
 bool hit(int a,int b) const {int v=close[a|b];return (v&(v>>1)&85)!=0;}
 bool has(int x) const{return find(bank.begin(),bank.end(),x)!=bank.end();}
 array<int,6> stamp(int x) const{
  array<int,6> out{};
  for(int j=0;j<6;j++){
   int a=0,b=0;
   auto add=[&](int m){a=a*2+((m>>(2*j))&1);b=b*2+((m>>(2*j+1))&1);};
   add(w);add(q);for(int m:helpers)add(m);add(x);
   out[j]=min(a,b)*256+max(a,b);
  }
  sort(out.begin(),out.begin()+4);return out;
 }
 bool receivers(const vector<Term>&t,int first,int left,int space){
  if(!left){
   int used=w|q;bool one=false,two=false;
   for(int m:chosen){used|=m;one|=(m&768)==768;two|=(close[m]&3072)==3072;}
   return used==4095&&one&&two;
  }
  for(int i=first;i+left<=(int)t.size();i++){
   if(left*t[i].v>space)break;
   bool ok=true;for(int m:chosen)if(!hit(t[i].m,m)){ok=false;break;}
   if(ok){chosen.push_back(t[i].m);if(receivers(t,i+1,left-1,space-t[i].v))return true;chosen.pop_back();}
  }
  return false;
 }
 bool run(int last){
  banks++;
  vector<int> joins;
  for(int i=0;i<(int)bank.size();i++)for(int j=0;j<i;j++){
   int m=bank[i]|bank[j];if(m!=bank[i]&&m!=bank[j]&&!hit(m,m))joins.push_back(m);
  }
  sort(joins.begin(),joins.end());joins.erase(unique(joins.begin(),joins.end()),joins.end());
  if(has(w)&&has(q)){
   vector<int> bysize=joins;sort(bysize.begin(),bysize.end(),[](int a,int b){return popcount((unsigned)a)>popcount((unsigned)b);});
   vector<Term> t;
   for(int m:bysize)if(none_of(t.begin(),t.end(),[&](const Term&a){return (m&a.m)==m;}))t.push_back({m,volume[m]});
   sort(t.begin(),t.end(),[](const Term&a,const Term&b){return a.v<b.v;});
   int total=0;for(int i=0;i<min(8,(int)t.size());i++)total+=t[i].v;
   if(t.size()>=8&&total<=64){fronts++;if(receivers(t,0,8,64)){printf("H");for(int m:helpers)printf(" %d",m);printf(" R");for(int m:chosen)printf(" %d",m);puts("");return true;}}
  }
  if(helpers.size()==4)return false;
  set<array<int,6>> seen;
  for(int m:joins){
   if(key[m]<=last||has(m))continue;
   if((stage[m]>1&&!has(w))||(stage[m]>2&&!has(q)))continue;
   if(!seen.insert(stamp(m)).second)continue;
   bank.push_back(m);helpers.push_back(m);if(run(key[m]))return true;helpers.pop_back();bank.pop_back();
  }
  return false;
 }
};
int main(int argc,char**argv){
 int w=atoi(argv[1]),q=atoi(argv[2]);Search S(w,q);
 assert((q&~255)==0&&(w&768)==0&&q&&w);
 bool valid=!S.hit(w,w)&&!S.hit(q,q);
 bool hit=valid&&S.run(-1);printf("W %d Q %d valid %d hit %d banks %lld fronts %lld\n",w,q,valid,hit,S.banks,S.fronts);
}
