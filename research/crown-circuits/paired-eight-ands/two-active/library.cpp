#include "anchors_core.hpp"
// Tested against the complete direction cube; this routine does not require an
// axis ordering other than the declared chronology of the two dirty gates.
struct Library{
 Template q;int K;
 vector<int> bank,helpers;
 vector<uint8_t> useful,valid;
 vector<int> frequency,vol;
 array<int,257> hist{};
 long long visited=0,screened=0,hits=0;
 Library(Key t,int k):q(t),K(k),useful(maskCount),valid(maskCount),frequency(maskCount),vol(maskCount){
  for(int a=0;a<16;a++)bank.push_back(1<<a);
  auto mark=[&](int m){for(int x=m;x;x=(x-1)&m)useful[x]=true;};
  mark(t.first);mark(t.second);mark(k);
  for(int m=1;m<maskCount;m++){int n=popcount((unsigned)m);
   if(n<2||n>7||!(m&~t.first)||!(m&~t.second))continue;
   auto d=q.deficit[m];int v=d.size();if(!v||d.overlaps(q.deficit[k])||!admissible(t,k,m))continue;
   valid[m]=1;vol[m]=v;mark(m);}
  for(int a:bank)for(int b:bank)if(a<b)bump(a|b,1);
 }
 void bump(int m,int delta){if(valid[m]){int old=frequency[m];frequency[m]+=delta;if(!old)hist[vol[m]]++;else if(!frequency[m])hist[vol[m]]--;}}
 bool present(int m){return find(bank.begin(),bank.end(),m)!=bank.end();}
 int bound(int target){
  vector<int> components;for(int m=target;m;m&=m-1)components.push_back(m&-m);
  for(int x:helpers)if(!(x&~target)){for(int j=0;j<(int)components.size();){if(x&components[j]){x|=components[j];components[j]=components.back();components.pop_back();}else j++;}components.push_back(x);}
  return components.size()-1;
 }
 bool possibleVolume(){int n=11,room=256-q.deficit[K].size();for(int i=1;i<=256&&n;i++){int t=min(n,hist[i]);room-=t*i;n-=t;}return !n&&room>=0;}
 vector<int> next(){vector<int> out;for(int a:bank)for(int b:bank)if(a<b)out.push_back(a|b);sort(out.begin(),out.end());out.erase(unique(out.begin(),out.end()),out.end());return out;}
 bool accept(const vector<int>&out){
  vector<Candidate> c;uint32_t cover=q.parity[K];for(int m:out)if(valid[m]){c.push_back({m,q.deficit[m],vol[m],q.parity[m]});cover|=q.parity[m];}
  if(cover!=allPairs)return false;
  sort(c.begin(),c.end(),[](auto&a,auto&b){return a.volume!=b.volume?a.volume<b.volume:a.m<b.m;});
  vector<Candidate> small;for(auto&x:c){bool drop=false;for(auto&z:small)if(z.d.subset(x.d)&&!(x.cover&~z.cover)){drop=true;break;}if(!drop)small.push_back(x);}
  return pack(small,0,11,q.deficit[K],allPairs&~q.parity[K]);
 }
 array<unsigned,8> stamp(int m){
  array<unsigned,8> result{};vector<int> rows{q.t.first,q.t.second,K};rows.insert(rows.end(),helpers.begin(),helpers.end());rows.push_back(m);
  for(int j=0;j<8;j++){unsigned a=0,b=0;for(int r:rows){a=(a<<1)|((r>>(2*j))&1);b=(b<<1)|((r>>(2*j+1))&1);}result[j]=(min(a,b)<<10)|max(a,b);}
  sort(result.begin()+2,result.end());return result;
 }
 void dfs(bool exterior,int last){
  ++visited;if(hits)return;int free=5-(int)helpers.size();int t=q.t.first,u=q.t.second;
  if(!exterior&&(bound(K)>free+1||bound(t)>free||bound(u)>free||bound(K|t)-((K&t)?0:1)>free+1))return;
  bool volume=exterior&&possibleVolume();if(exterior&&!free&&!volume)return;
  auto out=next();if(volume){++screened;if(accept(out)){++hits;return;}}
  if(!exterior&&present(t)&&present(u)&&binary_search(out.begin(),out.end(),K))dfs(true,0);
  if(!free)return;
  set<array<unsigned,8>> seen;
  for(int m:out){int rank=popcount((unsigned)m)*maskCount+m;
   bool inside=!(m&~t)||!(m&~u)||!(m&~K);
   if(inside==exterior||rank<=last||m==K||!useful[m]||present(m))continue;
   if(!exterior&&free==1&&((!present(t)&&m!=t)||(!present(u)&&m!=u)))continue;
   if(!seen.insert(stamp(m)).second)continue;
   for(int v:bank)bump(m|v,1);bank.push_back(m);helpers.push_back(m);
   dfs(exterior,rank);helpers.pop_back();bank.pop_back();for(int v:bank)bump(m|v,-1);
  }
 }
};
int main(int argc,char**argv){
 auto ts=makeTemplates();int lo=argc>1?atoi(argv[1]):0,hi=argc>2?atoi(argv[2]):ts.size();
 string tag;while(cin>>tag){if(tag!="root"){string s;getline(cin,s);continue;}
  int i,k,c;cin>>i>>k>>c;if(i<lo||i>=hi)continue;Library l(ts[i],k);l.dfs(false,0);
  cout<<i<<" "<<k<<" "<<l.visited<<" "<<l.screened<<" "<<l.hits<<endl;
 }
}
