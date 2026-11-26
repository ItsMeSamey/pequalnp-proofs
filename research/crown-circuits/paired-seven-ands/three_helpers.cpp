#define TRIPLE_NO_MAIN
#include "three_saturated.cpp"
struct Helpers:Triple{
 array<int,3> T;int mincost;long long libraries=0,volume=0,positives=0;
 ofstream witness;
 Helpers(array<int,3> t,int minc,const char*file):Triple(t),T(t),mincost(minc),witness(file){}
 bool has(int m)const{return find(bank.begin(),bank.end(),m)!=bank.end();}
 bool inside(int m)const{return any_of(T.begin(),T.end(),[&](int t){return (m&~t)==0;});}
 bool covers()const{return all_of(T.begin(),T.end(),[&](int t){return has(t);});}
 bool packTrace(const vector<pair<U,int>>&q,int i,int k,U used,vector<int>&out){
  if(!k)return true;for(;i+k<=(int)q.size();i++){
   if(pc(used)+k*pc(q[i].first)>128)return false;
   if(!(used&q[i].first)){out.push_back(q[i].second);if(packTrace(q,i+1,k-1,used|q[i].first,out))return true;out.pop_back();}
  }return false;
 }
 void check(const vector<int>&c){
  ++libraries;vector<U> replacements{z[T[0]]};for(int p:bank)if(!(p&3)){
   U v=z[T[0]]&z[p];if(v)replacements.push_back(v);}
  for(int k:c)if((k&3)==3&&wt(k&~(T[0]|3))>=2){
   if(any_of(replacements.begin(),replacements.end(),[&](U y){return (y&z[k])==y;}))continue;
   vector<pair<U,int>> events;for(int m:c)if(wt(m)>1&&!(z[m]&z[k]))events.push_back({z[m],m});
   sort(events.begin(),events.end(),[](auto x,auto y){return pc(x.first)!=pc(y.first)?pc(x.first)<pc(y.first):x<y;});
   vector<pair<U,int>> q;for(auto x:events){bool redundant=false;for(auto y:q)if((x.first&y.first)==y.first){redundant=true;break;}
    if(!redundant)q.push_back(x);}
   if(q.size()<11)continue;int v=pc(z[k]);for(int i=0;i<11;i++)v+=pc(q[i].first);if(v>128)continue;
   ++volume;vector<int> raw{k};if(packTrace(q,0,11,z[k],raw)){
    ++positives;witness<<"helpers";for(int m:chain)witness<<" "<<m;witness<<" raw";for(int m:raw)witness<<" "<<m;witness<<endl;return;}
  }
 }
 void visit(int phase,int last,int dirty){
  if(positives)return;int p=chain.size(),free=5-p;
  if(phase<2&&p>3)return;
  if(phase==0&&covers())visit(1,0,0);
  if(phase==1)visit(2,0,0);
  if(phase<2&&p>=3)return;
  auto c=choices();if(phase==2&&dirty>=2)check(c);if(!free)return;
  for(int m:c){int rank=wt(m)*16384+m;if(wt(m)<2||rank<=last||has(m))continue;
   if((m&3)?phase!=2:((phase==2)||(inside(m)!=(phase==0))))continue;
   if(phase==0&&p+1==3){
    bool ok=true;for(int t:T)if(!has(t)&&t!=m){ok=false;break;}if(!ok)continue;}
   if(phase==1&&p==mincost&&mincost==3)continue;
   bank.push_back(m);chain.push_back(m);visit(phase,rank,dirty+(phase==2));chain.pop_back();bank.pop_back();
  }
 }
};
int main(int argc,char**argv){if(argc<5)return 2;ifstream in(argv[1]);int cost=atoi(argv[2]),start=atoi(argv[3]),end=atoi(argv[4]);int id,c;
 array<int,3> t;while(in>>id>>t[0]>>t[1]>>t[2]>>c){
  if(c!=cost||id<start||id>=end)continue;
  Helpers h(t,c,"/dev/null");h.visit(0,0,0);if(h.positives){string name="three-positive-"+to_string(id);Helpers w(t,c,name.c_str());w.visit(0,0,0);}
  cout<<id<<" "<<t[0]<<" "<<t[1]<<" "<<t[2]<<" "<<h.libraries<<" "<<h.volume<<" "<<h.positives<<endl;
 }}
