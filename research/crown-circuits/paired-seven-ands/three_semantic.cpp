#define TRIPLE_NO_MAIN
#include "three_saturated.cpp"
struct Helpers:Triple{
 array<int,3> T;int mincost;array<unsigned char,16384> fires{};vector<array<unsigned short,16384>> group;
 void symmetry(){
  array<int,4> axes={3,4,5,6};
  do{for(int f=0;f<128;f++){
   int unit[14];for(int j=0;j<7;j++)for(int b=0;b<2;b++)unit[2*j+b]=1<<(2*(j<3?j:axes[j-3])+(b^(f>>j&1)));
   auto tr=[&](int m){int a=0;while(m){a|=unit[countr_zero((unsigned)m)];m&=m-1;}return a;};
   if(any_of(T.begin(),T.end(),[&](int t){return tr(t)!=t;}))continue;
   group.emplace_back();auto&g=group.back();g[0]=0;for(int m=1;m<16384;m++)g[m]=g[m&(m-1)]|unit[countr_zero((unsigned)m)];
  }}while(next_permutation(axes.begin(),axes.end()));
 }
long long libraries=0,volume=0,positives=0;
 ofstream witness;
 Helpers(array<int,3> t,int minc,const char*file):Triple(t),T(t),mincost(minc),witness(file){
  for(int m=1;m<16384;m++){int x=m;for(int j=0;j<3;j++)if((x>>(2*j)&3)==3){fires[m]|=1<<j;x|=T[j];}}
  symmetry();
 }
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
  ++libraries;array<vector<int>,3> hard;
  for(int j=0;j<3;j++){
   vector<U> repl{z[T[j]]};for(int p:bank){int m=T[j]|p;
    if(z[m]&&!(fires[m]>>j&1))repl.push_back(z[m]);}
   for(int m:c)if(wt(m)>1&&(fires[m]>>j&1)&&none_of(repl.begin(),repl.end(),[&](U q){return (q&z[m])==q;}))hard[j].push_back(m);
   if(hard[j].empty())return;
  }
  for(int k:hard[0]){
   bool compatible=false;
   for(int r:hard[1])if(r==k||!(z[r]&z[k])){
    for(int q:hard[2])if((q==r||!(z[r]&z[q]))&&(q==k||!(z[k]&z[q]))){compatible=true;break;}
    if(compatible)break;
   }if(!compatible)continue;
   vector<pair<U,int>> events;for(int m:c)if(wt(m)>1&&!(z[m]&z[k]))events.push_back({z[m],m});
   sort(events.begin(),events.end(),[](auto x,auto y){return pc(x.first)!=pc(y.first)?pc(x.first)<pc(y.first):x<y;});
   vector<pair<U,int>> q;for(auto x:events){bool redundant=false;for(auto y:q)if((x.first&y.first)==y.first){redundant=true;break;}
    if(!redundant)q.push_back(x);}
   if(q.size()<11)continue;int v=pc(z[k]);for(int i=0;i<11;i++)v+=pc(q[i].first);if(v>128)continue;
   ++volume;vector<int> raw{k};if(packTrace(q,0,11,z[k],raw)){
    ++positives;witness<<"helpers";for(int m:chain)witness<<" "<<m;witness<<" raw";for(int m:raw)witness<<" "<<m;witness<<endl;return;}
  }
 }
 void visit(int phase,int last,int dirty,const vector<int>&stab){
  if(positives)return;int p=chain.size(),free=5-p;
  if(phase<2&&p>3)return;
  if(phase==0&&covers())visit(1,0,0,stab);
  if(phase==1)visit(2,0,0,stab);
  if(phase<2&&p>=3)return;
  auto c=choices();if(phase==2&&dirty>=2)check(c);if(!free)return;
  for(int m:c){int rank=wt(m)*16384+m;if(wt(m)<2||rank<=last||has(m))continue;
   if((m&3)?phase!=2:((phase==2)||(inside(m)!=(phase==0))))continue;
   if(phase==0&&p+1==3){
    bool ok=true;for(int t:T)if(!has(t)&&t!=m){ok=false;break;}if(!ok)continue;}
   if(phase==1&&p==mincost&&mincost==3)continue;
   bool keep=true;vector<int> next;for(int g:stab){int image=group[g][m];if(image<m){keep=false;break;}if(image==m)next.push_back(g);}
   if(!keep)continue;
   bank.push_back(m);chain.push_back(m);visit(phase,rank,dirty+(phase==2),next);chain.pop_back();bank.pop_back();
  }
 }
};
int main(int argc,char**argv){if(argc<5)return 2;ifstream in(argv[1]);int cost=atoi(argv[2]),start=atoi(argv[3]),end=atoi(argv[4]);int id,c;
 array<int,3> t;while(in>>id>>t[0]>>t[1]>>t[2]>>c){
  if(c!=cost||id<start||id>=end)continue;
  Helpers h(t,c,"/dev/null");vector<int> ids(h.group.size());iota(ids.begin(),ids.end(),0);h.visit(0,0,0,ids);if(h.positives){string name="three-positive-"+to_string(id);Helpers w(t,c,name.c_str());w.visit(0,0,0,ids);}
  cout<<id<<" "<<t[0]<<" "<<t[1]<<" "<<t[2]<<" "<<h.libraries<<" "<<h.volume<<" "<<h.positives<<endl;
 }}
