#define THREE_HARD_NO_MAIN
#include "three_hard.cpp"
int main(int argc,char**argv){
 if(argc<3)return 2;ifstream in(argv[1]);int id,mc;array<int,3> t;Costs costs;ofstream roots(argv[2]);
 while(in>>id>>t[0]>>t[1]>>t[2]>>mc){
  if(mc>2)continue;Feasible f(t,costs);array<int,3> ord={0,1,2};sort(ord.begin(),ord.end(),[&](int a,int b){return pair(f.hot[a].size(),a)<pair(f.hot[b].size(),b);});
  set<uint64_t> seen;int n=0;
  for(int a:f.hot[ord[0]]){auto key=signature(t,a);if(!seen.insert(key).second)continue;bool ok=false;
   for(int b:f.hot[ord[1]])if(f.cleanPair(a,b)&&f.cut({a,b})){
    for(int c:f.hot[ord[2]])if(f.cleanPair(a,c)&&f.cleanPair(b,c)&&f.cut({a,b,c})){ok=true;break;}if(ok)break;}
   if(ok){++n;roots<<id<<" "<<a<<'\n';}}
  cout<<id<<" "<<mc<<" "<<ord[0]<<" "<<n<<endl;
 }}
