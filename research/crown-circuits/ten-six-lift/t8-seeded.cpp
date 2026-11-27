#define main generic_semantic_driver
#include "t8-dirty-exact.cpp"
#undef main
#include <iostream>
#include <sstream>
struct Fixed {
 Search s;vector<int>req,extra,chosen;vector<vector<int>> seen_seeds;
 Fixed(vector<int>t):s(t){
  for(int h:t)if(popcount((unsigned)h)>1)req.push_back(h);
  sort(req.begin(),req.end());req.erase(unique(req.begin(),req.end()),req.end());
  for(int h:req)for(int m=(h-1)&h;m;m=(m-1)&h)if(popcount((unsigned)m)>1&&!binary_search(req.begin(),req.end(),m))extra.push_back(m);
  sort(extra.begin(),extra.end());extra.erase(unique(extra.begin(),extra.end()),extra.end());
 }
 bool test(){
  vector<int> lib=req;lib.insert(lib.end(),chosen.begin(),chosen.end());
  sort(lib.begin(),lib.end());
  for(const auto&old:seen_seeds)if(includes(lib.begin(),lib.end(),old.begin(),old.end()))return false;
  auto identity=lib;
  sort(lib.begin(),lib.end(),[](int a,int b){return popcount((unsigned)a)<popcount((unsigned)b);});
  s.bank.resize(12);s.helpers.clear();
  for(int m:lib){
   if(s.hit(m,m))return false;
   bool ok=false;for(int a:s.bank)if(!(a&~m))for(int b:s.bank)if((a|b)==m){ok=true;break;}
   if(!ok)return false;
   s.bank.push_back(m);s.helpers.push_back(m);
  }
  seen_seeds.push_back(identity);return s.run(-1);
 }
 bool run(int lo,int n){if(!n)return test();for(int i=lo;i+n<=(int)extra.size();i++){
  chosen.push_back(extra[i]);if(run(i+1,n-1))return true;chosen.pop_back();}return false;}
};
int main(int argc,char**argv){
 int d=atoi(argv[1]);string l;
 while(getline(cin,l)){
  istringstream in(l);vector<int>t(d);for(int&i:t)in>>i;
  int cost=-1;in>>cost;assert(cost>=0&&cost<=4);Fixed f(t);
  bool ok=false;for(int k=cost;k<=4&&!ok;k++)ok=f.run(0,k-(int)f.req.size());
  for(int i:t)printf("%d ",i);printf("valid 1 hit %d banks %lld fronts %lld\n",ok,f.s.banks,f.s.fronts);fflush(stdout);
  if(ok)return 8;
 }
 return 0;
}
