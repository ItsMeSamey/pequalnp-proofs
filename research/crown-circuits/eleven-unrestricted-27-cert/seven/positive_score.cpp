#define main model_main
#include "full11.cpp"
#undef main
int main(){
 int na,n;cin>>na>>n;Full s(Row{});vector<unsigned> h(n),raw(11);
 for(auto&m:h)cin>>m;for(auto&m:raw)cin>>m;
 for(auto m:h){
  bool made=false;for(auto a:s.bank)for(auto b:s.bank)if(a!=b&&(a|b)==m)made=true;
  if(!made)return 2;for(auto a:s.bank)s.bump(a,m,1);s.bank.push_back(m);
 }
 for(auto m:raw)if(!s.freq[m])return 3;
 s.test();if(!s.solutions)return 4;
 vector<Candidate> options;for(int j=1;j<11;j++)options.push_back({int(raw[j]),invert(s.vals[raw[j]]),invert(s.vals[raw[j]]).size(),0});
 sort(options.begin(),options.end(),[](auto a,auto b){return a.volume<b.volume;});
 auto k=invert(s.vals[raw[0]]);
 if(!pack(options,0,10,k,0))return 5;
 options.pop_back();if(pack(options,0,10,k,0))return 6;
 cout<<"11-input threshold: 27 gates, "<<na<<" ANDs, "<<n<<" paid helper unions; 2048 inputs verified; eleven receivers accepted, ten rejected"<<endl;
}
