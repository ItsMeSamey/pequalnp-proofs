#define main original_scan
#include "one_dirty.cpp"
#undef main
int main(){
 int axes,helpers; cin>>axes>>helpers;
 for(int j=0,x;j<helpers;j++)cin>>x;
 Search search(0,0,"/dev/null",false);
 vector<U> deficits;
 for(int j=0,m;j<11;j++){
  cin>>m;U d=0;
  for(int s=0;s<128;s++){
   int pins=0;
   for(int a=0;a<axes;a++)pins|=1<<(2*a+((s>>a)&1));
   if(!(m&pins))d|=U(1)<<s;
  }
  if(!d)return 1;
  deficits.push_back(d);
 }
 const U anchor=deficits.back(); deficits.pop_back();
 sort(deficits.begin(),deficits.end(),[](U a,U b){return pc(a)<pc(b);});
 if(!search.pack(deficits,0,10,anchor))return 2;
 deficits.pop_back();
 if(search.pack(deficits,0,10,anchor))return 3;
 cout<<"Verified fixed-anchor acceptance of eleven receivers and rejection after one deletion.\n";
}
