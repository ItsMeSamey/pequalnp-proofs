#define main six_profile_main
#include "six13.cpp"
#undef main
int main(){
 Bank c;c.U.fill(F);c.leaf=F;c.L=64;
 for(int j=0;j<6;j++){c.B.push_back(halfs[j]);c.B.push_back(~halfs[j]);}
 c.lib=c.B;
 for(int i=0;i<13;i++){
  unsigned word=i|(popcount(unsigned(i&3))%2<<4)|(popcount(unsigned(i&12))%2<<5);M halves[2]{};
  for(int group=0;group<2;group++){M v=0;for(int p=0;p<3;p++){int j=group*3+p;v|=c.B[2*j+((word>>j)&1)];if(p&&find(c.lib.begin(),c.lib.end(),v)==c.lib.end()){c.lib.push_back(v);c.H.push_back(v);}}halves[group]=v;}
  if(~(halves[0]|halves[1])!=(M(1)<<word))return 2;
 }
 if(!c.chrono()||!c.pack())return 3;
 cout<<"Thirteen disjoint deficits found on six actual signed axes with "<<c.H.size()<<" furnished helper masks; relaxed-budget positive control."<<endl;
}
