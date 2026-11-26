#define main main_solver
#include "exact_five_helpers.cpp"
#undef main
int main(){Bank b;b.U.fill(F);for(int i=0;i<5;i++){b.B.push_back(halfs[i]);b.B.push_back(~halfs[i]);}b.lib=b.B;b.leaf=F;b.L=32;M h;while(scanf("%u",&h)==1){b.H.push_back(h);b.lib.push_back(h);}printf("accepted %d helpers %zu\n",b.pack(),b.H.size());}
