#include <array>
#include <cstdio>
std::array<int,11> p{};
long long count=0;
bool check(){
 int used[2]={};
 for(int x=0;x<2;x++)for(int a=0;a<4;a++){
  int img[3];
  for(int i=0;i<3;i++){
   int h=8+i;
   do{int s=h;if(h<2)s=h^x;else if(h<5)s=2+(h-2+(a&1))%3;else if(h<8)s=5+(h-5+(a>>1))%3;h=p[s];}while(h<8);
   img[i]=h-8;
  }
  if(img[0]==0&&img[1]==1&&img[2]==2){used[x]|=1;continue;}
  if(!x&&img[0]==1&&img[1]==0&&img[2]==2){used[x]|=2;continue;}
  if(x&&img[0]==0&&img[1]==2&&img[2]==1){used[x]|=2;continue;}
  return false;
 }
 return used[0]==3&&used[1]==3;
}
bool search(int k){if(k==8){count++;return check();}p[k]=k;if(search(k+1))return true;for(int i=0;i<11;i++)if(i<k||i>=8){int q=p[i];p[i]=k;p[k]=q;if(search(k+1))return true;p[i]=q;}return false;}
int main(){p[8]=9;p[9]=8;p[10]=10;bool ok=search(0);printf("%lld %s\n",count,ok?"FOUND":"NO");if(ok){for(int h:p)printf("%d ",h);puts("");}}
