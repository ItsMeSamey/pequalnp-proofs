#include <initializer_list>
#include <cstdio>
int main(){
  // Three guarded vertices on each shore, plus three left outputs. Bit 0 is each pin.
  unsigned cases=0,pairs=0;
  for(unsigned g=0;g<(1u<<18);g++){
    bool zero=false, singleton=false, possible[8]={};
    for(unsigned x=1;x<64;x+=2)for(unsigned y=1;y<8;y+=2){
      unsigned odd=0, col=0;
      for(int i=0;i<6;i++) if(x>>i&1){
        unsigned row=(g>>(3*i))&7;
        if(__builtin_parity(row&y))odd|=1u<<i;
        col^=row;
      }
      if((col&y)||(odd&7))continue;
      unsigned t=x>>3;
      if(!t)zero=true;
      if(__builtin_popcount(t)==1&&!odd)singleton=true;
      if((odd>>3)==t)possible[t]=true;
    }
    if(zero&&!singleton){
      cases++;
      for(unsigned t: {3u,5u,6u}){if(!possible[t])return 1;pairs++;}
    }
  }
  std::printf("%u qualifying graphs; %u pair-current traces verified\n",cases,pairs);
}
