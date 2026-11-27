#define main target_driver
#include "outer6d4.cpp"
#undef main
int main(){
 for(int x=0;x<1024;x++){graph[x]=false;for(int e:edgeMasks)if((x&e)==e)graph[x]=true;}
 trace=(M(1)<<17)-1;
 for(int j=0;j<17;j++){int omit=j==16?6:misGlobal[j];for(int v=0;v<10;v++)if(!(omit>>v&1))rawMask[v]|=M(1)<<j;}
 M z=M(1)<<16;
 if(!testZ(z))return 1;
 for(int j=0;j<16;j++)if(misGlobal[j]&2)z|=M(1)<<j;
 if(testZ(z))return 2;
 cout<<"positive H=0 and singleton-versus-edge obstruction verified"<<endl;
}
