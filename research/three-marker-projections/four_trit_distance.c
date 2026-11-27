#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static unsigned char p[12],taken[12],rot[81][12];
static uint16_t pairbit[81][6];
static uint64_t totals[10],wirings;
static int max_count, split;
static void evaluate(void){
 uint16_t seen[12][6]={{0}};unsigned char count[12]={0};unsigned live=4094;
 for(int t=0;t<81&&live;t++){
  int j=0;
  do{
   if(live>>j&1){
    int k=0;for(;k<6;k++)if(seen[j][k]&pairbit[t][k])break;
    if(k<6)live^=1<<j;
    else{count[j]++;for(int z=0;z<6;z++)seen[j][z]|=pairbit[t][z];}
   }
   j=p[rot[t][j]];
  }while(j);
 }
 for(int j=1;j<12;j++)if(live>>j&1){
  totals[count[j]]++;
  if(count[j]>max_count){max_count=count[j];printf("new max %d root %d wiring",max_count,j);
   for(int i=0;i<12;i++)printf(" %d",p[i]);puts("");}
 }wirings++;
}
static void gen(int at,int known){
 if(at==12){evaluate();return;}if(at==known)return;
 for(int j=0;j<known;j++)if(!taken[j]&&(at!=0||split<0||j==split)){
 p[at]=j;taken[j]=1;gen(at+1,known);taken[j]=0;}
 if(known<12&&(at!=0||split<0||known==split)){
 p[at]=known;taken[known]=1;gen(at+1,known+3);taken[known]=0;}
}
static uint32_t seed=872293;
static uint32_t rnd(void){seed^=seed<<13;seed^=seed>>17;seed^=seed<<5;return seed;}
int main(int argc,char**argv){
 if(argc<2)return 1;split=atoi(argv[1]);
 for(int t=0;t<81;t++){
 int x=t,v[4],z=0;
 for(int i=0;i<4;i++){v[i]=x%3;x/=3;for(int j=0;j<3;j++)rot[t][3*i+j]=3*i+(j+v[i])%3;}
 for(int i=0;i<4;i++)for(int j=i+1;j<4;j++)pairbit[t][z++]=1u<<(v[i]+3*v[j]);}
 if(split<=3)gen(0,3);else for(int k=0;k<split;k++){
 for(int i=0;i<12;i++)p[i]=i;for(int i=11;i;i--){int j=rnd()%(i+1),q=p[j];p[j]=p[i];p[i]=q;}evaluate();}
 printf("slice %d wirings %llu counts",split,(unsigned long long)wirings);
 for(int i=0;i<10;i++)printf(" %llu",(unsigned long long)totals[i]);puts("");
}
