inline bool four_ready(const int *f,int n,const int*t){
 int count=0;
 for(int j=0;j<7;j++){int m=8191;for(int i=0;i<n;i++)if(!(t[j]&~f[i]))m&=f[i];count+=m==t[j];}
 return count>=4;
}
