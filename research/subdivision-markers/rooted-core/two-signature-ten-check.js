function par(x){let p=0;while(x){p^=1;x&=x-1}return p}
const E=[0,3,5,6];let good=0,n=0,both=0,maps=0;
for(const a of E)for(const b of E)for(const c of E){
 let d=a^b^c;if(new Set([a,b,c,d].filter(Boolean)).size<2)continue;n++;
 let R=[a|8,b|16,c|16,d|16,7],raw=[],mult=false;
 for(let x=0;x<32;x++)for(let y=0;y<32;y++){
 let cr=R.reduce((m,r,i)=>m|(par(r&y)<<i),0),dc=R.reduce((m,r,i)=>m^((x>>i&1)*r),0);
 if((x&cr)||(y&dc))continue;
 let fixed=(y>>3)^((x&16)>>2),k=(y&1)|(par(y&6)<<1)|((x&1)<<2)|(par(x&14)<<3);
 if((fixed===7&&k===0&&(x!==16||y!==24))||(fixed===0&&k===13&&(x!==15||y!==7)))mult=true;
 raw.push([fixed,k]);
 }if(mult)continue;good++;
 for(let u=0;u<16;u++)for(let v=0;v<16;v++)if(u!==v)for(let w=0;w<16;w++)for(let t=0;t<16;t++)if(w!==t){
 let r=u^w^t;if(r===7)continue;maps++;const g=[0],G=[u,v,w,t];for(let i=1;i<16;i++)g.push(g[i&(i-1)]^G[31-Math.clz32(i&-i)]);
 let nq=0,nr=0;for(let [f,k] of raw){let score=f^g[k];if(score===7)nq++;if(score===r)nr++;if(nq>1||nr>1)break;}if(nq===1&&nr===1)both++;
 }}
console.log(n,good,maps,both);
