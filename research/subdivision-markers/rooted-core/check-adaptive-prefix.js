function par(x){let p=0;while(x){p^=1;x&=x-1}return p}
function verify(m,h,Y){let S=[],P=[];for(let i=0;i<m;i++)(h>>i&1?S:P).push(i);
let R=[9,2,4,Y?1:9];P.forEach((_,i)=>R[3]|=1<<(4+i));S.forEach(()=>R.push(8));let raw=[];
for(let x=0;x<1<<R.length;x++)for(let y=0;y<1<<(4+P.length);y++){let cb=R.reduce((v,r,i)=>v|(par(r&y)<<i),0),dn=R.reduce((v,r,i)=>v^((x>>i&1)*r),0);if((cb&x)||(dn&y))continue;
let c=0,d=0;S.forEach((i,j)=>{c|=(cb>>(4+j)&1)<<i;d|=(x>>(4+j)&1)<<i});P.forEach((i,j)=>{c|=(y>>(4+j)&1)<<i;d|=(dn>>(4+j)&1)<<i});raw.push([c,d,(x&7)^(x>>3&1)^(par(y&7)<<3)^((y>>3&1)<<1)]);}
for(let p=0;p<3**m;p++){let u=p,a=0,b=0;for(let i=0;i<m;i++){if(u%3===1)a|=1<<i;if(u%3===2)b|=1<<i;u=Math.floor(u/3);}let img=0;for(let [c,d,z] of raw)if(!(c&a)&&!(d&b))img|=1<<z;if(img!==(Y&&!(h&a)&&!(~h&b)?65535:32767))throw Error('incorrect spectrum');}return 3**m}
for(let m=0;m<=4;m++){let count=0;for(let h=0;h<1<<m;h++)for(const Y of [false,true])count+=verify(m,h,Y);console.log(m,count);}

