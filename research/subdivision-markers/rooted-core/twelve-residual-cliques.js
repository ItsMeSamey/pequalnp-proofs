function par(x){let p=0;while(x){x&=x-1;p^=1}return p}
function P(N){let R=N.map(x=>x|32).concat(31),T=new Set;for(let x=0;x<64;x++)for(let y=0;y<64;y++){if((y&R.reduce((v,r,i)=>v^((x>>i&1)*r),0))||R.some((r,i)=>(x>>i&1)&&par(y&r)))continue;let z=((x<<6)|y)^2080,k=Math.min(z,z^4095);if(k)T.add(k)}return T;}

const cases=[[[3,5,10,20,24],[0,2016,1939,1869,1742,1494,1081,985,566]],[[3,5,10,23,27],[0,2016,1939,1885,1758,318,189,115,550]]];for(const [N,S] of cases){let D=P(N);for(let i=0;i<9;i++)for(let j=0;j<i;j++)if(!D.has(S[i]^S[j]))throw Error("bad difference");console.log(N,D.size,36);}
