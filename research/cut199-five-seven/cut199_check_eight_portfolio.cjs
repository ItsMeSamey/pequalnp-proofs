// Exact necessary normalized-decoder check on a five-variable upper-face bank.
// Input JSON holds five 32-bit port truth words in "ports" and one 32-bit "h".
// Local raw order is 4,5,8,9,10; h=0 also permits a physical copy of raw 3.
const fs=require('node:fs');
const {bankWords,normalized}=require('./cut199_portfolio_onefork.cjs');
const word=(n,i)=>Array.from({length:1<<n},(_,x)=>BigInt(x>>i&1)<<BigInt(x)).reduce((a,b)=>a|b,0n);
function lift(w){let out=0n;for(let i=0;i<32;i++)if((BigInt(w)>>BigInt(i))&1n)out|=3n<<BigInt(2*i);return out}
function check(ports,h){
 if(ports.length!==5)throw Error('need five unchanged right-port words');
 const z=word(6,0), l=Array.from({length:5},(_,i)=>word(5,i));
 const r=[z,z|lift(h),...ports.map(lift)],w=bankWords(l,r);
 return [3,4].map(a=>({anchor:[0,1,2,6,7][a],tree:normalized(w,a)}));
}
if(require.main===module){
 const q=JSON.parse(fs.readFileSync(process.argv[2],'utf8'));
 console.log(JSON.stringify(check(q.ports,q.h)));
}
module.exports={check};
