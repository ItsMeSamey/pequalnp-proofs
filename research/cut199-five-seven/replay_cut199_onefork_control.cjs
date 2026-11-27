const {bankWords,test}=require('./cut199_portfolio_onefork.cjs');
const model=require('./cut199-two-raw-fork6-22.json');
const R=[3,4,5,8,9,10], L=[0,1,2,6,7];
const word=(n,j)=>Array.from({length:1<<n},(_,x)=>BigInt(x>>j&1)<<BigInt(x)).reduce((a,b)=>a|b,0n);
const truth=new Map(R.map((i,k)=>[i,word(6,k)]));
for(const [i,[op,a,b]] of model.gates.entries())if(truth.has(a)&&truth.has(b))truth.set(11+i,op?truth.get(a)&truth.get(b):truth.get(a)|truth.get(b));
const l=L.map((_,i)=>word(5,i)),r=model.right.map(i=>truth.get(i));
const found=test(bankWords(l,r),1<<3);
if(!found)throw Error('known fork not found');
function ev(t,v){if(Number.isInteger(t))return v[t];return t[0]?(ev(t[1],v)&ev(t[2],v)):(ev(t[1],v)|ev(t[2],v))}
for(let x=0;x<2048;x++){
 const p=R.reduce((m,k,j)=>m|((x>>k&1)<<j),0);
 let v=[...L.map(k=>x>>k&1),...r.map(w=>Number(w>>BigInt(p)&1n))];
 v.push(ev(found.donor,v));
 if(ev(found.exterior,v)!==Number(model.edges.some(([a,b])=>(x>>a)&(x>>b)&1)))throw Error('bad witness');
}
console.log(JSON.stringify(found));
