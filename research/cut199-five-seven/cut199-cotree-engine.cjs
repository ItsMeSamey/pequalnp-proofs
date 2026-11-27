// Shared search routines from cut199-exact-m12-cotree.cjs.
const sideMask=k=>k===0||(k&(k-1))===0;
function exactTree(P,N,n,left=6,limit=250000){
 const full=(1<<n)-1,lc=(1<<left)-1,rc=full^lc,memo=new Map(),bit=i=>1<<i;
 let visits=0;
 const childrenAllowed=m=>sideMask(m)||((m&lc)!==0&&(m&rc)!==0);
 function trivial(m,op){const ids=[];for(let x=m;x;x&=x-1)ids.push(31-Math.clz32(x&-x));
   if(ids.length>1){const j=ids.findIndex(i=>(i<left)!==(ids[0]<left));[ids[1],ids[j]]=[ids[j],ids[1]]}
   return ids.reduce((a,b)=>[op,a,b]);}
 function rec(m,pp,nn){
  if(++visits>limit)throw Error('limit');
  const key=[m,pp,nn].join();if(memo.has(key))return memo.get(key);
  if(!childrenAllowed(m))return null;
  let pm=[],nm=[];for(let x=pp;x;x&=x-1)pm.push(31-Math.clz32(x&-x));for(let x=nn;x;x&=x-1)nm.push(31-Math.clz32(x&-x));
  if(!pp)return nm.every(i=>(m&~N[i]))?trivial(m,1):null;
  if(!nn)return pm.every(i=>(m&P[i]))?trivial(m,0):null;
  let diff=pm.map(i=>nm.map(j=>m&P[i]&~N[j]));if(diff.some(row=>row.includes(0)))return null;
  if(sideMask(m))return 31-Math.clz32(m);
  for(let op of [0,1]){
   let rows=op?nm:pm, ds=op?nm.map((_,j)=>diff.map(row=>row[j])):diff;
   let comps=[];for(let x=m;x;x&=x-1)comps.push(x&-x);
   for(const row of ds){let req=0;for(const d of row)if(sideMask(d))req|=d;
    if(!req)continue;let merged=0;comps=comps.filter(c=>{if(c&req){merged|=c;return false}return true});comps.push(merged)}
   if(comps.length<2)continue;
   let splits=[];for(let k=1;k<(1<<comps.length)-1;k+=2){let a=0;for(let j=0;j<comps.length;j++)if(k>>j&1)a|=comps[j];let b=m^a;if(!childrenAllowed(a)||!childrenAllowed(b))continue;
    let fa=0,fb=0,amb=0,count=0,ok=true;
    for(let j=0;j<rows.length;j++){let noA=false,noB=false;for(const d of ds[j]){noA||=!(d&a);noB||=!(d&b);if(noA&&noB)break}
     if(noA&&noB){ok=false;break}if(noA)fb|=bit(rows[j]);else if(noB)fa|=bit(rows[j]);else{amb|=bit(rows[j]);count++}}
    if(ok)splits.push([count,a,b,fa,fb,amb]);}
   splits.sort((x,y)=>x[0]-y[0]);for(const [,a,b,fa,fb,amb] of splits){for(let x=amb;;x=(x-1)&amb){let aRows=fa|x,bRows=fb|(amb^x);
     let A=op?rec(a,pp,aRows):rec(a,aRows,nn);
     if(A!==null){let B=op?rec(b,pp,bRows):rec(b,bRows,nn);if(B!==null){let t=[op,A,B];memo.set(key,t);return t}}
     if(!x)break;}}
  }memo.set(key,null);return null;}
 try{return {tree:rec(full,(1<<P.length)-1,(1<<N.length)-1),visits,complete:true}}catch(e){if(e.message!=='limit')throw e;return {tree:null,visits,complete:false}}
}
function wedge(P,N,n){const full=(1<<n)-1,AND=Array(n).fill(0),OR=Array(n).fill(0),nr=Array(N.length).fill(0);for(let p of P){let pr=0;for(let j=0;j<N.length;j++){let d=p&~N[j];if(!d)return false;if(!(d&(d-1))){pr|=d;nr[j]|=d}}
 for(let v=pr;v;v&=v-1)AND[31-Math.clz32(v&-v)]|=pr}
 for(let v of nr)for(let u=v;u;u&=u-1)OR[31-Math.clz32(u&-u)]|=v;
 function allowed(m){if(!(m&(m-1)))return true;for(const g of [AND,OR]){let old=m,groups=[];while(old){let reach=old&-old,front=reach;while(front){let x=front&-front;front^=x;let add=old&g[31-Math.clz32(x)]&~reach;reach|=add;front|=add}groups.push(reach);old^=reach}if(groups.length>1&&groups.every(allowed))return true}return false}return allowed(full)}
module.exports={exactTree,wedge};
