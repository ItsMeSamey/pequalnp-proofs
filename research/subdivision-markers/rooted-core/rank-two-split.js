// Enumerate split sectors in a four-score rank-three chart.
function span(xs) {
  const S = new Set([0]);
  for (const x of xs) for (const y of [...S]) S.add(x ^ y);
  return S;
}
function parity(x) { let b=0; while(x){b^=1; x&=x-1;} return b; }
function* syntax(){
const Q=[0,1,2,3], b=4,g=1,r=5;
for(let alpha=1;alpha<16;alpha++)for(let d=alpha+1;d<16;d++)for(let beta=1;beta<4;beta++){
 const q=alpha^d^beta,P=span([alpha,d,b]),W=span([alpha,d,beta]);
 if(W.size!==8||P.has(q)||P.has(r)||W.has(r)||q<4||[b,g,r].includes(q))continue;
 for(let p=4;p<16;p++)if(!P.has(p)&&!W.has(p)&&![b,r].includes(p))yield {alpha,d,beta,q,p};
}}
function test2(param){const {alpha,d,beta,q,p}=param,b=4,g=1,r=5,F=[p,q,r],B=F.map(x=>x^b),tags=[0,1].flatMap(s=>[0,1,2,3].filter(x=>!B.includes(x)).map(x=>[s,x]));let counts=Array(9).fill(0),example=null;
 const collides=(v,S)=>[...span(S)].some(x=>F.includes(v^x));
 for(let ti=1;ti<1<<tags.length;ti++){const T=tags.filter((_,i)=>ti>>i&1),n=T.length,full=(1<<n)-1,U=T.reduce((v,[s],i)=>v+(!s?1<<i:0),0),V=full^U,G=T.map(t=>t[1]);
 if(!U||!V||span([...G,beta]).size!==4||collides(alpha,[beta,...G.filter((_,i)=>V>>i&1)])||collides(d,[beta,...G.filter((_,i)=>U>>i&1)]))continue;
 const gains=[0],ms=[];for(let m=1;m<=full;m++){gains[m]=gains[m&(m-1)]^G[31-Math.clz32(m&-m)];if(parity(m&U)&&parity(m&V)&&gains[m]===g)ms.push(m)}if(!ms.length)continue;
 const pp=[];for(let z=0;z<=full;z++){if(collides(b,G.filter((_,i)=>z>>i&1)))continue;for(let l=z;;l=(l-1)&z){let o=(full^z)|l;
 const gc=(s,t)=>G.filter((_,i)=>(s&t)>>i&1);const pair=A=>A.map(x=>x^A[0]);
 if(!collides(b^d,[...gc(U,z),...pair(gc(V,o))])&&!collides(b^alpha,[...gc(V,z),...pair(gc(U,o))]))pp.push([z,o]);if(!l)break;}}
 for(let m of ms){let seen=0,K=new Set;for(let [z,o] of pp)for(let k=z;;k=(k-1)&z){if(!parity(k)&&!((m^k)&~o)){seen|=z;K.add(k)}if(!k)break}
 if(seen!==full)continue;let pairs=[];for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if(T[i][0]===T[j][0]){const diff=G[i]^G[j];if(F.includes(q^diff)||F.includes((T[i][0]?d:alpha)^beta^diff))pairs.push((1<<i)|(1<<j));}
 const L=k=>pairs.reduce((v,e,i)=>v+((k&e)===e?2**(n+1+i):0),k+full+1);
 if(span([...K].map(L)).has(L(m))){counts[n]++;if(!example)example=[T,m];}
 }}
 return [counts,example];}
console.log([...syntax()].length,[...syntax()].filter(p=>test2(p)[0].some(Boolean)).length);
