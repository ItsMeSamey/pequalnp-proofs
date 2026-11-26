// Enumerate split sectors in a four-score rank-three chart.
function span(xs) {
  const S = new Set([0]);
  for (const x of xs) for (const y of [...S]) S.add(x ^ y);
  return S;
}
function parity(x) { let b=0; while(x){b^=1; x&=x-1;} return b; }
function exhaust(h,n) {
  const forbidden=[1,2,h], tags=[];
  for(const s of [0,1]) for(let x=0;x<8;x++) if(!forbidden.includes(x)) tags.push([s,x]);
  const counts=[0,0,0], full=(1<<n)-1;
  for(let ti=1;ti<1<<tags.length;ti++){
    const T=tags.filter((_,i)=>ti>>i&1);
    if(T.length!==n)continue;
    const U=T.reduce((m,[s,x],i)=>m+(s?0:1<<i),0), V=full^U;
    const G=T.map(t=>t[1]), gain=[0], masks=[], zeroMasks=[];
    for(let k=0;k<=full;k++) {
      if(k) gain[k]=gain[k&(k-1)]^G[31-Math.clz32(k&-k)];
      if(parity(k&U)&&parity(k&V)&&gain[k]===2)masks.push(k);
      if(![...span(G.filter((_,i)=>k>>i&1))].some(x=>forbidden.includes(x)))zeroMasks.push(k);
    }
    if(!masks.length)continue;
    for(let d=1;d<8;d++)for(let beta=1;beta<8;beta++){
      const a=1^d^beta;
      if(d===beta || span([...G,beta]).size!==8)continue;
      if([...span([beta,...G.filter((_,i)=>V>>i&1)])].some(x=>forbidden.includes(a^x)))continue;
      counts[0]+=masks.length;
      const profiles=[];
      for(const z of zeroMasks) for(let both=z;;both=(both-1)&z){
        const o=(full^z)|both,ones=G.filter((_,i)=>(o&V)>>i&1),vs=G.filter((_,i)=>(z&U)>>i&1);
        if(![...span([...vs,...ones.map(x=>x^ones[0])])].some(x=>forbidden.includes(d^x))) profiles.push([z,o]);
        if(!both)break;
      }
      for(const m of masks) {
        let seen=0; const bset=new Set();
        for(const [z,o] of profiles) for(let k=z;;k=(k-1)&z){
          if(!parity(k)&&!((k^m)&~o)){seen|=z;bset.add(k);}
          if(!k)break;
        }
        if(seen!==full || !span([...bset].map(k=>k+full+1)).has(m+full+1))continue;
        counts[1]++;
        const pairs=[];
        for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
          if(T[i][0]!==T[j][0])continue;
          const v=G[i]^G[j];
          if([0,3,1^h].includes(v)||(!T[i][0]&&v===d))pairs.push((1<<i)|(1<<j));
        }
        const lift=k=>pairs.reduce((v,p,i)=>v+((k&p)===p?2**(n+1+i):0),k+full+1);
        if(span([...bset].map(lift)).has(lift(m)))counts[2]++;
      }
    }
  }
  return counts;
}
if(typeof module!=='undefined'&&require.main===module) for(const n of [1,2,3,4,5,6,7,8,9,10]) for(const h of [4,3]) console.log(n,h,exhaust(h,n));
