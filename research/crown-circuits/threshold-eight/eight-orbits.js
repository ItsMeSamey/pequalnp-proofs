const by=Array.from({length:7},()=>[0,0,0,0]), leaves=[0,0,0,0];const full=(d)=>(1n<<BigInt(2**d))-1n;const perm=Array.from({length:6},(_,i)=>Array.from({length:2**i},(_,s)=>Array.from({length:2**i},(_,x)=>1n<<BigInt(x^s))));
function translate(m,d,s){if(!s)return m;let r=0n;for(let i=0;i<2**d;i++)if((m>>BigInt(i))&1n)r|=perm[d][s][i];return r}const index=new Map(), records=[];
function advance(d,branches,paid,group,blocks,sequence=[]){by[d][paid.length]++;if(d===6){if(blocks.length>=8){leaves[paid.length]++;index.set(sequence.join(','),records.length);records.push([sequence,paid.length])}return}let U=full(d),pool=new Set([0n]);for(let b of branches){for(let t of [...pool]) pool.add(t|b)}pool.add(U);const lift=m=>m|(m<<BigInt(2**d));let base=branches.map(lift),prev=paid.map(lift);for(let m of pool){if(!m)continue;let fresh=m!==U&&!branches.includes(m)&&!paid.includes(m);if(fresh&&paid.length===3)continue;let st=[],ok=true;for(let s of group){let mm=translate(m,d,s);if(mm<m){ok=false;break}if(mm===m)st.push(s)}if(!ok)continue;let lo=m,hi=m<<BigInt(2**d),nxt=[];for(let b of blocks){let inside=b&m,outside=b&(U^m);if(inside)nxt.push(inside,inside<<BigInt(2**d));if(outside)nxt.push(lift(outside))}advance(d+1,[...base,lo,hi],fresh?[...prev,lift(m)]:prev,[...st,...st.map(s=>s+2**d)],nxt,[...sequence,m])}}advance(0,[],[],[0],[1n]);const DS=records.map((_,i)=>i);const find=x=>DS[x]===x?x:(DS[x]=find(DS[x]));const xs=Array.from({length:6},(_,d)=>Array.from({length:d},(_,j)=>{let h=0n;for(let x=0;x<2**d;x++)if(x>>j&1)h|=1n<<BigInt(x);return h}));const memo=Array.from({length:6},()=>new Map);
function tr(m,d,s){let hits=memo[d].get(m);if(!hits){hits=[m];for(let j=0;j<d;j++){let shift=BigInt(1<<j),hi=xs[d][j];for(let k=0;k<1<<j;k++){let v=hits[k];hits.push(((v&hi)>>shift)|((v&~hi)<<shift))}}memo[d].set(m,hits)}return hits[s]}
function key(seq){let st=[0],ans=[];for(let d=0;d<6;d++){let vals=st.map(s=>tr(seq[d],d,s)),min=vals.reduce((a,b)=>a<b?a:b);ans.push(min);st=st.filter((s,k)=>vals[k]===min);st=st.concat(st.map(s=>s+2**d))}return ans.join(',')}let edges=0;for(let id=0;id<records.length;id++){let [seq,w]=records[id];for(let i=0;i<5;i++){let A=seq[i],B=seq[i+1],n=BigInt(1<<i);if((B>>n)!==(B&full(i)))continue;let out=seq.slice();out[i]=B&full(i);out[i+1]=A|(A<<n);for(let j=i+2;j<6;j++){let m=seq[j],a=xs[j][i],b=xs[j][i+1];out[j]=(m&~(a^b))|((m&a&~b)<<n)|((m&~a&b)>>n)}let target=index.get(key(out));if(target===undefined)throw Error('missing adjacent class');let x=find(id),y=find(target);if(x!==y){DS[x]=y;edges++}}}let total=[0,0,0,0];for(let id=0;id<DS.length;id++)if(find(id)===id)total[records[id][1]]++;if(process.argv[2]){const rows=[];for(let id=0;id<DS.length;id++)if(find(id)===id){const [seq]=records[id];rows.push(seq.map((m,d)=>{for(let j=d;j<6;j++)m|=m<<BigInt(1<<j);return m.toString()}).join(' '))}require('node:fs').writeFileSync(process.argv[2],rows.join('\n')+'\n')}
if (process.argv[3]) {
  const fs = require('node:fs');
  const classes = new Set();
  for (const row of fs.readFileSync(process.argv[3], 'utf8').trim().split(/\r?\n/)) {
    const masks = row.trim().split(/\s+/).map(BigInt);
    const id = index.get(key(masks.map((mask, d) => mask & full(d))));
    if (id === undefined) throw Error('external row missing from chronological inventory');
    const component = find(id);
    if (classes.has(component)) throw Error('duplicate external class');
    classes.add(component);
  }
  if (classes.size !== records.length - edges) throw Error('missing external class');
  console.log('external orbit bijection', classes.size);
}
console.log({total,edges});

