// Exhaust all six-port left banks on five raw inputs, up to four additional AO2 gates.
// JS masks are signed 32-bit truth tables in local assignment order.
const edges=[513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768];
const left=[0,1,2,6,7],right=[3,4,5,8,9,10],sub=(a,b)=>(a&b)===a;
const expand=(v,s)=>s.reduce((m,j,i)=>m|((v>>i&1)<<j),0);
const cof=new Map;
for(let b=0;b<64;b++){let t=0;for(let a=0;a<32;a++)if(edges.some(e=>sub(e,expand(a,left)|expand(b,right))))t|=1<<a;
if(!cof.has(t)){let p=[],n=[];for(let a=0;a<32;a++){if(t>>a&1){if(!Array.from({length:32},(_,j)=>j).some(j=>j!==a&&sub(j,a)&&(t>>j&1)))p.push(a)}else if(!Array.from({length:32},(_,j)=>j).some(j=>j!==a&&sub(a,j)&&!(t>>j&1)))n.push(a)}cof.set(t,[p,n])}}
let requirements=[...new Set([...cof.values()].flatMap(([p,n])=>p.flatMap(x=>n.map(y=>32*x+y))))];
requirements=requirements.filter(i=>!requirements.some(j=>i!==j&&sub(j>>5,i>>5)&&sub(i&31,j&31)));
const covers=new Map,goal=(1<<requirements.length)-1;
function obligations(w){if(!covers.has(w))covers.set(w,requirements.reduce((v,z,i)=>v|(((w>>(z>>5)&1)&&!(w>>(z&31)&1))<<i),0));return covers.get(w)}
function cotree(ws){let K=Array.from({length:32},(_,x)=>ws.reduce((m,w,i)=>m|((w>>x&1)<<i),0)),A=Array(6).fill(0),O=Array(6).fill(0);
for(let [p,n] of cof.values()){let P=p.map(x=>K[x]),N=n.map(x=>K[x]);for(let u of P){let absent=0;for(let v of N){let d=u&~v;if(d&&!(d&(d-1)))absent|=d}for(let i=0;i<6;i++)if(absent>>i&1)A[i]|=absent^(1<<i)}for(let v of N){let present=0;for(let u of P){let d=u&~v;if(d&&!(d&(d-1)))present|=d}for(let i=0;i<6;i++)if(present>>i&1)O[i]|=present^(1<<i)}}
function parts(m,g){let out=[];while(m){let a=m&-m,last;do{last=a;for(let i=0;i<6;i++)if(a>>i&1)a|=m&g[i]}while(a!==last);m&=~a;out.push(a)}return out}
function yes(m){if(!(m&(m-1)))return true;for(let g of [A,O]){let groups=parts(m,g);if(groups.length>1&&groups.every(yes))return true}return false}return yes(63)}
const raw=left.map((_,i)=>{let w=0;for(let x=0;x<32;x++)if(x>>i&1)w|=1<<x;return w});
function enumerate(lo,hi,budget){let hits=new Map,banks=Array(budget+1).fill(0),seen=Array.from({length:budget+1},()=>new Set),evaluated=new Map,first=[];
function visit(ws,d){let key=ws.slice(5).sort((a,b)=>a-b).join(',');if(seen[d].has(key))return;seen[d].add(key);banks[d]++;
for(let m=0;m<1<<ws.length;m++){let x=m,n=0;while(x){x&=x-1;n++}if(n!==6)continue;let u=0;for(let i=0;i<ws.length;i++)if(m>>i&1)u|=obligations(ws[i]);if(u!==goal)continue;
let sig=ws.filter((_,i)=>m>>i&1).sort((a,b)=>a-b),k=sig.join(',');if(!evaluated.has(k))evaluated.set(k,cotree(sig));if(evaluated.get(k)&&(!hits.has(k)||hits.get(k)>d))hits.set(k,d)}
if(d===budget)return;
let kids=new Set;for(let i=0;i<ws.length;i++)for(let j=0;j<i;j++)for(let v of [ws[i]&ws[j],ws[i]|ws[j]])if(!ws.includes(v))kids.add(v);
for(let v of kids)visit([...ws,v],d+1)}
for(let i=0;i<5;i++)for(let j=0;j<i;j++)first.push(raw[i]&raw[j],raw[i]|raw[j]);for(let k=lo;k<hi;k++)visit([...raw,first[k]],1);return {banks,order: evaluated.size,hits:[...hits]}}
if(require.main===module){const [lo=0,hi=20,budget=4]=process.argv.slice(2).map(Number);console.log(JSON.stringify(enumerate(lo,hi,budget)))}
