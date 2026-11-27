// Cut 199. Enumerate all right AO2 banks through three gates and test KW activity.
const graph = [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768];
const left = [0,1,2,6,7], right = [3,4,5,8,9,10];
const L = 199, R = 2047 ^ L;
const subset = (a,b) => (a & b) === a;
const pop = x => x.toString(2).replace(/0/g,'').length;
const pack = (x,labels) => labels.reduce((a,v,i) => a | ((x>>i & 1)<<v),0);
const bits = (w,i) => Number((w >> BigInt(i)) & 1n);
const independent = Array.from({length:2048},(_,i)=>i)
  .filter(x => graph.every(e=>!subset(e,x)))
  .filter((x,i,a) => !a.some(y=>x!==y && subset(x,y)));
const cross = graph.filter(e=>(e&L)&&(e&R));
const internal = graph.filter(e=>!(e&L));
function rankSix(positive) {
  const columns = independent.map(x=>{
    let forced=0, unknown=0;
    positive.forEach((e,i)=>{
      if (!(e&L&~x)) forced |= 1<<i;
      else if (e&R&~x) unknown |= 1<<i;
    });
    return {forced,unknown};
  });
  const kernels = new Set();
  for (let h=1;h<128;h++)
    if (columns.every(({forced,unknown})=>(unknown&h)||pop(forced&h)%2===0))
      kernels.add(h);
  for (const a of kernels) for (const b of kernels)
    if (a!==b && kernels.has(a^b)) return false;
  return true;
}
const certificates = [];
for (let mask=0;mask<1<<cross.length;mask++) {
  if(pop(mask)!==6) continue;
  const positives=cross.filter((_,i)=>mask>>i&1);
  if(rankSix([...positives,internal[0]]))
    for(const edge of internal) certificates.push([...positives,edge]);
}
const raw = right.map((_,i)=>{
  let w=0n;
  for(let y=0;y<64;y++) if(y>>i&1) w|=1n<<BigInt(y);
  return w;
});
const required=[];
const profiles=Array.from({length:64},(_,y)=>{
  let row=0n;
  for(let x=0;x<32;x++) {
    const z=pack(x,left)|pack(y,right);
    if(graph.some(e=>subset(e,z))) row|=1n<<BigInt(x);
  }
  return row;
});
for(let i=0;i<64;i++) for(let j=0;j<64;j++)
  if(profiles[i]&~profiles[j]) required.push([i,j]);
const rightInput=z=>right.reduce((a,v,i)=>a|((z>>v&1)<<i),0);
const activity=new Map(), signatures=new Map();
function feature(w) {
  if(!signatures.has(w)) signatures.set(w,Array.from({length:64},(_,i)=>bits(w,i)));
  return signatures.get(w);
}
function active(w) {
  if(!activity.has(w)) activity.set(w,certificates.every(row=>row.some(z=>feature(w)[rightInput(z)])));
  return activity.get(w);
}
function audit(depth,strict) {
  const seen=new Set(), good=[];
  function evaluate(bank) {
    const live=bank.filter(w=>strict ? active(w) : w!==raw[1] && w!==raw[3]);
    if(live.length<5) return; // Four bits encode at most sixteen profiles.
    // Any feasible five-port set extends to six usable masks when six exist.
    for(let mask=1;mask<1<<live.length;mask++) {
      if(pop(mask)!==Math.min(live.length,6)) continue;
      const selected=live.filter((_,i)=>mask>>i&1);
      const key=selected.map(String).sort().join(',');
      if(seen.has(key)) continue;
      seen.add(key);
      const fs=selected.map(feature);
      if(required.every(([i,j])=>fs.some(f=>f[i]&&!f[j]))) good.push(key);
    }
  }
  function visit(bank,d) {
    if(d===depth) {evaluate(bank);return;}
    for(let i=0;i<bank.length;i++) for(let j=0;j<i;j++) {
      for(const w of [bank[i]&bank[j],bank[i]|bank[j]])
        if(!bank.includes(w)) visit([...bank,w],d+1);
    }
  }
  visit(raw,0);
  return {tested:seen.size,compatible:good.length,good};
}
if(certificates.length!==40) throw Error('Rank-family mismatch');
for(let depth=0;depth<=3;depth++){
  const x=audit(depth,true);
  if(x.compatible) throw Error('Unexpected encoder');
  console.log({depth,activeBanks:x.tested,compatible:x.compatible});
}
const relaxed=audit(3,false);
const z=raw[2]&raw[4], expected=[raw[0],raw[2],raw[4],raw[5],raw[1]|z,raw[3]|z];
if(relaxed.good.join(';')!==expected.map(String).sort().join(',')) throw Error('Unexpected relaxed encoders');
console.log({relaxedBanks:relaxed.tested,relaxedCompatible:relaxed.compatible});
