function parity(x) {
  let result = 0;
  while (x) { result ^= 1; x &= x-1; }
  return result;
}
function score(bits, labels) {
  return labels.reduce((a,v,i) => (bits >> i & 1) ? a ^ v : a, 0);
}
function pairs(cols, dim) {
  const n = cols.length, rows = new Set(), result = new Set();
  for (let a = 0; a < 1<<dim; a++) {
    rows.add(cols.reduce((mask,v,i) => mask | parity(a & v)<<i, 0));
  }
  for (let c = 0; c < 1<<n; c++) {
    if (score(c,cols)) continue;
    for (const d of rows) if (!(c & d)) result.add(c + ',' + d);
  }
  return result;
}
function removeBit(x,i) {
  return (x & ((1<<i)-1)) | ((x>>(i+1))<<i);
}
function equal(a,b) {
  if (a.size !== b.size || [...a].some(v => !b.has(v))) throw Error('state mismatch');
}
let seed=711, comparisons=0;
function rand() {seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed>>>30;}
for (let trial=0;trial<60;trial++) {
  const cols=[1,2,rand(),rand(),rand()];
  const left=cols.map(rand), right=cols.map(rand), n=cols.length;
  const dual=[0,1].map(j=>cols.reduce((sum,v,i)=>sum^((right[i]>>j&1)?v:0),0));
  const lifted=cols.map((v,i)=>v | (left[i]<<2)).concat([4,8,...dual]);
  const full=pairs(lifted,4), raw=pairs(cols,2), seen=new Set();
  for(const pair of full) {
    const [c,d]=pair.split(',').map(Number);
    if ((c>>(n+2)) || ((d>>n)&3)) continue;
    if (((c>>n)^(d>>(n+2))) !== (score(c&31,left)^score(d&31,right))) throw Error('score');
    seen.add((c&31)+','+(d&31));
  }
  equal(raw,seen);
  for(let i=0;i<n;i++)for(let contraction=0;contraction<2;contraction++) {
    const v=lifted[i], leading=31-Math.clz32(v);
    const remaining=lifted.filter((_,j)=>i!==j).map(x=>contraction && v && (x>>leading&1) ? x^v : x);
    const projected=new Set();
    for(const pair of full) {
      const [c,d]=pair.split(',').map(Number);
      if (!((contraction?d:c)>>i&1)) projected.add(removeBit(c,i)+','+removeBit(d,i));
    }
    equal(pairs(remaining,4),projected);
    comparisons++;
  }
}
console.log('60 rooted instances and '+comparisons+' minor comparisons');
