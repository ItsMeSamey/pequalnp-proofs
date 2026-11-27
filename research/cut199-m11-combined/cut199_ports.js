// Check the one-way monotone encodings for mask 199 (raw-input order 0..10).
const edges = [[0,9],[0,10],[1,4],[1,8],[2,5],[2,10],[3,6],[3,7],
               [4,8],[4,10],[5,8],[5,9],[6,7],[6,10],[7,9],[8,9]];
const left = [0,1,2,6,7], right = [3,4,5,8,9,10];
const subset = (a,b) => (a & b) === a;
function pack(mask, side) {
  return side.reduce((w, v, i) => w | (((mask >> i) & 1) << v), 0);
}
const rows = Array(32).fill(0n);
for (let x=0; x<32; x++) for (let y=0; y<64; y++) {
  const assignment = pack(x,left) | pack(y,right);
  if (edges.some(([a,b]) => (assignment>>a&1) && (assignment>>b&1)))
    rows[x] |= 1n << BigInt(y);
}
if (new Set(rows.slice(0,16)).size !== 16 || rows[15] === rows[31])
  throw Error("The four-dimensional face no longer pins four port labels");
const code = Array.from({length:32}, (_,i) => i);
const counts = Array(17).fill(0);
function compatible(a,b,u,v) {
  return (!subset(a,b) || subset(u,v)) && (!subset(u,v) || subset(rows[a],rows[b]));
}
function enumerate(a) {
  counts[a-16]++;
  if (a === 32) {
    if (![0,8,16,15,23,31].every(i => code[i] === i)) throw Error("Changed LCA witness");
    // Right assignment 1 means vertex 3. Right assignment 0 is empty.
    if ((rows[0]&2n) || !(rows[8]&2n) || !(rows[16]&2n) ||
        (rows[15]&1n) || (rows[23]&1n) || !(rows[31]&1n)) throw Error("Bad cofactor");
    return;
  }
  for (let u=0; u<32; u++) {
    let valid = true;
    for (let b=0; b<a; b++)
      if (!compatible(a,b,u,code[b]) || !compatible(b,a,code[b],u)) { valid=false; break; }
    if (valid) { code[a]=u; enumerate(a+1); }
  }
}
enumerate(16);
if (counts[16] !== 504) throw Error("Unexpected number of encodings");
console.log(JSON.stringify({distinctLeftProfiles:new Set(rows).size, counts}));
