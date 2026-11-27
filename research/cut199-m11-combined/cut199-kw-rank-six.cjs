// Column masks for the eleven representative rows, ordered here by graph index.
const edges = [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768];
const indices = [0,1,2,3,4,5,6,7,8,13,14];
const columns = [1855,1843,1839,1827,2047,2035,2031,2019,2047,2035,2031,2019,1843,2035,2035,830,818,1022,1010,1293,1485,1297,1489,284];
const independent = [];
for (let x = 0; x < 2048; x++) {
  const valid = y => edges.every(e => (e & y) !== e);
  if (valid(x) && !Array.from({length: 11}, (_, i) => 1 << i).some(b => !(b & x) && valid(x | b))) independent.push(x);
}
const left = 199, right = 2047 ^ left;
const full = independent.map((x, j) => edges.reduce((col, e, i) => {
  const k = indices.indexOf(i);
  const bit = k >= 0 ? (columns[j] >> k) & 1 : Number((e & left) === 0);
  if ((!bit && !(e & left & ~x)) || (bit && !(e & right & ~x))) throw Error("Forced side violated");
  return col | bit << i;
}, 0));
function rank(words) {
  const pivots = new Map();
  for (let word of words) {
    while (word) {
      const p = Math.floor(Math.log2(word));
      if (!pivots.has(p)) { pivots.set(p, word); break; }
      word ^= pivots.get(p);
    }
  }
  return pivots.size;
}
if (columns.length !== independent.length || rank(full) !== 6 || rank(full.map(x => x ^ 65535)) !== 6) throw Error("Unexpected rank");
console.log("Verified 16 × 24 completion; both color matrices have rank six.");
