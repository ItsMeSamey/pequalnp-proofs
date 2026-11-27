// Lower bound for right-side producers with an uncharged final conjunction.
// Input order 4,5,8,9,10. Vertex 3 is pinned to zero before enumeration.
const raw = Array.from({length: 5}, (_, bit) => {
  let word = 0;
  for (let x = 0; x < 32; x++) word |= ((x >> bit) & 1) << x;
  return word;
});
const edges = [[0,2], [0,4], [1,2], [1,3], [2,3]];
const target = edges.reduce((word, [a,b]) => word | (raw[a] & raw[b]), 0);
const bank = [...raw];
const counts = Array(6).fill(0);

function visit(depth, intersection) {
  for (let a = 0; a < bank.length; a++) {
    for (let b = a + 1; b < bank.length; b++) {
      for (const word of [bank[a] | bank[b], bank[a] & bank[b]]) {
        // An equal earlier wire can replace a redundant gate everywhere.
        if (bank.includes(word)) continue;
        counts[depth]++;
        const next = (target & ~word) === 0 ? intersection & word : intersection;
        if (next === target) throw Error('bank of five gates or fewer suffices');
        if (depth === 5) continue;
        bank.push(word);
        visit(depth + 1, next);
        bank.pop();
      }
    }
  }
}
// Every positive raw input misses some edge, so none can be a terminal factor.
if (raw.some(word => (target & ~word) === 0)) throw Error('raw factor omitted');
visit(1, -1);
const [a,b,c,d,e] = raw;
const h = b & d, s = c | h, t = b | d, u = s & t;
if (((a | u) & (e | s)) !== target) throw Error('six-gate construction failed');
console.log(JSON.stringify({prefixes: counts.slice(1), optimum: 6}));
