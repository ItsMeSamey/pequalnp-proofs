// Right variable order 4, 5, 8, 9, 10. Each integer encodes the 32 truth rows.
const {check} = require('./cut199_check_eight_portfolio.cjs');
const raw = Array.from({length: 5}, (_, i) =>
  Array.from({length: 32}, (_, x) => ((x >> i) & 1) << x)
    .reduce((word, bit) => word | bit, 0));
const [a, b, c, d, e] = raw;
const edge = (a & c) | (a & e) | (b & c) | (b & d) | (c & d);
const pairs = [[3,4], [0,2], [1,4]];
for (const pair of pairs) {
  for (let i = 0; i < 5; i++) {
    // A bare port accepting i would activate its term at {i,j} for each j in the guard.
    if (pair.every(j => (edge >>> ((1 << i) | (1 << j))) & 1))
      throw Error('unexpected common neighbor');
  }
}
const ports = [...pairs.map(([i,j]) => raw[i] | raw[j] | edge), edge, edge];
let checked = 0;
for (let mask = 0; mask < 32; mask++) {
  const favorableH = raw.reduce((word, variable, i) =>
    ((mask >> i) & 1) ? word | variable : word, edge);
  for (const {anchor,tree} of check(ports, favorableH)) {
    if (tree !== null) throw Error('surviving mask ' + mask + ' at anchor ' + anchor);
    checked++;
  }
}
console.log({checked, survivors: 0});
