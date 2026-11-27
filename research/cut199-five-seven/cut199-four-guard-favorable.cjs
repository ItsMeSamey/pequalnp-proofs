// Read unique five-port singleton masks from a JSON array of {s:[...]}.
const fs = require('node:fs');
const {check} = require('./cut199_check_eight_portfolio.cjs');
const {F, raw} = require('./cut199-m12-four-guard-template.cjs');
const {banks: masks} = JSON.parse(fs.readFileSync(process.argv[2], 'utf8'));
const words = Array.from({length: 32}, (_, mask) =>
  raw.reduce((w, x, i) => mask & (1 << i) ? w | x : w, F));
const survivors = [];
let checked = 0;
for (const {s} of masks) {
  if (s.length !== 5 || !s.every(m => Number.isInteger(m) && m >= 0 && m < 32))
    throw Error('invalid five-port support vector');
  const ports = s.map(m => words[m]);
  for (let h = 0; h < 32; h++) {
    for (const {tree, anchor} of check(ports, words[h])) {
      if (tree !== null) survivors.push({s, h, anchor});
      checked++;
    }
  }
}
fs.writeFileSync(process.argv[3], JSON.stringify(survivors));
console.log({checked, survivors: survivors.length});
