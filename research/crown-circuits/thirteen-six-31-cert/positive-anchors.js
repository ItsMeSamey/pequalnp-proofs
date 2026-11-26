const fs = require('fs');
const path = require('path');
const F = (1n << 64n) - 1n;
const branches = [];
for (let i = 0; i < 6; i++) {
    let v = 0n;
    for (let s = 0; s < 64; s++) if ((s >> i) & 1) v |= 1n << BigInt(s);
    branches.push(v, F ^ v);
}
const helpers = new Set();
for (let i = 0; i < 13; i++) {
    const word = i | ((((i & 1) ^ ((i >> 1) & 1))) << 4) | (((((i >> 2) & 1) ^ ((i >> 3) & 1))) << 5);
    for (const start of [0, 3]) {
        let v = 0n;
        for (let j = start; j < start + 3; j++) {
            v |= branches[2*j + ((word >> j) & 1)];
            if (j > start) helpers.add(v);
        }
    }
}
if (helpers.size !== 23) throw Error('control helper count');
for (const name of ['port-anchor.js','group-anchor.js']) {
    const text = fs.readFileSync(path.join(__dirname, name), 'utf8');
    const pattern = 'budget=6-W.length-extra.length';
    if (text.split(pattern).length !== 2) throw Error('unexpected budget entry');
    const inner = {exports: null};
    Function('module', 'require', 'process', text.replace(pattern, 'budget=0').replace('for(const P of perms([0,1,2,3,4,5]))','for(const P of [])'))(inner, require, process);
    const result = inner.exports(Array(6).fill(F), [...helpers]);
    if (result.hit !== 1 || result.L !== 64 || result.budget !== 0) throw Error('positive control failed');
    console.log(name, result.L, result.hit);
}
