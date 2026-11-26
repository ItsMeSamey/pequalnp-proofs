const fs = require('fs');
const basis = require('./protected.js');
const solve = require(process.argv[4] === 'group' ? './group-anchor.js' : './port-anchor.js');
const q = Number(process.argv[2]);
for (const line of fs.readFileSync(process.argv[3], 'utf8').trim().split('\n')) {
    const [id, ...u] = line.split(/\s+/);
    const choices = basis(u, true);
    if (!choices.length) {
        console.log(id, 0, 0, 0);
        continue;
    }
    let checked = 0, visits = 0, hit = 0;
    for (const extra of choices) {
        const result = solve(u, extra);
        checked++;
        visits += result.visits;
        if (result.hit) { hit = 1; break; }
    }
    console.log(id, checked, visits, hit);
}
