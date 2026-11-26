// Replay paired six-AND certificates for two, three, and four clean terminals.
const assert = require("node:assert/strict");
const {readFileSync} = require("node:fs");
const path = require("node:path");
const {profiles, canon, hardness, short52, hot52, hot32} = require("./six_multiple_replay");
const {hot64} = require("./six_wide_masks");
const zeroSymmetry = require("./six_zero_symmetry");

function verify(p, k, expected) {
  const profile = profiles(p);
  assert.deepEqual(profile.seen, expected.chronological);
  const classes = canon(profile.data[k]);
  assert.equal(classes.length, expected.afterOneAtom[k]);
  const rows = classes.filter(row => hardness(row).every(group => group.length > 0));
  assert.equal(rows.length, expected.afterHardWitness[k]);
  const solver = k >= 3 ? short52 : (k === 0) ? (p === 2 ? hot32 : zeroSymmetry.solve) : (p === 4 && k === 2) ? hot64 : hot52;
  let visits = 0;
  for (const row of rows) {
    const result = solver(row);
    assert.equal(result.hit, 0);
    visits += result.visits;
  }
  assert.equal(visits, expected.visits[k]);
  console.log("p="+p, "k="+k, "profiles="+rows.length, "libraries="+visits);
}
const table = JSON.parse(readFileSync(path.join(__dirname,"six-middle-census.json"),"utf8"));
const requestedP = process.argv[2] === undefined ? null : Number(process.argv[2]);
const requestedK = process.argv[3] === undefined ? null : Number(process.argv[3]);
for (const [key, expected] of Object.entries(table)) {
  const p = Number(key);
  if (requestedP !== null && requestedP !== p) continue;
  for (let k=0; k<5; k++) {
    if (requestedK !== null && requestedK !== k) continue;
    verify(p,k,expected);
  }
}
