// Replay the six-AND single-terminal paired finite certificate using Node.js.
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const {profiles, canon, solve, solveShort} = require("./six_single_replay.js");
const {hardness, solveEarly} = require("./six_single_hard.js");

process.env.CROWN_WEAK_ANCHOR = "1";
const part = process.argv[2] ?? "all";
const run = key => part === "all" || part === String(key);
const expected = [4, 186, 1827, 5485, 4697];
const sparse = profiles();
assert.deepEqual(sparse.seen, [202, 3100, 14096, 22604, 10733, 0]);
if (run("profiles")) {
  const raw = profiles(false).data.map(rows => canon(rows).length);
  assert.deepEqual(raw, [20, 384, 2949, 8041, 6551]);
  assert.deepEqual(sparse.data.map(rows => canon(rows).length), expected);
  console.log("50,735 chronological profiles; 17,945 signed orbits; 12,199 after sparse filters");
}
for (let k = 0; k < 5; k++) {
  if (!run(k)) continue;
  const rows = canon(sparse.data[k]);
  assert.equal(rows.length, expected[k]);
  if (k === 0) {
    const table = fs.readFileSync(path.join(__dirname,"six-single-q0-certified.tsv"),"utf8")
      .trim().split("\n").map(line => line.trim().split(/\s+/));
    const supplied = table.map(row => row.slice(3));
    assert.equal(canon(supplied).length,4);
    assert.equal(canon(supplied.concat(rows)).length,4);
    for (const [id, L, visits, ...input] of table) {
      const r = solve(input);
      assert.deepEqual([r.L,r.visits,r.hit],[Number(L),Number(visits),0]);
      console.log("k=0",id,r.visits);
    }
    continue;
  }
  const selected = k < 3 ? rows.filter(row => hardness(row).every(list=>list.length)) : rows;
  const intended = [4,26,459,5485,4697][k];
  assert.equal(selected.length,intended);
  let visits = 0;
  for (const row of selected) {
    const result = k < 3 ? solveEarly(row) : solveShort(row);
    assert.equal(result.hit,0);
    visits += result.visits;
  }
  assert.equal(visits,[0,41620974,29353789,13312306,337971][k]);
  console.log("k="+k,selected.length,visits);
}
