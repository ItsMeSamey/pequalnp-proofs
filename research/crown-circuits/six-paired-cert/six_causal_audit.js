// Expand every possible predecessor compatible with essential selector dependence.
const assert = require("node:assert/strict");
const {profiles, canon, hardness} = require("./six_multiple_replay.js");
const {precursorPlan} = require("./six_causal_precursors.js");

function inspect(row) {
  const u = row.map(BigInt);
  const full = (1n<<64n)-1n;
  const branches = [];
  for (let i=0; i<6; i++) {
    let half=0n;
    for (let point=0; point<64; point++)
      if ((point>>i)&1) half |= 1n<<BigInt(point);
    branches.push(u[i]&half, u[i]&~half);
  }
  const paid = [...new Set(u)].filter(mask => mask!==full && !branches.includes(mask));
  return precursorPlan(u, branches, paid);
}

const expectedMain = {1:[26,459], 2:[166,820], 3:[56,228], 4:[11,29]};
for (const p of [1,2,3,4]) {
  const data=profiles(p).data;
  for (const k of [1,2]) {
    const rows=canon(data[k]);
    const changedAll=[], changedMain=[];
    let mainCount=0, invariantMain=0;
    rows.forEach((row,index)=>{
      const plan=inspect(row);
      const main=hardness(row).every(group=>group.length>0);
      if (plan.changed) changedAll.push(index);
      if (main) {
        mainCount++;
        if (plan.mode==="invariant") invariantMain++;
        if (plan.changed) changedMain.push(index);
      }
    });
    assert.equal(mainCount,expectedMain[p][k-1]);
    assert.equal(changedMain.length,0);
    console.log(JSON.stringify({p,k,all:rows.length,main:mainCount,invariantMain,changedMain,
      otherChangedCount:changedAll.length,otherChangedIndices:changedAll}));
  }
}
