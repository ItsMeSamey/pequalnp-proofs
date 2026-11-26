// Grant all independent branches before a demand, in every permissible chronology.
function safeLibrary(activations, branches, paid, goal) {
  const length = activations.length;
  const successor = Array.from({length}, () => Array(length).fill(false));
  for (let child=0; child<length; child++) {
    for (let parent=0; parent<length; parent++) {
      if (parent===child) continue;
      const bit = 1 << parent;
      const mask = activations[child];
      for (let point=0; point<(1<<length); point++) {
        if (((mask>>BigInt(point))&1n) !== ((mask>>BigInt(point^bit))&1n)) {
          successor[parent][child] = true;
          break;
        }
      }
    }
  }
  for (let middle=0; middle<length; middle++)
    for (let a=0; a<length; a++)
      for (let b=0; b<length; b++)
        if (successor[a][middle] && successor[middle][b]) successor[a][b] = true;
  const demand = activations.indexOf(goal);
  const usable = branches.filter((mask,index) => {
    const gate = index >> 1;
    return gate !== demand && !successor[demand][gate] && (mask & ~goal) === 0n;
  });
  const closure = new Set([0n]);
  for (const source of usable)
    for (const prior of [...closure]) closure.add(source | prior);
  const supplied = new Set(usable);
  for (const mask of paid)
    if (mask !== goal && closure.has(mask)) supplied.add(mask);
  return {sources:[...supplied], closure};
}
function precursorPlan(activations, branches, paid) {
  let bestScore = 0;
  let selected = null;
  for (const goal of paid) {
    const gate = activations.indexOf(goal);
    const initial = branches.slice(0, 2*gate).filter(mask => (mask & ~goal) === 0n);
    const closure = new Set([0n]);
    for (const mask of initial)
      for (const prior of [...closure]) closure.add(mask | prior);
    const sources = new Set(initial);
    for (const other of paid)
      if (other !== goal && closure.has(other)) sources.add(other);
    const cost = new Map([[0n, 0]]);
    for (const source of sources)
      for (const [prior, count] of [...cost]) {
        const joined = prior | source;
        cost.set(joined, Math.min(cost.get(joined) ?? Infinity, count+1));
      }
    const score = cost.get(goal)-2;
    if (score > bestScore) {
      bestScore = score;
      selected = {goal, original:sources};
    }
  }
  if (selected === null) return {mode:"unrestricted", changed:false};
  const {goal, original} = selected;
  const invariant = safeLibrary(activations, branches, paid, goal);
  const difference = invariant.sources.filter(source => !original.has(source));
  if (difference.length || invariant.sources.length !== original.size)
    return {mode:"unrestricted", changed:true, goal, difference};
  return {mode:"invariant", changed:false, goal, ...invariant};
}
module.exports = {safeLibrary, precursorPlan};

