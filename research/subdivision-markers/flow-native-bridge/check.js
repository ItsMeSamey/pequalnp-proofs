// Cycle-space enumeration; all binary masks and dot products are exact.
const bit = (word, i) => Number((word >> BigInt(i)) & 1n);
const unit = i => 1n << BigInt(i);

function weight(word) {
  let count = 0;
  while (word) {
    word &= word - 1n;
    count++;
  }
  return count;
}

function eliminate(columns) {
  const pivots = new Map();
  const relations = [];
  for (let i = 0; i < columns.length; i++) {
    let word = columns[i], combination = unit(i);
    while (word) {
      const j = word.toString(2).length - 1;
      if (!pivots.has(j)) {
        pivots.set(j, [word, combination]);
        break;
      }
      const [pivot, coefficients] = pivots.get(j);
      word ^= pivot;
      combination ^= coefficients;
    }
    if (!word) relations.push(combination);
  }
  return {pivots, relations};
}

const rank = cols => eliminate(cols).pivots.size;
const basis = cols => Array.from(eliminate(cols).pivots.values(), pair => pair[0]);
const dot = (a, b) => weight(a & b) % 2;
const inSpan = (rows, x) => rank([...rows, x]) === rank(rows);
const evaluations = (rows, value) => rows.reduce((acc, row, i) =>
  acc | (BigInt(dot(row, value)) << BigInt(i)), 0n);

function span(rows) {
  let words = [0n];
  for (const row of rows) words = words.concat(words.map(v => v ^ row));
  return words;
}

function dual(rows, length) {
  const cols = Array.from({length}, (_, i) => evaluations(rows, unit(i)));
  return eliminate(cols).relations;
}

function graph(name) {
  const edges = [];
  if (name === 'Petersen') {
    for (let i = 0; i < 5; i++) edges.push([i, (i+1)%5]);
    for (let i = 0; i < 5; i++) edges.push([i, i+5]);
    for (let i = 0; i < 5; i++) edges.push([5+i, 5+(i+2)%5]);
    return [10, edges];
  }
  if (name === 'K4') {
    for (let i = 0; i < 4; i++) {
      for (let j = i + 1; j < 4; j++) edges.push([i, j]);
    }
    return [4, edges];
  }
  if (name === 'K33') {
    for (let i = 0; i < 3; i++) {
      for (let j = 3; j < 6; j++) edges.push([i, j]);
    }
    return [6, edges];
  }
  const m = Number(name);
  for (let i = 0; i < m; i++) {
    for (const j of [0, 1, 3]) edges.push([i, m + (i+j)%m]);
  }
  return [2*m, edges];
}

function alternatingBlocks(edges, matching, third, vertices) {
  let component = Array.from({length: vertices}, (_, i) => i);
  for (let i = 0; i < edges.length; i++) {
    if (!bit(matching | third, i)) continue;
    const [a, b] = edges[i];
    const from = component[b], to = component[a];
    component = component.map(c => c === from ? to : c);
  }
  const blocks = new Map();
  for (let i = 0; i < edges.length; i++) {
    if (!bit(third, i)) continue;
    const group = component[edges[i][0]];
    blocks.set(group, (blocks.get(group) || 0n) | unit(i));
  }
  return [...blocks.values()];
}

function check(name) {
  const [n, edges] = graph(name);
  const m = edges.length, one = unit(m)-1n;
  const incidence = edges.map(([a,b]) => unit(a)^unit(b));
  const cycles = eliminate(incidence).relations;
  const cuts = dual(cycles, m);
  const odd = span(cycles).map(c => c^one);
  const delta = rank(cuts.map(h => evaluations(cuts, h)));
  let count = 0;
  const bounds = new Set();
  for (const x of odd) {
    if (weight(x) !== n/2) continue;
    for (const y of odd) {
      if (x & y) continue;
      count++;
      const z = one ^ (x | y);
      const first = alternatingBlocks(edges, x, z, n);
      const second = alternatingBlocks(edges, y, z, n);
      const overlap = rank(first.map(v => evaluations(second, v)));
      const bound = n/2 - first.length - second.length + overlap;
      bounds.add(bound);
      if (['7','8'].includes(name) && bound < 3*n/14) throw Error('joint bound');
    }
  }

  const evenCuts = dual([...cycles, one], m);
  const diagonal = v => v | (v << BigInt(m));
  const native = basis([...evenCuts, ...cycles.map(diagonal), diagonal(one)]);
  const nativeDual = dual(native, 2*m);
  const projected = rows => basis(rows.map(v => v & one));
  const primalRank = rank([...projected(native), ...cycles]) - cycles.length;
  const dualRank = rank([...projected(nativeDual), ...cycles]) - cycles.length;
  if (primalRank + 1 !== delta + delta%2 || dualRank !== 1) throw Error('affine rank');
  for (const x of odd) {
    if (!inSpan(native, diagonal(x)) || !inSpan(nativeDual, diagonal(x))) {
      throw Error('a source diagonal has no native lift');
    }
  }

  let falseWitness = null;
  if (name === 'Petersen') {
    const spokes = 31n << 5n;
    const star = edges.reduce((s, edge, i) => s | (edge.includes(0) ? unit(i) : 0n), 0n);
    const h = span(evenCuts).find(x => !(x & spokes) && dot(x, star) && !odd.includes(x));
    if (h === undefined || !inSpan(native, h) || !inSpan(nativeDual, diagonal(spokes))
        || (h & diagonal(spokes))) throw Error('spurious native witness did not verify');
    falseWitness = [h.toString(), spokes.toString()];
  }
  return [name, count, delta, delta + delta%2, [...bounds].sort((a,b) => a-b), falseWitness];
}

const result = ['K4','K33','Petersen','7','8'].map(check);
const expected = [6,12,0,48,120];
if (!result.every((row, i) => row[1] === expected[i])) throw Error('control count');
console.log(result);
