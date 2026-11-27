// A one in the side matrix means the KW leaf must be on the right.
// Nonedges selected as negative witnesses are entire independent sets.
const matrix = [
  "11111100??", "111111??00", "010???1011", "0001111100",
  "?110?1??01", "1111111111", "1???1?1100",
];
const edges = [513, 1025, 18, 36, 136, 272, 1088];
const independent = [113, 163, 177, 269, 325, 389, 582, 596, 1066, 1186];
const graphEdges = [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768];
const left = 199;
const right = 2047 ^ left;
for (const x of independent) {
  if (graphEdges.some(edge => (x & edge) === edge)) throw Error("Invalid negative witness");
}
for (const [i, edge] of edges.entries()) {
  if (!graphEdges.includes(edge)) throw Error("Invalid positive witness");
  const row = independent.map(x =>
    !(edge & left & ~x) ? "1" : !(edge & right & ~x) ? "0" : "?"
  ).join("");
  if (row !== matrix[i]) throw Error("Incorrect forced side");
}
const possible = new Set();
for (let h = 1; h < 128; h++) {
  const selected = matrix.filter((_, i) => (h >> i) & 1);
  const excluded = independent.some((_, j) => {
    const entries = selected.map(row => row[j]);
    return !entries.includes("?") && entries.filter(x => x === "1").length % 2;
  });
  if (!excluded) possible.add(h);
}
for (const a of possible) for (const b of possible) {
  if (a !== b && possible.has(a ^ b)) throw Error("Possible two-dimensional kernel");
}
console.log("All completions have rank at least six.", [...possible]);
