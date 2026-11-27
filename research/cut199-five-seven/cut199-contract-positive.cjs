const {solve}=require('./cut199_contract_syntax.cjs'),t=require('./cut199-contract-templates.json')[0],anchor=3;
const control=[1,[1,[0,[0,[0,t.tree,3],4],12],5],6];
const w=solve(t,anchor,16,control);
if(w===null)throw Error('positive syntax control failed');
function upper(tree,x){if(Number.isInteger(tree)){if([3,4,12].includes(tree))return 0;if([5,6].includes(tree))return 1;return x>>tree&1}return tree[0]?(upper(tree[1],x)&upper(tree[2],x)):(upper(tree[1],x)|upper(tree[2],x))}
const leaves=tree=>Number.isInteger(tree)?[tree]:leaves(tree[1]).concat(leaves(tree[2]));
if(leaves(w).sort((a,b)=>a-b).join()!=Array.from({length:13},(_,i)=>i).join())throw Error('incorrect leaf inventory');
for(let x=0;x<4096;x++)if(upper(w,x)!==upper(t.tree,x))throw Error('upper formal mismatch');
console.log('positive control: 13 leaves and 256 formal upper assignments checked');
