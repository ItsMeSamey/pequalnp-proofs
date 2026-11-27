# Recognizing zero existential 2-CNF backdoor dimension

Let F be an explicit 3-CNF on its original coordinates. Allow unrestricted finite
auxiliary variables and require the projection of the extended solutions to be
exactly Sat(F). The existence of an extension that is already 2-CNF is
coNP-complete, even when a satisfying assignment of F is supplied.

Projections of 2-CNF are 2-CNF by variable elimination. Conversely a Boolean
relation closed under coordinatewise ternary majority is definable by its valid
clauses of width at most two. Indeed if all unary and binary projections of a
tuple extend to the relation, inductively every subset of its coordinates
extends: for a subset of size at least three take three witnesses, each
omitting a different coordinate, and apply majority. The empty relation has
an inconsistent definition. Thus three satisfying assignments whose majority
fails give the complementary NP certificate.

Given an arbitrary 3-CNF H, add a selector y and three fresh bits a,b,c.
Condition each original clause and the clause (a or b or c) on y=1.
Split any resulting width-four clause (not y or l1 or l2 or l3) into
(not y or l1 or s) and (not s or l2 or l3) with its own bit s. Keep shorter
conditional clauses unchanged. For each variable v other than y, including
all split bits, add (y or not v). The all-zero assignment is a supplied
solution. If H is unsatisfiable, it is the unique solution. If H is satisfiable,
fix a model of H and lift each of the three singleton assignments of (a,b,c)
at y=1, choosing valid split bits. Their majority has y=1 and (a,b,c)=000;
no split-bit choice can repair this violated conditioned clause. This is
a polynomial reduction from UNSAT and establishes the claim.

The reduction addresses recognition of semantic dimension zero. An explicit
2-CNF extension supplied alongside an instance has a polynomial-time
satisfiability algorithm.
