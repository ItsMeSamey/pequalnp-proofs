from encoding_4186_small_witness import recognize

ops = [('and',[0,1]), ('or',[3,3]), ('and',[4,2])]
gates = [dict(op=op,inputs=pins) for op,pins in ops]
for k, edges, expected_pass, supports in [
        (0, [], False, [(0,1)]),
        (1, [], False, [(0,1),(0,1,2)]),
        (0, [[0,1]], True, []),
        (1, [[0,2]], True, [(0,1)])]:
    out = recognize(3,edges,gates,k)
    assert out["at_most_k"] is expected_pass
    assert [w["support"] for w in out["witnesses"]] == supports
    assert [w["gate"] for w in out["witnesses"]] == [0,2][:len(supports)]
    print(out)

for edges,bad_gates in [({},[]),("",[]),([],{}),([],""),([{}],[]),([],[{"op":"and","inputs":{}}])]:
    try:
        recognize(3,edges,bad_gates,1)
    except ValueError:
        pass
    else:
        raise AssertionError((edges,bad_gates))
n = 1<<400
result = recognize(n,[],[dict(op="and",inputs=[n-1,n-2])],0)
assert result["witnesses"] == [dict(gate=0,support=(n-2,n-1))]
print("Rejected malformed containers and verified sparse 401-bit input IDs.")
