"""Two physical sign markers computing AND, with optimal macro omission fee four."""
from padding_cnf import encode
from stack_align_padding import _comparator

def and_gate():
    """Only physical key 3 is accepted; underlying ID 71 carries inverted y."""
    challenge=[]
    table, initial, bottom, outputs=_comparator(challenge,("gate","gate"))
    return dict(challenge=challenge,n=1,aliases=[23,-71],table=table,
                initial=initial,bottom=bottom,outputs=outputs,schedule={},
                macro_schedule=("stay","stay"),occurrence_pins=(),id_pins=(),
                raw_witnesses={0:encode(challenge,1,0),1:encode(challenge,1,3)})

def codebooks(events):
    """Encode consecutive macro records as x, 2*x+y, and the output z."""
    first,second=events.slot_events
    rows=events.domains[first]
    previous={row.after:row.bit for row in rows}
    assert len(previous)==len(rows)==2
    books={first:{row:row.bit for row in rows},
           second:{row:2*previous[row.before]+row.bit for row in events.domains[second]},
           events.output:{0:0,1:1}}
    assert set(books[second].values())==set(range(4))
    return books
