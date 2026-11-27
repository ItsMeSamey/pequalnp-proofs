"""Original-word counting by projected rank-two Fourier evaluation."""
from event_physical_successor import run


def solve(challenge,n,aliases,table,initial,bottom,outputs,*,backend="macro",schedule=None,
          occurrence_pins=(),id_pins=(),codebooks=None,omission_cap=None, codimension_cap=None):
    from event_rank2_fourier import solve as core
    return run(core, dict(omission_cap=omission_cap, codimension_cap=codimension_cap), True, challenge,n,aliases,table,initial,bottom,outputs,
               backend=backend,schedule=schedule,occurrence_pins=occurrence_pins,
               id_pins=id_pins,codebooks=codebooks)
