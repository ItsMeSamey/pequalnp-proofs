"""Original-word counting by compressed Gaussian inclusion-exclusion."""
from event_physical_successor import run


def solve(challenge,n,aliases,table,initial,bottom,outputs,*,backend="macro",schedule=None,
          occurrence_pins=(),id_pins=(),codebooks=None,omission_cap=None, state_cap=None, work_cap=None):
    from event_compressed_ie import solve as core
    return run(core, dict(omission_cap=omission_cap, state_cap=state_cap, work_cap=work_cap), True, challenge,n,aliases,table,initial,bottom,outputs,
               backend=backend,schedule=schedule,occurrence_pins=occurrence_pins,
               id_pins=id_pins,codebooks=codebooks)
