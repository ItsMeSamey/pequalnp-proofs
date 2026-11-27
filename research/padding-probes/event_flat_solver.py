"""Original-word witnesses from projected affine-flat avoidance."""
from event_physical_successor import run


def solve(challenge,n,aliases,table,initial,bottom,outputs,*,backend="macro",schedule=None,
          occurrence_pins=(),id_pins=(),codebooks=None,omission_cap=None, dimension_cap=None, max_flat_rank=2):
    from event_affine_flat import solve as core
    return run(core, dict(omission_cap=omission_cap, dimension_cap=dimension_cap, max_flat_rank=max_flat_rank), False, challenge,n,aliases,table,initial,bottom,outputs,
               backend=backend,schedule=schedule,occurrence_pins=occurrence_pins,
               id_pins=id_pins,codebooks=codebooks)
