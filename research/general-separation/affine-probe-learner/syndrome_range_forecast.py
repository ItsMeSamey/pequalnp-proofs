"""Exact forecasts with the certified affine-syndrome interval engine.

Requires inject-range-engine.patch on the base tail_range_forecast module.
The latent_widths field reports independent syndrome ranks, which can differ
from physical tail widths and can differ between the two bins of one trial.
"""
import tail_range_forecast as base
from syndrome_tail_range import recognize


def posterior(h, history, query, *, max_latents=None):
    return base.posterior(h, history, query, max_latents=max_latents, range_engine=recognize)


class SyndromeRangeForecast(base.TailRangeForecast):
    def __init__(self, h, cap, *, max_latents=None):
        super().__init__(h, cap, max_latents=max_latents, range_engine=recognize)


def learner_factory(max_latents=None):
    return base.learner_factory(max_latents, range_engine=recognize)
