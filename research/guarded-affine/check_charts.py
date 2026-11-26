from random import Random
from charts import chart, value
from check import random_clause, valid


if __name__ == "__main__":
    rng = Random(38873)
    charts = 0
    assignments = 0
    for _ in range(320):
        obs = rng.randrange(5)
        hidden = rng.randrange(5)
        guards = [random_clause(rng, obs + hidden) for _ in range(hidden)]
        terminal = [random_clause(rng, obs + hidden) for _ in range(rng.randrange(4))]
        for model in range(1 << (obs + hidden)):
            if not valid(model, guards, terminal, obs):
                continue
            forms, restrictions = chart(obs, guards, terminal, model)
            charts += 1
            for x in range(1 << obs):
                y = sum(value(form, x, obs) << i for i, form in enumerate(forms))
                extension = x | (y << obs)
                assert valid(extension, guards, [], obs)
                if all(value(form, x, obs) for form in restrictions):
                    assert valid(extension, guards, terminal, obs)
                if x == model % (1 << obs):
                    assert extension == model
                    assert all(value(form, x, obs) for form in restrictions)
                assignments += 1
    print(f"Checked {charts} cyclic affine charts on {assignments} chart/input pairs.")
