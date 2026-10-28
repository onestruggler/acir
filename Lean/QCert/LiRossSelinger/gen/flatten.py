"""Expand macro steps into Table 1 (and reversed Table 1) steps."""
import json
from macros import BASE

BOOT = json.load(open(__file__.replace('flatten.py', 'boot.json')))

def invert(steps):
    return [(f, ps, not d, pos) for (f, ps, d, pos) in reversed(steps)]

def flat_macro(name):
    """Base steps of the macro on 0..k-1 (recursively flattened)."""
    return flatten(BOOT[name])

def flatten(steps):
    out = []
    for f, ps, d, pos in steps:
        if f in BASE:
            base = flat_macro(f)
            if not d:
                base = invert(base)
            for (g, qs, e, p) in base:
                out.append((g, [ps[i] for i in qs], e, p + pos))
        else:
            out.append((f, list(ps), d, pos))
    return out
