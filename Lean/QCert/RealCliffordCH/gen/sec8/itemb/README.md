# Chains for item (b) of Theorem 4.10

The scripts that produced the derivation chains of `Sec8/A/ItemBd3.lean`
((d3), both orderings of the middle indices) and `Sec8/A/ItemB21.lean`
(Clément's (21) from the relation of (46)). Every step is checked
numerically (`core.eq`), and `simlean.py` replays the emitted Lean steps.

| Script | Role |
| --- | --- |
| `core.py` | gate matrices, τ, the words of (20), (21), (45), (46), (d3), (d4) |
| `chain.py`, `lib.py`, `way.py` | splitting a chain into semantic windows on at most K indices, commutations and extra rules |
| `emit.py`, `simlean.py` | Lean step syntax, and a replay of it |
| `d3gen.py` → `gend3.py` | the (d3) chains (read the lines of the paper's Lemma A.1 derivation from `../rcch/paper.txt`, the paper's text, not committed) |
| `c21.py` → `gen21.py` | the (21) chain |
| `d3a.py`–`d3d.py`, `t1.py`, `t2.py` | exploratory checks |
