# Numerical checks for (295) on four wires and (148b) on three

The scripts that `Sec8/D/N8/Four295.lean` and `Sec8/D/W3/E148b.lean` cite as
scratch files. Run them from any directory; they import the models in `..`
(`eng3`, `letters`, `bfs3`) and `../w4` (`tok`).

| Script | Checks |
| --- | --- |
| `p295.py` | every table entry of `Four295` numerically on four wires, and the runs L4–L12 behind `eq295_4` |
| `d148.py` | the 43-step run for (148b) with `W` in its native position, and the `czc` sub-lemma |
| `d148w.py` | the relabelling of that run back to the wires of `l148b`/`r148b` |
| `s148.py` | the breadth-first search over (12), (13), (f3), (f4) alone, which finds no derivation of (148b) |
| `s1220.py` | the search that found the `czc` run |
