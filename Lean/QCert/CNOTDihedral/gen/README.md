# Numerical checks for the CNOT-dihedral completeness proof

No Lean module is generated: the derivations of the proof are short enough
to be written by hand.  These scripts check, on phase-affine pairs
(`|x⟩ ↦ ω^{p(x)} |f(x)⟩`, composed in operator order as in the Lean
development), every equation the proof relies on.  They need only Python 3.

* `sim.py` — the simulator: gates `X`, `T`, `ω`, `CNOT` on any wires
  (`c(n, a, b)`, the Lean `cc a b`), `SWAP`, moving up a wire, gadgets.
* `check_linear.py` — `Linear.lean`: the eleven cases of `R_mul_gen`
  (`R r * g = sh h * fo d * R r'` with the `h`, `d`, `r'` the proof uses)
  and the pushes of the fans past upper generators, at widths 2–5.
* `check_diagonal.py` — `Gadget.lean`, `Diagonal.lean`: the words of R₈,
  R₉, R₁₃ are the gadgets claimed, the steps of `T₀U₀₁ = U₀₁T₀`, `X`
  conjugation of gadgets, the phases and orders of the Möbius monomials
  (up to five wires: degree `≥ 4` vanishes), and the closure of the gadgets
  of at most three wires under `CNOT` and `SWAP` conjugation.

Run `python3 check_linear.py` and `python3 check_diagonal.py` in this folder.
