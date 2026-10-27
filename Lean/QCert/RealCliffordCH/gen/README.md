# Generators of `AuxEq.lean`, `Lemma75.lean`, `Lemma75Fam.lean`

Python 3 with numpy.  These scripts *find* the derivations; Lean checks
them independently (`Engine.check`, by `decide`), so they are a record of
how the certificates were obtained, not part of the trusted base.

Words are two-wire circuits in operator order over the letters `h z`
(H, Z on wire 0), `H Z` (wire 1), `C` (CZ), `K` (CH), `S` (the swap of
Equation (8)); `drawn(...)` writes a circuit in drawing order.

1. `eng.py`: semantics (numpy), canonical forms up to disjoint
   commutations, trace-aware matching, bidirectional search, tables with
   mirror (`rev`) and upside-down (`sig`) variants.
2. `auxeqs.py`: the two-wire axioms and Figure 12's equations (81)–(110), as
   transcribed (each checked numerically); `chains.py`: the paper's proof
   chains (Appendix B.2) used as waypoints, and helper equations.
3. `python prove2.py 200000` → `lib4.pkl` (all of (81)–(110));
   `python helpers.py` → `lib5.pkl`; `python d3.py` → `lib6.pkl`.
4. `fig6.py`: the 90 instances of Figure 6 on `𝒢₄` and the decoding of
   Definition 7.3; `python run6.py 60000 <families>`, `python run6b.py 400000`,
   `python collect.py` → `proven_dec.pkl`; `python d3c.py` → `proven_dec2.pkl`
   (the two instances of (d3), via `(K H)^4 = h`);
   `python g4search.py` → `g4res.pkl` (the remaining instances, by rewriting
   over `𝒢₄` with the decoded instances already proved).
5. `python gen_aux.py lib6.pkl AuxEq.lean`, `python gen75.py Lemma75.lean`,
   `python genfam.py Lemma75Fam.lean`.
