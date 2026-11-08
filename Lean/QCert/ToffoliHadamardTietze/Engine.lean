/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024), after the Agda `CCX+H-3qubit-Tietze`: the replay engine

Translation of `Engine.agda`: replay a concrete rewrite, retaining the
surrounding word.  All generated certificates reduce to the congruence of the
framework (`Derivable`); the search programs are outside the trusted proof.

The Agda's `by-assoc-and e p q` turns `e : a ≈ b` into `a' ≈ b'` when the two
sides have the same letters; words being lists here, `p` and `q` are equations
of words, closed by `rfl`.
-/
import QCert.ToffoliHadamardTietze.Syntactics

namespace QCert.ToffoliHadamardTietze

/-- An equation inside a prefix and a suffix. -/
theorem under {a b : Word Gen} (pre suf : Word Gen) (e : a ≈ b) : pre * a * suf ≈ pre * b * suf :=
  ((Derivable.refl pre).mul e).mul (Derivable.refl suf)

/-- An equation read with both sides rewritten to equal words. -/
theorem by_assoc_and {a b a' b' : Word Gen} (e : a ≈ b) (ha : a = a') (hb : b = b') : a' ≈ b' :=
  ha ▸ hb ▸ e

/-- An axiom. -/
theorem axiom' {w v : Word Gen} (r : Rel w v) : w ≈ v := Derivable.of r

/-- The congruence's reflexivity, symmetry and transitivity, under the
Agda's names, which the certificates use. -/
theorem refl {w : Word Gen} : w ≈ w := Derivable.refl w

theorem sym {w v : Word Gen} (e : w ≈ v) : v ≈ w := e.symm

theorem trans {u v w : Word Gen} (e : u ≈ v) (f : v ≈ w) : u ≈ w := e.trans f

end QCert.ToffoliHadamardTietze
