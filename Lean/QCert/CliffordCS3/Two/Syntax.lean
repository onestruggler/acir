/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Three-qubit Clifford+CS: the relations on a pair of qubits

The relations (a)–(c) of Figure 2 of Bian–Selinger (arXiv:2306.08530) on
one pair of adjacent qubits, the upper qubit `u` and the lower qubit `l`,
together with the monoidal relations of part (e) that concern these two
qubits: the generators `i, K_u, K_l, S_u, S_l, CS` (`Gen2`) and the
relations `Rel2`, constructor for constructor those of `Rel` at a pair
`j` (`Rel2.embed`).  Two-qubit completeness of `Rel2`
(`QCert.CliffordCS3.Two.complete2`) is the tool for the three-qubit
derivations: every equation between words on one pair that holds in
`U(4)` is derivable.
-/
import QCert.CliffordCS3.Syntax

namespace QCert.CliffordCS3.Two

/-- The generators on a pair of qubits `u` (upper) and `l` (lower). -/
inductive Gen2 : Type
  | i | Ku | Kl | Su | Sl | CS
  deriving DecidableEq, Fintype, Repr

namespace W2

abbrev g (x : Gen2) : Word Gen2 := FreeMonoid.of x
abbrev I : Word Gen2 := g .i
abbrev Ku : Word Gen2 := g .Ku
abbrev Kl : Word Gen2 := g .Kl
abbrev Su : Word Gen2 := g .Su
abbrev Sl : Word Gen2 := g .Sl
abbrev CS : Word Gen2 := g .CS
/-- `X_u = K_u S_u S_u K_u i`. -/
def Xu : Word Gen2 := Ku * Su * Su * Ku * I
/-- `X_l = K_l S_l S_l K_l i`. -/
def Xl : Word Gen2 := Kl * Sl * Sl * Kl * I

end W2

open W2

/-- The relations (a)–(c) of Figure 2 on the pair `u, l`, and the
commutations of part (e) between its gates. -/
inductive Rel2 : WRel Gen2
  | c1 : Rel2 (I ^ 4) 1
  | c2u : Rel2 (Ku ^ 2) (I ^ 3)
  | c2l : Rel2 (Kl ^ 2) (I ^ 3)
  | c3u : Rel2 (Su ^ 4) 1
  | c3l : Rel2 (Sl ^ 4) 1
  | c4u : Rel2 ((Su * Ku) ^ 3) (I ^ 3)
  | c4l : Rel2 ((Sl * Kl) ^ 3) (I ^ 3)
  | c5 : Rel2 (CS ^ 4) 1
  | c6 : Rel2 (Su * CS) (CS * Su)
  | c7 : Rel2 (Sl * CS) (CS * Sl)
  | c8 : Rel2 (Xu * CS) (CS ^ 3 * Xu * Sl)
  | c9 : Rel2 (Xl * CS) (CS ^ 3 * Xl * Su)
  | c10 : Rel2 (Su * Ku * CS * Ku * CS) (CS * Ku * CS * Ku * Su)
  | c11 : Rel2 (Sl * Kl * CS * Kl * CS) (CS * Kl * CS * Kl * Sl)
  | comm_i (A : Gen2) (hA : A ≠ .i) : Rel2 (I * g A) (g A * I)
  | comm_KuKl : Rel2 (Ku * Kl) (Kl * Ku)
  | comm_KuSl : Rel2 (Ku * Sl) (Sl * Ku)
  | comm_SuKl : Rel2 (Su * Kl) (Kl * Su)
  | comm_SuSl : Rel2 (Su * Sl) (Sl * Su)

/-- The letters of the pair `(j, j + 1)` of three qubits. -/
def emb (j : Fin 2) : Gen2 → Gen
  | .i => .i
  | .Ku => Local.K.on j.castSucc
  | .Kl => Local.K.on j.succ
  | .Su => Local.S.on j.castSucc
  | .Sl => Local.S.on j.succ
  | .CS => csOn j

/-- Words on the pair `(j, j + 1)` as three-qubit words. -/
def embW (j : Fin 2) : Word Gen2 →* Word Gen := FreeMonoid.map (emb j)

theorem embW_of (j : Fin 2) (x : Gen2) : embW j (FreeMonoid.of x) = FreeMonoid.of (emb j x) := rfl

theorem castSucc_lt_succ (j : Fin 2) : j.castSucc < j.succ := by revert j; decide

/-- Every relation on a pair is a relation of Figure 2. -/
theorem rel2_embed (j : Fin 2) {w v : Word Gen2} (h : Rel2 w v) :
    Derivable Rel (embW j w) (embW j v) := by
  cases h with
  | c1 => exact Derivable.of (by simpa [embW, emb] using Rel.c1)
  | c2u => exact Derivable.of (by simpa [embW, emb, W.K, W.I] using Rel.c2 j.castSucc)
  | c2l => exact Derivable.of (by simpa [embW, emb, W.K, W.I] using Rel.c2 j.succ)
  | c3u => exact Derivable.of (by simpa [embW, emb, W.S] using Rel.c3 j.castSucc)
  | c3l => exact Derivable.of (by simpa [embW, emb, W.S] using Rel.c3 j.succ)
  | c4u => exact Derivable.of (by simpa [embW, emb, W.S, W.K, W.I] using Rel.c4 j.castSucc)
  | c4l => exact Derivable.of (by simpa [embW, emb, W.S, W.K, W.I] using Rel.c4 j.succ)
  | c5 => exact Derivable.of (by simpa [embW, emb, W.CS] using Rel.c5 j)
  | c6 => exact Derivable.of (by simpa [embW, emb, W.S, W.CS] using Rel.c6 j)
  | c7 => exact Derivable.of (by simpa [embW, emb, W.S, W.CS] using Rel.c7 j)
  | c8 => exact Derivable.of (by simpa [embW, emb, W.S, W.CS, W.X, W.K, W.I, Xu] using Rel.c8 j)
  | c9 => exact Derivable.of (by simpa [embW, emb, W.S, W.CS, W.X, W.K, W.I, Xl] using Rel.c9 j)
  | c10 => exact Derivable.of (by simpa [embW, emb, W.S, W.CS, W.K] using Rel.c10 j)
  | c11 => exact Derivable.of (by simpa [embW, emb, W.S, W.CS, W.K] using Rel.c11 j)
  | comm_i A hA =>
    refine Derivable.of ?_
    simp only [map_mul, embW_of]
    exact Rel.comm_i (emb j A) (by revert j; cases A <;> first | exact absurd rfl hA | decide)
  | comm_KuKl =>
    exact Derivable.of (by
      simpa [embW, emb] using Rel.comm_loc Local.K Local.K j.castSucc j.succ (castSucc_lt_succ j))
  | comm_KuSl =>
    exact Derivable.of (by
      simpa [embW, emb] using Rel.comm_loc Local.K Local.S j.castSucc j.succ (castSucc_lt_succ j))
  | comm_SuKl =>
    exact Derivable.of (by
      simpa [embW, emb] using Rel.comm_loc Local.S Local.K j.castSucc j.succ (castSucc_lt_succ j))
  | comm_SuSl =>
    exact Derivable.of (by
      simpa [embW, emb] using Rel.comm_loc Local.S Local.S j.castSucc j.succ (castSucc_lt_succ j))

/-- Derivations on a pair are derivations of Figure 2. -/
theorem derivable_embed (j : Fin 2) {w v : Word Gen2} (h : Derivable Rel2 w v) :
    Derivable Rel (embW j w) (embW j v) := by
  have : conGen Rel2 ≤ (conGen Rel).comap (embW j) (fun _ _ => map_mul _ _ _) :=
    Con.conGen_le fun a b hab => rel2_embed j hab
  exact this h

end QCert.CliffordCS3.Two
