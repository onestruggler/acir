/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Derivations checked by the kernel, with derived relations as steps

`Checker.lean` checks a rewriting chain of Table 1 instances on concrete
indices.  Here the steps may also be relations of Table 1 read backwards
(every generator is an involution, `rev_derivable`) and the derived
relations of Propositions A.11 and A.12 of the paper, proved once at
every choice of indices (`dr_ksym2`, …, `dr_k32`): each is a chain on the
indices `0, …, 3` moved along an order embedding (`derivable_rename`).
The chains are found by a search script (scratch).

* Proposition A.11: (8a) `ksym4`, (8b) `ksym5`, (8c) `ksym2`, (8d) `ksym6`;
* Proposition A.12: (9a) `k12`, (9b) `k22`, (9c) `k32`, (9d) `k31`,
  (9e) `k21`, (9f) `k11`, (9g) `relk4`.
-/
import QCert.LiRossSelinger.Checker
import QCert.LiRossSelinger.CasePair

namespace QCert.LiRossSelinger

open QCert

variable {m n : ℕ}

/-! ## A checker over any families with sound sides -/

/-- A rewriting step over the families `F`. -/
structure GStep (F : Type) (m : ℕ) where
  fam : F
  ps : List (Fin m)
  dir : Bool
  pos : ℕ

section Generic

variable {F : Type} (sd : F → List (Fin m) → Option (List (Gen m) × List (Gen m)))

/-- Apply a step. -/
def gApply (w : List (Gen m)) (st : GStep F m) : Option (List (Gen m)) :=
  match sd st.fam st.ps with
  | none => none
  | some (u, v) => if st.dir then rewriteAt w st.pos u v else rewriteAt w st.pos v u

/-- Apply a list of steps. -/
def gRun (w : List (Gen m)) : List (GStep F m) → Option (List (Gen m))
  | [] => some w
  | st :: sts => match gApply sd w st with
    | none => none
    | some w' => gRun w' sts

/-- A derivation, checked by evaluation. -/
def gCheck (w w' : List (Gen m)) (sts : List (GStep F m)) : Bool := gRun sd w sts == some w'

variable {sd}

theorem gApply_sound
    (hsd : ∀ f ps u v, sd f ps = some (u, v) →
      Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v))
    {w w' : List (Gen m)} {st : GStep F m} (h : gApply sd w st = some w') :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  unfold gApply at h
  split at h
  · exact absurd h (by simp)
  · rename_i u v hs
    have hrel := hsd _ _ _ _ hs
    split_ifs at h
    · exact rewriteAt_sound hrel h
    · exact rewriteAt_sound hrel.symm h

theorem gRun_sound
    (hsd : ∀ f ps u v, sd f ps = some (u, v) →
      Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v))
    {w w' : List (Gen m)} {sts : List (GStep F m)} (h : gRun sd w sts = some w') :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction sts generalizing w with
  | nil => obtain rfl := Option.some.inj h; exact Derivable.refl _
  | cons st sts ih =>
    unfold gRun at h
    split at h
    · exact absurd h (by simp)
    · rename_i w'' hw''
      exact (gApply_sound hsd hw'').trans (ih h)

theorem gCheck_sound
    (hsd : ∀ f ps u v, sd f ps = some (u, v) →
      Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v))
    {w w' : List (Gen m)} {sts : List (GStep F m)} (h : gCheck sd w w' sts = true) :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') :=
  gRun_sound hsd (by simpa [gCheck] using h)

end Generic

/-! ## Table 1, forwards and backwards -/

/-- The sides of a family of Table 1, read backwards when the flag is set. -/
def rsides : Fam × Bool → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | (f, false), ps => sides f ps
  | (f, true), ps => (sides f ps).map fun p => (p.1.reverse, p.2.reverse)

theorem rsides_sound : ∀ (f : Fam × Bool) (ps : List (Fin m)) (u v : List (Gen m)),
    rsides f ps = some (u, v) → Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v)
  | (f, false), ps, u, v, h => Derivable.of (sides_sound h)
  | (f, true), ps, u, v, h => by
    simp only [rsides, Option.map_eq_some_iff] at h
    obtain ⟨⟨u', v'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact rev_derivable (Derivable.of (sides_sound h1))

/-! ## Order embeddings from increasing tuples -/

/-- The order embedding `i ↦ v i` of an increasing tuple. -/
def embV {k : ℕ} (v : Fin (k + 1) → Fin n) (hv : ∀ i : Fin k, v i.castSucc < v i.succ) :
    Fin (k + 1) ↪o Fin n :=
  OrderEmbedding.ofStrictMono v (Fin.strictMono_iff_lt_succ.2 hv)

theorem embV_apply {k : ℕ} (v : Fin (k + 1) → Fin n) (hv : ∀ i : Fin k, v i.castSucc < v i.succ)
    (i : Fin (k + 1)) : embV v hv i = v i := rfl

theorem renW_ofList (f : Fin m ↪o Fin n) (l : List (Gen m)) :
    renW f (FreeMonoid.ofList l) = FreeMonoid.ofList (l.map (Gen.rename f)) := rfl

/-- `0, 1, 2, 3 ↦ a, b, c, d`. -/
def emb4 {a b c d : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) : Fin 4 ↪o Fin n :=
  embV ![a, b, c, d] (fun i => match i with
    | 0 => h₁
    | 1 => h₂
    | 2 => h₃)

section
variable {a b c d : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d)
theorem emb4_0 : emb4 h₁ h₂ h₃ 0 = a := rfl
theorem emb4_1 : emb4 h₁ h₂ h₃ 1 = b := rfl
theorem emb4_2 : emb4 h₁ h₂ h₃ 2 = c := rfl
theorem emb4_3 : emb4 h₁ h₂ h₃ 3 = d := rfl
end

/-- `0, …, 5 ↦ a, …, f`. -/
def emb6 {a b c d e f : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) (h₄ : d < e)
    (h₅ : e < f) : Fin 6 ↪o Fin n :=
  embV ![a, b, c, d, e, f] (fun i => match i with
    | 0 => h₁
    | 1 => h₂
    | 2 => h₃
    | 3 => h₄
    | 4 => h₅)

/-- `0, …, 7 ↦ a, …, h`. -/
def emb8 {a b c d e f g h : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) (h₄ : d < e)
    (h₅ : e < f) (h₆ : f < g) (h₇ : g < h) : Fin 8 ↪o Fin n :=
  embV ![a, b, c, d, e, f, g, h] (fun i => match i with
    | 0 => h₁
    | 1 => h₂
    | 2 => h₃
    | 3 => h₄
    | 4 => h₅
    | 5 => h₆
    | 6 => h₇)

section
variable {a b c d e f g h : Fin n} (h₁ : a < b) (h₂ : b < c) (h₃ : c < d) (h₄ : d < e)
  (h₅ : e < f) (h₆ : f < g) (h₇ : g < h)
theorem emb6_0 : emb6 h₁ h₂ h₃ h₄ h₅ 0 = a := rfl
theorem emb6_1 : emb6 h₁ h₂ h₃ h₄ h₅ 1 = b := rfl
theorem emb6_2 : emb6 h₁ h₂ h₃ h₄ h₅ 2 = c := rfl
theorem emb6_3 : emb6 h₁ h₂ h₃ h₄ h₅ 3 = d := rfl
theorem emb6_4 : emb6 h₁ h₂ h₃ h₄ h₅ 4 = e := rfl
theorem emb6_5 : emb6 h₁ h₂ h₃ h₄ h₅ 5 = f := rfl
theorem emb8_0 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 0 = a := rfl
theorem emb8_1 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 1 = b := rfl
theorem emb8_2 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 2 = c := rfl
theorem emb8_3 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 3 = d := rfl
theorem emb8_4 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 4 = e := rfl
theorem emb8_5 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 5 = f := rfl
theorem emb8_6 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 6 = g := rfl
theorem emb8_7 : emb8 h₁ h₂ h₃ h₄ h₅ h₆ h₇ 7 = h := rfl
end

/-! ## Derived relations (generated) -/

/-- (8c) `X_[b,c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,c]`. -/
theorem dr_ksym2 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b c h2, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x b c h2]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.x 1 2 (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 1 2 (by decide)])
    (sts := [⟨(.r4b, false), [0, 1, 2, 3], true, 0⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (8d) `X_[b,d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[c,d]`. -/
theorem dr_ksym6 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x b d (h2.trans h3), Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x c d h3]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.x 1 3 (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 2 3 (by decide)])
    (sts := [⟨(.r4c, true), [0, 1, 2, 3], false, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (8a) `X_[a,c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[c,d] (−1)_[c] (−1)_[d]`. -/
theorem dr_ksym4 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x a c (h1.trans h2), Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x c d h3, Gen.neg c, Gen.neg d]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.x 0 2 (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 2 3 (by decide), Gen.neg 2, Gen.neg 3])
    (sts := [⟨(.r1a, false), [1, 2], false, 2⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 1⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 1⟩, ⟨(.r3b, false), [0, 1, 2], false, 0⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], true, 1⟩, ⟨(.r2b, false), [1, 2, 3], false, 4⟩, ⟨(.r3c, false), [1, 2], false, 3⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 1⟩,
      ⟨(.r3b, true), [1, 2, 3], true, 0⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 1⟩, ⟨(.r3b, false), [1, 2, 3], true, 2⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 1⟩,
      ⟨(.r1a, false), [2, 3], true, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (8b) `X_[a,d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,d] X_[c,d] X_[b,d] (−1)_[b] (−1)_[c]`. -/
theorem dr_ksym5 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.x a d (h1.trans (h2.trans h3)), Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x b d (h2.trans h3), Gen.x c d h3, Gen.x b d (h2.trans h3), Gen.neg b, Gen.neg c]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.x 0 3 (by decide), Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 1 3 (by decide), Gen.x 2 3 (by decide), Gen.x 1 3 (by decide), Gen.neg 1, Gen.neg 2])
    (sts := [⟨(.r1a, false), [1, 3], false, 2⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 1⟩, ⟨(.r3b, false), [0, 2, 3], false, 0⟩, ⟨(.r1a, false), [1, 2], false, 3⟩,
      ⟨(.r4b, true), [0, 1, 2, 3], true, 2⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r3b, false), [0, 1, 2], false, 1⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 2⟩,
      ⟨(.r2b, false), [1, 2, 3], false, 5⟩, ⟨(.r3c, false), [1, 2], false, 4⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r3b, true), [1, 2, 3], true, 1⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], false, 2⟩, ⟨(.r3b, false), [1, 2, 3], true, 3⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r1a, false), [2, 3], true, 1⟩,
      ⟨(.r2d, false), [2, 3], true, 3⟩, ⟨(.r2b, false), [1, 3, 2], false, 4⟩, ⟨(.r3c, true), [1, 3], true, 3⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9e) `(−1)_[b] (−1)_[d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[a,b] X_[c,d]`. -/
theorem dr_k21 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg b, Gen.neg d, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x a b h1, Gen.x c d h3]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 1, Gen.neg 3, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 0 1 (by decide), Gen.x 2 3 (by decide)])
    (sts := [⟨(.r1a, false), [2, 3], false, 3⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 2⟩, ⟨(.r2d, false), [1, 3], true, 0⟩, ⟨(.r4a, true), [0, 1, 2, 3], false, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9f) `(−1)_[c] (−1)_[d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[a,c] X_[b,d]`. -/
theorem dr_k11 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg c, Gen.neg d, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x a c (h1.trans h2), Gen.x b d (h2.trans h3)]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 2, Gen.neg 3, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 0 2 (by decide), Gen.x 1 3 (by decide)])
    (sts := [⟨(.r1c, false), [0, 1, 2, 3], false, 0⟩, ⟨(.r1a, false), [1, 3], false, 1⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 2⟩, ⟨(.r1a, false), [2, 3], false, 2⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r3b, false), [1, 2, 3], false, 4⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 3⟩, ⟨(.r3b, true), [1, 2, 3], false, 2⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r3c, false), [1, 2], true, 5⟩, ⟨(.r2b, false), [1, 2, 3], true, 6⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 3⟩,
      ⟨(.r3b, false), [0, 1, 2], true, 2⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 3⟩, ⟨(.r1a, false), [1, 2], true, 4⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 1⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9d) `(−1)_[b] (−1)_[c] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[a,d] X_[b,c]`. -/
theorem dr_k31 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg b, Gen.neg c, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x a d (h1.trans (h2.trans h3)), Gen.x b c h2]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 1, Gen.neg 2, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 0 3 (by decide), Gen.x 1 2 (by decide)])
    (sts := [⟨(.r2d, false), [1, 2], true, 0⟩, ⟨(.r1a, false), [1, 3], false, 1⟩, ⟨(.r3c, true), [1, 3], false, 2⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 3⟩,
      ⟨(.r2b, false), [1, 3, 2], false, 0⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 1⟩, ⟨(.r1a, false), [1, 3], false, 2⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 3⟩,
      ⟨(.r1a, false), [2, 3], false, 3⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r3b, false), [1, 2, 3], false, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 4⟩,
      ⟨(.r3b, true), [1, 2, 3], false, 3⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r3c, false), [1, 2], true, 6⟩, ⟨(.r2b, false), [1, 2, 3], true, 7⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r3b, false), [0, 1, 2], true, 3⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 4⟩,
      ⟨(.r1a, false), [1, 2], true, 5⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 2⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 0⟩,
      ⟨(.r3b, false), [1, 2, 3], false, 3⟩, ⟨(.r3b, true), [0, 2, 3], true, 2⟩, ⟨(.r1a, false), [2, 3], true, 1⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9g) `(−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d] K ≈ K (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`. -/
theorem dr_relk4 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3])
    (sts := [⟨(.r1c, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r1a, false), [1, 3], false, 3⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [2, 3], false, 4⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r3b, false), [1, 2, 3], false, 6⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 5⟩, ⟨(.r3b, true), [1, 2, 3], false, 4⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r3c, false), [1, 2], true, 7⟩, ⟨(.r2b, false), [1, 2, 3], true, 8⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 5⟩,
      ⟨(.r3b, false), [0, 1, 2], true, 4⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 5⟩, ⟨(.r1a, false), [1, 2], true, 6⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 3⟩, ⟨(.r1a, false), [1, 3], false, 1⟩, ⟨(.r3c, true), [1, 3], false, 2⟩,
      ⟨(.r1a, false), [0, 2], false, 3⟩, ⟨(.r2b, false), [0, 2, 3], false, 2⟩, ⟨(.r2b, false), [1, 3, 0], false, 0⟩, ⟨(.r3c, false), [0, 2], false, 1⟩,
      ⟨(.r2a, false), [0, 2, 1, 3], false, 0⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 6⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 8⟩,
      ⟨(.r1a, false), [1, 2], false, 9⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 8⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 8⟩, ⟨(.r3b, false), [0, 1, 2], false, 7⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], true, 8⟩, ⟨(.r2b, false), [1, 2, 3], false, 11⟩, ⟨(.r3c, false), [1, 2], false, 10⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 8⟩,
      ⟨(.r3b, true), [1, 2, 3], true, 7⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 8⟩, ⟨(.r3b, false), [1, 2, 3], true, 9⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 8⟩,
      ⟨(.r1a, false), [2, 3], true, 7⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩, ⟨(.r1a, false), [1, 3], true, 6⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r1a, false), [1, 3], false, 3⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 4⟩,
      ⟨(.r1a, false), [2, 3], false, 4⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r3b, false), [1, 2, 3], false, 6⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 5⟩,
      ⟨(.r3b, true), [1, 2, 3], false, 4⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r3c, false), [1, 2], true, 7⟩, ⟨(.r2b, false), [1, 2, 3], true, 8⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], false, 5⟩, ⟨(.r3b, false), [0, 1, 2], true, 4⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 5⟩,
      ⟨(.r1a, false), [1, 2], true, 6⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 3⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 3⟩,
      ⟨(.r3c, false), [0, 2], true, 4⟩, ⟨(.r2b, false), [1, 3, 0], true, 3⟩, ⟨(.r2b, false), [0, 2, 3], true, 5⟩, ⟨(.r1a, false), [0, 2], true, 6⟩,
      ⟨(.r3c, true), [1, 3], true, 5⟩, ⟨(.r1a, false), [1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 0⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 2⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [1, 2], false, 5⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 4⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 4⟩,
      ⟨(.r3b, false), [0, 1, 2], false, 3⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r2b, false), [1, 2, 3], false, 7⟩, ⟨(.r3c, false), [1, 2], false, 6⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r3b, true), [1, 2, 3], true, 3⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 4⟩, ⟨(.r3b, false), [1, 2, 3], true, 5⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [2, 3], true, 3⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 3⟩, ⟨(.r1a, false), [1, 3], true, 2⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 1⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r2d, false), [0, 3], false, 2⟩, ⟨(.r2d, false), [1, 3], false, 3⟩,
      ⟨(.r2d, false), [0, 2], false, 1⟩, ⟨(.r2d, false), [1, 2], false, 2⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9a) `(−1)_[a] (−1)_[b] K ≈ K X_[a,c] X_[b,d] (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`. -/
theorem dr_k12 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg a, Gen.neg b, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x a c (h1.trans h2), Gen.x b d (h2.trans h3), Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 0, Gen.neg 1, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 0 2 (by decide), Gen.x 1 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3])
    (sts := [⟨(.r1b, false), [3], false, 1⟩, ⟨(.r2d, false), [1, 3], false, 2⟩, ⟨(.r1b, false), [2], false, 3⟩, ⟨(.r2d, false), [1, 2], true, 2⟩,
      ⟨(.r2d, false), [0, 3], true, 0⟩, ⟨(.r2d, false), [0, 2], true, 1⟩, ⟨(.r2d, false), [2, 3], false, 0⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩,
      ⟨(.r1a, false), [1, 3], false, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r3b, false), [1, 2, 3], false, 8⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, true), [1, 2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r3c, false), [1, 2], true, 9⟩, ⟨(.r2b, false), [1, 2, 3], true, 10⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 7⟩, ⟨(.r3b, false), [0, 1, 2], true, 6⟩,
      ⟨(.r4b, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 7⟩, ⟨(.r1a, false), [1, 2], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r2a, false), [0, 2, 1, 3], false, 5⟩, ⟨(.r1a, false), [1, 3], false, 3⟩, ⟨(.r3c, true), [1, 3], false, 4⟩, ⟨(.r1a, false), [0, 2], false, 5⟩,
      ⟨(.r2b, false), [0, 2, 3], false, 4⟩, ⟨(.r2b, false), [1, 3, 0], false, 2⟩, ⟨(.r3c, false), [0, 2], false, 3⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 2⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r1a, false), [1, 2], false, 11⟩,
      ⟨(.r4b, true), [0, 1, 2, 3], true, 10⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, false), [0, 1, 2], false, 9⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 10⟩,
      ⟨(.r2b, false), [1, 2, 3], false, 13⟩, ⟨(.r3c, false), [1, 2], false, 12⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, true), [1, 2, 3], true, 9⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, false), [1, 2, 3], true, 11⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r1a, false), [2, 3], true, 9⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], true, 9⟩, ⟨(.r1a, false), [1, 3], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 9⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [1, 3], false, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], false, 6⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, false), [1, 2, 3], false, 8⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, true), [1, 2, 3], false, 6⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3c, false), [1, 2], true, 9⟩, ⟨(.r2b, false), [1, 2, 3], true, 10⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 7⟩,
      ⟨(.r3b, false), [0, 1, 2], true, 6⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 7⟩, ⟨(.r1a, false), [1, 2], true, 8⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 5⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.r3c, false), [0, 2], true, 6⟩,
      ⟨(.r2b, false), [1, 3, 0], true, 5⟩, ⟨(.r2b, false), [0, 2, 3], true, 7⟩, ⟨(.r1a, false), [0, 2], true, 8⟩, ⟨(.r3c, true), [1, 3], true, 7⟩,
      ⟨(.r1a, false), [1, 3], true, 6⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 6⟩,
      ⟨(.r1a, false), [1, 2], false, 7⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 6⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, false), [0, 1, 2], false, 5⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.r2b, false), [1, 2, 3], false, 9⟩, ⟨(.r3c, false), [1, 2], false, 8⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 6⟩,
      ⟨(.r3b, true), [1, 2, 3], true, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, false), [1, 2, 3], true, 7⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 6⟩,
      ⟨(.r1a, false), [2, 3], true, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 5⟩, ⟨(.r1a, false), [1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 3⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r2d, false), [0, 3], false, 4⟩, ⟨(.r2d, false), [1, 3], false, 5⟩, ⟨(.r2d, false), [0, 2], false, 3⟩,
      ⟨(.r2d, false), [1, 2], false, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 0⟩, ⟨(.r1a, false), [1, 3], false, 1⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 2⟩,
      ⟨(.r1a, false), [2, 3], false, 2⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r3b, false), [1, 2, 3], false, 4⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 3⟩,
      ⟨(.r3b, true), [1, 2, 3], false, 2⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r3c, false), [1, 2], true, 5⟩, ⟨(.r2b, false), [1, 2, 3], true, 6⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], false, 3⟩, ⟨(.r3b, false), [0, 1, 2], true, 2⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 3⟩,
      ⟨(.r1a, false), [1, 2], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 1⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9b) `(−1)_[a] (−1)_[c] K ≈ K X_[a,b] X_[c,d] (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`. -/
theorem dr_k22 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg a, Gen.neg c, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x a b h1, Gen.x c d h3, Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 0, Gen.neg 2, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 0 1 (by decide), Gen.x 2 3 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3])
    (sts := [⟨(.r1b, false), [1], false, 0⟩, ⟨(.r2d, false), [0, 1], false, 1⟩, ⟨(.r1b, false), [3], false, 1⟩, ⟨(.r2d, false), [0, 3], false, 2⟩,
      ⟨(.r2d, false), [1, 3], false, 3⟩, ⟨(.r2d, false), [2, 3], false, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [1, 3], false, 5⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, false), [1, 2, 3], false, 8⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, true), [1, 2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3c, false), [1, 2], true, 9⟩,
      ⟨(.r2b, false), [1, 2, 3], true, 10⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 7⟩, ⟨(.r3b, false), [0, 1, 2], true, 6⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r4b, true), [0, 1, 2, 3], false, 7⟩, ⟨(.r1a, false), [1, 2], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 5⟩,
      ⟨(.r1a, false), [1, 3], false, 3⟩, ⟨(.r3c, true), [1, 3], false, 4⟩, ⟨(.r1a, false), [0, 2], false, 5⟩, ⟨(.r2b, false), [0, 2, 3], false, 4⟩,
      ⟨(.r2b, false), [1, 3, 0], false, 2⟩, ⟨(.r3c, false), [0, 2], false, 3⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 2⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 6⟩,
      ⟨(.r2a, false), [0, 2, 1, 3], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r1a, false), [1, 2], false, 11⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 10⟩,
      ⟨(.r4b, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, false), [0, 1, 2], false, 9⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 10⟩, ⟨(.r2b, false), [1, 2, 3], false, 13⟩,
      ⟨(.r3c, false), [1, 2], false, 12⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, true), [1, 2, 3], true, 9⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 10⟩,
      ⟨(.r3b, false), [1, 2, 3], true, 11⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r1a, false), [2, 3], true, 9⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 9⟩,
      ⟨(.r1a, false), [1, 3], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 9⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩,
      ⟨(.r1a, false), [1, 3], false, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r3b, false), [1, 2, 3], false, 8⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, true), [1, 2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r3c, false), [1, 2], true, 9⟩, ⟨(.r2b, false), [1, 2, 3], true, 10⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 7⟩, ⟨(.r3b, false), [0, 1, 2], true, 6⟩,
      ⟨(.r4b, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 7⟩, ⟨(.r1a, false), [1, 2], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r2a, false), [0, 2, 1, 3], false, 5⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.r3c, false), [0, 2], true, 6⟩, ⟨(.r2b, false), [1, 3, 0], true, 5⟩,
      ⟨(.r2b, false), [0, 2, 3], true, 7⟩, ⟨(.r1a, false), [0, 2], true, 8⟩, ⟨(.r3c, true), [1, 3], true, 7⟩, ⟨(.r1a, false), [1, 3], true, 6⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], false, 2⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [1, 2], false, 7⟩,
      ⟨(.r4b, true), [0, 1, 2, 3], true, 6⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, false), [0, 1, 2], false, 5⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 6⟩,
      ⟨(.r2b, false), [1, 2, 3], false, 9⟩, ⟨(.r3c, false), [1, 2], false, 8⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, true), [1, 2, 3], true, 5⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, false), [1, 2, 3], true, 7⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], true, 5⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], true, 5⟩, ⟨(.r1a, false), [1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 5⟩,
      ⟨(.r2d, false), [0, 3], false, 4⟩, ⟨(.r2d, false), [1, 3], false, 5⟩, ⟨(.r2d, false), [0, 2], false, 3⟩, ⟨(.r2d, false), [1, 2], false, 4⟩,
      ⟨(.r1a, false), [2, 3], false, 3⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 2⟩, ⟨(.r2d, false), [1, 3], true, 0⟩, ⟨(.r4a, true), [0, 1, 2, 3], false, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- (9c) `(−1)_[a] (−1)_[d] K ≈ K X_[a,d] X_[b,c] (−1)_[a] (−1)_[b] (−1)_[c] (−1)_[d]`. -/
theorem dr_k32 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.neg a, Gen.neg d, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.x a d (h1.trans (h2.trans h3)), Gen.x b c h2, Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.neg 0, Gen.neg 3, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.x 0 3 (by decide), Gen.x 1 2 (by decide), Gen.neg 0, Gen.neg 1, Gen.neg 2, Gen.neg 3])
    (sts := [⟨(.r1b, false), [2], false, 1⟩, ⟨(.r1b, false), [1], false, 2⟩, ⟨(.r2d, false), [0, 2], true, 0⟩, ⟨(.r2d, false), [0, 1], true, 1⟩,
      ⟨(.r2d, false), [1, 2], false, 0⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [1, 3], false, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩,
      ⟨(.r1a, false), [2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, false), [1, 2, 3], false, 8⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r3b, true), [1, 2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3c, false), [1, 2], true, 9⟩, ⟨(.r2b, false), [1, 2, 3], true, 10⟩,
      ⟨(.r4a, false), [0, 1, 2, 3], false, 7⟩, ⟨(.r3b, false), [0, 1, 2], true, 6⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 7⟩,
      ⟨(.r1a, false), [1, 2], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 5⟩, ⟨(.r1a, false), [1, 3], false, 3⟩,
      ⟨(.r3c, true), [1, 3], false, 4⟩, ⟨(.r1a, false), [0, 2], false, 5⟩, ⟨(.r2b, false), [0, 2, 3], false, 4⟩, ⟨(.r2b, false), [1, 3, 0], false, 2⟩,
      ⟨(.r3c, false), [0, 2], false, 3⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 2⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r2a, false), [0, 2, 1, 3], true, 8⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r1a, false), [1, 2], false, 11⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 10⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 10⟩,
      ⟨(.r3b, false), [0, 1, 2], false, 9⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 10⟩, ⟨(.r2b, false), [1, 2, 3], false, 13⟩, ⟨(.r3c, false), [1, 2], false, 12⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, true), [1, 2, 3], true, 9⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 10⟩, ⟨(.r3b, false), [1, 2, 3], true, 11⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], false, 10⟩, ⟨(.r1a, false), [2, 3], true, 9⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 9⟩, ⟨(.r1a, false), [1, 3], true, 8⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 9⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [1, 3], false, 5⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, false), [1, 2, 3], false, 8⟩,
      ⟨(.r4c, true), [0, 1, 2, 3], true, 7⟩, ⟨(.r3b, true), [1, 2, 3], false, 6⟩, ⟨(.r4c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r3c, false), [1, 2], true, 9⟩,
      ⟨(.r2b, false), [1, 2, 3], true, 10⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 7⟩, ⟨(.r3b, false), [0, 1, 2], true, 6⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 7⟩,
      ⟨(.r4b, true), [0, 1, 2, 3], false, 7⟩, ⟨(.r1a, false), [1, 2], true, 8⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 7⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 5⟩,
      ⟨(.r2a, false), [0, 2, 1, 3], true, 5⟩, ⟨(.r3c, false), [0, 2], true, 6⟩, ⟨(.r2b, false), [1, 3, 0], true, 5⟩, ⟨(.r2b, false), [0, 2, 3], true, 7⟩,
      ⟨(.r1a, false), [0, 2], true, 8⟩, ⟨(.r3c, true), [1, 3], true, 7⟩, ⟨(.r1a, false), [1, 3], true, 6⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 2⟩,
      ⟨(.r2a, false), [0, 2, 1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [1, 2], false, 7⟩, ⟨(.r4b, true), [0, 1, 2, 3], true, 6⟩,
      ⟨(.r4b, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, false), [0, 1, 2], false, 5⟩, ⟨(.r4a, false), [0, 1, 2, 3], true, 6⟩, ⟨(.r2b, false), [1, 2, 3], false, 9⟩,
      ⟨(.r3c, false), [1, 2], false, 8⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r3b, true), [1, 2, 3], true, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 6⟩,
      ⟨(.r3b, false), [1, 2, 3], true, 7⟩, ⟨(.r4c, false), [0, 1, 2, 3], false, 6⟩, ⟨(.r1a, false), [2, 3], true, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 5⟩,
      ⟨(.r1a, false), [1, 3], true, 4⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 3⟩, ⟨(.r1c, false), [0, 1, 2, 3], true, 5⟩, ⟨(.r2d, false), [0, 3], false, 4⟩,
      ⟨(.r2d, false), [1, 3], false, 5⟩, ⟨(.r2d, false), [0, 2], false, 3⟩, ⟨(.r2d, false), [1, 2], false, 4⟩, ⟨(.r2d, false), [1, 2], true, 0⟩,
      ⟨(.r1a, false), [1, 3], false, 1⟩, ⟨(.r3c, true), [1, 3], false, 2⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 3⟩, ⟨(.r2b, false), [1, 3, 2], false, 0⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], false, 1⟩, ⟨(.r1a, false), [1, 3], false, 2⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 3⟩, ⟨(.r1a, false), [2, 3], false, 3⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r3b, false), [1, 2, 3], false, 5⟩, ⟨(.r4c, true), [0, 1, 2, 3], true, 4⟩, ⟨(.r3b, true), [1, 2, 3], false, 3⟩,
      ⟨(.r4c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r3c, false), [1, 2], true, 6⟩, ⟨(.r2b, false), [1, 2, 3], true, 7⟩, ⟨(.r4a, false), [0, 1, 2, 3], false, 4⟩,
      ⟨(.r3b, false), [0, 1, 2], true, 3⟩, ⟨(.r4b, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r4b, true), [0, 1, 2, 3], false, 4⟩, ⟨(.r1a, false), [1, 2], true, 5⟩,
      ⟨(.r1c, false), [0, 1, 2, 3], true, 4⟩, ⟨(.r2a, false), [0, 2, 1, 3], false, 2⟩, ⟨(.r4c, true), [0, 1, 2, 3], false, 0⟩, ⟨(.r3b, false), [1, 2, 3], false, 3⟩,
      ⟨(.r3b, true), [0, 2, 3], true, 2⟩, ⟨(.r1a, false), [2, 3], true, 1⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-- `K_[a,b,c,d] (−1)_[a] K_[a,b,c,d] ≈ X_[b,c] (−1)_[a] K_[a,b,c,d] (−1)_[a]`, from (4b). -/
theorem dr_knk0 {a b c d : Fin n} (h1 : a < b) (h2 : b < c) (h3 : c < d) :
    Derivable (Table1 n) (FreeMonoid.ofList [Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.k a b c d h1 h2 h3])
      (FreeMonoid.ofList [Gen.x b c h2, Gen.neg a, Gen.k a b c d h1 h2 h3, Gen.neg a]) := by
  have h := derivable_rename (emb4 h1 h2 h3) (gCheck_sound rsides_sound
    (w := ([Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.neg 0, Gen.k 0 1 2 3 (by decide) (by decide) (by decide)] : List (Gen 4)))
    (w' := [Gen.x 1 2 (by decide), Gen.neg 0, Gen.k 0 1 2 3 (by decide) (by decide) (by decide), Gen.neg 0])
    (sts := [⟨(.r1b, false), [0], false, 0⟩, ⟨(.r1b, false), [0], false, 5⟩, ⟨(.r4b, false), [0, 1, 2, 3], false, 1⟩, ⟨(.r2b, false), [1, 2, 0], false, 0⟩])
    (by decide +kernel))
  simpa only [renW_ofList, List.map_cons, List.map_nil, Gen.rename, emb4_0, emb4_1, emb4_2,
    emb4_3] using h

/-! ## Derived relations as steps -/

/-- The derived relations, on four increasing indices. -/
inductive MFam
  | ksym2 | ksym6 | ksym4 | ksym5 | k21 | k11 | k31 | relk4 | k12 | k22 | k32 | knk0
  deriving DecidableEq

/-- The two sides of a derived relation at `a < b < c < d`. -/
def mword : MFam → (a b c d : Fin m) → a < b → b < c → c < d → List (Gen m) × List (Gen m)
  | .ksym2, a, b, c, d, h1, h2, h3 =>
    ([Gen.x b c h2, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x b c h2])
  | .ksym6, a, b, c, d, h1, h2, h3 =>
    ([Gen.x b d (h2.trans h3), Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x c d h3])
  | .ksym4, a, b, c, d, h1, h2, h3 =>
    ([Gen.x a c (h1.trans h2), Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x c d h3, Gen.neg c, Gen.neg d])
  | .ksym5, a, b, c, d, h1, h2, h3 =>
    ([Gen.x a d (h1.trans (h2.trans h3)), Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x b d (h2.trans h3), Gen.x c d h3, Gen.x b d (h2.trans h3), Gen.neg b, Gen.neg c])
  | .k21, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg b, Gen.neg d, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x a b h1, Gen.x c d h3])
  | .k11, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg c, Gen.neg d, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x a c (h1.trans h2), Gen.x b d (h2.trans h3)])
  | .k31, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg b, Gen.neg c, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x a d (h1.trans (h2.trans h3)), Gen.x b c h2])
  | .relk4, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d])
  | .k12, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg a, Gen.neg b, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x a c (h1.trans h2), Gen.x b d (h2.trans h3), Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d])
  | .k22, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg a, Gen.neg c, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x a b h1, Gen.x c d h3, Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d])
  | .k32, a, b, c, d, h1, h2, h3 =>
    ([Gen.neg a, Gen.neg d, Gen.k a b c d h1 h2 h3],
      [Gen.k a b c d h1 h2 h3, Gen.x a d (h1.trans (h2.trans h3)), Gen.x b c h2, Gen.neg a, Gen.neg b, Gen.neg c, Gen.neg d])
  | .knk0, a, b, c, d, h1, h2, h3 =>
    ([Gen.k a b c d h1 h2 h3, Gen.neg a, Gen.k a b c d h1 h2 h3],
      [Gen.x b c h2, Gen.neg a, Gen.k a b c d h1 h2 h3, Gen.neg a])

theorem mword_sound : ∀ (f : MFam) (a b c d : Fin m) (h1 : a < b) (h2 : b < c) (h3 : c < d),
    Derivable (Table1 m) (FreeMonoid.ofList (mword f a b c d h1 h2 h3).1)
      (FreeMonoid.ofList (mword f a b c d h1 h2 h3).2)
  | .ksym2, _, _, _, _, h1, h2, h3 => dr_ksym2 h1 h2 h3
  | .ksym6, _, _, _, _, h1, h2, h3 => dr_ksym6 h1 h2 h3
  | .ksym4, _, _, _, _, h1, h2, h3 => dr_ksym4 h1 h2 h3
  | .ksym5, _, _, _, _, h1, h2, h3 => dr_ksym5 h1 h2 h3
  | .k21, _, _, _, _, h1, h2, h3 => dr_k21 h1 h2 h3
  | .k11, _, _, _, _, h1, h2, h3 => dr_k11 h1 h2 h3
  | .k31, _, _, _, _, h1, h2, h3 => dr_k31 h1 h2 h3
  | .relk4, _, _, _, _, h1, h2, h3 => dr_relk4 h1 h2 h3
  | .k12, _, _, _, _, h1, h2, h3 => dr_k12 h1 h2 h3
  | .k22, _, _, _, _, h1, h2, h3 => dr_k22 h1 h2 h3
  | .k32, _, _, _, _, h1, h2, h3 => dr_k32 h1 h2 h3
  | .knk0, _, _, _, _, h1, h2, h3 => dr_knk0 h1 h2 h3

/-- The sides of a derived relation at the given indices. -/
def msides : MFam → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | f, [a, b, c, d] => if h : a < b ∧ b < c ∧ c < d then some (mword f a b c d h.1 h.2.1 h.2.2)
      else none
  | _, _ => none

theorem msides_sound (f : MFam) (ps : List (Fin m)) (u v : List (Gen m))
    (h : msides f ps = some (u, v)) :
    Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v) := by
  unfold msides at h
  split at h
  · split_ifs at h with hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact mword_sound f _ _ _ _ hc.1 hc.2.1 hc.2.2
  · exact absurd h (by simp)

/-- Table 1 and the derived relations. -/
def bsides : Fam ⊕ MFam → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | .inl f, ps => sides f ps
  | .inr f, ps => msides f ps

theorem bsides_sound : ∀ (f : Fam ⊕ MFam) (ps : List (Fin m)) (u v : List (Gen m)),
    bsides f ps = some (u, v) → Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v)
  | .inl f, ps, u, v, h => Derivable.of (sides_sound h)
  | .inr f, ps, u, v, h => msides_sound f ps u v h

/-- Table 1 and the derived relations, read backwards when the flag is set. -/
def dsides : (Fam ⊕ MFam) × Bool → List (Fin m) → Option (List (Gen m) × List (Gen m))
  | (f, false), ps => bsides f ps
  | (f, true), ps => (bsides f ps).map fun p => (p.1.reverse, p.2.reverse)

theorem dsides_sound : ∀ (f : (Fam ⊕ MFam) × Bool) (ps : List (Fin m)) (u v : List (Gen m)),
    dsides f ps = some (u, v) → Derivable (Table1 m) (FreeMonoid.ofList u) (FreeMonoid.ofList v)
  | (f, false), ps, u, v, h => bsides_sound f ps u v h
  | (f, true), ps, u, v, h => by
    simp only [dsides, Option.map_eq_some_iff] at h
    obtain ⟨⟨u', v'⟩, h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact rev_derivable (bsides_sound f ps u' v' h1)

/-- A derivation with derived relations as steps, checked by evaluation. -/
abbrev checkD (w w' : List (Gen m)) (sts : List (GStep ((Fam ⊕ MFam) × Bool) m)) : Bool :=
  gCheck dsides w w' sts

theorem checkD_sound {w w' : List (Gen m)} {sts : List (GStep ((Fam ⊕ MFam) × Bool) m)}
    (h : checkD w w' sts = true) :
    Derivable (Table1 m) (FreeMonoid.ofList w) (FreeMonoid.ofList w') :=
  gCheck_sound dsides_sound h

end QCert.LiRossSelinger
