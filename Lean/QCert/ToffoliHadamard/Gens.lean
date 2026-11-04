/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Amy, Ross, Wesley (2024): generators of `𝒢₈` by their indices

`AG` describes a generator of Li–Ross–Selinger's `𝒢₈` by its indices, with
its encoding over the macro alphabet (`AG.enc`), the action of an adjacent
transposition `s_j` on its indices (`AG.act`), and whether `s_j` keeps it
well-formed, i.e. does not exchange two of its indices (`AG.valid`).
`allAG` lists the 106 generators.
-/
import QCert.ToffoliHadamard.Macro

namespace QCert.ToffoliHadamard.Macro

open Engine

/-- A generator of `𝒢₈` by its indices. -/
inductive AG : Type
  | n (a : ℕ)
  | x (a b : ℕ)
  | k (a b c d : ℕ)
  deriving DecidableEq

/-- Its encoding over `ML`. -/
def AG.enc : AG → List ML
  | .n a => negM a
  | .x a b => xabM a b
  | .k a b c d => kwM a b c d

/-- The adjacent transposition `s_j` on indices. -/
def sw (j i : ℕ) : ℕ := if i = j then j + 1 else if i = j + 1 then j else i

/-- `s_j` applied to the indices of a generator. -/
def AG.act (j : ℕ) : AG → AG
  | .n a => .n (sw j a)
  | .x a b => .x (sw j a) (sw j b)
  | .k a b c d => .k (sw j a) (sw j b) (sw j c) (sw j d)

/-- The indices of a generator. -/
def AG.idx : AG → List ℕ
  | .n a => [a]
  | .x a b => [a, b]
  | .k a b c d => [a, b, c, d]

/-- `s_j` does not exchange two indices of `g`. -/
def AG.valid (j : ℕ) (g : AG) : Bool := !(g.idx.contains j && g.idx.contains (j + 1))

/-- A path applied to the indices of a generator (`s_{j₁}` first). -/
def AG.actPath : List ℕ → AG → AG
  | [], g => g
  | j :: P, g => AG.actPath P (g.act j)

/-- Every step of the path is valid for the generator. -/
def AG.validPath : List ℕ → AG → Bool
  | [], _ => true
  | j :: P, g => g.valid j && AG.validPath P (g.act j)

/-- The 106 generators of `𝒢₈`. -/
def allAG : List AG :=
  [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .x 0 1, .x 0 2, .x 0 3, .x 0 4, .x 0 5,
   .x 0 6, .x 0 7, .x 1 2, .x 1 3, .x 1 4, .x 1 5, .x 1 6, .x 1 7, .x 2 3, .x 2 4, .x 2 5,
   .x 2 6, .x 2 7, .x 3 4, .x 3 5, .x 3 6, .x 3 7, .x 4 5, .x 4 6, .x 4 7, .x 5 6, .x 5 7,
   .x 6 7, .k 0 1 2 3, .k 0 1 2 4, .k 0 1 2 5, .k 0 1 2 6, .k 0 1 2 7, .k 0 1 3 4, .k 0 1 3 5,
   .k 0 1 3 6, .k 0 1 3 7, .k 0 1 4 5, .k 0 1 4 6, .k 0 1 4 7, .k 0 1 5 6, .k 0 1 5 7,
   .k 0 1 6 7, .k 0 2 3 4, .k 0 2 3 5, .k 0 2 3 6, .k 0 2 3 7, .k 0 2 4 5, .k 0 2 4 6,
   .k 0 2 4 7, .k 0 2 5 6, .k 0 2 5 7, .k 0 2 6 7, .k 0 3 4 5, .k 0 3 4 6, .k 0 3 4 7,
   .k 0 3 5 6, .k 0 3 5 7, .k 0 3 6 7, .k 0 4 5 6, .k 0 4 5 7, .k 0 4 6 7, .k 0 5 6 7,
   .k 1 2 3 4, .k 1 2 3 5, .k 1 2 3 6, .k 1 2 3 7, .k 1 2 4 5, .k 1 2 4 6, .k 1 2 4 7,
   .k 1 2 5 6, .k 1 2 5 7, .k 1 2 6 7, .k 1 3 4 5, .k 1 3 4 6, .k 1 3 4 7, .k 1 3 5 6,
   .k 1 3 5 7, .k 1 3 6 7, .k 1 4 5 6, .k 1 4 5 7, .k 1 4 6 7, .k 1 5 6 7, .k 2 3 4 5,
   .k 2 3 4 6, .k 2 3 4 7, .k 2 3 5 6, .k 2 3 5 7, .k 2 3 6 7, .k 2 4 5 6, .k 2 4 5 7,
   .k 2 4 6 7, .k 2 5 6 7, .k 3 4 5 6, .k 3 4 5 7, .k 3 4 6 7, .k 3 5 6 7, .k 4 5 6 7]

/-- An adjacent transport certificate: `T_j · enc g · T_j = enc (s_j g)` by
`n` plain steps packed in `code`. -/
structure AdjCert where
  j : ℕ
  g : AG
  n : ℕ
  code : ℕ

/-- The equation a certificate proves. -/
def AdjCert.entry (c : AdjCert) : Entry ML :=
  ⟨.T c.j :: c.g.enc ++ [.T c.j], (c.g.act c.j).enc, false, c.n, c.code⟩

theorem AdjCert.derivable {E : List (Eqn ML)} (hE : Valid MRel E) {cs : List AdjCert}
    (h : checkFlat' κM E (cs.map AdjCert.entry) = true) {c : AdjCert} (hc : c ∈ cs) :
    Derivable MRel (FreeMonoid.ofList c.entry.lhs) (FreeMonoid.ofList c.entry.rhs) :=
  checkFlat'_valid κM_inj hE h (c.entry.lhs, c.entry.rhs) (by
    simp only [Engine.eqns, List.map_map]
    exact List.mem_map_of_mem (f := (fun t : Entry ML => (t.lhs, t.rhs)) ∘ AdjCert.entry) hc)

/-- `p a` for every `a < n`, by primitive recursion: the families' checks
evaluate it tens of thousands of times, where `(List.range n).all p` cost
the kernel a third more. -/
def allBelow (n : ℕ) (p : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k acc => p k && acc) n

theorem allBelow_spec {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) {a : ℕ} (ha : a < n) :
    p a = true := by
  induction n with
  | zero => omega
  | succ k ih =>
    have h' : (p k && allBelow k p) = true := h
    rw [Bool.and_eq_true] at h'
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
    · exact ih h'.2 ha
    · exact h'.1

theorem imp_spec {p : Prop} [Decidable p] {b : Bool} (h : (!decide p || b) = true) (hp : p) :
    b = true := by
  simpa [hp] using h


/-! ## Membership by code

`allAG.contains g`, and the search of the certificate of a pair `(g, j)` in
`adjCerts`, scan lists of 106 and 630 elements with the derived equality of
`AG`; decided 2 123 and 742 times, that was most of the kernel time of
`Families` and `MacroTable`.  Instead a generator is coded by a number
(`agKey`, injective on generators with indices below 8), a list of
generators by the set of their codes as the bits of one number (`bitsOf`),
and membership is one `Nat.testBit`. -/

/-- The code of a generator: injective on generators with indices below `8`. -/
def agKey : AG → ℕ
  | .n a => a
  | .x a b => 8 + 8 * a + b
  | .k a b c d => 72 + 512 * a + 64 * b + 8 * c + d

/-- The indices are below `8`. -/
def boundedAG : AG → Bool
  | .n a => Nat.blt a 8
  | .x a b => Nat.blt a 8 && Nat.blt b 8
  | .k a b c d => Nat.blt a 8 && Nat.blt b 8 && Nat.blt c 8 && Nat.blt d 8

theorem agKey_inj {g g' : AG} (hg : boundedAG g = true) (hg' : boundedAG g' = true)
    (h : agKey g = agKey g') : g = g' := by
  cases g <;> cases g' <;>
    simp only [boundedAG, Bool.and_eq_true, Nat.blt_eq, agKey] at hg hg' h <;>
    first | rfl | (exfalso; omega) | (congr 1 <;> omega)

/-- The codes of a list, as the bits of a number. -/
def bitsOf {α : Type} (f : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: l => bitsOf f l ||| 2 ^ f a

theorem bitsOf_spec {α : Type} {f : α → ℕ} {l : List α} {k : ℕ}
    (h : (bitsOf f l).testBit k = true) : ∃ a ∈ l, f a = k := by
  induction l with
  | nil => simp [bitsOf] at h
  | cons a l ih =>
    rw [bitsOf, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, decide_eq_true_eq] at h
    rcases h with h | h
    · obtain ⟨b, hb, rfl⟩ := ih h
      exact ⟨b, List.mem_cons_of_mem a hb, rfl⟩
    · exact ⟨a, List.mem_cons_self .., h⟩

theorem allAG_bounded : allAG.all boundedAG = true := by decide

/-- The codes of `allAG`. -/
def allAGBits : ℕ := bitsOf agKey allAG

/-- `g ∈ allAG`, by one bit test. -/
def memAG (g : AG) : Bool := boundedAG g && allAGBits.testBit (agKey g)

theorem memAG_spec {g : AG} (h : memAG g = true) : g ∈ allAG := by
  simp only [memAG, Bool.and_eq_true] at h
  obtain ⟨g', hg', hk⟩ := bitsOf_spec h.2
  rw [← agKey_inj (List.all_eq_true.1 allAG_bounded g' hg') h.1 hk]
  exact hg'

/-- The code of a certificate's pair `(g, j)`. -/
def AdjCert.key (c : AdjCert) : ℕ := 8 * agKey c.g + c.j

/-- The certificate of `(g, j)` is in `cs`, given that `cs` has bounded
generators and transpositions, and `g`, `j` are bounded. -/
theorem AdjCert.of_bit {cs : List AdjCert} (hb : (cs.all fun c => boundedAG c.g && Nat.blt c.j 8) = true)
    {g : AG} (hg : boundedAG g = true) {j : ℕ} (hj : j < 8)
    (h : (bitsOf AdjCert.key cs).testBit (8 * agKey g + j) = true) :
    ∃ c ∈ cs, c.j = j ∧ c.g = g := by
  obtain ⟨c, hc, hk⟩ := bitsOf_spec h
  have hcb := List.all_eq_true.1 hb c hc
  simp only [Bool.and_eq_true, Nat.blt_eq] at hcb
  simp only [AdjCert.key] at hk
  have h1 : c.j = j ∧ agKey c.g = agKey g := by omega
  exact ⟨c, hc, h1.1, agKey_inj hcb.1 hg h1.2⟩

end QCert.ToffoliHadamard.Macro
