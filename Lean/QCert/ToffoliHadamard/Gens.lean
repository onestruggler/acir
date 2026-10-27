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
    (h : checkFlat E (cs.map AdjCert.entry) = true) {c : AdjCert} (hc : c ∈ cs) :
    Derivable MRel (FreeMonoid.ofList c.entry.lhs) (FreeMonoid.ofList c.entry.rhs) :=
  checkFlat_valid hE h (c.entry.lhs, c.entry.rhs) (by
    simp only [Engine.eqns, List.map_map]
    exact List.mem_map_of_mem (f := (fun t : Entry ML => (t.lhs, t.rhs)) ∘ AdjCert.entry) hc)

/-- `p a` for every `a < n`. -/
def allBelow (n : ℕ) (p : ℕ → Bool) : Bool := (List.range n).all p

theorem allBelow_spec {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) {a : ℕ} (ha : a < n) :
    p a = true :=
  List.all_eq_true.1 h a (List.mem_range.2 ha)

theorem imp_spec {p : Prop} [Decidable p] {b : Bool} (h : (!decide p || b) = true) (hp : p) :
    b = true := by
  simpa [hp] using h

end QCert.ToffoliHadamard.Macro
