/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Li, Ross, Selinger (2021): generators and relations

S. M. Li, N. J. Ross, P. Selinger, *Generators and relations for the group
O_n(ℤ[1/2])*, QPL 2021 (arXiv:2106.01175).

The generators `𝒢ₙ` of Definition 2.6 are the one-, two- and four-level
matrices `(−1)_[a]`, `X_[a,b]` and `K_[a,b,c,d]` with `a < b < c < d`, and
the relations are those of Table 1, numbered as printed: (1a)–(1c),
(2a)–(2f), (3a)–(3g), (4a)–(4c), (5a), (6a).  For the scaled dyadic group
`Lₙ` (Section 5) the generator `I ⊗ H` is added with the relations of
Table 2, (7a)–(7d).

**Indices start at `0`**, where the paper's start at `1`: the paper's
`X_[a,b]` is `X (a-1) (b-1)` here.  The caption of Table 1 asks that "the
indices are distinct and that the relations are well-formed": every
generator is in `𝒢ₙ` (its indices increase), and the indices of a relation
are pairwise distinct.  So the renaming relation (3a)
`X_[a,a'] X_[a,b] ≈ X_[a',b] X_[a,a']` is stated for `a < a' < b`, and so
on.

**Misprint in Table 2.**  As printed, (7d) reads (1-based `a`)
`(I⊗H) X_[a,a+1] (I⊗H) ≈ (−1)_[a+1]^{a+1} X_[a,a+1]^a K_[a−1,a,a+1,a+2]^a`,
with the exponents of the two cases exchanged: for odd `a` (a pair
`a, a+1` inside one block of `I ⊗ H`) the left-hand side is `(−1)_[a+1]`,
and for even `a` it is `X_[a,a+1] K_[a−1,a,a+1,a+2]` (for `a = 1` the
printed right-hand side is not even well-formed).  It is used corrected,
as the two families `r7d_even` and `r7d_odd` (0-based: even `a` is the
paper's odd `a`).
-/
import QCert.Presentation

namespace QCert.LiRossSelinger

/-- The generators `𝒢ₙ` of Definition 2.6 (indices from `0`). -/
inductive Gen (n : ℕ) : Type
  /-- `(−1)_[a]`, the one-level matrix of type `−1`. -/
  | neg (a : Fin n)
  /-- `X_[a,b]`, `a < b`, the two-level matrix of type `X`. -/
  | x (a b : Fin n) (hab : a < b)
  /-- `K_[a,b,c,d]`, `a < b < c < d`, the four-level matrix of type `K`. -/
  | k (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)

variable {n : ℕ}

/-- `(−1)_[a]` as a word. -/
abbrev N (a : Fin n) : Word (Gen n) := FreeMonoid.of (Gen.neg a)

/-- `X_[a,b]` as a word. -/
abbrev X (a b : Fin n) (hab : a < b) : Word (Gen n) := FreeMonoid.of (Gen.x a b hab)

/-- `K_[a,b,c,d]` as a word. -/
abbrev K (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) : Word (Gen n) :=
  FreeMonoid.of (Gen.k a b c d hab hbc hcd)

/-- The relations of Table 1 (indices from `0`; all indices of a relation
are distinct and every generator is well-formed). -/
inductive Table1 (n : ℕ) : WRel (Gen n)
  /-- (1a) `X_[a,b]² ≈ ε`. -/
  | r1a (a b : Fin n) (hab : a < b) : Table1 n (X a b hab * X a b hab) 1
  /-- (1b) `(−1)_[a]² ≈ ε`. -/
  | r1b (a : Fin n) : Table1 n (N a * N a) 1
  /-- (1c) `K_[a,b,c,d]² ≈ ε`. -/
  | r1c (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) :
      Table1 n (K a b c d hab hbc hcd * K a b c d hab hbc hcd) 1
  /-- (2a) `X_[a,b] X_[c,d] ≈ X_[c,d] X_[a,b]`. -/
  | r2a (a b c d : Fin n) (hab : a < b) (hcd : c < d) (h : [a, b, c, d].Nodup) :
      Table1 n (X a b hab * X c d hcd) (X c d hcd * X a b hab)
  /-- (2b) `X_[a,b] (−1)_[c] ≈ (−1)_[c] X_[a,b]`. -/
  | r2b (a b c : Fin n) (hab : a < b) (h : [a, b, c].Nodup) :
      Table1 n (X a b hab * N c) (N c * X a b hab)
  /-- (2c) `X_[a,b] K_[c,d,e,f] ≈ K_[c,d,e,f] X_[a,b]`. -/
  | r2c (a b c d e f : Fin n) (hab : a < b) (hcd : c < d) (hde : d < e) (hef : e < f)
      (h : [a, b, c, d, e, f].Nodup) :
      Table1 n (X a b hab * K c d e f hcd hde hef) (K c d e f hcd hde hef * X a b hab)
  /-- (2d) `(−1)_[a] (−1)_[b] ≈ (−1)_[b] (−1)_[a]`. -/
  | r2d (a b : Fin n) (h : a ≠ b) : Table1 n (N a * N b) (N b * N a)
  /-- (2e) `(−1)_[a] K_[b,c,d,e] ≈ K_[b,c,d,e] (−1)_[a]`. -/
  | r2e (a b c d e : Fin n) (hbc : b < c) (hcd : c < d) (hde : d < e)
      (h : [a, b, c, d, e].Nodup) :
      Table1 n (N a * K b c d e hbc hcd hde) (K b c d e hbc hcd hde * N a)
  /-- (2f) `K_[a,b,c,d] K_[e,f,g,h] ≈ K_[e,f,g,h] K_[a,b,c,d]`. -/
  | r2f (a b c d e f g h : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d)
      (hef : e < f) (hfg : f < g) (hgh : g < h) (hd : [a, b, c, d, e, f, g, h].Nodup) :
      Table1 n (K a b c d hab hbc hcd * K e f g h hef hfg hgh)
        (K e f g h hef hfg hgh * K a b c d hab hbc hcd)
  /-- (3a) `X_[a,a'] X_[a,b] ≈ X_[a',b] X_[a,a']`, `a < a' < b`. -/
  | r3a (a a' b : Fin n) (h₁ : a < a') (h₂ : a' < b) :
      Table1 n (X a a' h₁ * X a b (h₁.trans h₂)) (X a' b h₂ * X a a' h₁)
  /-- (3b) `X_[b,b'] X_[a,b] ≈ X_[a,b'] X_[b,b']`, `a < b < b'`. -/
  | r3b (a b b' : Fin n) (h₁ : a < b) (h₂ : b < b') :
      Table1 n (X b b' h₂ * X a b h₁) (X a b' (h₁.trans h₂) * X b b' h₂)
  /-- (3c) `X_[a,b] (−1)_[b] ≈ (−1)_[a] X_[a,b]`. -/
  | r3c (a b : Fin n) (hab : a < b) : Table1 n (X a b hab * N b) (N a * X a b hab)
  /-- (3d) `X_[a,a'] K_[a,b,c,d] ≈ K_[a',b,c,d] X_[a,a']`, `a < a' < b`. -/
  | r3d (a a' b c d : Fin n) (h₁ : a < a') (h₂ : a' < b) (hbc : b < c) (hcd : c < d) :
      Table1 n (X a a' h₁ * K a b c d (h₁.trans h₂) hbc hcd) (K a' b c d h₂ hbc hcd * X a a' h₁)
  /-- (3e) `X_[b,b'] K_[a,b,c,d] ≈ K_[a,b',c,d] X_[b,b']`, `b < b' < c`. -/
  | r3e (a b b' c d : Fin n) (hab : a < b) (h₁ : b < b') (h₂ : b' < c) (hcd : c < d) :
      Table1 n (X b b' h₁ * K a b c d hab (h₁.trans h₂) hcd)
        (K a b' c d (hab.trans h₁) h₂ hcd * X b b' h₁)
  /-- (3f) `X_[c,c'] K_[a,b,c,d] ≈ K_[a,b,c',d] X_[c,c']`, `c < c' < d`. -/
  | r3f (a b c c' d : Fin n) (hab : a < b) (hbc : b < c) (h₁ : c < c') (h₂ : c' < d) :
      Table1 n (X c c' h₁ * K a b c d hab hbc (h₁.trans h₂))
        (K a b c' d hab (hbc.trans h₁) h₂ * X c c' h₁)
  /-- (3g) `X_[d,d'] K_[a,b,c,d] ≈ K_[a,b,c,d'] X_[d,d']`, `d < d'`. -/
  | r3g (a b c d d' : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) (h₁ : d < d') :
      Table1 n (X d d' h₁ * K a b c d hab hbc hcd) (K a b c d' hab hbc (hcd.trans h₁) * X d d' h₁)
  /-- (4a) `X_[a,b] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,d] (−1)_[b] (−1)_[d]`. -/
  | r4a (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) :
      Table1 n (X a b hab * K a b c d hab hbc hcd)
        (K a b c d hab hbc hcd * X b d (hbc.trans hcd) * N b * N d)
  /-- (4b) `X_[b,c] K_[a,b,c,d] ≈ (−1)_[a] K_[a,b,c,d] (−1)_[a] K_[a,b,c,d] (−1)_[a]`. -/
  | r4b (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) :
      Table1 n (X b c hbc * K a b c d hab hbc hcd)
        (N a * K a b c d hab hbc hcd * N a * K a b c d hab hbc hcd * N a)
  /-- (4c) `X_[c,d] K_[a,b,c,d] ≈ K_[a,b,c,d] X_[b,d]`. -/
  | r4c (a b c d : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) :
      Table1 n (X c d hcd * K a b c d hab hbc hcd) (K a b c d hab hbc hcd * X b d (hbc.trans hcd))
  /-- (5a) `K_[a,b,c,d] K_[b,d,e,f] ≈ K_[c,d,e,f] K_[a,b,c,e]`, `a < b < c < d < e < f`. -/
  | r5a (a b c d e f : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
      (hef : e < f) :
      Table1 n (K a b c d hab hbc hcd * K b d e f (hbc.trans hcd) hde hef)
        (K c d e f hcd hde hef * K a b c e hab hbc (hcd.trans hde))
  /-- (6a), `a < b < c < d < e < f < g < h`:
  `(−1)_[a] (−1)_[e] X_[a,e] K_[e,f,g,h] K_[a,b,c,d] X_[d,e] K_[a,b,c,d] K_[e,f,g,h] X_[a,e] (−1)_[a] (−1)_[e]
    ≈ K_[e,f,g,h] K_[a,b,c,d] X_[d,e] K_[a,b,c,d] K_[e,f,g,h]`. -/
  | r6a (a b c d e f g h : Fin n) (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e)
      (hef : e < f) (hfg : f < g) (hgh : g < h) :
      Table1 n
        (N a * N e * X a e (hab.trans (hbc.trans (hcd.trans hde))) *
          K e f g h hef hfg hgh * K a b c d hab hbc hcd * X d e hde * K a b c d hab hbc hcd *
          K e f g h hef hfg hgh * X a e (hab.trans (hbc.trans (hcd.trans hde))) * N a * N e)
        (K e f g h hef hfg hgh * K a b c d hab hbc hcd * X d e hde * K a b c d hab hbc hcd *
          K e f g h hef hfg hgh)

/-! ## The scaled dyadic group `Lₙ` (Section 5)

`I ⊗ H` needs an even dimension; the dimension is written `m * 2`, the
`m` blocks of `I_{n/2} ⊗ H` being the pairs of indices `2i, 2i + 1`
(the paper's `2i + 1, 2i + 2`). -/

/-- The generators `𝓕ₙ` of Definition 5.2: `𝒢ₙ` and `I ⊗ H`. -/
inductive GenL (m : ℕ) : Type
  /-- A generator of `𝒢ₙ`. -/
  | base (g : Gen (m * 2))
  /-- `I_{n/2} ⊗ H`. -/
  | ih

/-- `I ⊗ H` as a word. -/
abbrev IH {m : ℕ} : Word (GenL m) := FreeMonoid.of GenL.ih

/-- A word over `𝒢ₙ` as a word over `𝓕ₙ`. -/
abbrev toL {m : ℕ} : Word (Gen (m * 2)) →* Word (GenL m) := FreeMonoid.map GenL.base

/-- The relations of Tables 1 and 2 for `𝓕ₙ`, `n = m * 2` (indices from
`0`; (7d) corrected, see the module docstring). -/
inductive Table12 (m : ℕ) : WRel (GenL m)
  /-- A relation of Table 1. -/
  | table1 {w v : Word (Gen (m * 2))} (r : Table1 (m * 2) w v) : Table12 m (toL w) (toL v)
  /-- (7a) `(I ⊗ H)² ≈ ε`. -/
  | r7a : Table12 m (IH * IH) 1
  /-- (7b) `(I ⊗ H) K_[1,2,3,4] (I ⊗ H) ≈ K_[1,2,3,4]` (`K_[0,1,2,3]` from `0`). -/
  | r7b (h : 3 < m * 2) :
      Table12 m (IH * toL (K ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, h⟩
          (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) (by simp [Fin.lt_def])) * IH)
        (toL (K ⟨0, by omega⟩ ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, h⟩
          (by simp [Fin.lt_def]) (by simp [Fin.lt_def]) (by simp [Fin.lt_def])))
  /-- (7c) `(I ⊗ H) (−1)_[1] (I ⊗ H) ≈ (−1)_[1] X_[1,2] (−1)_[1]` (`(−1)_[0]`,
  `X_[0,1]` from `0`). -/
  | r7c (h : 1 < m * 2) :
      Table12 m (IH * toL (N ⟨0, by omega⟩) * IH)
        (toL (N ⟨0, by omega⟩ * X ⟨0, by omega⟩ ⟨1, h⟩ (by simp [Fin.lt_def]) *
          N ⟨0, by omega⟩))
  /-- (7d) for a pair `a, a + 1` inside one block (`a` even from `0`, the
  paper's odd `a`), corrected: `(I ⊗ H) X_[a,a+1] (I ⊗ H) ≈ (−1)_[a+1]`. -/
  | r7d_even (a : ℕ) (ha : a % 2 = 0) (h : a + 1 < m * 2) :
      Table12 m (IH * toL (X ⟨a, by omega⟩ ⟨a + 1, h⟩ (by simp [Fin.lt_def])) * IH)
        (toL (N ⟨a + 1, h⟩))
  /-- (7d) for a pair `a, a + 1` across two blocks (`a` odd from `0`, the
  paper's even `a`), corrected:
  `(I ⊗ H) X_[a,a+1] (I ⊗ H) ≈ X_[a,a+1] K_[a−1,a,a+1,a+2]`. -/
  | r7d_odd (a : ℕ) (ha : a % 2 = 1) (h : a + 2 < m * 2) :
      Table12 m (IH * toL (X ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (by simp [Fin.lt_def])) * IH)
        (toL (X ⟨a, by omega⟩ ⟨a + 1, by omega⟩ (by simp [Fin.lt_def]) *
          K ⟨a - 1, by omega⟩ ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨a + 2, h⟩
            (by simp [Fin.lt_def]; omega) (by simp [Fin.lt_def]) (by simp [Fin.lt_def])))

end QCert.LiRossSelinger
