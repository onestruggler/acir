/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Toward hypothesis (b): the frame `Φ` and the images of Figure 6's relations

For three fresh indices `e, f, g` (`Tags`), `Φ` (`phiG`, `phiW`) writes a
generator of `𝒢_N` as a word over `𝒫_N` with the same action on the other
indices: `(-1)_[a] ↦ (-1)_[a](-1)_[g]`, `X_[a,b] ↦ (-1)_[g]X_[a,b]`,
`H_[a,b] ↦ H_[a,b]H_[e,f]` (the tags make the parities even).  Each relation
(a1)–(d2) of Hadamard-Π's Figure 6 whose indices avoid the tags has its two
images equal by Figure 8 (`img_a1`, …, `img_d2`), by Corollary A.5 for the
Hadamard-free ones, conjugation (`conj_hh`) for the mixed ones and
Equations (66), (71) for (b6).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBTools
import QCert.RealCliffordCH.Sec8.A.RS

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-- The generators of Hadamard-Π. -/
abbrev HG (N : ℕ) := HadamardPi.Gen N

/-- The image of a generator. -/
def phiG (n e f g : ℕ) : HG (2 ^ n) → List (PG (2 ^ n))
  | .Z a => [Zz n a g]
  | .X a b _ => [Zx n g a b]
  | .H a b _ => [Hh n a b e f]

/-- The image of a word. -/
def phiW (n e f g : ℕ) (w : Word (HG (2 ^ n))) : List (PG (2 ^ n)) :=
  w.toList.flatMap (phiG n e f g)

theorem phiW_mul (e f g : ℕ) (w v : Word (HG (2 ^ n))) :
    phiW n e f g (w * v) = phiW n e f g w ++ phiW n e f g v := by
  simp [phiW, FreeMonoid.toList_mul]

theorem phiW_of (e f g : ℕ) (y : HG (2 ^ n)) :
    phiW n e f g (FreeMonoid.of y) = phiG n e f g y := by
  simp [phiW, FreeMonoid.toList_of]

theorem phiW_one (e f g : ℕ) : phiW n e f g 1 = [] := rfl

/-- The tags: three distinct indices. -/
structure Tags (n e f g : ℕ) : Prop where
  he : e < 2 ^ n
  hf : f < 2 ^ n
  hg : g < 2 ^ n
  hef : e ≠ f
  heg : e ≠ g
  hfg : f ≠ g

/-- An index below `2ⁿ` away from the tags. -/
def Av (n e f g x : ℕ) : Prop := x < 2 ^ n ∧ x ≠ e ∧ x ≠ f ∧ x ≠ g

/-! ## Helpers -/

/-- `H_[x,y]H_[e,f] · H_[z,w]H_[e,f] ≈ H_[x,y]H_[z,w]`. -/
theorem contract (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {x y z w e f : ℕ} (hx : x < 2 ^ n)
    (hy : y < 2 ^ n) (hz : z < 2 ^ n) (hw : w < 2 ^ n) (he : e < 2 ^ n) (hf : f < 2 ^ n)
    (hxy : x ≠ y) (hd : Distinct4 z w e f) :
    D8 n [Hh n x y e f, Hh n z w e f] [Hh n x y z w] :=
  (DR.left [Hh n x y e f] (e66 h8 hE hz hw he hf hd)).trans
    (e71 h8 hE hx hy he hf hz hw hxy hd.2.2.2.2.2 hd.1)

/-- From a conjugation to a commutation. -/
theorem push_of_conj {Pm P'm R : List (PG (2 ^ n))} {x : PG (2 ^ n)}
    (hc : D8 n (Pm ++ x :: P'm) R) (hcan : D8 n (P'm ++ Pm) []) :
    D8 n (Pm ++ [x]) (R ++ Pm) := by
  have k := DR.ctx (Pm ++ [x]) [] hcan
  exact (DR.rfl' (by simp)).trans (k.symm.trans ((DR.rfl' (by simp)).trans (DR.right Pm hc)))

theorem bd1 {u : ℕ} (hu : u < 2 ^ n) {x : NL} (hx : x ∈ [NL.zz u u]) : x.Bd n := by
  simp only [List.mem_singleton] at hx; subst hx; exact ⟨hu, hu⟩

end QCert.RealCliffordCH.Sec8
