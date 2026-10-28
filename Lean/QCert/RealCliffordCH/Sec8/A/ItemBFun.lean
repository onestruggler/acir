/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Toward hypothesis (b): `Φ` carries derivations of Figure 6 to Figure 8

`fig6_img`: every relation of Figure 6 whose indices satisfy a predicate `R`
that keeps them away from the tags has its two images under `Φ` equal by
Figure 8, given that (d3) and (d4) do at such indices.  `phi_functor`: a
derivation of Figure 6 on `m` indices, moved to increasing indices away from
the tags, gives a derivation of Figure 8 between the images.  On at most
three indices there is no instance of (d3) or (d4), so `phi_functor3` needs
no hypothesis; with completeness of Figure 6 (`QCert.HadamardPi.theorem_4_14`)
an identity of matrices on at most three indices becomes an equation of
Figure 8 between images (`phi_of_check3`).
-/
import QCert.RealCliffordCH.Sec8.A.ItemBPhi
import QCert.HadamardPi.Soundness
import QCert.HadamardPi.Embed

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

open HadamardPi (Fig6)

/-- The indices of a generator. -/
def gidx {N : ℕ} : HG N → List ℕ
  | .Z a => [a]
  | .X a b _ => [a, b]
  | .H a b _ => [a, b]

/-- A word whose indices satisfy `R`. -/
def WR {N : ℕ} (R : ℕ → Prop) (w : Word (HG N)) : Prop := ∀ y ∈ w.toList, ∀ i ∈ gidx y, R i

/-- (d3) at given indices, as its images. -/
def D3img (n e f g : ℕ) (R : ℕ → Prop) : Prop :=
  ∀ (a b c d : Fin (2 ^ n)) (hab : a < b) (hcd : c < d) (hac : a < c) (hbd : b < d), b ≠ c →
    R a → R b → R c → R d →
    D8 n (phiW n e f g ((FreeMonoid.of (HadamardPi.Gen.H c d hcd) * FreeMonoid.of (HadamardPi.Gen.H a c hac) *
        FreeMonoid.of (HadamardPi.Gen.H b d hbd)) ^ 4))
      (phiW n e f g (FreeMonoid.of (HadamardPi.Gen.H a b hab) * FreeMonoid.of (HadamardPi.Gen.H c d hcd)))

/-- (d4) at given indices, as its images. -/
def D4img (n e f g : ℕ) (R : ℕ → Prop) : Prop :=
  ∀ (a b c d e' f' : Fin (2 ^ n)) (hac : a < c) (hbd : b < d) (hab : a < b) (hce : c < e')
    (hdf : d < f') (hef : e' < f'), b ≠ c → b ≠ e' → c ≠ d → d ≠ e' →
    R a → R b → R c → R d → R e' → R f' →
    D8 n (phiW n e f g ((FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd) *
        FreeMonoid.of (HadamardPi.Gen.H a b hab) * FreeMonoid.of (HadamardPi.Gen.H a c hac) *
        FreeMonoid.of (HadamardPi.Gen.H b d hbd) * FreeMonoid.of (HadamardPi.Gen.X c e' hce) *
        FreeMonoid.of (HadamardPi.Gen.X d f' hdf)) ^ 3))
      (phiW n e f g (FreeMonoid.of (HadamardPi.Gen.H c e' hce) * FreeMonoid.of (HadamardPi.Gen.H d f' hdf) *
        FreeMonoid.of (HadamardPi.Gen.H e' f' hef) * FreeMonoid.of (HadamardPi.Gen.H c e' hce) *
        FreeMonoid.of (HadamardPi.Gen.H d f' hdf) * FreeMonoid.of (HadamardPi.Gen.X c e' hce) *
        FreeMonoid.of (HadamardPi.Gen.X d f' hdf)))

theorem fin_ne {N : ℕ} {a b : Fin N} (h : a ≠ b) : (a : ℕ) ≠ b := fun e => h (Fin.ext e)

theorem fin_ne_of_lt {N : ℕ} {a b : Fin N} (h : a < b) : (a : ℕ) ≠ b := fun e => by
  rw [Fin.lt_def] at h; omega

/-- The images of every relation of Figure 6 at indices satisfying `R`. -/
theorem fig6_img (h8 : 8 ≤ 2 ^ n) (hE : E65 n) {e f g : ℕ} (T : Tags n e f g)
    (R : ℕ → Prop) (hR : ∀ x, R x → Av n e f g x) (h3 : D3img n e f g R)
    (h4 : D4img n e f g R) {w w' : Word (HG (2 ^ n))} (h : Fig6 w w') (hw : WR R w) :
    D8 n (phiW n e f g w) (phiW n e f g w') := by
  have A : ∀ (y : HG (2 ^ n)) (i : ℕ), y ∈ w.toList → i ∈ gidx y → Av n e f g i :=
    fun y i hy hi => hR i (hw y hy i hi)
  cases h with
  | a1 a =>
    simpa [phiW, phiG] using img_a1 h8 T (A (.Z a) a (by simp) (by simp [gidx]))
  | @a2 a b hab =>
    simpa [phiW, phiG] using img_a2 h8 T (A (.X a b hab) a (by simp) (by simp [gidx]))
      (A (.X a b hab) b (by simp) (by simp [gidx])) (fin_ne_of_lt hab)
  | @a3 a b hab =>
    simpa [phiW, phiG] using img_a3 h8 T hE (A (.H a b hab) a (by simp) (by simp [gidx]))
      (A (.H a b hab) b (by simp) (by simp [gidx])) (fin_ne_of_lt hab)
  | @b1 a b hab =>
    simpa [phiW, phiG] using img_b1 h8 T (A (.Z a) a (by simp) (by simp [gidx]))
      (A (.Z b) b (by simp) (by simp [gidx])) (fin_ne hab)
  | @b2 a b c hbc hab hac =>
    simpa [phiW, phiG] using img_b2 h8 T (A (.Z a) a (by simp) (by simp [gidx]))
      (A (.X b c hbc) b (by simp) (by simp [gidx])) (A (.X b c hbc) c (by simp) (by simp [gidx]))
      (fin_ne_of_lt hbc) (fin_ne hab) (fin_ne hac)
  | @b3 a b c d hab hcd hac had hbc hbd =>
    simpa [phiW, phiG] using img_b3 h8 T (A (.X a b hab) a (by simp) (by simp [gidx]))
      (A (.X a b hab) b (by simp) (by simp [gidx])) (A (.X c d hcd) c (by simp) (by simp [gidx]))
      (A (.X c d hcd) d (by simp) (by simp [gidx])) (fin_ne_of_lt hab) (fin_ne_of_lt hcd)
      (fin_ne hac) (fin_ne had) (fin_ne hbc) (fin_ne hbd)
  | @b4 a b c hbc hab hac =>
    simpa [phiW, phiG] using img_b4 h8 T hE (A (.Z a) a (by simp) (by simp [gidx]))
      (A (.H b c hbc) b (by simp) (by simp [gidx])) (A (.H b c hbc) c (by simp) (by simp [gidx]))
      (fin_ne_of_lt hbc) (fin_ne hab) (fin_ne hac)
  | @b5 a b c d hab hcd hac had hbc hbd =>
    simpa [phiW, phiG] using img_b5 h8 T hE (A (.X a b hab) a (by simp) (by simp [gidx]))
      (A (.X a b hab) b (by simp) (by simp [gidx])) (A (.H c d hcd) c (by simp) (by simp [gidx]))
      (A (.H c d hcd) d (by simp) (by simp [gidx])) (fin_ne_of_lt hab) (fin_ne_of_lt hcd)
      (fin_ne hac) (fin_ne had) (fin_ne hbc) (fin_ne hbd)
  | @b6 a b c d hab hcd hac had hbc hbd =>
    simpa [phiW, phiG] using img_b6 h8 T hE (A (.H a b hab) a (by simp) (by simp [gidx]))
      (A (.H a b hab) b (by simp) (by simp [gidx])) (A (.H c d hcd) c (by simp) (by simp [gidx]))
      (A (.H c d hcd) d (by simp) (by simp [gidx])) (fin_ne_of_lt hab) (fin_ne_of_lt hcd)
      (fin_ne hac) (fin_ne had) (fin_ne hbc) (fin_ne hbd)
  | @c1 a b hab =>
    simpa [phiW, phiG] using img_c1 h8 T (A (.Z a) a (by simp) (by simp [gidx]))
      (A (.X a b hab) b (by simp) (by simp [gidx])) (fin_ne_of_lt hab)
  | @c2 a b c hab hbc =>
    simpa [phiW, phiG] using img_c2 h8 T (A (.X a b hab) a (by simp) (by simp [gidx]))
      (A (.X a b hab) b (by simp) (by simp [gidx])) (A (.X b c hbc) c (by simp) (by simp [gidx]))
      (fin_ne_of_lt hab) (fin_ne_of_lt hbc) (fin_ne_of_lt (hab.trans hbc))
  | @c3 a b c hab hbc =>
    simpa [phiW, phiG] using img_c3 h8 T (A (.X a c (hab.trans hbc)) a (by simp)
      (by simp [gidx])) (A (.X b c hbc) b (by simp) (by simp [gidx]))
      (A (.X b c hbc) c (by simp) (by simp [gidx]))
      (fin_ne_of_lt hab) (fin_ne_of_lt hbc) (fin_ne_of_lt (hab.trans hbc))
  | @c4 a b c hab hbc =>
    simpa [phiW, phiG] using img_c4 h8 T hE (A (.X a b hab) a (by simp) (by simp [gidx]))
      (A (.X a b hab) b (by simp) (by simp [gidx])) (A (.H b c hbc) c (by simp) (by simp [gidx]))
      (fin_ne_of_lt hab) (fin_ne_of_lt hbc) (fin_ne_of_lt (hab.trans hbc))
  | @c5 a b c hab hbc =>
    simpa [phiW, phiG] using img_c5 h8 T hE (A (.H a c (hab.trans hbc)) a (by simp)
      (by simp [gidx])) (A (.X b c hbc) b (by simp) (by simp [gidx]))
      (A (.X b c hbc) c (by simp) (by simp [gidx]))
      (fin_ne_of_lt hab) (fin_ne_of_lt hbc) (fin_ne_of_lt (hab.trans hbc))
  | @d1 a b hab =>
    simpa [phiW, phiG] using img_d1 h8 T hE (A (.Z a) a (by simp) (by simp [gidx]))
      (A (.Z b) b (by simp) (by simp [gidx])) (fin_ne_of_lt hab)
  | @d2 a b hab =>
    simpa [phiW, phiG] using img_d2 h8 T hE (A (.H a b hab) a (by simp) (by simp [gidx]))
      (A (.Z b) b (by simp) (by simp [gidx])) (fin_ne_of_lt hab)
  | @d3 a b c d hab hcd hac hbd hbc =>
    have m1 : HadamardPi.Gen.H c d hcd ∈ ((FreeMonoid.of (HadamardPi.Gen.H c d hcd) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd)) ^ 4 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    have m2 : HadamardPi.Gen.H a c hac ∈ ((FreeMonoid.of (HadamardPi.Gen.H c d hcd) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd)) ^ 4 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    have m3 : HadamardPi.Gen.H b d hbd ∈ ((FreeMonoid.of (HadamardPi.Gen.H c d hcd) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd)) ^ 4 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    exact h3 a b c d hab hcd hac hbd hbc (hw _ m2 a (by simp [gidx]))
      (hw _ m3 b (by simp [gidx])) (hw _ m1 c (by simp [gidx])) (hw _ m1 d (by simp [gidx]))
  | @d4 a b c d e' f' hac hbd hab hce hdf hef hbc hbe hcd hde =>
    have m1 : HadamardPi.Gen.H a c hac ∈ ((FreeMonoid.of (HadamardPi.Gen.H a c hac) *
        FreeMonoid.of (HadamardPi.Gen.H b d hbd) * FreeMonoid.of (HadamardPi.Gen.H a b hab) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd) *
        FreeMonoid.of (HadamardPi.Gen.X c e' hce) * FreeMonoid.of (HadamardPi.Gen.X d f' hdf)) ^ 3 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    have m2 : HadamardPi.Gen.H b d hbd ∈ ((FreeMonoid.of (HadamardPi.Gen.H a c hac) *
        FreeMonoid.of (HadamardPi.Gen.H b d hbd) * FreeMonoid.of (HadamardPi.Gen.H a b hab) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd) *
        FreeMonoid.of (HadamardPi.Gen.X c e' hce) * FreeMonoid.of (HadamardPi.Gen.X d f' hdf)) ^ 3 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    have m3 : HadamardPi.Gen.X c e' hce ∈ ((FreeMonoid.of (HadamardPi.Gen.H a c hac) *
        FreeMonoid.of (HadamardPi.Gen.H b d hbd) * FreeMonoid.of (HadamardPi.Gen.H a b hab) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd) *
        FreeMonoid.of (HadamardPi.Gen.X c e' hce) * FreeMonoid.of (HadamardPi.Gen.X d f' hdf)) ^ 3 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    have m4 : HadamardPi.Gen.X d f' hdf ∈ ((FreeMonoid.of (HadamardPi.Gen.H a c hac) *
        FreeMonoid.of (HadamardPi.Gen.H b d hbd) * FreeMonoid.of (HadamardPi.Gen.H a b hab) *
        FreeMonoid.of (HadamardPi.Gen.H a c hac) * FreeMonoid.of (HadamardPi.Gen.H b d hbd) *
        FreeMonoid.of (HadamardPi.Gen.X c e' hce) * FreeMonoid.of (HadamardPi.Gen.X d f' hdf)) ^ 3 :
          Word (HG (2 ^ n))).toList := by simp [pow_succ]
    exact h4 a b c d e' f' hac hbd hab hce hdf hef hbc hbe hcd hde
      (hw _ m1 a (by simp [gidx])) (hw _ m2 b (by simp [gidx])) (hw _ m1 c (by simp [gidx]))
      (hw _ m2 d (by simp [gidx])) (hw _ m3 e' (by simp [gidx])) (hw _ m4 f' (by simp [gidx]))

/-! ## The functor -/

section Functor

variable {e f g : ℕ} {m : ℕ} (F : Fin m → Fin (2 ^ n)) (hF : StrictMono F)

/-- `Φ` after moving the indices. -/
def psi (n e f g : ℕ) {m : ℕ} (F : Fin m → Fin (2 ^ n)) (hF : StrictMono F) :
    Word (HG m) →* Word (PG (2 ^ n)) :=
  FreeMonoid.lift fun y => FreeMonoid.ofList (phiG n e f g (HadamardPi.Gen.map F hF y))

theorem psi_eq (u : Word (HG m)) :
    psi n e f g F hF u = FreeMonoid.ofList (phiW n e f g (HadamardPi.wmap F hF u)) := by
  induction u using FreeMonoid.inductionOn' with
  | one => rfl
  | mul_of y u ih =>
    rw [map_mul, ih, map_mul, phiW_mul, FreeMonoid.ofList_append]
    congr 1
    simp [psi, HadamardPi.wmap, phiW_of]

/-- **The functor**: a derivation of Figure 6 on `m` indices, moved to increasing
indices, gives one of Figure 8 between the images, when every relation does. -/
theorem phi_functor
    (himg : ∀ w w' : Word (HG m), Fig6 w w' →
      D8 n (phiW n e f g (HadamardPi.wmap F hF w)) (phiW n e f g (HadamardPi.wmap F hF w')))
    {u v : Word (HG m)} (h : Derivable Fig6 u v) :
    D8 n (phiW n e f g (HadamardPi.wmap F hF u)) (phiW n e f g (HadamardPi.wmap F hF v)) := by
  have hc : conGen (Fig6 (n := m)) ≤ (conGen (Fig8 n)).comap (psi n e f g F hF) (map_mul _) :=
    Con.conGen_le fun x y hxy => by
      show conGen (Fig8 n) (psi n e f g F hF x) (psi n e f g F hF y)
      rw [psi_eq, psi_eq]; exact himg x y hxy
  have := hc h
  show conGen (Fig8 n) _ _
  have e1 := psi_eq (e := e) (f := f) (g := g) F hF u
  have e2 := psi_eq (e := e) (f := f) (g := g) F hF v
  simp only [FreeMonoid.ofList_toList] at e1 e2
  rw [← FreeMonoid.ofList_toList (FreeMonoid.ofList _), FreeMonoid.toList_ofList] at e1 e2
  rw [← e1, ← e2]; exact this

/-- The indices reached by `F`. -/
def inF (x : ℕ) : Prop := ∃ i, (F i : ℕ) = x

theorem wmap_WR (u : Word (HG m)) : WR (inF F) (HadamardPi.wmap F hF u) := by
  intro y hy i hi
  rw [HadamardPi.wmap, FreeMonoid.toList_map, List.mem_map] at hy
  obtain ⟨x, -, rfl⟩ := hy
  cases x with
  | Z a => simp only [HadamardPi.Gen.map, gidx, List.mem_singleton] at hi; exact ⟨a, hi.symm⟩
  | X a b _ =>
    simp only [HadamardPi.Gen.map, gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩
  | H a b _ =>
    simp only [HadamardPi.Gen.map, gidx, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨a, rfl⟩
    · exact ⟨b, rfl⟩

/-- On at most three indices there are no instances of (d3), (d4). -/
theorem d3img_small (hm : m ≤ 3) : D3img n e f g (inF F) := by
  intro a b c d hab hcd hac hbd hbc ⟨ia, ea⟩ ⟨ib, eb⟩ ⟨ic, ec⟩ ⟨id, ed⟩
  exfalso
  have i1 := fun (i j : Fin m) (h : (F i : ℕ) ≠ F j) => fun (e : i = j) => h (by rw [e])
  rw [Fin.lt_def] at hab hcd hac hbd
  have hbc' : (b : ℕ) ≠ c := fun e => hbc (Fin.ext e)
  have d1 := i1 ia ib (by omega); have d2 := i1 ia ic (by omega); have d3 := i1 ia id (by omega)
  have d4 := i1 ib ic (by omega); have d5 := i1 ib id (by omega); have d6 := i1 ic id (by omega)
  simp only [Fin.ext_iff] at d1 d2 d3 d4 d5 d6
  have := ia.2; have := ib.2; have := ic.2; have := id.2
  omega

theorem d4img_small (hm : m ≤ 3) : D4img n e f g (inF F) := by
  intro a b c d e' f' hac hbd hab hce hdf hef hbc hbe hcd hde ⟨ia, ea⟩ ⟨ib, eb⟩ ⟨ic, ec⟩ ⟨id, ed⟩
    _ _
  exfalso
  have i1 := fun (i j : Fin m) (h : (F i : ℕ) ≠ F j) => fun (e : i = j) => h (by rw [e])
  rw [Fin.lt_def] at hab hbd hac
  have hbc' : (b : ℕ) ≠ c := fun e => hbc (Fin.ext e)
  have hcd' : (c : ℕ) ≠ d := fun e => hcd (Fin.ext e)
  have d1 := i1 ia ib (by omega); have d2 := i1 ia ic (by omega); have d3 := i1 ia id (by omega)
  have d4 := i1 ib ic (by omega); have d5 := i1 ib id (by omega); have d6 := i1 ic id (by omega)
  simp only [Fin.ext_iff] at d1 d2 d3 d4 d5 d6
  have := ia.2; have := ib.2; have := ic.2; have := id.2
  omega

/-- The functor on at most three indices away from the tags. -/
theorem phi_functor3 (h8 : 8 ≤ 2 ^ n) (hE : E65 n) (T : Tags n e f g) (hm : m ≤ 3)
    (hav : ∀ i, Av n e f g (F i)) {u v : Word (HG m)} (h : Derivable Fig6 u v) :
    D8 n (phiW n e f g (HadamardPi.wmap F hF u)) (phiW n e f g (HadamardPi.wmap F hF v)) := by
  refine phi_functor F hF (fun w w' hw => ?_) h
  exact fig6_img h8 hE T (inF F) (fun x ⟨i, hi⟩ => hi ▸ hav i) (d3img_small F hm)
    (d4img_small F hm) (HadamardPi.fig6_map F hF hw) (wmap_WR F hF w)

end Functor

end QCert.RealCliffordCH.Sec8
