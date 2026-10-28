/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Appendix E.4: Lemma 8.6, hence Lemma 8.7

`D(E(C)) = C` for every circuit `C`: both sides are monoid homomorphisms, so
it suffices for each gate (`lemma87_of`), the encoding of a gate being that
of its letter (`encAt_genL`).  For `Z` and `CZ` the encoding is a product
over the colourings of the other wires of letters `(-1)_[G⁻¹(x0y)](-1)_[G⁻¹(x1y)]`,
which Lemma 8.4 decodes to boxes; they merge by (309) into the box
controlled by the gate's wires alone (`mergeListP`), which is the gate.
-/
import QCert.RealCliffordCH.Sec8.E.Step84
import QCert.RealCliffordCH.Sec8.E.Merge

namespace QCert.RealCliffordCH.Sec8.E

open Circuit Net Eng

/-! ## The encoding of a gate is that of its letter -/

/-- The encoding of a letter (Definition 8.2); the swap is not a gate. -/
def encL (n : ℕ) : L → List (PG (2 ^ n))
  | .H j => enc1 n .H (n - 1 - j) j
  | .Z j => enc1 n .Z (n - 1 - j) j
  | .C j => enc2 n .CZ (n - 2 - j) j
  | .K j => enc2 n .CH (n - 2 - j) j
  | .S _ => []

/-- A letter `lo` wires up. -/
def addL (lo : ℕ) : L → L
  | .H j => .H (j + lo) | .Z j => .Z (j + lo) | .C j => .C (j + lo) | .K j => .K (j + lo)
  | .S j => .S (j + lo)

theorem addL_upL (lo : ℕ) (x : L) : addL lo (upL x) = addL (lo + 1) x := by
  cases x <;> simp [addL, upL] <;> omega

theorem encAt_genL (n : ℕ) : ∀ {m : ℕ} (g : Gen Gate m) (lo : ℕ),
    encAt n lo g = encL n (addL lo (genL g))
  | _, .gate0 c, _ => nomatch c
  | _, .gate3 c, _ => nomatch c
  | _, .gate1 .H, lo => by simp [encAt, genL, addL, encL]
  | _, .gate1 .Z, lo => by simp [encAt, genL, addL, encL]
  | _, .gate2 .CZ, lo => by simp [encAt, genL, addL, encL]
  | _, .gate2 .CH, lo => by simp [encAt, genL, addL, encL]
  | _, .up g, lo => by
    simp only [encAt, genL]
    rw [encAt_genL n g (lo + 1), addL_upL]

theorem addL_zero (x : L) : addL 0 x = x := by cases x <;> rfl

/-- Lemma 8.7 from its gate cases: if the decoding of the encoding of every
gate letter is that letter, it holds for every circuit. -/
theorem lemma87_of {n : ℕ}
    (hl : ∀ x : L, x.lo + x.wd ≤ n → (∀ j, x ≠ .S j) →
      Derivable (theory n) (decW n (wordOf (encL n x))) (x.circ n)) :
    ∀ w : Circ n, Derivable (theory n) (decW n (encW n w)) w := by
  intro w
  induction w using FreeMonoid.inductionOn' with
  | one => rw [map_one, map_one]
  | mul_of g w ih =>
    rw [map_mul, map_mul]
    refine dmul ?_ ih
    have e : encW n (FreeMonoid.of g) = wordOf (encL n (genL g)) := by
      rw [show encW n (FreeMonoid.of g) = wordOf (encAt n 0 g) from FreeMonoid.lift_eval_of _ _,
        encAt_genL, addL_zero]
    rw [e, ← genL_circ g]
    exact hl (genL g) (by rw [genL_fit]; exact gHi_le g) (genL_notS g)

/-! ## Merging in the order of a word -/

theorem prod_map_congr {N : ℕ} {α : Type*} (l : List α) {f g : α → Circ N}
    (h : ∀ a ∈ l, Derivable (theory N) (f a) (g a)) :
    Derivable (theory N) (l.map f).prod (l.map g).prod := by
  induction l with
  | nil => exact Derivable.refl _
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons]
    exact dmul (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

theorem prod_flatMap' {N : ℕ} {α : Type*} (l : List α) (f : α → List (Circ N)) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.prod_append, ih, List.map_cons, List.prod_cons]

theorem prod_pairs {N : ℕ} (K : ℕ) (F : ℕ → Circ N) (G : ℕ → Circ N)
    (h : ∀ i < K, Derivable (theory N) (F (2 * i) * F (2 * i + 1)) (G i)) :
    Derivable (theory N) ((List.range (2 * K)).map F).prod ((List.range K).map G).prod := by
  rw [range_double, prod_flatMap']
  apply prod_map_congr
  intro i hi
  simpa using h i (List.mem_range.1 hi)

/-- The boxes on wire `t` over every colouring of the wires `ws`, as a product
in the order of the colourings, merge into the box with the wires `ws` idle. -/
theorem mergeListP {M : ℕ} (ih : IH (M + 3)) {t : ℕ} (ht : t < M + 3) :
    ∀ (ws : List ℕ) (base : ℕ → Option Bool), ws.Nodup → t ∉ ws → (∀ w ∈ ws, w < M + 3) →
      base t = none →
      Derivable (theory (M + 3))
        ((List.range (2 ^ ws.length)).map fun i => mc (M + 3) .box [t] (bitsOn ws i base)).prod
        (mc (M + 3) .box [t] (idleOn ws base))
  | [], base, _, _, _, _ => by
    simp only [List.length_nil, pow_zero, List.range_one, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, bitsOn, idleOn]
    exact Derivable.refl _
  | w :: ws, base, hnd, htw, hws, hb => by
    have hnd' := List.nodup_cons.1 hnd
    have hwt : w ≠ t := fun e => htw (by simp [e])
    have ih' := mergeListP ih ht ws (setCtl base w none) hnd'.2 (fun h => htw (by simp [h]))
      (fun x hx => hws x (by simp [hx])) (by simp [setCtl, Ne.symm hwt, hb])
    refine Derivable.trans ?_ ih'
    rw [List.length_cons, pow_succ, mul_comm]
    apply prod_pairs
    intro i _
    have e0 : bitsOn (w :: ws) (2 * i) base = setCtl (bitsOn ws i base) w (some false) := by
      simp only [bitsOn]; congr 2 <;> simp
    have e1 : bitsOn (w :: ws) (2 * i + 1) base = setCtl (bitsOn ws i base) w (some true) := by
      simp only [bitsOn]; congr 2 <;> simp [Nat.mul_add_div]
    rw [e0, e1, ← setCtl_bitsOn ws i base w none hnd'.1]
    have hct : bitsOn ws i base t = none := by
      rw [bitsOn_of_not_mem ws i base t (fun h => htw (by simp [h]))]; exact hb
    have := mergeAt ih ht (bitsOn ws i base) hct hwt (hws w (by simp)) true
    rwa [drawn_two] at this

end QCert.RealCliffordCH.Sec8.E
