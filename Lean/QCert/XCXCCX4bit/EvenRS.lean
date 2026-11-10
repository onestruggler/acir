/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# The even permutations of `N` states, by Reidemeister–Schreier

Translation of `EvenRS.agda`.  The even permutations `A_N` are the subgroup
of index 2 of `S_N`, and the Reidemeister–Schreier method presents them from
the Coxeter presentation of `S_N` (`Lib/Symmetric`) and the transversal
`{ε, s₀}` (`rep`): coset `false` is `A_N`, coset `true` is `A_N s₀`.  A
letter `s_d` read in coset `c` moves to the other coset and leaves behind
the Schreier generator `γ(c, d)`, which is `s_d s₀` from coset `false` and
`s₀ s_d` from coset `true`, and the empty word for `d = 0` (`γw`).  So the
symbols are `γ c d` for `1 ≤ d ≤ N − 2` (`Sch`), read back as Coxeter words
by `f`; the coset action is `h` and its extension to words `rs`; and the
relations (`RSRel`, the Agda's `_RS,_===_`) are the Coxeter relations of
`S_N` rewritten from either coset, with `γ(c, 0)` written as `ε` and the
instances that become `ε = ε` left out: `order`, `braid₀`, `braid`, `far₀`
and `far`.

The Reidemeister–Schreier theorem (`QCert.reidemeister_schreier`, the Agda's
`Star-Injective-Full`) makes the relations complete for `A_N` given two
obligations: every relation instance of `S_N`, rewritten from either coset,
gives related words and the same coset (`h_wd`), and rewriting `f x` from
coset `false` gives `x` back (`h_f_gen`, the Agda's `h=⁻¹f-gen`).  With the
completeness of `S_N`'s presentation, two words of symbols whose Coxeter
words have the same permutation are related (`rs_complete`).  Conversely
`rs` turns a Coxeter word that ends in coset `false`, an even one, into
symbols whose Coxeter word is the same up to `S_N`'s relations (`rs_approx`,
the Agda's `rs-≈`), so with the same permutation (`rs_sem`).  And the
relations are sound: the two sides of each have equal Coxeter words
(`rs_sound`), so the same permutation (`rs_sound_sem`).

Symbols are `Sch.γ c d p q`, with `d : ℕ` and the bounds `p : 1 ≤ d`,
`q : 2 + d ≤ N` proofs, so that two symbols with the same `c` and `d` are
equal (proof irrelevance) and a client at a numeral `N` matches on
`⟨false, 3, _, _⟩` and the like.  The constructors of `RSRel` carry their
bounds as arguments.

**Deviation from the Agda.**  `S_N`'s relation is `Symmetric.SymRel N`, with
every instance at its absolute index, so `h_wd` is a case split on three
constructors where the Agda recurses on its circuit relation with an offset
(`wd`, `ᵗ-↑`); `h c g` writes `g.1` for the Agda's `tr 0 g`.  The pairs of a
word of symbols and a coset are related by `Sim` (the Agda's `_~_`).
Derivations are equations in the quotient monoid (`cl`) rather than chains
of congruence steps.
-/
import QCert.XCXCCX4bit.Coxeter
import QCert.CliffordT2.ReidemeisterSchreier

namespace QCert.XCXCCX4bit.EvenRS

open QCert.ToffoliHadamardRS
open Symmetric

variable (N : ℕ) {n : ℕ}

/-! ## Letters -/

/-- Letters of the Coxeter presentation of `S_N`. -/
abbrev G := SG N

/-- The letter `s_d` at width `n`: the transposition of the states `d` and
`d + 1`. -/
def letter (n d : ℕ) (q : 2 + d ≤ n) : SG n := ⟨d, q⟩

/-- Its index, read from an offset `o`, is `o + d`. -/
theorem tr_letter (n d : ℕ) (q : 2 + d ≤ n) (o : ℕ) : tr o (letter n d q) = o + d := rfl

theorem tr_suc (o : ℕ) (g : SG n) : tr (o + 1) g = tr o g + 1 := by
  unfold tr; omega

theorem letter_eq {n d d' : ℕ} (q : 2 + d ≤ n) (q' : 2 + d' ≤ n) (e : d = d') :
    letter n d q = letter n d' q' := by
  subst e; rfl

/-- Every letter is the letter of its index. -/
theorem letter_tr (g : SG n) : letter n (tr 0 g) (by have := tr_le 0 g; omega) = g :=
  Subtype.ext (tr_zero g)

/-! ## Schreier symbols -/

/-- `γ false d` stands for `s_d s₀` and `γ true d` for `s₀ s_d`,
`1 ≤ d ≤ N − 2`. -/
structure Sch where
  /-- The symbol `γ c d`. -/
  γ ::
  /-- The coset it is read from. -/
  c : Bool
  /-- The index of its letter. -/
  d : ℕ
  p : 1 ≤ d
  q : 2 + d ≤ N
deriving DecidableEq

/-- A symbol as a Coxeter word. -/
def f : Sch N → Word (G N)
  | ⟨false, d, _, q⟩ => s d q * s 0 (by omega)
  | ⟨true, d, _, q⟩ => s 0 (by omega) * s d q

/-- A symbol as a one-letter word. -/
abbrev y (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ N) : Word (Sch N) :=
  FreeMonoid.of (Sch.γ c d p q)

/-- The Schreier generator `γ(c, d)` as a word: `ε` for `d = 0`. -/
def γw (c : Bool) : (d : ℕ) → 2 + d ≤ N → Word (Sch N)
  | 0, _ => 1
  | d + 1, q => y N c (d + 1) (by omega) q

/-! ## The relations -/

/-- Bounds of the symbols in `far`. -/
theorem far_lo {d e : ℕ} (q : 2 + d ≤ e) (r : 2 + e ≤ N) : 2 + d ≤ N := by omega

theorem far_pos {d e : ℕ} (p : 1 ≤ d) (q : 2 + d ≤ e) : 1 ≤ e := by omega

/-- The Coxeter relations of `S_N` rewritten from the coset `c` (`!c` is the
other one), `γ(c, 0)` written as `ε` and the instances `ε = ε` left out
(the Agda's `_RS,_===_`). -/
inductive RSRel : WRel (Sch N)
  /-- `s_d s_d = ε`, for `1 ≤ d ≤ N − 2`: `γ(c, d) γ(¬c, d) = ε`. -/
  | order (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ N) :
      RSRel (y N c d p q * y N (!c) d p q) 1
  /-- `s₀ s₁ s₀ = s₁ s₀ s₁`, for `N ≥ 3`: `γ(¬c, 1) = γ(c, 1) γ(c, 1)`. -/
  | braid₀ (c : Bool) (q : 3 ≤ N) :
      RSRel (y N (!c) 1 le_rfl q) (y N c 1 le_rfl q * y N c 1 le_rfl q)
  /-- `s_d s_{d+1} s_d = s_{d+1} s_d s_{d+1}`, for `1 ≤ d ≤ N − 3`:
  `γ(c, d) γ(¬c, d + 1) γ(c, d) = γ(c, d + 1) γ(¬c, d) γ(c, d + 1)`. -/
  | braid (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 3 + d ≤ N) :
      RSRel (y N c d p (by omega) * y N (!c) (d + 1) (by omega) (by omega) * y N c d p (by omega))
        (y N c (d + 1) (by omega) (by omega) * y N (!c) d p (by omega) *
          y N c (d + 1) (by omega) (by omega))
  /-- `s₀ s_e = s_e s₀`, for `2 ≤ e ≤ N − 2`: `γ(c, e) = γ(¬c, e)`. -/
  | far₀ (c : Bool) (e : ℕ) (p : 2 ≤ e) (q : 2 + e ≤ N) :
      RSRel (y N c e (by omega) q) (y N (!c) e (by omega) q)
  /-- `s_d s_e = s_e s_d`, for `1 ≤ d`, `d + 2 ≤ e ≤ N − 2`:
  `γ(c, d) γ(¬c, e) = γ(c, e) γ(¬c, d)`. -/
  | far (c : Bool) (d e : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ e) (r : 2 + e ≤ N) :
      RSRel (y N c d p (far_lo N q r) * y N (!c) e (far_pos p q) r)
        (y N c e (far_pos p q) r * y N (!c) d p (far_lo N q r))

/-! ## The coset action -/

/-- The coset action: `s_d` read in coset `c` leaves `γ(c, d)` and moves
to the other coset. -/
def h (c : Bool) (g : G N) : Word (Sch N) × Bool := (γw N c g.1 g.2, !c)

/-- The action extended to words (the Agda's `h ᵗ`). -/
def rs (c : Bool) (w : Word (G N)) : Word (Sch N) × Bool := hstar (h N) c w

theorem rs_one (c : Bool) : rs N c 1 = (1, c) := rfl

theorem rs_of (c : Bool) (g : G N) : rs N c (FreeMonoid.of g) = h N c g := hstar_of _ _ _

theorem rs_mul (c : Bool) (u v : Word (G N)) :
    rs N c (u * v) = ((rs N c u).1 * (rs N (rs N c u).2 v).1, (rs N (rs N c u).2 v).2) :=
  hstar_mul _ _ _ _

/-- Words of symbols with cosets, compared by the relations and by
equality (the Agda's `_~_`). -/
def Sim (x x' : Word (Sch N) × Bool) : Prop := Derivable (RSRel N) x.1 x'.1 ∧ x.2 = x'.2

/-! ## Well-definedness on `S_N`'s relations -/

section WellDefined

variable {N}

private theorem rs_ss (c : Bool) (a b : G N) :
    rs N c (FreeMonoid.of a * FreeMonoid.of b) = (γw N c a.1 a.2 * γw N (!c) b.1 b.2, c) := by
  rw [rs_mul, rs_of, rs_of]; simp [h]

private theorem rs_sss (c : Bool) (a b e : G N) :
    rs N c (FreeMonoid.of a * FreeMonoid.of b * FreeMonoid.of e) =
      (γw N c a.1 a.2 * γw N (!c) b.1 b.2 * γw N c e.1 e.2, !c) := by
  rw [rs_mul, rs_ss, rs_of]; simp [h]

private theorem order_case (c : Bool) (d : ℕ) (q : 2 + d ≤ N) :
    Derivable (RSRel N) (γw N c d q * γw N (!c) d q) 1 := by
  cases d with
  | zero => exact Derivable.refl _
  | succ d => exact Derivable.of (RSRel.order c (d + 1) (by omega) q)

private theorem braid_case (c : Bool) (d : ℕ) (q : 3 + d ≤ N) :
    Derivable (RSRel N) (γw N c d (by omega) * γw N (!c) (d + 1) (by omega) * γw N c d (by omega))
      (γw N c (d + 1) (by omega) * γw N (!c) d (by omega) * γw N c (d + 1) (by omega)) := by
  cases d with
  | zero =>
    have := Derivable.of (RSRel.braid₀ (N := N) c q)
    simp only [γw, one_mul, mul_one]
    exact this
  | succ d => exact Derivable.of (RSRel.braid c (d + 1) (by omega) q)

private theorem far_case (c : Bool) (d e : ℕ) (lo : 2 + d ≤ e) (hi : 2 + e ≤ N) :
    Derivable (RSRel N) (γw N c d (by omega) * γw N (!c) e hi)
      (γw N c e hi * γw N (!c) d (by omega)) := by
  cases d with
  | zero =>
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 2 := ⟨e - 2, by omega⟩
    simp only [γw, one_mul, mul_one]
    exact (Derivable.of (RSRel.far₀ c (e + 2) (by omega) hi)).symm
  | succ d =>
    obtain ⟨e, rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    exact Derivable.of (RSRel.far c (d + 1) (e + 1) (by omega) lo hi)

/-- Every relation instance of `S_N` rewrites, from either coset, to
related words of symbols, ending in the same coset (the Agda's `h-wd`). -/
theorem h_wd (c : Bool) {u t : Word (G N)} (r : SymRel N u t) : Sim N (rs N c u) (rs N c t) := by
  cases r with
  | order d q =>
    rw [rs_ss, rs_one]
    exact ⟨order_case c d q, Bool.not_not c ▸ rfl⟩
  | braid d q =>
    rw [rs_sss, rs_sss]
    exact ⟨by simpa using braid_case c d q, rfl⟩
  | far d e lo q =>
    rw [rs_ss, rs_ss]
    exact ⟨far_case c d e lo q, rfl⟩

/-- Rewriting a symbol's Coxeter word from coset `false` gives the symbol
(the Agda's `h=⁻¹f-gen`). -/
theorem h_f_gen (x : Sch N) : Sim N (FreeMonoid.of x, false) (rs N false (f N x)) := by
  obtain ⟨c, d, p, q⟩ := x
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  cases c with
  | false =>
    rw [f, rs_ss]
    exact ⟨by simp only [γw, mul_one]; exact Derivable.refl _, rfl⟩
  | true =>
    rw [f, rs_ss]
    exact ⟨by simp only [γw, one_mul]; exact Derivable.refl _, rfl⟩

end WellDefined

/-! ## Completeness -/

/-- Two words of symbols whose Coxeter words have the same permutation are
equal by the relations. -/
theorem rs_complete (u v : Word (Sch N))
    (e : ∀ i, perm (FreeMonoid.lift (f N) u) i = perm (FreeMonoid.lift (f N) v) i) :
    Derivable (RSRel N) u v :=
  reidemeister_schreier (h N) false (f N)
    (fun x => ⟨(h_f_gen x).2.symm, (h_f_gen x).1.symm⟩)
    (fun c _ _ r => ⟨(h_wd c r).2, (h_wd c r).1⟩)
    (Symmetric.complete e)

/-! ## From even Coxeter words to symbols -/

/-- `s₀` at width `n` (`ε` below width 2). -/
def s0w : (n : ℕ) → Word (SG n)
  | 0 => 1
  | 1 => 1
  | _ + 2 => FreeMonoid.of ⟨0, by omega⟩

/-- The coset representatives: `ε` for coset `false`, `s₀` for coset
`true`. -/
def rep : Bool → Word (G N)
  | false => 1
  | true => s0w N

section Rep

variable {N}

open CoxeterFrames (cl cl_mul cl_one cl_eq)

theorem s0w_ok (q : 2 ≤ n) : s0w n = s 0 (by omega) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rfl

/-- A letter in the quotient monoid of `S_N`'s relations. -/
abbrev a (d : ℕ) (q : 2 + d ≤ N) : (conGen (SymRel N)).Quotient := cl (SymRel N) (s d q)

theorem a_a (d : ℕ) (q : 2 + d ≤ N) : a d q * a d q = 1 := by
  rw [← cl_mul, ← cl_one]
  exact cl_eq.2 (Derivable.of (SymRel.order d q))

theorem a_a' (d : ℕ) (q : 2 + d ≤ N) (x : (conGen (SymRel N)).Quotient) :
    a d q * (a d q * x) = x := by
  rw [← mul_assoc, a_a, one_mul]

theorem a_braid (d : ℕ) (q : 3 + d ≤ N) (x : (conGen (SymRel N)).Quotient) :
    a d (by omega) * (a (d + 1) (by omega) * (a d (by omega) * x)) =
      a (d + 1) (by omega) * (a d (by omega) * (a (d + 1) (by omega) * x)) := by
  have : a (N := N) d (by omega) * a (d + 1) (by omega) * a d (by omega) =
      a (d + 1) (by omega) * a d (by omega) * a (d + 1) (by omega) := by
    simp only [← cl_mul]
    exact cl_eq.2 (Derivable.of (SymRel.braid d q))
  simp only [← mul_assoc]; rw [this]

theorem a_far (d e : ℕ) (lo : 2 + d ≤ e) (q : 2 + e ≤ N) (x : (conGen (SymRel N)).Quotient) :
    a d (by omega) * (a e q * x) = a e q * (a d (by omega) * x) := by
  have : a d (by omega) * a e q = a e q * a d (by omega) := by
    simp only [← cl_mul]
    exact cl_eq.2 (Derivable.of (SymRel.far d e lo q))
  rw [← mul_assoc, this, mul_assoc]

/-- A symbol's Coxeter word in the quotient. -/
theorem cl_f_false (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ N) :
    cl (SymRel N) (f N ⟨false, d, p, q⟩) = a d q * a 0 (by omega) := cl_mul _ _

theorem cl_f_true (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ N) :
    cl (SymRel N) (f N ⟨true, d, p, q⟩) = a 0 (by omega) * a d q := cl_mul _ _

theorem cl_y (c : Bool) (d : ℕ) (p : 1 ≤ d) (q : 2 + d ≤ N) :
    cl (SymRel N) (FreeMonoid.lift (f N) (y N c d p q)) = cl (SymRel N) (f N ⟨c, d, p, q⟩) := rfl

/-- One letter: `rep c • s_d = f γ(c, d) • rep (not c)`. -/
theorem step (c : Bool) (g : G N) :
    cl (SymRel N) (rep N c * FreeMonoid.of g) =
      cl (SymRel N) (FreeMonoid.lift (f N) (h N c g).1 * rep N (h N c g).2) := by
  obtain ⟨d, q⟩ := g
  have h2 : 2 ≤ N := by omega
  rcases c with _ | _ <;> rcases d with _ | d
  · show cl (SymRel N) (1 * FreeMonoid.of _) = cl (SymRel N) (1 * s0w N)
    rw [s0w_ok h2]
  · show cl (SymRel N) (1 * FreeMonoid.of _) =
      cl (SymRel N) (f N ⟨false, d + 1, by omega, q⟩ * s0w N)
    rw [s0w_ok h2]
    simp only [map_mul, cl_f_false, one_mul, mul_assoc, a_a, mul_one]
  · show cl (SymRel N) (s0w N * FreeMonoid.of _) = cl (SymRel N) (1 * 1)
    rw [s0w_ok h2]
    simp only [map_mul, map_one, mul_one]
    exact a_a 0 q
  · show cl (SymRel N) (s0w N * FreeMonoid.of _) =
      cl (SymRel N) (f N ⟨true, d + 1, by omega, q⟩ * 1)
    rw [s0w_ok h2]
    simp only [map_mul, cl_f_true, mul_one]

/-- Reading a word from coset `c`: `rep c • w` is the Coxeter word of its
symbols followed by the representative of the coset reached (the Agda's
`rs-rep`). -/
theorem rs_rep (c : Bool) (w : Word (G N)) :
    Derivable (SymRel N) (rep N c * w) (FreeMonoid.lift (f N) (rs N c w).1 * rep N (rs N c w).2) := by
  apply cl_eq.1
  induction w using FreeMonoid.inductionOn' generalizing c with
  | one => rw [rs_one, map_one, one_mul, mul_one]
  | mul_of g w ih =>
    rw [rs_mul, rs_of, ← mul_assoc, cl_mul, step, cl_mul, mul_assoc, ← cl_mul, ih]
    simp only [map_mul, mul_assoc]

/-- An even word, read from coset `false`, is the Coxeter word of its
symbols (the Agda's `rs-≈`). -/
theorem rs_approx (w : Word (G N)) (e : (rs N false w).2 = false) :
    Derivable (SymRel N) (FreeMonoid.lift (f N) (rs N false w).1) w := by
  have := rs_rep false w
  rw [e] at this
  simp only [rep, one_mul, mul_one] at this
  exact this.symm

/-- So it has the same permutation (the Agda's `rs-sem`). -/
theorem rs_sem (w : Word (G N)) (e : (rs N false w).2 = false) :
    ∀ i, perm (FreeMonoid.lift (f N) (rs N false w).1) i = perm w i :=
  Symmetric.sound (rs_approx w e)

/-! ## The relations are sound -/

/-- Each relation's two sides have equal Coxeter words (the Agda's
`rs-sound`). -/
theorem rs_sound {u v : Word (Sch N)} (r : RSRel N u v) :
    Derivable (SymRel N) (FreeMonoid.lift (f N) u) (FreeMonoid.lift (f N) v) := by
  apply cl_eq.1
  cases r with
  | order c d p q =>
    cases c <;> simp only [Bool.not_false, Bool.not_true, map_mul, map_one,
      FreeMonoid.lift_eval_of, cl_f_false, cl_f_true, mul_assoc, a_a', a_a]
  | braid₀ c q =>
    cases c <;> simp only [Bool.not_false, Bool.not_true, map_mul, FreeMonoid.lift_eval_of,
      cl_f_false, cl_f_true, mul_assoc]
    · rw [← a_braid 0 q, a_a, mul_one]
    · rw [a_braid 0 q, a_a, mul_one]
  | braid c d p q =>
    cases c <;> simp only [Bool.not_false, Bool.not_true, map_mul, FreeMonoid.lift_eval_of,
      cl_f_false, cl_f_true, mul_assoc, a_a']
    · exact a_braid d q _
    · have := a_braid d q 1; simp only [mul_one] at this; rw [this]
  | far₀ c e p q =>
    cases c <;> simp only [Bool.not_false, Bool.not_true, FreeMonoid.lift_eval_of, cl_f_false,
      cl_f_true]
    · have := a_far 0 e p q 1; simp only [mul_one] at this; exact this.symm
    · have := a_far 0 e p q 1; simp only [mul_one] at this; exact this
  | far c d e p q r =>
    cases c <;> simp only [Bool.not_false, Bool.not_true, map_mul, FreeMonoid.lift_eval_of,
      cl_f_false, cl_f_true, mul_assoc, a_a']
    · have := a_far d e q r 1; simp only [mul_one] at this; exact this
    · rw [a_far d e q r]

/-- So their two sides have the same permutation (the Agda's
`rs-sound-sem`). -/
theorem rs_sound_sem {u v : Word (Sch N)} (r : RSRel N u v) :
    ∀ i, perm (FreeMonoid.lift (f N) u) i = perm (FreeMonoid.lift (f N) v) i :=
  Symmetric.sound (rs_sound r)

end Rep

end QCert.XCXCCX4bit.EvenRS
