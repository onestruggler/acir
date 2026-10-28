/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A rewriting engine for derivations on two and three wires

Toward Theorem 4.4.  A derivation on `k` wires is checked as a run over
letter lists (`Lt`: `H`, `S` on a wire, `CZ` on two adjacent wires), read
in time order (`cw`), up to a phase (`E`, i.e. `PEq`):

* `canon` puts a word in a normal form for commuting adjacent letters on
  disjoint wires (repeatedly the least letter that commutes with every
  letter before it), and `canon_E` says it is equal to the word;
* a `rule` step replaces an occurrence (up to `canon`) of one side of an
  equation of a table by the other side;
* a `free` step replaces a segment lying on the bottom `k - 1` wires, or on
  the top `k - 1` wires, by another one acting alike on the Paulis there:
  with completeness on `k - 1` wires they are derivably equal up to a phase
  (`pcomplete_gens`), and a derivation on `k - 1` wires holds on the bottom
  or top wires of `k` (`PEq.pad`, `PEq.shift`).

`Lib.check` runs a list of lemmas, each derived from the base rules and the
lemmas before it, and `Lib.sound` makes every one of them an equation.
-/
import QCert.QutritClifford.Proj
import QCert.QutritClifford.Run

namespace QCert.QutritClifford

namespace Lt

/-- The generator of a letter on `k` wires (the scalar if it does not fit). -/
def gen : (k : ℕ) → Lt → Gen Gate k
  | _ + 1, H 0 => .gate1 .H
  | _ + 1, S 0 => .gate1 .S
  | _ + 2, C 0 => .gate2 .CZ
  | k + 1, H (j + 1) => .up (gen k (H j))
  | k + 1, S (j + 1) => .up (gen k (S j))
  | k + 1, C (j + 1) => .up (gen k (C j))
  | _, _ => .gate0 .negω

end Lt

/-- A word of letters, in time order, as a circuit on `k` wires. -/
def cw (k : ℕ) : List Lt → Circ k
  | [] => 1
  | x :: l => cw k l * FreeMonoid.of (Lt.gen k x)

theorem cw_append (k : ℕ) (a b : List Lt) : cw k (a ++ b) = cw k b * cw k a := by
  induction a with
  | nil => simp [cw]
  | cons x a ih => simp only [List.cons_append, cw, ih, mul_assoc]

/-- Equality of words up to a phase. -/
def E (k : ℕ) (a b : List Lt) : Prop := PEq k (cw k a) (cw k b)

namespace E

variable {k : ℕ}

@[refl] theorem refl (a : List Lt) : E k a a := PEq.refl _

theorem symm {a b : List Lt} (h : E k a b) : E k b a := PEq.symm h

theorem trans {a b c : List Lt} (h₁ : E k a b) (h₂ : E k b c) : E k a c := PEq.trans h₁ h₂

theorem append {a a' b b' : List Lt} (h₁ : E k a a') (h₂ : E k b b') : E k (a ++ b) (a' ++ b') := by
  unfold E at *; rw [cw_append, cw_append]; exact h₂.mul h₁

theorem append3 {a b b' c : List Lt} (h : E k b b') : E k (a ++ b ++ c) (a ++ b' ++ c) :=
  ((refl a).append h).append (refl c)

theorem of_eq {a b : List Lt} (h : a = b) : E k a b := h ▸ refl a

end E

/-! ### Letters on disjoint wires commute -/

theorem scalar_comm {k : ℕ} (w : Circ k) :
    Der k (w * FreeMonoid.of (Gen.gate0 Gate.negω)) (FreeMonoid.of (Gen.gate0 Gate.negω) * w) :=
  (negω_comm w).symm

abbrev GC (k : ℕ) (x y : Lt) : Prop :=
  Der k (FreeMonoid.of (Lt.gen k y) * FreeMonoid.of (Lt.gen k x))
    (FreeMonoid.of (Lt.gen k x) * FreeMonoid.of (Lt.gen k y))

theorem GC.symm {k : ℕ} {x y : Lt} (h : GC k x y) : GC k y x := Derivable.symm h

theorem gen_up (k : ℕ) (z : Lt) (hz : 1 ≤ z.lo) : Lt.gen (k + 1) z = .up (Lt.gen k z.down) := by
  cases z with
  | H j => cases j with
    | zero => simp [Lt.lo] at hz
    | succ j => rfl
  | S j => cases j with
    | zero => simp [Lt.lo] at hz
    | succ j => rfl
  | C j => cases j with
    | zero => simp [Lt.lo] at hz
    | succ j => rfl

/-- A letter on wire 0 commutes with a letter on disjoint wires. -/
theorem gen_comm_base (k : ℕ) (x y : Lt) (hx : x.lo = 0) (h : Lt.disj x y = true) : GC k x y := by
  cases k with
  | zero =>
    show Der 0 _ _
    rw [show Lt.gen 0 x = .gate0 .negω by cases x <;> rfl]; exact scalar_comm _
  | succ k =>
    have h1 : ∀ (g : Gate 1) (y : Lt), 1 ≤ y.lo →
        Der (k + 1) (FreeMonoid.of (Lt.gen (k + 1) y) * FreeMonoid.of (Gen.gate1 g))
          (FreeMonoid.of (Gen.gate1 g) * FreeMonoid.of (Lt.gen (k + 1) y)) := by
      intro g y hy
      rw [gen_up k y hy]; exact Derivable.of (Lift.comm1 g _)
    cases x with
    | H j =>
      obtain rfl : j = 0 := hx
      have hy : 1 ≤ y.lo := by cases y <;> simp_all [Lt.disj, Lt.lo, Lt.hi] <;> omega
      exact h1 _ y hy
    | S j =>
      obtain rfl : j = 0 := hx
      have hy : 1 ≤ y.lo := by cases y <;> simp_all [Lt.disj, Lt.lo, Lt.hi] <;> omega
      exact h1 _ y hy
    | C j =>
      obtain rfl : j = 0 := hx
      have hy : 2 ≤ y.lo := by cases y <;> simp_all [Lt.disj, Lt.lo, Lt.hi] <;> omega
      cases k with
      | zero =>
        show Der 1 _ _
        rw [show Lt.gen 1 (.C 0) = .gate0 .negω from rfl]; exact scalar_comm _
      | succ k =>
        have hy1 : 1 ≤ y.lo := by omega
        have hy2 : 1 ≤ y.down.lo := by cases y <;> simp_all [Lt.lo, Lt.down] <;> omega
        show Der (k + 2) _ _
        rw [gen_up (k + 1) y hy1, gen_up k y.down hy2]
        exact Derivable.of (Lift.comm2 Gate.CZ _)

/-- **Letters on disjoint wires commute.** -/
theorem gen_comm : ∀ (k : ℕ) (x y : Lt), Lt.disj x y = true → GC k x y
  | 0, x, y, _ => by
    show Der 0 _ _
    rw [show Lt.gen 0 x = .gate0 .negω by cases x <;> rfl]; exact scalar_comm _
  | k + 1, x, y, h => by
    by_cases hx : x.lo = 0
    · exact gen_comm_base _ x y hx h
    by_cases hy : y.lo = 0
    · exact (gen_comm_base _ y x hy (by simp only [Lt.disj] at h ⊢; rw [Bool.or_comm]; exact h)).symm
    have hd : Lt.disj x.down y.down = true := by
      cases x <;> cases y <;> simp_all [Lt.disj, Lt.lo, Lt.hi, Lt.down] <;> omega
    have := derives_shift (gen_comm k x.down y.down hd)
    simp only [map_mul, Circuit.shift_of] at this
    show Der (k + 1) _ _
    rw [gen_up k x (by omega), gen_up k y (by omega)]; exact this

/-- Commuting two adjacent letters on disjoint wires. -/
theorem E.swap {k : ℕ} {x y : Lt} (h : Lt.disj x y = true) : E k [x, y] [y, x] := by
  unfold E; simp only [cw, one_mul]
  exact PEq.of_der (gen_comm k x y h)

theorem E.move_left {k : ℕ} (x : Lt) : ∀ (p : List Lt), (∀ y ∈ p, Lt.disj y x = true) →
    E k (p ++ [x]) (x :: p)
  | [], _ => E.refl _
  | y :: p, h => by
    have ih := move_left (k := k) x p (fun z hz => h z (List.mem_cons_of_mem _ hz))
    have h1 : E k (y :: (p ++ [x])) (y :: x :: p) := (E.refl [y]).append ih
    refine h1.trans ?_
    exact (E.swap (h y List.mem_cons_self)).append (E.refl p)

/-! ### Canonical forms -/

namespace Bl

/-- `bl` blocks every wire of the letters of `pre`. -/
def Inv (bl : Bl) (pre : List Lt) : Prop := ∀ w, bl.get w = false → ∀ y ∈ pre, onw y w = false

theorem inv_nil : Inv ⟨false, false, false⟩ [] := fun _ _ _ h => nomatch h

theorem inv_add {bl : Bl} {pre : List Lt} (h : Inv bl pre) (x : Lt) :
    Inv (bl.add x) (pre ++ [x]) := by
  intro w hw y hy
  have hw' : bl.get w = false ∧ onw x w = false := by
    match w, hw with
    | 0, hw => simp_all [get, add]
    | 1, hw => simp_all [get, add]
    | 2, hw => simp_all [get, add]
  rcases List.mem_append.1 hy with hy | hy
  · exact h w hw'.1 y hy
  · rw [List.mem_singleton.1 hy]; exact hw'.2

theorem disj_of_free {bl : Bl} {pre : List Lt} (h : Inv bl pre) {x : Lt}
    (hx : free bl x = true) : ∀ y ∈ pre, Lt.disj y x = true := by
  intro y hy
  simp only [free, Bool.and_eq_true, Bool.not_eq_true'] at hx
  have h1 := h _ hx.1 y hy
  have h2 := h _ hx.2 y hy
  cases x <;> cases y <;> simp_all [onw, Lt.disj, Lt.lo, Lt.hi] <;> omega

end Bl

/-- The specification of a choice `(j, x)` in `orig`. -/
def PickSpec (orig : List Lt) (j : ℕ) (x : Lt) : Prop :=
  orig.take j ++ x :: orig.drop (j + 1) = orig ∧ ∀ y ∈ orig.take j, Lt.disj y x = true

theorem pickI_spec : ∀ (bl : Bl) (pre : List Lt) (best : Option (ℕ × Lt)) (w : List Lt)
    (orig : List Lt), Bl.Inv bl pre → pre ++ w = orig →
    (∀ j x, best = some (j, x) → PickSpec orig j x) →
    ∀ j x, pickI bl pre.length best w = some (j, x) → PickSpec orig j x
  | _, _, _, [], _, _, _, hb => fun j x h => hb j x h
  | bl, pre, best, y :: rest, orig, hi, ho, hb => by
    intro j x h
    simp only [pickI] at h
    rw [show pre.length + 1 = (pre ++ [y]).length by simp] at h
    refine pickI_spec (bl.add y) (pre ++ [y]) _ rest orig (Bl.inv_add hi y)
      (by rw [← ho]; simp) ?_ j x h
    intro j' x' h'
    split_ifs at h' with hc
    · cases h'
      have hpre : orig.take pre.length = pre := by rw [← ho]; simp
      have hpost : orig.drop (pre.length + 1) = rest := by rw [← ho]; simp
      refine ⟨by rw [hpre, hpost, ← ho], ?_⟩
      rw [hpre]
      exact Bl.disj_of_free hi (Bool.and_eq_true _ _ ▸ hc).1
    · exact hb j' x' h'

theorem pick_spec {w : List Lt} {p : List Lt} {x : Lt} {s : List Lt}
    (h : pick w = some (p, x, s)) : p ++ x :: s = w ∧ ∀ y ∈ p, Lt.disj y x = true := by
  unfold pick at h
  cases hp : pickI ⟨false, false, false⟩ 0 none w with
  | none => rw [hp] at h; exact nomatch h
  | some iy =>
    obtain ⟨i, y⟩ := iy
    rw [hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact pickI_spec ⟨false, false, false⟩ [] none w w Bl.inv_nil rfl
      (fun _ _ h => nomatch h) i y hp

theorem canonF_E {k : ℕ} : ∀ (n : ℕ) (w : List Lt), E k w (canonF n w)
  | 0, w => E.refl w
  | n + 1, w => by
    unfold canonF
    split
    · exact E.refl w
    · rename_i p x s h
      obtain ⟨hw, hd⟩ := pick_spec h
      subst hw
      have h1 : E k (p ++ x :: s) (x :: (p ++ s)) := by
        have := (E.move_left (k := k) x p hd).append (E.refl s)
        simpa using this
      exact h1.trans ((E.refl [x]).append (canonF_E n (p ++ s)))

theorem canon_E {k : ℕ} (w : List Lt) : E k w (canon w) := canonF_E _ w

theorem E_of_canon {k : ℕ} {a b : List Lt} (h : canon a = canon b) : E k a b :=
  (canon_E a).trans (h ▸ (canon_E b).symm)

theorem E_of_canonOr {k : ℕ} {a b : List Lt} (h : (a == b || canon a == canon b) = true) :
    E k a b := by
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · rw [beq_iff_eq.1 h]
  · exact E_of_canon (beq_iff_eq.1 h)

/-! ### Runs -/

theorem swapAt_E {k : ℕ} : ∀ (i : ℕ) (w w' : List Lt), swapAt i w = some w' → E k w w'
  | 0, x :: y :: r, w', h => by
    simp only [swapAt] at h
    split_ifs at h with hd
    cases h
    exact (E.swap hd).append (E.refl r)
  | i + 1, x :: r, w', h => by
    simp only [swapAt, Option.map_eq_some_iff] at h
    obtain ⟨r', hr, rfl⟩ := h
    exact (E.refl [x]).append (swapAt_E i r r' hr)
  | 0, [], _, h => nomatch h
  | 0, [_], _, h => nomatch h
  | _ + 1, [], _, h => nomatch h

theorem swapsAt_E {k : ℕ} : ∀ (ps : List ℕ) (w w' : List Lt), swapsAt ps w = some w' → E k w w'
  | [], w, w', h => by cases h; exact E.refl w
  | i :: ps, w, w', h => by
    simp only [swapsAt, Option.bind_eq_some_iff] at h
    obtain ⟨v, hv, h⟩ := h
    exact (swapAt_E i w v hv).trans (swapsAt_E ps v w' h)

/-- Every equation of the table holds. -/
def Valid (k : ℕ) (T : Tbl) : Prop := ∀ e ∈ T, E k e.1 e.2

section Run

variable (fo : List Lt → List Lt → Bool)

variable {k : ℕ} (hfo : ∀ s t, fo s t = true → E k s t)
include hfo

theorem runStep_E {T : Tbl} (hT : Valid k T) {cur nxt : List Lt} {st : Step}
    (h : runStep fo T cur st = some nxt) : E k cur nxt := by
  cases st with
  | rule i rev u v =>
    simp only [runStep] at h
    split at h
    · exact nomatch h
    · rename_i e he
      have hv := hT e (List.mem_of_getElem? he)
      by_cases hc : (cur == u ++ (if rev then e.2 else e.1) ++ v ||
          canon cur == canon (u ++ (if rev then e.2 else e.1) ++ v)) = true
      · rw [if_pos hc] at h
        cases h
        refine (E_of_canonOr hc).trans (E.append3 ?_)
        cases rev
        · exact hv
        · exact hv.symm
      · rw [if_neg hc] at h; exact nomatch h
  | free u s t v =>
    simp only [runStep] at h
    split_ifs at h with hc
    cases h
    rw [Bool.and_eq_true] at hc
    exact (E_of_canonOr hc.1).trans (E.append3 (hfo s t hc.2))
  | swaps ps =>
    simp only [runStep] at h
    exact swapsAt_E ps cur nxt h

theorem runSteps_E {T : Tbl} (hT : Valid k T) :
    ∀ {cur fin : List Lt} {sts : List Step}, runSteps fo T cur sts = some fin → E k cur fin := by
  intro cur fin sts h
  induction sts generalizing cur with
  | nil => cases h; exact E.refl _
  | cons st sts ih =>
    simp only [runSteps] at h
    split at h
    · exact nomatch h
    · rename_i nxt hn
      exact (runStep_E fo hfo hT hn).trans (ih h)

theorem lemOk_E {T : Tbl} (hT : Valid k T) {l r : List Lt} {sts : List Step}
    (h : lemOk fo T l r sts = true) : E k l r := by
  unfold lemOk at h
  split at h
  · exact nomatch h
  · rename_i c hc
    exact (runSteps_E fo hfo hT hc).trans (E_of_canonOr h)

theorem libOk_valid : ∀ (T : Tbl) (L : List (List Lt × List Lt × List Step)),
    Valid k T → libOk fo T L = true → Valid k (libTbl T L)
  | T, [], hT, _ => by simpa [libTbl] using hT
  | T, (l, r, sts) :: rest, hT, h => by
    simp only [libOk, Bool.and_eq_true] at h
    have h1 : Valid k (T ++ [(l, r)]) := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact hT e he
      · rw [List.mem_singleton.1 he]; exact lemOk_E fo hfo hT h.1
    have := libOk_valid (T ++ [(l, r)]) rest h1 h.2
    simpa [libTbl] using this

end Run

end QCert.QutritClifford
