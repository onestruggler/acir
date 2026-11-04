/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A rewriting engine for derivations on two and three wires

Toward Theorem 4.4.  A derivation on `k` wires is checked as a run over
words of letters (`Lt`: `H`, `S` on a wire, `CZ` on two adjacent wires),
read in time order (`cw`), up to a phase (`E`, i.e. `PEq`); the words are
stored as base-16 codes (`dec16`, with `decS` its specification by
recursion on the code, and `decS_add`: a code split at a power of `16`
splits its word):

* `sameTr` tests whether two words are equal up to commuting adjacent
  letters on disjoint wires, and `sameTr_E` says they are then equal;
  `sameH` compares two codes, equal or equal up to commuting letters on a
  window (`sameH_E`);
* a rule step replaces an occurrence (up to `sameH`) of one side of an
  equation of a table by the other side (`ruleX_E`, `stepX_E`);
* a free step replaces a segment lying on the bottom `k - 1` wires, or on
  the top `k - 1` wires, by another one acting alike on the Paulis there:
  with completeness on `k - 1` wires they are derivably equal up to a phase
  (`pcomplete_gens`), and a derivation on `k - 1` wires holds on the bottom
  or top wires of `k` (`PEq.pad`, `PEq.shift`).

`runX_E` makes a run an equation; `Local.lean` checks a library lemma by
lemma, each over the table so far (`validUpTo_all`).
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

/-! ### Equality up to commuting letters

`sameTr` takes the letters of the second word out of the first in order;
each is taken from behind letters on disjoint wires only, so the two words
are equal (`sameTr_E`). -/

theorem Lt.eq_of_beq : ∀ {a b : Lt}, Lt.beq a b = true → a = b
  | .H _, .H _, h => congrArg Lt.H (Nat.eq_of_beq_eq_true h)
  | .S _, .S _, h => congrArg Lt.S (Nat.eq_of_beq_eq_true h)
  | .C _, .C _, h => congrArg Lt.C (Nat.eq_of_beq_eq_true h)
  | .H _, .S _, h | .H _, .C _, h | .S _, .H _, h | .S _, .C _, h | .C _, .H _, h
  | .C _, .S _, h => nomatch h

theorem extract_E {k : ℕ} (t : Lt) : ∀ {w w' : List Lt}, extract t w = some w' →
    E k w (t :: w')
  | [], _, h => nomatch h
  | y :: w, w', h => by
    simp only [extract] at h
    cases hb : Lt.beq t y with
    | true =>
      rw [hb, cond_true, Option.some.injEq] at h
      rw [← h, Lt.eq_of_beq hb]
    | false =>
      rw [hb, cond_false] at h
      cases hd : Lt.disj y t with
      | false => rw [hd] at h; exact nomatch h
      | true =>
        rw [hd, cond_true, Option.map_eq_some_iff] at h
        obtain ⟨w'', hw'', rfl⟩ := h
        have h1 : E k (y :: w) (y :: t :: w'') := (E.refl [y]).append (extract_E t hw'')
        have h2 : E k (y :: t :: w'') (t :: y :: w'') := (E.swap hd).append (E.refl w'')
        exact h1.trans h2

theorem sameTr_E {k : ℕ} : ∀ {w v : List Lt}, sameTr w v = true → E k w v
  | [], [], _ => E.refl _
  | _ :: _, [], h => nomatch h
  | w, t :: ts, h => by
    simp only [sameTr] at h
    match he : extract t w with
    | none => rw [he] at h; exact nomatch h
    | some w' =>
      rw [he] at h
      exact (extract_E t he).trans ((E.refl [t]).append (sameTr_E h))

/-- Every equation of the table holds. -/
def Valid (k : ℕ) (T : Tbl) : Prop := ∀ e ∈ T, E k e.1 e.2

/-! ### Codes

`dec16` reads a code digit by digit; `decS` is the same by recursion on the
code, and splitting a code at a power of `16` splits its word
(`decS_add`), whatever the digits, since a digit that is no letter stands
for none. -/

/-- The word of a code, by recursion on the code. -/
def decS (n : ℕ) : List Lt :=
  if n = 0 then [] else dig16 (n % 16) ++ decS (n / 16)
decreasing_by omega

theorem decS_zero : decS 0 = [] := by rw [decS]; rfl

theorem decS_eq (n : ℕ) : decS n = dig16 (n % 16) ++ decS (n / 16) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [decS_zero]; rfl
  · rw [decS, if_neg (by omega)]

theorem dec16F_eq : ∀ f n, n ≤ f → dec16F f n = decS n
  | 0, n, h => by
    obtain rfl : n = 0 := by omega
    rw [decS_zero]; rfl
  | f + 1, n, h => by
    show (bif n.beq 0 then [] else dig16 (n % 16) ++ dec16F f (n / 16)) = decS n
    cases n with
    | zero => rw [decS_zero]; rfl
    | succ m =>
      rw [show (m + 1).beq 0 = false from rfl, cond_false, dec16F_eq f _ (by omega), ← decS_eq]

theorem dec16_eq (n : ℕ) : dec16 n = decS n := dec16F_eq n n le_rfl

theorem decS_add : ∀ (k a b : ℕ), a < 16 ^ k → decS (a + 16 ^ k * b) = decS a ++ decS b
  | 0, a, b, h => by
    obtain rfl : a = 0 := by simpa using h
    rw [decS_zero, pow_zero, one_mul, zero_add, List.nil_append]
  | k + 1, a, b, h => by
    rw [pow_succ] at h
    have e : 16 ^ (k + 1) * b = 16 * (16 ^ k * b) := by rw [pow_succ]; ring
    have h1 : a / 16 < 16 ^ k := by generalize 16 ^ k = P at h ⊢; omega
    have ih := decS_add k (a / 16) b h1
    rw [e, decS_eq (a + 16 * (16 ^ k * b)), decS_eq a]
    generalize 16 ^ k * b = c at ih ⊢
    rw [show (a + 16 * c) % 16 = a % 16 by omega, show (a + 16 * c) / 16 = a / 16 + c by omega, ih,
      List.append_assoc]

theorem decS_split (n k : ℕ) : decS n = decS (n % 16 ^ k) ++ decS (n / 16 ^ k) := by
  conv_lhs => rw [← Nat.mod_add_div n (16 ^ k)]
  exact decS_add k _ _ (Nat.mod_lt _ (by positivity))

theorem dec16_cat3 {u lu a la : ℕ} (v : ℕ) (hu : u < 16 ^ lu) (ha : a < 16 ^ la) :
    dec16 (cat3 u lu a la v) = dec16 u ++ dec16 a ++ dec16 v := by
  simp only [dec16_eq, cat3]
  rw [decS_add lu u _ hu, decS_add la a v ha, List.append_assoc]

theorem sameH_E {k : ℕ} {c d p w : ℕ} (h : sameH c d p w = true) : E k (dec16 c) (dec16 d) := by
  simp only [sameH, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨⟨h1, h2⟩, h3⟩
  · rw [Nat.eq_of_beq_eq_true h]
  · have split : ∀ x : ℕ, dec16 x =
        decS (x % 16 ^ p) ++ dec16 (x / 16 ^ p % 16 ^ w) ++ decS (x / 16 ^ (p + w)) := by
      intro x
      rw [dec16_eq, dec16_eq, decS_split x p, decS_split (x / 16 ^ p) w, Nat.div_div_eq_div_mul,
        ← pow_add, List.append_assoc]
    rw [split c, split d, Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2]
    exact E.append3 (sameTr_E h3)

/-! ### Runs on codes -/

theorem ruleX_E {k : ℕ} {sm : ℕ → ℕ → ℕ → ℕ → Bool}
    (hsm : ∀ c d p w, sm c d p w = true → E k (dec16 c) (dec16 d))
    {cur u lu v p w x lx y ly nxt : ℕ} (hxy : E k (dec16 x) (dec16 y))
    (h : ruleX sm cur u lu v p w x lx y ly = some nxt) : E k (dec16 cur) (dec16 nxt) := by
  unfold ruleX at h
  cases hc : (Nat.blt u (16 ^ lu) && Nat.blt x (16 ^ lx) && Nat.blt y (16 ^ ly) &&
      sm cur (cat3 u lu x lx v) p w)
  · rw [hc] at h; exact nomatch h
  · rw [hc] at h
    cases h
    simp only [Bool.and_eq_true, Nat.blt_eq] at hc
    obtain ⟨⟨⟨hu, hx⟩, hy⟩, hs⟩ := hc
    have h1 := hsm _ _ _ _ hs
    rw [dec16_cat3 v hu hx] at h1
    rw [dec16_cat3 v hu hy]
    exact h1.trans (E.append3 hxy)

section Run

variable (fo : List Lt → List Lt → Bool)

variable {k : ℕ} (hfo : ∀ s t, fo s t = true → E k s t)
include hfo

theorem stepX_E {T : ℕ → Option (ℕ × ℕ × ℕ × ℕ)}
    (hT : ∀ j e, T j = some e → E k (dec16 e.1) (dec16 e.2.2.1))
    {cur nxt : ℕ} {st : SX} (h : stepX fo T cur st = some nxt) : E k (dec16 cur) (dec16 nxt) := by
  obtain ⟨kk, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := st
  simp only [stepX] at h
  cases hk : kk.beq 0
  · rw [hk, cond_false] at h
    cases hk1 : kk.beq 1
    · rw [hk1, cond_false] at h; exact nomatch h
    · rw [hk1, cond_true] at h
      cases hf : fo (dec16 a3) (dec16 a5)
      · rw [hf, cond_false] at h; exact nomatch h
      · rw [hf, cond_true] at h
        exact ruleX_E (fun _ _ _ _ => sameH_E) (hfo _ _ hf) h
  · rw [hk, cond_true] at h
    split at h
    · exact nomatch h
    · rename_i l ll r lr he
      have hlr := hT _ _ he
      cases hr : a2.beq 1
      · rw [hr, cond_false] at h; exact ruleX_E (fun _ _ _ _ => sameH_E) hlr h
      · rw [hr, cond_true] at h; exact ruleX_E (fun _ _ _ _ => sameH_E) hlr.symm h

theorem runX_E {T : ℕ → Option (ℕ × ℕ × ℕ × ℕ)}
    (hT : ∀ j e, T j = some e → E k (dec16 e.1) (dec16 e.2.2.1)) :
    ∀ {sts : List SX} {cur fin : ℕ}, runX fo T sts cur = some fin → E k (dec16 cur) (dec16 fin)
  | [], cur, fin, h => by cases h; exact E.refl _
  | st :: sts, cur, fin, h => by
    simp only [runX] at h
    split at h
    · rename_i c' hc
      exact (stepX_E fo hfo hT hc).trans (runX_E hT h)
    · exact nomatch h

end Run

end QCert.QutritClifford
