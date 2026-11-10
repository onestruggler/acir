/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Four wires: frames

Translation of `Frames.agda`.  The NOT gates and the swaps generate the
symmetries of the 4-cube, and a gate anywhere on the four wires, with black
or white controls, is a gate on the bottom wires between a word `p` of them
and its reverse: a three-wire circuit `b` in the frame `p`.  This module
decides the two kinds of equation that such words obey for structural
reasons, so that a derivation can use each as one step:

* `hstep u v`: two words in the NOT gates and swaps with the same function
  are equal.  `hnorm` brings such a word to the form `q • X₃ᵉ • r` (`q` on
  the bottom three wires, `r` one of four words that bring each wire to the
  top) one letter at a time, by a table (`tab`) whose 28 entries are derived
  from the rules; two words with the same `r`, the same `e` and `q`'s of the
  same function are then equal by completeness on three wires.

* `frame p p′ b b′`: `p • b • p⁻¹ = p′ • b′ • p′⁻¹` when `p⁻¹ • p′` keeps
  the top wire in place, `q • X₃ᵉ` say, and `q • b′ • q⁻¹` and `b` have the
  same function (`X₃` commutes with circuits on the bottom wires).

The evidence of each is a Boolean that evaluation decides.

**Deviations from the Agda.**  Letter lists are lists of names (`Engine`):
the Agda's `⌜_⌝ : HL → Gen 4` is `hgen : HL → L4`, `⌜_⌝ˡ` is `hl`, and `dn`
maps `dn34`.  Associativity and the units are those of the free monoid, so
the Agda's `by-passoc` steps disappear, and the two calculations with
several of them (`step-ok`, `Conj.conj`) are done once in any monoid
(`step_calc`, `conj_calc`) and applied in the quotient monoid of the theory
(`CircuitProp.cl`).  The Agda's `x3^`, `Out`'s field `or` and `ū` are
`x3p`, `orep` and `ub`.
-/
import QCert.Alt16RevCir.FourWire

namespace QCert.Alt16RevCir.Frames

open QCert QCert.Circuit CircuitProp Engine FourWire
open Engine.L4 (x0 x1 x2 x3 cx0 cx1 cx2 ex0 ex1 ex2 ccx0 ccx1)

/-- An equation of words is a derivation. -/
private theorem derOfEq {w v : Circ 4} (h : w = v) : 4 ⊢ᵀ w ≈ v := h ▸ Derivable.refl w

/-! ## The letters -/

/-- The NOT gates and the swaps. -/
inductive HL
  | hx0 | hx1 | hx2 | hx3 | he0 | he1 | he2

/-- The Agda's `⌜_⌝`. -/
def hgen : HL → L4
  | .hx0 => x0
  | .hx1 => x1
  | .hx2 => x2
  | .hx3 => x3
  | .he0 => ex0
  | .he1 => ex1
  | .he2 => ex2

/-- The Agda's `⌜_⌝ˡ`. -/
def hl (u : List HL) : List L4 := u.map hgen

/-- A circuit on the bottom three wires. -/
def dn (b : List L3) : List L4 := b.map dn34

private abbrev a₃ : L3 := .x0

private abbrev b₃ : L3 := .x1

private abbrev d₃ : L3 := .x2

private abbrev s₃ : L3 := .ex0

private abbrev t₃ : L3 := .ex1

private theorem hl_append (u v : List HL) : word (hl (u ++ v)) = word (hl u) * word (hl v) := by
  simp only [hl, List.map_append, word_append]

private theorem dn_append (q b : List L3) : word (dn (q ++ b)) = word (dn q) * word (dn b) := by
  simp only [dn, List.map_append, word_append]

/-! ## X on the top wire commutes with the bottom three wires -/

private theorem x3_letter : ∀ g : L3,
    4 ⊢ᵀ word [x3] * word [dn34 g] ≈ word [dn34 g] * word [x3]
  | .x0 => Derivable.of (Lift.comm1 Gate.X_gate (Gen.up (Gen.up (Gen.gate1 Gate.X_gate))))
  | .cx0 => Derivable.of (Lift.comm2 Gate.CX_gate (Gen.up (Gen.gate1 Gate.X_gate)))
  | .ex0 => Derivable.of (Lift.comm2 Gate.Ex_gate (Gen.up (Gen.gate1 Gate.X_gate)))
  | .ccx => Derivable.of (Lift.comm3 Gate.CCX_gate (Gen.gate1 Gate.X_gate))
  | .x1 => lemma_cong_up
      (Derivable.of (Lift.comm1 Gate.X_gate (Gen.up (Gen.gate1 Gate.X_gate))))
  | .cx1 => lemma_cong_up (Derivable.of (Lift.comm2 Gate.CX_gate (Gen.gate1 Gate.X_gate)))
  | .ex1 => lemma_cong_up (Derivable.of (Lift.comm2 Gate.Ex_gate (Gen.gate1 Gate.X_gate)))
  | .x2 => lemma_cong_up (lemma_cong_up
      (Derivable.of (Lift.comm1 Gate.X_gate (Gen.gate1 Gate.X_gate))))

private theorem x3_word : ∀ b : List L3,
    4 ⊢ᵀ word [x3] * word (dn b) ≈ word (dn b) * word [x3]
  | [] => Derivable.refl _
  | g :: b => by
    have h1 := cl_eq.2 (x3_letter g)
    have h2 := cl_eq.2 (x3_word b)
    rw [cl_mul, cl_mul] at h1 h2
    apply cl_eq.1
    show cl (PropRel TRel) 4 (word [x3] * (word [dn34 g] * word (dn b))) =
      cl (PropRel TRel) 4 (word [dn34 g] * word (dn b) * word [x3])
    rw [cl_mul, cl_mul, cl_mul, cl_mul, ← mul_assoc, h1, mul_assoc, h2, mul_assoc]

/-- `X` on the top wire, or nothing (the Agda's `x3^`). -/
def x3p : Bool → List L4
  | false => []
  | true => [x3]

private theorem E_word : ∀ (e : Bool) (b : List L3),
    4 ⊢ᵀ word (x3p e) * word (dn b) ≈ word (dn b) * word (x3p e)
  | false, b => derOfEq (by
      show 1 * word (dn b) = word (dn b) * 1
      rw [one_mul, mul_one])
  | true, b => x3_word b

private theorem x3x3 : 4 ⊢ᵀ word (x3p true) * word (x3p true) ≈ 1 :=
  (top [d₃, d₃] [] (by decide +kernel)).prf

private theorem E_mul : ∀ e e' : Bool,
    4 ⊢ᵀ word (x3p e) * word (x3p e') ≈ word (x3p (e ^^ e'))
  | false, e' => derOfEq (by
      rw [Bool.false_xor]
      exact one_mul (word (x3p e')))
  | true, false => derOfEq (mul_one (word (x3p true)))
  | true, true => x3x3

private theorem E_sq : ∀ e : Bool, 4 ⊢ᵀ word (x3p e) * word (x3p e) ≈ 1
  | false => derOfEq (one_mul 1)
  | true => x3x3

/-! ## The table -/

/-- The words that bring a wire to the top: none, the top swap, and the swaps
below it. -/
inductive Rep
  | r0 | r1 | r2 | r3

def rep : Rep → List L4
  | .r0 => []
  | .r1 => [ex2]
  | .r2 => [ex2, ex1]
  | .r3 => [ex2, ex1, ex0]

structure Out where
  out ::
  ob : List L3
  oe : Bool
  orep : Rep

open Rep HL in
/-- `rep r` followed by a letter is a letter on the bottom wires or `X` on
the top wire, followed by a `rep`. -/
def tab : Rep → HL → Out
  | r0, hx0 => ⟨[a₃], false, r0⟩
  | r0, hx1 => ⟨[b₃], false, r0⟩
  | r0, hx2 => ⟨[d₃], false, r0⟩
  | r0, hx3 => ⟨[], true, r0⟩
  | r0, he0 => ⟨[s₃], false, r0⟩
  | r0, he1 => ⟨[t₃], false, r0⟩
  | r0, he2 => ⟨[], false, r1⟩
  | r1, hx0 => ⟨[a₃], false, r1⟩
  | r1, hx1 => ⟨[b₃], false, r1⟩
  | r1, hx2 => ⟨[], true, r1⟩
  | r1, hx3 => ⟨[d₃], false, r1⟩
  | r1, he0 => ⟨[s₃], false, r1⟩
  | r1, he1 => ⟨[], false, r2⟩
  | r1, he2 => ⟨[], false, r0⟩
  | r2, hx0 => ⟨[a₃], false, r2⟩
  | r2, hx1 => ⟨[], true, r2⟩
  | r2, hx2 => ⟨[b₃], false, r2⟩
  | r2, hx3 => ⟨[d₃], false, r2⟩
  | r2, he0 => ⟨[], false, r3⟩
  | r2, he1 => ⟨[], false, r1⟩
  | r2, he2 => ⟨[t₃], false, r2⟩
  | r3, hx0 => ⟨[], true, r3⟩
  | r3, hx1 => ⟨[a₃], false, r3⟩
  | r3, hx2 => ⟨[b₃], false, r3⟩
  | r3, hx3 => ⟨[d₃], false, r3⟩
  | r3, he0 => ⟨[], false, r2⟩
  | r3, he1 => ⟨[s₃], false, r3⟩
  | r3, he2 => ⟨[t₃], false, r3⟩

/-! Pushing a letter through a swap, on the bottom or the top three wires. -/

private def b2 (x y x' y' : L3) (h : same3 [x, y] [x', y'] = true) : Eqn TRel L4 :=
  bot [x, y] [x', y'] h

private def t2 (x y x' y' : L3) (h : same3 [x, y] [x', y'] = true) : Eqn TRel L4 :=
  top [x, y] [x', y'] h

private def braid₃ : Eqn TRel L3 := sem₃ [t₃, s₃, t₃] [s₃, t₃, s₃] (by decide +kernel)

/-- A derivation on four wires. -/
private abbrev der4 (l r : List L4) (ss : List (Step TRel L4)) (h : check ss l r = true) :
    Eqn TRel L4 := derive l r ss h

open Rep HL in
private theorem tab_ok : ∀ (r : Rep) (y : HL),
    4 ⊢ᵀ word (rep r ++ [hgen y]) ≈
      word (dn (tab r y).ob ++ (x3p (tab r y).oe ++ rep (tab r y).orep))
  | r0, hx0 => Derivable.refl _
  | r0, hx1 => Derivable.refl _
  | r0, hx2 => Derivable.refl _
  | r0, hx3 => Derivable.refl _
  | r0, he0 => Derivable.refl _
  | r0, he1 => Derivable.refl _
  | r0, he2 => Derivable.refl _
  | r1, hx0 => comm_ex2_x0.prf
  | r1, hx1 => (t2 t₃ a₃ a₃ t₃ (by decide +kernel)).prf
  | r1, hx2 => (t2 t₃ b₃ d₃ t₃ (by decide +kernel)).prf
  | r1, hx3 => (t2 t₃ d₃ b₃ t₃ (by decide +kernel)).prf
  | r1, he0 => comm_ex2_ex0.prf
  | r1, he1 => Derivable.refl _
  | r1, he2 => (top [t₃, t₃] [] (by decide +kernel)).prf
  | r2, hx0 => (der4 [ex2, ex1, x0] [x0, ex2, ex1]
      [Step.rw 1 (b2 t₃ a₃ a₃ t₃ (by decide +kernel)), Step.rw 0 comm_ex2_x0]
      (by decide +kernel)).prf
  | r2, hx1 => (der4 [ex2, ex1, x1] [x3, ex2, ex1]
      [Step.rw 1 (b2 t₃ b₃ d₃ t₃ (by decide +kernel)),
       Step.rw 0 (t2 t₃ b₃ d₃ t₃ (by decide +kernel))]
      (by decide +kernel)).prf
  | r2, hx2 => (der4 [ex2, ex1, x2] [x1, ex2, ex1]
      [Step.rw 1 (b2 t₃ d₃ b₃ t₃ (by decide +kernel)),
       Step.rw 0 (t2 t₃ a₃ a₃ t₃ (by decide +kernel))]
      (by decide +kernel)).prf
  | r2, hx3 => (der4 [ex2, ex1, x3] [x2, ex2, ex1]
      [Step.rw 1 (t2 s₃ d₃ d₃ s₃ (by decide +kernel)),
       Step.rw 0 (t2 t₃ d₃ b₃ t₃ (by decide +kernel))]
      (by decide +kernel)).prf
  | r2, he0 => Derivable.refl _
  | r2, he1 => (der4 [ex2, ex1, ex1] [ex2]
      [Step.rw 1 (bot [t₃, t₃] [] (by decide +kernel))] (by decide +kernel)).prf
  | r2, he2 => (liftE up34 up34_gen braid₃).prf
  | r3, hx0 => (der4 [ex2, ex1, ex0, x0] [x3, ex2, ex1, ex0]
      [Step.rw 2 (b2 s₃ a₃ b₃ s₃ (by decide +kernel)),
       Step.rw 1 (b2 t₃ b₃ d₃ t₃ (by decide +kernel)),
       Step.rw 0 (t2 t₃ b₃ d₃ t₃ (by decide +kernel))]
      (by decide +kernel)).prf
  | r3, hx1 => (der4 [ex2, ex1, ex0, x1] [x0, ex2, ex1, ex0]
      [Step.rw 2 (b2 s₃ b₃ a₃ s₃ (by decide +kernel)),
       Step.rw 1 (b2 t₃ a₃ a₃ t₃ (by decide +kernel)), Step.rw 0 comm_ex2_x0]
      (by decide +kernel)).prf
  | r3, hx2 => (der4 [ex2, ex1, ex0, x2] [x1, ex2, ex1, ex0]
      [Step.rw 2 (b2 s₃ d₃ d₃ s₃ (by decide +kernel)),
       Step.rw 1 (b2 t₃ d₃ b₃ t₃ (by decide +kernel)),
       Step.rw 0 (t2 t₃ a₃ a₃ t₃ (by decide +kernel))]
      (by decide +kernel)).prf
  | r3, hx3 => (der4 [ex2, ex1, ex0, x3] [x2, ex2, ex1, ex0]
      [Step.rw 2 (symE comm_x3_ex0), Step.rw 1 (t2 s₃ d₃ d₃ s₃ (by decide +kernel)),
       Step.rw 0 (t2 t₃ d₃ b₃ t₃ (by decide +kernel))]
      (by decide +kernel)).prf
  | r3, he0 => (der4 [ex2, ex1, ex0, ex0] [ex2, ex1]
      [Step.rw 2 (bot [s₃, s₃] [] (by decide +kernel))] (by decide +kernel)).prf
  | r3, he1 => (der4 [ex2, ex1, ex0, ex1] [ex0, ex2, ex1, ex0]
      [Step.rw 1 (bot [t₃, s₃, t₃] [s₃, t₃, s₃] (by decide +kernel)), Step.rw 0 comm_ex2_ex0]
      (by decide +kernel)).prf
  | r3, he2 => (der4 [ex2, ex1, ex0, ex2] [ex1, ex2, ex1, ex0]
      [Step.rw 2 (symE comm_ex2_ex0), Step.rw 0 (liftE up34 up34_gen braid₃)]
      (by decide +kernel)).prf

/-! ## The normal form of a word in the NOT gates and swaps -/

structure St where
  st ::
  sq : List L3
  se : Bool
  sr : Rep

/-- The word of a state. -/
def W (s : St) : Circ 4 := word (dn s.sq) * (word (x3p s.se) * word (rep s.sr))

def step (s : St) (y : HL) : St :=
  ⟨s.sq ++ (tab s.sr y).ob, s.se ^^ (tab s.sr y).oe, (tab s.sr y).orep⟩

def hnorm : St → List HL → St
  | s, [] => s
  | s, y :: u => hnorm (step s y) u

def s₀ : St := ⟨[], false, .r0⟩

def hnorm₀ (u : List HL) : St := hnorm s₀ u

private theorem tabW (r : Rep) (y : HL) :
    4 ⊢ᵀ word (rep r) * word [hgen y] ≈
      word (dn (tab r y).ob) * (word (x3p (tab r y).oe) * word (rep (tab r y).orep)) := by
  have h := tab_ok r y
  rwa [word_append, word_append, word_append] at h

private theorem step_calc {M : Type} [Monoid M] {q e r y b e' r' ee : M}
    (h1 : r * y = b * (e' * r')) (h2 : e * b = b * e) (h3 : e * e' = ee) :
    q * (e * r) * y = q * b * (ee * r') := by
  calc q * (e * r) * y = q * e * (r * y) := by simp only [mul_assoc]
    _ = q * e * (b * (e' * r')) := by rw [h1]
    _ = q * (e * b) * (e' * r') := by simp only [mul_assoc]
    _ = q * (b * e) * (e' * r') := by rw [h2]
    _ = q * b * (e * e' * r') := by simp only [mul_assoc]
    _ = q * b * (ee * r') := by rw [h3]

private theorem step_ok (s : St) (y : HL) : 4 ⊢ᵀ W s * word [hgen y] ≈ W (step s y) := by
  have h1 := cl_eq.2 (tabW s.sr y)
  have h2 := cl_eq.2 (E_word s.se (tab s.sr y).ob)
  have h3 := cl_eq.2 (E_mul s.se (tab s.sr y).oe)
  simp only [cl_mul] at h1 h2 h3
  apply cl_eq.1
  simp only [W, step, dn_append, cl_mul]
  exact step_calc h1 h2 h3

private theorem hnorm_ok : ∀ (s : St) (u : List HL), 4 ⊢ᵀ W s * word (hl u) ≈ W (hnorm s u)
  | s, [] => derOfEq (mul_one (W s))
  | s, y :: u => by
    have e : W s * word (hl (y :: u)) = W s * word [hgen y] * word (hl u) := by
      rw [mul_assoc]; rfl
    rw [e]
    exact ((step_ok s y).mul (Derivable.refl _)).trans (hnorm_ok (step s y) u)

private theorem hnorm₀_ok (u : List HL) : 4 ⊢ᵀ word (hl u) ≈ W (hnorm₀ u) := by
  have h := hnorm_ok s₀ u
  have e : W s₀ * word (hl u) = word (hl u) := one_mul _
  rwa [e] at h

/-! ## Comparing normal forms -/

private def eqRep : Rep → Rep → Bool
  | .r0, .r0 => true
  | .r1, .r1 => true
  | .r2, .r2 => true
  | .r3, .r3 => true
  | _, _ => false

private theorem eqRep_sound : ∀ r r' : Rep, eqRep r r' = true → r = r' := by
  intro r r' h
  cases r <;> cases r' <;> first | rfl | exact absurd h (by decide)

/-- Two states with the same word, up to the function of the part on the
bottom wires. -/
def okSt (s s' : St) : Bool :=
  eqRep s.sr s'.sr && (eqB s.se s'.se && same3 s.sq s'.sq)

private theorem W_cong : ∀ (s s' : St), okSt s s' = true → 4 ⊢ᵀ W s ≈ W s'
  | ⟨q, e, r⟩, ⟨q', e', r'⟩, h => by
    simp only [okSt, Bool.and_eq_true] at h
    obtain ⟨h₁, h₂, h₃⟩ := h
    cases eqRep_sound _ _ h₁
    cases eqB_sound _ _ h₂
    exact (bot q q' h₃).prf.mul (Derivable.refl _)

/-- Two words in the NOT gates and swaps with the same normal form. -/
def hstep (u v : List HL) (h : okSt (hnorm₀ u) (hnorm₀ v) = true) : Eqn TRel L4 :=
  ⟨hl u, hl v, (hnorm₀_ok u).trans ((W_cong _ _ h).trans (hnorm₀_ok v).symm)⟩

/-! ## Changing the frame -/

private def isR0 : Rep → Bool
  | .r0 => true
  | _ => false

private theorem isR0_sound : ∀ r : Rep, isR0 r = true → r = .r0
  | .r0, _ => rfl
  | .r1, h => absurd h (by decide)
  | .r2, h => absurd h (by decide)
  | .r3, h => absurd h (by decide)

/-- From the frame `p` to the frame `p′`. -/
def fwd (p p' : List HL) : St := hnorm₀ (p.reverse ++ p')

def frame_ok (p p' : List HL) (b b' : List L3) : Bool :=
  okSt (hnorm₀ (p ++ p.reverse)) s₀ &&
  (isR0 (fwd p p').sr &&
  (isR0 (fwd p' p).sr &&
  (eqB (fwd p' p).se (fwd p p').se &&
   same3 ((fwd p p').sq ++ (b' ++ (fwd p' p).sq)) b)))

/-- The calculation, in any monoid (the Agda's module `Conj`). -/
private theorem conj_calc {M : Type} [Monoid M] {P Pb P' Pb' Q Qb E B B' : M}
    (ppb : P * Pb = 1) (u : Pb * P' = Q * E) (ub : Pb' * P = Qb * E)
    (EB' : E * B' = B' * E) (EQb : E * Qb = Qb * E) (EE : E * E = 1)
    (m : Q * (B' * Qb) = B) : P' * (B' * Pb') = P * (B * Pb) := by
  have inner : Q * E * (B' * (Qb * E)) = B := by
    calc Q * E * (B' * (Qb * E)) = Q * (E * B') * (Qb * E) := by simp only [mul_assoc]
      _ = Q * (B' * E) * (Qb * E) := by rw [EB']
      _ = Q * B' * (E * Qb) * E := by simp only [mul_assoc]
      _ = Q * B' * (Qb * E) * E := by rw [EQb]
      _ = Q * (B' * Qb) * (E * E) := by simp only [mul_assoc]
      _ = B := by rw [m, EE, mul_one]
  calc P' * (B' * Pb') = P * Pb * P' * (B' * (Pb' * (P * Pb))) := by
        rw [ppb, one_mul, mul_one]
    _ = P * (Pb * P' * (B' * (Pb' * P))) * Pb := by simp only [mul_assoc]
    _ = P * (Q * E * (B' * (Qb * E))) * Pb := by rw [u, ub]
    _ = P * (B * Pb) := by rw [inner, mul_assoc]

private theorem W_r0 (s : St) (h : s.sr = .r0) : W s = word (dn s.sq) * word (x3p s.se) := by
  rw [W, h]
  exact congrArg _ (mul_one _)

/-- The equation of a change of frame. -/
private theorem frame_prf (p p' : List HL) (b b' : List L3) (h : frame_ok p p' b b' = true) :
    4 ⊢ᵀ word (hl p ++ (dn b ++ hl p.reverse)) ≈ word (hl p' ++ (dn b' ++ hl p'.reverse)) := by
  simp only [frame_ok, Bool.and_eq_true] at h
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have ppb : 4 ⊢ᵀ word (hl p) * word (hl p.reverse) ≈ 1 := by
    rw [← hl_append]
    exact (hstep (p ++ p.reverse) [] h₁).prf
  have u : 4 ⊢ᵀ word (hl p.reverse) * word (hl p') ≈
      word (dn (fwd p p').sq) * word (x3p (fwd p p').se) := by
    rw [← hl_append, ← W_r0 _ (isR0_sound _ h₂)]
    exact hnorm₀_ok (p.reverse ++ p')
  have ub : 4 ⊢ᵀ word (hl p'.reverse) * word (hl p) ≈
      word (dn (fwd p' p).sq) * word (x3p (fwd p p').se) := by
    rw [← hl_append, ← eqB_sound _ _ h₄, ← W_r0 _ (isR0_sound _ h₃)]
    exact hnorm₀_ok (p'.reverse ++ p)
  have m : 4 ⊢ᵀ word (dn (fwd p p').sq) * (word (dn b') * word (dn (fwd p' p).sq)) ≈
      word (dn b) := by
    rw [← dn_append, ← dn_append]
    exact (bot _ b h₅).prf
  have ppb' := cl_eq.2 ppb
  have u' := cl_eq.2 u
  have ub' := cl_eq.2 ub
  have m' := cl_eq.2 m
  have EB' := cl_eq.2 (E_word (fwd p p').se b')
  have EQb := cl_eq.2 (E_word (fwd p p').se (fwd p' p).sq)
  have EE := cl_eq.2 (E_sq (fwd p p').se)
  simp only [cl_mul, cl_one] at ppb' u' ub' m' EB' EQb EE
  apply cl_eq.1
  simp only [word_append, cl_mul]
  exact (conj_calc ppb' u' ub' EB' EQb EE m').symm

/-- A circuit `b` on the bottom three wires in the frame `p` is the circuit
`b′` in the frame `p′`. -/
def frame (p p' : List HL) (b b' : List L3) (h : frame_ok p p' b b' = true) : Eqn TRel L4 :=
  ⟨hl p ++ (dn b ++ hl p.reverse), hl p' ++ (dn b' ++ hl p'.reverse), frame_prf p p' b b' h⟩

end QCert.Alt16RevCir.Frames
