------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of controlled circuits: ctrl C acts as C controlled by
-- wire 0, at every width from five wires on.
--
-- A gadget at the bottom of the circuit is checked on its own wires
-- (NaturalP.CtrlBase, NaturalP.CtrlBase5) and carried up by idle
-- wires on top, which commute with the control (`lift`,
-- Blocks2.top-ctrl).  A gate one wire up is the gadget conjugated by
-- the swap of wires 0 1, which moves its control from wire 1 to wire 0
-- (SwapBlocks.swap-ctrl); each further wire up conjugates by the swaps
-- of wires 1 2 and 0 1, the first moving the control down and the
-- second passing what is idle on both wires (`CTRL₁-sem`).  The
-- control is a homomorphism, so the gates assemble into circuits
-- (`ctrl-sem`).
--
-- Two spellings of one operator are never compared here: Agda compares
-- them by unfolding both through every gate, which branches at each
-- gate.  So every change of spelling is an equation of words (`via`),
-- and every cong is given its endpoints.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.NaturalP.CtrlSem where

open import Data.Nat.Base using (ℕ ; zero ; suc ; _^_)
open import Relation.Binary.PropositionalEquality
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (isCommutativeRing-D ; adj-D ; ½ᴰ)
open import Examples.Groups.CCX+HH.EncodingSemantics.Blocks isCommutativeRing-D adj-D ½ᴰ
  using (parallel ; parallel-cong ; parallel-id ; parallel-compose)
open import Examples.Groups.CCX+HH.EncodingSemantics.Binary using (alternating ; contiguous)
import Examples.Groups.CCX+HH.EncodingSemantics.Interchange as Interchange
import Examples.Groups.CCX+HH.Semantics as Q
import Examples.Groups.CCX+HH.Syntactics as H
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (τ ; τg ; τ-↑)
open import Examples.Groups.CCX+HH.NaturalP.Ctrl
open import Examples.Groups.CCX+HH.NaturalP.CtrlBase
open import Examples.Groups.CCX+HH.NaturalP.CtrlBase5
open import Examples.Groups.CCX+HH.NaturalP.Blocks2 using (Op ; ctrlA ; topA ; top-ctrl)
open import Examples.Groups.CCX+HH.NaturalP.SwapBlocks
  using (swap-ctrl ; swap-idle ; swap-invol)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalSemantics
  using (quantum ; quantum-shift ; swap ; swap-correct)
open import Examples.Groups.CCX+HH.GeneralN.ShiftSemantics using (top-correct)

private
  module I = Interchange isCommutativeRing-D adj-D ½ᴰ

  variable
    n m : ℕ

------------------------------------------------------------------------
-- Changing the spelling of a circuit

private
  -- Two spellings of one word: the equation is checked on the words,
  -- never on their actions (comparing two actions makes Agda evaluate
  -- them on a symbolic vector).
  via : ∀ {k} (w w′ : H.Circuit k) → w ≡ w′ → ∀ {R : Op (2 ^ k)} →
    (∀ v → quantum w′ v ≡ R v) → ∀ v → quantum w v ≡ R v
  via w w′ e h v = trans (cong (λ u → quantum u v) {x = w} {y = w′} e) (h v)

------------------------------------------------------------------------
-- Idle wires on top

private
  -- w′ and g′ are w and g with an idle wire on top.
  lift : (w : H.Circuit (suc n)) (w′ : H.Circuit (₂₊ n)) → w′ ≡ w H.⇓ →
    (g : H.Circuit n) (g′ : H.Circuit (suc n)) → g′ ≡ g H.⇓ →
    (∀ v → quantum w v ≡ ctrlA (2 ^ n) (quantum g) v) →
    ∀ v → quantum w′ v ≡ ctrlA (2 ^ suc n) (quantum g′) v
  lift {n} w w′ e g g′ e′ ih = via w′ (w H.⇓) e λ v →
    trans (top-correct w v)
    (trans (parallel-cong (contiguous (2 ^ suc n))
             {f = quantum w} {f′ = ctrlA (2 ^ n) (quantum g)}
             {g = quantum w} {g′ = ctrlA (2 ^ n) (quantum g)} ih ih v)
    (trans (top-ctrl (2 ^ n) (quantum g) v)
      (parallel-cong (alternating (2 ^ suc n))
        {f = λ x → x} {f′ = λ x → x}
        {g = topA (2 ^ n) (quantum g)} {g′ = quantum g′}
        (λ _ → refl) (λ x → sym (via g′ (g H.⇓) e′ (top-correct g) x)) v)))

------------------------------------------------------------------------
-- The gadgets at every width

XC-sem : ∀ k v → quantum (H.XC {k}) v ≡ ctrlA (2 ^ suc k) (quantum (H.X {k})) v
XC-sem zero    = XC-base
XC-sem (suc k) = lift (H.XC {k}) (H.XC {suc k}) refl (H.X {k}) (H.X {suc k}) refl (XC-sem k)

CCXc-sem : ∀ k v → quantum (τ (CCXc {k})) v ≡ ctrlA (2 ^ ₂₊ k) (quantum (H.CX {k})) v
CCXc-sem zero    = CCXc-base
CCXc-sem (suc k) =
  lift (τ (CCXc {k})) (τ (CCXc {suc k})) refl (H.CX {k}) (H.CX {suc k}) refl (CCXc-sem k)

Fredkin-sem : ∀ k v → quantum (τ (Fredkin {k})) v ≡ ctrlA (2 ^ ₂₊ k) (quantum (H.Ex {k})) v
Fredkin-sem zero    = Fredkin-base
Fredkin-sem (suc k) =
  lift (τ (Fredkin {k})) (τ (Fredkin {suc k})) refl (H.Ex {k}) (H.Ex {suc k}) refl (Fredkin-sem k)

CHHa-sem : ∀ k v → quantum (τ (CHHa {k})) v ≡ ctrlA (2 ^ ₃₊ k) (quantum (H.HH {suc k})) v
CHHa-sem zero    = CHHa-base
CHHa-sem (suc k) =
  lift (τ (CHHa {k})) (τ (CHHa {suc k})) refl (H.HH {suc k}) (H.HH {₂₊ k}) refl (CHHa-sem k)

CHHb-sem : ∀ k v → quantum (τ (CHHb {k})) v ≡ ctrlA (2 ^ ₃₊ k) (quantum (H.HH {k} H.↑)) v
CHHb-sem zero    = CHHb-base
CHHb-sem (suc k) =
  lift (τ (CHHb {k})) (τ (CHHb {suc k})) refl (H.HH {k} H.↑) (H.HH {suc k} H.↑) refl (CHHb-sem k)

C3Xa-sem : ∀ k v → quantum (τ (C3Xa {k})) v ≡ ctrlA (2 ^ ₄₊ k) (quantum (H.CCX {suc k})) v
C3Xa-sem zero    = C3Xa-base
C3Xa-sem (suc k) =
  lift (τ (C3Xa {k})) (τ (C3Xa {suc k})) refl (H.CCX {suc k}) (H.CCX {₂₊ k}) refl (C3Xa-sem k)

C3Xb-sem : ∀ k v → quantum (τ (C3Xb {k})) v ≡ ctrlA (2 ^ ₄₊ k) (quantum (H.CCX {k} H.↑)) v
C3Xb-sem zero    = C3Xb-base
C3Xb-sem (suc k) =
  lift (τ (C3Xb {k})) (τ (C3Xb {suc k})) refl (H.CCX {k} H.↑) (H.CCX {suc k} H.↑) refl (C3Xb-sem k)

------------------------------------------------------------------------
-- The swaps

-- Conjugating by the swap of wires 0 1 moves the control down.
conj₀ : ∀ k (w : H.Circuit (suc k)) (G : Op (2 ^ k)) →
  (∀ v → quantum w v ≡ ctrlA (2 ^ k) G v) →
  ∀ v → quantum (H.Ex {k} • w H.↑ • H.Ex {k}) v ≡ ctrlA (2 ^ suc k) (Q.bottom {k} G) v
conj₀ k w G h v =
  trans (swap-correct k (quantum (w H.↑) (quantum (H.Ex {k}) v)))
  (trans (cong (swap k)
    (trans (quantum-shift w (quantum (H.Ex {k}) v))
      (parallel-cong (alternating (2 ^ suc k))
        {f = quantum w} {f′ = ctrlA (2 ^ k) G} {g = quantum w} {g′ = ctrlA (2 ^ k) G}
        h h (quantum (H.Ex {k}) v))))
  (trans (cong (λ y → swap k (Q.bottom {suc k} (ctrlA (2 ^ k) G) y)) (swap-correct k v))
    (swap-ctrl k G v)))

private
  -- Conjugating by the swap of wires 1 2 passes the control and what is
  -- idle on wires 1 2.
  conj₁ : ∀ k (G : Op (2 ^ k)) v →
    Q.bottom {₂₊ k} (swap k)
      (ctrlA (2 ^ ₂₊ k) (Q.bottom {suc k} (Q.bottom {k} G)) (Q.bottom {₂₊ k} (swap k) v))
    ≡ ctrlA (2 ^ ₂₊ k) (Q.bottom {suc k} (Q.bottom {k} G)) v
  conj₁ k G v =
    trans (cong (parallel p (swap k) (swap k))
            (parallel-compose p (λ x → x) B (swap k) (swap k) v))
    (trans (parallel-compose p (swap k) (swap k) (λ x → swap k x) (λ x → B (swap k x)) v)
      (parallel-cong p {f = λ x → swap k (swap k x)} {f′ = λ x → x}
        {g = λ x → swap k (B (swap k x))} {g′ = B}
        (swap-invol k) (swap-idle k G) v))
    where
    p = alternating (2 ^ ₂₊ k)
    B = Q.bottom {suc k} (Q.bottom {k} G)

  -- An operator one wire up, read off its circuit.
  shifted : ∀ k (w : H.Circuit k) v → Q.bottom {k} (quantum w) v ≡ quantum (w H.↑) v
  shifted k w v = sym (quantum-shift w v)

  -- The action of a conjugate, unfolded (proved for variable words).
  unfold₅ : ∀ {k} (A B C : H.Circuit k) x →
    quantum ((A • B) • C • (B • A)) x ≡ quantum A (quantum B (quantum C (quantum B (quantum A x))))
  unfold₅ A B C x = refl

  -- ctrlA of equal operators.
  ctrl-cong : ∀ M {F F′ : Op M} → (∀ x → F x ≡ F′ x) → ∀ v → ctrlA M F v ≡ ctrlA M F′ v
  ctrl-cong M {F} {F′} e v =
    parallel-cong (alternating M) {f = λ x → x} {f′ = λ x → x} {g = F} {g′ = F′} (λ _ → refl) e v

------------------------------------------------------------------------
-- Gates one wire up: wire 1 spare

CTRL₁-sem : (g : P.Gen m) → ∀ v →
  quantum (τ (CTRL₁ g)) v ≡ ctrlA (2 ^ suc m) (Q.bottom {m} (quantum (τg g))) v
CTRL₁-sem (P.gate₀ ())
CTRL₁-sem (P.gate₁ {k} P.X-gate) =
  via (τ (CTRL₁ (P.gate₁ {k} P.X-gate))) (H.Ex {suc k} • H.XC {k} H.↑ • H.Ex {suc k}) refl
    (conj₀ (suc k) (H.XC {k}) (quantum (H.X {k})) (XC-sem k))
CTRL₁-sem (P.gate₂ {k} P.CX-gate) =
  via (τ (CTRL₁ (P.gate₂ {k} P.CX-gate))) (H.Ex {₂₊ k} • τ (CCXc {k}) H.↑ • H.Ex {₂₊ k}) refl
    (conj₀ (₂₊ k) (τ (CCXc {k})) (quantum (H.CX {k})) (CCXc-sem k))
CTRL₁-sem (P.gate₂ {k} P.SW-gate) =
  via (τ (CTRL₁ (P.gate₂ {k} P.SW-gate))) (H.Ex {₂₊ k} • τ (Fredkin {k}) H.↑ • H.Ex {₂₊ k}) refl
    (conj₀ (₂₊ k) (τ (Fredkin {k})) (quantum (H.Ex {k})) (Fredkin-sem k))
CTRL₁-sem (P.gate₂ {k} P.HH-gate) v =
  trans (CHHb-sem k v) (ctrl-cong (2 ^ ₃₊ k) (λ x → quantum-shift (H.HH {k}) x) v)
CTRL₁-sem (P.gate₃ {k} P.CCX-gate) v =
  trans (C3Xb-sem k v) (ctrl-cong (2 ^ ₄₊ k) (λ x → quantum-shift (H.CCX {k}) x) v)
CTRL₁-sem (P._↥ {k} g) v =
  -- the swap of wires 1 2, then of wires 0 1, around the gate one wire up
  trans e₁ (trans e₂ (trans e₃ (trans e₄ (trans e₅ (trans e₆ (trans e₇ e₈))))))
  where
  -- No operator is abbreviated in a type below, and every cong is given
  -- its endpoints: two spellings of one operator, or an endpoint found
  -- by unification, are compared by unfolding both through every gate.
  G = quantum (τg g)
  B₁ = Q.bottom {k} G
  S12 = Q.bottom {₂₊ k} (swap k)
  y₀ = S12 v
  y₁ = swap (suc k) y₀
  y₂ = Q.bottom {₂₊ k} (ctrlA (2 ^ suc k) B₁) y₁
  y₃ = ctrlA (2 ^ ₂₊ k) (Q.bottom {suc k} B₁) y₀

  -- the swap of wires 1 2
  S₁₂ : ∀ x → quantum (H.Ex {k} H.↑) x ≡ S12 x
  S₁₂ x = trans (quantum-shift (H.Ex {k}) x)
    (parallel-cong (alternating (2 ^ ₂₊ k)) {f = quantum (H.Ex {k})} {f′ = swap k}
      {g = quantum (H.Ex {k})} {g′ = swap k} (swap-correct k) (swap-correct k) x)

  e₁ : quantum (τ (CTRL₁ (g P.↥))) v
     ≡ quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k})
         (quantum (τ (CTRL₁ g P.↑)) (quantum (H.Ex {suc k}) y₀)))
  e₁ = trans (cong (λ u → quantum u v) {x = τ (CTRL₁ (g P.↥))} {y = W} refl)
    (trans (unfold₅ (H.Ex {k} H.↑) (H.Ex {suc k}) (τ (CTRL₁ g P.↑)) v)
      (cong (λ y → quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k})
                    (quantum (τ (CTRL₁ g P.↑)) (quantum (H.Ex {suc k}) y))))
        {x = quantum (H.Ex {k} H.↑) v} {y = y₀} (S₁₂ v)))
    where
    W = (H.Ex {k} H.↑ • H.Ex {suc k}) • τ (CTRL₁ g P.↑) • (H.Ex {suc k} • H.Ex {k} H.↑)

  e₂ : quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k})
         (quantum (τ (CTRL₁ g P.↑)) (quantum (H.Ex {suc k}) y₀)))
     ≡ quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k}) (quantum (τ (CTRL₁ g P.↑)) y₁))
  e₂ = cong (λ y → quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k}) (quantum (τ (CTRL₁ g P.↑)) y)))
    {x = quantum (H.Ex {suc k}) y₀} {y = y₁} (swap-correct (suc k) y₀)

  e₃ : quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k}) (quantum (τ (CTRL₁ g P.↑)) y₁))
     ≡ quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k}) y₂)
  e₃ = cong (λ y → quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k}) y))
    {x = quantum (τ (CTRL₁ g P.↑)) y₁} {y = y₂}
    (trans (cong (λ w → quantum w y₁) {x = τ (CTRL₁ g P.↑)} {y = τ (CTRL₁ g) H.↑} (τ-↑ (CTRL₁ g)))
    (trans (quantum-shift (τ (CTRL₁ g)) y₁)
      (parallel-cong (alternating (2 ^ ₂₊ k))
        {f = quantum (τ (CTRL₁ g))} {f′ = ctrlA (2 ^ suc k) B₁}
        {g = quantum (τ (CTRL₁ g))} {g′ = ctrlA (2 ^ suc k) B₁}
        (CTRL₁-sem g) (CTRL₁-sem g) y₁)))

  e₄ : quantum (H.Ex {k} H.↑) (quantum (H.Ex {suc k}) y₂)
     ≡ quantum (H.Ex {k} H.↑) (swap (suc k) y₂)
  e₄ = cong (quantum (H.Ex {k} H.↑)) {x = quantum (H.Ex {suc k}) y₂} {y = swap (suc k) y₂}
    (swap-correct (suc k) y₂)

  e₅ : quantum (H.Ex {k} H.↑) (swap (suc k) y₂) ≡ quantum (H.Ex {k} H.↑) y₃
  e₅ = cong (quantum (H.Ex {k} H.↑)) {x = swap (suc k) y₂} {y = y₃} (swap-ctrl (suc k) B₁ y₀)

  e₆ : quantum (H.Ex {k} H.↑) y₃ ≡ S12 y₃
  e₆ = S₁₂ y₃

  e₇ : S12 y₃ ≡ ctrlA (2 ^ ₂₊ k) (Q.bottom {suc k} B₁) v
  e₇ = conj₁ k G v

  e₈ : ctrlA (2 ^ ₂₊ k) (Q.bottom {suc k} B₁) v
     ≡ ctrlA (2 ^ ₂₊ k) (Q.bottom {suc k} (quantum (τg (g P.↥)))) v
  e₈ = ctrl-cong (2 ^ ₂₊ k)
    (parallel-cong (alternating (2 ^ suc k))
      {f = B₁} {f′ = quantum (τg g H.↑)} {g = B₁} {g′ = quantum (τg g H.↑)}
      (shifted k (τg g)) (shifted k (τg g))) v

------------------------------------------------------------------------
-- Gates and circuits on five or more wires

CTRL-sem : (g : P.Gen (₄₊ n)) → ∀ v →
  quantum (τ (CTRL g)) v ≡ ctrlA (2 ^ ₄₊ n) (quantum (τg g)) v
CTRL-sem (P.gate₀ ())
CTRL-sem {n} (P.gate₁ P.X-gate)   =
  via (τ (CTRL (P.gate₁ {₃₊ n} P.X-gate))) (H.XC {₃₊ n}) refl (XC-sem (₃₊ n))
CTRL-sem {n} (P.gate₂ P.CX-gate)  = CCXc-sem (₂₊ n)
CTRL-sem {n} (P.gate₂ P.SW-gate)  = Fredkin-sem (₂₊ n)
CTRL-sem {n} (P.gate₂ P.HH-gate)  = CHHa-sem (suc n)
CTRL-sem {n} (P.gate₃ P.CCX-gate) = C3Xa-sem n
CTRL-sem {n} (g P.↥) v = trans (CTRL₁-sem g v)
  (ctrl-cong (2 ^ ₄₊ n) (shifted (₃₊ n) (τg g)) v)

ctrl-sem : (C : P.Circuit (₄₊ n)) → ∀ v →
  quantum (τ (ctrl C)) v ≡ ctrlA (2 ^ ₄₊ n) (quantum (τ C)) v
ctrl-sem [ g ]ʷ = CTRL-sem g
ctrl-sem {n} ε v = sym (parallel-id (alternating (2 ^ ₄₊ n)) v)
ctrl-sem {n} (u • w) v =
  trans (cong (quantum (τ (ctrl u))) (ctrl-sem w v))
  (trans (ctrl-sem u (ctrlA (2 ^ ₄₊ n) (quantum (τ w)) v))
    (parallel-compose (alternating (2 ^ ₄₊ n))
      (λ x → x) (quantum (τ u)) (λ x → x) (quantum (τ w)) v))
