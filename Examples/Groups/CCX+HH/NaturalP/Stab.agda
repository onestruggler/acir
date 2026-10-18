------------------------------------------------------------------------
-- Presentations of groups
--
-- An affine word that fixes the window commutes with every gate on the
-- window, given completeness on at most eight wires, in the calculus
-- with the schema.
--
-- A gate on the window is `Λw k w`: w on the block, under white
-- controls on the bottom k wires.  An affine word S that fixes every
-- state of the window satisfies S • Λw k w • S⁻¹ ≈ Λw k w (`stab`).
-- By affine completeness S is the word S′ = wₐ c (realise N) • Lfan k L
-- of NaturalP/Window, whose letters commute with Λw k w one by one:
--
-- * a CX or swap between two controls, by Λ-swap-top and `opposite`
--   (the CX is the swap-conjugate of XC = ctrl X);
-- * a fan from a control into the wires above it, which by affine
--   completeness is R⁻¹ • CX • R for a word R on the wires above
--   (R reducing the mask to e₀), hence ctrl (R⁻¹ • X • R) by
--   `conj-ctrl`, and a black control passes a white one (`opposite`);
-- * anything one wire up passes into the white control below it
--   (`under`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base using (ℕ ; _≤_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Examples.Groups.CCX+HH.NaturalP.Syntactics as P
import Examples.Groups.CCX+HH.NaturalP.Schema as S
open import Examples.Groups.CCX+HH.NaturalP.Bridge using (interpret)

module Examples.Groups.CCX+HH.NaturalP.Stab
  (complete≤ : ∀ {k} → k ≤ 8 → ∀ {u v : P.Circuit k} → interpret u ≡ interpret v →
     k S.⊢ u ≈ v)
  where

open import Data.Bool.Base using (Bool ; true ; false ; T ; _xor_ ; _∧_)
open import Data.Bool.Properties using (xor-identityʳ ; ∧-identityʳ ; ∧-zeroʳ)
open import Data.Fin.Base using (Fin ; zero ; suc)
open import Data.Maybe.Base using (just)
open import Data.Nat.Base using (zero ; suc ; _+_ ; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq
  using (refl ; sym ; trans ; cong ; cong₂)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; wmap)
open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)
import Presentation.Base as PB

open import Examples.Groups.CCX+HH.NaturalP.Schema
open import Examples.Groups.CCX+HH.NaturalP.Ctrl using (ctrl ; ctrl⁻)
open import Examples.Groups.CCX+HH.NaturalP.Lambda using (Pos ; Λ)
open import Examples.Groups.CCX+HH.NaturalP.LambdaLaws complete≤ using (under ; Λ-swap-top)
open import Examples.Groups.CCX+HH.NaturalP.CtrlColour complete≤ using (opposite)
open import Examples.Groups.CCX+HH.NaturalP.Controls complete≤ using (conj-ctrl)
open import Examples.Groups.CCX+HH.NaturalP.Affine complete≤
open import Examples.Groups.CCX+HH.NaturalP.AffineRoute
open import Examples.Groups.CCX+HH.NaturalP.Window
open import Examples.Groups.CCX+HH.Decide using (by-eq)
open import Examples.Groups.CCX+HH-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.CCX+HH.GeneralN.Classical as C
open C using (State ; _≈s_ ; lower)
open import Examples.Groups.CCX+HH.GeneralN.ClassicalProperties using (zeros ; e₀)
open import Examples.Groups.CCX+HH.GeneralN.BinaryBasis using (cons)
open import Examples.Groups.CCX+HH.GeneralN.AffineRouting using (NZ ; vec ; View ; is-zero ; is-nonzero ; view)

private
  variable
    n m k c : ℕ

  le : ∀ a → T (a ≤ᵇ 8) → a ≤ 8
  le a p = ≤ᵇ⇒≤ a 8 p

------------------------------------------------------------------------
-- Gates on the window

whites : ∀ k → Vec Pos k
whites zero    = []
whites (suc k) = just false ∷ whites k

Λw : ∀ k → Circuit (₄₊ c) → Circuit (₄₊ (k + c))
Λw k w = Λ (whites k) w

------------------------------------------------------------------------
-- Word algebra

private
  comm-• : ∀ {a b W : Circuit n} → n ⊢ a • W ≈ W • a → n ⊢ b • W ≈ W • b →
    n ⊢ (a • b) • W ≈ W • (a • b)
  comm-• aW bW =
    PB.trans PB.assoc (PB.trans (PB.cong PB.refl bW)
    (PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong aW PB.refl) PB.assoc)))

  comm-ε : ∀ {W : Circuit n} → n ⊢ ε • W ≈ W • ε
  comm-ε = PB.trans PB.left-unit (PB.sym PB.right-unit)

  -- A conjugation that fixes W is a commutation.
  conj⇒comm : ∀ {a a⁻ W : Circuit n} → n ⊢ a • (W • a⁻) ≈ W → n ⊢ a⁻ • a ≈ ε →
    n ⊢ a • W ≈ W • a
  conj⇒comm {a = a} {a⁻} {W} e inv =
    PB.trans (PB.sym PB.right-unit)
    (PB.trans (PB.cong PB.refl (PB.sym inv))
    (PB.trans (PB.sym PB.assoc)
    (PB.trans (PB.cong (PB.trans PB.assoc e) PB.refl) PB.refl)))

  -- A commutation is a conjugation that fixes W.
  comm⇒conj : ∀ {a a⁻ W : Circuit n} → n ⊢ a • W ≈ W • a → n ⊢ a • a⁻ ≈ ε →
    n ⊢ a • (W • a⁻) ≈ W
  comm⇒conj aW inv =
    PB.trans (PB.sym PB.assoc) (PB.trans (PB.cong aW PB.refl)
    (PB.trans PB.assoc (PB.trans (PB.cong PB.refl inv) PB.right-unit)))

  -- Through a white control.
  comm-up : ∀ {x x⁻ Z : Circuit (₄₊ m)} → (₄₊ m) ⊢ x • x⁻ ≈ ε → (₄₊ m) ⊢ x⁻ • x ≈ ε →
    (₄₊ m) ⊢ x • Z ≈ Z • x → suc (₄₊ m) ⊢ x ↑ • ctrl⁻ Z ≈ ctrl⁻ Z • x ↑
  comm-up {x = x} {x⁻} xx⁻ x⁻x xZ =
    conj⇒comm (under (just false) xx⁻ (comm⇒conj xZ xx⁻))
      (lemma-cong↑ (x⁻ • x) ε x⁻x)

  infixr 4 _∙_
  _∙_ : {s t u : State n} → s ≈s t → t ≈s u → s ≈s u
  (e ∙ f) i = trans (e i) (f i)

  ⊕-resp : {s s′ t t′ : State n} → s ≈s s′ → t ≈s t′ → s ⊕ t ≈s s′ ⊕ t′
  ⊕-resp e f i = cong₂ _xor_ (e i) (f i)

  ⌈↑⌉ : (w : Word (AGen n)) → ⌈ w ↑ₐ ⌉ ≡ ⌈ w ⌉ ↑
  ⌈↑⌉ [ g ]ʷ  = refl
  ⌈↑⌉ ε       = refl
  ⌈↑⌉ (u • v) = cong₂ _•_ (⌈↑⌉ u) (⌈↑⌉ v)

------------------------------------------------------------------------
-- Facts on two wires

private
  opaque
    unfolding _+ᴰ_ _*ᴰ_ -ᴰ_

    CX-σ₀ : 2 ⊢ CX ≈ σ • (XC • σ)
    CX-σ₀ = complete≤ (le 2 tt) {u = CX} {v = σ • (XC • σ)} (by-eq tt)

    cx01-XC₀ : 2 ⊢ σ • (CX • σ) ≈ XC
    cx01-XC₀ = complete≤ (le 2 tt) {u = σ • (CX • σ)} {v = XC} (by-eq tt)

  CX-σ : ∀ j → (₂₊ j) ⊢ CX ≈ σ • (XC • σ)
  CX-σ j = widen j CX-σ₀

  cx01-XC : ∀ j → (₂₊ j) ⊢ ⌈ cx01 ⌉ ≈ XC
  cx01-XC j = widen j cx01-XC₀

------------------------------------------------------------------------
-- Two white controls

private
  σ-WW : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ σ • ctrl⁻ (ctrl⁻ Y) ≈ ctrl⁻ (ctrl⁻ Y) • σ
  σ-WW Y = conj⇒comm (Λ-swap-top (just false) (just false) Y) (PB.axiom (srel (σrel σ-inv)))

  XC-WW : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ XC • ctrl⁻ (ctrl⁻ Y) ≈ ctrl⁻ (ctrl⁻ Y) • XC
  XC-WW Y = opposite X (ctrl⁻ Y)

  CX-WW : (Y : Circuit (₄₊ m)) → (₂₊ (₄₊ m)) ⊢ CX • ctrl⁻ (ctrl⁻ Y) ≈ ctrl⁻ (ctrl⁻ Y) • CX
  CX-WW {m} Y =
    PB.trans (PB.cong (CX-σ (₄₊ m)) PB.refl)
    (PB.trans (comm-• (σ-WW Y) (comm-• (XC-WW Y) (σ-WW Y)))
      (PB.cong PB.refl (PB.sym (CX-σ (₄₊ m)))))

------------------------------------------------------------------------
-- Words on the controls

gate-comm : (g : AGen k) → LinG g → (w : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ ⌈ [ wg c g ]ʷ ⌉ • Λw k w ≈ Λw k w • ⌈ [ wg c g ]ʷ ⌉
gate-comm {₂₊ k} acx lg-cx w = CX-WW (Λw k w)
gate-comm {₂₊ k} asw lg-sw w = σ-WW (Λw k w)
gate-comm {suc k} {c} (g ↥ₐ) (lg-up p) w =
  comm-up (inv-r [ wg c g ]ʷ) (inv-r [ wg c g ]ʷ) (gate-comm g p w)

word-comm : (u : Word (AGen k)) → LinW u → (w : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ ⌈ wₐ c u ⌉ • Λw k w ≈ Λw k w • ⌈ wₐ c u ⌉
word-comm [ g ]ʷ  (lw-g p)   w = gate-comm g p w
word-comm ε       lw-ε       w = comm-ε
word-comm (u • v) (lw-• p q) w = comm-• (word-comm u p w) (word-comm v q w)

------------------------------------------------------------------------
-- Fans from a control

private
  -- The CX from wire 0 into wire 1.
  cx01-act : (y : State (suc (suc n))) →
    A⟦ cx01 ⟧ y ≈s cons (y zero) (cons (y (suc zero) xor y zero) (lower (lower y)))
  cx01-act y zero          = refl
  cx01-act y (suc zero)    = refl
  cx01-act y (suc (suc i)) = refl

  -- R⁻¹ • CX • R, which adds wire 0 into the wires of R⁻¹(e₀).
  fanR : (v : NZ (₄₊ m)) → Word (AGen (suc (₄₊ m)))
  fanR v = inv (reduceA v) ↑ₐ • (cx01 • (reduceA v ↑ₐ))

  fanR-ctrl : (v : NZ (₄₊ m)) →
    suc (₄₊ m) ⊢ ⌈ fanR v ⌉ ≈ ctrl (⌈ inv (reduceA v) ⌉ • (X • ⌈ reduceA v ⌉))
  fanR-ctrl {m} v =
    PB.trans (Eq.subst (λ x → _ ⊢ ⌈ fanR v ⌉ ≈ x)
                (cong₂ _•_ (⌈↑⌉ (inv R)) (cong (⌈ cx01 ⌉ •_) (⌈↑⌉ R))) PB.refl)
    (PB.trans (PB.cong PB.refl (PB.cong (cx01-XC (₃₊ m)) PB.refl))
      (conj-ctrl ⌈ inv R ⌉ X ⌈ R ⌉ (inv-l R)))
    where
    R = reduceA v

  fanR-act : (v : NZ (₄₊ m)) (mask : State (₄₊ m)) → vec v ≈s mask →
    ∀ x → A⟦ fanR v ⟧ x ≈s cons (x zero) (lower x ⊕ scale (x zero) mask)
  fanR-act v mask vm x =
    A-cong (inv R ↑ₐ) (A-cong cx01 step₁ ∙ cx01-act (cons x₀ y) ∙ step₂)
    ∙ A-↑ (inv R) x₀ z ∙ step₃
    where
    R = reduceA v
    x₀ = x zero
    y = A⟦ R ⟧ (lower x)
    z = y ⊕ scale x₀ e₀
    cv : cons x₀ (lower x) ≈s x
    cv zero    = refl
    cv (suc _) = refl
    step₁ : A⟦ R ↑ₐ ⟧ x ≈s cons x₀ y
    step₁ = A-cong (R ↑ₐ) (λ i → sym (cv i)) ∙ A-↑ R x₀ (lower x)
    step₂ : cons x₀ (cons (y zero xor x₀) (lower y)) ≈s cons x₀ z
    step₂ zero          = refl
    step₂ (suc zero)    = refl
    step₂ (suc (suc i)) = sym (xor-identityʳ (y (suc i)))
    IL : Lin A⟦ inv R ⟧
    IL = word-lin (inv R)
      (λ i → trans (A-cong (inv R) (λ j → sym (reduceA-zero v j)) i) (A-inv R zeros i))
    inv-e₀ : A⟦ inv R ⟧ e₀ ≈s mask
    inv-e₀ = A-cong (inv R) (λ i → sym (reduceA-vec v i)) ∙ A-inv R (vec v) ∙ vm
    sc : ∀ b → A⟦ inv R ⟧ (scale b e₀) ≈s scale b mask
    sc true  j = trans (Lin.resp IL (λ l → ∧-identityʳ (e₀ l)) j)
                   (trans (inv-e₀ j) (sym (∧-identityʳ (mask j))))
    sc false j = trans (Lin.resp IL (λ l → ∧-zeroʳ (e₀ l)) j)
                   (trans (lin-zero IL j) (sym (∧-zeroʳ (mask j))))
    step₃ : cons x₀ (A⟦ inv R ⟧ z) ≈s cons x₀ (lower x ⊕ scale x₀ mask)
    step₃ zero    = refl
    step₃ (suc i) = (Lin.add IL y (scale x₀ e₀) ∙ ⊕-resp (A-inv R (lower x)) (sc x₀)) i

fan01-comm : (mask : State (₄₊ m)) (Z : Circuit (₄₊ m)) →
  suc (₄₊ m) ⊢ ⌈ fan01 mask ⌉ • ctrl⁻ Z ≈ ctrl⁻ Z • ⌈ fan01 mask ⌉
fan01-comm {m} mask Z = by-view (view (₄₊ m) mask)
  where
  by-view : View mask → suc (₄₊ m) ⊢ ⌈ fan01 mask ⌉ • ctrl⁻ Z ≈ ctrl⁻ Z • ⌈ fan01 mask ⌉
  by-view (is-zero z) =
    PB.trans (PB.cong (affine-complete (fan01 mask) ε (act⇒interpret (fan01 mask) ε id-act)) PB.refl)
      (PB.trans comm-ε (PB.cong PB.refl (PB.sym (affine-complete (fan01 mask) ε
        (act⇒interpret (fan01 mask) ε id-act)))))
    where
    id-act : ∀ s → A⟦ fan01 mask ⟧ s ≈s A⟦ ε ⟧ s
    id-act s i = trans (fan01-act mask s i) (at i)
      where
      at : ∀ i → cons (s zero) (lower s ⊕ scale (s zero) mask) i ≡ s i
      at zero    = refl
      at (suc j) = trans (cong (λ b → s (suc j) xor (b ∧ s zero)) (z j)) (xor-identityʳ _)
  by-view (is-nonzero v vm) =
    PB.trans (PB.cong eq PB.refl) (PB.trans (opposite U Z) (PB.cong PB.refl (PB.sym eq)))
    where
    U = ⌈ inv (reduceA v) ⌉ • (X • ⌈ reduceA v ⌉)
    eq : suc (₄₊ m) ⊢ ⌈ fan01 mask ⌉ ≈ ctrl U
    eq = PB.trans (affine-complete (fan01 mask) (fanR v)
                    (act⇒interpret (fan01 mask) (fanR v)
                      (λ s i → trans (fan01-act mask s i) (sym (fanR-act v mask vm s i)))))
           (fanR-ctrl v)

Lfan-comm : ∀ k (L : State k → State (₄₊ c)) (w : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ ⌈ Lfan k L ⌉ • Λw k w ≈ Λw k w • ⌈ Lfan k L ⌉
Lfan-comm zero    L w = comm-ε
Lfan-comm {c} (suc k) L w =
  comm-• (Eq.subst (λ x → _ ⊢ x • Λw (suc k) w ≈ Λw (suc k) w • x) (sym (⌈↑⌉ F))
            (comm-up (inv-r F) (inv-l F) (Lfan-comm k L′ w)))
    (fan01-comm (join k zeros (L e₀)) (Λw k w))
  where
  L′ : State k → State (₄₊ c)
  L′ a = L (cons false a)
  F = Lfan k L′

------------------------------------------------------------------------
-- The stabiliser of the window

stab : ∀ k c (S : Word (AGen (₄₊ (k + c)))) →
  (∀ x → low {c} k x ≈s zeros → A⟦ S ⟧ x ≈s x) → (w : Circuit (₄₊ c)) →
  (₄₊ (k + c)) ⊢ ⌈ S ⌉ • (Λw k w • ⌈ inv S ⌉) ≈ Λw k w
stab k c S fixW w =
  PB.trans (PB.cong SS′ PB.refl)
  (PB.trans (PB.sym PB.assoc)
  (PB.trans (PB.cong (comm-• (word-comm (realise N-emb) (realise-lin N-emb) w)
                              (Lfan-comm k L w)) PB.refl)
  (PB.trans (PB.cong (PB.cong PB.refl (PB.sym SS′)) PB.refl)
  (PB.trans PB.assoc
  (PB.trans (PB.cong PB.refl (inv-r S)) PB.right-unit)))))
  where
  open Fix {k} {c} S fixW
  SS′ : (₄₊ (k + c)) ⊢ ⌈ S ⌉ ≈ ⌈ S′ ⌉
  SS′ = affine-complete S S′ (act⇒interpret S S′ (λ x i → sym (S′-act x i)))
