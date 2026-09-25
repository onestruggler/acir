------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled forms: a general-width gate as a payload on its bottom
-- wires, chosen by its controls on the top ones
--
-- Lemma 5.1, completeness one width down, needs the two sides of a
-- derivation step to have the same semantics at a symbolic width.  In
-- the general-n derivations every gate has its explicit wires at the
-- bottom and, above them, either nothing or the whole block of the
-- remaining wires as black controls (the paper's dashed series).  So
-- the operator of a step is ctrl A B allT: A on the bottom j wires when
-- the top m are all set, B otherwise.  `CF w` records that form for a
-- circuit w,
--
--     √2^ e · ⟦ w ⟧ₒ  ≐  √2^ (len w) · ctrl (ix A) (ix B) allT,
--
-- with A and B stored j-wire matrices: the operator w denotes is
-- (1/√2)^e · ctrl A B allT.  A local circuit has it with A = B its
-- stored matrix and e its length (`cf-loc`), the box with A its phase
-- on the bottom wires and e = 0 (`cf-box`), and it is closed under
-- products (`cf-•`) and under shifting up a wire (`cf-↑`).  Since the
-- symbolic lengths sit on the right, two forms are compared by their
-- payloads alone (`cf-~`): √2^ e′ · A = √2^ e · A′ is a closed identity
-- of tries, the exponents being sums of lengths of closed circuits.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.CForm where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Bool.Properties using (∧-zeroʳ ; ∧-assoc)
open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Nat.Solver using (module +-*-Solver)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
open import Examples.Groups.Real-Clifford+CH.Semantics.Decide using (eqM ; eqM-sound)
open import Examples.Groups.Real-Clifford+CH.Evaluation using (⟦_⟧R ; ⟦⟧R≡⟦⟧M)
open import Examples.Groups.Real-Clifford+CH.Soundness.Operators
  using (ctrl ; ctrl-⊙ ; ctrl-cong ; ctrl-· ; emb-ctrl ; allT ; sgn ; phase ; diag ; up-·)
open import Examples.Groups.Real-Clifford+CH.Soundness.Box using (Λ□-sem)

open +-*-Solver using (solve ; _:+_ ; _:=_)

private
  variable
    j m : ℕ

------------------------------------------------------------------------
-- The form

record CF {j m : ℕ} (w : Circuit (j +ℕ m)) : Set where
  constructor cf
  field
    e    : ℕ
    A B  : Mat j
    form : (√2^ e · ⟦ w ⟧ₒ) ≐ (√2^ len w · ctrl (ix A) (ix B) (allT {m}))

------------------------------------------------------------------------
-- Products

cf-• : {u v : Circuit (j +ℕ m)} → CF {j} {m} u → CF {j} {m} v → CF {j} {m} (u • v)
cf-• {j} {m} {u} {v} (cf e₁ A₁ B₁ f₁) (cf e₂ A₂ B₂ f₂) =
  cf (e₁ +ℕ e₂) (mulM A₁ A₂) (mulM B₁ B₂)
     (≐-trans (·-cong (√2^-+ e₁ e₂) (⟦⟧ₒ-• u v))
     (≐-trans (≐-sym (·-⊙ (√2^ e₁) (√2^ e₂) ⟦ u ⟧ₒ ⟦ v ⟧ₒ))
     (≐-trans (⊙-cong f₁ f₂)
     (≐-trans (·-⊙ (√2^ len u) (√2^ len v) (ctrl (ix A₁) (ix B₁) allT) (ctrl (ix A₂) (ix B₂) allT))
              (·-cong (Eq.sym (√2^-+ (len u) (len v)))
                (≐-trans (ctrl-⊙ (ix A₁) (ix A₂) (ix B₁) (ix B₂) allT)
                         (ctrl-cong (≐-sym (ix-mul A₁ A₂)) (≐-sym (ix-mul B₁ B₂)))))))))

------------------------------------------------------------------------
-- Local circuits: the same payload on both branches

-- The stored matrix given as a literal (GeneralN.Locals), so that
-- products of payloads never recompute it.
cf-loc′ : (c : Circuit j) (M : Mat j) → ⟦ c ⟧M ≡ M → CF {j} {m} (c ↓ᵏ m)
cf-loc′ {j} {m} c M e = cf (len c) M M
  (·-cong (Eq.cong √2^_ (Eq.sym (len-↓ᵏ c)))
    (≐-trans (localise c)
    (≐-trans (tensor-cong (ix-≡ e) (≐-refl Idₒ)) (emb-ctrl M allT))))

-- Read by row operations (Evaluation), which is several times cheaper
-- to evaluate than the dense ⟦ c ⟧M.
cf-loc : (c : Circuit j) → CF {j} {m} (c ↓ᵏ m)
cf-loc c = cf-loc′ c ⟦ c ⟧R (Eq.sym (⟦⟧R≡⟦⟧M c))

------------------------------------------------------------------------
-- One wire up: the new bottom wire joins the payload

up-ctrl : (A B : Op j) (p : Bits m → Bool) →
          up (ctrl A B p) ≐ ctrl {suc j} (tensor (Idₒ {1}) A) (tensor (Idₒ {1}) B) p
up-ctrl A B p (a ∷ x) (b ∷ y) = Eq.sym (ctrl-· (δb (a ∷ []) (b ∷ [])) A B p x y)

cf-↑ : {w : Circuit (j +ℕ m)} → CF {j} {m} w → CF {suc j} {m} (w ↑)
cf-↑ {j} {m} {w} (cf e A B f) =
  cf e (tenM (idM {1}) A) (tenM (idM {1}) B)
    (≐-trans (·-cong Eq.refl (up-word w))
    (≐-trans (≐-sym (up-· (√2^ e) ⟦ w ⟧ₒ))
    (≐-trans (up-cong f)
    (≐-trans (up-· (√2^ len w) (ctrl (ix A) (ix B) allT))
             (·-cong (Eq.cong √2^_ (Eq.sym (len-↑ w)))
               (≐-trans (up-ctrl (ix A) (ix B) allT)
                        (ctrl-cong (≐-sym (pad A)) (≐-sym (pad B)))))))))
  where
  pad : (M : Mat j) → ix (tenM (idM {1}) M) ≐ tensor (Idₒ {1}) (ix M)
  pad M = ≐-trans (ix-tenM (idM {1}) M) (tensor-cong (ix-id {1}) (≐-refl (ix M)))

------------------------------------------------------------------------
-- The box

-- A diagonal payload under the top block, as one diagonal operator.
ctrlPh : (j : ℕ) → (Bits j → 𝔽) → Bits (j +ℕ m) → 𝔽
ctrlPh zero    f x       = if allT x then f [] else 1#
ctrlPh (suc j) f (a ∷ x) = ctrlPh j (λ u → f (a ∷ u)) x

private
  ctrlPh-cong : (j : ℕ) {f g : Bits j → 𝔽} → (∀ u → f u ≡ g u) →
                (x : Bits (j +ℕ m)) → ctrlPh j f x ≡ ctrlPh j g x
  ctrlPh-cong zero    e x       = Eq.cong (λ z → if allT x then z else 1#) (e [])
  ctrlPh-cong (suc j) e (a ∷ x) = ctrlPh-cong j (λ u → e (a ∷ u)) x

  -- A controlled operator with vanishing payloads vanishes.
  ctrl-0 : (A B : Op j) (p : Bits m → Bool) →
           (∀ u v → A u v ≡ 0#) → (∀ u v → B u v ≡ 0#) → ∀ x y → ctrl A B p x y ≡ 0#
  ctrl-0 {zero} A B p eA eB x y = go (p x)
    where
    go : (b : Bool) → (if b then A [] [] else B [] []) * δb x y ≡ 0#
    go true  = Eq.trans (Eq.cong (_* δb x y) (eA [] [])) (*-zeroˡ (δb x y))
    go false = Eq.trans (Eq.cong (_* δb x y) (eB [] [])) (*-zeroˡ (δb x y))
  ctrl-0 {suc j} A B p eA eB (a ∷ x) (b ∷ y) =
    ctrl-0 {j} (λ u v → A (a ∷ u) (b ∷ v)) (λ u v → B (a ∷ u) (b ∷ v)) p
           (λ u v → eA (a ∷ u) (b ∷ v)) (λ u v → eB (a ∷ u) (b ∷ v)) x y

-- A diagonal payload, controlled by the top block, is diagonal.
ctrl-diagⱼ : (f : Bits j → 𝔽) → ctrl {j} {m} (diag f) Idₒ allT ≐ diag (ctrlPh j f)
ctrl-diagⱼ {zero} f x y = go (allT x)
  where
  go : (t : Bool) → (if t then f [] * 1# else 1#) * δb x y ≡ (if t then f [] else 1#) * δb x y
  go true  = Eq.cong (_* δb x y) (*-identityʳ (f []))
  go false = Eq.refl
ctrl-diagⱼ {suc j} f (true ∷ x) (true ∷ y) = ctrl-diagⱼ {j} (λ u → f (true ∷ u)) x y
ctrl-diagⱼ {suc j} f (false ∷ x) (false ∷ y) = ctrl-diagⱼ {j} (λ u → f (false ∷ u)) x y
ctrl-diagⱼ {suc j} {m} f (true ∷ x) (false ∷ y) =
  Eq.trans (ctrl-0 {j} {m} (λ u v → f (true ∷ u) * 0#) (λ u v → 0#) allT
                   (λ u v → *-zeroʳ (f (true ∷ u))) (λ u v → Eq.refl) x y)
           (Eq.sym (*-zeroʳ (ctrlPh j (λ u → f (true ∷ u)) x)))
ctrl-diagⱼ {suc j} {m} f (false ∷ x) (true ∷ y) =
  Eq.trans (ctrl-0 {j} {m} (λ u v → f (false ∷ u) * 0#) (λ u v → 0#) allT
                   (λ u v → *-zeroʳ (f (false ∷ u))) (λ u v → Eq.refl) x y)
           (Eq.sym (*-zeroʳ (ctrlPh j (λ u → f (false ∷ u)) x)))

private
  -- The sign of the box, split at the top block.
  ph-split : (j : ℕ) (c : Bool) (xs : Bits (j +ℕ m)) →
             sgn (c ∧ allT xs) ≡ ctrlPh j (λ u → sgn (c ∧ allT u)) xs
  ph-split zero c xs = go (allT xs)
    where
    go : (t : Bool) → sgn (c ∧ t) ≡ (if t then sgn (c ∧ true) else 1#)
    go true  = Eq.refl
    go false = Eq.cong sgn (∧-zeroʳ c)
  ph-split (suc j) c (a ∷ xs) =
    Eq.trans (Eq.cong sgn (Eq.sym (∧-assoc c a (allT xs))))
    (Eq.trans (ph-split j (c ∧ a) xs)
              (ctrlPh-cong j (λ u → Eq.cong sgn (∧-assoc c a (allT u))) xs))

-- The box's phase: the box wire and the controls below the top block
-- are the payload's, the top block controls it.
box-split : (j : ℕ) → diag (phase (j +ℕ m)) ≐ ctrl {suc j} {m} (diag (phase j)) Idₒ allT
box-split {m} j x y =
  Eq.trans (Eq.cong (_* δb x y) (ph x)) (Eq.sym (ctrl-diagⱼ {suc j} {m} (phase j) x y))
  where
  ph : (x : Bits (suc (j +ℕ m))) → phase (j +ℕ m) x ≡ ctrlPh (suc j) (phase j) x
  ph (a ∷ xs) = ph-split j true xs

cf-box : (j m : ℕ) → CF {suc j} {m} (Λ□ (j +ℕ m))
cf-box j m = cf 0 (matOf (diag (phase j))) idM
  (≐-trans (·-1 ⟦ Λ□ (j +ℕ m) ⟧ₒ)
  (≐-trans (Λ□-sem (j +ℕ m))
           (·-cong Eq.refl
             (≐-trans (box-split j)
                      (ctrl-cong (≐-sym (ix-matOf (diag (phase j)))) (≐-sym (ix-id {suc j})))))))

------------------------------------------------------------------------
-- Comparing two forms

private
  shuffle : ∀ a b a′ b′ (z : 𝔽) → a +ℕ b ≡ a′ +ℕ b′ →
            √2^ a * (√2^ b * z) ≡ √2^ a′ * (√2^ b′ * z)
  shuffle a b a′ b′ z e =
    Eq.trans (Eq.sym (*-assoc (√2^ a) (√2^ b) z))
    (Eq.trans (Eq.cong (_* z) (Eq.sym (√2^-+ a b)))
    (Eq.trans (Eq.cong (λ k → √2^ k * z) e)
    (Eq.trans (Eq.cong (_* z) (√2^-+ a′ b′))
              (*-assoc (√2^ a′) (√2^ b′) z))))

-- Two forms whose payloads agree once each is scaled by the other's
-- exponent give the same semantics.  The agreement is asked for as the
-- boolean of Semantics.Decide, which `Eq.refl` decides in one shared
-- evaluation of the payloads.
cf-~ : {u v : Circuit (j +ℕ m)} (cu : CF {j} {m} u) (cv : CF {j} {m} v) →
       eqM (scaleM (√2^ CF.e cv) (CF.A cu)) (scaleM (√2^ CF.e cu) (CF.A cv)) ≡ true →
       eqM (scaleM (√2^ CF.e cv) (CF.B cu)) (scaleM (√2^ CF.e cu) (CF.B cv)) ≡ true →
       ⟦ u ⟧ ~ ⟦ v ⟧
cf-~ {j} {m} {u} {v} (cf eu Au Bu fu) (cf ev Av Bv fv) bA bB x y =
  √2^-cancel K (√2^ len v * ⟦ u ⟧ₒ x y) (√2^ len u * ⟦ v ⟧ₒ x y) (begin
    √2^ K * (√2^ len v * ⟦ u ⟧ₒ x y)
      ≡⟨ shuffle K (len v) (len v +ℕ ev) eu (⟦ u ⟧ₒ x y)
           (solve 3 (λ a b l → (a :+ b) :+ l := (l :+ b) :+ a) Eq.refl eu ev (len v)) ⟩
    √2^ (len v +ℕ ev) * (√2^ eu * ⟦ u ⟧ₒ x y)
      ≡⟨ Eq.cong (√2^ (len v +ℕ ev) *_) (fu x y) ⟩
    √2^ (len v +ℕ ev) * (√2^ len u * Cu x y)
      ≡⟨ shuffle (len v +ℕ ev) (len u) (len v +ℕ len u) ev (Cu x y)
           (solve 3 (λ l b k → (l :+ b) :+ k := (l :+ k) :+ b) Eq.refl (len v) ev (len u)) ⟩
    √2^ (len v +ℕ len u) * (√2^ ev * Cu x y)
      ≡⟨ Eq.cong (√2^ (len v +ℕ len u) *_) (eC x y) ⟩
    √2^ (len v +ℕ len u) * (√2^ eu * Cv x y)
      ≡⟨ shuffle (len v +ℕ len u) eu (len u +ℕ eu) (len v) (Cv x y)
           (solve 3 (λ l k a → (l :+ k) :+ a := (k :+ a) :+ l) Eq.refl (len v) (len u) eu) ⟩
    √2^ (len u +ℕ eu) * (√2^ len v * Cv x y)
      ≡⟨ Eq.cong (√2^ (len u +ℕ eu) *_) (Eq.sym (fv x y)) ⟩
    √2^ (len u +ℕ eu) * (√2^ ev * ⟦ v ⟧ₒ x y)
      ≡⟨ shuffle (len u +ℕ eu) ev K (len u) (⟦ v ⟧ₒ x y)
           (solve 3 (λ k a b → (k :+ a) :+ b := (a :+ b) :+ k) Eq.refl (len u) eu ev) ⟩
    √2^ K * (√2^ len u * ⟦ v ⟧ₒ x y) ∎)
  where
  open Eq.≡-Reasoning
  K : ℕ
  K = eu +ℕ ev
  eA : scaleM (√2^ ev) Au ≡ scaleM (√2^ eu) Av
  eA = eqM-sound _ _ bA
  eB : scaleM (√2^ ev) Bu ≡ scaleM (√2^ eu) Bv
  eB = eqM-sound _ _ bB
  Cu Cv : Op (j +ℕ m)
  Cu = ctrl (ix Au) (ix Bu) (allT {m})
  Cv = ctrl (ix Av) (ix Bv) (allT {m})
  eC : (√2^ ev · Cu) ≐ (√2^ eu · Cv)
  eC = ≐-trans (≐-sym (ctrl-· (√2^ ev) (ix Au) (ix Bu) allT))
       (≐-trans (ctrl-cong (≐-trans (≐-sym (ix-scaleM (√2^ ev) Au))
                                    (≐-trans (ix-≡ eA) (ix-scaleM (√2^ eu) Av)))
                           (≐-trans (≐-sym (ix-scaleM (√2^ ev) Bu))
                                    (≐-trans (ix-≡ eB) (ix-scaleM (√2^ eu) Bv))))
                (ctrl-· (√2^ eu) (ix Av) (ix Bv) allT))
