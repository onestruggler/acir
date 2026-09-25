------------------------------------------------------------------------
-- Presentations of groups
--
-- The syllable of a matrix (step 3 of Algorithm 2.10), and the facts
-- about the action of words that the analysis of the algorithm uses:
-- words acting on indices ≤ p leave the columns beyond p alone, and
-- the actions of i_[a]ᵉ and of K†_[a,b] on columns.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.Syllable where

open import Data.Empty using (⊥-elim)
open import Data.Fin.Base as Fin using (Fin ; zero ; suc ; _<_ ; _≤_ ; toℕ)
import Data.Fin.Properties as FinP
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc ; z≤n ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Product.Base using (∃ ; _×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec ; tabulate)
import Data.Vec.Properties as VecP
open import Function.Base using (_∘_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _^_)
open import Examples.Groups.Clifford+CS-TwoLevel.Ring
open import Examples.Groups.Clifford+CS-TwoLevel.Scale
open import Examples.Groups.Clifford+CS-TwoLevel.Lde using (scV ; scV-! ; lde ; num)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (dec-elim)
open import Examples.Groups.Clifford+CS-TwoLevel.Column
open import Examples.Groups.Clifford+CS-TwoLevel.ColumnAction
open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics
open import Examples.Groups.Clifford+CS-TwoLevel.Embedding using (emb₂)
open import Examples.Groups.Clifford+CS-TwoLevel.Semantics
open import Examples.Groups.Clifford+CS-TwoLevel.Pivot

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- The syllable, and one step of the algorithm

sylAt : Maybe (Fin n) → Matrix n n D → Word (Gen n)
sylAt nothing  M = ε
sylAt (just p) M = sylData p (lde (col M p)) (num (col M p))

syl : Matrix n n D → Word (Gen n)
syl M = sylAt (pivot M) M

syl-just : (M : Matrix n n D) {p : Fin n} → pivot M ≡ just p →
           syl M ≡ sylData p (lde (col M p)) (num (col M p))
syl-just M eq = cong (λ x → sylAt x M) eq

syl-nothing : (M : Matrix n n D) → pivot M ≡ nothing → syl M ≡ ε
syl-nothing M eq = cong (λ x → sylAt x M) eq

-- Step 4: apply the syllable.
step : Matrix n n D → Matrix n n D
step M = actMʷ (syl M) M

------------------------------------------------------------------------
-- Words acting on indices ≤ p

-- The largest index a generator acts on.
top : Gen n → Fin n
top (X-gen a b _) = b
top (K-gen a b _) = b
top (i-gen a)     = a

Within : Fin n → Word (Gen n) → Set
Within p [ g ]ʷ   = top g ≤ p
Within p ε        = ⊤
Within p (u • v)  = Within p u × Within p v

Within-^ : ∀ {p : Fin n} (w : Word (Gen n)) → Within p w → ∀ e → Within p (w ^ e)
Within-^ w h zero = tt
Within-^ w h (suc zero) = h
Within-^ w h (suc (suc e)) = h , Within-^ w h (suc e)

∈ₛ-top : ∀ {x : Fin n} {g} → x ∈ₛ g → x ≤ top g
∈ₛ-top (X-a {b} {p}) = ℕP.<⇒≤ (recompute (_ FinP.<? b) p)
∈ₛ-top X-b = FinP.≤-refl
∈ₛ-top (K-a {b} {p}) = ℕP.<⇒≤ (recompute (_ FinP.<? b) p)
∈ₛ-top K-b = FinP.≤-refl
∈ₛ-top i-a = FinP.≤-refl

-- The zero vector is fixed by every generator.
zeroV : Vec D n
zeroV = Vec.replicate _ DR.0#

private
  0!  : (x : Fin n) → zeroV ! x ≡ DR.0#
  0! x = VecP.lookup-replicate x DR.0#

actV-0 : (g : Gen n) → actV g zeroV ≡ zeroV
actV-0 (X-gen a b p) = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → trans (set₂-a x b (zeroV ! b) (zeroV ! x) zeroV) (trans (0! b) (sym (0! x))) })
    (λ x≢a → dec-elim (x FinP.≟ b)
      (λ { refl → trans (set₂-b a x (zeroV ! x) (zeroV ! a) zeroV (<⇒≢ p)) (trans (0! a) (sym (0! x))) })
      (λ x≢b → set₂-≢ a b (zeroV ! b) (zeroV ! a) zeroV x≢a x≢b))
actV-0 (K-gen a b p) = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → trans (set₂-a x b α β zeroV) (trans (sum0 x b) (sym (0! x))) })
    (λ x≢a → dec-elim (x FinP.≟ b)
      (λ { refl → trans (set₂-b a x α β zeroV (<⇒≢ p)) (trans (dif0 a x) (sym (0! x))) })
      (λ x≢b → set₂-≢ a b α β zeroV x≢a x≢b))
  where
  α = γ⁻ DR.* (zeroV ! a DR.+ zeroV ! b)
  β = γ⁻ DR.* (zeroV ! a DR.- zeroV ! b)
  sum0 : ∀ y z → γ⁻ DR.* (zeroV ! y DR.+ zeroV ! z) ≡ DR.0#
  sum0 y z = trans (cong₂ (λ s t → γ⁻ DR.* (s DR.+ t)) (0! y) (0! z))
                   (trans (cong (γ⁻ DR.*_) (DR.+-identityˡ DR.0#)) (DR.zeroʳ γ⁻))
  dif0 : ∀ y z → γ⁻ DR.* (zeroV ! y DR.- zeroV ! z) ≡ DR.0#
  dif0 y z = trans (cong₂ (λ s t → γ⁻ DR.* (s DR.- t)) (0! y) (0! z))
                   (trans (cong (γ⁻ DR.*_) (DR.-‿inverseʳ DR.0#)) (DR.zeroʳ γ⁻))
actV-0 (i-gen a) = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → trans (set₁-a x (ⅈ DR.* (zeroV ! x)) zeroV)
                      (trans (cong (ⅈ DR.*_) (0! x)) (trans (DR.zeroʳ ⅈ) (sym (0! x)))) })
    (λ x≢a → set₁-≢ a (ⅈ DR.* (zeroV ! a)) zeroV x≢a)

-- A generator acting on indices ≤ p fixes the standard basis vectors
-- beyond p.
actV-e-beyond : (g : Gen n) {p c : Fin n} → top g ≤ p → p < c → actV g (col 𝕀 c) ≡ col 𝕀 c
actV-e-beyond g {p} {c} tp pc = vec-ext λ x →
  dec-elim (∈ₛ? x g)
    (λ x∈g → begin
      actV g e ! x          ≡⟨ actV-local g e zeroV agree x x∈g ⟩
      actV g zeroV ! x      ≡⟨ cong (_! x) (actV-0 g) ⟩
      zeroV ! x             ≡⟨ sym (agree x x∈g) ⟩
      e ! x                 ∎)
    (λ x∉g → actV-off g e x x∉g)
  where
  open ≡-Reasoning
  e = col 𝕀 c
  agree : ∀ y → y ∈ₛ g → e ! y ≡ zeroV ! y
  agree y y∈g = trans (ent-𝕀 y c) (trans (δ-≢ y≢c) (sym (0! y)))
    where
    y≢c : y ≢ c
    y≢c refl = FinP.<-irrefl refl (ℕP.≤-<-trans (ℕP.≤-trans (∈ₛ-top y∈g) tp) pc)

Beyond-actM : (g : Gen n) {p : Fin n} {M : Matrix n n D} → top g ≤ p → Beyond p M → Beyond p (actM g M)
Beyond-actM g {M = M} tp be c pc =
  trans (col-actM g M c) (trans (cong (actV g) (be c pc)) (actV-e-beyond g tp pc))

Beyond-actMʷ : (w : Word (Gen n)) {p : Fin n} {M : Matrix n n D} → Within p w → Beyond p M → Beyond p (actMʷ w M)
Beyond-actMʷ [ g ]ʷ {p} {M} h be = Beyond-actM g {p} {M} h be
Beyond-actMʷ ε h be = be
Beyond-actMʷ (u • v) {p} {M} (hu , hv) be = Beyond-actMʷ u {p} {actMʷ v M} hu (Beyond-actMʷ v {p} {M} hv be)

------------------------------------------------------------------------
-- Standard basis vectors as scaled vectors

δᶻ : Fin n → Fin n → Z
δᶻ x c with x FinP.≟ c
... | yes _ = ZR.1#
... | no  _ = ZR.0#

eᶻ : Fin n → Vec Z n
eᶻ c = tabulate (λ x → δᶻ x c)

δᶻ-refl : (x : Fin n) → δᶻ x x ≡ ZR.1#
δᶻ-refl x with x FinP.≟ x
... | yes _ = refl
... | no x≢x = ⊥-elim (x≢x refl)

δᶻ-≢ : {x c : Fin n} → x ≢ c → δᶻ x c ≡ ZR.0#
δᶻ-≢ {x = x} {c} x≢c with x FinP.≟ c
... | yes x≡c = ⊥-elim (x≢c x≡c)
... | no _ = refl

eᶻ-! : (c x : Fin n) → eᶻ c ! x ≡ δᶻ x c
eᶻ-! c x = VecP.lookup∘tabulate (λ x → δᶻ x c) x

private
  δ≡ : (x c : Fin n) → δ x c ≡ sc 0 (δᶻ x c)
  δ≡ x c = dec-elim (x FinP.≟ c)
    (λ { refl → trans (δ-refl x) (sym (trans (cong (sc 0) (δᶻ-refl x)) (trans (sc-def 0 ZR.1#) (DR.*-identityʳ DR.1#)))) })
    (λ x≢c → trans (δ-≢ x≢c) (sym (trans (cong (sc 0) (δᶻ-≢ x≢c)) (sc-0 0))))

col𝕀≡ : (c : Fin n) → col 𝕀 c ≡ scV 0 (eᶻ c)
col𝕀≡ c = vec-ext λ x → begin
  col 𝕀 c ! x               ≡⟨ ent-𝕀 x c ⟩
  δ x c                     ≡⟨ δ≡ x c ⟩
  sc 0 (δᶻ x c)             ≡⟨ cong (sc 0) (sym (VecP.lookup∘tabulate (λ x → δᶻ x c) x)) ⟩
  sc 0 (eᶻ c ! x)           ≡⟨ sym (scV-! 0 (eᶻ c) x) ⟩
  scV 0 (eᶻ c) ! x          ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- Updating one entry twice, or by its own value

set₁-set₁ : {B : Set} (a : Fin n) (α β : B) (v : Vec B n) → set₁ a α (set₁ a β v) ≡ set₁ a α v
set₁-set₁ a α β v = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → trans (set₁-a x α (set₁ x β v)) (sym (set₁-a x α v)) })
    (λ x≢a → trans (set₁-≢ a α (set₁ a β v) x≢a) (trans (set₁-≢ a β v x≢a) (sym (set₁-≢ a α v x≢a))))

set₁-self : {B : Set} (a : Fin n) (v : Vec B n) → set₁ a (v ! a) v ≡ v
set₁-self a v = vec-ext λ x →
  dec-elim (x FinP.≟ a)
    (λ { refl → set₁-a x (v ! x) v })
    (λ x≢a → set₁-≢ a (v ! a) v x≢a)

------------------------------------------------------------------------
-- The actions of i_[a]ᵉ and of K†_[a,b] on columns

-- i_[a]ᵉ multiplies entry a by iᵉ.
i^-action : (a : Fin n) (e k : ℕ) (w : Vec Z n) →
            actVʷ (i a ^ e) (scV k w) ≡ scV k (set₁ a ((ⅈᶻ ^ᶻ e) ZR.* (w ! a)) w)
i^-action a zero k w =
  cong (scV k) (sym (trans (cong (λ z → set₁ a z w) (ZR.*-identityˡ (w ! a))) (set₁-self a w)))
i^-action a (suc zero) k w =
  trans (actV-i a k w) (cong (λ z → scV k (set₁ a z w)) (cong (ZR._* (w ! a)) (sym (ZR.*-identityʳ ⅈᶻ))))
i^-action a (suc (suc e)) k w = begin
  actV (i-gen a) (actVʷ (i a ^ suc e) (scV k w))
    ≡⟨ cong (actV (i-gen a)) (i^-action a (suc e) k w) ⟩
  actV (i-gen a) (scV k w′)
    ≡⟨ actV-i a k w′ ⟩
  scV k (set₁ a (ⅈᶻ ZR.* (w′ ! a)) w′)
    ≡⟨ cong (λ z → scV k (set₁ a (ⅈᶻ ZR.* z) w′)) (set₁-a a c w) ⟩
  scV k (set₁ a (ⅈᶻ ZR.* c) w′)
    ≡⟨ cong (scV k) (set₁-set₁ a (ⅈᶻ ZR.* c) c w) ⟩
  scV k (set₁ a (ⅈᶻ ZR.* c) w)
    ≡⟨ cong (λ z → scV k (set₁ a z w)) (sym (ZR.*-assoc ⅈᶻ (ⅈᶻ ^ᶻ suc e) (w ! a))) ⟩
  scV k (set₁ a ((ⅈᶻ ^ᶻ suc (suc e)) ZR.* (w ! a)) w) ∎
  where
  open ≡-Reasoning
  c = (ⅈᶻ ^ᶻ suc e) ZR.* (w ! a)
  w′ = set₁ a c w

private
  f0² f1² : Fin 2
  f0² = zero
  f1² = suc zero
  0<1² : f0² < f1²
  0<1² = s≤s z≤n

-- K⁷ = K† = i_[0] i_[1] K in dimension 2, by computation through the
-- vector updates.
opaque
  unfolding set₁ set₂

  private
    K⁷≡ : ⟦ K f0² f1² 0<1² ^ 7 ⟧ᵐ ≡ ⟦ i f0² • i f1² • K f0² f1² 0<1² ⟧ᵐ
    K⁷≡ = refl

K†-action : (a b : Fin n) (ab : a < b) (u : Vec D n) →
            actVʷ (K† a b ab) u ≡ actV (i-gen a) (actV (i-gen b) (actV (K-gen a b ab) u))
K†-action a b ab u =
  same-action (K† a b ab) (i a • i b • K a b ab)
    (emb-sound (emb₂ a b ab) (K f0² f1² 0<1² ^ 7) (i f0² • i f1² • K f0² f1² 0<1²) K⁷≡) u
