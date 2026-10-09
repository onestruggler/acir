------------------------------------------------------------------------
-- Presentations of groups
--
-- The action of embedded generators, and of generators with disjoint
-- indices.
--
-- * An embedded word acts on the coordinates ι y as the original word
--   acts on the restricted vector, and fixes the other coordinates.
--   So two words of dimension d with the same matrix stay equal in
--   action after embedding (emb-sound).
--
-- * Generators whose indices are disjoint commute (comm-sound).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)

module Examples.Groups.CCX+HH-TwoLevel.EmbedAction
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (h : A)
  where

open import Data.Fin.Base using (Fin ; zero ; _<_)
import Data.Fin.Properties as FinP
open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using (Vec ; [] ; _∷_ ; tabulate)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary using (¬_ ; Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; _·*·_)

open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH-TwoLevel.Syntactics
open import Examples.Groups.CCX+HH-TwoLevel.Embedding
import Examples.Groups.CCX+HH-TwoLevel.Action as Action

open Action isCR adjI h

private
  variable
    m n : ℕ

  cong₄ : ∀ {B : Set} (f : A → A → A → A → B) {x x′ y y′ z z′ t t′} →
          x ≡ x′ → y ≡ y′ → z ≡ z′ → t ≡ t′ → f x y z t ≡ f x′ y′ z′ t′
  cong₄ f refl refl refl refl = refl

------------------------------------------------------------------------
-- The action of a word is multiplication by its matrix, on vectors too

-- A vector as a one-column matrix.
colmat : Vec A n → Matrix n 1 A
colmat u = Matrix' (u ∷ [])

actVʷ≡ : (w : Word (Gen n)) (u : Vec A n) → actVʷ w u ≡ col (⟦ w ⟧ᵐ ·*· colmat u) zero
actVʷ≡ w u = trans (sym (col-actMʷ w (colmat u) zero)) (cong (λ M → col M zero) (actMʷ≡ w (colmat u)))

-- Words with the same matrix act alike.
same-action : (w v : Word (Gen n)) → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ → ∀ u → actVʷ w u ≡ actVʷ v u
same-action w v eq u = trans (actVʷ≡ w u) (trans (cong (λ M → col (M ·*· colmat u) zero) eq) (sym (actVʷ≡ v u)))

-- Conversely, words that act alike have the same matrix.
same-matrix : (w v : Word (Gen n)) → (∀ u → actVʷ w u ≡ actVʷ v u) → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ
same-matrix w v eq = col-ext λ c →
  trans (col-actMʷ w 𝕀 c) (trans (eq (col 𝕀 c)) (sym (col-actMʷ v 𝕀 c)))

------------------------------------------------------------------------
-- Embedded generators

module _ (e : Emb m n) where

  private
    ι′ = ι e
    inj = injective e

  restrict : Vec A n → Vec A m
  restrict v = tabulate (λ y → v ! ι′ y)

  restrict-! : (v : Vec A n) (y : Fin m) → restrict v ! y ≡ v ! ι′ y
  restrict-! v y = !-tabulate (λ y → v ! ι′ y) y

  private
    -- Updates commute with restriction.
    set₂-in : (a b : Fin m) → a ≢ b → (α β : A) (v : Vec A n) (y : Fin m) →
              set₂ (ι′ a) (ι′ b) α β v ! ι′ y ≡ set₂ a b α β (restrict v) ! y
    set₂-in a b a≢b α β v y with y FinP.≟ a | y FinP.≟ b
    ... | yes refl | _ = trans (set₂-a (ι′ y) (ι′ b) α β v) (sym (set₂-a y b α β (restrict v)))
    ... | no _ | yes refl = trans (set₂-b (ι′ a) (ι′ y) α β v (inj a≢b)) (sym (set₂-b a y α β (restrict v) a≢b))
    ... | no y≢a | no y≢b = trans (set₂-≢ (ι′ a) (ι′ b) α β v (inj y≢a) (inj y≢b))
                                  (trans (sym (restrict-! v y)) (sym (set₂-≢ a b α β (restrict v) y≢a y≢b)))

    set₂-restrict : (a b : Fin m) → a ≢ b → (α β : A) (v : Vec A n) →
                    restrict (set₂ (ι′ a) (ι′ b) α β v) ≡ set₂ a b α β (restrict v)
    set₂-restrict a b a≢b α β v = vec-ext λ y →
      trans (restrict-! (set₂ (ι′ a) (ι′ b) α β v) y) (set₂-in a b a≢b α β v y)

    set₄-restrict : (a b c d : Fin m) → a ≢ b → c ≢ d → (α β γ δ′ : A) (v : Vec A n) →
                    restrict (set₄ (ι′ a) (ι′ b) (ι′ c) (ι′ d) α β γ δ′ v) ≡ set₄ a b c d α β γ δ′ (restrict v)
    set₄-restrict a b c d a≢b c≢d α β γ δ′ v =
      trans (set₂-restrict a b a≢b α β (set₂ (ι′ c) (ι′ d) γ δ′ v))
            (cong (set₂ a b α β) (set₂-restrict c d c≢d γ δ′ v))

    set₁-in : (a : Fin m) (α : A) (v : Vec A n) (y : Fin m) →
              set₁ (ι′ a) α v ! ι′ y ≡ set₁ a α (restrict v) ! y
    set₁-in a α v y with y FinP.≟ a
    ... | yes refl = trans (set₁-a (ι′ y) α v) (sym (set₁-a y α (restrict v)))
    ... | no y≢a = trans (set₁-≢ (ι′ a) α v (inj y≢a))
                         (trans (sym (restrict-! v y)) (sym (set₁-≢ a α (restrict v) y≢a)))

  -- On the embedded coordinates, the embedded generator acts as the
  -- original one on the restricted vector.
  emb-restrict : (g : Gen m) (v : Vec A n) → restrict (actV (gen e g) v) ≡ actV g (restrict v)
  emb-restrict (M-gen a) v = vec-ext λ y →
    trans (restrict-! (actV (M-gen (ι′ a)) v) y)
      (trans (cong (_! ι′ y) (actV-M≡ (ι′ a) v))
        (trans (set₁-in a (- (v ! ι′ a)) v y)
          (trans (cong (λ α → set₁ a α (restrict v) ! y) (cong -_ (sym (restrict-! v a))))
            (sym (cong (_! y) (actV-M≡ a (restrict v)))))))
  emb-restrict (X-gen a b p) v =
    trans (cong restrict (actV-X≡ (mono e p) v))
      (trans (set₂-restrict a b (<⇒≢ p) (v ! ι′ b) (v ! ι′ a) v)
        (trans (cong₂ (λ α β → set₂ a b α β (restrict v)) (sym (restrict-! v b)) (sym (restrict-! v a)))
          (sym (actV-X≡ p (restrict v)))))
  emb-restrict (K-gen a b c d p q r) v =
    trans (cong restrict (actV-K≡ (mono e p) (mono e q) (mono e r) v))
      (trans (set₄-restrict a b c d ab cd _ _ _ _ v)
        (trans (cong₄ (λ α β γ δ′ → set₄ a b c d α β γ δ′ (restrict v))
                      (cong₄ rowA ra rb rc rd) (cong₄ rowB ra rb rc rd)
                      (cong₄ rowC ra rb rc rd) (cong₄ rowD ra rb rc rd))
          (sym (actV-K≡ p q r (restrict v)))))
    where
    open Distinct₄ (distinct₄ p q r)
    ra = sym (restrict-! v a)
    rb = sym (restrict-! v b)
    rc = sym (restrict-! v c)
    rd = sym (restrict-! v d)

  -- The other coordinates are fixed.
  emb-actV-out : (g : Gen m) (v : Vec A n) (x : Fin n) → (∀ y → x ≢ ι′ y) → actV (gen e g) v ! x ≡ v ! x
  emb-actV-out (M-gen a) v x out = actV-M≢ (ι′ a) v (out a)
  emb-actV-out (X-gen a b p) v x out = actV-X≢ (mono e p) v (out a) (out b)
  emb-actV-out (K-gen a b c d p q r) v x out =
    actV-K≢ (mono e p) (mono e q) (mono e r) v (out a) (out b) (out c) (out d)

  -- The same for words.
  emb-actVʷ-restrict : (w : Word (Gen m)) (v : Vec A n) → restrict (actVʷ (word e w) v) ≡ actVʷ w (restrict v)
  emb-actVʷ-restrict [ g ]ʷ v = emb-restrict g v
  emb-actVʷ-restrict ε v = refl
  emb-actVʷ-restrict (u • w) v =
    trans (emb-actVʷ-restrict u (actVʷ (word e w) v)) (cong (actVʷ u) (emb-actVʷ-restrict w v))

  emb-actVʷ-out : (w : Word (Gen m)) (v : Vec A n) (x : Fin n) → (∀ y → x ≢ ι′ y) →
                  actVʷ (word e w) v ! x ≡ v ! x
  emb-actVʷ-out [ g ]ʷ v x out = emb-actV-out g v x out
  emb-actVʷ-out ε v x out = refl
  emb-actVʷ-out (u • w) v x out = trans (emb-actVʷ-out u (actVʷ (word e w) v) x out) (emb-actVʷ-out w v x out)

  -- Words of dimension d with the same matrix, embedded, act alike.
  emb-sound : (w v : Word (Gen m)) → ⟦ w ⟧ᵐ ≡ ⟦ v ⟧ᵐ → ⟦ word e w ⟧ᵐ ≡ ⟦ word e v ⟧ᵐ
  emb-sound w v eq = same-matrix (word e w) (word e v) λ u → vec-ext λ x → pointwise u x
    where
    pointwise : ∀ u x → actVʷ (word e w) u ! x ≡ actVʷ (word e v) u ! x
    pointwise u x with FinP.any? (λ y → x FinP.≟ ι′ y)
    ... | yes (y , refl) = begin
      actVʷ (word e w) u ! ι′ y              ≡⟨ sym (restrict-! (actVʷ (word e w) u) y) ⟩
      restrict (actVʷ (word e w) u) ! y      ≡⟨ cong (_! y) (emb-actVʷ-restrict w u) ⟩
      actVʷ w (restrict u) ! y               ≡⟨ cong (_! y) (same-action w v eq (restrict u)) ⟩
      actVʷ v (restrict u) ! y               ≡⟨ cong (_! y) (sym (emb-actVʷ-restrict v u)) ⟩
      restrict (actVʷ (word e v) u) ! y      ≡⟨ restrict-! (actVʷ (word e v) u) y ⟩
      actVʷ (word e v) u ! ι′ y              ∎
      where open ≡-Reasoning
    ... | no none = trans (emb-actVʷ-out w u x out) (sym (emb-actVʷ-out v u x out))
      where
      out : ∀ y → x ≢ ι′ y
      out y x≡ιy = none (y , x≡ιy)

------------------------------------------------------------------------
-- Generators with disjoint indices commute

-- The indices a generator acts on.
data _∈ₛ_ {n : ℕ} (x : Fin n) : Gen n → Set where
  M-a : x ∈ₛ M-gen x
  X-a : ∀ {b} .{p : x < b} → x ∈ₛ X-gen x b p
  X-b : ∀ {a} .{p : a < x} → x ∈ₛ X-gen a x p
  K-a : ∀ {b c d} .{p : x < b} .{q : b < c} .{r : c < d} → x ∈ₛ K-gen x b c d p q r
  K-b : ∀ {a c d} .{p : a < x} .{q : x < c} .{r : c < d} → x ∈ₛ K-gen a x c d p q r
  K-c : ∀ {a b d} .{p : a < b} .{q : b < x} .{r : x < d} → x ∈ₛ K-gen a b x d p q r
  K-d : ∀ {a b c} .{p : a < b} .{q : b < c} .{r : c < x} → x ∈ₛ K-gen a b c x p q r

∈ₛ? : (x : Fin n) (g : Gen n) → Dec (x ∈ₛ g)
∈ₛ? x (M-gen a) with x FinP.≟ a
... | yes refl = yes M-a
... | no x≢a = no λ { M-a → x≢a refl }
∈ₛ? x (X-gen a b p) with x FinP.≟ a | x FinP.≟ b
... | yes refl | _ = yes X-a
... | no x≢a | yes refl = yes X-b
... | no x≢a | no x≢b = no λ { X-a → x≢a refl ; X-b → x≢b refl }
∈ₛ? x (K-gen a b c d p q r) with x FinP.≟ a | x FinP.≟ b | x FinP.≟ c | x FinP.≟ d
... | yes refl | _ | _ | _ = yes K-a
... | no _ | yes refl | _ | _ = yes K-b
... | no _ | no _ | yes refl | _ = yes K-c
... | no _ | no _ | no _ | yes refl = yes K-d
... | no xa | no xb | no xc | no xd =
  no λ { K-a → xa refl ; K-b → xb refl ; K-c → xc refl ; K-d → xd refl }

-- Outside its indices, a generator does nothing.
actV-off : (g : Gen n) (v : Vec A n) (x : Fin n) → ¬ (x ∈ₛ g) → actV g v ! x ≡ v ! x
actV-off (M-gen a) v x x∉ = actV-M≢ a v (λ { refl → x∉ M-a })
actV-off (X-gen a b p) v x x∉ = actV-X≢ p v (λ { refl → x∉ X-a }) (λ { refl → x∉ X-b })
actV-off (K-gen a b c d p q r) v x x∉ =
  actV-K≢ p q r v (λ { refl → x∉ K-a }) (λ { refl → x∉ K-b }) (λ { refl → x∉ K-c }) (λ { refl → x∉ K-d })

-- On its indices, a generator only reads its indices.
actV-local : (g : Gen n) (u v : Vec A n) → (∀ y → y ∈ₛ g → u ! y ≡ v ! y) →
             ∀ x → x ∈ₛ g → actV g u ! x ≡ actV g v ! x
actV-local (M-gen a) u v agree .a M-a =
  trans (actV-Ma a u) (trans (cong -_ (agree a M-a)) (sym (actV-Ma a v)))
actV-local (X-gen a b p) u v agree .a X-a =
  trans (actV-Xa p u) (trans (agree b X-b) (sym (actV-Xa p v)))
actV-local (X-gen a b p) u v agree .b X-b =
  trans (actV-Xb p u) (trans (agree a X-a) (sym (actV-Xb p v)))
actV-local (K-gen a b c d p q r) u v agree .a K-a =
  trans (actV-Ka p q r u) (trans (cong₄ rowA (agree a K-a) (agree b K-b) (agree c K-c) (agree d K-d)) (sym (actV-Ka p q r v)))
actV-local (K-gen a b c d p q r) u v agree .b K-b =
  trans (actV-Kb p q r u) (trans (cong₄ rowB (agree a K-a) (agree b K-b) (agree c K-c) (agree d K-d)) (sym (actV-Kb p q r v)))
actV-local (K-gen a b c d p q r) u v agree .c K-c =
  trans (actV-Kc p q r u) (trans (cong₄ rowC (agree a K-a) (agree b K-b) (agree c K-c) (agree d K-d)) (sym (actV-Kc p q r v)))
actV-local (K-gen a b c d p q r) u v agree .d K-d =
  trans (actV-Kd p q r u) (trans (cong₄ rowD (agree a K-a) (agree b K-b) (agree c K-c) (agree d K-d)) (sym (actV-Kd p q r v)))

-- Generators with disjoint indices.
Disjoint : Gen n → Gen n → Set
Disjoint g h = ∀ x → x ∈ₛ g → ¬ (x ∈ₛ h)

actV-comm : (g h : Gen n) → Disjoint g h → ∀ v → actV g (actV h v) ≡ actV h (actV g v)
actV-comm g h dis v = vec-ext pointwise
  where
  pointwise : ∀ x → actV g (actV h v) ! x ≡ actV h (actV g v) ! x
  pointwise x with ∈ₛ? x g | ∈ₛ? x h
  ... | yes x∈g | _ = begin
    actV g (actV h v) ! x      ≡⟨ actV-local g (actV h v) v (λ y y∈g → actV-off h v y (dis y y∈g)) x x∈g ⟩
    actV g v ! x               ≡⟨ sym (actV-off h (actV g v) x (dis x x∈g)) ⟩
    actV h (actV g v) ! x      ∎
    where open ≡-Reasoning
  ... | no x∉g | yes x∈h = begin
    actV g (actV h v) ! x      ≡⟨ actV-off g (actV h v) x x∉g ⟩
    actV h v ! x               ≡⟨ actV-local h v (actV g v) (λ y y∈h → sym (actV-off g v y (λ y∈g → dis y y∈g y∈h))) x x∈h ⟩
    actV h (actV g v) ! x      ∎
    where open ≡-Reasoning
  ... | no x∉g | no x∉h = begin
    actV g (actV h v) ! x      ≡⟨ actV-off g (actV h v) x x∉g ⟩
    actV h v ! x               ≡⟨ actV-off h v x x∉h ⟩
    v ! x                      ≡⟨ sym (actV-off g v x x∉g) ⟩
    actV g v ! x               ≡⟨ sym (actV-off h (actV g v) x x∉h) ⟩
    actV h (actV g v) ! x      ∎
    where open ≡-Reasoning

-- So the words g • h and h • g have the same matrix.
comm-sound : (g h : Gen n) → Disjoint g h → ⟦ [ g ]ʷ • [ h ]ʷ ⟧ᵐ ≡ ⟦ [ h ]ʷ • [ g ]ʷ ⟧ᵐ
comm-sound g h dis = same-matrix ([ g ]ʷ • [ h ]ʷ) ([ h ]ʷ • [ g ]ʷ) (actV-comm g h dis)
