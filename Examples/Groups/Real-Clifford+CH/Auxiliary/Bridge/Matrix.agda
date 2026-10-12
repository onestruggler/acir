------------------------------------------------------------------------
-- Presentations of groups
--
-- Scaled matrices of this development as matrices over ℤ[1/√2]
--
-- Number the 2ⁿ basis vectors by a bijection code : Fin 2ⁿ → Bits n
-- (the Gray code, Auxiliary.Gray, or the table of TwoQubit).  A scaled
-- matrix (ℓ , M), which denotes (1/√2)^ℓ · M, is then the 2ⁿ × 2ⁿ
-- matrix Φ (ℓ , M) over the ring 𝔻[√2] = ℤ[1/√2] of Real-Clifford+CH-
-- TwoLevel with entry (1/√2)^ℓ · ι (M (code r) (code c)) at (r , c).
--
-- * Φ is a monoid homomorphism (Φ-∙, Φ-ε): sums over bit vectors are
--   sums over Fin 2ⁿ, renumbered by code (sum-code, through
--   Real-Clifford's binary numbering and a permutation);
-- * Φ identifies the pairs that _~_ does (Φ-~);
-- * Φ sends the matrices of the generators (−1)_[a], X_[a,b], H_[a,b]
--   of this development, numbered by code (⟦_⟧c), to those of their
--   translations φ (letter).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ ; _^_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Matrix
  (n : ℕ) (code : Fin (2 ^ n) → Bits n) (index : Bits n → Fin (2 ^ n))
  (code-index : ∀ g → code (index g) ≡ g) (index-code : ∀ a → index (code a) ≡ a)
  where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (_<_)
import Data.Fin.Properties as FinP
open import Data.Fin.Permutation using (Permutation ; permutation)
open import Data.Nat.Base using (zero ; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_,_ ; proj₁ ; proj₂)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≢_ ; refl ; cong ; cong₂ ; trans ; sym ; module ≡-Reasoning)
open import Relation.Nullary using (Dec ; yes ; no)

open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Examples.Groups.Real-Clifford+CH.Semantics as S
import Examples.Groups.Real-Clifford+CH.Semantics.Ring as R
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB ; negOp ; swapOp ; hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas using (eqB-refl ; eqB-sound)
import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_] ; Proper ; ProperG ; −1ᵖ ; Xᵖ ; Hᵖ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Ring
import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Syntax as Syn

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; module DR ; SemiRingD ; RingD ; AdjointD ; isCommutativeRing-D ; adj-D ; √½ ; √2ᴰ ; -1ᴰ ; √½*√2)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics using (Gen ; X-gen ; K-gen ; i-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
  using ( ent ; mk ; ent-mk ; mat-ext ; ent-·*· ; 𝕀 ; ent-𝕀 ; δ ; δ-refl ; δ-≢ ; sum ; sum-cong-≗
        ; *-distribˡ-sum ; col ; _!_ ; actV ; actVʷ ; col-actMʷ ; ⟦_⟧ᵐ ; ⟦•⟧ᵐ
        ; actV-Xa ; actV-Xb ; actV-X≢ ; actV-Ka ; actV-Kb ; actV-K≢ ; actV-ia ; actV-i≢ )
open import Algebra.Properties.CommutativeMonoid.Sum DR.+-commutativeMonoid using (sum-permute)
import Examples.Groups.Real-Clifford.Semantics.Laws as RCLaws
import Examples.Groups.Real-Clifford.Semantics.Matrix as RCMatrix

open Syn (2 ^ n) public using (φX ; φH ; φg ; φ)

private
  N : ℕ
  N = 2 ^ n

  module RL = RCLaws {A = D} isCommutativeRing-D
  module RM = RCMatrix {A = D} isCommutativeRing-D adj-D

  code-inj : ∀ {r c} → code r ≡ code c → r ≡ c
  code-inj {r} {c} e = trans (sym (index-code r)) (trans (cong index e) (index-code c))

  if-t : ∀ {A : Set} {b : Bool} {x y : A} → b ≡ true → (if b then x else y) ≡ x
  if-t refl = refl

  if-f : ∀ {A : Set} {b : Bool} {x y : A} → b ≡ false → (if b then x else y) ≡ y
  if-f refl = refl

  eqB-false : ∀ {m} (x y : Bits m) → x ≢ y → eqB x y ≡ false
  eqB-false x y ne with eqB x y in e
  ... | true  = ⊥-elim (ne (eqB-sound x y e))
  ... | false = refl

  eqB-code : ∀ {r c} → r ≢ c → eqB (code r) (code c) ≡ false
  eqB-code {r} {c} ne = eqB-false (code r) (code c) (λ e → ne (code-inj e))

  δb-≢ : ∀ {m} (x y : Bits m) → x ≢ y → S.δb x y ≡ R.0#
  δb-≢ []          []          ne = ⊥-elim (ne refl)
  δb-≢ (true ∷ x)  (true ∷ y)  ne = δb-≢ x y (λ e → ne (cong (true ∷_) e))
  δb-≢ (false ∷ x) (false ∷ y) ne = δb-≢ x y (λ e → ne (cong (false ∷_) e))
  δb-≢ (true ∷ x)  (false ∷ y) ne = refl
  δb-≢ (false ∷ x) (true ∷ y)  ne = refl

  -- The delta, read through code.
  ι-δb : ∀ r c → ι (S.δb (code r) (code c)) ≡ δ r c
  ι-δb r c = by (r FinP.≟ c)
    where
    by : Dec (r ≡ c) → ι (S.δb (code r) (code c)) ≡ δ r c
    by (yes refl) = trans (cong ι (S.δb-refl (code r))) (sym (δ-refl r))
    by (no r≢c)   = trans (cong ι (δb-≢ (code r) (code c) (λ e → r≢c (code-inj e)))) (sym (δ-≢ r≢c))

  -- The unit vector e_c, column c of the identity.
  e! : ∀ (c x : Fin N) → col 𝕀 c ! x ≡ δ x c
  e! c x = ent-𝕀 x c

  neg0 : DR.- DR.0# ≡ DR.0#
  neg0 = trans (sym (DR.+-identityˡ (DR.- DR.0#))) (DR.-‿inverseʳ DR.0#)

  -1≡ : -1ᴰ ≡ DR.- DR.1#
  -1≡ = ι-neg R.1#

------------------------------------------------------------------------
-- Sums over bit vectors are sums over Fin 2ⁿ, numbered by code

Σb-ι : ∀ {m} (f : Bits m → R.ℤ√2) → ι (S.Σb f) ≡ RL.Σb (λ x → ι (f x))
Σb-ι {zero}  f = refl
Σb-ι {suc m} f =
  trans (ι-+ (S.Σb (λ bs → f (false ∷ bs))) (S.Σb (λ bs → f (true ∷ bs))))
        (cong₂ DR._+_ (Σb-ι (λ bs → f (false ∷ bs))) (Σb-ι (λ bs → f (true ∷ bs))))

private
  π π⁻ : Fin N → Fin N
  π k = RM.idx (code k)
  π⁻ j = index (RM.bits n j)

  Π : Permutation N N
  Π = permutation π π⁻
        (λ j → trans (cong RM.idx (code-index (RM.bits n j))) (RM.idx-bits n j))
        (λ k → trans (cong index (RM.bits-idx (code k))) (index-code k))

sum-code : (h : Bits n → D) → sum (λ k → h (code k)) ≡ RL.Σb h
sum-code h = begin
  sum (λ k → h (code k))                     ≡⟨ sum-cong-≗ (λ k → cong h (sym (RM.bits-idx (code k)))) ⟩
  sum (λ k → h (RM.bits n (π k)))            ≡⟨ sym (sum-permute (λ j → h (RM.bits n j)) Π) ⟩
  sum (λ j → h (RM.bits n j))                ≡⟨ RM.Σb-sum n (λ j → h (RM.bits n j)) ⟩
  RL.Σb {n} (λ v → h (RM.bits n (RM.idx {n} v)))
                                             ≡⟨ RL.Σ-cong {n} (λ v → cong h (RM.bits-idx {n} v)) ⟩
  RL.Σb h                                    ∎
  where open ≡-Reasoning

------------------------------------------------------------------------
-- The matrix of a scaled matrix

Φ : S.Scaled n → Matrix N N D
Φ s = mk (λ r c → √½^ (proj₁ s) DR.* ι (proj₂ s (code r) (code c)))

ent-Φ : ∀ s r c → ent (Φ s) r c ≡ √½^ (proj₁ s) DR.* ι (proj₂ s (code r) (code c))
ent-Φ s = ent-mk (λ r c → √½^ (proj₁ s) DR.* ι (proj₂ s (code r) (code c)))

Φ-≐ : ∀ {ℓ M M′} → M S.≐ M′ → Φ (ℓ , M) ≡ Φ (ℓ , M′)
Φ-≐ {ℓ} {M} {M′} e = mat-ext λ r c →
  trans (ent-Φ (ℓ , M) r c) (trans (cong (λ x → √½^ ℓ DR.* ι x) (e (code r) (code c))) (sym (ent-Φ (ℓ , M′) r c)))

-- Φ is a monoid homomorphism.
Φ-ε : Φ S.ε∙ ≡ 𝕀
Φ-ε = mat-ext λ r c →
  trans (ent-Φ S.ε∙ r c) (trans (DR.*-identityˡ _) (trans (ι-δb r c) (sym (ent-𝕀 r c))))

Φ-∙ : ∀ s t → Φ (s S.∙ t) ≡ Φ s ·*· Φ t
Φ-∙ (ℓ₁ , M) (ℓ₂ , M′) = mat-ext λ r c → begin
  ent (Φ ((ℓ₁ , M) S.∙ (ℓ₂ , M′))) r c
    ≡⟨ ent-Φ ((ℓ₁ , M) S.∙ (ℓ₂ , M′)) r c ⟩
  √½^ (ℓ₁ +ℕ ℓ₂) DR.* ι (S.Σb (λ z → M (code r) z R.* M′ z (code c)))
    ≡⟨ cong₂ DR._*_ (√½^-+ ℓ₁ ℓ₂)
         (trans (Σb-ι (λ z → M (code r) z R.* M′ z (code c)))
           (trans (RL.Σ-cong (λ z → ι-* (M (code r) z) (M′ z (code c))))
                  (sym (sum-code (λ z → ι (M (code r) z) DR.* ι (M′ z (code c))))))) ⟩
  (√½^ ℓ₁ DR.* √½^ ℓ₂) DR.* sum (λ k → ι (M (code r) (code k)) DR.* ι (M′ (code k) (code c)))
    ≡⟨ *-distribˡ-sum (√½^ ℓ₁ DR.* √½^ ℓ₂) (λ k → ι (M (code r) (code k)) DR.* ι (M′ (code k) (code c))) ⟩
  sum (λ k → (√½^ ℓ₁ DR.* √½^ ℓ₂) DR.* (ι (M (code r) (code k)) DR.* ι (M′ (code k) (code c))))
    ≡⟨ sum-cong-≗ (λ k → interchange (√½^ ℓ₁) (√½^ ℓ₂) (ι (M (code r) (code k))) (ι (M′ (code k) (code c)))) ⟩
  sum (λ k → (√½^ ℓ₁ DR.* ι (M (code r) (code k))) DR.* (√½^ ℓ₂ DR.* ι (M′ (code k) (code c))))
    ≡⟨ sym (sum-cong-≗ (λ k → cong₂ DR._*_ (ent-Φ (ℓ₁ , M) r k) (ent-Φ (ℓ₂ , M′) k c))) ⟩
  sum (λ k → ent (Φ (ℓ₁ , M)) r k DR.* ent (Φ (ℓ₂ , M′)) k c)
    ≡⟨ sym (ent-·*· (Φ (ℓ₁ , M)) (Φ (ℓ₂ , M′)) r c) ⟩
  ent (Φ (ℓ₁ , M) ·*· Φ (ℓ₂ , M′)) r c ∎
  where open ≡-Reasoning

-- Φ identifies localised-equal pairs.
private
  cancel : ∀ u v U V x y → u DR.* U ≡ DR.1# → v DR.* V ≡ DR.1# → V DR.* x ≡ U DR.* y → u DR.* x ≡ v DR.* y
  cancel u v U V x y uU vV e = begin
    u DR.* x                             ≡⟨ sym (DR.*-identityʳ (u DR.* x)) ⟩
    (u DR.* x) DR.* DR.1#                ≡⟨ cong ((u DR.* x) DR.*_) (sym vV) ⟩
    (u DR.* x) DR.* (v DR.* V)           ≡⟨ interchange u x v V ⟩
    (u DR.* v) DR.* (x DR.* V)           ≡⟨ cong ((u DR.* v) DR.*_) (trans (DR.*-comm x V) e) ⟩
    (u DR.* v) DR.* (U DR.* y)           ≡⟨ interchange u v U y ⟩
    (u DR.* U) DR.* (v DR.* y)           ≡⟨ cong (DR._* (v DR.* y)) uU ⟩
    DR.1# DR.* (v DR.* y)                ≡⟨ DR.*-identityˡ (v DR.* y) ⟩
    v DR.* y                             ∎
    where open ≡-Reasoning

Φ-~ : ∀ {s t} → s S.~ t → Φ s ≡ Φ t
Φ-~ {ℓ , M} {ℓ′ , M′} e = mat-ext λ r c →
  trans (ent-Φ (ℓ , M) r c)
    (trans (cancel (√½^ ℓ) (√½^ ℓ′) (√2^ᴰ ℓ) (√2^ᴰ ℓ′) (ι (M (code r) (code c))) (ι (M′ (code r) (code c)))
                   (√½√2^ ℓ) (√½√2^ ℓ′)
                   (trans (cong₂ DR._*_ (sym (ι-√2^ ℓ′)) refl)
                     (trans (sym (ι-* (R.√2^ ℓ′) (M (code r) (code c))))
                       (trans (cong ι (e (code r) (code c)))
                         (trans (ι-* (R.√2^ ℓ) (M′ (code r) (code c))) (cong₂ DR._*_ (ι-√2^ ℓ) refl))))))
           (sym (ent-Φ (ℓ′ , M′) r c)))

------------------------------------------------------------------------
-- The generators

-- Their matrices, numbered by code.
⟦_⟧c : G.Gen N → S.Scaled n
⟦ −1[ a ] ⟧c    = 0 , negOp (code a)
⟦ X[ a , b ] ⟧c = 0 , swapOp (code a) (code b)
⟦ H[ a , b ] ⟧c = 1 , hadOp (code a) (code b)

-- An entry of the matrix of a word.
ent-⟦⟧ : ∀ (w : Word (Gen N)) r c → ent ⟦ w ⟧ᵐ r c ≡ actVʷ w (col 𝕀 c) ! r
ent-⟦⟧ w r c = cong (_! r) (col-actMʷ w 𝕀 c)

private
  -- (−1)_[a].
  letZ : ∀ a r c → √½^ 0 DR.* ι (negOp (code a) (code r) (code c)) ≡ actV (i-gen a) (col 𝕀 c) ! r
  letZ a r c = trans (DR.*-identityˡ _) (by r (r FinP.≟ a))
    where
    by : ∀ r → Dec (r ≡ a) → ι (negOp (code a) (code r) (code c)) ≡ actV (i-gen a) (col 𝕀 c) ! r
    by r (yes refl) =
      trans (cong (λ x → ι (x R.* S.δb (code r) (code c))) (if-t (eqB-refl (code r))))
        (trans (ι-* R.-1# (S.δb (code r) (code c)))
          (trans (cong (-1ᴰ DR.*_) (trans (ι-δb r c) (sym (e! c r)))) (sym (actV-ia r (col 𝕀 c)))))
    by r (no ra) =
      trans (cong (λ x → ι (x R.* S.δb (code r) (code c))) (if-f (eqB-code ra)))
        (trans (ι-* R.1# (S.δb (code r) (code c)))
          (trans (DR.*-identityˡ _)
            (trans (trans (ι-δb r c) (sym (e! c r))) (sym (actV-i≢ a (col 𝕀 c) ra)))))

  -- X_[a,b]: the entries of the exchange.
  module SwapE (a b : Fin N) (ab : a ≢ b) (c : Fin N) where

    at-a : ι (swapOp (code a) (code b) (code a) (code c)) ≡ δ b c
    at-a = trans (cong (λ x → ι (S.δb x (code c))) (if-t (eqB-refl (code a)))) (ι-δb b c)

    at-b : ι (swapOp (code a) (code b) (code b) (code c)) ≡ δ a c
    at-b = trans (cong (λ x → ι (S.δb x (code c)))
                   (trans (if-f (eqB-code (λ e → ab (sym e)))) (if-t (eqB-refl (code b)))))
                 (ι-δb a c)

    at-o : ∀ {r} → r ≢ a → r ≢ b → ι (swapOp (code a) (code b) (code r) (code c)) ≡ δ r c
    at-o ra rb = trans (cong (λ x → ι (S.δb x (code c))) (trans (if-f (eqB-code ra)) (if-f (eqB-code rb))))
                       (ι-δb _ c)

  letX : ∀ a b (t : Tri (a < b) (a ≡ b) (b < a)) → a ≢ b → ∀ r c →
         √½^ 0 DR.* ι (swapOp (code a) (code b) (code r) (code c)) ≡ actVʷ (φX a b t) (col 𝕀 c) ! r
  letX a b (tri≈ _ e _) ab r c = ⊥-elim (ab e)
  letX a b (tri< lt _ _) ab r c = trans (DR.*-identityˡ _) (by r (r FinP.≟ a) (r FinP.≟ b))
    where
    open SwapE a b ab c
    v = col 𝕀 c
    by : ∀ r → Dec (r ≡ a) → Dec (r ≡ b) → ι (swapOp (code a) (code b) (code r) (code c)) ≡ actV (X-gen a b lt) v ! r
    by r (yes refl) _        = trans at-a (trans (sym (e! c b)) (sym (actV-Xa lt v)))
    by r (no ra) (yes refl)  = trans at-b (trans (sym (e! c a)) (sym (actV-Xb lt v)))
    by r (no ra) (no rb)     = trans (at-o ra rb) (trans (sym (e! c r)) (sym (actV-X≢ lt v ra rb)))
  letX a b (tri> _ _ gt) ab r c = trans (DR.*-identityˡ _) (by r (r FinP.≟ a) (r FinP.≟ b))
    where
    open SwapE a b ab c
    v = col 𝕀 c
    by : ∀ r → Dec (r ≡ a) → Dec (r ≡ b) → ι (swapOp (code a) (code b) (code r) (code c)) ≡ actV (X-gen b a gt) v ! r
    by r (yes refl) _        = trans at-a (trans (sym (e! c b)) (sym (actV-Xb gt v)))
    by r (no ra) (yes refl)  = trans at-b (trans (sym (e! c a)) (sym (actV-Xa gt v)))
    by r (no ra) (no rb)     = trans (at-o ra rb) (trans (sym (e! c r)) (sym (actV-X≢ gt v rb ra)))

  -- H_[a,b]: the entries of the Hadamard, and of the two words.
  module HadE (a b : Fin N) (ab : a ≢ b) (c : Fin N) where

    v = col 𝕀 c

    row-a : ι (hadOp (code a) (code b) (code a) (code c)) ≡ δ a c DR.+ δ b c
    row-a = trans (cong ι (if-t (eqB-refl (code a)))) (by c (c FinP.≟ a) (c FinP.≟ b))
      where
      by : ∀ c → Dec (c ≡ a) → Dec (c ≡ b) →
           ι (if eqB (code c) (code a) then R.1# else if eqB (code c) (code b) then R.1# else R.0#) ≡ δ a c DR.+ δ b c
      by c (yes refl) _ = trans (cong ι (if-t (eqB-refl (code c))))
                            (sym (trans (cong₂ DR._+_ (δ-refl c) (δ-≢ (λ e → ab (sym e)))) (DR.+-identityʳ DR.1#)))
      by c (no ca) (yes refl) = trans (cong ι (trans (if-f (eqB-code ca)) (if-t (eqB-refl (code c)))))
                                  (sym (trans (cong₂ DR._+_ (δ-≢ ab) (δ-refl c)) (DR.+-identityˡ DR.1#)))
      by c (no ca) (no cb) = trans (cong ι (trans (if-f (eqB-code ca)) (if-f (eqB-code cb))))
                               (sym (trans (cong₂ DR._+_ (δ-≢ (λ e → ca (sym e))) (δ-≢ (λ e → cb (sym e))))
                                           (DR.+-identityʳ DR.0#)))

    row-b : ι (hadOp (code a) (code b) (code b) (code c)) ≡ δ a c DR.- δ b c
    row-b = trans (cong ι (trans (if-f (eqB-code (λ e → ab (sym e)))) (if-t (eqB-refl (code b)))))
                  (by c (c FinP.≟ a) (c FinP.≟ b))
      where
      by : ∀ c → Dec (c ≡ a) → Dec (c ≡ b) →
           ι (if eqB (code c) (code a) then R.1# else if eqB (code c) (code b) then R.-1# else R.0#) ≡ δ a c DR.- δ b c
      by c (yes refl) _ = trans (cong ι (if-t (eqB-refl (code c))))
                            (sym (trans (cong₂ DR._-_ (δ-refl c) (δ-≢ (λ e → ab (sym e))))
                                        (trans (cong (DR.1# DR.+_) neg0) (DR.+-identityʳ DR.1#))))
      by c (no ca) (yes refl) = trans (cong ι (trans (if-f (eqB-code ca)) (if-t (eqB-refl (code c)))))
                                  (trans -1≡ (sym (trans (cong₂ DR._-_ (δ-≢ ab) (δ-refl c)) (DR.+-identityˡ (DR.- DR.1#)))))
      by c (no ca) (no cb) = trans (cong ι (trans (if-f (eqB-code ca)) (if-f (eqB-code cb))))
                               (sym (trans (cong₂ DR._-_ (δ-≢ (λ e → ca (sym e))) (δ-≢ (λ e → cb (sym e))))
                                           (trans (cong (DR.0# DR.+_) neg0) (DR.+-identityʳ DR.0#))))

    row-o : ∀ {r} → r ≢ a → r ≢ b → √½^ 1 DR.* ι (hadOp (code a) (code b) (code r) (code c)) ≡ δ r c
    row-o {r} ra rb =
      trans (cong (λ x → √½^ 1 DR.* ι x) (trans (if-f (eqB-code ra)) (if-f (eqB-code rb))))
        (trans (cong (√½^ 1 DR.*_) (trans (ι-* R.√2 (S.δb (code r) (code c))) (cong (√2ᴰ DR.*_) (ι-δb r c))))
          (trans (sym (DR.*-assoc (√½^ 1) √2ᴰ (δ r c)))
            (trans (cong (DR._* δ r c) (trans (cong (DR._* √2ᴰ) (DR.*-identityʳ √½)) √½*√2))
              (DR.*-identityˡ (δ r c)))))

    -- √½^ 1 is √½.
    one : ∀ x → √½^ 1 DR.* x ≡ √½ DR.* x
    one x = cong (DR._* x) (DR.*-identityʳ √½)

  letH : ∀ a b (t : Tri (a < b) (a ≡ b) (b < a)) → a ≢ b → ∀ r c →
         √½^ 1 DR.* ι (hadOp (code a) (code b) (code r) (code c)) ≡ actVʷ (φH a b t) (col 𝕀 c) ! r
  letH a b (tri≈ _ e _) ab r c = ⊥-elim (ab e)
  letH a b (tri< lt _ _) ab r c = by r (r FinP.≟ a) (r FinP.≟ b)
    where
    open HadE a b ab c
    by : ∀ r → Dec (r ≡ a) → Dec (r ≡ b) →
         √½^ 1 DR.* ι (hadOp (code a) (code b) (code r) (code c)) ≡ actV (K-gen a b lt) v ! r
    by r (yes refl) _ =
      trans (one _) (trans (cong (√½ DR.*_) (trans row-a (sym (cong₂ DR._+_ (e! c r) (e! c b)))))
                           (sym (actV-Ka lt v)))
    by r (no ra) (yes refl) =
      trans (one _) (trans (cong (√½ DR.*_) (trans row-b (sym (cong₂ DR._-_ (e! c a) (e! c r)))))
                           (sym (actV-Kb lt v)))
    by r (no ra) (no rb) = trans (row-o ra rb) (trans (sym (e! c r)) (sym (actV-K≢ lt v ra rb)))
  letH a b (tri> _ _ gt) ab r c = by r (r FinP.≟ a) (r FinP.≟ b)
    where
    open HadE a b ab c
    u = actV (X-gen b a gt) v
    w = actV (K-gen b a gt) u
    -- u exchanges the entries a and b of v.
    ub : u ! b ≡ v ! a
    ub = actV-Xa gt v
    ua : u ! a ≡ v ! b
    ua = actV-Xb gt v
    by : ∀ r → Dec (r ≡ a) → Dec (r ≡ b) →
         √½^ 1 DR.* ι (hadOp (code a) (code b) (code r) (code c)) ≡ actV (X-gen b a gt) w ! r
    by r (yes refl) _ =
      trans (one _)
        (trans (cong (√½ DR.*_) (trans row-a (sym (cong₂ DR._+_ (trans ub (e! c r)) (trans ua (e! c b))))))
          (trans (sym (actV-Ka gt u)) (sym (actV-Xb gt w))))
    by r (no ra) (yes refl) =
      trans (one _)
        (trans (cong (√½ DR.*_) (trans row-b (sym (cong₂ DR._-_ (trans ub (e! c a)) (trans ua (e! c r))))))
          (trans (sym (actV-Kb gt u)) (sym (actV-Xa gt w))))
    by r (no ra) (no rb) =
      trans (row-o ra rb)
        (trans (sym (e! c r))
          (trans (sym (actV-X≢ gt v rb ra)) (trans (sym (actV-K≢ gt u rb ra)) (sym (actV-X≢ gt w rb ra)))))

letter-ent : ∀ g → ProperG g → ∀ r c →
             √½^ (proj₁ ⟦ g ⟧c) DR.* ι (proj₂ ⟦ g ⟧c (code r) (code c)) ≡ actVʷ (φg g) (col 𝕀 c) ! r
letter-ent −1[ a ]    −1ᵖ     r c = letZ a r c
letter-ent X[ a , b ] (Xᵖ ne) r c = letX a b (FinP.<-cmp a b) ne r c
letter-ent H[ a , b ] (Hᵖ ne) r c = letH a b (FinP.<-cmp a b) ne r c

-- The generators' matrices are those of their translations.
letter : ∀ g → ProperG g → Φ ⟦ g ⟧c ≡ ⟦ φg g ⟧ᵐ
letter g pg = mat-ext λ r c →
  trans (ent-Φ ⟦ g ⟧c r c) (trans (letter-ent g pg r c) (sym (ent-⟦⟧ (φg g) r c)))

------------------------------------------------------------------------
-- Words

-- Any reading of words that Φ turns into a monoid homomorphism, and
-- that agrees with the translations on the generators, agrees with
-- them on proper words.
module Words (⟦_⟧W : Word (G.Gen N) → S.Scaled n)
             (W-ε : Φ ⟦ ε ⟧W ≡ 𝕀)
             (W-• : ∀ u v → Φ ⟦ u • v ⟧W ≡ Φ ⟦ u ⟧W ·*· Φ ⟦ v ⟧W)
             (W-g : ∀ g → ProperG g → Φ ⟦ [ g ]ʷ ⟧W ≡ ⟦ φg g ⟧ᵐ)
             where

  sem : ∀ u → Proper u → Φ ⟦ u ⟧W ≡ ⟦ φ u ⟧ᵐ
  sem [ g ]ʷ  pg        = W-g g pg
  sem ε       _         = W-ε
  sem (u • v) (pu , pv) = trans (W-• u v) (trans (cong₂ _·*·_ (sem u pu) (sem v pv)) (sym (⟦•⟧ᵐ (φ u) (φ v))))
