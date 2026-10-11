------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoding preserves the semantics of Z and CZ (Definition 8.2)
--
-- The letters of E(Z on wire p) are the signs (−1)_[s] on the basis
-- vectors s with bit p set, each vector once; as diagonal operators
-- their product is the sign of bit p, which is Z on wire p.  For CZ
-- the vectors have bits p and p + 1 set.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.EncodingSemantics.Diagonal where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; not ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List ; [] ; _∷_ ; foldr)
open import Data.Nat using (ℕ ; zero ; suc ; _<_) renaming (_+_ to _+ℕ_ ; _^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Vec using (Vec ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Soundness.Operators using (diag ; diag-⊙ ; diag-cong)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (code ; index ; code-index)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB ; negOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Auxiliary.WireForms
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
open import Examples.Groups.Real-Clifford+CH.Encoding
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Products
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Strings

module _ {m : ℕ} where
  private
    n : ℕ
    n = ₃₊ m
    idx : Bits n → Fin (2 ^ℕ n)
    idx = index n

  ----------------------------------------------------------------------
  -- The sign letters

  -- The sign of (−1)_[s] at a basis vector.
  sgn : Bits n → Bits n → 𝔽
  sgn s x = if eqB x s then -1# else 1#

  private
    negOp-idx : ∀ s → negOp (code n (idx s)) ≐ diag (sgn s)
    negOp-idx s = Eq.subst (λ v → negOp v ≐ diag (sgn s)) (Eq.sym (code-index n s)) (≐-refl (diag (sgn s)))

    zz-M : ∀ s s′ → proj₂ ⟦ zz (idx s) (idx s′) ⟧Y ≐ diag (λ x → sgn s x * sgn s′ x)
    zz-M s s′ = ≐-trans (⊙-cong (negOp-idx s) (negOp-idx s′)) (diag-⊙ (sgn s) (sgn s′))

    sum-zero : ∀ {A : Set} (cs : List A) (f : A → Word (GenP n)) →
               (∀ c → proj₁ ⟦ f c ⟧Y ≡ 0) → foldr (λ c k → proj₁ ⟦ f c ⟧Y +ℕ k) 0 cs ≡ 0
    sum-zero []       f h = Eq.refl
    sum-zero (c ∷ cs) f h = Eq.trans (Eq.cong₂ _+ℕ_ (h c) (sum-zero cs f h)) Eq.refl

    -- The two facts about a sign at a basis vector.
    sgn-hit : ∀ s x → x ≡ s → sgn s x ≡ -1#
    sgn-hit s x e = Eq.cong (λ b → if b then -1# else 1#) (eqB-complete x s e)

    sgn-miss : ∀ s x → x ≢ s → sgn s x ≡ 1#
    sgn-miss s x ne = Eq.cong (λ b → if b then -1# else 1#) (eqB-false x s ne)

    -- The diagonal reading of a product of sign letters over contexts.
    diag-letters : ∀ {k} (cs : List (Bits k)) (s₀ s₁ : Bits k → Bits n) →
                   proj₂ ⟦ ∏ cs (λ c → zz (idx (s₀ c)) (idx (s₁ c))) ⟧Y ≐
                   diag (∏ᶠ cs (λ c x → sgn (s₀ c) x * sgn (s₁ c) x))
    diag-letters cs s₀ s₁ =
      ≐-trans (∏-M {m = m} cs (λ c → zz (idx (s₀ c)) (idx (s₁ c))))
        (≐-trans (fold-cong cs (λ c → zz-M (s₀ c) (s₁ c)))
                 (diag-fold cs (λ c x → sgn (s₀ c) x * sgn (s₁ c) x)))

    ℓ-letters : ∀ {k} (cs : List (Bits k)) (s₀ s₁ : Bits k → Bits n) →
                proj₁ ⟦ ∏ cs (λ c → zz (idx (s₀ c)) (idx (s₁ c))) ⟧Y ≡ 0
    ℓ-letters cs s₀ s₁ =
      Eq.trans (∏-ℓ {m = m} cs (λ c → zz (idx (s₀ c)) (idx (s₁ c))))
               (sum-zero cs (λ c → zz (idx (s₀ c)) (idx (s₁ c))) (λ c → Eq.refl))

    -- From a diagonal reading to the semantic equivalence with a gate
    -- (1 , √2 · diag f).
    √2^1 : √2^ 1 ≡ √2
    √2^1 = Eq.refl

    diag-sem : (u : Word (GenP n)) (f : Bits n → 𝔽) → proj₁ ⟦ u ⟧Y ≡ 0 → proj₂ ⟦ u ⟧Y ≐ diag f →
               ⟦ u ⟧Y ~ (1 , √2 · diag f)
    diag-sem u f ℓ M =
      ≐-trans (·-cong √2^1 M)
        (≐-sym (≐-trans (·-cong (Eq.cong √2^_ ℓ) (≐-refl (√2 · diag f))) (·-1 (√2 · diag f))))

  ----------------------------------------------------------------------
  -- Z on wire p

  private
    gZ : ℕ → Bits (₁₊ m) → Bits n → 𝔽
    gZ p c x = sgn (str₁ p c false true) x * sgn (str₁ p c true true) x

    -- The product of the signs at a basis vector: −1 when bit p is set.
    ∏gZ : ∀ p x → p < n → ∏ᶠ (allBits (₁₊ m)) (gZ p) x ≡ zsgn p x
    ∏gZ p x q with lookupℕ p x in bit
    ... | false = ∏ᶠ-one (allBits (₁₊ m)) (gZ p) x
      (λ c _ → Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (miss c false)) (sgn-miss _ x (miss c true))) (*-identityˡ 1#))
      where
      -- No letter is at x: the letters have bit p set.
      miss : ∀ c b → x ≢ str₁ p c b true
      miss c b e = true≢false (Eq.trans (Eq.sym (bit-str₁ p c b true q)) (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) bit))
        where
        true≢false : true ≢ false
        true≢false ()
    ... | true  =
      Eq.trans (∏ᶠ-unique (allBits (₁₊ m)) (gZ p) x (ctx₁ p x) (allBits-nodup (₁₊ m)) (∈-allBits (ctx₁ p x)) others)
               here
      where
      -- Only the context of x carries a letter at x.
      others : ∀ c → eqB c (ctx₁ p x) ≡ false → gZ p c x ≡ 1#
      others c ne = Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (miss false)) (sgn-miss _ x (miss true))) (*-identityˡ 1#)
        where
        miss : ∀ b → x ≢ str₁ p c b true
        miss b e = true≢false (Eq.trans (Eq.sym (eqB-refl (ctx₁ p x)))
                                        (Eq.trans (Eq.cong (λ v → eqB (ctx₁ p v) (ctx₁ p x)) e)
                                          (Eq.trans (Eq.cong (λ v → eqB v (ctx₁ p x)) (ctx-str₁ p c b true q)) ne)))
          where
          true≢false : true ≢ false
          true≢false ()
      -- At the context of x, the letter with the pairing bit of x is at
      -- x and the other is not.
      here : gZ p (ctx₁ p x) x ≡ -1#
      here with pr₁ p x in pb
      ... | false = Eq.trans (Eq.cong₂ _*_ (sgn-hit _ x (Eq.subst (λ b → x ≡ str₁ p (ctx₁ p x) b true) pb x≡))
                                         (sgn-miss _ x (other true (λ ()))))
                             (*-identityʳ -1#)
        where
        x≡ : x ≡ str₁ p (ctx₁ p x) (pr₁ p x) true
        x≡ = Eq.subst (λ g → x ≡ str₁ p (ctx₁ p x) (pr₁ p x) g) bit (Eq.sym (str-ctx₁ p x q))
        other : ∀ b → b ≢ false → x ≢ str₁ p (ctx₁ p x) b true
        other b ne e = ne (Eq.trans (Eq.sym (pr-str₁ p (ctx₁ p x) b true q)) (Eq.trans (Eq.cong (pr₁ p) (Eq.sym e)) pb))
      ... | true  = Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (other false (λ ())))
                                         (sgn-hit _ x (Eq.subst (λ b → x ≡ str₁ p (ctx₁ p x) b true) pb x≡)))
                             (*-identityˡ -1#)
        where
        x≡ : x ≡ str₁ p (ctx₁ p x) (pr₁ p x) true
        x≡ = Eq.subst (λ g → x ≡ str₁ p (ctx₁ p x) (pr₁ p x) g) bit (Eq.sym (str-ctx₁ p x q))
        other : ∀ b → b ≢ true → x ≢ str₁ p (ctx₁ p x) b true
        other b ne e = ne (Eq.trans (Eq.sym (pr-str₁ p (ctx₁ p x) b true q)) (Eq.trans (Eq.cong (pr₁ p) (Eq.sym e)) pb))

  E-Z-sem : ∀ p → p < n → ⟦ E-Z p ⟧Y ~ (1 , √2 · diag (zsgn p))
  E-Z-sem p q =
    diag-sem (E-Z p) (zsgn p)
      (ℓ-letters (allBits (₁₊ m)) (λ c → str₁ p c false true) (λ c → str₁ p c true true))
      (≐-trans (diag-letters (allBits (₁₊ m)) (λ c → str₁ p c false true) (λ c → str₁ p c true true))
               (diag-cong (λ x → ∏gZ p x q)))

  ----------------------------------------------------------------------
  -- CZ on wires p and p + 1

  private
    gCZ : ℕ → Bits m → Bits n → 𝔽
    gCZ p c x = sgn (str₂ p c false true true) x * sgn (str₂ p c true true true) x

    ∏gCZ : ∀ p x → suc p < n → ∏ᶠ (allBits m) (gCZ p) x ≡ czsgn p x
    ∏gCZ p x q with lookupℕ p x in bit | lookupℕ (suc p) x in ctl
    ... | false | _ = ∏ᶠ-one (allBits m) (gCZ p) x
      (λ c _ → Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (miss c false)) (sgn-miss _ x (miss c true))) (*-identityˡ 1#))
      where
      miss : ∀ c b → x ≢ str₂ p c b true true
      miss c b e = true≢false (Eq.trans (Eq.sym (bit-str₂ p c b true true q)) (Eq.trans (Eq.cong (lookupℕ p) (Eq.sym e)) bit))
        where
        true≢false : true ≢ false
        true≢false ()
    ... | true | false = ∏ᶠ-one (allBits m) (gCZ p) x
      (λ c _ → Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (miss c false)) (sgn-miss _ x (miss c true))) (*-identityˡ 1#))
      where
      miss : ∀ c b → x ≢ str₂ p c b true true
      miss c b e = true≢false (Eq.trans (Eq.sym (ctl-str₂ p c b true true q)) (Eq.trans (Eq.cong (lookupℕ (suc p)) (Eq.sym e)) ctl))
        where
        true≢false : true ≢ false
        true≢false ()
    ... | true | true =
      Eq.trans (∏ᶠ-unique (allBits m) (gCZ p) x (ctx₂ p x) (allBits-nodup m) (∈-allBits (ctx₂ p x)) others) here
      where
      others : ∀ c → eqB c (ctx₂ p x) ≡ false → gCZ p c x ≡ 1#
      others c ne = Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (miss false)) (sgn-miss _ x (miss true))) (*-identityˡ 1#)
        where
        miss : ∀ b → x ≢ str₂ p c b true true
        miss b e = true≢false (Eq.trans (Eq.sym (eqB-refl (ctx₂ p x)))
                                        (Eq.trans (Eq.cong (λ v → eqB (ctx₂ p v) (ctx₂ p x)) e)
                                          (Eq.trans (Eq.cong (λ v → eqB v (ctx₂ p x)) (ctx-str₂ p c b true true q)) ne)))
          where
          true≢false : true ≢ false
          true≢false ()
      x≡ : x ≡ str₂ p (ctx₂ p x) (pr₂ p x) true true
      x≡ = Eq.subst₂ (λ u t → x ≡ str₂ p (ctx₂ p x) (pr₂ p x) u t) ctl bit (Eq.sym (str-ctx₂ p x q))
      other : ∀ b → b ≢ pr₂ p x → x ≢ str₂ p (ctx₂ p x) b true true
      other b ne e = ne (Eq.trans (Eq.sym (pr-str₂ p (ctx₂ p x) b true true q)) (Eq.cong (pr₂ p) (Eq.sym e)))
      here : gCZ p (ctx₂ p x) x ≡ -1#
      here with pr₂ p x in pb
      ... | false = Eq.trans (Eq.cong₂ _*_ (sgn-hit _ x (Eq.subst (λ b → x ≡ str₂ p (ctx₂ p x) b true true) pb x≡))
                                         (sgn-miss _ x (other true (λ e → true≢false (Eq.trans e pb)))))
                             (*-identityʳ -1#)
        where
        true≢false : true ≢ false
        true≢false ()
      ... | true  = Eq.trans (Eq.cong₂ _*_ (sgn-miss _ x (other false (λ e → true≢false (Eq.trans (Eq.sym pb) (Eq.sym e)))))
                                         (sgn-hit _ x (Eq.subst (λ b → x ≡ str₂ p (ctx₂ p x) b true true) pb x≡)))
                             (*-identityˡ -1#)
        where
        true≢false : true ≢ false
        true≢false ()

  E-CZ-sem : ∀ p → suc p < n → ⟦ E-CZ p ⟧Y ~ (1 , √2 · diag (czsgn p))
  E-CZ-sem p q =
    diag-sem (E-CZ p) (czsgn p)
      (ℓ-letters (allBits m) (λ c → str₂ p c false true true) (λ c → str₂ p c true true true))
      (≐-trans (diag-letters (allBits m) (λ c → str₂ p c false true true) (λ c → str₂ p c true true true))
               (diag-cong (λ x → ∏gCZ p x q)))
