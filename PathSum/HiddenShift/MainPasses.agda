------------------------------------------------------------------------
-- Presentations of groups
--
-- The three passes of the hidden shift reduction, for any path-sum
-- with the circuit's values
--
-- PathSum.HiddenShift.Exists reduces the hidden shift composite on |0⟩
-- (Amy, QPL 2018, section 5.2) in three passes over the coordinates
-- i < m of its six blocks of path variables a, b, c, d, e, h
-- (PathSum.HiddenShift.Blocks):
--
--   pass 1: [HH] at b_i with d_i ← a_i ⊕ s_L,i, then [Elim] of d_i;
--   pass 2: [HH] at c_i with e_i ← s_L,i,       then [Elim] of e_i;
--   pass 3: [HH] at a_i with h_i ← s_R,i,       then [Elim] of h_i.
--
-- This module runs the same passes on the labelled machine of
-- PathSum.HiddenShift.Engine, for any path-sum whose phase is ½ Fblk
-- of the blocks and whose outputs are e and h (or other outputs that
-- read no path variable but e and h), in two generalities the figure 3
-- circuits need.  The shift may depend on the input (sL, sR): in
-- figure 3(b) it is the second register, and the quotients a_i ⊕ s_L,i,
-- s_L,i and s_R,i are then inputs -- the caller gives them as
-- expressions (qL, qR) with those values.  And the path variables may
-- carry more labels than the six blocks (Lbl m ⊎ E): figure 3(a) has
-- the X gates' variables too, which a pass of their own removes first;
-- the three passes need of the extra labels only that, once removed,
-- they make the phase Fblk of the blocks (F-main).  Each step's
-- derivative is Blocks' ∂-b, ∂-c or ∂-a, applied to the two labelled
-- paths the machine flips; nothing here reads a polynomial.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.MainPasses (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _xor_)
open import Data.Bool.Properties using (xor-comm; xor-assoc; xor-same)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Sum.Properties using (≡-dec; inj₁-injective)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂)

open import PathSum.Assign using (_[_≔_]; ≔-here; ≔-there)
open import PathSum.Base using (PathSum)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Engine M₀ using
  (QExp; qlit; qin; qvar; _q⊕_; ⟦_⟧q; QOk; module Machine)
open import PathSum.HiddenShift.Exists M₀ using (module Sweep)
open import PathSum.HiddenShift.Walsh using (RespectsB)

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.Full M using (_⟶ᶠ*_)


------------------------------------------------------------------------
-- The passes

module Passes
  {m N : ℕ} {E : Set} (_≟ᴱ_ : DecidableEquality E)
  (gᵇ : (Fin m → Bool) → Bool) (gᵇ-resp : RespectsB gᵇ)
  (sL sR : Assign N → Fin m → Bool)
  (qL qR : Fin m → QExp (Lbl m ⊎ E) N)
  (qL-ok : ∀ Ret v u i → QOk Ret v u (qL i))
  (qR-ok : ∀ Ret v u i → QOk Ret v u (qR i))
  (qL-val : ∀ i x Z → ⟦ qL i ⟧q x Z ≡ sL x i)
  (qR-val : ∀ i x Z → ⟦ qR i ⟧q x Z ≡ sR x i)
  (F : Assign N → (Lbl m ⊎ E → Bool) → Bool)
  (G : Fin N → Assign N → (Lbl m ⊎ E → Bool) → Bool)
  (dflt : Assign N → Lbl m ⊎ E → (Lbl m ⊎ E → Bool) → Bool)
  (dflt-main : ∀ x ℓ Z → dflt x (inj₁ ℓ) Z ≡
               Phase.dflt gᵇ gᵇ-resp (sL x) (sR x) ℓ (λ ℓ′ → Z (inj₁ ℓ′)))
  (F-main : ∀ x Z → (∀ e → Z (inj₂ e) ≡ dflt x (inj₂ e) Z) →
            F x Z ≡ Phase.Fblk gᵇ gᵇ-resp (sL x) (sR x) (λ ℓ → Z (inj₁ ℓ)))
  (G-main : ∀ x Z Z′ → (∀ i → Z (inj₁ (E₃ , i)) ≡ Z′ (inj₁ (E₃ , i))) →
            (∀ i → Z (inj₁ (H₃ , i)) ≡ Z′ (inj₁ (H₃ , i))) →
            ∀ w → G w x Z ≡ G w x Z′)
  {K : ℕ} (ξ₀ : PathSum N K K)
  where

  Lab : Set
  Lab = Lbl m ⊎ E

  _≟ᴸ_ : DecidableEquality Lab
  _≟ᴸ_ = ≡-dec _≟ˡ_ _≟ᴱ_

  open Machine _≟ᴸ_ F G dflt ξ₀ public

  -- The labels still path variables during each pass: the blocks as
  -- Blocks' Ret₁, Ret₂, Ret₃ say, none of the extra ones.

  RetM₁ RetM₂ RetM₃ : (Fin m → Bool) → Lab → Bool
  RetM₁ d (inj₁ ℓ) = Ret₁ d ℓ
  RetM₁ d (inj₂ e) = false
  RetM₂ d (inj₁ ℓ) = Ret₂ d ℓ
  RetM₂ d (inj₂ e) = false
  RetM₃ d (inj₁ ℓ) = Ret₃ d ℓ
  RetM₃ d (inj₂ e) = false

  private
    RetM₁-resp : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
                 ∀ ℓ → RetM₁ d ℓ ≡ RetM₁ d′ ℓ
    RetM₁-resp h (inj₁ ℓ) = Ret₁-resp h ℓ
    RetM₁-resp h (inj₂ e) = refl

    RetM₂-resp : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
                 ∀ ℓ → RetM₂ d ℓ ≡ RetM₂ d′ ℓ
    RetM₂-resp h (inj₁ ℓ) = Ret₂-resp h ℓ
    RetM₂-resp h (inj₂ e) = refl

    RetM₃-resp : {d d′ : Fin m → Bool} → (∀ i → d i ≡ d′ i) →
                 ∀ ℓ → RetM₃ d ℓ ≡ RetM₃ d′ ℓ
    RetM₃-resp h (inj₁ ℓ) = Ret₃-resp h ℓ
    RetM₃-resp h (inj₂ e) = refl

    RetM₁₂ : ∀ ℓ → RetM₁ (λ _ → true) ℓ ≡ RetM₂ (λ _ → false) ℓ
    RetM₁₂ (inj₁ ℓ) = Ret₁₂ ℓ
    RetM₁₂ (inj₂ e) = refl

    RetM₂₃ : ∀ ℓ → RetM₂ (λ _ → true) ℓ ≡ RetM₃ (λ _ → false) ℓ
    RetM₂₃ (inj₁ ℓ) = Ret₂₃ ℓ
    RetM₂₃ (inj₂ e) = refl

    RetM₃-none : ∀ ℓ → RetM₃ (λ _ → true) ℓ ≡ false
    RetM₃-none (inj₁ ℓ) = Ret₃-none ℓ
    RetM₃-none (inj₂ e) = refl

    -- Labels of one block at different coordinates differ.

    crd≢ : ∀ {b : Blk} {t i : Fin m} → t ≢ i →
           inj₁ {B = E} (b , t) ≢ inj₁ (b , i)
    crd≢ ne e = ne (cong proj₂ (inj₁-injective e))

    -- The derivative on the blocks, from the derivative on all labels:
    -- with the extra labels removed, F is Fblk of the blocks.

    F-flip : ∀ {Ret : Lab → Bool} {v x Zt Zf} →
             (∀ e → Ret (inj₂ e) ≡ false) → FlipAt Ret v x Zt Zf →
             F x Zt xor F x Zf ≡
             Phase.Fblk gᵇ gᵇ-resp (sL x) (sR x) (λ ℓ → Zt (inj₁ ℓ)) xor
             Phase.Fblk gᵇ gᵇ-resp (sL x) (sR x) (λ ℓ → Zf (inj₁ ℓ))
    F-flip {x = x} {Zt = Zt} {Zf = Zf} off fl = cong₂ _xor_
      (F-main x Zt (λ e → dflt-t fl (inj₂ e) (off e)))
      (F-main x Zf (λ e → dflt-f fl (inj₂ e) (off e)))

    -- A block label whose fixed value is the same on both sides.

    same-dflt : ∀ x ℓ (Zt Zf : Lab → Bool) →
                Phase.dflt gᵇ gᵇ-resp (sL x) (sR x) ℓ (λ ℓ′ → Zt (inj₁ ℓ′)) ≡
                Phase.dflt gᵇ gᵇ-resp (sL x) (sR x) ℓ (λ ℓ′ → Zf (inj₁ ℓ′)) →
                dflt x (inj₁ ℓ) Zt ≡ dflt x (inj₁ ℓ) Zf
    same-dflt x ℓ Zt Zf e =
      trans (dflt-main x ℓ Zt) (trans e (sym (dflt-main x ℓ Zf)))

    xor-cancelˡ : ∀ a b → a xor (a xor b) ≡ b
    xor-cancelˡ a b =
      trans (sym (xor-assoc a a b)) (cong (_xor b) (xor-same a))

  ----------------------------------------------------------------------
  -- Pass 1: [HH] at b_i with d_i ← a_i ⊕ s_L,i, then [Elim] of d_i

  pass₁ : ∀ d i → d i ≡ false → State (RetM₁ d) →
          State (RetM₁ (d [ i ≔ true ]))
  pass₁ d i di st =
    step st S (RetM₁ (d [ i ≔ true ]))
         (cong not (≔-here d i true)) (cong not (≔-here d i true)) R′
    where
    v u : Lab
    v = inj₁ (B₁ , i)
    u = inj₁ (D₂ , i)

    ∂F₁ : ∀ x Zt Zf → FlipAt (RetM₁ d) v x Zt Zf →
          F x Zt xor F x Zf ≡
          Zf u xor ⟦ qvar (inj₁ (A₁ , i)) q⊕ qL i ⟧q x Zf
    ∂F₁ x Zt Zf fl = trans (F-flip (λ _ → refl) fl)
      (trans (Phase.∂-b gᵇ gᵇ-resp (sL x) (sR x)
                (λ ℓ → Zt (inj₁ ℓ)) (λ ℓ → Zf (inj₁ ℓ)) i
                A-kept B-kept (cong₂ _xor_ (flip-t fl) (flip-f fl))
                C-kept D-kept E-kept H-kept)
        (trans (xor-comm (Zf (inj₁ (A₁ , i)) xor sL x i) (Zf u))
               (cong (λ t → Zf u xor (Zf (inj₁ (A₁ , i)) xor t))
                     (sym (qL-val i x Zf)))))
      where
      A-kept : ∀ t → Zt (inj₁ (A₁ , t)) ≡ Zf (inj₁ (A₁ , t))
      A-kept t = kept fl (inj₁ (A₁ , t)) refl (λ ())

      B-kept : ∀ t → t ≢ i → Zt (inj₁ (B₁ , t)) ≡ Zf (inj₁ (B₁ , t))
      B-kept t t≢i = kept-or-fixed fl (inj₁ (B₁ , t)) (crd≢ t≢i)
        (λ _ → same-dflt x (B₁ , t) Zt Zf refl)

      C-kept : ∀ t → Zt (inj₁ (C₂ , t)) ≡ Zf (inj₁ (C₂ , t))
      C-kept t = kept fl (inj₁ (C₂ , t)) refl (λ ())

      D-kept : ∀ t → Zt (inj₁ (D₂ , t)) ≡ Zf (inj₁ (D₂ , t))
      D-kept t = kept-or-fixed fl (inj₁ (D₂ , t)) (λ ())
        (λ _ → same-dflt x (D₂ , t) Zt Zf (cong (_xor sL x t) (A-kept t)))

      E-kept : ∀ t → Zt (inj₁ (E₃ , t)) ≡ Zf (inj₁ (E₃ , t))
      E-kept t = kept fl (inj₁ (E₃ , t)) refl (λ ())

      H-kept : ∀ t → Zt (inj₁ (H₃ , t)) ≡ Zf (inj₁ (H₃ , t))
      H-kept t = kept fl (inj₁ (H₃ , t)) refl (λ ())

    ∂G₁ : ∀ x Zt Zf → FlipAt (RetM₁ d) v x Zt Zf → ∀ w → G w x Zt ≡ G w x Zf
    ∂G₁ x Zt Zf fl = G-main x Zt Zf
      (λ t → kept fl (inj₁ (E₃ , t)) refl (λ ()))
      (λ t → kept fl (inj₁ (H₃ , t)) refl (λ ()))

    S : Step (RetM₁ d) v u
    S = record
      { v-on    = cong not di
      ; u-on    = cong not di
      ; v≢u     = λ ()
      ; quot    = qvar (inj₁ (A₁ , i)) q⊕ qL i
      ; quot-ok = (refl , (λ ()) , (λ ())) , qL-ok (RetM₁ d) v u i
      ; ∂F      = ∂F₁
      ; ∂G      = ∂G₁
      ; v-dflt  = λ x Z → dflt-main x (B₁ , i) Z
      ; u-dflt  = λ x Z → trans (dflt-main x (D₂ , i) Z)
                    (cong (Z (inj₁ (A₁ , i)) xor_) (sym (qL-val i x Z)))
      }

    R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → RetM₁ (d [ i ≔ true ]) ℓ ≡ RetM₁ d ℓ
    R′ (inj₁ (A₁ , t)) _  _  = refl
    R′ (inj₁ (B₁ , t)) ne _  =
      cong not (≔-there d true (λ e → ne (cong (λ s → inj₁ (B₁ , s)) e)))
    R′ (inj₁ (C₂ , t)) _  _  = refl
    R′ (inj₁ (D₂ , t)) _  ne =
      cong not (≔-there d true (λ e → ne (cong (λ s → inj₁ (D₂ , s)) e)))
    R′ (inj₁ (E₃ , t)) _  _  = refl
    R′ (inj₁ (H₃ , t)) _  _  = refl
    R′ (inj₂ e)        _  _  = refl

  ----------------------------------------------------------------------
  -- Pass 2: [HH] at c_i with e_i ← s_L,i, then [Elim] of e_i

  pass₂ : ∀ d i → d i ≡ false → State (RetM₂ d) →
          State (RetM₂ (d [ i ≔ true ]))
  pass₂ d i di st =
    step st S (RetM₂ (d [ i ≔ true ]))
         (cong not (≔-here d i true)) (cong not (≔-here d i true)) R′
    where
    v u : Lab
    v = inj₁ (C₂ , i)
    u = inj₁ (E₃ , i)

    ∂F₂ : ∀ x Zt Zf → FlipAt (RetM₂ d) v x Zt Zf →
          F x Zt xor F x Zf ≡ Zf u xor ⟦ qL i ⟧q x Zf
    ∂F₂ x Zt Zf fl = trans (F-flip (λ _ → refl) fl)
      (trans (Phase.∂-c gᵇ gᵇ-resp (sL x) (sR x)
                (λ ℓ → Zt (inj₁ ℓ)) (λ ℓ → Zf (inj₁ ℓ)) i
                A-kept B-kept C-kept (cong₂ _xor_ (flip-t fl) (flip-f fl))
                D-kept E-kept H-kept)
        (trans (cong (λ t → (Zf (inj₁ (A₁ , i)) xor t) xor Zf u)
                     (trans (dflt-f fl (inj₁ (D₂ , i)) refl)
                            (dflt-main x (D₂ , i) Zf)))
          (trans (cong (_xor Zf u)
                       (xor-cancelˡ (Zf (inj₁ (A₁ , i))) (sL x i)))
            (trans (xor-comm (sL x i) (Zf u))
                   (cong (Zf u xor_) (sym (qL-val i x Zf)))))))
      where
      A-kept : ∀ t → Zt (inj₁ (A₁ , t)) ≡ Zf (inj₁ (A₁ , t))
      A-kept t = kept fl (inj₁ (A₁ , t)) refl (λ ())

      B-kept : ∀ t → Zt (inj₁ (B₁ , t)) ≡ Zf (inj₁ (B₁ , t))
      B-kept t = kept-or-fixed fl (inj₁ (B₁ , t)) (λ ())
        (λ _ → same-dflt x (B₁ , t) Zt Zf refl)

      C-kept : ∀ t → t ≢ i → Zt (inj₁ (C₂ , t)) ≡ Zf (inj₁ (C₂ , t))
      C-kept t t≢i = kept-or-fixed fl (inj₁ (C₂ , t)) (crd≢ t≢i)
        (λ _ → same-dflt x (C₂ , t) Zt Zf refl)

      D-kept : ∀ t → Zt (inj₁ (D₂ , t)) ≡ Zf (inj₁ (D₂ , t))
      D-kept t = kept-or-fixed fl (inj₁ (D₂ , t)) (λ ())
        (λ _ → same-dflt x (D₂ , t) Zt Zf (cong (_xor sL x t) (A-kept t)))

      E-kept : ∀ t → Zt (inj₁ (E₃ , t)) ≡ Zf (inj₁ (E₃ , t))
      E-kept t = kept-or-fixed fl (inj₁ (E₃ , t)) (λ ())
        (λ _ → same-dflt x (E₃ , t) Zt Zf refl)

      H-kept : ∀ t → Zt (inj₁ (H₃ , t)) ≡ Zf (inj₁ (H₃ , t))
      H-kept t = kept fl (inj₁ (H₃ , t)) refl (λ ())

    ∂G₂ : ∀ x Zt Zf → FlipAt (RetM₂ d) v x Zt Zf → ∀ w → G w x Zt ≡ G w x Zf
    ∂G₂ x Zt Zf fl = G-main x Zt Zf
      (λ t → kept-or-fixed fl (inj₁ (E₃ , t)) (λ ())
               (λ _ → same-dflt x (E₃ , t) Zt Zf refl))
      (λ t → kept fl (inj₁ (H₃ , t)) refl (λ ()))

    S : Step (RetM₂ d) v u
    S = record
      { v-on    = cong not di
      ; u-on    = cong not di
      ; v≢u     = λ ()
      ; quot    = qL i
      ; quot-ok = qL-ok (RetM₂ d) v u i
      ; ∂F      = ∂F₂
      ; ∂G      = ∂G₂
      ; v-dflt  = λ x Z → dflt-main x (C₂ , i) Z
      ; u-dflt  = λ x Z → trans (dflt-main x (E₃ , i) Z) (sym (qL-val i x Z))
      }

    R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → RetM₂ (d [ i ≔ true ]) ℓ ≡ RetM₂ d ℓ
    R′ (inj₁ (A₁ , t)) _  _  = refl
    R′ (inj₁ (B₁ , t)) _  _  = refl
    R′ (inj₁ (C₂ , t)) ne _  =
      cong not (≔-there d true (λ e → ne (cong (λ s → inj₁ (C₂ , s)) e)))
    R′ (inj₁ (D₂ , t)) _  _  = refl
    R′ (inj₁ (E₃ , t)) _  ne =
      cong not (≔-there d true (λ e → ne (cong (λ s → inj₁ (E₃ , s)) e)))
    R′ (inj₁ (H₃ , t)) _  _  = refl
    R′ (inj₂ e)        _  _  = refl

  ----------------------------------------------------------------------
  -- Pass 3: [HH] at a_i with h_i ← s_R,i, then [Elim] of h_i

  pass₃ : ∀ d i → d i ≡ false → State (RetM₃ d) →
          State (RetM₃ (d [ i ≔ true ]))
  pass₃ d i di st =
    step st S (RetM₃ (d [ i ≔ true ]))
         (cong not (≔-here d i true)) (cong not (≔-here d i true)) R′
    where
    v u : Lab
    v = inj₁ (A₁ , i)
    u = inj₁ (H₃ , i)

    ∂F₃ : ∀ x Zt Zf → FlipAt (RetM₃ d) v x Zt Zf →
          F x Zt xor F x Zf ≡ Zf u xor ⟦ qR i ⟧q x Zf
    ∂F₃ x Zt Zf fl = trans (F-flip (λ _ → refl) fl)
      (trans (Phase.∂-a gᵇ gᵇ-resp (sL x) (sR x)
                (λ ℓ → Zt (inj₁ ℓ)) (λ ℓ → Zf (inj₁ ℓ)) i
                A-kept (cong₂ _xor_ (flip-t fl) (flip-f fl)) B-kept C-kept
                (λ t → trans (dflt-t fl (inj₁ (D₂ , t)) refl)
                             (dflt-main x (D₂ , t) Zt))
                (λ t → trans (dflt-f fl (inj₁ (D₂ , t)) refl)
                             (dflt-main x (D₂ , t) Zf))
                E-kept H-kept)
        (trans (xor-comm (sR x i) (Zf u))
               (cong (Zf u xor_) (sym (qR-val i x Zf)))))
      where
      A-kept : ∀ t → t ≢ i → Zt (inj₁ (A₁ , t)) ≡ Zf (inj₁ (A₁ , t))
      A-kept t t≢i = kept-or-fixed fl (inj₁ (A₁ , t)) (crd≢ t≢i)
        (λ _ → same-dflt x (A₁ , t) Zt Zf refl)

      B-kept : ∀ t → Zt (inj₁ (B₁ , t)) ≡ Zf (inj₁ (B₁ , t))
      B-kept t = kept-or-fixed fl (inj₁ (B₁ , t)) (λ ())
        (λ _ → same-dflt x (B₁ , t) Zt Zf refl)

      C-kept : ∀ t → Zt (inj₁ (C₂ , t)) ≡ Zf (inj₁ (C₂ , t))
      C-kept t = kept-or-fixed fl (inj₁ (C₂ , t)) (λ ())
        (λ _ → same-dflt x (C₂ , t) Zt Zf refl)

      E-kept : ∀ t → Zt (inj₁ (E₃ , t)) ≡ Zf (inj₁ (E₃ , t))
      E-kept t = kept-or-fixed fl (inj₁ (E₃ , t)) (λ ())
        (λ _ → same-dflt x (E₃ , t) Zt Zf refl)

      H-kept : ∀ t → Zt (inj₁ (H₃ , t)) ≡ Zf (inj₁ (H₃ , t))
      H-kept t = kept-or-fixed fl (inj₁ (H₃ , t)) (λ ())
        (λ _ → same-dflt x (H₃ , t) Zt Zf refl)

    ∂G₃ : ∀ x Zt Zf → FlipAt (RetM₃ d) v x Zt Zf → ∀ w → G w x Zt ≡ G w x Zf
    ∂G₃ x Zt Zf fl = G-main x Zt Zf
      (λ t → kept-or-fixed fl (inj₁ (E₃ , t)) (λ ())
               (λ _ → same-dflt x (E₃ , t) Zt Zf refl))
      (λ t → kept-or-fixed fl (inj₁ (H₃ , t)) (λ ())
               (λ _ → same-dflt x (H₃ , t) Zt Zf refl))

    S : Step (RetM₃ d) v u
    S = record
      { v-on    = cong not di
      ; u-on    = cong not di
      ; v≢u     = λ ()
      ; quot    = qR i
      ; quot-ok = qR-ok (RetM₃ d) v u i
      ; ∂F      = ∂F₃
      ; ∂G      = ∂G₃
      ; v-dflt  = λ x Z → dflt-main x (A₁ , i) Z
      ; u-dflt  = λ x Z → trans (dflt-main x (H₃ , i) Z) (sym (qR-val i x Z))
      }

    R′ : ∀ ℓ → ℓ ≢ v → ℓ ≢ u → RetM₃ (d [ i ≔ true ]) ℓ ≡ RetM₃ d ℓ
    R′ (inj₁ (A₁ , t)) ne _  =
      cong not (≔-there d true (λ e → ne (cong (λ s → inj₁ (A₁ , s)) e)))
    R′ (inj₁ (B₁ , t)) _  _  = refl
    R′ (inj₁ (C₂ , t)) _  _  = refl
    R′ (inj₁ (D₂ , t)) _  _  = refl
    R′ (inj₁ (E₃ , t)) _  _  = refl
    R′ (inj₁ (H₃ , t)) _  ne =
      cong not (≔-there d true (λ e → ne (cong (λ s → inj₁ (H₃ , s)) e)))
    R′ (inj₂ e)        _  _  = refl

  ----------------------------------------------------------------------
  -- The three passes

  -- Every coordinate through pass 1, then pass 2, then pass 3.

  passes : State (RetM₁ (λ _ → false)) → State (RetM₃ (λ _ → true))
  passes st =
    third (State-resp RetM₂₃ (second (State-resp RetM₁₂ (first st))))
    where
    first : State (RetM₁ (λ _ → false)) → State (RetM₁ (λ _ → true))
    first = Sweep.all (λ d → State (RetM₁ d))
                      (λ h → State-resp (RetM₁-resp h)) pass₁

    second : State (RetM₂ (λ _ → false)) → State (RetM₂ (λ _ → true))
    second = Sweep.all (λ d → State (RetM₂ d))
                       (λ h → State-resp (RetM₂-resp h)) pass₂

    third : State (RetM₃ (λ _ → false)) → State (RetM₃ (λ _ → true))
    third = Sweep.all (λ d → State (RetM₃ d))
                      (λ h → State-resp (RetM₃-resp h)) pass₃

  -- From a stage in which every block label is present and no extra
  -- one, a complete reduction of ξ₀.

  complete : State (RetM₁ (λ _ → false)) →
             Σ (PathSum N 0 0) (λ ζ → ξ₀ ⟶ᶠ* ζ)
  complete st = finish (passes st) RetM₃-none
