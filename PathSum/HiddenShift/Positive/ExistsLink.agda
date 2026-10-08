------------------------------------------------------------------------
-- Presentations of groups
--
-- In the first pass, a Clifford a_i makes d_i Clifford
--
-- PathSum.HiddenShift.Exists' first pass applies [HH] at b_i with
-- d_i ← a_i ⊕ s_L,i.  For that step to be Clifford-safe (PathSum.
-- HiddenShift.Positive.Class), a_i -- which the quotient mentions --
-- must stay Clifford if it was, and Boolean's Cl-hh gives that once
-- d_i, the substituted variable, is Clifford too.  It is: the phase
-- reads a_i through g(a ⊕ s_L), (a ⊕ s_L)·(b ⊕ s_R) and a·c, and d_i
-- through b·d, g(d), c·d and d·h, so that the two derivatives are
--
--   ∂_{a_i} = γ(a ⊕ s_L) ⊕ b_i ⊕ s_R,i ⊕ c_i,
--   ∂_{d_i} = γ(d) ⊕ b_i ⊕ c_i ⊕ h_i,
--
-- γ being the derivative of g in its coordinate i (∂-a″, ∂-d″).  If
-- the first is affine then so is γ -- read it at the paths where a ⊕ s_L
-- is anything and the rest 0 (ι) -- and then so is the second (g-link).
-- Here the path-sum is any stage of the first pass, known through
-- Exists' reading of its paths by label: ρ, with the present labels
-- read off the path (rd, fd) and the removed ones at their fixed values
-- (df); i is not done, so a_i and d_i are both present.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.Positive.ExistsLink (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; not; _∧_; _xor_)
open import Data.Bool.Properties using (xor-same; xor-comm)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (_∷_; lookup; tabulate)
open import Data.Vec.Properties using (lookup∘tabulate)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary.Decidable using (Dec; yes; no)

open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift M₀ using (boolᴾ; boolᴾ-resp)
open import PathSum.HiddenShift.Blocks using
  (Blk; A₁; B₁; C₂; D₂; E₃; H₃; Lbl; LAssign; _‹_›; Ret₁; module Phase;
   dot-∂⁰; dot-∂ˡ; dot-∂ʳ)
open import PathSum.HiddenShift.Positive.Boolean
open import PathSum.HiddenShift.Walsh using (lhalf; rhalf; _⊕ᵃ_)
open import PathSum.Polynomial using (Poly)

private
  t≢f : true ≢ false
  t≢f ()

  xor-cancelʳ′ : ∀ a b c → (a xor c) xor (b xor c) ≡ a xor b
  xor-cancelʳ′ false false false = refl
  xor-cancelʳ′ false false true  = refl
  xor-cancelʳ′ false true  false = refl
  xor-cancelʳ′ false true  true  = refl
  xor-cancelʳ′ true  false false = refl
  xor-cancelʳ′ true  false true  = refl
  xor-cancelʳ′ true  true  false = refl
  xor-cancelʳ′ true  true  true  = refl

  close-a : ∀ G X Y → (((G xor X) xor (Y xor false)) xor (false xor false)) xor
                      (false xor false) ≡ G xor (X xor Y)
  close-a false false false = refl
  close-a false false true  = refl
  close-a false true  false = refl
  close-a false true  true  = refl
  close-a true  false false = refl
  close-a true  false true  = refl
  close-a true  true  false = refl
  close-a true  true  true  = refl

  close-d : ∀ G B C H →
            (((false xor false) xor (false xor B)) xor (G xor C)) xor
            (false xor H) ≡ G xor ((B xor C) xor H)
  close-d false false false false = refl
  close-d false false false true  = refl
  close-d false false true  false = refl
  close-d false false true  true  = refl
  close-d false true  false false = refl
  close-d false true  false true  = refl
  close-d false true  true  false = refl
  close-d false true  true  true  = refl
  close-d true  false false false = refl
  close-d true  false false true  = refl
  close-d true  false true  false = refl
  close-d true  false true  true  = refl
  close-d true  true  false false = refl
  close-d true  true  false true  = refl
  close-d true  true  true  false = refl
  close-d true  true  true  true  = refl

  -- x ⊕ b ⊕ b is x.
  xx : ∀ x b → (x xor b) xor b ≡ x
  xx false false = refl
  xx false true  = refl
  xx true  false = refl
  xx true  true  = refl

  -- Solving a ⊕ b = e for a.
  solve-xor : ∀ {a b e} → a xor b ≡ e → a ≡ e xor b
  solve-xor {false} {false} refl = refl
  solve-xor {false} {true}  refl = refl
  solve-xor {true}  {false} refl = refl
  solve-xor {true}  {true}  refl = refl


module _ {m : ℕ} (g : Poly m 0) (s : Assign (m ℕ+ m)) where

  private
    sL sR : Fin m → Bool
    sL = lhalf {m} s
    sR = rhalf {m} s

  open Phase (boolᴾ g) (boolᴾ-resp g) sL sR using
    (Fblk; T₁; T₅; Fblk-∂; dflt)

  private
    g-∂⁰ : {u u′ : Fin m → Bool} → (∀ j → u j ≡ u′ j) →
           boolᴾ g u xor boolᴾ g u′ ≡ false
    g-∂⁰ {u} {u′} h =
      trans (cong (_xor boolᴾ g u′) (boolᴾ-resp g u u′ h))
            (xor-same (boolᴾ g u′))

  ----------------------------------------------------------------------
  -- The two derivatives, g kept

  -- a_i flips and nothing else changes.

  ∂-a″ : ∀ (Z Z′ : LAssign m) (i : Fin m) →
         (∀ j → j ≢ i → Z (A₁ , j) ≡ Z′ (A₁ , j)) →
         Z (A₁ , i) xor Z′ (A₁ , i) ≡ true →
         (∀ j → Z (B₁ , j) ≡ Z′ (B₁ , j)) →
         (∀ j → Z (C₂ , j) ≡ Z′ (C₂ , j)) →
         (∀ j → Z (D₂ , j) ≡ Z′ (D₂ , j)) →
         (∀ j → Z (E₃ , j) ≡ Z′ (E₃ , j)) →
         (∀ j → Z (H₃ , j) ≡ Z′ (H₃ , j)) →
         Fblk Z xor Fblk Z′ ≡
         (T₁ Z xor T₁ Z′) xor ((Z′ (B₁ , i) xor sR i) xor Z′ (C₂ , i))
  ∂-a″ Z Z′ i a ai b c d e h = trans (Fblk-∂ Z Z′)
    (trans (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
              (cong ((T₁ Z xor T₁ Z′) xor_) (dot-∂ˡ i aL aLi bR))
              (cong₂ _xor_ (dot-∂ˡ i a ai c) (dot-∂⁰ b d)))
              (cong₂ _xor_ (g-∂⁰ d) (dot-∂⁰ c d)))
              (cong₂ _xor_ (dot-∂⁰ c e) (dot-∂⁰ d h)))
      (close-a (T₁ Z xor T₁ Z′) (Z′ (B₁ , i) xor sR i) (Z′ (C₂ , i))))
    where
    aL : ∀ j → j ≢ i → (Z ‹ A₁ › ⊕ᵃ sL) j ≡ (Z′ ‹ A₁ › ⊕ᵃ sL) j
    aL j j≢i = cong (_xor sL j) (a j j≢i)

    aLi : (Z (A₁ , i) xor sL i) xor (Z′ (A₁ , i) xor sL i) ≡ true
    aLi = trans (xor-cancelʳ′ (Z (A₁ , i)) (Z′ (A₁ , i)) (sL i)) ai

    bR : ∀ j → (Z ‹ B₁ › ⊕ᵃ sR) j ≡ (Z′ ‹ B₁ › ⊕ᵃ sR) j
    bR j = cong (_xor sR j) (b j)

  -- d_i flips and nothing else changes.

  ∂-d″ : ∀ (Z Z′ : LAssign m) (i : Fin m) →
         (∀ j → Z (A₁ , j) ≡ Z′ (A₁ , j)) →
         (∀ j → Z (B₁ , j) ≡ Z′ (B₁ , j)) →
         (∀ j → Z (C₂ , j) ≡ Z′ (C₂ , j)) →
         (∀ j → j ≢ i → Z (D₂ , j) ≡ Z′ (D₂ , j)) →
         Z (D₂ , i) xor Z′ (D₂ , i) ≡ true →
         (∀ j → Z (E₃ , j) ≡ Z′ (E₃ , j)) →
         (∀ j → Z (H₃ , j) ≡ Z′ (H₃ , j)) →
         Fblk Z xor Fblk Z′ ≡
         (T₅ Z xor T₅ Z′) xor ((Z′ (B₁ , i) xor Z′ (C₂ , i)) xor Z′ (H₃ , i))
  ∂-d″ Z Z′ i a b c d di e h = trans (Fblk-∂ Z Z′)
    (trans (cong₂ _xor_ (cong₂ _xor_ (cong₂ _xor_
              (cong₂ _xor_ (g-∂⁰ aL) (dot-∂⁰ aL bR))
              (cong₂ _xor_ (dot-∂⁰ a c) (dot-∂ʳ i b d di)))
              (cong ((T₅ Z xor T₅ Z′) xor_) (dot-∂ʳ i c d di)))
              (cong₂ _xor_ (dot-∂⁰ c e) (dot-∂ˡ i d di h)))
      (close-d (T₅ Z xor T₅ Z′) (Z′ (B₁ , i)) (Z′ (C₂ , i)) (Z′ (H₃ , i))))
    where
    aL : ∀ j → (Z ‹ A₁ › ⊕ᵃ sL) j ≡ (Z′ ‹ A₁ › ⊕ᵃ sL) j
    aL j = cong (_xor sL j) (a j)

    bR : ∀ j → (Z ‹ B₁ › ⊕ᵃ sR) j ≡ (Z′ ‹ B₁ › ⊕ᵃ sR) j
    bR j = cong (_xor sR j) (b j)

  ----------------------------------------------------------------------
  -- A stage of the first pass

  module Link {d : Fin m → Bool} {sz : ℕ}
              (lab : Fin sz → Lbl m) (ρ : Assign sz → LAssign m)
              (rd : ∀ y p → ρ y (lab p) ≡ y p)
              (df : ∀ y ℓ → Ret₁ d ℓ ≡ false → ρ y ℓ ≡ dflt ℓ (ρ y))
              (fd : ∀ ℓ → Ret₁ d ℓ ≡ true → Σ (Fin sz) (λ p → lab p ≡ ℓ))
              (i : Fin m) (di : d i ≡ false) where

    -- The phase as a function of the path.

    Fv : Pt sz → Bool
    Fv p = Fblk (ρ (lookup p))

    -- A present label is read off the path.

    present : ∀ y ℓ (R : Ret₁ d ℓ ≡ true) → ρ y ℓ ≡ y (proj₁ (fd ℓ R))
    present y ℓ R = trans (cong (ρ y) (sym (proj₂ (fd ℓ R))))
                          (rd y (proj₁ (fd ℓ R)))

    -- Setting the variable at pv, labelled v, leaves a present label
    -- other than v alone ...

    keep-present : ∀ (pv : Fin sz) {v} → lab pv ≡ v → ∀ p b ℓ →
                   (R : Ret₁ d ℓ ≡ true) → ℓ ≢ v →
                   ρ (lookup (set p pv b)) ℓ ≡ ρ (lookup p) ℓ
    keep-present pv lv p b ℓ R ℓ≢v = trans (present (lookup (set p pv b)) ℓ R)
      (trans (lookup-set-there p b q≢pv) (sym (present (lookup p) ℓ R)))
      where
      q≢pv : proj₁ (fd ℓ R) ≢ pv
      q≢pv e = ℓ≢v (trans (sym (proj₂ (fd ℓ R))) (trans (cong lab e) lv))

    -- ... and so every a label other than v ...

    keep-A : ∀ (pv : Fin sz) {v} → lab pv ≡ v → ∀ p b t → (A₁ , t) ≢ v →
             ρ (lookup (set p pv b)) (A₁ , t) ≡ ρ (lookup p) (A₁ , t)
    keep-A pv lv p b t ne = keep-present pv lv p b (A₁ , t) refl ne

    -- ... and every label other than v, when v is a_i or d_i.

    keep : ∀ (pv : Fin sz) {v} → lab pv ≡ v →
           (∀ t → d t ≡ true → (A₁ , t) ≢ v) → ∀ p b ℓ → ℓ ≢ v →
           ρ (lookup (set p pv b)) ℓ ≡ ρ (lookup p) ℓ
    keep pv {v} lv hA p b ℓ ℓ≢v = go ℓ (Ret₁ d ℓ) refl ℓ≢v
      where
      y y′ : Assign sz
      y  = lookup (set p pv b)
      y′ = lookup p

      not-true : ∀ {c} → not c ≡ false → c ≡ true
      not-true {true}  _  = refl
      not-true {false} ()

      go : ∀ ℓ c → Ret₁ d ℓ ≡ c → ℓ ≢ v → ρ y ℓ ≡ ρ y′ ℓ
      go ℓ true  R ne = keep-present pv lv p b ℓ R ne
      go (A₁ , t) false () ne
      go (B₁ , t) false R ne = trans (df y (B₁ , t) R) (sym (df y′ (B₁ , t) R))
      go (C₂ , t) false () ne
      go (D₂ , t) false R ne = trans (df y (D₂ , t) R)
        (trans (cong (_xor sL t) (keep-A pv lv p b t (hA t (not-true R))))
               (sym (df y′ (D₂ , t) R)))
      go (E₃ , t) false () ne
      go (H₃ , t) false () ne

    -- The variable itself takes the value set.

    here : ∀ (pv : Fin sz) {v} → lab pv ≡ v → (R : Ret₁ d v ≡ true) →
           ∀ p b → ρ (lookup (set p pv b)) v ≡ b
    here pv lv R p b = trans (cong (ρ (lookup (set p pv b))) (sym lv))
      (trans (rd (lookup (set p pv b)) pv) (lookup-set-here p pv b))

    -- Present labels read affinely.

    Aff-present : ∀ ℓ → Ret₁ d ℓ ≡ true → Aff (λ p → ρ (lookup p) ℓ)
    Aff-present ℓ R = Aff-cong (λ p → sym (present (lookup p) ℓ R))
                               (Aff-lookup (proj₁ (fd ℓ R)))

    ----------------------------------------------------------------------
    -- γ, the derivative of g in coordinate i

    gb : Pt m → Bool
    gb w = boolᴾ g (lookup w)

    γ : Pt m → Bool
    γ w = gb (set w i true) xor gb (set w i false)

    γ-pair : ∀ (w : Pt m) c → gb (set w i (not c)) xor gb (set w i c) ≡ γ w
    γ-pair w false = refl
    γ-pair w true  = xor-comm (gb (set w i false)) (gb (set w i true))

    -- The a block shifted by s_L, and the d block, as points.

    Aw : Pt sz → Pt m
    Aw p = tabulate (λ t → ρ (lookup p) (A₁ , t) xor sL t)

    Dw : Pt sz → Pt m
    Dw p = tabulate (λ t → ρ (lookup p) (D₂ , t))

    -- Where a_i flips.

    module AtA (pa : Fin sz) (la : lab pa ≡ (A₁ , i)) where

      hA : ∀ t → d t ≡ true → _≢_ {A = Lbl m} (A₁ , t) (A₁ , i)
      hA t dt e = t≢f (trans (sym dt) (trans (cong d (cong proj₂ e)) di))

      Zc : Pt sz → Bool → LAssign m
      Zc p c = ρ (lookup (set p pa c))

      off : ∀ p c (ℓ : Lbl m) → ℓ ≢ (A₁ , i) → Zc p c ℓ ≡ ρ (lookup p) ℓ
      off p c ℓ ne = keep pa la hA p c ℓ ne

      agree : ∀ p (ℓ : Lbl m) → ℓ ≢ (A₁ , i) → Zc p true ℓ ≡ Zc p false ℓ
      agree p ℓ ne = trans (off p true ℓ ne) (sym (off p false ℓ ne))

      blk : ∀ {b} → b ≢ A₁ → ∀ {j : Fin m} → _≢_ {A = Lbl m} (b , j) (A₁ , i)
      blk ne e = ne (cong proj₁ e)

      at-i : ∀ p c → Zc p c (A₁ , i) ≡ c
      at-i p c = here pa la refl p c

      shifted : ∀ p c → ∀ t → (Zc p c ‹ A₁ › ⊕ᵃ sL) t ≡
                              lookup (set (Aw p) i (c xor sL i)) t
      shifted p c t = pick (t ≟ i)
        where
        pick : Dec (t ≡ i) → (Zc p c ‹ A₁ › ⊕ᵃ sL) t ≡
                             lookup (set (Aw p) i (c xor sL i)) t
        pick (yes t≡i) = subst (λ u → (Zc p c ‹ A₁ › ⊕ᵃ sL) u ≡
                                      lookup (set (Aw p) i (c xor sL i)) u)
          (sym t≡i)
          (trans (cong (_xor sL i) (at-i p c))
                 (sym (lookup-set-here (Aw p) i (c xor sL i))))
        pick (no t≢i)  = trans (cong (_xor sL t)
                                 (off p c (A₁ , t) (λ e → t≢i (cong proj₂ e))))
          (trans (sym (lookup∘tabulate
                        (λ t → ρ (lookup p) (A₁ , t) xor sL t) t))
                 (sym (lookup-set-there (Aw p) (c xor sL i) t≢i)))

      β : Pt sz → Bool
      β p = (ρ (lookup p) (B₁ , i) xor sR i) xor ρ (lookup p) (C₂ , i)

      ∂a : ∀ p → ∂ˢ Fv pa p ≡ γ (Aw p) xor β p
      ∂a p = trans (∂-a″ (Zc p true) (Zc p false) i
          (λ j j≢i → agree p (A₁ , j) (λ e → j≢i (cong proj₂ e)))
          (cong₂ _xor_ (at-i p true) (at-i p false))
          (λ j → agree p (B₁ , j) (blk (λ ())))
          (λ j → agree p (C₂ , j) (blk (λ ())))
          (λ j → agree p (D₂ , j) (blk (λ ())))
          (λ j → agree p (E₃ , j) (blk (λ ())))
          (λ j → agree p (H₃ , j) (blk (λ ()))))
        (cong₂ _xor_ g-part
          (cong₂ (λ u v → (u xor sR i) xor v)
                 (off p false (B₁ , i) (blk (λ ())))
                 (off p false (C₂ , i) (blk (λ ())))))
        where
        g-part : T₁ (Zc p true) xor T₁ (Zc p false) ≡ γ (Aw p)
        g-part = trans (cong₂ _xor_
          (boolᴾ-resp g _ _ (shifted p true))
          (boolᴾ-resp g _ _ (shifted p false)))
          (γ-pair (Aw p) (sL i))

    -- Where d_i flips.

    module AtD (pd : Fin sz) (ld : lab pd ≡ (D₂ , i)) where

      hA : ∀ t → d t ≡ true → _≢_ {A = Lbl m} (A₁ , t) (D₂ , i)
      hA t _ e = A≢D (cong proj₁ e)
        where
        A≢D : A₁ ≢ D₂
        A≢D ()

      Zc : Pt sz → Bool → LAssign m
      Zc p c = ρ (lookup (set p pd c))

      off : ∀ p c (ℓ : Lbl m) → ℓ ≢ (D₂ , i) → Zc p c ℓ ≡ ρ (lookup p) ℓ
      off p c ℓ ne = keep pd ld hA p c ℓ ne

      agree : ∀ p (ℓ : Lbl m) → ℓ ≢ (D₂ , i) → Zc p true ℓ ≡ Zc p false ℓ
      agree p ℓ ne = trans (off p true ℓ ne) (sym (off p false ℓ ne))

      blk : ∀ {b} → b ≢ D₂ → ∀ {j : Fin m} → _≢_ {A = Lbl m} (b , j) (D₂ , i)
      blk ne e = ne (cong proj₁ e)

      at-i : ∀ p c → Zc p c (D₂ , i) ≡ c
      at-i p c = here pd ld (cong not di) p c

      read : ∀ p c → ∀ t → (Zc p c ‹ D₂ ›) t ≡ lookup (set (Dw p) i c) t
      read p c t = pick (t ≟ i)
        where
        pick : Dec (t ≡ i) → (Zc p c ‹ D₂ ›) t ≡ lookup (set (Dw p) i c) t
        pick (yes t≡i) = subst (λ u → (Zc p c ‹ D₂ ›) u ≡
                                      lookup (set (Dw p) i c) u)
          (sym t≡i)
          (trans (at-i p c) (sym (lookup-set-here (Dw p) i c)))
        pick (no t≢i)  = trans (off p c (D₂ , t) (λ e → t≢i (cong proj₂ e)))
          (trans (sym (lookup∘tabulate (λ t → ρ (lookup p) (D₂ , t)) t))
                 (sym (lookup-set-there (Dw p) c t≢i)))

      β : Pt sz → Bool
      β p = (ρ (lookup p) (B₁ , i) xor ρ (lookup p) (C₂ , i)) xor
            ρ (lookup p) (H₃ , i)

      ∂d : ∀ p → ∂ˢ Fv pd p ≡ γ (Dw p) xor β p
      ∂d p = trans (∂-d″ (Zc p true) (Zc p false) i
          (λ j → agree p (A₁ , j) (blk (λ ())))
          (λ j → agree p (B₁ , j) (blk (λ ())))
          (λ j → agree p (C₂ , j) (blk (λ ())))
          (λ j j≢i → agree p (D₂ , j) (λ e → j≢i (cong proj₂ e)))
          (cong₂ _xor_ (at-i p true) (at-i p false))
          (λ j → agree p (E₃ , j) (blk (λ ())))
          (λ j → agree p (H₃ , j) (blk (λ ()))))
        (cong₂ _xor_
          (cong₂ _xor_ (boolᴾ-resp g _ _ (read p true))
                       (boolᴾ-resp g _ _ (read p false)))
          (cong₂ _xor_
            (cong₂ _xor_ (off p false (B₁ , i) (blk (λ ())))
                         (off p false (C₂ , i) (blk (λ ()))))
            (off p false (H₃ , i) (blk (λ ())))))

    ----------------------------------------------------------------------
    -- The link

    -- Points with a ⊕ s_L anything and everything else 0.

    aval : Pt m → Lbl m → Bool
    aval w (A₁ , t) = lookup w t xor sL t
    aval w (B₁ , t) = false
    aval w (C₂ , t) = false
    aval w (D₂ , t) = false
    aval w (E₃ , t) = false
    aval w (H₃ , t) = false

    ι : Pt m → Pt sz
    ι w = tabulate (λ q → aval w (lab q))

    private
      Aff-aval : ∀ ℓ → Aff (λ w → aval w ℓ)
      Aff-aval (A₁ , t) = Aff-xor (Aff-lookup t) (Aff-const (sL t))
      Aff-aval (B₁ , t) = Aff-const false
      Aff-aval (C₂ , t) = Aff-const false
      Aff-aval (D₂ , t) = Aff-const false
      Aff-aval (E₃ , t) = Aff-const false
      Aff-aval (H₃ , t) = Aff-const false

    AffMap-ι : AffMap ι
    AffMap-ι = AffMap-coords (λ q → Aff-cong
      (λ w → sym (lookup∘tabulate (λ q → aval w (lab q)) q))
      (Aff-aval (lab q)))

    Aw-ι : ∀ w → Aw (ι w) ≡ w
    Aw-ι w = vext λ t → trans
      (lookup∘tabulate (λ t → ρ (lookup (ι w)) (A₁ , t) xor sL t) t)
      (trans (cong (_xor sL t)
        (trans (present (lookup (ι w)) (A₁ , t) refl)
          (trans (lookup∘tabulate (λ q → aval w (lab q))
                                  (proj₁ (fd (A₁ , t) refl)))
                 (cong (aval w) (proj₂ (fd (A₁ , t) refl))))))
        (xx (lookup w t) (sL t)))

    -- The d block reads affinely.

    AffMap-Dw : AffMap Dw
    AffMap-Dw = AffMap-coords (λ t → Aff-cong
      (λ p → sym (lookup∘tabulate (λ t → ρ (lookup p) (D₂ , t)) t))
      (go t (Ret₁ d (D₂ , t)) refl))
      where
      go : ∀ t c → Ret₁ d (D₂ , t) ≡ c → Aff (λ p → ρ (lookup p) (D₂ , t))
      go t true  R = Aff-present (D₂ , t) R
      go t false R = Aff-cong (λ p → sym (df (lookup p) (D₂ , t) R))
        (Aff-xor (Aff-present (A₁ , t) refl) (Aff-const (sL t)))

    -- a_i Clifford makes γ affine, and so d_i Clifford.

    g-link : (pa pd : Fin sz) → lab pa ≡ (A₁ , i) → lab pd ≡ (D₂ , i) →
             Cl Fv pa → Cl Fv pd
    g-link pa pd la ld cl = Aff-cong (λ p → sym (AtD.∂d pd ld p))
      (Aff-xor (Aff-∘ aγ AffMap-Dw) βd)
      where
      Bi : Ret₁ d (B₁ , i) ≡ true
      Bi = cong not di

      βa : Aff (AtA.β pa la)
      βa = Aff-xor (Aff-xor (Aff-present (B₁ , i) Bi) (Aff-const (sR i)))
                   (Aff-present (C₂ , i) refl)

      βd : Aff (AtD.β pd ld)
      βd = Aff-xor (Aff-xor (Aff-present (B₁ , i) Bi)
                            (Aff-present (C₂ , i) refl))
                   (Aff-present (H₃ , i) refl)

      aγ : Aff γ
      aγ = Aff-cong (λ w → trans
        (sym (solve-xor (sym (AtA.∂a pa la (ι w)))))
        (cong γ (Aw-ι w)))
        (Aff-xor (Aff-∘ cl AffMap-ι) (Aff-∘ βa AffMap-ι))
