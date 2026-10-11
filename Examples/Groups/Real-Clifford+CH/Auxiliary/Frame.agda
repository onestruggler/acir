------------------------------------------------------------------------
-- Presentations of groups
--
-- The coset action through a fresh frame
--
-- Definition A.2's action h emits, for each auxiliary generator read
-- at a coset, a word of P, and item (b) of the Reidemeister–Schreier
-- method asks that the two sides of every rule of Figure 7 emit
-- equivalent words.  Read naively that is a case analysis on where the
-- rule's indices meet the distinguished indices 0 and 1, at each of
-- the four cosets: some two hundred equations.
--
-- They collapse.  Pick three indices e, f, g away from 0, 1 and from
-- the rule, and embed the generators uniformly,
--
--     Φ((−1)_[a]) = (−1)_[a] (−1)_[g]     Φ(X_[a,b]) = (−1)_[g] X_[a,b]
--     Φ(H_[a,b])  = H_[a,b] H_[e,f],
--
-- tagging each with a sign on the sink g or the frame's Hadamard on
-- e, f — both commute with everything the rule touches.  Then the
-- action is *conjugation* of that embedding by four fixed words,
--
--     h(c, y)  ≈  T c · Φ(y) · T⁻ c′        (c′ the coset reached),
--
-- with T ⟨ε⟩ = ε, T ⟨M⟩ = (−1)_[1] (−1)_[g], T ⟨K⟩ = H_[0,1] H_[e,f]
-- and T ⟨KM⟩ their product (`tr`).  That is some forty equations, one
-- per branch of the action, each decided by `FrameNorm.by-norm` or in a
-- line; and item (b) for a rule becomes the rule's image under Φ,
-- with no case analysis at all (`Frame.run`, and `ItemB`).
--
-- The whole transport was checked numerically first, at every
-- generator on eight indices and every coset (`scratchpad/tF.py`), and
-- each branch's normal forms were computed in Python before being
-- written here (`scratchpad/tN.py`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Frame (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (⊤ ; tt)
open import Data.Vec using (Vec ; [] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P
  using (GenP ; −1−1 ; −1X ; XX ; HH)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx ; xx)
import Examples.Groups.Real-Clifford+CH.Auxiliary.CosetAction as CA
import Examples.Groups.Real-Clifford+CH.Auxiliary.FrameAct m as FA
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; cat ; nil ; hf-zz ; gen-zx ; gen-xx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; δ ; NEG ; SWP ; L ; sp-zx ; eqv ; xor-self ; idSP)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-trans to ≐-trans′ ; ≐-sym to ≐-sym′
          ; ≐-refl to ≐-refl′ ; ⊙-cong to ⊙-cong′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m using (hfree-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (gen-hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m
  using (Distinct ; []ᵈ ; _∷ᵈ_ ; lookup-inj ; allAt ; tz ; ty ; tx ; ⌜_⌝ ; _•ᵗ_ ; emp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m
  using (Eq65 ; eq66 ; comm-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m using (fuse ; hh-cancel)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.FrameNorm m using (module Norm)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (−1[_] ; X[_,_] ; H[_,_])

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  zzʷ : Fin N → Fin N → W
  zzʷ = zz {₃₊ m}

  zxʷ : Fin N → Fin N → Fin N → W
  zxʷ = zx {₃₊ m}

  xxʷ : Fin N → Fin N → Fin N → Fin N → W
  xxʷ = xx {₃₊ m}

  hhʷ : Fin N → Fin N → Fin N → Fin N → W
  hhʷ = hh {₃₊ m}

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  zx-same : ∀ (c x : Fin N) → zxʷ c x x ≡ ε
  zx-same c x with x ≟ x
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  hh-same : ∀ (a c d : Fin N) → hhʷ a a c d ≡ ε
  hh-same a c d with a ≟ a
  ... | yes _  = Eq.refl
  ... | no  ne = ⊥-elim (ne Eq.refl)

  -- Boolean identities for the sign pairs.
  b₃ : ∀ (x y w : Bool) → x xor y ≡ (y xor w) xor (x xor w)
  b₃ false false false = Eq.refl
  b₃ false false true  = Eq.refl
  b₃ false true  false = Eq.refl
  b₃ false true  true  = Eq.refl
  b₃ true  false false = Eq.refl
  b₃ true  false true  = Eq.refl
  b₃ true  true  false = Eq.refl
  b₃ true  true  true  = Eq.refl

  b₃′ : ∀ (x y w : Bool) → x xor y ≡ (x xor w) xor ((y xor w) xor false)
  b₃′ false false false = Eq.refl
  b₃′ false false true  = Eq.refl
  b₃′ false true  false = Eq.refl
  b₃′ false true  true  = Eq.refl
  b₃′ true  false false = Eq.refl
  b₃′ true  false true  = Eq.refl
  b₃′ true  true  false = Eq.refl
  b₃′ true  true  true  = Eq.refl

  b₂ : ∀ (x w : Bool) → x xor false ≡ (x xor w) xor ((w xor false) xor false)
  b₂ false false = Eq.refl
  b₂ false true  = Eq.refl
  b₂ true  false = Eq.refl
  b₂ true  true  = Eq.refl

  -- A sign pair through a third index, in the two shapes the transport
  -- meets: `zz x y ≈ zz y w • zz x w` and `zz x y ≈ zz x w • (zz y w • ε)`.
  zz-tri : ∀ (x y w : Fin N) → zzʷ x y ≈ zzʷ y w • zzʷ x w
  zz-tri x y w =
    A5-full (gen (hf-zz x y)) (cat (gen (hf-zz y w)) (gen (hf-zz x w)))
            (eqv (λ i → b₃ (δ x i) (δ y i) (δ w i)) (λ _ → Eq.refl))

  zz-tri′ : ∀ (x y w : Fin N) → zzʷ x y ≈ zzʷ x w • (zzʷ y w • ε)
  zz-tri′ x y w =
    A5-full (gen (hf-zz x y)) (cat (gen (hf-zz x w)) (cat (gen (hf-zz y w)) nil))
            (eqv (λ i → b₃′ (δ x i) (δ y i) (δ w i)) (λ _ → Eq.refl))

  -- A mixed letter's sign moved onto another index.
  zx-split : ∀ (c w a b : Fin N) → a ≢ b → zxʷ c a b ≈ zzʷ c w • (zxʷ w a b • ε)
  zx-split c w a b ab =
    A5-full (hfree-zx c a b) (cat (gen (hf-zz c w)) (cat (hfree-zx w a b) nil))
      (≐-trans′ (sp-zx c a b ab)
      (≐-trans′ (eqv (λ i → b₂ (δ c i) (δ w i)) (λ _ → Eq.refl))
                (≐-sym′ (⊙-cong′ (≐-refl′ {NEG c ⊛ NEG w})
                                 (⊙-cong′ (sp-zx w a b ab) (≐-refl′ {idSP}))))))

------------------------------------------------------------------------
-- The cosets as the Klein four-group

-- A Hadamard moves between ⟨ε⟩ and ⟨K⟩, a sign or an exchange between
-- ⟨ε⟩ and ⟨M⟩, and the two commute.
infixl 6 _⊕_
_⊕_ : Coset → Coset → Coset
⟨ε⟩  ⊕ d    = d
⟨M⟩  ⊕ ⟨ε⟩  = ⟨M⟩
⟨M⟩  ⊕ ⟨M⟩  = ⟨ε⟩
⟨M⟩  ⊕ ⟨K⟩  = ⟨KM⟩
⟨M⟩  ⊕ ⟨KM⟩ = ⟨K⟩
⟨K⟩  ⊕ ⟨ε⟩  = ⟨K⟩
⟨K⟩  ⊕ ⟨M⟩  = ⟨KM⟩
⟨K⟩  ⊕ ⟨K⟩  = ⟨ε⟩
⟨K⟩  ⊕ ⟨KM⟩ = ⟨M⟩
⟨KM⟩ ⊕ ⟨ε⟩  = ⟨KM⟩
⟨KM⟩ ⊕ ⟨M⟩  = ⟨K⟩
⟨KM⟩ ⊕ ⟨K⟩  = ⟨M⟩
⟨KM⟩ ⊕ ⟨KM⟩ = ⟨ε⟩

tag : G.Gen N → Coset
tag −1[ _ ]    = ⟨M⟩
tag X[ _ , _ ] = ⟨M⟩
tag H[ _ , _ ] = ⟨K⟩

-- Where a word leads, generator by generator.
cos : Coset → Word (G.Gen N) → Coset
cos c [ y ]ʷ   = c ⊕ tag y
cos c ε        = c
cos c (u • v)  = cos (cos c u) v

------------------------------------------------------------------------
-- The frame

module Frame (e65 : Eq65) (z o : Fin N) (z≢o : z ≢ o) (e f g : Fin N)
             (ef : e ≢ f) (eg : e ≢ g) (fg : f ≢ g)
             (ez : e ≢ z) (eo : e ≢ o) (fz : f ≢ z) (fo : f ≢ o)
             (gz : g ≢ z) (go : g ≢ o) where

  open CA (₃₊ m) z o z≢o using (act)
  open FA.Branches z o z≢o

  private
    o≢z : o ≢ z
    o≢z = ≢sym z≢o

  -- The transition words and the embedding.
  T : Coset → W
  T ⟨ε⟩  = ε
  T ⟨M⟩  = zzʷ o g
  T ⟨K⟩  = hhʷ z o e f
  T ⟨KM⟩ = hhʷ z o e f • zzʷ o g

  T⁻ : Coset → W
  T⁻ ⟨ε⟩  = ε
  T⁻ ⟨M⟩  = zzʷ o g
  T⁻ ⟨K⟩  = hhʷ e f z o
  T⁻ ⟨KM⟩ = zzʷ o g • hhʷ e f z o

  Φ : G.Gen N → W
  Φ −1[ a ]    = zzʷ a g
  Φ X[ a , b ] = zxʷ g a b
  Φ H[ a , b ] = hhʷ a b e f

  -- An index away from the frame.
  Av : Fin N → Set
  Av a = (a ≢ e) × (a ≢ f) × (a ≢ g)

  Avoids : G.Gen N → Set
  Avoids −1[ a ]    = Av a
  Avoids X[ a , b ] = Av a × Av b
  Avoids H[ a , b ] = Av a × Av b

  Goal : Coset → G.Gen N → Set
  Goal c y = proj₁ (act c y) ≈ T c • (Φ y • T⁻ (proj₂ (act c y)))

  private
    ze : z ≢ e
    ze = ≢sym ez

    zf : z ≢ f
    zf = ≢sym fz

    oe : o ≢ e
    oe = ≢sym eo

    of′ : o ≢ f
    of′ = ≢sym fo

    -- The transitions cancel.
    TT⁻ : ∀ (c : Coset) → T c • T⁻ c ≈ ε
    TT⁻ ⟨ε⟩  = left-unit
    TT⁻ ⟨M⟩  = A5-full (cat (gen (hf-zz o g)) (gen (hf-zz o g))) nil
                       (eqv (λ i → xor-self (δ o i xor δ g i)) (λ _ → Eq.refl))
    TT⁻ ⟨K⟩  = hh-cancel e65 z o e f z≢o ze zf oe of′ ef
    TT⁻ ⟨KM⟩ = begin
      (hhʷ z o e f • zzʷ o g) • (zzʷ o g • hhʷ e f z o)
        ≈⟨ assoc ⟩
      hhʷ z o e f • (zzʷ o g • (zzʷ o g • hhʷ e f z o))
        ≈⟨ back (hhʷ z o e f) (sym assoc) ⟩
      hhʷ z o e f • ((zzʷ o g • zzʷ o g) • hhʷ e f z o)
        ≈⟨ back (hhʷ z o e f) (front (hhʷ e f z o) (TT⁻ ⟨M⟩)) ⟩
      hhʷ z o e f • (ε • hhʷ e f z o)
        ≈⟨ back (hhʷ z o e f) left-unit ⟩
      hhʷ z o e f • hhʷ e f z o
        ≈⟨ TT⁻ ⟨K⟩ ⟩
      ε ∎

    -- A degenerate generator emits nothing and stays.
    deg : ∀ (c : Coset) (u : W) → u ≡ ε → ε ≈ T c • (u • T⁻ c)
    deg c .ε Eq.refl = sym (trans (back (T c) left-unit) (TT⁻ c))

  -- Reading one branch of the action.
  via-act : ∀ (c : Coset) (y : G.Gen N) {w : W} {c′ : Coset} → act c y ≡ (w , c′) →
            w ≈ T c • (Φ y • T⁻ c′) → Goal c y
  via-act c y ex p = Eq.subst (λ q → proj₁ q ≈ T c • (Φ y • T⁻ (proj₂ q))) (Eq.sym ex) p

  -- The normaliser at a vector of indices.
  module NV {k : ℕ} (v : Vec (Fin N) k) (dv : Distinct v)
            (ae : All (λ y → y ≢ e) v) (af : All (λ y → y ≢ f) v) =
    Norm e65 (lookup v) (lookup-inj dv) e f ef (allAt ae) (allAt af)

  -- The three we use most: 0 1 g, 0 1 x g and 0 1 a b g.
  module N3 = NV (z ∷ o ∷ g ∷ [])
                 ((o≢z ∷ gz ∷ []) ∷ᵈ (go ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
                 (ze ∷ oe ∷ ≢sym eg ∷ []) (zf ∷ of′ ∷ ≢sym fg ∷ [])

  module N4 (x : Fin N) (xz : x ≢ z) (xo : x ≢ o) (av : Av x) =
    NV (z ∷ o ∷ x ∷ g ∷ [])
       ((o≢z ∷ xz ∷ gz ∷ []) ∷ᵈ (xo ∷ go ∷ []) ∷ᵈ (≢sym (proj₂ (proj₂ av)) ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
       (ze ∷ oe ∷ proj₁ av ∷ ≢sym eg ∷ []) (zf ∷ of′ ∷ proj₁ (proj₂ av) ∷ ≢sym fg ∷ [])

  module N5 (a b : Fin N) (az : a ≢ z) (ao : a ≢ o) (bz : b ≢ z) (bo : b ≢ o)
            (ba : b ≢ a) (av : Av a) (bv : Av b) =
    NV (z ∷ o ∷ a ∷ b ∷ g ∷ [])
       ((o≢z ∷ az ∷ bz ∷ gz ∷ []) ∷ᵈ (ao ∷ bo ∷ go ∷ []) ∷ᵈ
        (ba ∷ ≢sym (proj₂ (proj₂ av)) ∷ []) ∷ᵈ (≢sym (proj₂ (proj₂ bv)) ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
       (ze ∷ oe ∷ proj₁ av ∷ proj₁ bv ∷ ≢sym eg ∷ [])
       (zf ∷ of′ ∷ proj₁ (proj₂ av) ∷ proj₁ (proj₂ bv) ∷ ≢sym fg ∷ [])

  -- For the Hadamard-free branches, without 0: 1 x g and 1 a b g.
  module O3 (x : Fin N) (xo : x ≢ o) (av : Av x) =
    NV (o ∷ x ∷ g ∷ [])
       ((xo ∷ go ∷ []) ∷ᵈ (≢sym (proj₂ (proj₂ av)) ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
       (oe ∷ proj₁ av ∷ ≢sym eg ∷ []) (of′ ∷ proj₁ (proj₂ av) ∷ ≢sym fg ∷ [])

  module O4 (a b : Fin N) (ao : a ≢ o) (bo : b ≢ o) (ba : b ≢ a) (av : Av a) (bv : Av b) =
    NV (o ∷ a ∷ b ∷ g ∷ [])
       ((ao ∷ bo ∷ go ∷ []) ∷ᵈ (ba ∷ ≢sym (proj₂ (proj₂ av)) ∷ []) ∷ᵈ
        (≢sym (proj₂ (proj₂ bv)) ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
       (oe ∷ proj₁ av ∷ proj₁ bv ∷ ≢sym eg ∷ [])
       (of′ ∷ proj₁ (proj₂ av) ∷ proj₁ (proj₂ bv) ∷ ≢sym fg ∷ [])

  ----------------------------------------------------------------------
  -- The transport, branch by branch
  --
  -- Each branch reads the action by its lemma in `FrameAct` and then
  -- either decides the equation on a template (`by-norm`, `A5-tmpl`) or,
  -- when no index meets 0 or 1, says it in a line.

  private
    zz-sq-w : ∀ (u : W) → zzʷ o g • (zzʷ o g • u) ≈ u
    zz-sq-w u = trans (sym assoc) (trans (front u (TT⁻ ⟨M⟩)) left-unit)

    -- The sign pair on 1 and g passes a pair away from both.
    com : ∀ (a b : Fin N) → a ≢ b → Av a → Av b → a ≢ o → b ≢ o →
          zzʷ o g • hhʷ a b e f ≈ hhʷ a b e f • zzʷ o g
    com a b ab av bv ao bo =
      comm-zz e65 a b e f ab (proj₁ av) (proj₁ (proj₂ av)) (proj₁ bv) (proj₁ (proj₂ bv)) ef
              o g (≢sym ao) (≢sym bo) oe of′
              (≢sym (proj₂ (proj₂ av))) (≢sym (proj₂ (proj₂ bv))) (≢sym eg) (≢sym fg)

  -- At ⟨ε⟩.
  tr-ε-Z : ∀ (a : Fin N) → Goal ⟨ε⟩ −1[ a ]
  tr-ε-Z a = trans (zz-tri o a g) (sym left-unit)

  tr-ε-X : ∀ (a b : Fin N) → Av a → Av b →
           Dec (a ≡ b) → Dec (a ≡ o) → Dec (b ≡ o) → Goal ⟨ε⟩ X[ a , b ]
  tr-ε-X a .a av bv (yes Eq.refl) _ _ =
    via-act ⟨ε⟩ X[ a , a ] (aεX-deg a) (deg ⟨ε⟩ (zxʷ g a a) (zx-same g a))
  tr-ε-X .o b av bv (no ab) (yes Eq.refl) _ =
    via-act ⟨ε⟩ X[ o , b ] (aεX-o b ab)
      (trans (refl≡ (gen-zx b o b ab))
             (A5-tmpl ⌜ ty ₁ ₀ ₁ ⌝ (emp •ᵗ (⌜ ty ₂ ₀ ₁ ⌝ •ᵗ ⌜ tz ₀ ₂ ⌝)) Eq.refl))
    where open O3 b (≢sym ab) bv
  tr-ε-X a .o av bv (no ab) (no ao) (yes Eq.refl) =
    via-act ⟨ε⟩ X[ a , o ] (aεX-o′ a ao)
      (trans (refl≡ (gen-zx a a o ao))
             (A5-tmpl ⌜ ty ₁ ₁ ₀ ⌝ (emp •ᵗ (⌜ ty ₂ ₁ ₀ ⌝ •ᵗ ⌜ tz ₀ ₂ ⌝)) Eq.refl))
    where open O3 a ao av
  tr-ε-X a b av bv (no ab) (no ao) (no bo) =
    via-act ⟨ε⟩ X[ a , b ] (aεX-off a b ab ao bo)
      (trans (refl≡ (gen-zx o a b ab))
             (A5-tmpl ⌜ ty ₀ ₁ ₂ ⌝ (emp •ᵗ (⌜ ty ₃ ₁ ₂ ⌝ •ᵗ ⌜ tz ₀ ₃ ⌝)) Eq.refl))
    where open O4 a b ao bo (≢sym ab) av bv

  tr-ε-H : ∀ (a b : Fin N) → Dec (a ≡ b) → Goal ⟨ε⟩ H[ a , b ]
  tr-ε-H a .a (yes Eq.refl) =
    via-act ⟨ε⟩ H[ a , a ] (aεH-deg a) (deg ⟨ε⟩ (hhʷ a a e f) (hh-same a e f))
  tr-ε-H a b (no ab) =
    via-act ⟨ε⟩ H[ a , b ] (aεH a b ab)
      (trans (refl≡ (gen-hh a b z o ab z≢o))
             (sym (trans left-unit (fuse e65 a b e f z o ab ef z≢o))))

  -- At ⟨M⟩.
  tr-M-Z : ∀ (a : Fin N) → Goal ⟨M⟩ −1[ a ]
  tr-M-Z a = zz-tri′ o a g

  tr-M-X : ∀ (a b : Fin N) → Dec (a ≡ b) → Goal ⟨M⟩ X[ a , b ]
  tr-M-X a .a (yes Eq.refl) =
    via-act ⟨M⟩ X[ a , a ] (aMX-deg a) (deg ⟨M⟩ (zxʷ g a a) (zx-same g a))
  tr-M-X a b (no ab) =
    via-act ⟨M⟩ X[ a , b ] (aMX a b ab)
      (trans (refl≡ (gen-zx o a b ab)) (zx-split o g a b ab))

  tr-M-H : ∀ (a b : Fin N) → Av a → Av b →
           Dec (a ≡ b) → Dec (a ≡ o) → Dec (b ≡ o) → Dec (a ≡ z) → Dec (b ≡ z) →
           Goal ⟨M⟩ H[ a , b ]
  tr-M-H a .a av bv (yes Eq.refl) _ _ _ _ =
    via-act ⟨M⟩ H[ a , a ] (aMH-deg a) (deg ⟨M⟩ (hhʷ a a e f) (hh-same a e f))
  tr-M-H .o .z av bv (no ab) (yes Eq.refl) _ _ (yes Eq.refl) =
    via-act ⟨M⟩ H[ o , z ] (aMH-o z ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-zx z o z ab) (gen-hh o z z o ab z≢o)))
             (by-norm (⌞ hf (ty ₀ ₁ ₀) ⌟ •ᶠ ⌞ hp ₁ ₀ ₀ ₁ ⌟)
                      (⌞ hf (tz ₁ ₂) ⌟ •ᶠ (⌞ hl ₁ ₀ ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N3
  tr-M-H .o b av bv (no ab) (yes Eq.refl) _ _ (no bz) =
    via-act ⟨M⟩ H[ o , b ] (aMH-o b ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-zx b o b ab) (gen-hh o b z o ab z≢o)))
             (by-norm (⌞ hf (ty ₂ ₁ ₂) ⌟ •ᶠ ⌞ hp ₁ ₂ ₀ ₁ ⌟)
                      (⌞ hf (tz ₁ ₃) ⌟ •ᶠ (⌞ hl ₁ ₂ ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 b bz (≢sym ab) bv
  tr-M-H .z .o av bv (no ab) (no ao) (yes Eq.refl) (yes Eq.refl) _ =
    via-act ⟨M⟩ H[ z , o ] (aMH-o′ z ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-zx o z o ab) (gen-hh z o z o ab z≢o)))
             (by-norm (⌞ hf (ty ₁ ₀ ₁) ⌟ •ᶠ ⌞ hp ₀ ₁ ₀ ₁ ⌟)
                      (⌞ hf (tz ₁ ₂) ⌟ •ᶠ (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N3
  tr-M-H a .o av bv (no ab) (no ao) (yes Eq.refl) (no az) _ =
    via-act ⟨M⟩ H[ a , o ] (aMH-o′ a ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-zx o a o ab) (gen-hh a o z o ab z≢o)))
             (by-norm (⌞ hf (ty ₁ ₂ ₁) ⌟ •ᶠ ⌞ hp ₂ ₁ ₀ ₁ ⌟)
                      (⌞ hf (tz ₁ ₃) ⌟ •ᶠ (⌞ hl ₂ ₁ ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 a az ab av
  tr-M-H a b av bv (no ab) (no ao) (no bo) _ _ =
    via-act ⟨M⟩ H[ a , b ] (aMH-off a b ab ao bo)
      (trans (refl≡ (gen-hh a b z o ab z≢o)) (sym (begin
        zzʷ o g • (hhʷ a b e f • (zzʷ o g • hhʷ e f z o))
          ≈⟨ back (zzʷ o g) (sym assoc) ⟩
        zzʷ o g • ((hhʷ a b e f • zzʷ o g) • hhʷ e f z o)
          ≈⟨ back (zzʷ o g) (front (hhʷ e f z o) (sym (com a b ab av bv ao bo))) ⟩
        zzʷ o g • ((zzʷ o g • hhʷ a b e f) • hhʷ e f z o)
          ≈⟨ back (zzʷ o g) assoc ⟩
        zzʷ o g • (zzʷ o g • (hhʷ a b e f • hhʷ e f z o))
          ≈⟨ zz-sq-w (hhʷ a b e f • hhʷ e f z o) ⟩
        hhʷ a b e f • hhʷ e f z o
          ≈⟨ fuse e65 a b e f z o ab ef z≢o ⟩
        hhʷ a b z o ∎)))

  -- At ⟨K⟩.
  tr-K-Z : ∀ (a : Fin N) → Av a → Dec (a ≡ z) → Dec (a ≡ o) → Goal ⟨K⟩ −1[ a ]
  tr-K-Z .z av (yes Eq.refl) _ =
    via-act ⟨K⟩ −1[ z ] aKZ-z
      (by-norm ⌞ hf (tz ₁ ₀) ⌟
               (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (tz ₀ ₂) ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
               Eq.refl Eq.refl)
    where open N3
  tr-K-Z .o av (no az) (yes Eq.refl) =
    via-act ⟨K⟩ −1[ o ] aKZ-o
      (by-norm ⌞ hf (tz ₁ ₁) ⌟
               (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
               Eq.refl Eq.refl)
    where open N3
  tr-K-Z a av (no az) (no ao) =
    via-act ⟨K⟩ −1[ a ] (aKZ-off a az ao)
      (trans (refl≡ (gen-zx a z o z≢o))
             (by-norm ⌞ hf (ty ₂ ₀ ₁) ⌟
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (tz ₂ ₃) ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 a az ao av

  tr-K-X : ∀ (a b : Fin N) → Av a → Av b →
           Dec (a ≡ b) → Dec (a ≡ z) → Dec (b ≡ o) → Dec (b ≡ z) → Dec (a ≡ o) →
           Goal ⟨K⟩ X[ a , b ]
  tr-K-X a .a av bv (yes Eq.refl) _ _ _ _ =
    via-act ⟨K⟩ X[ a , a ] (aKX-deg a) (deg ⟨K⟩ (zxʷ g a a) (zx-same g a))
  tr-K-X .z .o av bv (no ab) (yes Eq.refl) (yes Eq.refl) _ _ =
    via-act ⟨K⟩ X[ z , o ] aKX-zo
      (trans (refl≡ (gen-zx o z o z≢o))
             (by-norm ⌞ hf (ty ₁ ₀ ₁) ⌟
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₂ ₀ ₁) ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N3
  tr-K-X .z b av bv (no ab) (yes Eq.refl) (no bo) _ _ =
    via-act ⟨K⟩ X[ z , b ] (aKX-zt b ab bo)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-xx z o z b z≢o ab) (gen-hh b o z o bo z≢o)))
             (by-norm (⌞ hf (tx ₀ ₁ ₀ ₂) ⌟ •ᶠ ⌞ hp ₂ ₁ ₀ ₁ ⌟)
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₃ ₀ ₂) ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 b (≢sym ab) bo bv
  tr-K-X .o .z av bv (no ab) (no az) _ (yes Eq.refl) (yes Eq.refl) =
    via-act ⟨K⟩ X[ o , z ] aKX-oz
      (trans (refl≡ (gen-zx o z o z≢o))
             (by-norm ⌞ hf (ty ₁ ₀ ₁) ⌟
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₂ ₁ ₀) ⌟ •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N3
  tr-K-X a .z av bv (no ab) (no az) _ (yes Eq.refl) (no ao) =
    via-act ⟨K⟩ X[ a , z ] (aKX-tz a az ao)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-xx z o a z z≢o ab) (gen-hh a o z o ao z≢o)))
             (by-norm (⌞ hf (tx ₀ ₁ ₂ ₀) ⌟ •ᶠ ⌞ hp ₂ ₁ ₀ ₁ ⌟)
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₃ ₂ ₀) ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 a az ao av
  tr-K-X .o b av bv (no ab) (no az) _ (no bz) (yes Eq.refl) =
    via-act ⟨K⟩ X[ o , b ] (aKX-ot b bz ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-zx b o b ab) (gen-hh z b z o (λ h → bz (Eq.sym h)) z≢o)))
             (by-norm (⌞ hf (ty ₂ ₁ ₂) ⌟ •ᶠ ⌞ hp ₀ ₂ ₀ ₁ ⌟)
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₃ ₁ ₂) ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 b bz (≢sym ab) bv
  tr-K-X a .o av bv (no ab) (no az) (yes Eq.refl) (no bz) (no ao) =
    via-act ⟨K⟩ X[ a , o ] (aKX-to a az ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-zx a a o ab) (gen-hh z a z o (λ h → az (Eq.sym h)) z≢o)))
             (by-norm (⌞ hf (ty ₂ ₂ ₁) ⌟ •ᶠ ⌞ hp ₀ ₂ ₀ ₁ ⌟)
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₃ ₂ ₁) ⌟ •ᶠ (⌞ hf (tz ₁ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N4 a az ab av
  tr-K-X a b av bv (no ab) (no az) (no bo) (no bz) (no ao) =
    via-act ⟨K⟩ X[ a , b ] (aKX-none a b ab az bz ao bo)
      (trans (refl≡ (gen-xx a b z o ab z≢o))
             (by-norm ⌞ hf (tx ₂ ₃ ₀ ₁) ⌟
                      (⌞ hl ₀ ₁ ⌟ •ᶠ (⌞ hf (ty ₄ ₂ ₃) ⌟ •ᶠ (⌞ hf (tz ₁ ₄) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟)))
                      Eq.refl Eq.refl))
    where open N5 a b az ao bz bo (≢sym ab) av bv

  tr-K-H : ∀ (a b : Fin N) → Av a → Av b → Dec (a ≡ b) → Goal ⟨K⟩ H[ a , b ]
  tr-K-H a .a av bv (yes Eq.refl) =
    via-act ⟨K⟩ H[ a , a ] (aKH-deg a) (deg ⟨K⟩ (hhʷ a a e f) (hh-same a e f))
  tr-K-H a b av bv (no ab) =
    via-act ⟨K⟩ H[ a , b ] (aKH a b ab)
      (trans (refl≡ (gen-hh z o a b z≢o ab)) (begin
        hhʷ z o a b                         ≈⟨ sym (fuse e65 z o e f a b z≢o ef ab) ⟩
        hhʷ z o e f • hhʷ e f a b           ≈⟨ back (hhʷ z o e f)
                                                  (sym (eq66 e65 a b e f ab (proj₁ av) (proj₁ (proj₂ av))
                                                                 (proj₁ bv) (proj₁ (proj₂ bv)) ef)) ⟩
        hhʷ z o e f • hhʷ a b e f           ≈⟨ back (hhʷ z o e f) (sym right-unit) ⟩
        hhʷ z o e f • (hhʷ a b e f • ε)     ∎))

  -- At ⟨KM⟩.
  tr-KM-Z : ∀ (a : Fin N) → Av a → Dec (a ≡ z) → Dec (a ≡ o) → Goal ⟨KM⟩ −1[ a ]
  tr-KM-Z .z av (yes Eq.refl) _ =
    via-act ⟨KM⟩ −1[ z ] aKMZ-z
      (by-norm ⌞ hf (tz ₁ ₀) ⌟
               ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) •ᶠ (⌞ hf (tz ₀ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
               Eq.refl Eq.refl)
    where open N3
  tr-KM-Z .o av (no az) (yes Eq.refl) =
    via-act ⟨KM⟩ −1[ o ] aKMZ-o
      (by-norm ⌞ hf (tz ₁ ₁) ⌟
               ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) •ᶠ (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
               Eq.refl Eq.refl)
    where open N3
  tr-KM-Z a av (no az) (no ao) =
    via-act ⟨KM⟩ −1[ a ] (aKMZ-off a az ao)
      (trans (refl≡ (gen-zx a z o z≢o))
             (by-norm ⌞ hf (ty ₂ ₀ ₁) ⌟
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hf (tz ₂ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N4 a az ao av

  tr-KM-X : ∀ (a b : Fin N) → Av a → Av b →
            Dec (a ≡ b) → Dec (a ≡ z) → Dec (b ≡ o) → Dec (b ≡ z) → Dec (a ≡ o) →
            Goal ⟨KM⟩ X[ a , b ]
  tr-KM-X a .a av bv (yes Eq.refl) _ _ _ _ =
    via-act ⟨KM⟩ X[ a , a ] (aKMX-deg a) (deg ⟨KM⟩ (zxʷ g a a) (zx-same g a))
  tr-KM-X .z .o av bv (no ab) (yes Eq.refl) (yes Eq.refl) _ _ =
    via-act ⟨KM⟩ X[ z , o ] aKMX-zo
      (trans (refl≡ (gen-zx z z o z≢o))
             (by-norm ⌞ hf (ty ₀ ₀ ₁) ⌟
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) •ᶠ (⌞ hf (ty ₂ ₀ ₁) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N3
  tr-KM-X .z b av bv (no ab) (yes Eq.refl) (no bo) _ _ =
    via-act ⟨KM⟩ X[ z , b ] (aKMX-zt b ab bo)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-xx z o z b z≢o ab) (gen-hh b o z o bo z≢o)))
             (by-norm (⌞ hf (tx ₀ ₁ ₀ ₂) ⌟ •ᶠ ⌞ hp ₂ ₁ ₀ ₁ ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hf (ty ₃ ₀ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N4 b (≢sym ab) bo bv
  tr-KM-X .o .z av bv (no ab) (no az) _ (yes Eq.refl) (yes Eq.refl) =
    via-act ⟨KM⟩ X[ o , z ] aKMX-oz
      (trans (refl≡ (gen-zx z z o z≢o))
             (by-norm ⌞ hf (ty ₀ ₀ ₁) ⌟
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) •ᶠ (⌞ hf (ty ₂ ₁ ₀) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N3
  tr-KM-X a .z av bv (no ab) (no az) _ (yes Eq.refl) (no ao) =
    via-act ⟨KM⟩ X[ a , z ] (aKMX-tz a az ao)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-xx z o a z z≢o ab) (gen-hh a o z o ao z≢o)))
             (by-norm (⌞ hf (tx ₀ ₁ ₂ ₀) ⌟ •ᶠ ⌞ hp ₂ ₁ ₀ ₁ ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hf (ty ₃ ₂ ₀) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N4 a az ao av
  tr-KM-X .o b av bv (no ab) (no az) _ (no bz) (yes Eq.refl) =
    via-act ⟨KM⟩ X[ o , b ] (aKMX-ot b bz ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-xx z o o b z≢o ab) (gen-hh z b z o (λ h → bz (Eq.sym h)) z≢o)))
             (by-norm (⌞ hf (tx ₀ ₁ ₁ ₂) ⌟ •ᶠ ⌞ hp ₀ ₂ ₀ ₁ ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hf (ty ₃ ₁ ₂) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N4 b bz (≢sym ab) bv
  tr-KM-X a .o av bv (no ab) (no az) (yes Eq.refl) (no bz) (no ao) =
    via-act ⟨KM⟩ X[ a , o ] (aKMX-to a az ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-xx z o a o z≢o ab) (gen-hh z a z o (λ h → az (Eq.sym h)) z≢o)))
             (by-norm (⌞ hf (tx ₀ ₁ ₂ ₁) ⌟ •ᶠ ⌞ hp ₀ ₂ ₀ ₁ ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hf (ty ₃ ₂ ₁) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N4 a az ab av
  tr-KM-X a b av bv (no ab) (no az) (no bo) (no bz) (no ao) =
    via-act ⟨KM⟩ X[ a , b ] (aKMX-none a b ab az bz ao bo)
      (trans (refl≡ (gen-xx a b z o ab z≢o))
             (by-norm ⌞ hf (tx ₂ ₃ ₀ ₁) ⌟
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₄) ⌟) •ᶠ (⌞ hf (ty ₄ ₂ ₃) ⌟ •ᶠ ⌞ hr ₀ ₁ ⌟))
                      Eq.refl Eq.refl))
    where open N5 a b az ao bz bo (≢sym ab) av bv

  tr-KM-H : ∀ (a b : Fin N) → Av a → Av b →
            Dec (a ≡ b) → Dec (a ≡ o) → Dec (b ≡ o) → Dec (a ≡ z) → Dec (b ≡ z) →
            Goal ⟨KM⟩ H[ a , b ]
  tr-KM-H a .a av bv (yes Eq.refl) _ _ _ _ =
    via-act ⟨KM⟩ H[ a , a ] (aKMH-deg a) (deg ⟨KM⟩ (hhʷ a a e f) (hh-same a e f))
  tr-KM-H .o .z av bv (no ab) (yes Eq.refl) _ _ (yes Eq.refl) =
    via-act ⟨KM⟩ H[ o , z ] (aKMH-o z ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-hh z o o z z≢o ab) (gen-zx o o z ab)))
             (by-norm (⌞ hp ₀ ₁ ₁ ₀ ⌟ •ᶠ ⌞ hf (ty ₁ ₁ ₀) ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) •ᶠ (⌞ hl ₁ ₀ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟))
                      Eq.refl Eq.refl))
    where open N3
  tr-KM-H .o b av bv (no ab) (yes Eq.refl) _ _ (no bz) =
    via-act ⟨KM⟩ H[ o , b ] (aKMH-o b ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-hh z o o b z≢o ab) (gen-zx o o b ab)))
             (by-norm (⌞ hp ₀ ₁ ₁ ₂ ⌟ •ᶠ ⌞ hf (ty ₁ ₁ ₂) ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hl ₁ ₂ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟))
                      Eq.refl Eq.refl))
    where open N4 b bz (≢sym ab) bv
  tr-KM-H .z .o av bv (no ab) (no ao) (yes Eq.refl) (yes Eq.refl) _ =
    via-act ⟨KM⟩ H[ z , o ] (aKMH-o′ z ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-hh z o z o z≢o ab) (gen-zx z z o ab)))
             (by-norm (⌞ hp ₀ ₁ ₀ ₁ ⌟ •ᶠ ⌞ hf (ty ₀ ₀ ₁) ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟) •ᶠ (⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₂) ⌟))
                      Eq.refl Eq.refl))
    where open N3
  tr-KM-H a .o av bv (no ab) (no ao) (yes Eq.refl) (no az) _ =
    via-act ⟨KM⟩ H[ a , o ] (aKMH-o′ a ab)
      (trans (refl≡ (Eq.cong₂ _•_ (gen-hh z o a o z≢o ab) (gen-zx a a o ab)))
             (by-norm (⌞ hp ₀ ₁ ₂ ₁ ⌟ •ᶠ ⌞ hf (ty ₂ ₂ ₁) ⌟)
                      ((⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟) •ᶠ (⌞ hl ₂ ₁ ⌟ •ᶠ ⌞ hf (tz ₁ ₃) ⌟))
                      Eq.refl Eq.refl))
    where open N4 a az ab av
  tr-KM-H a b av bv (no ab) (no ao) (no bo) _ _ =
    via-act ⟨KM⟩ H[ a , b ] (aKMH-off a b ab ao bo)
      (trans (refl≡ (gen-hh z o a b z≢o ab)) (sym (begin
        (hhʷ z o e f • zzʷ o g) • (hhʷ a b e f • zzʷ o g)
          ≈⟨ assoc ⟩
        hhʷ z o e f • (zzʷ o g • (hhʷ a b e f • zzʷ o g))
          ≈⟨ back (hhʷ z o e f) (back (zzʷ o g) (sym (com a b ab av bv ao bo))) ⟩
        hhʷ z o e f • (zzʷ o g • (zzʷ o g • hhʷ a b e f))
          ≈⟨ back (hhʷ z o e f) (zz-sq-w (hhʷ a b e f)) ⟩
        hhʷ z o e f • hhʷ a b e f
          ≈⟨ back (hhʷ z o e f) (eq66 e65 a b e f ab (proj₁ av) (proj₁ (proj₂ av))
                                     (proj₁ bv) (proj₁ (proj₂ bv)) ef) ⟩
        hhʷ z o e f • hhʷ e f a b
          ≈⟨ fuse e65 z o e f a b z≢o ef ab ⟩
        hhʷ z o a b ∎)))

  -- All of them.
  tr : ∀ (c : Coset) (y : G.Gen N) → Avoids y → Goal c y
  tr ⟨ε⟩  −1[ a ]    av        = tr-ε-Z a
  tr ⟨ε⟩  X[ a , b ] (av , bv) = tr-ε-X a b av bv (a ≟ b) (a ≟ o) (b ≟ o)
  tr ⟨ε⟩  H[ a , b ] (av , bv) = tr-ε-H a b (a ≟ b)
  tr ⟨M⟩  −1[ a ]    av        = tr-M-Z a
  tr ⟨M⟩  X[ a , b ] (av , bv) = tr-M-X a b (a ≟ b)
  tr ⟨M⟩  H[ a , b ] (av , bv) = tr-M-H a b av bv (a ≟ b) (a ≟ o) (b ≟ o) (a ≟ z) (b ≟ z)
  tr ⟨K⟩  −1[ a ]    av        = tr-K-Z a av (a ≟ z) (a ≟ o)
  tr ⟨K⟩  X[ a , b ] (av , bv) = tr-K-X a b av bv (a ≟ b) (a ≟ z) (b ≟ o) (b ≟ z) (a ≟ o)
  tr ⟨K⟩  H[ a , b ] (av , bv) = tr-K-H a b av bv (a ≟ b)
  tr ⟨KM⟩ −1[ a ]    av        = tr-KM-Z a av (a ≟ z) (a ≟ o)
  tr ⟨KM⟩ X[ a , b ] (av , bv) = tr-KM-X a b av bv (a ≟ b) (a ≟ z) (b ≟ o) (b ≟ z) (a ≟ o)
  tr ⟨KM⟩ H[ a , b ] (av , bv) = tr-KM-H a b av bv (a ≟ b) (a ≟ o) (b ≟ o) (a ≟ z) (b ≟ z)

  ----------------------------------------------------------------------
  -- Words

  Φʷ : Word (G.Gen N) → W
  Φʷ [ y ]ʷ   = Φ y
  Φʷ ε        = ε
  Φʷ (u • v)  = Φʷ u • Φʷ v

  AvoidsW : Word (G.Gen N) → Set
  AvoidsW [ y ]ʷ  = Avoids y
  AvoidsW ε       = ⊤
  AvoidsW (u • v) = AvoidsW u × AvoidsW v

  private
    T⁻T : ∀ (c : Coset) → T⁻ c • T c ≈ ε
    T⁻T ⟨ε⟩  = left-unit
    T⁻T ⟨M⟩  = TT⁻ ⟨M⟩
    T⁻T ⟨K⟩  = hh-cancel e65 e f z o ef ez eo fz fo z≢o
    T⁻T ⟨KM⟩ = begin
      (zzʷ o g • hhʷ e f z o) • (hhʷ z o e f • zzʷ o g)
        ≈⟨ assoc ⟩
      zzʷ o g • (hhʷ e f z o • (hhʷ z o e f • zzʷ o g))
        ≈⟨ back (zzʷ o g) (sym assoc) ⟩
      zzʷ o g • ((hhʷ e f z o • hhʷ z o e f) • zzʷ o g)
        ≈⟨ back (zzʷ o g) (front (zzʷ o g) (T⁻T ⟨K⟩)) ⟩
      zzʷ o g • (ε • zzʷ o g)
        ≈⟨ back (zzʷ o g) left-unit ⟩
      zzʷ o g • zzʷ o g
        ≈⟨ TT⁻ ⟨M⟩ ⟩
      ε ∎

  -- The traversal of a word is the conjugate of its embedding.
  run : ∀ (c : Coset) (u : Word (G.Gen N)) → AvoidsW u →
        proj₁ ((act ᵗ) c u) ≈ T c • (Φʷ u • T⁻ (proj₂ ((act ᵗ) c u)))
  run c [ y ]ʷ  av        = tr c y av
  run c ε       _         = sym (trans (back (T c) left-unit) (TT⁻ c))
  run c (u • v) (au , av) = begin
    proj₁ ((act ᵗ) c u) • proj₁ ((act ᵗ) c′ v)
      ≈⟨ cong (run c u au) (run c′ v av) ⟩
    (T c • (Φʷ u • T⁻ c′)) • (T c′ • (Φʷ v • T⁻ c″))
      ≈⟨ assoc ⟩
    T c • ((Φʷ u • T⁻ c′) • (T c′ • (Φʷ v • T⁻ c″)))
      ≈⟨ back (T c) assoc ⟩
    T c • (Φʷ u • (T⁻ c′ • (T c′ • (Φʷ v • T⁻ c″))))
      ≈⟨ back (T c) (back (Φʷ u) (sym assoc)) ⟩
    T c • (Φʷ u • ((T⁻ c′ • T c′) • (Φʷ v • T⁻ c″)))
      ≈⟨ back (T c) (back (Φʷ u) (front (Φʷ v • T⁻ c″) (T⁻T c′))) ⟩
    T c • (Φʷ u • (ε • (Φʷ v • T⁻ c″)))
      ≈⟨ back (T c) (back (Φʷ u) left-unit) ⟩
    T c • (Φʷ u • (Φʷ v • T⁻ c″))
      ≈⟨ back (T c) (sym assoc) ⟩
    T c • ((Φʷ u • Φʷ v) • T⁻ c″) ∎
    where
    c′ c″ : Coset
    c′ = proj₂ ((act ᵗ) c u)
    c″ = proj₂ ((act ᵗ) c′ v)

  ----------------------------------------------------------------------
  -- The cosets reached

  NonDeg : G.Gen N → Set
  NonDeg −1[ a ]    = ⊤
  NonDeg X[ a , b ] = a ≢ b
  NonDeg H[ a , b ] = a ≢ b

  NonDegW : Word (G.Gen N) → Set
  NonDegW [ y ]ʷ  = NonDeg y
  NonDegW ε       = ⊤
  NonDegW (u • v) = NonDegW u × NonDegW v

  private
    nxt-K-Z : ∀ (a : Fin N) → Dec (a ≡ z) → Dec (a ≡ o) → proj₂ (act ⟨K⟩ −1[ a ]) ≡ ⟨KM⟩
    nxt-K-Z .z (yes Eq.refl) _           = Eq.cong proj₂ aKZ-z
    nxt-K-Z .o (no az)       (yes Eq.refl) = Eq.cong proj₂ aKZ-o
    nxt-K-Z a  (no az)       (no ao)     = Eq.cong proj₂ (aKZ-off a az ao)

    nxt-KM-Z : ∀ (a : Fin N) → Dec (a ≡ z) → Dec (a ≡ o) → proj₂ (act ⟨KM⟩ −1[ a ]) ≡ ⟨K⟩
    nxt-KM-Z .z (yes Eq.refl) _           = Eq.cong proj₂ aKMZ-z
    nxt-KM-Z .o (no az)       (yes Eq.refl) = Eq.cong proj₂ aKMZ-o
    nxt-KM-Z a  (no az)       (no ao)     = Eq.cong proj₂ (aKMZ-off a az ao)

    nxt-ε-X : ∀ (a b : Fin N) → a ≢ b → Dec (a ≡ o) → Dec (b ≡ o) →
              proj₂ (act ⟨ε⟩ X[ a , b ]) ≡ ⟨M⟩
    nxt-ε-X .o b  ab (yes Eq.refl) _             = Eq.cong proj₂ (aεX-o b ab)
    nxt-ε-X a  .o ab (no ao)       (yes Eq.refl) = Eq.cong proj₂ (aεX-o′ a ao)
    nxt-ε-X a  b  ab (no ao)       (no bo)       = Eq.cong proj₂ (aεX-off a b ab ao bo)

    nxt-M-H : ∀ (a b : Fin N) → a ≢ b → Dec (a ≡ o) → Dec (b ≡ o) →
              proj₂ (act ⟨M⟩ H[ a , b ]) ≡ ⟨KM⟩
    nxt-M-H .o b  ab (yes Eq.refl) _             = Eq.cong proj₂ (aMH-o b ab)
    nxt-M-H a  .o ab (no ao)       (yes Eq.refl) = Eq.cong proj₂ (aMH-o′ a ao)
    nxt-M-H a  b  ab (no ao)       (no bo)       = Eq.cong proj₂ (aMH-off a b ab ao bo)

    nxt-KM-H : ∀ (a b : Fin N) → a ≢ b → Dec (a ≡ o) → Dec (b ≡ o) →
               proj₂ (act ⟨KM⟩ H[ a , b ]) ≡ ⟨M⟩
    nxt-KM-H .o b  ab (yes Eq.refl) _             = Eq.cong proj₂ (aKMH-o b ab)
    nxt-KM-H a  .o ab (no ao)       (yes Eq.refl) = Eq.cong proj₂ (aKMH-o′ a ao)
    nxt-KM-H a  b  ab (no ao)       (no bo)       = Eq.cong proj₂ (aKMH-off a b ab ao bo)

    nxt-K-X : ∀ (a b : Fin N) → a ≢ b →
              Dec (a ≡ z) → Dec (b ≡ o) → Dec (b ≡ z) → Dec (a ≡ o) →
              proj₂ (act ⟨K⟩ X[ a , b ]) ≡ ⟨KM⟩
    nxt-K-X .z .o ab (yes Eq.refl) (yes Eq.refl) _ _ = Eq.cong proj₂ aKX-zo
    nxt-K-X .z b  ab (yes Eq.refl) (no bo) _ _ = Eq.cong proj₂ (aKX-zt b ab bo)
    nxt-K-X .o .z ab (no az) _ (yes Eq.refl) (yes Eq.refl) = Eq.cong proj₂ aKX-oz
    nxt-K-X a  .z ab (no az) _ (yes Eq.refl) (no ao) = Eq.cong proj₂ (aKX-tz a az ao)
    nxt-K-X .o b  ab (no az) _ (no bz) (yes Eq.refl) = Eq.cong proj₂ (aKX-ot b bz ab)
    nxt-K-X a  .o ab (no az) (yes Eq.refl) (no bz) (no ao) = Eq.cong proj₂ (aKX-to a az ab)
    nxt-K-X a  b  ab (no az) (no bo) (no bz) (no ao) =
      Eq.cong proj₂ (aKX-none a b ab az bz ao bo)

    nxt-KM-X : ∀ (a b : Fin N) → a ≢ b →
               Dec (a ≡ z) → Dec (b ≡ o) → Dec (b ≡ z) → Dec (a ≡ o) →
               proj₂ (act ⟨KM⟩ X[ a , b ]) ≡ ⟨K⟩
    nxt-KM-X .z .o ab (yes Eq.refl) (yes Eq.refl) _ _ = Eq.cong proj₂ aKMX-zo
    nxt-KM-X .z b  ab (yes Eq.refl) (no bo) _ _ = Eq.cong proj₂ (aKMX-zt b ab bo)
    nxt-KM-X .o .z ab (no az) _ (yes Eq.refl) (yes Eq.refl) = Eq.cong proj₂ aKMX-oz
    nxt-KM-X a  .z ab (no az) _ (yes Eq.refl) (no ao) = Eq.cong proj₂ (aKMX-tz a az ao)
    nxt-KM-X .o b  ab (no az) _ (no bz) (yes Eq.refl) = Eq.cong proj₂ (aKMX-ot b bz ab)
    nxt-KM-X a  .o ab (no az) (yes Eq.refl) (no bz) (no ao) = Eq.cong proj₂ (aKMX-to a az ab)
    nxt-KM-X a  b  ab (no az) (no bo) (no bz) (no ao) =
      Eq.cong proj₂ (aKMX-none a b ab az bz ao bo)

  -- A non-degenerate generator moves the coset by its tag.
  nxt : ∀ (c : Coset) (y : G.Gen N) → NonDeg y → proj₂ (act c y) ≡ c ⊕ tag y
  nxt ⟨ε⟩  −1[ a ]    _  = Eq.refl
  nxt ⟨M⟩  −1[ a ]    _  = Eq.refl
  nxt ⟨K⟩  −1[ a ]    _  = nxt-K-Z a (a ≟ z) (a ≟ o)
  nxt ⟨KM⟩ −1[ a ]    _  = nxt-KM-Z a (a ≟ z) (a ≟ o)
  nxt ⟨ε⟩  X[ a , b ] ab = nxt-ε-X a b ab (a ≟ o) (b ≟ o)
  nxt ⟨M⟩  X[ a , b ] ab = Eq.cong proj₂ (aMX a b ab)
  nxt ⟨K⟩  X[ a , b ] ab = nxt-K-X a b ab (a ≟ z) (b ≟ o) (b ≟ z) (a ≟ o)
  nxt ⟨KM⟩ X[ a , b ] ab = nxt-KM-X a b ab (a ≟ z) (b ≟ o) (b ≟ z) (a ≟ o)
  nxt ⟨ε⟩  H[ a , b ] ab = Eq.cong proj₂ (aεH a b ab)
  nxt ⟨M⟩  H[ a , b ] ab = nxt-M-H a b ab (a ≟ o) (b ≟ o)
  nxt ⟨K⟩  H[ a , b ] ab = Eq.cong proj₂ (aKH a b ab)
  nxt ⟨KM⟩ H[ a , b ] ab = nxt-KM-H a b ab (a ≟ o) (b ≟ o)

  run-cos : ∀ (c : Coset) (u : Word (G.Gen N)) → NonDegW u → proj₂ ((act ᵗ) c u) ≡ cos c u
  run-cos c [ y ]ʷ  nd        = nxt c y nd
  run-cos c ε       _         = Eq.refl
  run-cos c (u • v) (nu , nv) =
    Eq.trans (run-cos (proj₂ ((act ᵗ) c u)) v nv) (Eq.cong (λ d → cos d v) (run-cos c u nu))

  ----------------------------------------------------------------------
  -- Item (b) for a rule is its image under Φ

  by-frame : ∀ (c : Coset) (u t : Word (G.Gen N)) →
             AvoidsW u → AvoidsW t → NonDegW u → NonDegW t →
             cos c u ≡ cos c t → Φʷ u ≈ Φʷ t →
             (proj₁ ((act ᵗ) c u) ≈ proj₁ ((act ᵗ) c t)) ×
             (proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t))
  by-frame c u t au at nu nt ec eΦ =
    trans (run c u au)
          (trans (back (T c) (cong eΦ (refl≡ (Eq.cong T⁻ ec′)))) (sym (run c t at))) ,
    ec′
    where
    ec′ : proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t)
    ec′ = Eq.trans (run-cos c u nu) (Eq.trans ec (Eq.sym (run-cos c t nt)))

  ----------------------------------------------------------------------
  -- Avoidance that depends on the coset
  --
  -- At ⟨ε⟩ and ⟨K⟩ a Hadamard is transported without the sink: only the
  -- frame pair must avoid it.  So a word whose Hadamards are all read at
  -- those two cosets — (d4*) from ⟨ε⟩ or ⟨K⟩, where the signs come in an
  -- adjacent pair — may have the sink among its own indices, which is
  -- what makes room for a frame on three qubits.

  AvH : Fin N → Set
  AvH a = (a ≢ e) × (a ≢ f)

  AvAt : Coset → G.Gen N → Set
  AvAt ⟨ε⟩  −1[ a ]    = Av a
  AvAt ⟨ε⟩  X[ a , b ] = Av a × Av b
  AvAt ⟨ε⟩  H[ a , b ] = AvH a × AvH b
  AvAt ⟨K⟩  −1[ a ]    = Av a
  AvAt ⟨K⟩  X[ a , b ] = Av a × Av b
  AvAt ⟨K⟩  H[ a , b ] = AvH a × AvH b
  AvAt ⟨M⟩  y          = Avoids y
  AvAt ⟨KM⟩ y          = Avoids y

  private
    tr-K-H′ : ∀ (a b : Fin N) → AvH a → AvH b → Dec (a ≡ b) → Goal ⟨K⟩ H[ a , b ]
    tr-K-H′ a .a av bv (yes Eq.refl) =
      via-act ⟨K⟩ H[ a , a ] (aKH-deg a) (deg ⟨K⟩ (hhʷ a a e f) (hh-same a e f))
    tr-K-H′ a b av bv (no ab) =
      via-act ⟨K⟩ H[ a , b ] (aKH a b ab)
        (trans (refl≡ (gen-hh z o a b z≢o ab)) (begin
          hhʷ z o a b                         ≈⟨ sym (fuse e65 z o e f a b z≢o ef ab) ⟩
          hhʷ z o e f • hhʷ e f a b           ≈⟨ back (hhʷ z o e f)
                                                    (sym (eq66 e65 a b e f ab (proj₁ av) (proj₂ av)
                                                                   (proj₁ bv) (proj₂ bv) ef)) ⟩
          hhʷ z o e f • hhʷ a b e f           ≈⟨ back (hhʷ z o e f) (sym right-unit) ⟩
          hhʷ z o e f • (hhʷ a b e f • ε)     ∎))

  trAt : ∀ (c : Coset) (y : G.Gen N) → AvAt c y → Goal c y
  trAt ⟨ε⟩  −1[ a ]    av        = tr ⟨ε⟩ −1[ a ] av
  trAt ⟨ε⟩  X[ a , b ] av        = tr ⟨ε⟩ X[ a , b ] av
  trAt ⟨ε⟩  H[ a , b ] _         = tr-ε-H a b (a ≟ b)
  trAt ⟨K⟩  −1[ a ]    av        = tr ⟨K⟩ −1[ a ] av
  trAt ⟨K⟩  X[ a , b ] av        = tr ⟨K⟩ X[ a , b ] av
  trAt ⟨K⟩  H[ a , b ] (av , bv) = tr-K-H′ a b av bv (a ≟ b)
  trAt ⟨M⟩  y          av        = tr ⟨M⟩ y av
  trAt ⟨KM⟩ y          av        = tr ⟨KM⟩ y av

  AvRun : Coset → Word (G.Gen N) → Set
  AvRun c [ y ]ʷ  = AvAt c y
  AvRun c ε       = ⊤
  AvRun c (u • v) = AvRun c u × AvRun (cos c u) v

  runAt : ∀ (c : Coset) (u : Word (G.Gen N)) → AvRun c u → NonDegW u →
          proj₁ ((act ᵗ) c u) ≈ T c • (Φʷ u • T⁻ (proj₂ ((act ᵗ) c u)))
  runAt c [ y ]ʷ  av        _         = trAt c y av
  runAt c ε       _         _         = sym (trans (back (T c) left-unit) (TT⁻ c))
  runAt c (u • v) (au , av) (nu , nv) = begin
    proj₁ ((act ᵗ) c u) • proj₁ ((act ᵗ) c′ v)
      ≈⟨ cong (runAt c u au nu) (runAt c′ v av′ nv) ⟩
    (T c • (Φʷ u • T⁻ c′)) • (T c′ • (Φʷ v • T⁻ c″))
      ≈⟨ assoc ⟩
    T c • ((Φʷ u • T⁻ c′) • (T c′ • (Φʷ v • T⁻ c″)))
      ≈⟨ back (T c) assoc ⟩
    T c • (Φʷ u • (T⁻ c′ • (T c′ • (Φʷ v • T⁻ c″))))
      ≈⟨ back (T c) (back (Φʷ u) (sym assoc)) ⟩
    T c • (Φʷ u • ((T⁻ c′ • T c′) • (Φʷ v • T⁻ c″)))
      ≈⟨ back (T c) (back (Φʷ u) (front (Φʷ v • T⁻ c″) (T⁻T c′))) ⟩
    T c • (Φʷ u • (ε • (Φʷ v • T⁻ c″)))
      ≈⟨ back (T c) (back (Φʷ u) left-unit) ⟩
    T c • (Φʷ u • (Φʷ v • T⁻ c″))
      ≈⟨ back (T c) (sym assoc) ⟩
    T c • ((Φʷ u • Φʷ v) • T⁻ c″) ∎
    where
    c′ c″ : Coset
    c′ = proj₂ ((act ᵗ) c u)
    c″ = proj₂ ((act ᵗ) c′ v)

    av′ : AvRun c′ v
    av′ = Eq.subst (λ d → AvRun d v) (Eq.sym (run-cos c u nu)) av

  by-frameAt : ∀ (c : Coset) (u t : Word (G.Gen N)) →
               AvRun c u → AvRun c t → NonDegW u → NonDegW t →
               cos c u ≡ cos c t → Φʷ u ≈ Φʷ t →
               (proj₁ ((act ᵗ) c u) ≈ proj₁ ((act ᵗ) c t)) ×
               (proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t))
  by-frameAt c u t au at nu nt ec eΦ =
    trans (runAt c u au nu)
          (trans (back (T c) (cong eΦ (refl≡ (Eq.cong T⁻ ec′)))) (sym (runAt c t at nt))) ,
    ec′
    where
    ec′ : proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t)
    ec′ = Eq.trans (run-cos c u nu) (Eq.trans ec (Eq.sym (run-cos c t nt)))
