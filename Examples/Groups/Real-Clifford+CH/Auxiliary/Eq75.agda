------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 10's (75), from Equation (40)
--
--     ((−1)_[a] X_[a,b]) (H_[a,b] H_[c,d])
--        ≈  (H_[a,b] H_[c,d]) ((−1)_[b] X_[a,b])        {a,b} ∩ {c,d} = ∅
--
-- The mixed letter here exchanges the pair's own first two indices, so
-- no *passing* rule moves it: conjugated by Definition E.1's word it
-- becomes the letter (−1)_[0] X_[0,1] on the standard pair, and what
-- is needed is that Λ = H_[0,1] H_[3,2] conjugates that letter to its
-- inverse.  None of (38), (39), (44) says so, (38) starting at 4.
--
-- Equation (40) does, one pair over.  It moves a sign pair on 3 and 4
-- across Λ at the cost of the letter (−1)_[2] X_[2,3] — which says
-- that Λ conjugates a sign on 3 to an exchange of 3 and 2.  The double
-- exchange X_[0,3] X_[1,2] passes Λ by (44), so conjugating (40) by it
-- carries all of that to the first pair: a sign pair on 0 and 4 crosses
-- Λ at the cost of (−1)_[1] X_[1,0].  From there it is algebra — Λ
-- conjugates that letter to (−1)_[0] X_[0,1], and Λ-conjugation is an
-- involution — and the Hadamard-free identifications on the way are
-- Corollary A.5.  `scratchpad/t75.py` checked every step numerically
-- first.
--
-- (75) at any tuple is then that instance transported by Definition
-- E.1's word, which carries a, b to 0, 1 without signing either.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq75 (m : ℕ) where

open import Data.Bool using (Bool ; false ; true ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-inject≤ ; _≟_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₄ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
  using (_P,_===_ ; r40 ; r41 ; r44)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (hh ; zz ; zx ; zzℕ ; zxℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz ; zxℕ-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; cat ; nil ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; idSP ; NEG ; SWP ; L ; Inj ; sp-inj ; sp-zx
       ; δ ; δ-here ; δ-≢ ; xor-comm ; xor-self ; eqv
       ; swapF ; swapF-a ; swapF-b ; swapF-o
       ; SWP-NEG ; SWP-sym ; NEG-invol ; hop ; drop)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-sym to ≐-sym′
          ; ≐-trans to ≐-trans′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; prm≡ to prm≡′ ; sgn≡ to sgn≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m using (hfree-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃
       ; i₀≢i₁ ; i₀≢i₂ ; i₀≢i₃ ; i₁≢i₂ ; i₁≢i₃ ; i₂≢i₃
       ; Xw ; sp-Xw ; hfree-X ; Xw-sp-invol ; Xw-invol ; xx0312≡)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65 using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP (₃₊ m))

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  neg≡ : ∀ {x y : Fin N} → x ≡ y → NEG x ≗ NEG y
  neg≡ Eq.refl = ≐-refl′

------------------------------------------------------------------------
-- Carrying a sign and a letter across a signed permutation

-- A sign test is carried along an injective permutation.
δ-by : ∀ (f : SP) → Inj f → ∀ (c i : Fin N) → δ c i ≡ δ (prm f c) (prm f i)
δ-by f inj c i = go (i ≟ c)
  where
  go : Dec (i ≡ c) → δ c i ≡ δ (prm f c) (prm f i)
  go (yes e) =
    Eq.subst (λ z → δ c z ≡ δ (prm f c) (prm f z)) (Eq.sym e)
             (Eq.trans (δ-here c) (Eq.sym (δ-here (prm f c))))
  go (no ne) =
    Eq.trans (δ-≢ c i ne) (Eq.sym (δ-≢ (prm f c) (prm f i) (λ e → ne (inj e))))

-- A sign crosses any signed permutation, landing on its image.
NEG-by : ∀ (f : SP) → Inj f → ∀ (c : Fin N) → NEG c ⊛ f ≗ f ⊛ NEG (prm f c)
NEG-by f inj c = eqv sg (λ _ → Eq.refl)
  where
  sg : ∀ (i : Fin N) → sgn (NEG c ⊛ f) i ≡ sgn (f ⊛ NEG (prm f c)) i
  sg i = Eq.trans (xor-comm (δ c i) (sgn f i))
                  (Eq.cong (sgn f i xor_) (δ-by f inj c i))

-- An exchange is carried along an injective permutation.
swap-by : ∀ (f : SP) → Inj f → ∀ (x y i : Fin N) →
          prm f (swapF x y i) ≡ swapF (prm f x) (prm f y) (prm f i)
swap-by f inj x y i = go (i ≟ x) (i ≟ y)
  where
  Goal : Fin N → Set
  Goal z = prm f (swapF x y z) ≡ swapF (prm f x) (prm f y) (prm f z)

  go : Dec (i ≡ x) → Dec (i ≡ y) → Goal i
  go (yes e) _ =
    Eq.subst Goal (Eq.sym e)
      (Eq.trans (Eq.cong (prm f) (swapF-a x y))
                (Eq.sym (swapF-a (prm f x) (prm f y))))
  go (no _) (yes e) =
    Eq.subst Goal (Eq.sym e)
      (Eq.trans (Eq.cong (prm f) (swapF-b x y))
                (Eq.sym (swapF-b (prm f x) (prm f y))))
  go (no nx) (no ny) =
    Eq.trans (Eq.cong (prm f) (swapF-o x y i nx ny))
             (Eq.sym (swapF-o (prm f x) (prm f y) (prm f i)
                              (λ e → nx (inj e)) (λ e → ny (inj e))))

-- So a letter crosses a signed permutation that signs its two
-- exchanged indices alike, landing on the images of all three.
L-by : ∀ (f : SP) → Inj f → ∀ (c x y : Fin N) → sgn f x ≡ sgn f y →
       L c x y ⊛ f ≗ f ⊛ L (prm f c) (prm f x) (prm f y)
L-by f inj c x y sxy = eqv sg (swap-by f inj x y)
  where
  -- The exchange does not disturb f's signs.
  sf : ∀ (i : Fin N) → sgn f (swapF x y i) ≡ sgn f i
  sf i = go (i ≟ x) (i ≟ y)
    where
    Goal : Fin N → Set
    Goal z = sgn f (swapF x y z) ≡ sgn f z

    go : Dec (i ≡ x) → Dec (i ≡ y) → Goal i
    go (yes e) _ =
      Eq.subst Goal (Eq.sym e) (Eq.trans (Eq.cong (sgn f) (swapF-a x y)) (Eq.sym sxy))
    go (no _) (yes e) =
      Eq.subst Goal (Eq.sym e) (Eq.trans (Eq.cong (sgn f) (swapF-b x y)) sxy)
    go (no nx) (no ny) = Eq.cong (sgn f) (swapF-o x y i nx ny)

  sg : ∀ (i : Fin N) →
       sgn (L c x y ⊛ f) i ≡ sgn (f ⊛ L (prm f c) (prm f x) (prm f y)) i
  sg i = Eq.trans (Eq.cong₂ (λ u v → (u xor false) xor v) (δ-by f inj c i) (sf i))
                  (xor-comm (δ (prm f c) (prm f i) xor false) (sgn f i))

-- Conjugating by an involution.
NEG2-conj : ∀ (f : SP) → Inj f → f ⊛ f ≗ idSP → ∀ (u v : Fin N) →
            f ⊛ ((NEG u ⊛ NEG v) ⊛ f) ≗ NEG (prm f u) ⊛ NEG (prm f v)
NEG2-conj f inj ff u v =
  ≐-trans′ (⊙-cong′ (≐-refl′ {f})
             (≐-trans′ (⊙-assoc′ (NEG u) (NEG v) f)
             (≐-trans′ (⊙-cong′ (≐-refl′ {NEG u}) (NEG-by f inj v))
             (≐-trans′ (≐-sym′ (⊙-assoc′ (NEG u) f (NEG (prm f v))))
             (≐-trans′ (⊙-cong′ (NEG-by f inj u) (≐-refl′ {NEG (prm f v)}))
                       (⊙-assoc′ f (NEG (prm f u)) (NEG (prm f v))))))))
           (drop f f (NEG (prm f u) ⊛ NEG (prm f v)) ff)

L-conj : ∀ (f : SP) → Inj f → f ⊛ f ≗ idSP → ∀ (c x y : Fin N) →
         sgn f x ≡ sgn f y →
         f ⊛ (L c x y ⊛ f) ≗ L (prm f c) (prm f x) (prm f y)
L-conj f inj ff c x y sxy =
  ≐-trans′ (⊙-cong′ (≐-refl′ {f}) (L-by f inj c x y sxy))
           (drop f f (L (prm f c) (prm f x) (prm f y)) ff)

------------------------------------------------------------------------
-- The numerals, and the rules at them

private
  f₄ : Fin N
  f₄ = fin8 {m} ₄

  toℕ-f₄ : toℕ f₄ ≡ 4
  toℕ-f₄ = toℕ-inject≤ ₄ _

  dif : ∀ {x y : Fin N} {u v : ℕ} → toℕ x ≡ u → toℕ y ≡ v → u ≢ v → x ≢ y
  dif ex ey ne q = ne (Eq.trans (Eq.sym ex) (Eq.trans (Eq.cong toℕ q) ey))

  i₀≢f₄ : i₀ ≢ f₄
  i₀≢f₄ = dif toℕ-i₀ toℕ-f₄ (λ ())

  i₁≢f₄ : i₁ ≢ f₄
  i₁≢f₄ = dif toℕ-i₁ toℕ-f₄ (λ ())

  i₂≢f₄ : i₂ ≢ f₄
  i₂≢f₄ = dif toℕ-i₂ toℕ-f₄ (λ ())

  i₃≢f₄ : i₃ ≢ f₄
  i₃≢f₄ = dif toℕ-i₃ toℕ-f₄ (λ ())

  -- The words in play.
  Z34 Z04 Y223 Y110 Y001 Y101 : W
  Z34  = zz {₃₊ m} i₃ f₄
  Z04  = zz {₃₊ m} i₀ f₄
  Y223 = zx {₃₊ m} i₂ i₂ i₃
  Y110 = zx {₃₊ m} i₁ i₁ i₀
  Y001 = zx {₃₊ m} i₀ i₀ i₁
  Y101 = zx {₃₊ m} i₁ i₀ i₁

  hZ34 : HFreeʷ Z34
  hZ34 = gen (hf-zz i₃ f₄)

  hZ04 : HFreeʷ Z04
  hZ04 = gen (hf-zz i₀ f₄)

  -- Equations (40), (41) and (44) at those words.
  zz34≡ : zzℕ {₃₊ m} 3 4 ≡ Z34
  zz34≡ = Eq.trans (Eq.cong₂ (zzℕ {₃₊ m}) (Eq.sym toℕ-i₃) (Eq.sym toℕ-f₄))
                   (zzℕ-zz i₃ f₄)

  zx223≡ : zxℕ {₃₊ m} 2 2 3 ≡ Y223
  zx223≡ = Eq.trans (Eq.cong₂ (λ u v → zxℕ {₃₊ m} u u v)
                              (Eq.sym toℕ-i₂) (Eq.sym toℕ-i₃))
                    (zxℕ-zx i₂ i₂ i₃)

  e40 : Z34 • Λ ≈ Λ • (Z34 • Y223)
  e40 = Eq.subst₂ (λ z y → z • Λ ≈ Λ • (z • y)) zz34≡ zx223≡ (axiom r40)

  e44 : Xw • Λ ≈ Λ • Xw
  e44 = Eq.subst (λ x → x • Λ ≈ Λ • x) xx0312≡ (axiom r44)

  LL : Λ • Λ ≈ ε
  LL = axiom r41

  -- Where the double exchange sends the numerals it meets.
  xw : ∀ (t : Fin N) → prm (sp Xw) t ≡ swapF i₁ i₂ (swapF i₀ i₃ t)
  xw = prm≡′ sp-Xw

  xw-3 : prm (sp Xw) i₃ ≡ i₀
  xw-3 = Eq.trans (xw i₃)
           (Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-b i₀ i₃))
                     (swapF-o i₁ i₂ i₀ i₀≢i₁ i₀≢i₂))

  xw-2 : prm (sp Xw) i₂ ≡ i₁
  xw-2 = Eq.trans (xw i₂)
           (Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-o i₀ i₃ i₂ (≢sym i₀≢i₂) i₂≢i₃))
                     (swapF-b i₁ i₂))

  xw-4 : prm (sp Xw) f₄ ≡ f₄
  xw-4 = Eq.trans (xw f₄)
           (Eq.trans (Eq.cong (swapF i₁ i₂)
                              (swapF-o i₀ i₃ f₄ (≢sym i₀≢f₄) (≢sym i₃≢f₄)))
                     (swapF-o i₁ i₂ f₄ (≢sym i₁≢f₄) (≢sym i₂≢f₄)))

  xw-sgn : ∀ (t : Fin N) → sgn (sp Xw) t ≡ false
  xw-sgn = sgn≡′ sp-Xw

  ------------------------------------------------------------------
  -- The Hadamard-free identifications (Corollary A.5)

  -- The double exchange carries the sign pair on 3, 4 to 0, 4 …
  conjZ : Xw • (Z34 • Xw) ≈ Z04
  conjZ = A5-full (cat hfree-X (cat hZ34 hfree-X)) hZ04
            (≐-trans′ (NEG2-conj (sp Xw) (sp-inj Xw) Xw-sp-invol i₃ f₄)
                      (⊙-cong′ (neg≡ xw-3) (neg≡ xw-4)))

  -- … and the letter (−1)_[2] X_[2,3] to (−1)_[1] X_[1,0].
  conjY : Xw • (Y223 • Xw) ≈ Y110
  conjY = A5-full (cat hfree-X (cat (hfree-zx i₂ i₂ i₃) hfree-X)) (hfree-zx i₁ i₁ i₀)
            (≐-trans′ (⊙-cong′ (≐-refl′ {sp Xw})
                                (⊙-cong′ (sp-zx i₂ i₂ i₃ i₂≢i₃) (≐-refl′ {sp Xw})))
            (≐-trans′ (L-conj (sp Xw) (sp-inj Xw) Xw-sp-invol i₂ i₂ i₃
                              (Eq.trans (xw-sgn i₂) (Eq.sym (xw-sgn i₃))))
            (≐-trans′ (Eq.subst₂ (λ u v → L (prm (sp Xw) i₂) (prm (sp Xw) i₂)
                                             (prm (sp Xw) i₃) ≗ L u u v)
                                 xw-2 xw-3 ≐-refl′)
                      (≐-sym′ (sp-zx i₁ i₁ i₀ (≢sym i₀≢i₁))))))

  -- The sign pair on 0, 4 moves the letter's sign from 1 to 0.
  conjC : Z04 • (Y110 • Z04) ≈ Y001
  conjC = A5-full (cat hZ04 (cat (hfree-zx i₁ i₁ i₀) hZ04)) (hfree-zx i₀ i₀ i₁)
            (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₀ ⊛ NEG f₄})
                                (⊙-cong′ (sp-zx i₁ i₁ i₀ (≢sym i₀≢i₁))
                                         (≐-refl′ {NEG i₀ ⊛ NEG f₄})))
            (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₀ ⊛ NEG f₄}) inner)
            (≐-trans′ outer (≐-sym′ (sp-zx i₀ i₀ i₁ i₀≢i₁)))))
    where
    -- The exchange carries the sign on 0 over to 1, where it meets
    -- the letter's own and cancels it.
    through : SWP i₁ i₀ ⊛ (NEG i₀ ⊛ NEG f₄) ≗ NEG i₁ ⊛ (NEG f₄ ⊛ SWP i₁ i₀)
    through =
      ≐-trans′ (hop (SWP i₁ i₀) (NEG i₀) (SWP i₁ i₀) (NEG (swapF i₁ i₀ i₀))
                    (NEG f₄) (SWP-NEG i₁ i₀ i₀))
               (⊙-cong′ (neg≡ (swapF-b i₁ i₀))
                 (≐-trans′ (SWP-NEG i₁ i₀ f₄)
                           (⊙-cong′ (neg≡ (swapF-o i₁ i₀ f₄ (≢sym i₁≢f₄) (≢sym i₀≢f₄)))
                                    (≐-refl′ {SWP i₁ i₀}))))

    inner : (NEG i₁ ⊛ SWP i₁ i₀) ⊛ (NEG i₀ ⊛ NEG f₄) ≗ NEG f₄ ⊛ SWP i₁ i₀
    inner =
      ≐-trans′ (⊙-assoc′ (NEG i₁) (SWP i₁ i₀) (NEG i₀ ⊛ NEG f₄))
      (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₁}) through)
                (drop (NEG i₁) (NEG i₁) (NEG f₄ ⊛ SWP i₁ i₀) (NEG-invol i₁)))

    outer : (NEG i₀ ⊛ NEG f₄) ⊛ (NEG f₄ ⊛ SWP i₁ i₀) ≗ NEG i₀ ⊛ SWP i₀ i₁
    outer =
      ≐-trans′ (⊙-assoc′ (NEG i₀) (NEG f₄) (NEG f₄ ⊛ SWP i₁ i₀))
               (⊙-cong′ (≐-refl′ {NEG i₀})
                 (≐-trans′ (drop (NEG f₄) (NEG f₄) (SWP i₁ i₀) (NEG-invol f₄))
                           (SWP-sym i₁ i₀)))

  -- The letter is the same whichever way its exchange is written.
  Y110≈Y101 : Y110 ≈ Y101
  Y110≈Y101 = A5-full (hfree-zx i₁ i₁ i₀) (hfree-zx i₁ i₀ i₁)
                (≐-trans′ (sp-zx i₁ i₁ i₀ (≢sym i₀≢i₁))
                (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₁}) (SWP-sym i₁ i₀))
                          (≐-sym′ (sp-zx i₁ i₀ i₁ i₀≢i₁))))

  -- A sign pair is its own inverse.
  Z04-invol : Z04 • Z04 ≈ ε
  Z04-invol = A5-full (cat hZ04 hZ04) nil
                (eqv (λ i → xor-self (δ i₀ i xor δ f₄ i)) (λ _ → Eq.refl))

  ------------------------------------------------------------------
  -- Word algebra around Λ, over abstract words

  -- Multiplying a passing equation on the left by Λ, and back.
  sandwich : ∀ {u w : W} → u • Λ ≈ Λ • w → Λ • (u • Λ) ≈ w
  sandwich {u} {w} e = begin
    Λ • (u • Λ)   ≈⟨ back Λ e ⟩
    Λ • (Λ • w)   ≈⟨ sym assoc ⟩
    (Λ • Λ) • w   ≈⟨ front w LL ⟩
    ε • w         ≈⟨ left-unit ⟩
    w             ∎

  unsandwich : ∀ {u w : W} → Λ • (u • Λ) ≈ w → u • Λ ≈ Λ • w
  unsandwich {u} {w} e = begin
    u • Λ               ≈⟨ sym left-unit ⟩
    ε • (u • Λ)         ≈⟨ front (u • Λ) (sym LL) ⟩
    (Λ • Λ) • (u • Λ)   ≈⟨ assoc ⟩
    Λ • (Λ • (u • Λ))   ≈⟨ back Λ e ⟩
    Λ • w               ∎

  -- Conjugating a passing equation by a word that passes Λ.
  conj-pass : ∀ {x u v : W} → x • Λ ≈ Λ • x → u • Λ ≈ Λ • v →
              (x • (u • x)) • Λ ≈ Λ • (x • (v • x))
  conj-pass {x} {u} {v} xΛ e = begin
    (x • (u • x)) • Λ   ≈⟨ assoc ⟩
    x • ((u • x) • Λ)   ≈⟨ back x assoc ⟩
    x • (u • (x • Λ))   ≈⟨ back x (back u xΛ) ⟩
    x • (u • (Λ • x))   ≈⟨ back x (sym assoc) ⟩
    x • ((u • Λ) • x)   ≈⟨ back x (front x e) ⟩
    x • ((Λ • v) • x)   ≈⟨ back x assoc ⟩
    x • (Λ • (v • x))   ≈⟨ sym assoc ⟩
    (x • Λ) • (v • x)   ≈⟨ front (v • x) xΛ ⟩
    (Λ • x) • (v • x)   ≈⟨ assoc ⟩
    Λ • (x • (v • x))   ∎

  -- The conjugate of a product by an involution is the product of the
  -- conjugates.
  split-conj : ∀ {x p q : W} → x • x ≈ ε →
               x • ((p • q) • x) ≈ (x • (p • x)) • (x • (q • x))
  split-conj {x} {p} {q} xx = begin
    x • ((p • q) • x)               ≈⟨ back x assoc ⟩
    x • (p • (q • x))               ≈⟨ back x (back p (sym left-unit)) ⟩
    x • (p • (ε • (q • x)))         ≈⟨ back x (back p (front (q • x) (sym xx))) ⟩
    x • (p • ((x • x) • (q • x)))   ≈⟨ back x (back p assoc) ⟩
    x • (p • (x • (x • (q • x))))   ≈⟨ back x (sym assoc) ⟩
    x • ((p • x) • (x • (q • x)))   ≈⟨ sym assoc ⟩
    (x • (p • x)) • (x • (q • x))   ∎

  -- Two Λ's meeting in the middle cancel.
  cancel-tail : ∀ {p q : W} → Λ • ((p • (Λ • (q • Λ))) • Λ) ≈ (Λ • (p • Λ)) • q
  cancel-tail {p} {q} = begin
    Λ • ((p • (Λ • (q • Λ))) • Λ)   ≈⟨ back Λ assoc ⟩
    Λ • (p • ((Λ • (q • Λ)) • Λ))   ≈⟨ back Λ (back p assoc) ⟩
    Λ • (p • (Λ • ((q • Λ) • Λ)))   ≈⟨ back Λ (back p (back Λ assoc)) ⟩
    Λ • (p • (Λ • (q • (Λ • Λ))))   ≈⟨ back Λ (back p (back Λ (back q LL))) ⟩
    Λ • (p • (Λ • (q • ε)))         ≈⟨ back Λ (back p (back Λ right-unit)) ⟩
    Λ • (p • (Λ • q))               ≈⟨ back Λ (sym assoc) ⟩
    Λ • ((p • Λ) • q)               ≈⟨ sym assoc ⟩
    (Λ • (p • Λ)) • q               ∎

  -- Λ-conjugation is an involution.
  twice : ∀ {u : W} → Λ • ((Λ • (u • Λ)) • Λ) ≈ u
  twice {u} = begin
    Λ • ((Λ • (u • Λ)) • Λ)   ≈⟨ back Λ assoc ⟩
    Λ • (Λ • ((u • Λ) • Λ))   ≈⟨ sym assoc ⟩
    (Λ • Λ) • ((u • Λ) • Λ)   ≈⟨ front ((u • Λ) • Λ) LL ⟩
    ε • ((u • Λ) • Λ)         ≈⟨ left-unit ⟩
    (u • Λ) • Λ               ≈⟨ assoc ⟩
    u • (Λ • Λ)               ≈⟨ back u LL ⟩
    u • ε                     ≈⟨ right-unit ⟩
    u                         ∎

------------------------------------------------------------------------
-- (75) at the standard pair

-- Equation (40), carried to the first pair by the double exchange: a
-- sign pair on 0 and 4 crosses Λ at the cost of (−1)_[1] X_[1,0].
eq40′ : Z04 • Λ ≈ Λ • (Z04 • Y110)
eq40′ = begin
  Z04 • Λ                                        ≈⟨ front Λ (sym conjZ) ⟩
  (Xw • (Z34 • Xw)) • Λ                          ≈⟨ conj-pass e44 e40 ⟩
  Λ • (Xw • ((Z34 • Y223) • Xw))                 ≈⟨ back Λ (split-conj Xw-invol) ⟩
  Λ • ((Xw • (Z34 • Xw)) • (Xw • (Y223 • Xw)))   ≈⟨ back Λ (cong conjZ conjY) ⟩
  Λ • (Z04 • Y110)                               ∎

private
  S1 : Λ • (Z04 • Λ) ≈ Z04 • Y110
  S1 = sandwich eq40′

  -- So the letter is a Λ-conjugate of the sign pair, up to the pair.
  Y110-as : Y110 ≈ Z04 • (Λ • (Z04 • Λ))
  Y110-as = begin
    Y110                    ≈⟨ sym left-unit ⟩
    ε • Y110                ≈⟨ front Y110 (sym Z04-invol) ⟩
    (Z04 • Z04) • Y110      ≈⟨ assoc ⟩
    Z04 • (Z04 • Y110)      ≈⟨ back Z04 (sym S1) ⟩
    Z04 • (Λ • (Z04 • Λ))   ∎

  -- And Λ conjugates it to (−1)_[0] X_[0,1].
  ΛY110Λ : Λ • (Y110 • Λ) ≈ Y001
  ΛY110Λ = begin
    Λ • (Y110 • Λ)                      ≈⟨ back Λ (front Λ Y110-as) ⟩
    Λ • ((Z04 • (Λ • (Z04 • Λ))) • Λ)   ≈⟨ cancel-tail ⟩
    (Λ • (Z04 • Λ)) • Z04               ≈⟨ front Z04 S1 ⟩
    (Z04 • Y110) • Z04                  ≈⟨ assoc ⟩
    Z04 • (Y110 • Z04)                  ≈⟨ conjC ⟩
    Y001                                ∎

  ΛY001Λ : Λ • (Y001 • Λ) ≈ Y101
  ΛY001Λ = begin
    Λ • (Y001 • Λ)                ≈⟨ back Λ (front Λ (sym ΛY110Λ)) ⟩
    Λ • ((Λ • (Y110 • Λ)) • Λ)    ≈⟨ twice ⟩
    Y110                          ≈⟨ Y110≈Y101 ⟩
    Y101                          ∎

-- (75) at the standard pair: the letter (−1)_[0] X_[0,1] crosses
-- H_[0,1] H_[3,2] and comes out as (−1)_[1] X_[0,1].
eq75₀ : zx {₃₊ m} i₀ i₀ i₁ • Λ ≈ Λ • zx {₃₊ m} i₁ i₀ i₁
eq75₀ = unsandwich ΛY001Λ

------------------------------------------------------------------------
-- (75) at any tuple
--
-- Definition E.1's word carries a and b to 0 and 1 without signing
-- either, so the letter crosses it and becomes the standard one; the
-- standard (75) moves it across Λ; and the result crosses back.  The
-- two crossings are Corollary A.5, through `L-by`.

module _ (e65 : Eq65) where

  eq75 : ∀ (a b c d : Fin N) →
         a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
         zx {₃₊ m} a a b • hh {₃₊ m} a b c d
         ≈ hh {₃₊ m} a b c d • zx {₃₊ m} b a b
  eq75 a b c d ab ac ad bc bd cd = begin
    zx {₃₊ m} a a b • hh {₃₊ m} a b c d
      ≈⟨ back (zx {₃₊ m} a a b) split ⟩
    zx {₃₊ m} a a b • (T • (Λ • T′))
      ≈⟨ sym assoc ⟩
    (zx {₃₊ m} a a b • T) • (Λ • T′)
      ≈⟨ front (Λ • T′) inL ⟩
    (T • Y001) • (Λ • T′)
      ≈⟨ assoc ⟩
    T • (Y001 • (Λ • T′))
      ≈⟨ back T (sym assoc) ⟩
    T • ((Y001 • Λ) • T′)
      ≈⟨ back T (front T′ eq75₀) ⟩
    T • ((Λ • Y101) • T′)
      ≈⟨ back T assoc ⟩
    T • (Λ • (Y101 • T′))
      ≈⟨ back T (back Λ inR) ⟩
    T • (Λ • (T′ • zx {₃₊ m} b a b))
      ≈⟨ back T (sym assoc) ⟩
    T • ((Λ • T′) • zx {₃₊ m} b a b)
      ≈⟨ sym assoc ⟩
    (T • (Λ • T′)) • zx {₃₊ m} b a b
      ≈⟨ front (zx {₃₊ m} b a b) (sym split) ⟩
    hh {₃₊ m} a b c d • zx {₃₊ m} b a b ∎
    where
    module S = E65.Tuple a b c d ab ac ad bc bd cd

    T T′ : W
    T  = S.Σw
    T′ = S.Σ′w

    split : hh {₃₊ m} a b c d ≈ T • (Λ • T′)
    split = e65 a b c d ab ac ad bc bd cd

    -- Where Definition E.1's word sends a and b, and back again.
    pa : prm (sp T) a ≡ i₀
    pa = toℕ-injective (Eq.trans S.prm-Σ-a (Eq.sym toℕ-i₀))

    pb : prm (sp T) b ≡ i₁
    pb = toℕ-injective (Eq.trans S.prm-Σ-b (Eq.sym toℕ-i₁))

    back-a : prm (sp T′) i₀ ≡ a
    back-a = Eq.trans (Eq.cong (prm (sp T′)) (Eq.sym pa)) (prm≡′ S.Σ-inv a)

    back-b : prm (sp T′) i₁ ≡ b
    back-b = Eq.trans (Eq.cong (prm (sp T′)) (Eq.sym pb)) (prm≡′ S.Σ-inv b)

    -- The inverse signs the images no more than the word signs a, b.
    sgn′ : ∀ (x k : Fin N) → prm (sp T) x ≡ k → sgn (sp T) x ≡ false →
           sgn (sp T′) k ≡ false
    sgn′ x k p s =
      Eq.subst (λ z → sgn (sp T′) z ≡ false) p
        (Eq.trans (Eq.sym (Eq.cong (_xor sgn (sp T′) (prm (sp T) x)) s))
                  (sgn≡′ S.Σ-inv x))

    s₀ : sgn (sp T′) i₀ ≡ false
    s₀ = sgn′ a i₀ pa S.sgn-Σ-a

    s₁ : sgn (sp T′) i₁ ≡ false
    s₁ = sgn′ b i₁ pb S.sgn-Σ-b

    -- The letter crosses into the standard frame …
    inL : zx {₃₊ m} a a b • T ≈ T • Y001
    inL = A5-full (cat (hfree-zx a a b) S.hfree-Σ) (cat S.hfree-Σ (hfree-zx i₀ i₀ i₁))
      (≐-trans′ (⊙-cong′ (sp-zx a a b ab) (≐-refl′ {sp T}))
      (≐-trans′ (L-by (sp T) (sp-inj T) a a b (Eq.trans S.sgn-Σ-a (Eq.sym S.sgn-Σ-b)))
                (⊙-cong′ (≐-refl′ {sp T})
                  (≐-trans′ (Eq.subst₂ (λ u v → L (prm (sp T) a) (prm (sp T) a)
                                                  (prm (sp T) b) ≗ L u u v)
                                       pa pb ≐-refl′)
                            (≐-sym′ (sp-zx i₀ i₀ i₁ i₀≢i₁))))))

    -- … and back out of it.
    inR : Y101 • T′ ≈ T′ • zx {₃₊ m} b a b
    inR = A5-full (cat (hfree-zx i₁ i₀ i₁) S.hfree-Σ′) (cat S.hfree-Σ′ (hfree-zx b a b))
      (≐-trans′ (⊙-cong′ (sp-zx i₁ i₀ i₁ i₀≢i₁) (≐-refl′ {sp T′}))
      (≐-trans′ (L-by (sp T′) (sp-inj T′) i₁ i₀ i₁ (Eq.trans s₀ (Eq.sym s₁)))
                (⊙-cong′ (≐-refl′ {sp T′})
                  (≐-trans′ (Eq.subst₂ (λ u v → L (prm (sp T′) i₁) (prm (sp T′) i₀)
                                                  (prm (sp T′) i₁) ≗ L v u v)
                                       back-a back-b ≐-refl′)
                            (≐-sym′ (sp-zx b a b ab))))))
