------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 10's (77), and with it (69)
--
--     ((−1)_[a] X_[a,e]) (H_[e,b] H_[c,d])
--        ≈  (H_[a,b] H_[c,d]) ((−1)_[a] X_[a,b]) ((−1)_[a] X_[a,e])
--                                              |{a, e, b, c, d}| = 5
--
-- (76) moves the same letter across a pair containing a; here the pair
-- contains e, so the letter's sign lands on the pre-image a of e while
-- the pair's other index b is unsigned — the two signs along the pair
-- disagree, which is what `Move.hh-pass` cannot handle, and the extra
-- letter on the right is the price.
--
-- The sign is split off.  With e₀ a fresh index,
--
--     (−1)_[a] X_[a,e]  =  ((−1)_[a] (−1)_[e₀]) ((−1)_[e₀] X_[a,e]),
--
-- the second factor passes the pair by `hh-pass` (its sign is on e₀),
-- and the first is Equation (40) at the tuple: a sign pair with one
-- index on the pair and one off crosses it at the cost of a letter.
-- That is `Eq75.eq40′` carried to a, b, c, d by Definition E.1's word
-- — and taking e₀ to be where the word's inverse sends 4 makes it the
-- carried form's own fresh index, so nothing else is needed.  The
-- Hadamard-free identifications are Corollary A.5; `scratchpad/t75.py`
-- checks every step.  (69) is (77) at e = a + 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq77 (m : ℕ) where

open import Data.Bool using (false ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-inject≤)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₄ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; cat ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; idSP ; NEG ; SWP ; L ; Inj ; sp-inj ; sp-zx
       ; ⊙-inverse ; swapF ; swapF-a ; swapF-o ; swapF-invol
       ; SWP-NEG ; SWP-sym ; NEG-invol ; NEG-comm ; hop ; drop)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-sym to ≐-sym′
          ; ≐-trans to ≐-trans′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; prm≡ to prm≡′ ; sgn≡ to sgn≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m
  using (hfree-zx ; zx-prm ; zx-sgn ; zx-pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃ ; i₀≢i₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65 using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Move m using (hh-pass)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq75 m
  using (NEG-by ; L-by ; eq40′)
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

-- A sign pair crosses any signed permutation, landing on the images.
NEG2-by : ∀ (f : SP) → Inj f → ∀ (u v : Fin N) →
          (NEG u ⊛ NEG v) ⊛ f ≗ f ⊛ (NEG (prm f u) ⊛ NEG (prm f v))
NEG2-by f inj u v =
  ≐-trans′ (⊙-assoc′ (NEG u) (NEG v) f)
  (≐-trans′ (⊙-cong′ (≐-refl′ {NEG u}) (NEG-by f inj v))
  (≐-trans′ (≐-sym′ (⊙-assoc′ (NEG u) f (NEG (prm f v))))
  (≐-trans′ (⊙-cong′ (NEG-by f inj u) (≐-refl′ {NEG (prm f v)}))
            (⊙-assoc′ f (NEG (prm f u)) (NEG (prm f v))))))

-- A sign pair and a signed exchange cross a Hadamard-free word, landing
-- on the images (Corollary A.5), over a variable word: stated at
-- Definition E.1's word, the signed permutations were compared by
-- evaluating the word's (`inZ` 2.8 s), where over a variable word
-- `sp T` is stuck.
private
  L≡ : ∀ {u v w u′ v′ w′ : Fin N} → u ≡ u′ → v ≡ v′ → w ≡ w′ → L u v w ≗ L u′ v′ w′
  L≡ Eq.refl Eq.refl Eq.refl = ≐-refl′

  zzCross : ∀ (T : W) → HFreeʷ T → ∀ (x y x′ y′ : Fin N) →
            prm (sp T) x ≡ x′ → prm (sp T) y ≡ y′ → zz {₃₊ m} x y • T ≈ T • zz {₃₊ m} x′ y′
  zzCross T hT x y x′ y′ px py =
    A5-full (cat (gen (hf-zz x y)) hT) (cat hT (gen (hf-zz x′ y′)))
      (≐-trans′ (NEG2-by (sp T) (sp-inj T) x y)
                (⊙-cong′ (≐-refl′ {sp T}) (⊙-cong′ (neg≡ px) (neg≡ py))))

  zxCross : ∀ (T : W) → HFreeʷ T → ∀ (x y z : Fin N) (yz : y ≢ z) (x′ y′ z′ : Fin N) (y′z′ : y′ ≢ z′) →
            prm (sp T) x ≡ x′ → prm (sp T) y ≡ y′ → prm (sp T) z ≡ z′ → sgn (sp T) y ≡ sgn (sp T) z →
            zx {₃₊ m} x y z • T ≈ T • zx {₃₊ m} x′ y′ z′
  zxCross T hT x y z yz x′ y′ z′ y′z′ px py pz s =
    A5-full (cat (hfree-zx x y z) hT) (cat hT (hfree-zx x′ y′ z′))
      (≐-trans′ (⊙-cong′ (sp-zx x y z yz) (≐-refl′ {sp T}))
      (≐-trans′ (L-by (sp T) (sp-inj T) x y z s)
                (⊙-cong′ (≐-refl′ {sp T})
                  (≐-trans′ (L≡ px py pz) (≐-sym′ (sp-zx x′ y′ z′ y′z′))))))

module _ (e65 : Eq65) where

  ----------------------------------------------------------------------
  -- Equation (40) at a tuple

  module Frame (a b c d : Fin N)
               (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d)
               (bc : b ≢ c) (bd : b ≢ d) (cd : c ≢ d) where

    private
      module S = E65.Tuple a b c d ab ac ad bc bd cd

      T T′ : W
      T  = S.Σw
      T′ = S.Σ′w

      pa : prm (sp T) a ≡ i₀
      pa = toℕ-injective (Eq.trans S.prm-Σ-a (Eq.sym toℕ-i₀))

      pb : prm (sp T) b ≡ i₁
      pb = toℕ-injective (Eq.trans S.prm-Σ-b (Eq.sym toℕ-i₁))

      pc : prm (sp T) c ≡ i₃
      pc = toℕ-injective (Eq.trans S.prm-Σ-c (Eq.sym toℕ-i₃))

      pd : prm (sp T) d ≡ i₂
      pd = toℕ-injective (Eq.trans S.prm-Σ-d (Eq.sym toℕ-i₂))

      -- The inverse undoes it.
      bk : ∀ {x k : Fin N} → prm (sp T) x ≡ k → prm (sp T′) k ≡ x
      bk {x} p = Eq.trans (Eq.cong (prm (sp T′)) (Eq.sym p)) (prm≡′ S.Σ-inv x)

      sgn′ : ∀ (x k : Fin N) → prm (sp T) x ≡ k → sgn (sp T) x ≡ false →
             sgn (sp T′) k ≡ false
      sgn′ x k p s =
        Eq.subst (λ z → sgn (sp T′) z ≡ false) p
          (Eq.trans (Eq.sym (Eq.cong (_xor sgn (sp T′) (prm (sp T) x)) s))
                    (sgn≡′ S.Σ-inv x))

      -- … on both sides.
      T′T : sp T′ ⊛ sp T ≗ idSP
      T′T = ⊙-inverse (sp T) (sp T′) (sp-inj T′) S.Σ-inv

    -- The fresh index: where the inverse sends 4.
    e₀ : Fin N
    e₀ = prm (sp T′) f₄

    private
      Te₀ : prm (sp T) e₀ ≡ f₄
      Te₀ = prm≡′ T′T f₄

      -- It is none of the four, the inverse being injective.
      fresh : ∀ {x k : Fin N} → prm (sp T) x ≡ k → k ≢ f₄ → e₀ ≢ x
      fresh {x} {k} p ne e = ne (sp-inj T′ (Eq.trans (bk p) (Eq.sym e)))

    e₀a : e₀ ≢ a
    e₀a = fresh pa i₀≢f₄

    e₀b : e₀ ≢ b
    e₀b = fresh pb i₁≢f₄

    e₀c : e₀ ≢ c
    e₀c = fresh pc i₃≢f₄

    e₀d : e₀ ≢ d
    e₀d = fresh pd i₂≢f₄

    private
      split : hh {₃₊ m} a b c d ≈ T • (Λ • T′)
      split = e65 a b c d ab ac ad bc bd cd

      -- The sign pair crosses into the standard frame, onto 0 and 4 …
      inZ : zz {₃₊ m} a e₀ • T ≈ T • zz {₃₊ m} i₀ f₄
      inZ = zzCross T S.hfree-Σ a e₀ i₀ f₄ pa Te₀

      -- … and the letters come back out of it.
      outY : zx {₃₊ m} i₁ i₁ i₀ • T′ ≈ T′ • zx {₃₊ m} b b a
      outY = zxCross T′ S.hfree-Σ′ i₁ i₁ i₀ (≢sym i₀≢i₁) b b a (≢sym ab) (bk pb) (bk pb) (bk pa)
               (Eq.trans (sgn′ b i₁ pb S.sgn-Σ-b) (Eq.sym (sgn′ a i₀ pa S.sgn-Σ-a)))

      outZ : zz {₃₊ m} i₀ f₄ • T′ ≈ T′ • zz {₃₊ m} a e₀
      outZ = zzCross T′ S.hfree-Σ′ i₀ f₄ a e₀ (bk pa) Eq.refl

      Z04 Y110 : W
      Z04  = zz {₃₊ m} i₀ f₄
      Y110 = zx {₃₊ m} i₁ i₁ i₀

    -- (40) at the tuple: the sign pair on a and e₀ crosses the pair at
    -- the cost of (−1)_[b] X_[b,a].
    std : zz {₃₊ m} a e₀ • hh {₃₊ m} a b c d
          ≈ hh {₃₊ m} a b c d • (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a)
    std = begin
      zz {₃₊ m} a e₀ • hh {₃₊ m} a b c d        ≈⟨ back (zz {₃₊ m} a e₀) split ⟩
      zz {₃₊ m} a e₀ • (T • (Λ • T′))           ≈⟨ sym assoc ⟩
      (zz {₃₊ m} a e₀ • T) • (Λ • T′)           ≈⟨ front (Λ • T′) inZ ⟩
      (T • Z04) • (Λ • T′)                      ≈⟨ assoc ⟩
      T • (Z04 • (Λ • T′))                      ≈⟨ back T (sym assoc) ⟩
      T • ((Z04 • Λ) • T′)                      ≈⟨ back T (front T′ eq40′) ⟩
      T • ((Λ • (Z04 • Y110)) • T′)             ≈⟨ back T assoc ⟩
      T • (Λ • ((Z04 • Y110) • T′))             ≈⟨ back T (back Λ assoc) ⟩
      T • (Λ • (Z04 • (Y110 • T′)))             ≈⟨ back T (back Λ (back Z04 outY)) ⟩
      T • (Λ • (Z04 • (T′ • zx {₃₊ m} b b a)))  ≈⟨ back T (back Λ (sym assoc)) ⟩
      T • (Λ • ((Z04 • T′) • zx {₃₊ m} b b a))  ≈⟨ back T (back Λ (front (zx {₃₊ m} b b a) outZ)) ⟩
      T • (Λ • ((T′ • zz {₃₊ m} a e₀) • zx {₃₊ m} b b a))
                                                ≈⟨ back T (back Λ assoc) ⟩
      T • (Λ • (T′ • (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a)))
                                                ≈⟨ back T (sym assoc) ⟩
      T • ((Λ • T′) • (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a))
                                                ≈⟨ sym assoc ⟩
      (T • (Λ • T′)) • (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a)
                                                ≈⟨ front (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a) (sym split) ⟩
      hh {₃₊ m} a b c d • (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a) ∎

  ----------------------------------------------------------------------
  -- (77)

  eq77 : ∀ (a e b c d : Fin N) →
         a ≢ e → a ≢ b → a ≢ c → a ≢ d →
         e ≢ b → e ≢ c → e ≢ d → b ≢ c → b ≢ d → c ≢ d →
         zx {₃₊ m} a a e • hh {₃₊ m} e b c d
         ≈ hh {₃₊ m} a b c d • (zx {₃₊ m} a a b • zx {₃₊ m} a a e)
  eq77 a e b c d ae ab ac ad eb ec ed bc bd cd = begin
    zx {₃₊ m} a a e • hh {₃₊ m} e b c d                 ≈⟨ front (hh {₃₊ m} e b c d) splitU ⟩
    (zz {₃₊ m} a e₀ • U) • hh {₃₊ m} e b c d            ≈⟨ assoc ⟩
    zz {₃₊ m} a e₀ • (U • hh {₃₊ m} e b c d)            ≈⟨ back (zz {₃₊ m} a e₀) passU ⟩
    zz {₃₊ m} a e₀ • (hh {₃₊ m} a b c d • U)            ≈⟨ sym assoc ⟩
    (zz {₃₊ m} a e₀ • hh {₃₊ m} a b c d) • U            ≈⟨ front U F.std ⟩
    (hh {₃₊ m} a b c d • (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a)) • U
                                                        ≈⟨ assoc ⟩
    hh {₃₊ m} a b c d • ((zz {₃₊ m} a e₀ • zx {₃₊ m} b b a) • U)
                                                        ≈⟨ back (hh {₃₊ m} a b c d) foldU ⟩
    hh {₃₊ m} a b c d • (zx {₃₊ m} a a b • zx {₃₊ m} a a e) ∎
    where
    module F = Frame a b c d ab ac ad bc bd cd

    e₀ : Fin N
    e₀ = F.e₀

    -- The letter with its sign moved onto the fresh index, and its
    -- inverse (which is itself unless e₀ happens to be e).
    U U′ : W
    U  = zx {₃₊ m} e₀ a e
    U′ = zx {₃₊ m} (swapF a e e₀) a e

    -- Splitting the sign off.
    splitU : zx {₃₊ m} a a e ≈ zz {₃₊ m} a e₀ • U
    splitU = A5-full (hfree-zx a a e) (cat (gen (hf-zz a e₀)) (hfree-zx e₀ a e))
      (≐-trans′ (sp-zx a a e ae)
      (≐-sym′ (≐-trans′ (⊙-cong′ (≐-refl′ {NEG a ⊛ NEG e₀}) (sp-zx e₀ a e ae))
              (≐-trans′ (⊙-assoc′ (NEG a) (NEG e₀) (NEG e₀ ⊛ SWP a e))
                        (⊙-cong′ (≐-refl′ {NEG a})
                                 (drop (NEG e₀) (NEG e₀) (SWP a e) (NEG-invol e₀)))))))

    -- The rest passes the pair, its sign being on none of the four.
    passU : U • hh {₃₊ m} e b c d ≈ hh {₃₊ m} a b c d • U
    passU = hh-pass e65 U U′ (hfree-zx e₀ a e) (hfree-zx (swapF a e e₀) a e)
              (zx-pair e₀ (swapF a e e₀) a e (Eq.sym (swapF-invol a e e₀)))
              a b c d e b c d
              (Eq.trans (zx-prm e₀ a e a) (swapF-a a e))
              (Eq.trans (zx-prm e₀ a e b) (swapF-o a e b (≢sym ab) (≢sym eb)))
              (Eq.trans (zx-prm e₀ a e c) (swapF-o a e c (≢sym ac) (≢sym ec)))
              (Eq.trans (zx-prm e₀ a e d) (swapF-o a e d (≢sym ad) (≢sym ed)))
              (Eq.trans (zx-sgn e₀ a e a (≢sym F.e₀a)) (Eq.sym (zx-sgn e₀ a e b (≢sym F.e₀b))))
              (Eq.trans (zx-sgn e₀ a e c (≢sym F.e₀c)) (Eq.sym (zx-sgn e₀ a e d (≢sym F.e₀d))))
              ab ac ad bc bd cd

    -- And what is left beside the pair is the two letters of (77).
    foldU : (zz {₃₊ m} a e₀ • zx {₃₊ m} b b a) • U ≈ zx {₃₊ m} a a b • zx {₃₊ m} a a e
    foldU = A5-full (cat (cat (gen (hf-zz a e₀)) (hfree-zx b b a)) (hfree-zx e₀ a e))
                    (cat (hfree-zx a a b) (hfree-zx a a e))
      (≐-trans′ (⊙-cong′ (⊙-cong′ (≐-refl′ {NEG a ⊛ NEG e₀}) (sp-zx b b a (≢sym ab)))
                         (sp-zx e₀ a e ae))
      (≐-trans′ lhs
      (≐-sym′ (≐-trans′ (⊙-cong′ (sp-zx a a b ab) (sp-zx a a e ae)) rhs))))
      where
      R : SP
      R = SWP b a ⊛ SWP a e

      -- ((a e₀) (b ⇄)) (e₀ ⇄′)  ≗  a b R: the two signs on e₀ meet and
      -- cancel, the exchange of a and b leaving e₀ alone.
      lhs : ((NEG a ⊛ NEG e₀) ⊛ (NEG b ⊛ SWP b a)) ⊛ (NEG e₀ ⊛ SWP a e)
            ≗ NEG a ⊛ (NEG b ⊛ R)
      lhs =
        ≐-trans′ (⊙-assoc′ (NEG a ⊛ NEG e₀) (NEG b ⊛ SWP b a) (NEG e₀ ⊛ SWP a e))
        (≐-trans′ (⊙-assoc′ (NEG a) (NEG e₀) ((NEG b ⊛ SWP b a) ⊛ (NEG e₀ ⊛ SWP a e)))
        (⊙-cong′ (≐-refl′ {NEG a})
          (≐-trans′ (⊙-cong′ (≐-refl′ {NEG e₀})
                      (≐-trans′ (⊙-assoc′ (NEG b) (SWP b a) (NEG e₀ ⊛ SWP a e))
                      (⊙-cong′ (≐-refl′ {NEG b})
                        (≐-trans′ (hop (SWP b a) (NEG e₀) (SWP b a) (NEG (swapF b a e₀))
                                       (SWP a e) (SWP-NEG b a e₀))
                                  (⊙-cong′ (neg≡ (swapF-o b a e₀ F.e₀b F.e₀a))
                                           (≐-refl′ {R}))))))
          (≐-trans′ (hop (NEG e₀) (NEG b) (NEG e₀) (NEG b) (NEG e₀ ⊛ R) (NEG-comm e₀ b))
                    (⊙-cong′ (≐-refl′ {NEG b})
                             (drop (NEG e₀) (NEG e₀) R (NEG-invol e₀)))))))

      -- (a ⇄) (a ⇄′)  ≗  a b R: the second sign crosses the first
      -- exchange onto b.
      rhs : (NEG a ⊛ SWP a b) ⊛ (NEG a ⊛ SWP a e) ≗ NEG a ⊛ (NEG b ⊛ R)
      rhs =
        ≐-trans′ (⊙-assoc′ (NEG a) (SWP a b) (NEG a ⊛ SWP a e))
        (⊙-cong′ (≐-refl′ {NEG a})
          (≐-trans′ (hop (SWP a b) (NEG a) (SWP a b) (NEG (swapF a b a)) (SWP a e)
                         (SWP-NEG a b a))
                    (⊙-cong′ (neg≡ (swapF-a a b))
                             (⊙-cong′ (SWP-sym a b) (≐-refl′ {SWP a e})))))
