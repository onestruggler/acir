------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 10's (67)
--
--     H_[b,a] H_[c,d]  ≈  (H_[a,b] H_[c,d]) ((−1)_[b] X_[a,b])
--                                                  {a,b} ∩ {c,d} = ∅
--
-- The two letters have the same pairs in different orders, and that is
-- what neither Corollary A.7 nor `Move.hh-conj` reaches: the one word
-- that turns a pair round, its own exchange, signs the two indices
-- unequally.  Equation (40) is the rule that does it, and the route is:
--
--   * at the standard pair, H_[0,1] H_[2,3] is the conjugate of
--     Λ = H_[0,1] H_[3,2] by (−1)_[4] X_[2,3] — `hh-conj`, the fresh
--     sign on 4 making both pairs' signs agree;
--   * that letter is (−1)_[3](−1)_[4] times (−1)_[3] X_[2,3], which
--     crosses Λ by (75) on the second pair, and the sign pair crosses
--     it by (40) at the cost of (−1)_[2] X_[2,3];
--   * what is left beside Λ is Hadamard-free and, by Corollary A.5,
--     just (−1)_[2] X_[2,3] — so H_[0,1] H_[2,3] ≈ Λ ((−1)_[2] X_[2,3]);
--   * and at any tuple that is Definition E.1's word for (c , d , a , b)
--     carrying it across, (66) putting the pairs back in order.
--
-- (72), H_[a,b] H_[b,a] ≈ (−1)_[b] X_[a,b], follows by (66) and (71).
-- `scratchpad/t75.py` checks every step numerically.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq67 (m : ℕ) where

open import Data.Bool using (Bool ; false ; true ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-inject≤)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₄ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Data.List using (_∷_ ; [])
open import Data.Nat using (s≤s ; z≤n)
open import Data.Nat.Properties using (≤-trans)
import Data.Nat
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
  using (_P,_===_ ; r40)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (hh ; zz ; zx ; zzℕ ; zxℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz ; zxℕ-zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; cat ; nil ; hf-zz ; fin ; fin-toℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; idSP ; NEG ; SWP ; L ; sp-inj ; sp-zx
       ; swapF ; swapF-a ; swapF-b ; swapF-o
       ; SWP-NEG ; SWP-sym ; SWP-invol ; NEG-invol ; NEG-comm ; hop ; drop)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-sym to ≐-sym′
          ; ≐-trans to ≐-trans′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; ⊙-idʳ to ⊙-idʳ′ ; prm≡ to prm≡′ ; sgn≡ to sgn≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SigmaPerm m
  using (hfree-zx ; zx-prm ; zx-sgn ; zx-pair)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃
       ; i₀≢i₁ ; i₀≢i₂ ; i₀≢i₃ ; i₁≢i₂ ; i₁≢i₃ ; i₂≢i₃ ; hh0132≡ ; gen-hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65 using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m
  using (Eq65 ; eq66)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Move m using (hh-conj)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq75 m using (L-by ; eq75)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m as FU using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Avoid as AV using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (8≤2^)
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

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

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
  Z34 Y223 Y232 Y323 Y332 Y423 : W
  Z34  = zz {₃₊ m} i₃ f₄
  Y223 = zx {₃₊ m} i₂ i₂ i₃
  Y232 = zx {₃₊ m} i₂ i₃ i₂
  Y323 = zx {₃₊ m} i₃ i₂ i₃
  Y332 = zx {₃₊ m} i₃ i₃ i₂
  Y423 = zx {₃₊ m} f₄ i₂ i₃

  -- The standard pair as a letter.
  Λ≡ : Λ ≡ hh {₃₊ m} i₀ i₁ i₃ i₂
  Λ≡ = Eq.trans hh0132≡ (gen-hh i₀ i₁ i₃ i₂ i₀≢i₁ (≢sym i₂≢i₃))

  -- Equation (40) at those words.
  e40 : Z34 • Λ ≈ Λ • (Z34 • Y223)
  e40 = Eq.subst₂ (λ z y → z • Λ ≈ Λ • (z • y))
          (Eq.trans (Eq.cong₂ (zzℕ {₃₊ m}) (Eq.sym toℕ-i₃) (Eq.sym toℕ-f₄))
                    (zzℕ-zz i₃ f₄))
          (Eq.trans (Eq.cong₂ (λ u v → zxℕ {₃₊ m} u u v)
                              (Eq.sym toℕ-i₂) (Eq.sym toℕ-i₃))
                    (zxℕ-zx i₂ i₂ i₃))
          (axiom r40)

  ------------------------------------------------------------------
  -- The Hadamard-free identifications (Corollary A.5)

  -- (−1)_[4] X_[2,3] is the sign pair on 3, 4 times (−1)_[3] X_[2,3].
  split423 : Y423 ≈ Z34 • Y323
  split423 = A5-full (hfree-zx f₄ i₂ i₃) (cat (gen (hf-zz i₃ f₄)) (hfree-zx i₃ i₂ i₃))
    (≐-trans′ (sp-zx f₄ i₂ i₃ i₂≢i₃)
    (≐-sym′ (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₃ ⊛ NEG f₄}) (sp-zx i₃ i₂ i₃ i₂≢i₃))
            (≐-trans′ (⊙-assoc′ (NEG i₃) (NEG f₄) (NEG i₃ ⊛ SWP i₂ i₃))
            (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₃})
                        (hop (NEG f₄) (NEG i₃) (NEG f₄) (NEG i₃) (SWP i₂ i₃)
                             (NEG-comm f₄ i₃)))
                      (drop (NEG i₃) (NEG i₃) (NEG f₄ ⊛ SWP i₂ i₃) (NEG-invol i₃)))))))

  -- The letter is the same whichever way its exchange is written.
  Y323≈Y332 : Y323 ≈ Y332
  Y323≈Y332 = A5-full (hfree-zx i₃ i₂ i₃) (hfree-zx i₃ i₃ i₂)
    (≐-trans′ (sp-zx i₃ i₂ i₃ i₂≢i₃)
    (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₃}) (SWP-sym i₂ i₃))
              (≐-sym′ (sp-zx i₃ i₃ i₂ (≢sym i₂≢i₃)))))

  -- Two letters on the same exchange multiply to their signs.
  pair232 : Y232 • Y423 ≈ zz {₃₊ m} i₂ f₄
  pair232 = A5-full (cat (hfree-zx i₂ i₃ i₂) (hfree-zx f₄ i₂ i₃)) (gen (hf-zz i₂ f₄))
    (≐-trans′ (⊙-cong′ (sp-zx i₂ i₃ i₂ (≢sym i₂≢i₃)) (sp-zx f₄ i₂ i₃ i₂≢i₃))
    (≐-trans′ (⊙-assoc′ (NEG i₂) (SWP i₃ i₂) (NEG f₄ ⊛ SWP i₂ i₃))
              (⊙-cong′ (≐-refl′ {NEG i₂})
                (≐-trans′ (hop (SWP i₃ i₂) (NEG f₄) (SWP i₃ i₂) (NEG (swapF i₃ i₂ f₄))
                               (SWP i₂ i₃) (SWP-NEG i₃ i₂ f₄))
                (≐-trans′ (⊙-cong′ (neg≡ (swapF-o i₃ i₂ f₄ (≢sym i₃≢f₄) (≢sym i₂≢f₄)))
                                   (≐-trans′ (⊙-cong′ (SWP-sym i₃ i₂) (≐-refl′ {SWP i₂ i₃}))
                                             (SWP-invol i₂ i₃)))
                          (⊙-idʳ′ (NEG f₄)))))))
    where
    neg≡ : ∀ {x y : Fin N} → x ≡ y → NEG x ≗ NEG y
    neg≡ Eq.refl = ≐-refl′

  -- And a sign pair on 2, 4 moves the letter's sign from 2 to 3 and back.
  fold223 : (Z34 • Y223) • zz {₃₊ m} i₂ f₄ ≈ Y223
  fold223 = A5-full (cat (cat (gen (hf-zz i₃ f₄)) (hfree-zx i₂ i₂ i₃)) (gen (hf-zz i₂ f₄)))
                    (hfree-zx i₂ i₂ i₃)
    (≐-trans′ (⊙-cong′ (⊙-cong′ (≐-refl′ {NEG i₃ ⊛ NEG f₄}) (sp-zx i₂ i₂ i₃ i₂≢i₃))
                       (≐-refl′ {NEG i₂ ⊛ NEG f₄}))
    (≐-trans′ core (≐-sym′ (sp-zx i₂ i₂ i₃ i₂≢i₃))))
    where
    neg≡ : ∀ {x y : Fin N} → x ≡ y → NEG x ≗ NEG y
    neg≡ Eq.refl = ≐-refl′

    S : SP
    S = SWP i₂ i₃

    -- The exchange carries the trailing signs on 2, 4 to 3, 4.
    across : S ⊛ (NEG i₂ ⊛ NEG f₄) ≗ NEG i₃ ⊛ (NEG f₄ ⊛ S)
    across =
      ≐-trans′ (hop S (NEG i₂) S (NEG (swapF i₂ i₃ i₂)) (NEG f₄) (SWP-NEG i₂ i₃ i₂))
               (⊙-cong′ (neg≡ (swapF-a i₂ i₃))
                 (≐-trans′ (SWP-NEG i₂ i₃ f₄)
                           (⊙-cong′ (neg≡ (swapF-o i₂ i₃ f₄ (≢sym i₂≢f₄) (≢sym i₃≢f₄)))
                                    (≐-refl′ {S}))))

    core : ((NEG i₃ ⊛ NEG f₄) ⊛ (NEG i₂ ⊛ S)) ⊛ (NEG i₂ ⊛ NEG f₄) ≗ NEG i₂ ⊛ S
    core =
      ≐-trans′ (⊙-assoc′ (NEG i₃ ⊛ NEG f₄) (NEG i₂ ⊛ S) (NEG i₂ ⊛ NEG f₄))
      (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₃ ⊛ NEG f₄})
                  (≐-trans′ (⊙-assoc′ (NEG i₂) S (NEG i₂ ⊛ NEG f₄))
                            (⊙-cong′ (≐-refl′ {NEG i₂}) across)))
      -- (N₃ N₄) (N₂ (N₃ (N₄ S)))  ≗  N₂ S
      (≐-trans′ (⊙-assoc′ (NEG i₃) (NEG f₄) (NEG i₂ ⊛ (NEG i₃ ⊛ (NEG f₄ ⊛ S))))
      (≐-trans′ (⊙-cong′ (≐-refl′ {NEG i₃})
                  (≐-trans′ (hop (NEG f₄) (NEG i₂) (NEG f₄) (NEG i₂)
                                 (NEG i₃ ⊛ (NEG f₄ ⊛ S)) (NEG-comm f₄ i₂))
                  (⊙-cong′ (≐-refl′ {NEG i₂})
                    (≐-trans′ (hop (NEG f₄) (NEG i₃) (NEG f₄) (NEG i₃) (NEG f₄ ⊛ S)
                                   (NEG-comm f₄ i₃))
                    (⊙-cong′ (≐-refl′ {NEG i₃})
                             (drop (NEG f₄) (NEG f₄) S (NEG-invol f₄)))))))
      (≐-trans′ (hop (NEG i₃) (NEG i₂) (NEG i₃) (NEG i₂) (NEG i₃ ⊛ S)
                     (NEG-comm i₃ i₂))
                (⊙-cong′ (≐-refl′ {NEG i₂})
                         (drop (NEG i₃) (NEG i₃) S (NEG-invol i₃)))))))

------------------------------------------------------------------------
-- (67) at the standard pair, and at any tuple

module _ (e65 : Eq65) where

  private
    -- (−1)_[4] X_[2,3] turns the second pair of Λ round: its fresh sign
    -- sits on neither pair, so `hh-conj` applies.
    turn : Y423 • (Λ • Y423) ≈ hh {₃₊ m} i₀ i₁ i₂ i₃
    turn = Eq.subst (λ h → Y423 • (h • Y423) ≈ hh {₃₊ m} i₀ i₁ i₂ i₃) (Eq.sym Λ≡)
             (hh-conj e65 Y423 Y423 (hfree-zx f₄ i₂ i₃) (hfree-zx f₄ i₂ i₃) inv
                      i₀ i₁ i₂ i₃ i₀ i₁ i₃ i₂ p₀ p₁ p₂ p₃
                      (Eq.trans (sg i₀ i₀≢f₄) (Eq.sym (sg i₁ i₁≢f₄)))
                      (Eq.trans (sg i₂ i₂≢f₄) (Eq.sym (sg i₃ i₃≢f₄)))
                      i₀≢i₁ i₀≢i₂ i₀≢i₃ i₁≢i₂ i₁≢i₃ i₂≢i₃)
      where
      inv : sp Y423 ⊛ sp Y423 ≗ idSP
      inv = zx-pair f₄ f₄ i₂ i₃ (Eq.sym (swapF-o i₂ i₃ f₄ (≢sym i₂≢f₄) (≢sym i₃≢f₄)))

      p₀ : prm (sp Y423) i₀ ≡ i₀
      p₀ = Eq.trans (zx-prm f₄ i₂ i₃ i₀) (swapF-o i₂ i₃ i₀ i₀≢i₂ i₀≢i₃)

      p₁ : prm (sp Y423) i₁ ≡ i₁
      p₁ = Eq.trans (zx-prm f₄ i₂ i₃ i₁) (swapF-o i₂ i₃ i₁ i₁≢i₂ i₁≢i₃)

      p₂ : prm (sp Y423) i₂ ≡ i₃
      p₂ = Eq.trans (zx-prm f₄ i₂ i₃ i₂) (swapF-a i₂ i₃)

      p₃ : prm (sp Y423) i₃ ≡ i₂
      p₃ = Eq.trans (zx-prm f₄ i₂ i₃ i₃) (swapF-b i₂ i₃)

      sg : ∀ (x : Fin N) → x ≢ f₄ → sgn (sp Y423) x ≡ false
      sg x ne = zx-sgn f₄ i₂ i₃ x ne

    -- (75) on the second pair of Λ.
    second : Y323 • Λ ≈ Λ • Y232
    second = begin
      Y323 • Λ                        ≈⟨ front Λ Y323≈Y332 ⟩
      Y332 • Λ                        ≈⟨ back Y332 flipΛ ⟩
      Y332 • hh {₃₊ m} i₃ i₂ i₀ i₁    ≈⟨ eq75 e65 i₃ i₂ i₀ i₁ (≢sym i₂≢i₃) (≢sym i₀≢i₃)
                                              (≢sym i₁≢i₃) (≢sym i₀≢i₂) (≢sym i₁≢i₂) i₀≢i₁ ⟩
      hh {₃₊ m} i₃ i₂ i₀ i₁ • Y232    ≈⟨ front Y232 (sym flipΛ) ⟩
      Λ • Y232                        ∎
      where
      flipΛ : Λ ≈ hh {₃₊ m} i₃ i₂ i₀ i₁
      flipΛ = trans (refl≡ Λ≡)
                    (eq66 e65 i₀ i₁ i₃ i₂ i₀≢i₁ i₀≢i₃ i₀≢i₂ i₁≢i₃ i₁≢i₂ (≢sym i₂≢i₃))

  -- (67) at the standard pair: H_[0,1] H_[2,3] ≈ Λ ((−1)_[2] X_[2,3]).
  eq67₀ : hh {₃₊ m} i₀ i₁ i₂ i₃ ≈ Λ • Y223
  eq67₀ = begin
    hh {₃₊ m} i₀ i₁ i₂ i₃                  ≈⟨ sym turn ⟩
    Y423 • (Λ • Y423)                      ≈⟨ front (Λ • Y423) split423 ⟩
    (Z34 • Y323) • (Λ • Y423)              ≈⟨ assoc ⟩
    Z34 • (Y323 • (Λ • Y423))              ≈⟨ back Z34 (sym assoc) ⟩
    Z34 • ((Y323 • Λ) • Y423)              ≈⟨ back Z34 (front Y423 second) ⟩
    Z34 • ((Λ • Y232) • Y423)              ≈⟨ back Z34 assoc ⟩
    Z34 • (Λ • (Y232 • Y423))              ≈⟨ sym assoc ⟩
    (Z34 • Λ) • (Y232 • Y423)              ≈⟨ cong e40 pair232 ⟩
    (Λ • (Z34 • Y223)) • zz {₃₊ m} i₂ f₄    ≈⟨ assoc ⟩
    Λ • ((Z34 • Y223) • zz {₃₊ m} i₂ f₄)    ≈⟨ back Λ fold223 ⟩
    Λ • Y223                               ∎

  -- (67) at any tuple: Definition E.1's word for (c , d , a , b)
  -- carries a, b to 3, 2, so the standard instance applies there.
  eq67 : ∀ (a b c d : Fin N) →
         a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
         hh {₃₊ m} b a c d ≈ hh {₃₊ m} a b c d • zx {₃₊ m} b a b
  eq67 a b c d ab ac ad bc bd cd = begin
    hh {₃₊ m} b a c d                     ≈⟨ eq66 e65 b a c d (≢sym ab) bc bd ac ad cd ⟩
    hh {₃₊ m} c d b a                     ≈⟨ sym fwd ⟩
    T • (hh {₃₊ m} i₀ i₁ i₂ i₃ • T′)       ≈⟨ back T (front T′ eq67₀) ⟩
    T • ((Λ • Y223) • T′)                 ≈⟨ ins ⟩
    (T • (Λ • T′)) • (T • (Y223 • T′))    ≈⟨ cong bwd letter ⟩
    hh {₃₊ m} c d a b • zx {₃₊ m} b b a   ≈⟨ cong (eq66 e65 c d a b cd (≢sym ac) (≢sym bc)
                                                     (≢sym ad) (≢sym bd) ab)
                                               Ybba≈Ybab ⟩
    hh {₃₊ m} a b c d • zx {₃₊ m} b a b   ∎
    where
    module S = E65.Tuple c d a b cd (≢sym ac) (≢sym bc) (≢sym ad) (≢sym bd) ab

    T T′ : W
    T  = S.Σw
    T′ = S.Σ′w

    -- Σ_{c,d,a,b} sends c, d, a, b to 0, 1, 3, 2, signing none of them.
    pc : prm (sp T) c ≡ i₀
    pc = toℕ-injective (Eq.trans S.prm-Σ-a (Eq.sym toℕ-i₀))

    pd : prm (sp T) d ≡ i₁
    pd = toℕ-injective (Eq.trans S.prm-Σ-b (Eq.sym toℕ-i₁))

    pa : prm (sp T) a ≡ i₃
    pa = toℕ-injective (Eq.trans S.prm-Σ-c (Eq.sym toℕ-i₃))

    pb : prm (sp T) b ≡ i₂
    pb = toℕ-injective (Eq.trans S.prm-Σ-d (Eq.sym toℕ-i₂))

    fwd : T • (hh {₃₊ m} i₀ i₁ i₂ i₃ • T′) ≈ hh {₃₊ m} c d b a
    fwd = hh-conj e65 T T′ S.hfree-Σ S.hfree-Σ′ S.Σ-inv c d b a i₀ i₁ i₂ i₃
                  pc pd pb pa
                  (Eq.trans S.sgn-Σ-a (Eq.sym S.sgn-Σ-b))
                  (Eq.trans S.sgn-Σ-d (Eq.sym S.sgn-Σ-c))
                  cd (≢sym bc) (≢sym ac) (≢sym bd) (≢sym ad) (≢sym ab)

    bwd : T • (Λ • T′) ≈ hh {₃₊ m} c d a b
    bwd = sym (e65 c d a b cd (≢sym ac) (≢sym bc) (≢sym ad) (≢sym bd) ab)

    -- The inverse sends 2, 3 back to b, a, signing neither.
    back-b : prm (sp T′) i₂ ≡ b
    back-b = Eq.trans (Eq.cong (prm (sp T′)) (Eq.sym pb)) (prm≡′ S.Σ-inv b)

    back-a : prm (sp T′) i₃ ≡ a
    back-a = Eq.trans (Eq.cong (prm (sp T′)) (Eq.sym pa)) (prm≡′ S.Σ-inv a)

    sgn′ : ∀ (x k : Fin N) → prm (sp T) x ≡ k → sgn (sp T) x ≡ false →
           sgn (sp T′) k ≡ false
    sgn′ x k p s =
      Eq.subst (λ z → sgn (sp T′) z ≡ false) p
        (Eq.trans (Eq.sym (Eq.cong (_xor sgn (sp T′) (prm (sp T) x)) s))
                  (sgn≡′ S.Σ-inv x))

    letter : T • (Y223 • T′) ≈ zx {₃₊ m} b b a
    letter = A5-full (cat S.hfree-Σ (cat (hfree-zx i₂ i₂ i₃) S.hfree-Σ′)) (hfree-zx b b a)
      (≐-trans′ (⊙-cong′ (≐-refl′ {sp T})
                  (≐-trans′ (⊙-cong′ (sp-zx i₂ i₂ i₃ i₂≢i₃) (≐-refl′ {sp T′}))
                            (L-by (sp T′) (sp-inj T′) i₂ i₂ i₃
                                  (Eq.trans (sgn′ b i₂ pb S.sgn-Σ-d)
                                            (Eq.sym (sgn′ a i₃ pa S.sgn-Σ-c))))))
      (≐-trans′ (drop (sp T) (sp T′) (L (prm (sp T′) i₂) (prm (sp T′) i₂) (prm (sp T′) i₃))
                      S.Σ-inv)
      (≐-trans′ (Eq.subst₂ (λ u v → L (prm (sp T′) i₂) (prm (sp T′) i₂) (prm (sp T′) i₃)
                                     ≗ L u u v)
                           back-b back-a ≐-refl′)
                (≐-sym′ (sp-zx b b a (≢sym ab))))))

    Ybba≈Ybab : zx {₃₊ m} b b a ≈ zx {₃₊ m} b a b
    Ybba≈Ybab = A5-full (hfree-zx b b a) (hfree-zx b a b)
      (≐-trans′ (sp-zx b b a (≢sym ab))
      (≐-trans′ (⊙-cong′ (≐-refl′ {NEG b}) (SWP-sym b a))
                (≐-sym′ (sp-zx b a b ab))))

    -- Splitting the conjugate of a product, T′ T being ε.
    ins : T • ((Λ • Y223) • T′) ≈ (T • (Λ • T′)) • (T • (Y223 • T′))
    ins = begin
      T • ((Λ • Y223) • T′)               ≈⟨ back T assoc ⟩
      T • (Λ • (Y223 • T′))               ≈⟨ back T (back Λ (sym left-unit)) ⟩
      T • (Λ • (ε • (Y223 • T′)))         ≈⟨ back T (back Λ (front (Y223 • T′) (sym S.Σ′Σ-≈))) ⟩
      T • (Λ • ((T′ • T) • (Y223 • T′)))  ≈⟨ back T (back Λ assoc) ⟩
      T • (Λ • (T′ • (T • (Y223 • T′))))  ≈⟨ back T (sym assoc) ⟩
      T • ((Λ • T′) • (T • (Y223 • T′)))  ≈⟨ sym assoc ⟩
      (T • (Λ • T′)) • (T • (Y223 • T′))  ∎

------------------------------------------------------------------------
-- (72), from (67)
--
--     H_[a,b] H_[b,a]  ≈  (−1)_[b] X_[a,b]
--
-- Split the letter over a pair fresh to a and b by (71), turn the
-- second half round by (66), and it is (67) times the letter squared.

module _ (e65 : Eq65) where

  eq72 : ∀ (a b : Fin N) → a ≢ b → hh {₃₊ m} a b b a ≈ zx {₃₊ m} b a b
  eq72 a b ab = begin
    hh {₃₊ m} a b b a                                  ≈⟨ sym (FU.fuse e65 a b c′ d′ b a ab cd′ (≢sym ab)) ⟩
    hh {₃₊ m} a b c′ d′ • hh {₃₊ m} c′ d′ b a          ≈⟨ back (hh {₃₊ m} a b c′ d′) turnPair ⟩
    hh {₃₊ m} a b c′ d′ • hh {₃₊ m} b a c′ d′          ≈⟨ back (hh {₃₊ m} a b c′ d′)
                                                             (eq67 e65 a b c′ d′ ab ac′ ad′ bc′ bd′ cd′) ⟩
    hh {₃₊ m} a b c′ d′ • (hh {₃₊ m} a b c′ d′ • zx {₃₊ m} b a b)
                                                       ≈⟨ sym assoc ⟩
    (hh {₃₊ m} a b c′ d′ • hh {₃₊ m} a b c′ d′) • zx {₃₊ m} b a b
                                                       ≈⟨ front (zx {₃₊ m} b a b)
                                                             (FU.hh-invol e65 a b c′ d′ ab ac′ ad′ bc′ bd′ cd′) ⟩
    ε • zx {₃₊ m} b a b                                ≈⟨ left-unit ⟩
    zx {₃₊ m} b a b                                    ∎
    where
    -- Two indices fresh to a and b.
    module F = AV.Two (AV.avoid (toℕ a ∷ toℕ b ∷ []) (s≤s (s≤s z≤n)))

    lt : ∀ {v : ℕ} → v Data.Nat.< 8 → v Data.Nat.< N
    lt p = ≤-trans p (8≤2^ m)

    c′ d′ : Fin N
    c′ = fin F.p (lt F.p<)
    d′ = fin F.q (lt F.q<)

    off : ∀ {k : ℕ} (x : Fin N) (p : k Data.Nat.< 8) → k ≢ toℕ x → fin k (lt p) ≢ x
    off {k} x p ne e = ne (Eq.trans (Eq.sym (fin-toℕ k (lt p))) (Eq.cong toℕ e))

    ac′ : a ≢ c′
    ac′ = ≢sym (off a F.p< (F.p∉ AV.here))

    bc′ : b ≢ c′
    bc′ = ≢sym (off b F.p< (F.p∉ (AV.there AV.here)))

    ad′ : a ≢ d′
    ad′ = ≢sym (off a F.q< (F.q∉ AV.here))

    bd′ : b ≢ d′
    bd′ = ≢sym (off b F.q< (F.q∉ (AV.there AV.here)))

    cd′ : c′ ≢ d′
    cd′ e = F.p≢q (Eq.trans (Eq.sym (fin-toℕ F.p (lt F.p<)))
                    (Eq.trans (Eq.cong toℕ e) (fin-toℕ F.q (lt F.q<))))

    turnPair : hh {₃₊ m} c′ d′ b a ≈ hh {₃₊ m} b a c′ d′
    turnPair = eq66 e65 c′ d′ b a cd′ (≢sym bc′) (≢sym ac′) (≢sym bd′) (≢sym ad′) (≢sym ab)
