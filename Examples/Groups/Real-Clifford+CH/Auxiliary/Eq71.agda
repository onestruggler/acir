------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 10's (71)
--
--     (H_[a,b] H_[c,d]) (H_[c,d] H_[e,f])  ≈  H_[a,b] H_[e,f]
--
-- for six distinct indices.  The paper's proof, completed:
--
--   * (65) writes both letters around the standard pair;
--   * Corollary A.7 rewrites the first as `T Λ T′` and the second as
--     `(T V) Λ (V′ T′)`, where T is the six-index word of `SixWord`
--     and V is Definition E.1's word at the *numerals* 3, 2, 4, 5 —
--     the point being that both now use the same T;
--   * `T′ T ≈ ε` collapses the middle, leaving `T Λ V Λ V′ T′`;
--   * (65) backwards turns `V Λ V′` into `H_[3,2] H_[4,5]`, and then
--     **(43)** — a rule of Figure 8 — moves the standard pair across it
--     at the cost of a double exchange on either side;
--   * (65) forwards again gives `W Λ W′` with `W = T (X_[0,3]X_[1,2]) V`,
--     whose permutation sends a, b, e, f to 0, 1, 3, 2, so one last
--     appeal to A.7 lands on `Σ_{a,b,e,f} Λ Σ′_{a,b,e,f}`, which is
--     `H_[a,b] H_[e,f]`.
--
-- Every conjugation fact is one call to `A6.conj-at`; the permutations
-- are traced index by index (a ↦ 0 ↦ 3 ↦ 0, b ↦ 1 ↦ 2 ↦ 1,
-- e ↦ 4 ↦ 4 ↦ 3, f ↦ 5 ↦ 5 ↦ 2 for the last one).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq71 (m : ℕ) where

open import Data.Bool using (false ; _xor_)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-inject≤)
open import Data.Nat renaming (_^_ to _^ℕ_ ; _+_ to _+ℕ_) using ()
open import Data.Product using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₃₊)

import Presentation.Base as PB

open import Examples.Groups.Real-Clifford+CH.Semantics hiding (_^_ ; ^-+)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8 ; code)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (hadOp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
  using (_P,_===_ ; r43)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; hhℕ ; xxℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; cat ; nil)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; sp-inj ; idSP ; SP ; ⊙-inverse
       ; swapF ; swapF-a ; swapF-b ; swapF-o)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-refl to ≐-refl′ ; ≐-sym to ≐-sym′
          ; ≐-trans to ≐-trans′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; ⊙-idˡ to ⊙-idˡ′ ; prm≡ to prm≡′ ; sgn≡ to sgn≡′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SPMatrix m
  using (spOp ; spOp-⊙ ; spOp-id ; spOp-cong ; word-op ; word-scale ; ⟦_⟧ʷ
       ; A5-mat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; Xw ; sp-Xw ; hfree-X ; Xw-sp-invol ; xx0312≡
       ; hhℕ-hh ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃
       ; i₀≢i₁ ; i₀≢i₂ ; i₀≢i₃ ; i₁≢i₂ ; i₁≢i₃ ; i₂≢i₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Passes m using (Λ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A6 m
  using (Mpair ; Λ-op ; Λ-scale ; conj-at)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.A7 m using (A7)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq65 m as E65 using ()
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SixWord m as SW using ()
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

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

  -- The numerals 4 and 5 as indices.
  f₄ f₅ : Fin N
  f₄ = fin8 {m} ₄
  f₅ = fin8 {m} ₅

  toℕ-f₄ : toℕ f₄ ≡ 4
  toℕ-f₄ = toℕ-inject≤ ₄ _

  toℕ-f₅ : toℕ f₅ ≡ 5
  toℕ-f₅ = toℕ-inject≤ ₅ _

  dif : ∀ {x y : Fin N} {u v : ℕ} → toℕ x ≡ u → toℕ y ≡ v → u ≢ v → x ≢ y
  dif ex ey ne q = ne (Eq.trans (Eq.sym ex) (Eq.trans (Eq.cong toℕ q) ey))

  -- The six numerals in play are pairwise distinct.
  d₃₂ : i₃ ≢ i₂
  d₃₂ = dif toℕ-i₃ toℕ-i₂ (λ ())

  d₃₄ : i₃ ≢ f₄
  d₃₄ = dif toℕ-i₃ toℕ-f₄ (λ ())

  d₃₅ : i₃ ≢ f₅
  d₃₅ = dif toℕ-i₃ toℕ-f₅ (λ ())

  d₂₄ : i₂ ≢ f₄
  d₂₄ = dif toℕ-i₂ toℕ-f₄ (λ ())

  d₂₅ : i₂ ≢ f₅
  d₂₅ = dif toℕ-i₂ toℕ-f₅ (λ ())

  d₄₅ : f₄ ≢ f₅
  d₄₅ = dif toℕ-f₄ toℕ-f₅ (λ ())

  d₀₄ : i₀ ≢ f₄
  d₀₄ = dif toℕ-i₀ toℕ-f₄ (λ ())

  d₀₅ : i₀ ≢ f₅
  d₀₅ = dif toℕ-i₀ toℕ-f₅ (λ ())

  d₁₄ : i₁ ≢ f₄
  d₁₄ = dif toℕ-i₁ toℕ-f₄ (λ ())

  d₁₅ : i₁ ≢ f₅
  d₁₅ = dif toℕ-i₁ toℕ-f₅ (λ ())

  -- What the double exchange does to the numerals it meets.
  xw : ∀ (t : Fin N) → prm (sp Xw) t ≡ swapF i₁ i₂ (swapF i₀ i₃ t)
  xw = prm≡′ sp-Xw

  xw-0 : prm (sp Xw) i₀ ≡ i₃
  xw-0 = Eq.trans (xw i₀)
           (Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-a i₀ i₃))
                     (swapF-o i₁ i₂ i₃ (≢sym i₁≢i₃) (≢sym i₂≢i₃)))

  xw-1 : prm (sp Xw) i₁ ≡ i₂
  xw-1 = Eq.trans (xw i₁)
           (Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-o i₀ i₃ i₁ (≢sym i₀≢i₁) i₁≢i₃))
                     (swapF-a i₁ i₂))

  xw-4 : prm (sp Xw) f₄ ≡ f₄
  xw-4 = Eq.trans (xw f₄)
           (Eq.trans (Eq.cong (swapF i₁ i₂)
                              (swapF-o i₀ i₃ f₄ (≢sym d₀₄) (≢sym d₃₄)))
                     (swapF-o i₁ i₂ f₄ (≢sym d₁₄) (≢sym d₂₄)))

  xw-5 : prm (sp Xw) f₅ ≡ f₅
  xw-5 = Eq.trans (xw f₅)
           (Eq.trans (Eq.cong (swapF i₁ i₂)
                              (swapF-o i₀ i₃ f₅ (≢sym d₀₅) (≢sym d₃₅)))
                     (swapF-o i₁ i₂ f₅ (≢sym d₁₅) (≢sym d₂₅)))

  xw-sgn : ∀ (t : Fin N) → sgn (sp Xw) t ≡ false
  xw-sgn = sgn≡′ sp-Xw

  -- Words that pair off cancel through the middle.
  peel : ∀ (F A B G : SP) → (A ⊛ B) ≗ idSP → (F ⊛ G) ≗ idSP →
         (F ⊛ A) ⊛ (B ⊛ G) ≗ idSP
  peel F A B G e e′ =
    ≐-trans′ (⊙-assoc′ F A (B ⊛ G))
    (≐-trans′ (⊙-cong′ (≐-refl′ {F})
                (≐-trans′ (≐-trans′ (≐-sym′ (⊙-assoc′ A B G))
                                    (⊙-cong′ e (≐-refl′ {G})))
                          (⊙-idˡ′ G)))
              e′)

  -- The scale and the matrix of `X Λ X′`, separately: composing two
  -- `_~_`s directly is what makes the conversion checker explode.
  cs : ∀ {X X′ : W} → HFreeʷ X → HFreeʷ X′ → proj₁ ⟦ X • (Λ • X′) ⟧ʷ ≡ 2
  cs hX hX′ =
    Eq.cong₂ _+ℕ_ (word-scale hX) (Eq.cong₂ _+ℕ_ Λ-scale (word-scale hX′))

  co : ∀ {X X′ : W} → HFreeʷ X → HFreeʷ X′ →
       proj₂ ⟦ X • (Λ • X′) ⟧ʷ ≐ (spOp (sp X) ⊙ (Mpair ⊙ spOp (sp X′)))
  co hX hX′ = ⊙-cong (word-op hX) (⊙-cong Λ-op (word-op hX′))

  -- The re-bracketing (71) needs, over **abstract** words: with the
  -- telescope spelled out the conversion checker would unfold it at
  -- every step of the chain, and 2 GB is not enough.
  chain : ∀ (t t′ v v′ x h : W) →
          t′ • t ≈ ε →
          Λ • h ≈ x • (h • x) →
          h ≈ v • (Λ • v′) →
          (t • (Λ • t′)) • ((t • v) • (Λ • (v′ • t′)))
          ≈ (t • (x • v)) • (Λ • ((v′ • x) • t′))
  chain t t′ v v′ x h tt e43 ev = begin
    (t • (Λ • t′)) • ((t • v) • (Λ • (v′ • t′)))
      ≈⟨ assoc ⟩
    t • ((Λ • t′) • ((t • v) • (Λ • (v′ • t′))))
      ≈⟨ back t assoc ⟩
    t • (Λ • (t′ • ((t • v) • (Λ • (v′ • t′)))))
      ≈⟨ back t (back Λ (sym assoc)) ⟩
    t • (Λ • ((t′ • (t • v)) • (Λ • (v′ • t′))))
      ≈⟨ back t (back Λ (front (Λ • (v′ • t′)) (sym assoc))) ⟩
    t • (Λ • (((t′ • t) • v) • (Λ • (v′ • t′))))
      ≈⟨ back t (back Λ (front (Λ • (v′ • t′)) (front v tt))) ⟩
    t • (Λ • ((ε • v) • (Λ • (v′ • t′))))
      ≈⟨ back t (back Λ (front (Λ • (v′ • t′)) left-unit)) ⟩
    t • (Λ • (v • (Λ • (v′ • t′))))
      ≈⟨ back t (back Λ (back v (sym assoc))) ⟩
    t • (Λ • (v • ((Λ • v′) • t′)))
      ≈⟨ back t (back Λ (sym assoc)) ⟩
    t • (Λ • ((v • (Λ • v′)) • t′))
      ≈⟨ back t (back Λ (front t′ (sym ev))) ⟩
    t • (Λ • (h • t′))
      ≈⟨ back t (sym assoc) ⟩
    t • ((Λ • h) • t′)
      ≈⟨ back t (front t′ e43) ⟩
    t • ((x • (h • x)) • t′)
      ≈⟨ back t (front t′ (back x (front x ev))) ⟩
    t • ((x • ((v • (Λ • v′)) • x)) • t′)
      ≈⟨ back t (front t′ (back x assoc)) ⟩
    t • ((x • (v • ((Λ • v′) • x))) • t′)
      ≈⟨ back t (front t′ (back x (back v assoc))) ⟩
    t • ((x • (v • (Λ • (v′ • x)))) • t′)
      ≈⟨ back t (front t′ (sym assoc)) ⟩
    t • (((x • v) • (Λ • (v′ • x))) • t′)
      ≈⟨ back t assoc ⟩
    t • ((x • v) • ((Λ • (v′ • x)) • t′))
      ≈⟨ back t (back (x • v) assoc) ⟩
    t • ((x • v) • (Λ • ((v′ • x) • t′)))
      ≈⟨ sym assoc ⟩
    (t • (x • v)) • (Λ • ((v′ • x) • t′)) ∎

  -- Two such words denoting the same pair denote the same operator.
  same : ∀ {X X′ Y Y′ : W} (M : Op n) →
         HFreeʷ X → HFreeʷ X′ → HFreeʷ Y → HFreeʷ Y′ →
         (spOp (sp X) ⊙ (Mpair ⊙ spOp (sp X′))) ≐ M →
         (spOp (sp Y) ⊙ (Mpair ⊙ spOp (sp Y′))) ≐ M →
         ⟦ X • (Λ • X′) ⟧ʷ ~ ⟦ Y • (Λ • Y′) ⟧ʷ
  same M hX hX′ hY hY′ eX eY =
    ~-reflexive (Eq.trans (cs hX hX′) (Eq.sym (cs hY hY′)))
                (≐-trans (co hX hX′) (≐-trans eX (≐-trans (≐-sym eY)
                                                          (≐-sym (co hY hY′)))))

  -- And an inverse pair of Hadamard-free words denotes the identity.
  invʷ : ∀ {X X′ : W} → HFreeʷ X → HFreeʷ X′ → sp X ⊛ sp X′ ≗ idSP →
         ⟦ X • X′ ⟧ʷ ~ ⟦ ε ⟧ʷ
  invʷ {X} {X′} hX hX′ e =
    ~-reflexive (Eq.cong₂ _+ℕ_ (word-scale hX) (word-scale hX′))
      (≐-trans (⊙-cong (word-op hX) (word-op hX′))
        (≐-trans (≐-sym (spOp-⊙ (sp X) (sp X′)))
                 (≐-trans (spOp-cong e) spOp-id)))

------------------------------------------------------------------------
-- Equation (71), for six distinct indices

module _ (e65 : Eq65)
         (a b c d e f : Fin N)
         (ab : a ≢ b) (ac : a ≢ c) (ad : a ≢ d) (ae : a ≢ e) (af : a ≢ f)
         (bc : b ≢ c) (bd : b ≢ d) (be : b ≢ e) (bf : b ≢ f)
         (cd : c ≢ d) (ce : c ≢ e) (cf : c ≢ f)
         (de : d ≢ e) (df : d ≢ f)
         (ef : e ≢ f)
  where

  private
    module T6 = SW.Six a b c d e f ab ac ad ae af bc bd be bf cd ce cf de df ef
    module SV = E65.Tuple i₃ i₂ f₄ f₅ d₃₂ d₃₄ d₃₅ d₂₄ d₂₅ d₄₅
    module S₁ = E65.Tuple a b c d ab ac ad bc bd cd
    module S₂ = E65.Tuple c d e f cd ce cf de df ef
    module S₃ = E65.Tuple a b e f ab ae af be bf ef

    T V T′ V′ : W
    T  = T6.Tw
    T′ = T6.T′w
    V  = SV.Σw
    V′ = SV.Σ′w

    -- Where T sends the six indices, as indices.
    tp : ∀ (x : Fin N) (k : Fin N) → toℕ (prm (sp T) x) ≡ toℕ k →
         prm (sp T) x ≡ k
    tp x k q = toℕ-injective q

    T-0 : prm (sp T) a ≡ i₀
    T-0 = tp a i₀ (Eq.trans T6.T-a (Eq.sym toℕ-i₀))

    T-1 : prm (sp T) b ≡ i₁
    T-1 = tp b i₁ (Eq.trans T6.T-b (Eq.sym toℕ-i₁))

    T-3 : prm (sp T) c ≡ i₃
    T-3 = tp c i₃ (Eq.trans T6.T-c (Eq.sym toℕ-i₃))

    T-2 : prm (sp T) d ≡ i₂
    T-2 = tp d i₂ (Eq.trans T6.T-d (Eq.sym toℕ-i₂))

    T-4 : prm (sp T) e ≡ f₄
    T-4 = tp e f₄ (Eq.trans T6.T-e (Eq.sym toℕ-f₄))

    T-5 : prm (sp T) f ≡ f₅
    T-5 = tp f f₅ (Eq.trans T6.T-f (Eq.sym toℕ-f₅))

    -- And where V sends the four numerals.
    V-3 : prm (sp V) i₃ ≡ i₀
    V-3 = toℕ-injective (Eq.trans SV.prm-Σ-a (Eq.sym toℕ-i₀))

    V-2 : prm (sp V) i₂ ≡ i₁
    V-2 = toℕ-injective (Eq.trans SV.prm-Σ-b (Eq.sym toℕ-i₁))

    V-4 : prm (sp V) f₄ ≡ i₃
    V-4 = toℕ-injective (Eq.trans SV.prm-Σ-c (Eq.sym toℕ-i₃))

    V-5 : prm (sp V) f₅ ≡ i₂
    V-5 = toℕ-injective (Eq.trans SV.prm-Σ-d (Eq.sym toℕ-i₂))

    ------------------------------------------------------------------
    -- The three words that conjugate the standard pair

    TV V′T′ Wd Wd′ : W
    TV   = T • V
    V′T′ = V′ • T′
    Wd   = T • (Xw • V)
    Wd′  = (V′ • Xw) • T′

    hTV : HFreeʷ TV
    hTV = cat T6.hfree-T SV.hfree-Σ

    hV′T′ : HFreeʷ V′T′
    hV′T′ = cat SV.hfree-Σ′ T6.hfree-T′

    hW : HFreeʷ Wd
    hW = cat T6.hfree-T (cat hfree-X SV.hfree-Σ)

    hW′ : HFreeʷ Wd′
    hW′ = cat (cat SV.hfree-Σ′ hfree-X) T6.hfree-T′

    inv-TV : sp TV ⊛ sp V′T′ ≗ idSP
    inv-TV = peel (sp T) (sp V) (sp V′) (sp T′) SV.Σ-inv T6.T-inv

    inv-W : sp Wd ⊛ sp Wd′ ≗ idSP
    inv-W = peel (sp T) (sp Xw ⊛ sp V) (sp V′ ⊛ sp Xw) (sp T′) middle T6.T-inv
      where
      middle : (sp Xw ⊛ sp V) ⊛ (sp V′ ⊛ sp Xw) ≗ idSP
      middle = peel (sp Xw) (sp V) (sp V′) (sp Xw) SV.Σ-inv Xw-sp-invol

    -- T carries a, b, c, d to 0, 1, 3, 2 …
    cT : (spOp (sp T) ⊙ (Mpair ⊙ spOp (sp T′)))
         ≐ (hadOp (code n a) (code n b) ⊙ hadOp (code n c) (code n d))
    cT = conj-at T T′ (sp-inj T′) T6.T-inv a b c d
           T-0 T-1 T-3 T-2 T6.T-sa T6.T-sb T6.T-sc T6.T-sd

    -- … T then V carries c, d, e, f there …
    cTV : (spOp (sp TV) ⊙ (Mpair ⊙ spOp (sp V′T′)))
          ≐ (hadOp (code n c) (code n d) ⊙ hadOp (code n e) (code n f))
    cTV = conj-at TV V′T′ (sp-inj V′T′) inv-TV c d e f
            (Eq.trans (Eq.cong (prm (sp V)) T-3) V-3)
            (Eq.trans (Eq.cong (prm (sp V)) T-2) V-2)
            (Eq.trans (Eq.cong (prm (sp V)) T-4) V-4)
            (Eq.trans (Eq.cong (prm (sp V)) T-5) V-5)
            (sg T6.T-sc T-3 SV.sgn-Σ-a) (sg T6.T-sd T-2 SV.sgn-Σ-b)
            (sg T6.T-se T-4 SV.sgn-Σ-c) (sg T6.T-sf T-5 SV.sgn-Σ-d)
      where
      sg : ∀ {x k : Fin N} → sgn (sp T) x ≡ false → prm (sp T) x ≡ k →
           sgn (sp V) k ≡ false → sgn (sp TV) x ≡ false
      sg {x} {k} t p v =
        Eq.trans (Eq.cong₂ _xor_ t (Eq.trans (Eq.cong (sgn (sp V)) p) v)) Eq.refl

    -- … and T, the double exchange and V together carry a, b, e, f.
    cW : (spOp (sp Wd) ⊙ (Mpair ⊙ spOp (sp Wd′)))
         ≐ (hadOp (code n a) (code n b) ⊙ hadOp (code n e) (code n f))
    cW = conj-at Wd Wd′ (sp-inj Wd′) inv-W a b e f
           (mv T-0 xw-0 V-3) (mv T-1 xw-1 V-2)
           (mv T-4 xw-4 V-4) (mv T-5 xw-5 V-5)
           (sg T6.T-sa T-0 xw-0 SV.sgn-Σ-a) (sg T6.T-sb T-1 xw-1 SV.sgn-Σ-b)
           (sg T6.T-se T-4 xw-4 SV.sgn-Σ-c) (sg T6.T-sf T-5 xw-5 SV.sgn-Σ-d)
      where
      mv : ∀ {x u v w : Fin N} → prm (sp T) x ≡ u → prm (sp Xw) u ≡ v →
           prm (sp V) v ≡ w → prm (sp Wd) x ≡ w
      mv {x} p q r =
        Eq.trans (Eq.cong (λ z → prm (sp V) (prm (sp Xw) z)) p)
                 (Eq.trans (Eq.cong (prm (sp V)) q) r)

      sg : ∀ {x u v : Fin N} → sgn (sp T) x ≡ false → prm (sp T) x ≡ u →
           prm (sp Xw) u ≡ v → sgn (sp V) v ≡ false → sgn (sp Wd) x ≡ false
      sg {x} {u} {v} t p q s =
        Eq.trans (Eq.cong₂ _xor_ t
                   (Eq.cong₂ _xor_ (xw-sgn (prm (sp T) x))
                     (Eq.trans (Eq.cong (λ z → sgn (sp V) (prm (sp Xw) z)) p)
                               (Eq.trans (Eq.cong (sgn (sp V)) q) s))))
                 Eq.refl

    ------------------------------------------------------------------
    -- The three joins
    --
    -- Each is (65) at one tuple, followed — or preceded — by Corollary
    -- A.7 between Definition E.1's word there and the word built out
    -- of T, the double exchange and V.  A.7 needs the two words to be
    -- inverse and the two readings to agree, which is what the
    -- conjugation facts above say.
    --
    -- **Every argument of `A7` is named, with its own type.**  Inlined,
    -- the `same` and `invʷ` applications leave their own implicit words
    -- as metavariables to be solved against A.7's, and unifying two
    -- unsolved readings of a nine-letter word is what makes the
    -- conversion checker expand them — 600 s was not enough.  Written
    -- as definitions with their types given, the same three lines take
    -- a second.

    -- H_[a,b] H_[c,d], written around the standard pair by T.
    sem₁ : ⟦ S₁.Σw • (Λ • S₁.Σ′w) ⟧ʷ ~ ⟦ T • (Λ • T′) ⟧ʷ
    sem₁ = same (hadOp (code n a) (code n b) ⊙ hadOp (code n c) (code n d))
                S₁.hfree-Σ S₁.hfree-Σ′ T6.hfree-T T6.hfree-T′ S₁.Σ-conj cT

    invT : ⟦ T • T′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    invT = invʷ T6.hfree-T T6.hfree-T′ T6.T-inv

    j₁ : S₁.Σw • (Λ • S₁.Σ′w) ≈ T • (Λ • T′)
    j₁ = A7 S₁.hfree-Σ S₁.hfree-Σ′ T6.hfree-T T6.hfree-T′ S₁.ΣΣ′ invT sem₁

    step₁ : hh {₃₊ m} a b c d ≈ T • (Λ • T′)
    step₁ = trans (e65 a b c d ab ac ad bc bd cd) j₁

    -- H_[c,d] H_[e,f], by the same T followed by V.
    sem₂ : ⟦ S₂.Σw • (Λ • S₂.Σ′w) ⟧ʷ ~ ⟦ TV • (Λ • V′T′) ⟧ʷ
    sem₂ = same (hadOp (code n c) (code n d) ⊙ hadOp (code n e) (code n f))
                S₂.hfree-Σ S₂.hfree-Σ′ hTV hV′T′ S₂.Σ-conj cTV

    invTV : ⟦ TV • V′T′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    invTV = invʷ hTV hV′T′ inv-TV

    j₂ : S₂.Σw • (Λ • S₂.Σ′w) ≈ TV • (Λ • V′T′)
    j₂ = A7 S₂.hfree-Σ S₂.hfree-Σ′ hTV hV′T′ S₂.ΣΣ′ invTV sem₂

    step₂ : hh {₃₊ m} c d e f ≈ TV • (Λ • V′T′)
    step₂ = trans (e65 c d e f cd ce cf de df ef) j₂

    -- And what the chain lands on is H_[a,b] H_[e,f].
    sem₃ : ⟦ Wd • (Λ • Wd′) ⟧ʷ ~ ⟦ S₃.Σw • (Λ • S₃.Σ′w) ⟧ʷ
    sem₃ = same (hadOp (code n a) (code n b) ⊙ hadOp (code n e) (code n f))
                hW hW′ S₃.hfree-Σ S₃.hfree-Σ′ cW S₃.Σ-conj

    invWd : ⟦ Wd • Wd′ ⟧ʷ ~ ⟦ ε ⟧ʷ
    invWd = invʷ hW hW′ inv-W

    j₃ : Wd • (Λ • Wd′) ≈ S₃.Σw • (Λ • S₃.Σ′w)
    j₃ = A7 hW hW′ S₃.hfree-Σ S₃.hfree-Σ′ invWd S₃.ΣΣ′ sem₃

    step₃ : Wd • (Λ • Wd′) ≈ hh {₃₊ m} a b e f
    step₃ = trans j₃ (sym (e65 a b e f ab ae af be bf ef))

    ------------------------------------------------------------------
    -- What the chain consumes

    -- The six-index word cancels in the middle (Corollary A.5, the two
    -- signed permutations being inverse).
    T′-inv : sp T′ ⊛ sp T ≗ idSP
    T′-inv = ⊙-inverse (sp T) (sp T′) (sp-inj T′) T6.T-inv

    invT′ : ⟦ T′ • T ⟧ʷ ~ ⟦ ε ⟧ʷ
    invT′ = invʷ T6.hfree-T′ T6.hfree-T T′-inv

    T′T : T′ • T ≈ ε
    T′T = A5-mat (cat T6.hfree-T′ T6.hfree-T) nil invT′

    -- The letter Equation (43) moves the standard pair across.
    H32 : W
    H32 = hhℕ {₃₊ m} 3 2 4 5

    h32≡ : H32 ≡ hh {₃₊ m} i₃ i₂ f₄ f₅
    h32≡ =
      Eq.trans (Eq.cong₂ (λ x y → hhℕ {₃₊ m} x y 4 5)
                         (Eq.sym toℕ-i₃) (Eq.sym toℕ-i₂))
      (Eq.trans (Eq.cong₂ (λ x y → hhℕ {₃₊ m} (toℕ i₃) (toℕ i₂) x y)
                          (Eq.sym toℕ-f₄) (Eq.sym toℕ-f₅))
                (hhℕ-hh i₃ i₂ f₄ f₅))

    -- Equation (43) itself, at the decided numerals.
    e43 : Λ • H32 ≈ Xw • (H32 • Xw)
    e43 = Eq.subst (λ x → Λ • H32 ≈ x • (H32 • x)) xx0312≡ (axiom r43)

    -- And (65) at (3 , 2 , 4 , 5).
    eV : H32 ≈ V • (Λ • V′)
    eV = trans (refl≡ h32≡) (e65 i₃ i₂ f₄ f₅ d₃₂ d₃₄ d₃₅ d₂₄ d₂₅ d₄₅)

  ----------------------------------------------------------------------
  -- Equation (71)

  eq71 : hh {₃₊ m} a b c d • hh {₃₊ m} c d e f ≈ hh {₃₊ m} a b e f
  eq71 = trans (cong step₁ step₂)
               (trans (chain T T′ V V′ Xw H32 T′T e43 eV) step₃)
