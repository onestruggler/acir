------------------------------------------------------------------------
-- Presentations of groups
--
-- Words that commute with the Hadamard pair
--
-- What Corollary A.7 consumes is not the *shape* Lemma A.6 gives a
-- commuting word but the consequence: that such a word can be carried
-- across H_[0,1] H_[3,2] inside a derivation.  This module collects
-- the words for which Figure 8 says so outright, and closes them under
-- products and under equivalence.
--
--   * a letter on a consecutive pair at index 4 or above, by (38);
--   * the sign pair on 0 and 1, by (39);
--   * the double exchange X_[0,3] X_[1,2], by (44);
--   * and the sign pair on 3 and 2, which is the sign pair on 0 and 1
--     conjugated by that double exchange.
--
-- Those are exactly the generators of the form A.6 gives, which is
-- why it is stated over them.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Passes (m : ℕ) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n)
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat using (zero ; suc ; _+_ ; _<_ ; _≤_ ; _∸_ ; _<?_ ; z≤n ; s≤s)
  renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties
  using (≤-refl ; ≤-trans ; <-trans ; <⇒≤ ; ≮⇒≥ ; ≤-antisym ; <-irrefl ; <-cmp
       ; n<1+n ; n≤1+n ; +-identityʳ ; +-suc)
open import Data.Bool using (Bool ; true ; false ; not ; _xor_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.Definitions using (tri< ; tri≈ ; tri>)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (zz ; zx ; zxℕ ; zzℕ ; xxℕ ; hhℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (sx ; sx-zx ; fin ; fin-toℕ ; runFrom ; runAt ; permFrom ; permPart
       ; Lehmer ; runAt≡ ; run-bounds ; shift-Ni
       ; signOf ; NF ; Normal ; HFreeʷ ; Reduced ; existence)
  renaming (gen to hgen ; nil to hnil ; cat to hcat)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m
  using (High ; nil ; cons ; module NFHigh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (sp ; sgn ; prm ; prm≡ ; sgn≡ ; sound ; δ ; δ-here ; δ-≢ ; swapF
       ; swapF-a ; swapF-b ; swapF-o)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m
  using (i₀ ; i₁ ; i₂ ; i₃ ; Xw ; Z₀₁ ; Z₃₂ ; sp-Xw ; conj-≈
       ; zz01≡ ; xx0312≡ ; Xw-invol ; Z₀₁-invol ; Z₃₂-invol
       ; hfree-X ; hfree-Z₀₁ ; hfree-Z₃₂
       ; toℕ-i₀ ; toℕ-i₁ ; toℕ-i₂ ; toℕ-i₃
       ; i₀≢i₁ ; i₀≢i₂ ; i₀≢i₃ ; i₁≢i₂ ; i₁≢i₃ ; i₂≢i₃)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8Free using (free⇒full-≈)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m
  using (next ; next-Succ ; ∸suc ; pred≤pred ; 0<∸)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

-- The Hadamard pair the whole theory is written around.
Λ : W
Λ = hhℕ {₃₊ m} 0 1 3 2

------------------------------------------------------------------------
-- Passing it

refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
refl≡ Eq.refl = refl

Passes : W → Set
Passes u = u • Λ ≈ Λ • u

passes-ε : Passes ε
passes-ε = trans left-unit (sym right-unit)

passes-• : ∀ {u v : W} → Passes u → Passes v → Passes (u • v)
passes-• {u} {v} pu pv = begin
  (u • v) • Λ   ≈⟨ assoc ⟩
  u • (v • Λ)   ≈⟨ back _ pv ⟩
  u • (Λ • v)   ≈⟨ sym assoc ⟩
  (u • Λ) • v   ≈⟨ front _ pu ⟩
  (Λ • u) • v   ≈⟨ assoc ⟩
  Λ • (u • v)  ∎

passes-≈ : ∀ {u v : W} → u ≈ v → Passes v → Passes u
passes-≈ e p = trans (front _ e) (trans p (back _ (sym e)))

------------------------------------------------------------------------
-- The generators that pass it

-- A letter on a consecutive pair, at index 4 or above: (38).
passes-sx : ∀ (j : ℕ) (q : j < N) (p : suc j < N) → 4 ≤ j → Passes (sx j)
passes-sx j q p 4≤j =
  Eq.subst (λ w → w • Λ ≈ Λ • w) (Eq.sym (sx-zx j q p))
           (axiom (r38 (fin j q) (fin (suc j) p) succ bound))
  where
  succ : Succ (fin j q) (fin (suc j) p)
  succ = Eq.trans (fin-toℕ (suc j) p) (Eq.cong suc (Eq.sym (fin-toℕ j q)))

  bound : 4 ≤ toℕ (fin j q)
  bound = Eq.subst (4 ≤_) (Eq.sym (fin-toℕ j q)) 4≤j

-- The sign pair on the indices 0 and 1: (39).
passes-zz01 : Passes (zzℕ {₃₊ m} 0 1)
passes-zz01 = axiom r39

-- The double exchange: (44).
passes-xx : Passes (xxℕ {₃₊ m} 0 3 1 2)
passes-xx = axiom r44

-- A whole product of letters at index 4 or above.
data Ok₄ : List ℕ → Set where
  nil  : Ok₄ []
  cons : ∀ {j l} → 4 ≤ j → j < N → suc j < N → Ok₄ l → Ok₄ (j ∷ l)

sxs : List ℕ → W
sxs []      = ε
sxs (j ∷ l) = sx j • sxs l

passes-sxs : ∀ (l : List ℕ) → Ok₄ l → Passes (sxs l)
passes-sxs []      nil                 = passes-ε
passes-sxs (j ∷ l) (cons 4≤j q p ok)   =
  passes-• (passes-sx j q p 4≤j) (passes-sxs l ok)

------------------------------------------------------------------------
-- A permutation part over the high indices passes it
--
-- Every letter of a run is at or above the run's start, so a run that
-- starts at 4 or above passes the pair letter by letter; and `low-runs`
-- says that in a normal form of a word fixing the low indices every
-- other run is empty.

private
  Bnd : ℕ → ℕ → Set
  Bnd v L = ∀ e → e < L → suc (v + e) < N

  bnd-hd : ∀ {v L} → Bnd v (suc L) → suc v < N
  bnd-hd {v} b = Eq.subst (λ z → suc z < N) (+-identityʳ v) (b 0 (s≤s z≤n))

  bnd-tl : ∀ {v L} → Bnd v (suc L) → Bnd (suc v) L
  bnd-tl {v} b e lt = Eq.subst (λ z → suc z < N) (+-suc v e) (b (suc e) (s≤s lt))

passes-runFrom : ∀ (v L : ℕ) → Bnd v L → 4 ≤ v → Passes (runFrom v L)
passes-runFrom v zero    b 4v = passes-ε
passes-runFrom v (suc L) b 4v =
  passes-• (passes-sx v (<-trans (n<1+n v) (bnd-hd b)) (bnd-hd b) 4v)
           (passes-runFrom (suc v) L (bnd-tl b) (≤-trans 4v (n≤1+n v)))

passes-runAt : ∀ (i k v : ℕ) → 1 ≤ i → N ∸ i ≡ k → v ≤ k →
               (N ∸ i ∸ v ≡ 0) ⊎ (4 ≤ v) → Passes (runAt i v)
passes-runAt i k v 1i Ni vk (inj₁ e) =
  Eq.subst Passes (Eq.sym (Eq.cong (runFrom v) e)) passes-ε
passes-runAt i k v 1i Ni vk (inj₂ 4v) =
  Eq.subst Passes (Eq.sym (runAt≡ i v Ni))
           (passes-runFrom v (k ∸ v) (run-bounds i k v 1i Ni vk) 4v)

passes-permFrom : ∀ (i k : ℕ) (d : ℕ → ℕ) → 1 ≤ i → N ∸ i ≡ k → Lehmer d →
                  (∀ (j : ℕ) → i ≤ j → d j < 4 → N ∸ j ∸ d j ≡ 0) →
                  Passes (permFrom i k d)
passes-permFrom i zero    d 1i Ni L low = passes-ε
passes-permFrom i (suc k) d 1i Ni L low =
  passes-• (passes-runAt i (suc k) (d i) 1i Ni (Eq.subst (d i ≤_) Ni (L i))
                         (choice (d i <? 4)))
           (passes-permFrom (suc i) k d (s≤s z≤n) (shift-Ni i k Ni) L
                            (λ j ij → low j (≤-trans (n≤1+n i) ij)))
  where
  choice : Dec (d i < 4) → (N ∸ i ∸ d i ≡ 0) ⊎ (4 ≤ d i)
  choice (yes p) = inj₁ (low i ≤-refl p)
  choice (no ¬p) = inj₂ (≮⇒≥ ¬p)

------------------------------------------------------------------------
-- A sign pair on two high indices passes it
--
-- (22) cuts the pair into consecutive ones, all of them still high,
-- and a consecutive one is a letter squared, (23).

private
  -- The sign pair on one consecutive pair, at 4 or above.
  passes-zz-step : ∀ (a a′ : Fin N) → Succ a a′ → 4 ≤ toℕ a → Passes (zz a a′)
  passes-zz-step a a′ succ 4a =
    passes-≈ (axiom (r23 a a′ succ))
             (passes-• (passes-zx a a′ succ 4a) (passes-zx a a′ succ 4a))
    where
    passes-zx : ∀ (a a′ : Fin N) → Succ a a′ → 4 ≤ toℕ a → Passes (zx a a a′)
    passes-zx a a′ s 4a = axiom (r38 a a′ s 4a)

  -- And on any pair above it, by induction on the gap.
  passes-zz-up : ∀ (k : ℕ) (a b : Fin N) → toℕ a < toℕ b → toℕ b ∸ toℕ a ≤ k →
                 4 ≤ toℕ a → Passes (zz a b)
  passes-zz-up zero a b lt fu 4a = ⊥-elim (<-irrefl Eq.refl (≤-trans (0<∸ lt) fu))
  passes-zz-up (suc k) a b lt fu 4a with suc (toℕ a) <? toℕ b
  ... | no ¬p = passes-zz-step a b (≤-antisym (≮⇒≥ ¬p) lt) 4a
  ... | yes p =
    passes-≈ (sym (axiom (r22 a a′ b)))
             (passes-• (passes-zz-step a a′ sa 4a)
                       (passes-zz-up k a′ b lt′ fu′ (≤-trans 4a (<⇒≤ (Eq.subst (toℕ a <_) (Eq.sym sa) (n<1+n (toℕ a)))))))
    where
    pa : suc (toℕ a) < N
    pa = <-trans p (toℕ<n b)

    a′ = next a pa
    sa : Succ a a′
    sa = next-Succ a pa

    lt′ : toℕ a′ < toℕ b
    lt′ = Eq.subst (_< toℕ b) (Eq.sym sa) p

    fu′ : toℕ b ∸ toℕ a′ ≤ k
    fu′ = Eq.subst (λ z → toℕ b ∸ z ≤ k) (Eq.sym sa)
            (Eq.subst (_≤ k) (Eq.sym (∸suc (toℕ b) (toℕ a))) (pred≤pred fu))

passes-zz : ∀ (a b : Fin N) → 4 ≤ toℕ a → 4 ≤ toℕ b → Passes (zz a b)
passes-zz a b 4a 4b with <-cmp (toℕ a) (toℕ b)
... | tri< lt _ _ = passes-zz-up (toℕ b ∸ toℕ a) a b lt ≤-refl 4a
... | tri≈ _ e _  =
  passes-≈ (trans (refl≡ (Eq.cong (zz a) (Eq.sym (toℕ-injective e)))) (axiom (r20 a)))
           passes-ε
... | tri> _ _ gt =
  passes-≈ (axiom (r21 a b)) (passes-zz-up (toℕ a ∸ toℕ b) b a gt ≤-refl 4b)

------------------------------------------------------------------------
-- A Hadamard-free word over the high indices passes it
--
-- The sign part is a product of sign pairs, all of them high; the
-- permutation part is the runs, all starting high; and a word is its
-- normal form.  That is Lemma A.6's conclusion in the form Corollary
-- A.7 wants it: not the *shape* of a commuting word but that it can be
-- carried across the pair.

passes-signOf : ∀ (l : List (Fin N)) → High l → Passes (signOf l)
passes-signOf []           nil                   = passes-ε
passes-signOf (a ∷ [])     (cons _ nil)          = passes-ε
passes-signOf (a ∷ b ∷ l) (cons 4a (cons 4b h)) =
  passes-• (passes-zz a b 4a 4b) (passes-signOf l h)

passes-NF : ∀ (l : List (Fin N)) (d : ℕ → ℕ) (nm : Normal l d) →
            (∀ (t : Fin N) → toℕ t < 4 → prm (sp (NF l d)) t ≡ t) →
            (∀ (t : Fin N) → toℕ t < 4 → sgn (sp (NF l d)) t ≡ false) →
            Passes (NF l d)
passes-NF l d nm fix sg0 =
  passes-• (passes-signOf l H.nf-high)
           (passes-permFrom 1 (N ∸ 1) d ≤-refl Eq.refl (Normal.lehmer nm) H.nf-low-runs)
  where
  module H = NFHigh l d nm fix sg0

-- And so does any Hadamard-free word that neither moves nor signs an
-- index below 4 — which, by `Commutant`, is what commuting with the
-- pair comes to.
passes-low : ∀ {w : W} → HFreeʷ w →
             (∀ (t : Fin N) → toℕ t < 4 → prm (sp w) t ≡ t) →
             (∀ (t : Fin N) → toℕ t < 4 → sgn (sp w) t ≡ false) →
             Passes w
passes-low {w} h fix sg0 =
  passes-≈ (free⇒full-≈ (Reduced.law r))
           (passes-NF (Reduced.lis r) (Reduced.code r) (Reduced.norm r) fix′ sg0′)
  where
  r = existence h
  e = sound (Reduced.law r)

  fix′ : ∀ (t : Fin N) → toℕ t < 4 →
         prm (sp (NF (Reduced.lis r) (Reduced.code r))) t ≡ t
  fix′ t lt = Eq.trans (Eq.sym (prm≡ e t)) (fix t lt)

  sg0′ : ∀ (t : Fin N) → toℕ t < 4 →
         sgn (sp (NF (Reduced.lis r) (Reduced.code r))) t ≡ false
  sg0′ t lt = Eq.trans (Eq.sym (sgn≡ e t)) (sg0 t lt)

------------------------------------------------------------------------
-- The three special generators pass
--
-- (39) and (44) are stated over numerals; `LowGens` decides those
-- indices, and gets the third generator by conjugating the first by the
-- second.

passes-Z₀₁ : Passes Z₀₁
passes-Z₀₁ = Eq.subst Passes zz01≡ passes-zz01

passes-Xw : Passes Xw
passes-Xw = Eq.subst Passes xx0312≡ passes-xx

passes-Z₃₂ : Passes Z₃₂
passes-Z₃₂ =
  passes-≈ (sym conj-≈) (passes-• passes-Xw (passes-• passes-Z₀₁ passes-Xw))

-- A factor that passes and is its own inverse may be divided out.
passes-factor : ∀ {g w : W} → g • g ≈ ε → Passes g → Passes (g • w) → Passes w
passes-factor {g} {w} inv pg pgw = passes-≈ split (passes-• pg pgw)
  where
  split : w ≈ g • (g • w)
  split = begin
    w            ≈⟨ sym left-unit ⟩
    ε • w        ≈⟨ front _ (sym inv) ⟩
    (g • g) • w  ≈⟨ assoc ⟩
    g • (g • w) ∎

------------------------------------------------------------------------
-- Lemma A.6
--
-- By `Commutant`, a Hadamard-free word commuting with the pair has a
-- signed permutation that either fixes both low pairs or exchanges
-- both, and whose signs agree along each pair.  Each of those four
-- possibilities is one of the special generators times a word that
-- neither moves nor signs a low index, so each passes.

private
  ≢sym : ∀ {a b : Fin N} → a ≢ b → b ≢ a
  ≢sym ne e = ne (Eq.sym e)

-- Below 4 there are exactly the four indices the pair is written on.
low-four : ∀ (t : Fin N) → toℕ t < 4 →
           t ≡ i₀ ⊎ t ≡ i₁ ⊎ t ≡ i₂ ⊎ t ≡ i₃
low-four t lt = go (toℕ t) Eq.refl lt
  where
  go : ∀ (k : ℕ) → toℕ t ≡ k → k < 4 →
       t ≡ i₀ ⊎ t ≡ i₁ ⊎ t ≡ i₂ ⊎ t ≡ i₃
  go zero                            e _ =
    inj₁ (toℕ-injective (Eq.trans e (Eq.sym toℕ-i₀)))
  go (suc zero)                      e _ =
    inj₂ (inj₁ (toℕ-injective (Eq.trans e (Eq.sym toℕ-i₁))))
  go (suc (suc zero))                e _ =
    inj₂ (inj₂ (inj₁ (toℕ-injective (Eq.trans e (Eq.sym toℕ-i₂)))))
  go (suc (suc (suc zero)))          e _ =
    inj₂ (inj₂ (inj₂ (toℕ-injective (Eq.trans e (Eq.sym toℕ-i₃)))))
  go (suc (suc (suc (suc _))))       _ (s≤s (s≤s (s≤s (s≤s ()))))

four-of : ∀ {P : Fin N → Set} → P i₀ → P i₁ → P i₂ → P i₃ →
          ∀ (t : Fin N) → toℕ t < 4 → P t
four-of p₀ p₁ p₂ p₃ t lt with low-four t lt
... | inj₁ Eq.refl                = p₀
... | inj₂ (inj₁ Eq.refl)         = p₁
... | inj₂ (inj₂ (inj₁ Eq.refl))  = p₂
... | inj₂ (inj₂ (inj₂ Eq.refl))  = p₃

private
  -- The sign a `zz` letter contributes, read off the deltas.
  sgn-zz : ∀ (a b : Fin N) (w : W) (t : Fin N) →
           sgn (sp (zz {₃₊ m} a b • w)) t ≡ (δ a t xor δ b t) xor sgn (sp w) t
  sgn-zz a b w t = Eq.refl

  zz-hit : ∀ {a b t : Fin N} (w : W) → δ a t ≡ true → δ b t ≡ false →
           sgn (sp (zz {₃₊ m} a b • w)) t ≡ not (sgn (sp w) t)
  zz-hit {a} {b} {t} w da db = Eq.trans (sgn-zz a b w t) (step da db)
    where
    step : δ a t ≡ true → δ b t ≡ false →
           (δ a t xor δ b t) xor sgn (sp w) t ≡ not (sgn (sp w) t)
    step da db rewrite da | db = Eq.refl

  zz-hit′ : ∀ {a b t : Fin N} (w : W) → δ a t ≡ false → δ b t ≡ true →
            sgn (sp (zz {₃₊ m} a b • w)) t ≡ not (sgn (sp w) t)
  zz-hit′ {a} {b} {t} w da db = Eq.trans (sgn-zz a b w t) (step da db)
    where
    step : δ a t ≡ false → δ b t ≡ true →
           (δ a t xor δ b t) xor sgn (sp w) t ≡ not (sgn (sp w) t)
    step da db rewrite da | db = Eq.refl

  zz-miss : ∀ {a b t : Fin N} (w : W) → δ a t ≡ false → δ b t ≡ false →
            sgn (sp (zz {₃₊ m} a b • w)) t ≡ sgn (sp w) t
  zz-miss {a} {b} {t} w da db = Eq.trans (sgn-zz a b w t) (step da db)
    where
    step : δ a t ≡ false → δ b t ≡ false →
           (δ a t xor δ b t) xor sgn (sp w) t ≡ sgn (sp w) t
    step da db rewrite da | db = Eq.refl

  -- And it moves nothing.
  prm-zz : ∀ (a b : Fin N) (w : W) (t : Fin N) →
           prm (sp (zz {₃₊ m} a b • w)) t ≡ prm (sp w) t
  prm-zz a b w t = Eq.refl

  not-true : ∀ {b : Bool} → b ≡ true → not b ≡ false
  not-true Eq.refl = Eq.refl

-- All four low signs already cancelled.
private
  passes-zeroed : ∀ {w : W} → HFreeʷ w →
                  (∀ (t : Fin N) → toℕ t < 4 → prm (sp w) t ≡ t) →
                  sgn (sp w) i₀ ≡ false → sgn (sp w) i₁ ≡ false →
                  sgn (sp w) i₂ ≡ false → sgn (sp w) i₃ ≡ false →
                  Passes w
  passes-zeroed {w} h fix e₀ e₁ e₂ e₃ =
    passes-low h fix (four-of {λ t → sgn (sp w) t ≡ false} e₀ e₁ e₂ e₃)

  -- The sign pair on 3 and 2, divided out if it is there.
  passes-z32 : ∀ {w : W} → HFreeʷ w →
               (∀ (t : Fin N) → toℕ t < 4 → prm (sp w) t ≡ t) →
               sgn (sp w) i₀ ≡ false → sgn (sp w) i₁ ≡ false →
               sgn (sp w) i₃ ≡ sgn (sp w) i₂ →
               Passes w
  passes-z32 {w} h fix e₀ e₁ s₃ = go (sgn (sp w) i₃) Eq.refl
    where
    go : ∀ (b : Bool) → sgn (sp w) i₃ ≡ b → Passes w
    go false e₃ = passes-zeroed h fix e₀ e₁ (Eq.trans (Eq.sym s₃) e₃) e₃
    go true  e₃ =
      passes-factor Z₃₂-invol passes-Z₃₂
        (passes-zeroed (hcat hfree-Z₃₂ h) fix z₀ z₁ z₂ z₃)
      where
      z₀ : sgn (sp (Z₃₂ • w)) i₀ ≡ false
      z₀ = Eq.trans (zz-miss w (δ-≢ i₃ i₀ i₀≢i₃) (δ-≢ i₂ i₀ i₀≢i₂)) e₀

      z₁ : sgn (sp (Z₃₂ • w)) i₁ ≡ false
      z₁ = Eq.trans (zz-miss w (δ-≢ i₃ i₁ i₁≢i₃) (δ-≢ i₂ i₁ i₁≢i₂)) e₁

      z₂ : sgn (sp (Z₃₂ • w)) i₂ ≡ false
      z₂ = Eq.trans (zz-hit′ w (δ-≢ i₃ i₂ i₂≢i₃) (δ-here i₂))
                    (not-true (Eq.trans (Eq.sym s₃) e₃))

      z₃ : sgn (sp (Z₃₂ • w)) i₃ ≡ false
      z₃ = Eq.trans (zz-hit w (δ-here i₃) (δ-≢ i₂ i₃ (≢sym i₂≢i₃)))
                    (not-true e₃)

-- The permutation fixes the four low indices: divide out whichever
-- sign pairs remain and appeal to `passes-low`.
passes-fixed : ∀ {w : W} → HFreeʷ w →
               (∀ (t : Fin N) → toℕ t < 4 → prm (sp w) t ≡ t) →
               sgn (sp w) i₀ ≡ sgn (sp w) i₁ →
               sgn (sp w) i₃ ≡ sgn (sp w) i₂ →
               Passes w
passes-fixed {w} h fix s₀ s₃ = go (sgn (sp w) i₀) Eq.refl
  where
  go : ∀ (b : Bool) → sgn (sp w) i₀ ≡ b → Passes w
  go false e₀ = passes-z32 h fix e₀ (Eq.trans (Eq.sym s₀) e₀) s₃
  go true  e₀ =
    passes-factor Z₀₁-invol passes-Z₀₁
      (passes-z32 (hcat hfree-Z₀₁ h) fix z₀ z₁ s₃′)
    where
    z₀ : sgn (sp (Z₀₁ • w)) i₀ ≡ false
    z₀ = Eq.trans (zz-hit w (δ-here i₀) (δ-≢ i₁ i₀ i₀≢i₁)) (not-true e₀)

    z₁ : sgn (sp (Z₀₁ • w)) i₁ ≡ false
    z₁ = Eq.trans (zz-hit′ w (δ-≢ i₀ i₁ (≢sym i₀≢i₁)) (δ-here i₁))
                  (not-true (Eq.trans (Eq.sym s₀) e₀))

    s₃′ : sgn (sp (Z₀₁ • w)) i₃ ≡ sgn (sp (Z₀₁ • w)) i₂
    s₃′ =
      Eq.trans (zz-miss w (δ-≢ i₀ i₃ (≢sym i₀≢i₃)) (δ-≢ i₁ i₃ (≢sym i₁≢i₃)))
      (Eq.trans s₃
                (Eq.sym (zz-miss w (δ-≢ i₀ i₂ (≢sym i₀≢i₂))
                                   (δ-≢ i₁ i₂ (≢sym i₁≢i₂)))))

-- The permutation exchanges the two low pairs: divide out the double
-- exchange, which renames the four indices back.
passes-swapped : ∀ {w : W} → HFreeʷ w →
                 prm (sp w) i₀ ≡ i₃ → prm (sp w) i₁ ≡ i₂ →
                 prm (sp w) i₂ ≡ i₁ → prm (sp w) i₃ ≡ i₀ →
                 sgn (sp w) i₀ ≡ sgn (sp w) i₁ →
                 sgn (sp w) i₃ ≡ sgn (sp w) i₂ →
                 Passes w
passes-swapped {w} h p₀ p₁ p₂ p₃ s₀ s₃ =
  passes-factor Xw-invol passes-Xw
    (passes-fixed (hcat hfree-X h)
                  (four-of {λ t → prm (sp (Xw • w)) t ≡ t} f₀ f₁ f₂ f₃) s₀′ s₃′)
  where
  -- What the double exchange does to the four indices.
  sw₀ : swapF i₁ i₂ (swapF i₀ i₃ i₀) ≡ i₃
  sw₀ = Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-a i₀ i₃))
                 (swapF-o i₁ i₂ i₃ (≢sym i₁≢i₃) (≢sym i₂≢i₃))

  sw₁ : swapF i₁ i₂ (swapF i₀ i₃ i₁) ≡ i₂
  sw₁ = Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-o i₀ i₃ i₁ (≢sym i₀≢i₁) i₁≢i₃))
                 (swapF-a i₁ i₂)

  sw₂ : swapF i₁ i₂ (swapF i₀ i₃ i₂) ≡ i₁
  sw₂ = Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-o i₀ i₃ i₂ (≢sym i₀≢i₂) i₂≢i₃))
                 (swapF-b i₁ i₂)

  sw₃ : swapF i₁ i₂ (swapF i₀ i₃ i₃) ≡ i₀
  sw₃ = Eq.trans (Eq.cong (swapF i₁ i₂) (swapF-b i₀ i₃))
                 (swapF-o i₁ i₂ i₀ i₀≢i₁ i₀≢i₂)

  img : ∀ (t : Fin N) →
        prm (sp (Xw • w)) t ≡ prm (sp w) (swapF i₁ i₂ (swapF i₀ i₃ t))
  img t = Eq.cong (prm (sp w)) (prm≡ sp-Xw t)

  -- The exchange carries no sign, so it only renames.
  sg : ∀ (t : Fin N) →
       sgn (sp (Xw • w)) t ≡ sgn (sp w) (swapF i₁ i₂ (swapF i₀ i₃ t))
  sg t = Eq.cong₂ _xor_ (sgn≡ sp-Xw t) (Eq.cong (sgn (sp w)) (prm≡ sp-Xw t))

  f₀ : prm (sp (Xw • w)) i₀ ≡ i₀
  f₀ = Eq.trans (img i₀) (Eq.trans (Eq.cong (prm (sp w)) sw₀) p₃)

  f₁ : prm (sp (Xw • w)) i₁ ≡ i₁
  f₁ = Eq.trans (img i₁) (Eq.trans (Eq.cong (prm (sp w)) sw₁) p₂)

  f₂ : prm (sp (Xw • w)) i₂ ≡ i₂
  f₂ = Eq.trans (img i₂) (Eq.trans (Eq.cong (prm (sp w)) sw₂) p₁)

  f₃ : prm (sp (Xw • w)) i₃ ≡ i₃
  f₃ = Eq.trans (img i₃) (Eq.trans (Eq.cong (prm (sp w)) sw₃) p₀)

  s₀′ : sgn (sp (Xw • w)) i₀ ≡ sgn (sp (Xw • w)) i₁
  s₀′ = Eq.trans (sg i₀)
        (Eq.trans (Eq.cong (sgn (sp w)) sw₀)
        (Eq.trans s₃
        (Eq.trans (Eq.cong (sgn (sp w)) (Eq.sym sw₁)) (Eq.sym (sg i₁)))))

  s₃′ : sgn (sp (Xw • w)) i₃ ≡ sgn (sp (Xw • w)) i₂
  s₃′ = Eq.trans (sg i₃)
        (Eq.trans (Eq.cong (sgn (sp w)) sw₃)
        (Eq.trans s₀
        (Eq.trans (Eq.cong (sgn (sp w)) (Eq.sym sw₂)) (Eq.sym (sg i₂)))))

------------------------------------------------------------------------
-- Lemma A.6, the word-level conclusion
--
-- A Hadamard-free word whose signed permutation fixes or exchanges the
-- two low pairs — together — and whose signs agree along each pair can
-- be carried across the Hadamard pair.  That is the hypothesis
-- `Commutant` delivers from commuting with it.

passes-A6 : ∀ {w : W} → HFreeʷ w →
            ( (prm (sp w) i₀ ≡ i₀ × prm (sp w) i₁ ≡ i₁
               × prm (sp w) i₂ ≡ i₂ × prm (sp w) i₃ ≡ i₃)
            ⊎ (prm (sp w) i₀ ≡ i₃ × prm (sp w) i₁ ≡ i₂
               × prm (sp w) i₂ ≡ i₁ × prm (sp w) i₃ ≡ i₀) ) →
            sgn (sp w) i₀ ≡ sgn (sp w) i₁ →
            sgn (sp w) i₃ ≡ sgn (sp w) i₂ →
            Passes w
passes-A6 {w} h (inj₁ (p₀ , p₁ , p₂ , p₃)) s₀ s₃ =
  passes-fixed h (four-of {λ t → prm (sp w) t ≡ t} p₀ p₁ p₂ p₃) s₀ s₃
passes-A6 h (inj₂ (p₀ , p₁ , p₂ , p₃)) s₀ s₃ =
  passes-swapped h p₀ p₁ p₂ p₃ s₀ s₃
