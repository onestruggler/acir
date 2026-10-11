------------------------------------------------------------------------
-- Presentations of groups
--
-- The encoded gates of Appendix A.4.1 as signed permutations
--
-- Equations (36) and (37) write a Hadamard pair as the standard pair
-- conjugated by a word of encoded swaps and X gates, and Corollary A.7
-- needs that word's signed permutation.  Each encoded gate is a
-- product, over the contexts of the other wires, of letters acting on
-- basis vectors of one context, so its signed permutation at a basis
-- vector is that of the one letter of its context (`Local`, and
-- `ZXProd`, `ZZProd` for the two letter shapes).  Read off that way,
-- the encoded Z negates the vectors with a 1 on its wire (`sp-EZ`), CZ
-- those with 1s on both of its (`sp-ECZ`), and the encoded X and swap
-- carry no sign at all: X flips its wire (`sp-EX`) and the swap
-- exchanges its two (`sp-Eswap`), the signs of their letters
-- cancelling in pairs.  A signed permutation with no signs is a bit
-- map (`bm`), and a product of bit maps is the composite (`sp-∏`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.NetSP (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_ ; not ; _∧_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Nat using (zero ; suc ; _≤_ ; _<_ ; z≤n ; s≤s) renaming (_^_ to _^ℕ_)
open import Data.Nat.Properties using (≤-refl ; n<1+n ; ≤-pred ; <⇒≤)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitstringsLemmas
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (code ; index ; code-index ; index-code)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Matrices using (eqB)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Encoding
  using (∏ ; zz ; zx ; str₁ ; str₂ ; E-Z ; E-CZ ; E-X ; E-swap ; ℰ)
open import Examples.Groups.Real-Clifford+CH.EncodingSemantics.Strings
  using (ctx₁ ; pr₁ ; ctx-str₁ ; pr-str₁ ; bit-str₁ ; str-ctx₁
       ; ctx₂ ; pr₂ ; ctx-str₂ ; pr-str₂ ; bit-str₂ ; ctl-str₂ ; str-ctx₂)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp[_,_] ; sgn ; prm ; _⊙_ ; _≐_ ; eqv ; sgn≡ ; prm≡ ; idSP ; ≐-refl ; ≐-sym
       ; ≐-trans ; ⊙-cong ; δ ; δ-here ; δ-≢ ; swapF ; swapF-a ; swapF-b ; swapF-o ; sp ; sp-zx
       ; xor-idʳ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.BitAlg
  using (run ; swapBits ; swap-ins ; cflip ; flip-ins)

private
  n : ℕ
  n = ₃₊ m

  N : ℕ
  N = 2 ^ℕ n

  W : Set
  W = Word (GenP n)

  idx : Bits n → Fin N
  idx = index n

  idx-inj : ∀ {x y : Bits n} → idx x ≡ idx y → x ≡ y
  idx-inj {x} {y} e =
    Eq.trans (Eq.sym (code-index n x)) (Eq.trans (Eq.cong (code n) e) (code-index n y))

  idx-≢ : ∀ {x y : Bits n} → x ≢ y → idx x ≢ idx y
  idx-≢ ne e = ne (idx-inj e)

  true≢false : true ≢ false
  true≢false ()

  -- An index is the index of its code.
  at-code : ∀ (z : Fin N) → z ≡ idx (code n z)
  at-code z = Eq.sym (index-code n z)

  -- The sign atom at the index of a string.
  δ-same : ∀ (u : Bits n) (z : Fin N) → z ≡ idx u → δ (idx u) z ≡ true
  δ-same u z e = Eq.trans (Eq.cong (δ (idx u)) e) (δ-here (idx u))

  δ-diff : ∀ (u v : Bits n) (z : Fin N) → z ≡ idx v → u ≢ v → δ (idx u) z ≡ false
  δ-diff u v z e ne = δ-≢ (idx u) z (λ e′ → ne (idx-inj (Eq.trans (Eq.sym e′) e)))

------------------------------------------------------------------------
-- Bit maps

bm : (Bits n → Bits n) → SP
bm φ = sp[ (λ _ → false) , (λ z → idx (φ (code n z))) ]

bm-⊙ : ∀ (φ ψ : Bits n → Bits n) → bm φ ⊙ bm ψ ≐ bm (λ x → ψ (φ x))
bm-⊙ φ ψ =
  eqv (λ _ → Eq.refl) (λ z → Eq.cong (λ y → idx (ψ y)) (code-index n (φ (code n z))))

bm-id : ∀ (φ : Bits n → Bits n) → (∀ x → φ x ≡ x) → bm φ ≐ idSP
bm-id φ h = eqv (λ _ → Eq.refl) (λ z → Eq.trans (Eq.cong idx (h (code n z))) (index-code n z))

bm-cong : ∀ (φ ψ : Bits n → Bits n) → (∀ x → φ x ≡ ψ x) → bm φ ≐ bm ψ
bm-cong φ ψ h = eqv (λ _ → Eq.refl) (λ z → Eq.cong idx (h (code n z)))

-- A product of words that are bit maps is the composite map.
sp-∏ : ∀ {A : Set} (F : A → W) (φ : A → Bits n → Bits n) (L : List A) →
       All (λ a → sp (F a) ≐ bm (φ a)) L → sp (∏ L F) ≐ bm (run φ L)
sp-∏ F φ []      []       = ≐-sym (bm-id (λ x → x) (λ _ → Eq.refl))
sp-∏ F φ (a ∷ L) (h ∷ hs) = ≐-trans (⊙-cong h (sp-∏ F φ L hs)) (bm-⊙ (φ a) (run φ L))

------------------------------------------------------------------------
-- A product over the contexts, of letters acting within one context

module Local {k : ℕ} (f : Bits k → W) (ctx : Fin N → Bits k)
             (out : ∀ c z → ctx z ≢ c → (prm (sp (f c)) z ≡ z) × (sgn (sp (f c)) z ≡ false))
             (stay : ∀ z → ctx (prm (sp (f (ctx z))) z) ≡ ctx z) where

  private
    ≢of : ∀ z c → eqB (ctx z) c ≡ false → ctx z ≢ c
    ≢of z c e p = true≢false (Eq.trans (Eq.sym (eqB-complete (ctx z) c p)) e)

    absent : ∀ (L : List (Bits k)) z → ctx z ∈ᵇ L ≡ false →
             (prm (sp (∏ L f)) z ≡ z) × (sgn (sp (∏ L f)) z ≡ false)
    absent []      z _ = Eq.refl , Eq.refl
    absent (c ∷ L) z h with eqB (ctx z) c in e
    ... | true  = ⊥-elim (true≢false h)
    ... | false =
      Eq.trans (Eq.cong (prm (sp (∏ L f))) op) (proj₁ r) ,
      Eq.trans (Eq.cong₂ _xor_ os (Eq.cong (sgn (sp (∏ L f))) op)) (proj₂ r)
      where
      op : prm (sp (f c)) z ≡ z
      op = proj₁ (out c z (≢of z c e))

      os : sgn (sp (f c)) z ≡ false
      os = proj₂ (out c z (≢of z c e))

      r : (prm (sp (∏ L f)) z ≡ z) × (sgn (sp (∏ L f)) z ≡ false)
      r = absent L z h

    present : ∀ (L : List (Bits k)) → Nodup L → ∀ z → ctx z ∈ᵇ L ≡ true →
              (prm (sp (∏ L f)) z ≡ prm (sp (f (ctx z))) z) ×
              (sgn (sp (∏ L f)) z ≡ sgn (sp (f (ctx z))) z)
    present []      _         z ()
    present (c ∷ L) (nc , nL) z h with eqB (ctx z) c in e
    ... | true with eqB-sound (ctx z) c e
    ...   | Eq.refl = proj₁ r , Eq.trans (Eq.cong (sgn (sp (f (ctx z))) z xor_) (proj₂ r))
                                         (xor-idʳ (sgn (sp (f (ctx z))) z))
      where
      z′ : Fin N
      z′ = prm (sp (f (ctx z))) z

      r : (prm (sp (∏ L f)) z′ ≡ z′) × (sgn (sp (∏ L f)) z′ ≡ false)
      r = absent L z′ (Eq.trans (Eq.cong (_∈ᵇ L) (stay z)) nc)
    present (c ∷ L) (nc , nL) z h | false =
      Eq.trans (Eq.cong (prm (sp (∏ L f))) op) (proj₁ r) ,
      Eq.trans (Eq.cong₂ _xor_ os (Eq.cong (sgn (sp (∏ L f))) op)) (proj₂ r)
      where
      op : prm (sp (f c)) z ≡ z
      op = proj₁ (out c z (≢of z c e))

      os : sgn (sp (f c)) z ≡ false
      os = proj₂ (out c z (≢of z c e))

      r : (prm (sp (∏ L f)) z ≡ prm (sp (f (ctx z))) z) ×
          (sgn (sp (∏ L f)) z ≡ sgn (sp (f (ctx z))) z)
      r = present L nL z h

  at : ∀ z → (prm (sp (∏ (allBits k) f)) z ≡ prm (sp (f (ctx z))) z) ×
             (sgn (sp (∏ (allBits k) f)) z ≡ sgn (sp (f (ctx z))) z)
  at z = present (allBits k) (allBits-nodup k) z (∈-allBits (ctx z))

-- Letters (−1)_[s c] X_[x c, y c], one per context.
module ZXProd {k : ℕ} (ctxF : Bits n → Bits k) (s x y : Bits k → Bits n)
              (cs : ∀ c → ctxF (s c) ≡ c) (cx : ∀ c → ctxF (x c) ≡ c)
              (cy : ∀ c → ctxF (y c) ≡ c) (xy : ∀ c → x c ≢ y c) where

  F : Bits k → W
  F c = zx {₃₊ m} (idx (s c)) (idx (x c)) (idx (y c))

  private
    ctx : Fin N → Bits k
    ctx z = ctxF (code n z)

    ctx-idx : ∀ (v : Bits n) → ctx (idx v) ≡ ctxF v
    ctx-idx v = Eq.cong ctxF (code-index n v)

    prmF : ∀ c z → prm (sp (F c)) z ≡ swapF (idx (x c)) (idx (y c)) z
    prmF c z = prm≡ (sp-zx (idx (s c)) (idx (x c)) (idx (y c)) (idx-≢ (xy c))) z

    sgnF : ∀ c z → sgn (sp (F c)) z ≡ δ (idx (s c)) z
    sgnF c z = Eq.trans (sgn≡ (sp-zx (idx (s c)) (idx (x c)) (idx (y c)) (idx-≢ (xy c))) z)
                        (xor-idʳ (δ (idx (s c)) z))

    -- An index of another context is none of this one's.
    notin : ∀ c z (v : Bits k → Bits n) → (∀ c → ctxF (v c) ≡ c) → ctx z ≢ c → z ≢ idx (v c)
    notin c z v cv ne e = ne (Eq.trans (Eq.cong ctx e) (Eq.trans (ctx-idx (v c)) (cv c)))

    out : ∀ c z → ctx z ≢ c → (prm (sp (F c)) z ≡ z) × (sgn (sp (F c)) z ≡ false)
    out c z ne =
      Eq.trans (prmF c z) (swapF-o (idx (x c)) (idx (y c)) z (notin c z x cx ne) (notin c z y cy ne)) ,
      Eq.trans (sgnF c z) (δ-≢ (idx (s c)) z (notin c z s cs ne))

    stay : ∀ z → ctx (prm (sp (F (ctx z))) z) ≡ ctx z
    stay z = Eq.trans (Eq.cong ctx (prmF (ctx z) z)) (go (z ≟ X) (z ≟ Y))
      where
      X Y : Fin N
      X = idx (x (ctx z))
      Y = idx (y (ctx z))

      go : Dec (z ≡ X) → Dec (z ≡ Y) → ctx (swapF X Y z) ≡ ctx z
      go (yes e) _ =
        Eq.trans (Eq.cong (λ w → ctx (swapF X Y w)) e)
          (Eq.trans (Eq.cong ctx (swapF-a X Y)) (Eq.trans (ctx-idx (y (ctx z))) (cy (ctx z))))
      go (no _) (yes e) =
        Eq.trans (Eq.cong (λ w → ctx (swapF X Y w)) e)
          (Eq.trans (Eq.cong ctx (swapF-b X Y)) (Eq.trans (ctx-idx (x (ctx z))) (cx (ctx z))))
      go (no n₁) (no n₂) = Eq.cong ctx (swapF-o X Y z n₁ n₂)

    module L = Local F ctx out stay

  at : ∀ z → (prm (sp (∏ (allBits k) F)) z
              ≡ swapF (idx (x (ctxF (code n z)))) (idx (y (ctxF (code n z)))) z) ×
             (sgn (sp (∏ (allBits k) F)) z ≡ δ (idx (s (ctxF (code n z)))) z)
  at z = Eq.trans (proj₁ (L.at z)) (prmF (ctx z) z) , Eq.trans (proj₂ (L.at z)) (sgnF (ctx z) z)

-- Letters (−1)_[x c] (−1)_[y c], one per context.
module ZZProd {k : ℕ} (ctxF : Bits n → Bits k) (x y : Bits k → Bits n)
              (cx : ∀ c → ctxF (x c) ≡ c) (cy : ∀ c → ctxF (y c) ≡ c) where

  F : Bits k → W
  F c = zz {₃₊ m} (idx (x c)) (idx (y c))

  private
    ctx : Fin N → Bits k
    ctx z = ctxF (code n z)

    notin : ∀ c z (v : Bits k → Bits n) → (∀ c → ctxF (v c) ≡ c) → ctx z ≢ c → z ≢ idx (v c)
    notin c z v cv ne e =
      ne (Eq.trans (Eq.cong ctx e) (Eq.trans (Eq.cong ctxF (code-index n (v c))) (cv c)))

    out : ∀ c z → ctx z ≢ c → (prm (sp (F c)) z ≡ z) × (sgn (sp (F c)) z ≡ false)
    out c z ne = Eq.refl , Eq.cong₂ _xor_ (δ-≢ (idx (x c)) z (notin c z x cx ne))
                                           (δ-≢ (idx (y c)) z (notin c z y cy ne))

    module L = Local F ctx out (λ z → Eq.refl)

  at : ∀ z → (prm (sp (∏ (allBits k) F)) z ≡ z) ×
             (sgn (sp (∏ (allBits k) F)) z
              ≡ δ (idx (x (ctxF (code n z)))) z xor δ (idx (y (ctxF (code n z)))) z)
  at z = L.at z

------------------------------------------------------------------------
-- The encoded Z: a sign on the vectors with a 1 on its wire

module _ (p : ℕ) (p<n : p < n) where

  private
    X₀ X₁ : Bits (₁₊ m) → Bits n
    X₀ c = str₁ {m} p c false true
    X₁ c = str₁ {m} p c true true

    module Z = ZZProd (ctx₁ {m} p) X₀ X₁ (λ c → ctx-str₁ p c false true p<n)
                      (λ c → ctx-str₁ p c true true p<n)

    pr-≢ : ∀ c b b′ g g′ → b ≢ b′ → str₁ {m} p c b g ≢ str₁ {m} p c b′ g′
    pr-≢ c b b′ g g′ ne e =
      ne (Eq.trans (Eq.sym (pr-str₁ p c b g p<n))
                   (Eq.trans (Eq.cong (pr₁ p) e) (pr-str₁ p c b′ g′ p<n)))

    bit-≢ : ∀ c b b′ g g′ → g ≢ g′ → str₁ {m} p c b g ≢ str₁ {m} p c b′ g′
    bit-≢ c b b′ g g′ ne e =
      ne (Eq.trans (Eq.sym (bit-str₁ p c b g p<n))
                   (Eq.trans (Eq.cong (lookupℕ p) e) (bit-str₁ p c b′ g′ p<n)))

    f≢t : false ≢ true
    f≢t ()

    t≢f : true ≢ false
    t≢f ()

    ez : ∀ c b g z → z ≡ idx (str₁ {m} p c b g) →
         δ (idx (X₀ c)) z xor δ (idx (X₁ c)) z ≡ g
    ez c false true  z e = Eq.cong₂ _xor_ (δ-same (X₀ c) z e)
                                          (δ-diff (X₁ c) (X₀ c) z e (pr-≢ c true false true true t≢f))
    ez c true  true  z e = Eq.cong₂ _xor_ (δ-diff (X₀ c) (X₁ c) z e (pr-≢ c false true true true f≢t))
                                          (δ-same (X₁ c) z e)
    ez c b     false z e = Eq.cong₂ _xor_ (δ-diff (X₀ c) (str₁ p c b false) z e
                                                  (bit-≢ c false b true false t≢f))
                                          (δ-diff (X₁ c) (str₁ p c b false) z e
                                                  (bit-≢ c true b true false t≢f))

  sp-EZ : ∀ z → (prm (sp (E-Z {m} p)) z ≡ z) × (sgn (sp (E-Z {m} p)) z ≡ lookupℕ p (code n z))
  sp-EZ z = proj₁ (Z.at z) , Eq.trans (proj₂ (Z.at z)) (ez c (pr₁ p x) (lookupℕ p x) z e)
    where
    x : Bits n
    x = code n z

    c : Bits (₁₊ m)
    c = ctx₁ p x

    e : z ≡ idx (str₁ {m} p c (pr₁ p x) (lookupℕ p x))
    e = Eq.trans (at-code z) (Eq.cong idx (Eq.sym (str-ctx₁ p x p<n)))

------------------------------------------------------------------------
-- The encoded X: it flips its wire, with no sign

module _ (p : ℕ) (p<n : p < n) where

  private
    p≤ : p ≤ ₂₊ m
    p≤ = ≤-pred p<n

    ins : Bool → Bits (₂₊ m) → Bits n
    ins g c = insertℕ p g c

    ins-≢ : ∀ c → ins false c ≢ ins true c
    ins-≢ c e = f≢t (Eq.trans (Eq.sym (lookup-insert p false c p≤))
                              (Eq.trans (Eq.cong (lookupℕ p) e) (lookup-insert p true c p≤)))
      where
      f≢t : false ≢ true
      f≢t ()

    module X = ZXProd (removeℕ p) (ins true) (ins false) (ins true)
                      (λ c → remove-insert p true c p≤) (λ c → remove-insert p false c p≤)
                      (λ c → remove-insert p true c p≤) ins-≢

    -- At a vector of the context c with bit g on the wire.
    xp : ∀ c g z → z ≡ idx (ins g c) →
         (swapF (idx (ins false c)) (idx (ins true c)) z ≡ idx (flipℕ p (ins g c))) ×
         (δ (idx (ins true c)) z ≡ g)
    xp c false z e =
      Eq.trans (Eq.cong (swapF (idx (ins false c)) (idx (ins true c))) e)
        (Eq.trans (swapF-a (idx (ins false c)) (idx (ins true c)))
                  (Eq.cong idx (Eq.sym (flip-ins p false c p≤)))) ,
      δ-diff (ins true c) (ins false c) z e (λ h → ins-≢ c (Eq.sym h))
    xp c true  z e =
      Eq.trans (Eq.cong (swapF (idx (ins false c)) (idx (ins true c))) e)
        (Eq.trans (swapF-b (idx (ins false c)) (idx (ins true c)))
                  (Eq.cong idx (Eq.sym (flip-ins p true c p≤)))) ,
      δ-same (ins true c) z e

  sp-EX : sp (E-X {m} p) ≐ bm (flipℕ p)
  sp-EX = eqv sg pm
    where
    dec : ∀ z → z ≡ idx (ins (lookupℕ p (code n z)) (removeℕ p (code n z)))
    dec z = Eq.trans (at-code z) (Eq.cong idx (Eq.sym (insert-lookup-remove p (code n z) p≤)))

    split : ∀ z → code n z ≡ ins (lookupℕ p (code n z)) (removeℕ p (code n z))
    split z = Eq.sym (insert-lookup-remove p (code n z) p≤)

    sg : ∀ z → sgn (sp (E-X {m} p)) z ≡ false
    sg z = begin
      sgn (sp (E-Z {m} p)) z xor sgn (sp (∏ (allBits (₂₊ m)) X.F)) (prm (sp (E-Z {m} p)) z)
        ≡⟨ Eq.cong₂ _xor_ (proj₂ (sp-EZ p p<n z))
                          (Eq.cong (sgn (sp (∏ (allBits (₂₊ m)) X.F))) (proj₁ (sp-EZ p p<n z))) ⟩
      lookupℕ p (code n z) xor sgn (sp (∏ (allBits (₂₊ m)) X.F)) z
        ≡⟨ Eq.cong (lookupℕ p (code n z) xor_)
                   (Eq.trans (proj₂ (X.at z))
                             (proj₂ (xp (removeℕ p (code n z)) (lookupℕ p (code n z)) z (dec z)))) ⟩
      lookupℕ p (code n z) xor lookupℕ p (code n z)
        ≡⟨ self (lookupℕ p (code n z)) ⟩
      false ∎
      where
      open Eq.≡-Reasoning
      self : ∀ b → b xor b ≡ false
      self true  = Eq.refl
      self false = Eq.refl

    pm : ∀ z → prm (sp (E-X {m} p)) z ≡ idx (flipℕ p (code n z))
    pm z =
      Eq.trans (Eq.cong (prm (sp (∏ (allBits (₂₊ m)) X.F))) (proj₁ (sp-EZ p p<n z)))
        (Eq.trans (proj₁ (X.at z))
          (Eq.trans (proj₁ (xp (removeℕ p (code n z)) (lookupℕ p (code n z)) z (dec z)))
                    (Eq.cong (λ v → idx (flipℕ p v)) (Eq.sym (split z)))))

-- ℰ: X where the bit is 1.
sp-ℰ : ∀ b w → w < n → sp (ℰ {m} b w) ≐ bm (cflip b w)
sp-ℰ true  w w<n = sp-EX w w<n
sp-ℰ false w w<n = ≐-sym (bm-id (cflip false w) (λ _ → Eq.refl))

------------------------------------------------------------------------
-- The encoded CZ: a sign on the vectors with 1s on both of its wires

module _ (p : ℕ) (sp<n : suc p < n) where

  private
    X₀ X₁ : Bits m → Bits n
    X₀ c = str₂ {m} p c false true true
    X₁ c = str₂ {m} p c true true true

    module Z = ZZProd (ctx₂ {m} p) X₀ X₁ (λ c → ctx-str₂ p c false true true sp<n)
                      (λ c → ctx-str₂ p c true true true sp<n)

    f≢t : false ≢ true
    f≢t ()

    t≢f : true ≢ false
    t≢f ()

    pr-≢ : ∀ c b b′ u u′ t t′ → b ≢ b′ → str₂ {m} p c b u t ≢ str₂ {m} p c b′ u′ t′
    pr-≢ c b b′ u u′ t t′ ne e =
      ne (Eq.trans (Eq.sym (pr-str₂ p c b u t sp<n))
                   (Eq.trans (Eq.cong (pr₂ p) e) (pr-str₂ p c b′ u′ t′ sp<n)))

    ctl-≢ : ∀ c b b′ u u′ t t′ → u ≢ u′ → str₂ {m} p c b u t ≢ str₂ {m} p c b′ u′ t′
    ctl-≢ c b b′ u u′ t t′ ne e =
      ne (Eq.trans (Eq.sym (ctl-str₂ p c b u t sp<n))
                   (Eq.trans (Eq.cong (lookupℕ (suc p)) e) (ctl-str₂ p c b′ u′ t′ sp<n)))

    bit-≢ : ∀ c b b′ u u′ t t′ → t ≢ t′ → str₂ {m} p c b u t ≢ str₂ {m} p c b′ u′ t′
    bit-≢ c b b′ u u′ t t′ ne e =
      ne (Eq.trans (Eq.sym (bit-str₂ p c b u t sp<n))
                   (Eq.trans (Eq.cong (lookupℕ p) e) (bit-str₂ p c b′ u′ t′ sp<n)))

    ecz : ∀ c b u t z → z ≡ idx (str₂ {m} p c b u t) →
          δ (idx (X₀ c)) z xor δ (idx (X₁ c)) z ≡ u ∧ t
    ecz c false true  true  z e =
      Eq.cong₂ _xor_ (δ-same (X₀ c) z e)
                     (δ-diff (X₁ c) (X₀ c) z e (pr-≢ c true false true true true true t≢f))
    ecz c true  true  true  z e =
      Eq.cong₂ _xor_ (δ-diff (X₀ c) (X₁ c) z e (pr-≢ c false true true true true true f≢t))
                     (δ-same (X₁ c) z e)
    ecz c b     false t     z e =
      Eq.cong₂ _xor_ (δ-diff (X₀ c) (str₂ p c b false t) z e (ctl-≢ c false b true false true t t≢f))
                     (δ-diff (X₁ c) (str₂ p c b false t) z e (ctl-≢ c true b true false true t t≢f))
    ecz c b     true  false z e =
      Eq.cong₂ _xor_ (δ-diff (X₀ c) (str₂ p c b true false) z e (bit-≢ c false b true true true false t≢f))
                     (δ-diff (X₁ c) (str₂ p c b true false) z e (bit-≢ c true b true true true false t≢f))

  sp-ECZ : ∀ z → (prm (sp (E-CZ {m} p)) z ≡ z) ×
                 (sgn (sp (E-CZ {m} p)) z ≡ lookupℕ (suc p) (code n z) ∧ lookupℕ p (code n z))
  sp-ECZ z = proj₁ (Z.at z) ,
             Eq.trans (proj₂ (Z.at z)) (ecz c (pr₂ p x) (lookupℕ (suc p) x) (lookupℕ p x) z e)
    where
    x : Bits n
    x = code n z

    c : Bits m
    c = ctx₂ p x

    e : z ≡ idx (str₂ {m} p c (pr₂ p x) (lookupℕ (suc p) x) (lookupℕ p x))
    e = Eq.trans (at-code z) (Eq.cong idx (Eq.sym (str-ctx₂ p x sp<n)))

------------------------------------------------------------------------
-- The encoded swap: it exchanges its two wires, with no sign
--
-- It is CZ and three products of letters, and on the four vectors of a
-- context (u on wire p + 1, t on wire p) each letter moves one vector
-- to another with a sign or back without; composed, the vector (u, t)
-- lands on (t, u), and the signs met cancel in pairs.

module _ (p : ℕ) (sp<n : suc p < n) where

  private
    sp≤ : suc p ≤ ₂₊ m
    sp≤ = ≤-pred sp<n

    p≤ : p ≤ ₁₊ m
    p≤ = ≤-pred sp≤

    S : Bits (₁₊ m) → Bool → Bool → Bits n
    S c u t = insertℕ (suc p) u (insertℕ p t c)

    A : Bits (₁₊ m) → Bool → Bool → Fin N
    A c u t = idx (S c u t)

    rm2 : Bits n → Bits (₁₊ m)
    rm2 x = removeℕ p (removeℕ (suc p) x)

    rm2-S : ∀ c u t → rm2 (S c u t) ≡ c
    rm2-S c u t = Eq.trans (Eq.cong (removeℕ p) (remove-insert (suc p) u (insertℕ p t c) sp≤))
                           (remove-insert p t c p≤)

    lk-u : ∀ c u t → lookupℕ (suc p) (S c u t) ≡ u
    lk-u c u t = lookup-insert (suc p) u (insertℕ p t c) sp≤

    lk-t : ∀ c u t → lookupℕ p (S c u t) ≡ t
    lk-t c u t = Eq.trans (lookup-insert-below (suc p) p u (insertℕ p t c) (n<1+n p) sp≤)
                          (lookup-insert p t c p≤)

    u-≢ : ∀ c u u′ t t′ → u ≢ u′ → S c u t ≢ S c u′ t′
    u-≢ c u u′ t t′ ne e =
      ne (Eq.trans (Eq.sym (lk-u c u t)) (Eq.trans (Eq.cong (lookupℕ (suc p)) e) (lk-u c u′ t′)))

    t-≢ : ∀ c u u′ t t′ → t ≢ t′ → S c u t ≢ S c u′ t′
    t-≢ c u u′ t t′ ne e =
      ne (Eq.trans (Eq.sym (lk-t c u t)) (Eq.trans (Eq.cong (lookupℕ p) e) (lk-t c u′ t′)))

    A-u≢ : ∀ c u u′ t t′ → u ≢ u′ → A c u t ≢ A c u′ t′
    A-u≢ c u u′ t t′ ne = idx-≢ (u-≢ c u u′ t t′ ne)

    A-t≢ : ∀ c u u′ t t′ → t ≢ t′ → A c u t ≢ A c u′ t′
    A-t≢ c u u′ t t′ ne = idx-≢ (t-≢ c u u′ t t′ ne)

    ctx-A : ∀ c u t → rm2 (code n (A c u t)) ≡ c
    ctx-A c u t = Eq.trans (Eq.cong rm2 (code-index n (S c u t))) (rm2-S c u t)

    -- Every vector is one of its context's.
    split : ∀ x → x ≡ S (rm2 x) (lookupℕ (suc p) x) (lookupℕ p x)
    split x = Eq.trans (Eq.sym (insert-lookup-remove (suc p) x sp≤))
                (Eq.cong (insertℕ (suc p) (lookupℕ (suc p) x))
                  (Eq.trans (Eq.sym (insert-lookup-remove p (removeℕ (suc p) x) p≤))
                            (Eq.cong (λ b → insertℕ p b (rm2 x))
                                     (lookup-remove-below (suc p) p x (n<1+n p) sp≤))))

    f≢t : false ≢ true
    f≢t ()

    t≢f : true ≢ false
    t≢f ()

    -- (−1)_[11] X_[10,11], and (−1)_[01] X_[01,11].
    module P1 = ZXProd rm2 (λ c → S c true true) (λ c → S c true false) (λ c → S c true true)
                       (λ c → rm2-S c true true) (λ c → rm2-S c true false) (λ c → rm2-S c true true)
                       (λ c → t-≢ c true true false true f≢t)
    module P2 = ZXProd rm2 (λ c → S c false true) (λ c → S c false true) (λ c → S c true true)
                       (λ c → rm2-S c false true) (λ c → rm2-S c false true) (λ c → rm2-S c true true)
                       (λ c → u-≢ c false true true true f≢t)

    Π₁ Π₂ : W
    Π₁ = ∏ (allBits (₁₊ m)) P1.F
    Π₂ = ∏ (allBits (₁₊ m)) P2.F

    -- Their tables.
    t₁ : Bool → Bool → Bool
    t₁ true  t = not t
    t₁ false t = t

    s₁ : Bool → Bool → Bool
    s₁ true true = true
    s₁ _    _    = false

    u₂ : Bool → Bool → Bool
    u₂ u true  = not u
    u₂ u false = u

    s₂ : Bool → Bool → Bool
    s₂ u     false = false
    s₂ false true  = true
    s₂ true  true  = false

    P1-at : ∀ c u t → (prm (sp Π₁) (A c u t) ≡ swapF (A c true false) (A c true true) (A c u t)) ×
                      (sgn (sp Π₁) (A c u t) ≡ δ (A c true true) (A c u t))
    P1-at c u t =
      Eq.subst (λ c′ → prm (sp Π₁) (A c u t) ≡ swapF (A c′ true false) (A c′ true true) (A c u t))
               (ctx-A c u t) (proj₁ (P1.at (A c u t))) ,
      Eq.subst (λ c′ → sgn (sp Π₁) (A c u t) ≡ δ (A c′ true true) (A c u t))
               (ctx-A c u t) (proj₂ (P1.at (A c u t)))

    P2-at : ∀ c u t → (prm (sp Π₂) (A c u t) ≡ swapF (A c false true) (A c true true) (A c u t)) ×
                      (sgn (sp Π₂) (A c u t) ≡ δ (A c false true) (A c u t))
    P2-at c u t =
      Eq.subst (λ c′ → prm (sp Π₂) (A c u t) ≡ swapF (A c′ false true) (A c′ true true) (A c u t))
               (ctx-A c u t) (proj₁ (P2.at (A c u t))) ,
      Eq.subst (λ c′ → sgn (sp Π₂) (A c u t) ≡ δ (A c′ false true) (A c u t))
               (ctx-A c u t) (proj₂ (P2.at (A c u t)))

    P1-prm : ∀ c u t → prm (sp Π₁) (A c u t) ≡ A c u (t₁ u t)
    P1-prm c true  true  = Eq.trans (proj₁ (P1-at c true true)) (swapF-b (A c true false) (A c true true))
    P1-prm c true  false = Eq.trans (proj₁ (P1-at c true false)) (swapF-a (A c true false) (A c true true))
    P1-prm c false t     =
      Eq.trans (proj₁ (P1-at c false t))
               (swapF-o (A c true false) (A c true true) (A c false t)
                        (A-u≢ c false true t false f≢t) (A-u≢ c false true t true f≢t))

    P1-sgn : ∀ c u t → sgn (sp Π₁) (A c u t) ≡ s₁ u t
    P1-sgn c true  true  = Eq.trans (proj₂ (P1-at c true true)) (δ-here (A c true true))
    P1-sgn c true  false =
      Eq.trans (proj₂ (P1-at c true false))
               (δ-≢ (A c true true) (A c true false) (A-t≢ c true true false true f≢t))
    P1-sgn c false t     =
      Eq.trans (proj₂ (P1-at c false t))
               (δ-≢ (A c true true) (A c false t) (A-u≢ c false true t true f≢t))

    P2-prm : ∀ c u t → prm (sp Π₂) (A c u t) ≡ A c (u₂ u t) t
    P2-prm c false true  = Eq.trans (proj₁ (P2-at c false true)) (swapF-a (A c false true) (A c true true))
    P2-prm c true  true  = Eq.trans (proj₁ (P2-at c true true)) (swapF-b (A c false true) (A c true true))
    P2-prm c u     false =
      Eq.trans (proj₁ (P2-at c u false))
               (swapF-o (A c false true) (A c true true) (A c u false)
                        (A-t≢ c u false false true f≢t) (A-t≢ c u true false true f≢t))

    P2-sgn : ∀ c u t → sgn (sp Π₂) (A c u t) ≡ s₂ u t
    P2-sgn c false true  = Eq.trans (proj₂ (P2-at c false true)) (δ-here (A c false true))
    P2-sgn c true  true  =
      Eq.trans (proj₂ (P2-at c true true))
               (δ-≢ (A c false true) (A c true true) (A-u≢ c true false true true t≢f))
    P2-sgn c u     false =
      Eq.trans (proj₂ (P2-at c u false))
               (δ-≢ (A c false true) (A c u false) (A-t≢ c u false false true f≢t))

    CZ-sgn : ∀ c u t → sgn (sp (E-CZ {m} p)) (A c u t) ≡ u ∧ t
    CZ-sgn c u t =
      Eq.trans (proj₂ (sp-ECZ p sp<n (A c u t)))
        (Eq.cong₂ _∧_ (Eq.trans (Eq.cong (lookupℕ (suc p)) (code-index n (S c u t))) (lk-u c u t))
                      (Eq.trans (Eq.cong (lookupℕ p) (code-index n (S c u t))) (lk-t c u t)))

    -- The composite, as tables.
    fu ft : Bool → Bool → Bool
    fu u t = u₂ u (t₁ u t)
    ft u t = t₁ (u₂ u (t₁ u t)) (t₁ u t)

    tot : Bool → Bool → Bool
    tot u t = (u ∧ t) xor (s₁ u t xor (s₂ u (t₁ u t) xor s₁ (fu u t) (t₁ u t)))

    fin : ∀ u t → (fu u t ≡ t) × (ft u t ≡ u) × (tot u t ≡ false)
    fin false false = Eq.refl , Eq.refl , Eq.refl
    fin false true  = Eq.refl , Eq.refl , Eq.refl
    fin true  false = Eq.refl , Eq.refl , Eq.refl
    fin true  true  = Eq.refl , Eq.refl , Eq.refl

    es-prm : ∀ c u t → prm (sp (E-swap {m} p)) (A c u t) ≡ A c (fu u t) (ft u t)
    es-prm c u t =
      Eq.trans (Eq.cong (λ w → prm (sp Π₁) (prm (sp Π₂) (prm (sp Π₁) w)))
                        (proj₁ (sp-ECZ p sp<n (A c u t))))
      (Eq.trans (Eq.cong (λ w → prm (sp Π₁) (prm (sp Π₂) w)) (P1-prm c u t))
      (Eq.trans (Eq.cong (prm (sp Π₁)) (P2-prm c u (t₁ u t)))
                (P1-prm c (u₂ u (t₁ u t)) (t₁ u t))))

    es-sgn : ∀ c u t → sgn (sp (E-swap {m} p)) (A c u t) ≡ tot u t
    es-sgn c u t =
      Eq.cong₂ _xor_ (CZ-sgn c u t)
        (Eq.trans (Eq.cong (sgn (sp Π₁ ⊙ (sp Π₂ ⊙ sp Π₁))) (proj₁ (sp-ECZ p sp<n (A c u t))))
          (Eq.cong₂ _xor_ (P1-sgn c u t)
            (Eq.trans (Eq.cong (sgn (sp Π₂ ⊙ sp Π₁)) (P1-prm c u t))
              (Eq.cong₂ _xor_ (P2-sgn c u (t₁ u t))
                (Eq.trans (Eq.cong (sgn (sp Π₁)) (P2-prm c u (t₁ u t)))
                          (P1-sgn c (u₂ u (t₁ u t)) (t₁ u t)))))))

  sp-Eswap : sp (E-swap {m} p) ≐ bm (swapBits p)
  sp-Eswap = eqv sg pm
    where
    at : ∀ z → z ≡ A (rm2 (code n z)) (lookupℕ (suc p) (code n z)) (lookupℕ p (code n z))
    at z = Eq.trans (at-code z) (Eq.cong idx (split (code n z)))

    sg : ∀ z → sgn (sp (E-swap {m} p)) z ≡ false
    sg z = Eq.trans (Eq.cong (sgn (sp (E-swap {m} p))) (at z))
             (Eq.trans (es-sgn (rm2 (code n z)) (lookupℕ (suc p) (code n z)) (lookupℕ p (code n z)))
                       (proj₂ (proj₂ (fin (lookupℕ (suc p) (code n z)) (lookupℕ p (code n z))))))

    pm : ∀ z → prm (sp (E-swap {m} p)) z ≡ idx (swapBits p (code n z))
    pm z =
      Eq.trans (Eq.cong (prm (sp (E-swap {m} p))) (at z))
        (Eq.trans (es-prm c u t)
          (Eq.trans (Eq.cong₂ (A c) (proj₁ (fin u t)) (proj₁ (proj₂ (fin u t))))
            (Eq.trans (Eq.cong idx (Eq.sym (swap-ins p u t c p≤)))
                      (Eq.cong (λ v → idx (swapBits p v)) (Eq.sym (split (code n z)))))))
      where
      c : Bits (₁₊ m)
      c = rm2 (code n z)

      u t : Bool
      u = lookupℕ (suc p) (code n z)
      t = lookupℕ p (code n z)
