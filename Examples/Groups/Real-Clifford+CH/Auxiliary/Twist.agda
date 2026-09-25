------------------------------------------------------------------------
-- Presentations of groups
--
-- Carrying a Hadamard-free word across a pair, whatever its signs
--
-- `Move.hh-pass` carries a Hadamard-free word u across a pair when its
-- signs agree along each of the two pre-image pairs.  When they
-- disagree along one, conjugating by u turns that 2 × 2 Hadamard into
-- itself times the letter `(−1)_[p] X_[p,q]` on the pre-images:
--
--     u · H_[p′,q′] H_[r′,s′]  ≈  H_[p,q] H_[r,s] · κ₁ · κ₂ · u,
--
-- κ₁ being that letter when the signs at p and q differ and ε
-- otherwise, and κ₂ the same for r and s (`hh-twist`, with `κ`).  The
-- proof flips the sign at p (or at r, or both) with a sign pair, so
-- that `hh-pass` applies, and pays for the flip with Equation (40) at
-- the tuple: `std-any`, which is `Eq77.Frame.std` with the sign's
-- partner any index fresh to the four, and `std-any₂`, the same for
-- the second pair.  The Hadamard-free bookkeeping is decided on
-- templates (`Template.A5-tmpl`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Twist (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; _xor_)
open import Data.Fin using (Fin)
open import Data.Fin.Properties using (_≟_)
open import Data.Nat using () renaming (_^_ to _^ℕ_)
open import Data.Vec using ([] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m
  using (HFreeʷ ; gen ; cat ; nil ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (SP ; sp ; sgn ; prm ; idSP ; δ ; δ-here ; δ-≢ ; xor-self ; eqv)
  renaming (_⊙_ to _⊛_ ; _≐_ to _≗_ ; ≐-trans to ≐-trans′ ; ≐-sym to ≐-sym′
          ; ≐-refl to ≐-refl′ ; ⊙-cong to ⊙-cong′ ; ⊙-assoc to ⊙-assoc′
          ; ⊙-idˡ to ⊙-idˡ′)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m
  using (tz ; ty ; ⌜_⌝ ; _•ᵗ_ ; Distinct ; []ᵈ ; _∷ᵈ_ ; lookup-inj ; module At)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m
  using (Eq65 ; eq66 ; comm-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Move m using (hh-pass)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Eq77 m using (module Frame)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

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

  hhʷ : Fin N → Fin N → Fin N → Fin N → W
  hhʷ = hh {₃₊ m}

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  -- Two signs agree when their sum is false …
  xf : ∀ (x y : Bool) → x xor y ≡ false → x ≡ y
  xf false false _ = Eq.refl
  xf true  true  _ = Eq.refl
  xf false true  ()
  xf true  false ()

  -- … and flipping the first makes them agree when it is true.
  xt : ∀ (x y : Bool) → x xor y ≡ true → true xor x ≡ y
  xt false true  _ = Eq.refl
  xt true  false _ = Eq.refl
  xt false false ()
  xt true  true  ()

  -- A sign pair, read at one of its indices or away from both.
  δδ-off : ∀ (p x i : Fin N) → i ≢ p → i ≢ x → (δ p i xor δ x i) ≡ false
  δδ-off p x i ip ix = Eq.cong₂ _xor_ (δ-≢ p i ip) (δ-≢ x i ix)

  δδ-fst : ∀ (p x : Fin N) → p ≢ x → (δ p p xor δ x p) ≡ true
  δδ-fst p x px = Eq.cong₂ _xor_ (δ-here p) (δ-≢ x p px)

  δδ-snd : ∀ (p x : Fin N) → x ≢ p → (δ p x xor δ x x) ≡ true
  δδ-snd p x xp = Eq.cong₂ _xor_ (δ-≢ p x xp) (δ-here x)

  -- A sign pair around a word and its inverse.
  conj-inv : ∀ (Z U U′ : SP) → Z ⊛ Z ≗ idSP → U ⊛ U′ ≗ idSP →
             (Z ⊛ U) ⊛ (U′ ⊛ Z) ≗ idSP
  conj-inv Z U U′ z² uu =
    ≐-trans′ (⊙-assoc′ Z U (U′ ⊛ Z))
    (≐-trans′ (⊙-cong′ (≐-refl′ {Z}) (≐-sym′ (⊙-assoc′ U U′ Z)))
    (≐-trans′ (⊙-cong′ (≐-refl′ {Z}) (⊙-cong′ uu (≐-refl′ {Z})))
    (≐-trans′ (⊙-cong′ (≐-refl′ {Z}) (⊙-idˡ′ Z)) z²)))

  zz-invol : ∀ (p x : Fin N) → sp (zzʷ p x) ⊛ sp (zzʷ p x) ≗ idSP
  zz-invol p x = eqv (λ i → xor-self (δ p i xor δ x i)) (λ _ → Eq.refl)

  -- A sign pair twice is nothing.
  zz-sq-w : ∀ (p x : Fin N) (u : W) → zzʷ p x • (zzʷ p x • u) ≈ u
  zz-sq-w p x u = begin
    zzʷ p x • (zzʷ p x • u)   ≈⟨ sym assoc ⟩
    (zzʷ p x • zzʷ p x) • u   ≈⟨ front u sq ⟩
    ε • u                     ≈⟨ left-unit ⟩
    u                         ∎
    where
    sq : zzʷ p x • zzʷ p x ≈ ε
    sq = A5-full (cat (gen (hf-zz p x)) (gen (hf-zz p x))) nil (zz-invol p x)

------------------------------------------------------------------------
-- The correction

κ : Bool → Fin N → Fin N → W → W
κ false p q w = w
κ true  p q w = zx {₃₊ m} p p q • w

module _ (e65 : Eq65) where

  ----------------------------------------------------------------------
  -- Equation (40) at a tuple, with any fresh partner for the sign

  std-any : ∀ (a b c d x : Fin N) →
            a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
            x ≢ a → x ≢ b → x ≢ c → x ≢ d →
            zzʷ a x • hhʷ a b c d ≈ hhʷ a b c d • (zzʷ a x • zxʷ b b a)
  std-any a b c d x ab ac ad bc bd cd xa xb xc xd = go (x ≟ F.e₀)
    where
    module F = Frame e65 a b c d ab ac ad bc bd cd

    H : W
    H = hhʷ a b c d

    go : Dec (x ≡ F.e₀) → zzʷ a x • H ≈ H • (zzʷ a x • zxʷ b b a)
    go (yes e) = Eq.subst (λ y → zzʷ a y • H ≈ H • (zzʷ a y • zxʷ b b a)) (Eq.sym e) F.std
    go (no ne) = begin
      zzʷ a x • H                                  ≈⟨ front H split ⟩
      (zzʷ a e₀ • zzʷ e₀ x) • H                    ≈⟨ assoc ⟩
      zzʷ a e₀ • (zzʷ e₀ x • H)                    ≈⟨ back (zzʷ a e₀) com ⟩
      zzʷ a e₀ • (H • zzʷ e₀ x)                    ≈⟨ sym assoc ⟩
      (zzʷ a e₀ • H) • zzʷ e₀ x                    ≈⟨ front (zzʷ e₀ x) F.std ⟩
      (H • (zzʷ a e₀ • zxʷ b b a)) • zzʷ e₀ x      ≈⟨ assoc ⟩
      H • ((zzʷ a e₀ • zxʷ b b a) • zzʷ e₀ x)      ≈⟨ back H fold ⟩
      H • (zzʷ a x • zxʷ b b a)                    ∎
      where
      e₀ : Fin N
      e₀ = F.e₀

      dv : Distinct (a ∷ b ∷ e₀ ∷ x ∷ [])
      dv = (≢sym ab ∷ F.e₀a ∷ xa ∷ []) ∷ᵈ (F.e₀b ∷ xb ∷ []) ∷ᵈ (ne ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ

      open At (lookup (a ∷ b ∷ e₀ ∷ x ∷ [])) (lookup-inj dv)

      split : zzʷ a x ≈ zzʷ a e₀ • zzʷ e₀ x
      split = A5-tmpl ⌜ tz ₀ ₃ ⌝ (⌜ tz ₀ ₂ ⌝ •ᵗ ⌜ tz ₂ ₃ ⌝) Eq.refl

      fold : (zzʷ a e₀ • zxʷ b b a) • zzʷ e₀ x ≈ zzʷ a x • zxʷ b b a
      fold = A5-tmpl ((⌜ tz ₀ ₂ ⌝ •ᵗ ⌜ ty ₁ ₁ ₀ ⌝) •ᵗ ⌜ tz ₂ ₃ ⌝)
                     (⌜ tz ₀ ₃ ⌝ •ᵗ ⌜ ty ₁ ₁ ₀ ⌝) Eq.refl

      com : zzʷ e₀ x • H ≈ H • zzʷ e₀ x
      com = comm-zz e65 a b c d ab ac ad bc bd cd e₀ x
                    F.e₀a F.e₀b F.e₀c F.e₀d xa xb xc xd

  -- The same for the second pair.
  std-any₂ : ∀ (a b c d x : Fin N) →
             a ≢ b → a ≢ c → a ≢ d → b ≢ c → b ≢ d → c ≢ d →
             x ≢ a → x ≢ b → x ≢ c → x ≢ d →
             zzʷ c x • hhʷ a b c d ≈ hhʷ a b c d • (zzʷ c x • zxʷ d d c)
  std-any₂ a b c d x ab ac ad bc bd cd xa xb xc xd = begin
    zzʷ c x • hhʷ a b c d                 ≈⟨ back (zzʷ c x) sw ⟩
    zzʷ c x • hhʷ c d a b                 ≈⟨ std-any c d a b x cd (≢sym ac) (≢sym bc)
                                                     (≢sym ad) (≢sym bd) ab xc xd xa xb ⟩
    hhʷ c d a b • (zzʷ c x • zxʷ d d c)   ≈⟨ front (zzʷ c x • zxʷ d d c) (sym sw) ⟩
    hhʷ a b c d • (zzʷ c x • zxʷ d d c)   ∎
    where
    sw : hhʷ a b c d ≈ hhʷ c d a b
    sw = eq66 e65 a b c d ab ac ad bc bd cd

  ----------------------------------------------------------------------
  -- The twisted pass

  hh-twist : ∀ (u u′ : W) → HFreeʷ u → HFreeʷ u′ → sp u ⊛ sp u′ ≗ idSP →
             ∀ (p q r s p′ q′ r′ s′ : Fin N) →
             prm (sp u) p ≡ p′ → prm (sp u) q ≡ q′ →
             prm (sp u) r ≡ r′ → prm (sp u) s ≡ s′ →
             ∀ (b₁ b₂ : Bool) →
             sgn (sp u) p xor sgn (sp u) q ≡ b₁ →
             sgn (sp u) r xor sgn (sp u) s ≡ b₂ →
             p ≢ q → p ≢ r → p ≢ s → q ≢ r → q ≢ s → r ≢ s →
             u • hhʷ p′ q′ r′ s′ ≈ hhʷ p q r s • κ b₁ p q (κ b₂ r s u)
  hh-twist u u′ hu hu′ inv p q r s p′ q′ r′ s′ ep eq er es b₁ b₂ e₁ e₂
           pq pr ps qr qs rs = go b₁ b₂ e₁ e₂
    where
    module F = Frame e65 p q r s pq pr ps qr qs rs

    x : Fin N
    x = F.e₀

    H H′ : W
    H  = hhʷ p q r s
    H′ = hhʷ p′ q′ r′ s′

    -- Flip signs with a sign pair Z, pass, and pay for the flip.
    via : ∀ (y z : Fin N) (C K : W) →
          sgn (sp (zzʷ y z • u)) p ≡ sgn (sp (zzʷ y z • u)) q →
          sgn (sp (zzʷ y z • u)) r ≡ sgn (sp (zzʷ y z • u)) s →
          zzʷ y z • H ≈ H • C → C • zzʷ y z ≈ K →
          u • H′ ≈ H • (K • u)
    via y z C K s₁ s₂ zH CZ = begin
      u • H′                     ≈⟨ front H′ (sym (zz-sq-w y z u)) ⟩
      (Z • (Z • u)) • H′         ≈⟨ assoc ⟩
      Z • ((Z • u) • H′)         ≈⟨ back Z pass ⟩
      Z • (H • (Z • u))          ≈⟨ sym assoc ⟩
      (Z • H) • (Z • u)          ≈⟨ front (Z • u) zH ⟩
      (H • C) • (Z • u)          ≈⟨ assoc ⟩
      H • (C • (Z • u))          ≈⟨ back H (sym assoc) ⟩
      H • ((C • Z) • u)          ≈⟨ back H (front u CZ) ⟩
      H • (K • u)                ∎
      where
      Z : W
      Z = zzʷ y z

      pass : (Z • u) • H′ ≈ H • (Z • u)
      pass = hh-pass e65 (Z • u) (u′ • Z) (cat (gen (hf-zz y z)) hu)
                     (cat hu′ (gen (hf-zz y z)))
                     (conj-inv (sp Z) (sp u) (sp u′) (zz-invol y z) inv)
                     p q r s p′ q′ r′ s′ ep eq er es s₁ s₂ pq pr ps qr qs rs

    -- The sign of `zz y z • u` at an index away from y and z.
    keep : ∀ (y z i : Fin N) → i ≢ y → i ≢ z →
           sgn (sp (zzʷ y z • u)) i ≡ sgn (sp u) i
    keep y z i iy iz = Eq.cong (_xor sgn (sp u) i) (δδ-off y z i iy iz)

    xp : x ≢ p
    xp = F.e₀a

    xq : x ≢ q
    xq = F.e₀b

    xr : x ≢ r
    xr = F.e₀c

    xs : x ≢ s
    xs = F.e₀d

    go : ∀ (b₁ b₂ : Bool) →
         sgn (sp u) p xor sgn (sp u) q ≡ b₁ →
         sgn (sp u) r xor sgn (sp u) s ≡ b₂ →
         u • H′ ≈ H • κ b₁ p q (κ b₂ r s u)
    go false false e₁ e₂ =
      hh-pass e65 u u′ hu hu′ inv p q r s p′ q′ r′ s′ ep eq er es
              (xf _ _ e₁) (xf _ _ e₂) pq pr ps qr qs rs
    go true false e₁ e₂ =
      via p x (zzʷ p x • zxʷ q q p) (zxʷ p p q)
          (Eq.trans (Eq.cong (_xor sgn (sp u) p) (δδ-fst p x (≢sym xp)))
                    (Eq.trans (xt _ _ e₁) (Eq.sym (keep p x q (≢sym pq) (≢sym xq)))))
          (Eq.trans (keep p x r (≢sym pr) (≢sym xr))
                    (Eq.trans (xf _ _ e₂) (Eq.sym (keep p x s (≢sym ps) (≢sym xs)))))
          (std-any p q r s x pq pr ps qr qs rs xp xq xr xs)
          fold
      where
      dv : Distinct (p ∷ q ∷ x ∷ [])
      dv = (≢sym pq ∷ xp ∷ []) ∷ᵈ (xq ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ

      open At (lookup (p ∷ q ∷ x ∷ [])) (lookup-inj dv)

      fold : (zzʷ p x • zxʷ q q p) • zzʷ p x ≈ zxʷ p p q
      fold = A5-tmpl ((⌜ tz ₀ ₂ ⌝ •ᵗ ⌜ ty ₁ ₁ ₀ ⌝) •ᵗ ⌜ tz ₀ ₂ ⌝) ⌜ ty ₀ ₀ ₁ ⌝ Eq.refl
    go false true e₁ e₂ =
      via r x (zzʷ r x • zxʷ s s r) (zxʷ r r s)
          (Eq.trans (keep r x p pr (≢sym xp))
                    (Eq.trans (xf _ _ e₁) (Eq.sym (keep r x q qr (≢sym xq)))))
          (Eq.trans (Eq.cong (_xor sgn (sp u) r) (δδ-fst r x (≢sym xr)))
                    (Eq.trans (xt _ _ e₂) (Eq.sym (keep r x s (≢sym rs) (≢sym xs)))))
          (std-any₂ p q r s x pq pr ps qr qs rs xp xq xr xs)
          fold
      where
      dv : Distinct (r ∷ s ∷ x ∷ [])
      dv = (≢sym rs ∷ xr ∷ []) ∷ᵈ (xs ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ

      open At (lookup (r ∷ s ∷ x ∷ [])) (lookup-inj dv)

      fold : (zzʷ r x • zxʷ s s r) • zzʷ r x ≈ zxʷ r r s
      fold = A5-tmpl ((⌜ tz ₀ ₂ ⌝ •ᵗ ⌜ ty ₁ ₁ ₀ ⌝) •ᵗ ⌜ tz ₀ ₂ ⌝) ⌜ ty ₀ ₀ ₁ ⌝ Eq.refl
    go true true e₁ e₂ =
      trans (via p r C (zxʷ p p q • zxʷ r r s)
          (Eq.trans (Eq.cong (_xor sgn (sp u) p) (δδ-fst p r pr))
                    (Eq.trans (xt _ _ e₁) (Eq.sym (keep p r q (≢sym pq) qr))))
          (Eq.trans (Eq.cong (_xor sgn (sp u) r) (δδ-snd p r (≢sym pr)))
                    (Eq.trans (xt _ _ e₂) (Eq.sym (keep p r s (≢sym ps) (≢sym rs)))))
          zH fold)
        (back H assoc)
      where
      C : W
      C = (zzʷ p x • zxʷ q q p) • (zzʷ r x • zxʷ s s r)

      dv : Distinct (p ∷ q ∷ r ∷ s ∷ x ∷ [])
      dv = (≢sym pq ∷ ≢sym pr ∷ ≢sym ps ∷ xp ∷ []) ∷ᵈ (≢sym qr ∷ ≢sym qs ∷ xq ∷ [])
          ∷ᵈ (≢sym rs ∷ xr ∷ []) ∷ᵈ (xs ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ

      open At (lookup (p ∷ q ∷ r ∷ s ∷ x ∷ [])) (lookup-inj dv)

      split : zzʷ p r ≈ zzʷ p x • zzʷ r x
      split = A5-tmpl ⌜ tz ₀ ₂ ⌝ (⌜ tz ₀ ₄ ⌝ •ᵗ ⌜ tz ₂ ₄ ⌝) Eq.refl

      zH : zzʷ p r • H ≈ H • C
      zH = begin
        zzʷ p r • H                                              ≈⟨ front H split ⟩
        (zzʷ p x • zzʷ r x) • H                                  ≈⟨ assoc ⟩
        zzʷ p x • (zzʷ r x • H)                                  ≈⟨ back (zzʷ p x)
                                                                      (std-any₂ p q r s x pq pr ps qr qs rs xp xq xr xs) ⟩
        zzʷ p x • (H • (zzʷ r x • zxʷ s s r))                    ≈⟨ sym assoc ⟩
        (zzʷ p x • H) • (zzʷ r x • zxʷ s s r)                    ≈⟨ front (zzʷ r x • zxʷ s s r)
                                                                      (std-any p q r s x pq pr ps qr qs rs xp xq xr xs) ⟩
        (H • (zzʷ p x • zxʷ q q p)) • (zzʷ r x • zxʷ s s r)      ≈⟨ assoc ⟩
        H • C                                                    ∎

      fold : C • zzʷ p r ≈ zxʷ p p q • zxʷ r r s
      fold = A5-tmpl (((⌜ tz ₀ ₄ ⌝ •ᵗ ⌜ ty ₁ ₁ ₀ ⌝) •ᵗ (⌜ tz ₂ ₄ ⌝ •ᵗ ⌜ ty ₃ ₃ ₂ ⌝))
                        •ᵗ ⌜ tz ₀ ₂ ⌝)
                     (⌜ ty ₀ ₀ ₁ ⌝ •ᵗ ⌜ ty ₂ ₂ ₃ ⌝) Eq.refl
