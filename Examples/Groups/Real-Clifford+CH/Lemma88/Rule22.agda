------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.8 on rule (22) of Figure 8 (Clément, Appendix E.5)
--
-- (22) is zz a b • zz b c = zz a c.  The decoding of zz x y is the
-- chain of the boxes of the consecutive indices from the smaller of x,
-- y to the larger (Decoding.dZZ).  Each box of a chain is a placed
-- coloured box (Lemma84's MI at distance one, its box wire the first
-- 0 bit of the index), so any two commute — (335) and (336) placed,
-- BoxAnywhere — and each is an involution.  Writing S x for the chain
-- from 0 to x, the decoding of zz x y is then S x • S y whichever of x,
-- y is larger, the common part cancelling, so the rule is
-- S a • S b • S b • S c = S a • S c.  The decodings are reversed, which
-- an involution does not see.  The paper distinguishes the six orders of
-- a, b and c; the prefix chains S make one argument of them.
--
-- Parameters: the canonical box facts and (335), (336) at the width.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Col using (C335 ; C336)

module Examples.Groups.Real-Clifford+CH.Lemma88.Rule22
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  {m : ℕ} (C : Canon m) (c335 : C335 m) (c336 : C336 m)
  where

open import Data.Bool using (Bool ; true ; false ; T ; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ<)
open import Data.Nat using (zero ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<ᵇ_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (+-comm ; +-suc ; +-identityʳ ; m+[n∸m]≡n ; <⇒≤ ; ≤-trans ; ≤-<-trans ; m≤m+n ; suc-injective ;
         m≤n⇒m<n∨m≡n ; <ᵇ⇒< ; <⇒<ᵇ ; ≮⇒≥ ; 0≢1+n)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_ ; replicate)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Notations using (₂₊ ; ₃₊)

open import Presentation.GroupLike using (module Group-Lemmas)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.Reverse using (rev ; rev≈⁻¹)
open import Examples.Groups.Real-Clifford+CH.PermCalc using (perm)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (toBits ; fromBits ; fromBits-toBits ; gray)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep
  using (incr ; firstZero ; incr-first ; toBits-suc ; compl)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (mc□)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (−1−1)
open import Examples.Groups.Real-Clifford+CH.Encoding using (zz)
open import Examples.Groups.Real-Clifford+CH.Decoding using (d ; dZZ ; dZZ-chain ; dZZ₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts using (layoutAt)
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires using (sdS ; sd-target ; negsB ; negs² ; net-inv)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (module Frames ; pl ; pl-• ; pl-cong)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Lemma84 C using (MI ; mc□-boxF)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxAnywhere complete₂ complete₃ using (module Anywhere)

open Frames C using (boxF)
open Anywhere C c335 c336 using (boxes-comm)

private
  N : ℕ
  N = ₃₊ m

  I : Set
  I = Fin (2 ^ N)

open Tools (N VRel,_===_)
open Group-Lemmas (N VRel,_===_) grouplike using (inverseʳ-unique)

private
  ------------------------------------------------------------------
  -- The first 0 of an index that has a successor

  fz≤ : ∀ {n} (s : Bits n) → firstZero s ≤ n
  fz≤ []          = z≤n
  fz≤ (false ∷ s) = z≤n
  fz≤ (true ∷ s)  = s≤s (fz≤ s)

  incr-full : ∀ {n} (s : Bits n) → firstZero s ≡ n → incr s ≡ replicate n false
  incr-full []          _  = Eq.refl
  incr-full (true ∷ s)  e  = Eq.cong (false ∷_) (incr-full s (suc-injective e))

  toBits-0 : ∀ n → toBits n 0 ≡ replicate n false
  toBits-0 zero    = Eq.refl
  toBits-0 (suc n) = Eq.cong (false ∷_) (toBits-0 n)

  fz< : ∀ i → suc i < 2 ^ N → firstZero (toBits N i) < N
  fz< i bnd with m≤n⇒m<n∨m≡n (fz≤ (toBits N i))
  ... | inj₁ lt = lt
  ... | inj₂ eq = ⊥-elim (0≢1+n (Eq.trans (Eq.sym (fromBits-toBits N 0 pos))
                                   (Eq.trans (Eq.cong fromBits e) (fromBits-toBits N (suc i) bnd))))
    where
    pos : 0 < 2 ^ N
    pos = ≤-trans (s≤s z≤n) (<⇒≤ bnd)
    e : toBits N 0 ≡ toBits N (suc i)
    e = Eq.trans (toBits-0 N) (Eq.sym (Eq.trans (toBits-suc N i) (incr-full (toBits N i) eq)))

  lookup-fz : ∀ {n} (s : Bits n) → firstZero s < n → lookupℕ (firstZero s) s ≡ false
  lookup-fz (false ∷ s) _       = Eq.refl
  lookup-fz (true ∷ s)  (s≤s p) = lookup-fz s p

  ------------------------------------------------------------------
  -- Each box of a chain is a placed box

  tw : ∀ i → suc i < 2 ^ N → Fin N
  tw i bnd = fromℕ< (fz< i bnd)

  box-i : ∀ i (bnd : suc i < 2 ^ N) → dZZ₁ {m} i ≈ boxF (sdS (toℕ (tw i bnd))) (gray (toBits N i))
  box-i i bnd = begin
    dZZ₁ i                                   ≈⟨ sym right-unit ⟩
    dZZ-chain i 1                            ≈⟨ MI 1 i t t<N (lookup-fz (toBits N i) t<N) E bnd′ ⟩
    mc□ (layoutAt t (gray (toBits N i)))     ≈⟨ mc□-boxF t t<N (gray (toBits N i)) ⟩
    boxF (sdS t) (gray (toBits N i))         ≈⟨ ≡→≈ (Eq.cong (λ v → boxF (sdS v) (gray (toBits N i))) (Eq.sym (toℕ-fromℕ< t<N))) ⟩
    boxF (sdS (toℕ (tw i bnd))) (gray (toBits N i)) ∎
    where
    t : ℕ
    t = firstZero (toBits N i)
    t<N : t < N
    t<N = fz< i bnd
    bnd′ : i + 1 < 2 ^ N
    bnd′ = Eq.subst (_< 2 ^ N) (+-comm 1 i) bnd
    E : toBits N (i + 1) ≡ compl t (toBits N i)
    E = Eq.trans (Eq.cong (toBits N) (+-comm i 1)) (Eq.trans (toBits-suc N i) (incr-first (toBits N i) t<N))
    ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
    ≡→≈ Eq.refl = refl

  box-comm : ∀ i j → suc i < 2 ^ N → suc j < 2 ^ N → dZZ₁ {m} i • dZZ₁ j ≈ dZZ₁ j • dZZ₁ i
  box-comm i j bi bj = begin
    dZZ₁ i • dZZ₁ j   ≈⟨ cong (box-i i bi) (box-i j bj) ⟩
    Bi • Bj           ≈⟨ boxes-comm (sdS (toℕ (tw i bi))) (sdS (toℕ (tw j bj))) (tw i bi) (tw j bj)
                                    (sd-target (tw i bi)) (sd-target (tw j bj)) (gray (toBits N i)) (gray (toBits N j)) ⟩
    Bj • Bi           ≈⟨ sym (cong (box-i j bj) (box-i i bi)) ⟩
    dZZ₁ j • dZZ₁ i ∎
    where
    Bi Bj : Circuit N
    Bi = boxF (sdS (toℕ (tw i bi))) (gray (toBits N i))
    Bj = boxF (sdS (toℕ (tw j bj))) (gray (toBits N j))

  box² : ∀ i → suc i < 2 ^ N → dZZ₁ {m} i • dZZ₁ i ≈ ε
  box² i bi = trans (cong (box-i i bi) (box-i i bi)) (boxF² (sdS (toℕ (tw i bi))) (gray (toBits N i)))
    where
    boxF² : ∀ u s → boxF u s • boxF u s ≈ ε
    boxF² u s = begin
      (M • A • M) • (M • A • M)       ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • ((□ • □) • □ • □)) Eq.refl ⟩
      M • A • ((M • M) • A • M)       ≈⟨ back _ (back _ (trans (front _ (negs² s)) left-unit)) ⟩
      M • A • (A • M)                 ≈⟨ back _ (trans (sym assoc) (front _ AA)) ⟩
      M • ε • M                       ≈⟨ back _ left-unit ⟩
      M • M                           ≈⟨ negs² s ⟩
      ε ∎
      where
      M A : Circuit N
      M = negsB s
      A = pl u (Λ□ (₂₊ m))
      AA : A • A ≈ ε
      AA = trans (sym (pl-• u (Λ□ (₂₊ m)) (Λ□ (₂₊ m))))
                 (trans (pl-cong u (Canon.invol C)) (trans (back _ left-unit) (net-inv u)))

  pass : ∀ {a u v : Circuit N} → a • u ≈ u • a → a • v ≈ v • a → a • (u • v) ≈ (u • v) • a
  pass eu ev = trans (sym assoc) (trans (front _ eu) (trans assoc (trans (back _ ev) (sym assoc))))

  passL : ∀ {x u y : Circuit N} → x • y ≈ y • x → u • y ≈ y • u → (x • u) • y ≈ y • (x • u)
  passL ex eu = trans assoc (trans (back _ eu) (trans (sym assoc) (trans (front _ ex) assoc)))

  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

  ------------------------------------------------------------------
  -- Chains of boxes

  ch : ℕ → ℕ → Circuit N
  ch = dZZ-chain {m}

  -- The boxes of a chain ending below 2 ^ N are boxes.
  first : ∀ a d → a + suc d < 2 ^ N → suc a < 2 ^ N
  first a d b = ≤-<-trans (Eq.subst (suc a ≤_) (Eq.sym (+-suc a d)) (s≤s (m≤m+n a d))) b

  rest : ∀ a d → a + suc d < 2 ^ N → suc a + d < 2 ^ N
  rest a d b = Eq.subst (_< 2 ^ N) (+-suc a d) b

  chain-box : ∀ i a d → suc i < 2 ^ N → a + d < 2 ^ N → dZZ₁ {m} i • ch a d ≈ ch a d • dZZ₁ i
  chain-box i a zero    bi b = trans right-unit (sym left-unit)
  chain-box i a (suc d) bi b = pass (box-comm i a bi (first a d b)) (chain-box i (suc a) d bi (rest a d b))

  chain-comm : ∀ a d a′ d′ → a + d < 2 ^ N → a′ + d′ < 2 ^ N → ch a d • ch a′ d′ ≈ ch a′ d′ • ch a d
  chain-comm a zero    a′ d′ b b′ = trans left-unit (sym right-unit)
  chain-comm a (suc d) a′ d′ b b′ =
    passL (chain-box a a′ d′ (first a d b) b′) (chain-comm (suc a) d a′ d′ (rest a d b) b′)

  chain² : ∀ a d → a + d < 2 ^ N → ch a d • ch a d ≈ ε
  chain² a zero    _ = left-unit
  chain² a (suc d) b = begin
    (B • R) • (B • R)      ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) Eq.refl ⟩
    B • ((R • B) • R)      ≈⟨ back _ (front _ (sym (chain-box a (suc a) d (first a d b) (rest a d b)))) ⟩
    B • ((B • R) • R)      ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
    (B • B) • (R • R)      ≈⟨ cong (box² a (first a d b)) (chain² (suc a) d (rest a d b)) ⟩
    ε • ε                  ≈⟨ left-unit ⟩
    ε ∎
    where
    B R : Circuit N
    B = dZZ₁ a
    R = ch (suc a) d

  chain-split : ∀ a d e → ch a (d + e) ≈ ch a d • ch (a + d) e
  chain-split a zero    e = Eq.subst (λ v → ch a e ≈ ε • ch v e) (Eq.sym (+-identityʳ a)) (sym left-unit)
  chain-split a (suc d) e = begin
    dZZ₁ a • ch (suc a) (d + e)                    ≈⟨ back _ (chain-split (suc a) d e) ⟩
    dZZ₁ a • (ch (suc a) d • ch (suc a + d) e)     ≈⟨ sym assoc ⟩
    (dZZ₁ a • ch (suc a) d) • ch (suc a + d) e     ≈⟨ ≡→≈ (Eq.cong (λ v → (dZZ₁ a • ch (suc a) d) • ch v e) (Eq.sym (+-suc a d))) ⟩
    (dZZ₁ a • ch (suc a) d) • ch (a + suc d) e ∎

  ------------------------------------------------------------------
  -- Prefix chains

  S : ℕ → Circuit N
  S x = ch 0 x

  S-split : ∀ x y → x ≤ y → S y ≈ S x • ch x (y ∸ x)
  S-split x y x≤y = Eq.subst (λ v → ch 0 v ≈ S x • ch x (y ∸ x)) (m+[n∸m]≡n x≤y) (chain-split 0 x (y ∸ x))

  -- The decoding of a sign pair is the product of the two prefix chains.
  dZZ-S : ∀ x y → x < 2 ^ N → y < 2 ^ N → dZZ {m} x y ≈ S x • S y
  dZZ-S x y bx by = go (x <ᵇ y) Eq.refl
    where
    lt-case : x < y → ch x (y ∸ x) ≈ S x • S y
    lt-case lt = sym (begin
      S x • S y                     ≈⟨ back _ (S-split x y (<⇒≤ lt)) ⟩
      S x • (S x • ch x (y ∸ x))    ≈⟨ sym assoc ⟩
      (S x • S x) • ch x (y ∸ x)    ≈⟨ front _ (chain² 0 x bx) ⟩
      ε • ch x (y ∸ x)              ≈⟨ left-unit ⟩
      ch x (y ∸ x) ∎)

    ge-case : y ≤ x → ch y (x ∸ y) ≈ S x • S y
    ge-case y≤x = sym (begin
      S x • S y                     ≈⟨ front _ (S-split y x y≤x) ⟩
      (S y • K) • S y               ≈⟨ assoc ⟩
      S y • (K • S y)               ≈⟨ back _ (chain-comm y (x ∸ y) 0 y bK by) ⟩
      S y • (S y • K)               ≈⟨ sym assoc ⟩
      (S y • S y) • K               ≈⟨ front _ (chain² 0 y by) ⟩
      ε • K                         ≈⟨ left-unit ⟩
      K ∎)
      where
      K : Circuit N
      K = ch y (x ∸ y)
      bK : y + (x ∸ y) < 2 ^ N
      bK = Eq.subst (_< 2 ^ N) (Eq.sym (m+[n∸m]≡n y≤x)) bx

    go : ∀ c → (x <ᵇ y) ≡ c → dZZ {m} x y ≈ S x • S y
    go true  e = Eq.subst (λ c → (if c then ch x (y ∸ x) else ch y (x ∸ y)) ≈ S x • S y) (Eq.sym e)
                   (lt-case (<ᵇ⇒< x y (Eq.subst T (Eq.sym e) tt)))
    go false e = Eq.subst (λ c → (if c then ch x (y ∸ x) else ch y (x ∸ y)) ≈ S x • S y) (Eq.sym e)
                   (ge-case (≮⇒≥ (λ lt → Eq.subst T e (<⇒<ᵇ lt))))

  dZZ² : ∀ x y → x < 2 ^ N → y < 2 ^ N → dZZ {m} x y • dZZ x y ≈ ε
  dZZ² x y bx by = begin
    dZZ x y • dZZ x y           ≈⟨ cong (dZZ-S x y bx by) (dZZ-S x y bx by) ⟩
    (S x • S y) • (S x • S y)   ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • ((□ • □) • □)) Eq.refl ⟩
    S x • ((S y • S x) • S y)   ≈⟨ back _ (front _ (chain-comm 0 y 0 x by bx)) ⟩
    S x • ((S x • S y) • S y)   ≈⟨ by-passoc (□ • ((□ • □) • □)) ((□ • □) • (□ • □)) Eq.refl ⟩
    (S x • S x) • (S y • S y)   ≈⟨ cong (chain² 0 x bx) (chain² 0 y by) ⟩
    ε • ε                       ≈⟨ left-unit ⟩
    ε ∎

  rev-dZZ : ∀ x y → x < 2 ^ N → y < 2 ^ N → rev (dZZ {m} x y) ≈ dZZ x y
  rev-dZZ x y bx by = trans (rev≈⁻¹ (dZZ x y)) (sym (inverseʳ-unique (dZZ² x y bx by)))

------------------------------------------------------------------------
-- (22)

e22 : ∀ (a b c : I) → (d ʷ) (zz {N} a b • zz b c) ≈ (d ʷ) (zz a c)
e22 a b c = begin
  rev (dZZ x y) • rev (dZZ y z)       ≈⟨ cong (rev-dZZ x y bx by) (rev-dZZ y z by bz) ⟩
  dZZ x y • dZZ y z                   ≈⟨ cong (dZZ-S x y bx by) (dZZ-S y z by bz) ⟩
  (S x • S y) • (S y • S z)           ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  S x • (S y • S y) • S z             ≈⟨ back _ (trans (front _ (chain² 0 y by)) left-unit) ⟩
  S x • S z                           ≈⟨ sym (dZZ-S x z bx bz) ⟩
  dZZ x z                             ≈⟨ sym (rev-dZZ x z bx bz) ⟩
  rev (dZZ x z) ∎
  where
  x y z : ℕ
  x = toℕ a
  y = toℕ b
  z = toℕ c
  bx : x < 2 ^ N
  bx = toℕ<n a
  by : y < 2 ^ N
  by = toℕ<n b
  bz : z < 2 ^ N
  bz = toℕ<n c
