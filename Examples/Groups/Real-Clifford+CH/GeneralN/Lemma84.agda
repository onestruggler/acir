------------------------------------------------------------------------
-- Presentations of groups
--
-- Lemma 8.4: the decoding of a sign pair on two Gray neighbours is one
-- box (Clément, Appendix E.2)
--
-- For a code G and a wire t, the indices of G and of G with the bit t
-- flipped carry the letter (−1)[a] (−1)[b], which Definition 8.3
-- decodes as the product of the boxes of the consecutive indices from
-- the smaller to the larger (`Decoding.dZZ-chain`); Lemma 8.4 says it is
-- the one box on wire t, the other bits of G as controls (`lemma84`).
--
-- The proof is the paper's induction on the distance, in binary: the
-- two indices a < b differ by complementing the bits 0 … t (`GrayStep`),
-- a + 1 complements a's bits up to its first 0, at a wire z < t unless
-- b = a + 1, and b − 1 then does the same to b; so a + 1, b − 1 is a
-- pair of the same kind two closer (`MI`), and the chain is
--
--   box(z; G) • box(t; G flipped at z) • box(z; G flipped at t),
--
-- which is BoxFrames' three-box step.  Everything rests on the record
-- `Canon` of facts about the box at the canonical position, so the
-- lemma holds at every width at which those do.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFrames using (Canon ; module Frames ; pl)

module Examples.Groups.Real-Clifford+CH.GeneralN.Lemma84 {m : ℕ} (C : Canon m) where

open import Data.Bool using (Bool ; true ; false ; not ; if_then_else_)
open import Data.Bool.Properties using (not-involutive ; not-¬)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; fromℕ<) renaming (zero to 0F ; suc to sF)
open import Data.Fin.Properties using (toℕ<n ; toℕ-fromℕ<)
open import Data.Nat using (zero ; suc ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<ᵇ_ ; _^_ ; s≤s ; z≤n)
open import Data.Nat.Properties
  using (+-suc ; +-identityʳ ; +-comm ; m≢1+m+n ; m≤m+n ; m+[n∸m]≡n ; <⇒≤ ; ≤-trans ; ≤-reflexive ;
         <-transʳ ; m≤n⇒m<n∨m≡n ; suc-injective ; <-irrefl)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁ ; inj₂)
open import Data.Vec using (Vec ; [] ; _∷_ ; zipWith)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_)

open import Notations using (₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics.Algebra using (Bits)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (mc□ ; negs ; tgtWire ; shiftDown ; shiftUp)
open import Examples.Groups.Real-Clifford+CH.Decoding using (dZZ ; dZZ-chain ; dZZ₁ ; slot ; gcode ; layout□)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray
  using (toBits ; fromBits ; gray ; ungray ; hd ; parity ; index ; toBits-fromBits ; fromBits-toBits ;
         fromBits<2^n ; gray-ungray ; ungray-gray)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Bitstrings using (lookupℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.GrayStep
open import Examples.Groups.Real-Clifford+CH.GeneralN.NetWires
  using (sdS ; suS ; revS ; net-sdS ; net-suS ; revS-sdS ; sd-target ; negsB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Layouts
open import Examples.Groups.Real-Clifford+CH.PermCalc using (net ; perm)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)

open Frames C

private
  N : ℕ
  N = ₃₊ m

open Tools (N VRel,_===_)

private
  ≡→≈ : ∀ {a b : Circuit N} → a ≡ b → a ≈ b
  ≡→≈ Eq.refl = refl

------------------------------------------------------------------------
-- A layout box is a placed box

mc□-boxF : ∀ i → i < N → (s : Bits N) → mc□ (layoutAt i s) ≈ boxF (sdS i) s
mc□-boxF i i<N s = trans step₁ step₂
  where
  iF : Fin N
  iF = fromℕ< i<N

  ti : toℕ iF ≡ i
  ti = toℕ-fromℕ< i<N

  target : perm (sdS i) ⟨$⟩ʳ iF ≡ 0F
  target = Eq.subst (λ j → perm (sdS j) ⟨$⟩ʳ iF ≡ 0F)
                    ti (sd-target iF)

  s′ : Bits N
  s′ = setT i s

  e₁ : mc□ (layoutAt i s) ≡ negsB s′ • shiftDown i • Λ□ (₂₊ m) • shiftUp i • negsB s′
  e₁ = Eq.cong₂ (λ w j → w • shiftDown j • Λ□ (₂₊ m) • shiftUp j • w) (negs-at i s) (tgtWire-at i s i<N)

  e₂ : net (sdS {N} i) ≡ shiftDown i
  e₂ = net-sdS i

  e₃ : net (revS (sdS {N} i)) ≡ shiftUp i
  e₃ = Eq.trans (Eq.cong net (revS-sdS i)) (net-suS i)

  step₁ : mc□ (layoutAt i s) ≈ boxF (sdS i) s′
  step₁ = Eq.subst (_≈ boxF (sdS i) s′) (Eq.sym e₁)
            (Eq.subst₂ (λ a b → negsB s′ • a • Λ□ (₂₊ m) • b • negsB s′ ≈ boxF (sdS i) s′) e₂ e₃
              (by-passoc (□ • □ • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl))

  step₂ : boxF (sdS i) s′ ≈ boxF (sdS i) s
  step₂ with setT-cases i s
  ... | inj₁ e = ≡→≈ (Eq.cong (boxF (sdS i)) e)
  ... | inj₂ e = Eq.subst (λ w → boxF (sdS i) w ≈ boxF (sdS i) s) (Eq.sym e)
                   (Eq.subst (λ j → boxF (sdS i) (flipAt j s) ≈ boxF (sdS i) s) ti
                     (boxF-flip (sdS i) iF target s))

-- The three-box step with the wires as numbers.
three-boxesℕ : ∀ p q → p < N → q < N → p ≢ q → (s : Bits N) →
               boxF (sdS q) s • boxF (sdS p) (flipAt q s) • boxF (sdS q) (flipAt p s) ≈ boxF (sdS p) s
three-boxesℕ p q p<N q<N p≢q s =
  Eq.subst₂ (λ x y → boxF (sdS y) s • boxF (sdS x) (flipAt y s) • boxF (sdS y) (flipAt x s) ≈ boxF (sdS x) s)
            tp tq
            (three-boxes (sdS (toℕ qF)) (sdS (toℕ pF)) pF qF pF≢qF (sd-target qF) (sd-target pF) s)
  where
  pF qF : Fin N
  pF = fromℕ< p<N
  qF = fromℕ< q<N
  tp : toℕ pF ≡ p
  tp = toℕ-fromℕ< p<N
  tq : toℕ qF ≡ q
  tq = toℕ-fromℕ< q<N
  pF≢qF : pF ≢ qF
  pF≢qF e = p≢q (Eq.trans (Eq.sym tp) (Eq.trans (Eq.cong toℕ e) tq))

------------------------------------------------------------------------
-- The chain

chain-snoc : ∀ a d → dZZ-chain {m} a (suc d) ≈ dZZ-chain a d • dZZ₁ (a + d)
chain-snoc a zero = begin
  dZZ₁ a • ε            ≈⟨ right-unit ⟩
  dZZ₁ a                ≈⟨ sym left-unit ⟩
  ε • dZZ₁ a            ≈⟨ back _ (≡→≈ (Eq.cong dZZ₁ (Eq.sym (+-identityʳ a)))) ⟩
  ε • dZZ₁ (a + 0) ∎
chain-snoc a (suc d) = begin
  dZZ₁ a • dZZ-chain (suc a) (suc d)                  ≈⟨ back _ (chain-snoc (suc a) d) ⟩
  dZZ₁ a • (dZZ-chain (suc a) d • dZZ₁ (suc a + d))   ≈⟨ sym assoc ⟩
  (dZZ₁ a • dZZ-chain (suc a) d) • dZZ₁ (suc a + d)   ≈⟨ back _ (≡→≈ (Eq.cong dZZ₁ (Eq.sym (+-suc a d)))) ⟩
  (dZZ₁ a • dZZ-chain (suc a) d) • dZZ₁ (a + suc d) ∎

private
  toBits-inj : ∀ {a b} → a < 2 ^ N → b < 2 ^ N → toBits N a ≡ toBits N b → a ≡ b
  toBits-inj {a} {b} a< b< e =
    Eq.trans (Eq.sym (fromBits-toBits N a a<)) (Eq.trans (Eq.cong fromBits e) (fromBits-toBits N b b<))

  -- Parity at the bottom bit, for the two impossible distances.
  not-self : ∀ {b} → b ≡ not b → ∀ {A : Set} → A
  not-self {b} e = ⊥-elim (not-¬ {b} {b} Eq.refl e)

  -- The layout of the box for a and a + 1 when a + 1 complements a up to z.
  layout-step : ∀ a z → z < N → toBits N (suc a) ≡ compl z (toBits N a) →
                layout□ {m} a ≡ layoutAt z (gray (toBits N a))
  layout-step a z z<N e =
    Eq.trans (Eq.cong (zipWith slot (gcode a)) (Eq.trans (Eq.cong gray e) (gray-compl z (toBits N a) z<N)))
             (zip-flip z (gray (toBits N a)) z<N)

------------------------------------------------------------------------
-- The induction

-- From a, whose bit t is 0, to a + e, which is a with the bits 0 … t
-- complemented.
MI : ∀ e a t → t < N → lookupℕ t (toBits N a) ≡ false →
     toBits N (a + e) ≡ compl t (toBits N a) → a + e < 2 ^ N →
     dZZ-chain {m} a e ≈ mc□ (layoutAt t (gray (toBits N a)))
MI zero a t t<N lt E bnd = not-self (Eq.trans (Eq.cong hd e₀) (hd-compl t (parity a) _))
  where
  e₀ : toBits N a ≡ compl t (toBits N a)
  e₀ = Eq.trans (Eq.cong (toBits N) (Eq.sym (+-identityʳ a))) E
MI (suc zero) a t t<N lt E bnd = begin
  dZZ₁ a • ε                          ≈⟨ right-unit ⟩
  mc□ (layout□ a)                     ≈⟨ ≡→≈ (Eq.cong mc□ (layout-step a t t<N e₁)) ⟩
  mc□ (layoutAt t (gray (toBits N a))) ∎
  where
  e₁ : toBits N (suc a) ≡ compl t (toBits N a)
  e₁ = Eq.trans (Eq.cong (toBits N) (Eq.trans (Eq.sym (+-identityʳ (suc a))) (Eq.sym (+-suc a 0)))) E
MI (suc (suc zero)) a t t<N lt E bnd =
  not-self (Eq.trans (Eq.sym (not-involutive (parity a)))
             (Eq.trans (Eq.cong hd e₂) (hd-compl t (parity a) _)))
  where
  e₂ : toBits N (suc (suc a)) ≡ compl t (toBits N a)
  e₂ = Eq.trans (Eq.cong (toBits N) (Eq.sym (Eq.trans (+-suc a 1) (Eq.cong suc (Eq.trans (+-suc a 0) (Eq.cong suc (+-identityʳ a))))))) E
MI (suc (suc (suc e))) a t t<N lt E bnd with m≤n⇒m<n∨m≡n (firstZero-≤ t (toBits N a) lt t<N)
... | inj₂ z≡t = ⊥-elim (m≢1+m+n a (suc-injective (Eq.trans a+d≡ idx)))
  where
  A : Bits N
  A = toBits N a
  sa : toBits N (suc a) ≡ compl t A
  sa = Eq.trans (toBits-suc N a)
         (Eq.trans (incr-first A (Eq.subst (_< N) (Eq.sym z≡t) t<N)) (Eq.cong (λ j → compl j A) z≡t))
  idx : a + suc (suc (suc e)) ≡ suc (suc (a + suc e))
  idx = Eq.trans (+-suc a (suc (suc e))) (Eq.cong suc (+-suc a (suc e)))
  sa< : suc a < 2 ^ N
  sa< = ≤-trans (s≤s (≤-trans (s≤s (m≤m+n a (suc (suc e)))) (≤-reflexive (Eq.sym (+-suc a (suc (suc e))))))) bnd
  a+d≡ : suc a ≡ a + suc (suc (suc e))
  a+d≡ = toBits-inj sa< bnd (Eq.trans sa (Eq.sym E))
... | inj₁ z<t = begin
  dZZ₁ a • dZZ-chain (suc a) (suc (suc e))
    ≈⟨ back _ (chain-snoc (suc a) (suc e)) ⟩
  dZZ₁ a • (dZZ-chain (suc a) (suc e) • dZZ₁ (suc a + suc e))
    ≈⟨ cong (≡→≈ (Eq.cong mc□ (layout-step a z z<N A1≡)))
            (cong (MI (suc e) (suc a) t t<N lt1 T1 b1) (≡→≈ (Eq.cong mc□ L3))) ⟩
  mc□ (layoutAt z G) • (mc□ (layoutAt t (gray (toBits N (suc a)))) • mc□ (layoutAt z (flipAt t G)))
    ≈⟨ cong (mc□-boxF z z<N G) (cong (trans (≡→≈ (Eq.cong (λ w → mc□ (layoutAt t w)) G1))
                                           (mc□-boxF t t<N (flipAt z G)))
                                     (mc□-boxF z z<N (flipAt t G))) ⟩
  boxF (sdS z) G • (boxF (sdS t) (flipAt z G) • boxF (sdS z) (flipAt t G))
    ≈⟨ three-boxesℕ t z t<N z<N (λ e → <-irrefl′ (Eq.subst (_< t) (Eq.sym e) z<t)) G ⟩
  boxF (sdS t) G
    ≈⟨ sym (mc□-boxF t t<N G) ⟩
  mc□ (layoutAt t G) ∎
  where
  A : Bits N
  A = toBits N a
  G : Bits N
  G = gray A
  z : ℕ
  z = firstZero A
  z<N : z < N
  z<N = <-transʳ (<⇒≤ z<t) t<N

  <-irrefl′ : t < t → ∀ {B : Set} → B
  <-irrefl′ p = ⊥-elim (<-irrefl Eq.refl p)

  -- a + 1: complemented up to z.
  A1≡ : toBits N (suc a) ≡ compl z A
  A1≡ = Eq.trans (toBits-suc N a) (incr-first A z<N)
  G1 : gray (toBits N (suc a)) ≡ flipAt z G
  G1 = Eq.trans (Eq.cong gray A1≡) (gray-compl z A z<N)

  lt1 : lookupℕ t (toBits N (suc a)) ≡ false
  lt1 = Eq.trans (Eq.cong (lookupℕ t) A1≡) (Eq.trans (lookup-compl-hi z t A z<t) lt)

  idx : suc (suc a + suc e) ≡ a + suc (suc (suc e))
  idx = Eq.sym (Eq.trans (+-suc a (suc (suc e))) (Eq.cong suc (+-suc a (suc e))))

  -- b − 1 = a + 1 + (1 + e): complemented up to t from a + 1.
  X′ : Bits N
  X′ = compl t (compl z A)
  fzX : firstZero X′ ≡ z
  fzX = firstZero-cc z t A Eq.refl z<t t<N
  incrX : incr X′ ≡ compl t A
  incrX = Eq.trans (incr-first X′ (Eq.subst (_< N) (Eq.sym fzX) z<N))
            (Eq.trans (Eq.cong (λ j → compl j X′) fzX)
              (Eq.trans (compl-comm z t (compl z A)) (Eq.cong (compl t) (compl-invol z A))))
  T1 : toBits N (suc a + suc e) ≡ compl t (toBits N (suc a))
  T1 = incr-inj (Eq.trans (Eq.sym (toBits-suc N (suc a + suc e)))
                  (Eq.trans (Eq.cong (toBits N) idx)
                    (Eq.trans E (Eq.sym (Eq.trans (Eq.cong (λ w → incr (compl t w)) A1≡) incrX)))))
  b1 : suc a + suc e < 2 ^ N
  b1 = Eq.subst (_≤ 2 ^ N) (Eq.sym idx) (<⇒≤ bnd)

  -- The last box: the codes of b − 1 and b.
  L3 : layout□ {m} (suc a + suc e) ≡ layoutAt z (flipAt t G)
  L3 = Eq.trans (Eq.cong₂ (zipWith slot) c₁ c₂) (zip-flip′ z (flipAt t G) z<N)
    where
    c₁ : gcode (suc a + suc e) ≡ flipAt z (flipAt t G)
    c₁ = Eq.trans (Eq.cong gray T1)
           (Eq.trans (gray-compl t (toBits N (suc a)) t<N)
             (Eq.trans (Eq.cong (flipAt t) G1) (flipAt-comm t z G)))
    c₂ : gcode (suc (suc a + suc e)) ≡ flipAt t G
    c₂ = Eq.trans (Eq.cong (λ k → gray (toBits N k)) idx)
           (Eq.trans (Eq.cong gray E) (gray-compl t A t<N))

------------------------------------------------------------------------
-- Lemma 8.4

private
  lt-true : ∀ a b → a < b → (a <ᵇ b) ≡ true
  lt-true zero    (suc b) _       = Eq.refl
  lt-true (suc a) (suc b) (s≤s p) = lt-true a b p

  ge-false : ∀ a b → b ≤ a → (a <ᵇ b) ≡ false
  ge-false a       zero    _       = Eq.refl
  ge-false (suc a) (suc b) (s≤s p) = ge-false a b p

  dZZ-lt : ∀ {a b} → a < b → dZZ {m} a b ≡ dZZ-chain a (b ∸ a)
  dZZ-lt {a} {b} p =
    Eq.cong (λ x → if x then dZZ-chain {m} a (b ∸ a) else dZZ-chain b (a ∸ b)) (lt-true a b p)

  dZZ-gt : ∀ {a b} → b < a → dZZ {m} a b ≡ dZZ-chain b (a ∸ b)
  dZZ-gt {a} {b} p =
    Eq.cong (λ x → if x then dZZ-chain {m} a (b ∸ a) else dZZ-chain b (a ∸ b)) (ge-false a b (<⇒≤ p))

lemma84 : ∀ (t : Fin N) (G : Bits N) →
          dZZ {m} (toℕ (index N G)) (toℕ (index N (flipAt (toℕ t) G))) ≈ mc□ (layoutAt (toℕ t) G)
lemma84 tF G = Eq.subst₂ (λ x y → dZZ {m} x y ≈ mc□ (layoutAt t G)) (Eq.sym ia) (Eq.sym ib) (go (lookupℕ t A) Eq.refl)
  where
  t : ℕ
  t = toℕ tF
  t<N : t < N
  t<N = toℕ<n tF

  A A′ : Bits N
  A  = ungray G
  A′ = ungray (flipAt t G)

  gA : gray A ≡ G
  gA = gray-ungray G

  A′≡ : A′ ≡ compl t A
  A′≡ = Eq.trans (Eq.cong (λ w → ungray (flipAt t w)) (Eq.sym gA))
          (Eq.trans (Eq.cong ungray (Eq.sym (gray-compl t A t<N))) (ungray-gray (compl t A)))

  a b : ℕ
  a = fromBits A
  b = fromBits A′

  ia : toℕ (index N G) ≡ a
  ia = toℕ-fromℕ< (fromBits<2^n A)
  ib : toℕ (index N (flipAt t G)) ≡ b
  ib = toℕ-fromℕ< (fromBits<2^n A′)

  ta : toBits N a ≡ A
  ta = toBits-fromBits A
  tb : toBits N b ≡ A′
  tb = toBits-fromBits A′

  go : ∀ x → lookupℕ t A ≡ x → dZZ {m} a b ≈ mc□ (layoutAt t G)
  go false e = begin
    dZZ a b                                  ≈⟨ ≡→≈ (dZZ-lt a<b) ⟩
    dZZ-chain a (b ∸ a)                      ≈⟨ MI (b ∸ a) a t t<N (Eq.trans (Eq.cong (lookupℕ t) ta) e) E bnd ⟩
    mc□ (layoutAt t (gray (toBits N a)))     ≈⟨ ≡→≈ (Eq.cong (λ w → mc□ (layoutAt t (gray w))) ta) ⟩
    mc□ (layoutAt t (gray A))                ≈⟨ ≡→≈ (Eq.cong (λ w → mc□ (layoutAt t w)) gA) ⟩
    mc□ (layoutAt t G) ∎
    where
    a<b : a < b
    a<b = Eq.subst (λ w → a < fromBits w) (Eq.sym A′≡) (lt-compl t A e t<N)
    ab : a + (b ∸ a) ≡ b
    ab = m+[n∸m]≡n (<⇒≤ a<b)
    E : toBits N (a + (b ∸ a)) ≡ compl t (toBits N a)
    E = Eq.trans (Eq.cong (toBits N) ab) (Eq.trans tb (Eq.trans A′≡ (Eq.cong (compl t) (Eq.sym ta))))
    bnd : a + (b ∸ a) < 2 ^ N
    bnd = Eq.subst (_< 2 ^ N) (Eq.sym ab) (fromBits<2^n A′)
  go true e = begin
    dZZ a b                                  ≈⟨ ≡→≈ (dZZ-gt b<a) ⟩
    dZZ-chain b (a ∸ b)                      ≈⟨ MI (a ∸ b) b t t<N lt′ E bnd ⟩
    mc□ (layoutAt t (gray (toBits N b)))     ≈⟨ ≡→≈ (Eq.cong (λ w → mc□ (layoutAt t (gray w))) tb) ⟩
    mc□ (layoutAt t (gray A′))               ≈⟨ ≡→≈ (Eq.cong (λ w → mc□ (layoutAt t w)) (gray-ungray (flipAt t G))) ⟩
    mc□ (layoutAt t (flipAt t G))            ≈⟨ ≡→≈ (Eq.cong mc□ (layoutAt-flip t G)) ⟩
    mc□ (layoutAt t G) ∎
    where
    lA′ : lookupℕ t A′ ≡ false
    lA′ = Eq.trans (Eq.cong (lookupℕ t) A′≡) (Eq.trans (lookup-compl-self t A t<N) (Eq.cong not e))
    lt′ : lookupℕ t (toBits N b) ≡ false
    lt′ = Eq.trans (Eq.cong (lookupℕ t) tb) lA′
    b<a : b < a
    b<a = Eq.subst (λ w → b < fromBits w)
            (Eq.trans (Eq.cong (compl t) A′≡) (compl-invol t A))
            (lt-compl t A′ lA′ t<N)
    ba : b + (a ∸ b) ≡ a
    ba = m+[n∸m]≡n (<⇒≤ b<a)
    E : toBits N (b + (a ∸ b)) ≡ compl t (toBits N b)
    E = Eq.trans (Eq.cong (toBits N) ba)
          (Eq.trans ta (Eq.trans (Eq.sym (compl-invol t A))
            (Eq.cong (compl t) (Eq.trans (Eq.sym A′≡) (Eq.sym tb)))))
    bnd : b + (a ∸ b) < 2 ^ N
    bnd = Eq.subst (_< 2 ^ N) (Eq.sym ba) (fromBits<2^n A)
