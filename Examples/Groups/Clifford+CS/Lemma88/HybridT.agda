------------------------------------------------------------------------
-- Presentations of groups
--
-- Transport of the hybrid letter along K-free words
--
-- On N = 4 + m indices: a K-free word u whose phased permutation sends
-- the consecutive pair c′, c′ + 1 to c, c + 1, with equal phases at c′
-- and c′ + 1, carries the decoded hybrid k c to k c′:
--
--     (d ʷ) u • k c ≈ k c′ • (d ʷ) u                       (`transport`)
--
-- given the shifts l j l (j+1) k j = k (j+1) l j l (j+1) and the facts at
-- the top pair that HybridCen needs.  The shift chain
-- ρ c = σ (top−1) ⋯ σ c, σ j = l j l (j+1), carries k c to k top; as a
-- phased permutation it sends top, top + 1 to c, c + 1 with phase zero
-- (`ρ-a`, `ρ-b`), and its inverse is the chain of the letters
-- (−1)_[j+1] X_[j,j+1] (`ρ-inv`, by px-inv).  So ρ c′ u ρ c⁻¹ fixes the
-- top pair with equal phases, HybridCen.cen-top makes it commute with
-- k top, and the conjugations undo.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridT
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-injective)
open import Data.Nat using (zero ; _+_ ; _∸_ ; _<_ ; _≤_ ; _<?_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (ε ; _•_ ; [_]ʷ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_ ; xw ; s<)
open import Examples.Groups.Clifford+CS.Auxiliary.NF (suc (suc (suc m)))
  using (KFreeʷ ; gen ; nil ; cat ; kf-px ; sx ; sx-letter ; fin ; fin-toℕ ; fin-irr
       ; fin-succ ; j<sj<N ; xw-cong ; n≢sn)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc (suc (suc (suc m))))
  using (Ph ; p0 ; p2 ; _+ᵖ_ ; +ᵖ-idʳ ; sp ; ph ; prm ; prm≡ ; ph≡ ; δ-≢ ; phif
       ; swapF ; swapF-b ; sound)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique (suc (suc (suc m)))
  using (sx-prm ; sx-off)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k using (d ; dPX)
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
import Examples.Groups.Clifford+CS.Lemma88.HybridCen as HCen
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

open _F,_===_ using (px-inv)

private
  N′ N : ℕ
  N′ = suc (suc (suc m))
  N  = suc N′

  W : Set
  W = Word (GenP N)

  module FrN = Fr Γ N p p′ l h k

open PB Γ using (_≈_)
open HTop Γ N p p′ l h k using (top ; TopFar)
open HCen Γ m p p′ l h k using (tT ; tT1 ; toT ; toT1)

private
  infix 4 _≈ᶠ_
  _≈ᶠ_ : W → W → Set
  _≈ᶠ_ = PB._≈_ (N F,_===_)

------------------------------------------------------------------------
-- The inverse letter of sx j: (−1)_[j+1] X_[j,j+1]

hx : ℕ → W
hx j with suc j <? N
... | yes q = xw (fin (suc j) q) (fin j (j<sj<N q)) (fin (suc j) q)
                 (s< (fin-succ j (j<sj<N q) q))
... | no  _ = ε

hx-letter : ∀ j (q : suc j < N) →
            hx j ≡ xw (fin (suc j) q) (fin j (j<sj<N q)) (fin (suc j) q)
                      (s< (fin-succ j (j<sj<N q) q))
hx-letter j q with suc j <? N
... | yes q′ = xw-cong (fin-irr (suc j) q′ q) (fin-irr j (j<sj<N q′) (j<sj<N q))
                       (fin-irr (suc j) q′ q)
... | no ¬q  = ⊥-elim (¬q q)

kf-sx : ∀ j → KFreeʷ (sx j)
kf-sx j with suc j <? N
... | yes q = gen (kf-px _ _ _ _)
... | no  _ = nil

kf-hx : ∀ j → KFreeʷ (hx j)
kf-hx j with suc j <? N
... | yes q = gen (kf-px _ _ _ _)
... | no  _ = nil

sx-hx : ∀ j (q : suc j < N) → (sx j • hx j) ≈ᶠ ε
sx-hx j q = Eq.subst₂ (λ x y → (x • y) ≈ᶠ ε) (Eq.sym (sx-letter j q)) (Eq.sym (hx-letter j q))
                      (PB.axiom (px-inv (fin j (j<sj<N q)) (fin (suc j) q)
                                        (fin-succ j (j<sj<N q) q)))

------------------------------------------------------------------------
-- How sx j acts

private
  ne-sj : ∀ j → suc j ≢ j
  ne-sj j e = n≢sn j (Eq.sym e)

  ne-ssj : ∀ j → j ≢ suc (suc j)
  ne-ssj j = NP.<⇒≢ (NP.<-trans (NP.n<1+n j) (NP.n<1+n (suc j)))

-- It moves the upper index of its pair down.
sx-back : ∀ j (q : suc j < N) t → toℕ t ≡ suc j → toℕ (prm (sp (sx j)) t) ≡ j
sx-back j q t e =
  Eq.trans (Eq.cong toℕ (Eq.trans (sx-prm j (j<sj<N q) q t)
                                  (Eq.trans (Eq.cong (swapF a b) t≡) (swapF-b a b))))
           (fin-toℕ j (j<sj<N q))
  where
  a = fin j (j<sj<N q)
  b = fin (suc j) q

  t≡ : t ≡ b
  t≡ = toℕ-injective (Eq.trans e (Eq.sym (fin-toℕ (suc j) q)))

-- Its only phase is on its lower index.
sx-ph0 : ∀ j (q : suc j < N) t → toℕ t ≢ j → ph (sp (sx j)) t ≡ p0
sx-ph0 j q t ne =
  Eq.trans (Eq.cong (λ w → ph (sp w) t) (sx-letter j q))
           (Eq.cong (λ b → phif b p2 +ᵖ p0)
                    (δ-≢ (fin j (j<sj<N q)) t
                         (λ e → ne (Eq.trans (Eq.cong toℕ e) (fin-toℕ j (j<sj<N q))))))

------------------------------------------------------------------------
-- The shift σ j = l j l (j+1), and the chain ρ c

σw σb : ℕ → W
σw j = sx j • sx (suc j)
σb j = hx (suc j) • hx j

-- σ j sends j + 1 to j and j + 2 to j + 1, with phase zero.
σ-1 : ∀ j (q : suc (suc j) < N) t → toℕ t ≡ suc j →
      toℕ (prm (sp (σw j)) t) ≡ j × ph (sp (σw j)) t ≡ p0
σ-1 j q t e =
  Eq.trans (Eq.cong toℕ fix) at ,
  Eq.cong₂ _+ᵖ_ (sx-ph0 j qj t (λ e′ → ne-sj j (Eq.trans (Eq.sym e) e′)))
                (sx-ph0 (suc j) q t′ (λ e′ → n≢sn j (Eq.trans (Eq.sym at) e′)))
  where
  qj : suc j < N
  qj = NP.<-trans (NP.n<1+n (suc j)) q

  t′ = prm (sp (sx j)) t

  at : toℕ t′ ≡ j
  at = sx-back j qj t e

  fix : prm (sp (sx (suc j))) t′ ≡ t′
  fix = sx-off (suc j) qj q t′ (λ e′ → n≢sn j (Eq.trans (Eq.sym at) e′))
                               (λ e′ → ne-ssj j (Eq.trans (Eq.sym at) e′))

σ-2 : ∀ j (q : suc (suc j) < N) t → toℕ t ≡ suc (suc j) →
      toℕ (prm (sp (σw j)) t) ≡ suc j × ph (sp (σw j)) t ≡ p0
σ-2 j q t e =
  Eq.trans (Eq.cong (λ z → toℕ (prm (sp (sx (suc j))) z)) fix) (sx-back (suc j) q t e) ,
  Eq.cong₂ _+ᵖ_ (sx-ph0 j qj t (λ e′ → ne-ssj j (Eq.trans (Eq.sym e′) e)))
                (sx-ph0 (suc j) q t′ (λ e′ → ne-sj (suc j)
                                         (Eq.trans (Eq.sym e)
                                           (Eq.trans (Eq.cong toℕ (Eq.sym fix)) e′))))
  where
  qj : suc j < N
  qj = NP.<-trans (NP.n<1+n (suc j)) q

  t′ = prm (sp (sx j)) t

  fix : t′ ≡ t
  fix = sx-off j (j<sj<N qj) qj t (λ e′ → ne-ssj j (Eq.trans (Eq.sym e′) e))
                                  (λ e′ → ne-sj (suc j) (Eq.trans (Eq.sym e) e′))

ρw ρb : ℕ → ℕ → W
ρw c zero    = ε
ρw c (suc e) = ρw (suc c) e • σw c
ρb c zero    = ε
ρb c (suc e) = σb c • ρb (suc c) e

kf-ρw : ∀ c e → KFreeʷ (ρw c e)
kf-ρw c zero    = nil
kf-ρw c (suc e) = cat (kf-ρw (suc c) e) (cat (kf-sx c) (kf-sx (suc c)))

kf-ρb : ∀ c e → KFreeʷ (ρb c e)
kf-ρb c zero    = nil
kf-ρb c (suc e) = cat (cat (kf-hx (suc c)) (kf-hx c)) (kf-ρb (suc c) e)

private
  shift-q : ∀ c e → suc (c + suc e) < N → suc (suc c + e) < N
  shift-q c e q = Eq.subst (λ z → suc z < N) (NP.+-suc c e) q

  σ-q : ∀ c e → suc (c + suc e) < N → suc (suc c) < N
  σ-q c e q = NP.≤-<-trans (s≤s (s≤s (NP.m≤m+n c e))) (shift-q c e q)

-- ρ c e sends c + e to c and c + e + 1 to c + 1, with phase zero.
ρ-a : ∀ c e → suc (c + e) < N → ∀ t → toℕ t ≡ c + e →
      toℕ (prm (sp (ρw c e)) t) ≡ c × ph (sp (ρw c e)) t ≡ p0
ρ-a c zero    q t et = Eq.trans et (NP.+-identityʳ c) , Eq.refl
ρ-a c (suc e) q t et = proj₁ s , Eq.cong₂ _+ᵖ_ (proj₂ ih) (proj₂ s)
  where
  ih = ρ-a (suc c) e (shift-q c e q) t (Eq.trans et (NP.+-suc c e))
  s  = σ-1 c (σ-q c e q) (prm (sp (ρw (suc c) e)) t) (proj₁ ih)

ρ-b : ∀ c e → suc (c + e) < N → ∀ t → toℕ t ≡ suc (c + e) →
      toℕ (prm (sp (ρw c e)) t) ≡ suc c × ph (sp (ρw c e)) t ≡ p0
ρ-b c zero    q t et = Eq.trans et (Eq.cong suc (NP.+-identityʳ c)) , Eq.refl
ρ-b c (suc e) q t et = proj₁ s , Eq.cong₂ _+ᵖ_ (proj₂ ih) (proj₂ s)
  where
  ih = ρ-b (suc c) e (shift-q c e q) t (Eq.trans et (Eq.cong suc (NP.+-suc c e)))
  s  = σ-2 c (σ-q c e q) (prm (sp (ρw (suc c) e)) t) (proj₁ ih)

-- The inverse chain.
σ-inv : ∀ j → suc (suc j) < N → (σw j • σb j) ≈ᶠ ε
σ-inv j q =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl
                (PB.trans (PB.sym PB.assoc)
                  (PB.trans (PB.cong (sx-hx (suc j) q) PB.refl) PB.left-unit)))
              (sx-hx j (NP.<-trans (NP.n<1+n (suc j)) q)))

ρ-inv : ∀ c e → suc (c + e) < N → (ρw c e • ρb c e) ≈ᶠ ε
ρ-inv c zero    q = PB.left-unit
ρ-inv c (suc e) q =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl
                (PB.trans (PB.sym PB.assoc)
                  (PB.trans (PB.cong (σ-inv c (σ-q c e q)) PB.refl) PB.left-unit)))
              (ρ-inv (suc c) e (shift-q c e q)))

------------------------------------------------------------------------
-- The transport

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))))
  (shift : ∀ {j} → suc (suc j) < N →
           (l j • l (suc j)) • k j ≈ k (suc j) • (l j • l (suc j))) where

  open FrN.Facts F
  open FrN.Proofs F
  open Tools Γ hiding (_≈_)
  open HCen.Proofs Γ m p p′ l h k F T sc using (cen-top ; d-≈)

  ----------------------------------------------------------------------
  -- Decoded

  d-sx : ∀ j (q : suc j < N) → (d ʷ) (sx j) ≡ l j
  d-sx j q =
    Eq.trans (Eq.cong (d ʷ) (sx-letter j q))
      (Eq.trans (Eq.cong₂ (λ x y → dPX x x y) (fin-toℕ j (j<sj<N q)) (fin-toℕ (suc j) q))
                (lo1 j))

  d-hx : ∀ j (q : suc j < N) → (d ʷ) (hx j) ≡ h j
  d-hx j q =
    Eq.trans (Eq.cong (d ʷ) (hx-letter j q))
      (Eq.trans (Eq.cong₂ (λ x y → dPX y x y) (fin-toℕ j (j<sj<N q)) (fin-toℕ (suc j) q))
                (hi1 j))

  private
    qlo : ∀ {j} → suc (suc j) < N → suc j < N
    qlo q = NP.<-trans (NP.n<1+n _) q

  dσ : ∀ j → suc (suc j) < N → (d ʷ) (σw j) ≡ l j • l (suc j)
  dσ j q = Eq.cong₂ _•_ (d-sx j (qlo q)) (d-sx (suc j) q)

  dσb : ∀ j → suc (suc j) < N → (d ʷ) (σb j) ≡ h (suc j) • h j
  dσb j q = Eq.cong₂ _•_ (d-hx (suc j) q) (d-hx j (qlo q))

  -- The inverse chain is a left inverse, decoded.
  dσ-inv : ∀ j → suc (suc j) < N → (d ʷ) (σb j) • (d ʷ) (σw j) ≈ ε
  dσ-inv j q = Eq.subst₂ (λ x y → x • y ≈ ε) (Eq.sym (dσb j q)) (Eq.sym (dσ j q)) (begin
    (h (suc j) • h j) • (l j • l (suc j))    ≈⟨ assoc ⟩
    h (suc j) • (h j • (l j • l (suc j)))    ≈⟨ back (h (suc j)) (sym assoc) ⟩
    h (suc j) • ((h j • l j) • l (suc j))    ≈⟨ back (h (suc j)) (front (l (suc j)) (h-inv (qlo q))) ⟩
    h (suc j) • (ε • l (suc j))              ≈⟨ back (h (suc j)) left-unit ⟩
    h (suc j) • l (suc j)                    ≈⟨ h-inv q ⟩
    ε                                        ∎)

  dρ-inv : ∀ c e → suc (c + e) < N → (d ʷ) (ρb c e) • (d ʷ) (ρw c e) ≈ ε
  dρ-inv c zero    q = left-unit
  dρ-inv c (suc e) q = begin
    (Sb • Rb) • (R • S)    ≈⟨ assoc ⟩
    Sb • (Rb • (R • S))    ≈⟨ back Sb (sym assoc) ⟩
    Sb • ((Rb • R) • S)    ≈⟨ back Sb (front S (dρ-inv (suc c) e (shift-q c e q))) ⟩
    Sb • (ε • S)           ≈⟨ back Sb left-unit ⟩
    Sb • S                 ≈⟨ dσ-inv c (σ-q c e q) ⟩
    ε                      ∎
    where
    Sb = (d ʷ) (σb c)
    Rb = (d ʷ) (ρb (suc c) e)
    R  = (d ʷ) (ρw (suc c) e)
    S  = (d ʷ) (σw c)

  -- The chain carries k c to k (c + e).
  ρ-k : ∀ c e → suc (c + e) < N →
        (d ʷ) (ρw c e) • k c ≈ k (c + e) • (d ʷ) (ρw c e)
  ρ-k c zero    q = Eq.subst (λ z → ε • k c ≈ k z • ε) (Eq.sym (NP.+-identityʳ c))
                             (trans left-unit (sym right-unit))
  ρ-k c (suc e) q = Eq.subst (λ z → (R • S) • k c ≈ k z • (R • S)) (Eq.sym (NP.+-suc c e)) (begin
    (R • S) • k c                 ≈⟨ assoc ⟩
    R • (S • k c)                 ≈⟨ back R sh ⟩
    R • (k (suc c) • S)           ≈⟨ sym assoc ⟩
    (R • k (suc c)) • S           ≈⟨ front S (ρ-k (suc c) e (shift-q c e q)) ⟩
    (k (suc c + e) • R) • S       ≈⟨ assoc ⟩
    k (suc c + e) • (R • S)       ∎)
    where
    R = (d ʷ) (ρw (suc c) e)
    S = (d ʷ) (σw c)

    sh : S • k c ≈ k (suc c) • S
    sh = Eq.subst (λ z → z • k c ≈ k (suc c) • z) (Eq.sym (dσ c (σ-q c e q)))
                  (shift (σ-q c e q))

  ----------------------------------------------------------------------
  -- The conjugation algebra

  private
    alg : ∀ {U A Ā B B̄ kc kc′ kt : Word X} → Ā • A ≈ ε → B̄ • B ≈ ε →
          A • kc′ ≈ kt • A → B • kc ≈ kt • B →
          (A • (U • B̄)) • kt ≈ kt • (A • (U • B̄)) → U • kc ≈ kc′ • U
    alg {U} {A} {Ā} {B} {B̄} {kc} {kc′} {kt} iA iB cA cB cW = begin
      U • kc                ≈⟨ sym left-unit ⟩
      ε • (U • kc)          ≈⟨ front (U • kc) (sym iA) ⟩
      (Ā • A) • (U • kc)    ≈⟨ assoc ⟩
      Ā • (A • (U • kc))    ≈⟨ back Ā (trans lhs (sym rhs)) ⟩
      Ā • (A • (kc′ • U))   ≈⟨ sym assoc ⟩
      (Ā • A) • (kc′ • U)   ≈⟨ front (kc′ • U) iA ⟩
      ε • (kc′ • U)         ≈⟨ left-unit ⟩
      kc′ • U               ∎
      where
      lhs : A • (U • kc) ≈ kt • (A • U)
      lhs = begin
        A • (U • kc)                    ≈⟨ back A (back U (trans (sym left-unit) (front kc (sym iB)))) ⟩
        A • (U • ((B̄ • B) • kc))        ≈⟨ back A (back U assoc) ⟩
        A • (U • (B̄ • (B • kc)))        ≈⟨ back A (back U (back B̄ cB)) ⟩
        A • (U • (B̄ • (kt • B)))        ≈⟨ back A (back U (sym assoc)) ⟩
        A • (U • ((B̄ • kt) • B))        ≈⟨ back A (sym assoc) ⟩
        A • ((U • (B̄ • kt)) • B)        ≈⟨ back A (front B (sym assoc)) ⟩
        A • (((U • B̄) • kt) • B)        ≈⟨ sym assoc ⟩
        (A • ((U • B̄) • kt)) • B        ≈⟨ front B (sym assoc) ⟩
        ((A • (U • B̄)) • kt) • B        ≈⟨ front B cW ⟩
        (kt • (A • (U • B̄))) • B        ≈⟨ assoc ⟩
        kt • ((A • (U • B̄)) • B)        ≈⟨ back kt assoc ⟩
        kt • (A • ((U • B̄) • B))        ≈⟨ back kt (back A assoc) ⟩
        kt • (A • (U • (B̄ • B)))        ≈⟨ back kt (back A (back U iB)) ⟩
        kt • (A • (U • ε))              ≈⟨ back kt (back A right-unit) ⟩
        kt • (A • U)                    ∎

      rhs : A • (kc′ • U) ≈ kt • (A • U)
      rhs = begin
        A • (kc′ • U)     ≈⟨ sym assoc ⟩
        (A • kc′) • U     ≈⟨ front U cA ⟩
        (kt • A) • U      ≈⟨ assoc ⟩
        kt • (A • U)      ∎

  ----------------------------------------------------------------------
  -- The transport

  transport : ∀ {u : W} (c c′ : ℕ) → c ≤ top → c′ ≤ top → KFreeʷ u →
              (∀ t → toℕ t ≡ c′ → toℕ (prm (sp u) t) ≡ c) →
              (∀ t → toℕ t ≡ suc c′ → toℕ (prm (sp u) t) ≡ suc c) →
              (∀ t t′ → toℕ t ≡ c′ → toℕ t′ ≡ suc c′ → ph (sp u) t ≡ ph (sp u) t′) →
              (d ʷ) u • k c ≈ k c′ • (d ʷ) u
  transport {u} c c′ c≤ c′≤ ku πa πb φ =
    alg (dρ-inv c′ e′ q′) (dρ-inv c e q) cA cB cW
    where
    e e′ : ℕ
    e  = top ∸ c
    e′ = top ∸ c′

    ce : c + e ≡ top
    ce = NP.m+[n∸m]≡n c≤

    ce′ : c′ + e′ ≡ top
    ce′ = NP.m+[n∸m]≡n c′≤

    qtop : suc top < N
    qtop = NP.n<1+n (suc top)

    q : suc (c + e) < N
    q = Eq.subst (λ z → suc z < N) (Eq.sym ce) qtop

    q′ : suc (c′ + e′) < N
    q′ = Eq.subst (λ z → suc z < N) (Eq.sym ce′) qtop

    A B B̄ : W
    A  = ρw c′ e′
    B  = ρw c e
    B̄  = ρb c e

    w : W
    w = A • (u • B̄)

    kw : KFreeʷ w
    kw = cat (kf-ρw c′ e′) (cat ku (kf-ρb c e))

    a0 = ρ-a c′ e′ q′ tT  (Eq.trans toT (Eq.sym ce′))
    a1 = ρ-b c′ e′ q′ tT1 (Eq.trans toT1 (Eq.cong suc (Eq.sym ce′)))
    b0 = ρ-a c e q tT  (Eq.trans toT (Eq.sym ce))
    b1 = ρ-b c e q tT1 (Eq.trans toT1 (Eq.cong suc (Eq.sym ce)))

    inv = sound (ρ-inv c e q)

    x0 x1 : Fin N
    x0 = prm (sp A) tT
    x1 = prm (sp A) tT1

    y0≡ : prm (sp u) x0 ≡ prm (sp B) tT
    y0≡ = toℕ-injective (Eq.trans (πa x0 (proj₁ a0)) (Eq.sym (proj₁ b0)))

    y1≡ : prm (sp u) x1 ≡ prm (sp B) tT1
    y1≡ = toℕ-injective (Eq.trans (πb x1 (proj₁ a1)) (Eq.sym (proj₁ b1)))

    fT : prm (sp w) tT ≡ tT
    fT = Eq.trans (Eq.cong (prm (sp B̄)) y0≡) (prm≡ inv tT)

    fT1 : prm (sp w) tT1 ≡ tT1
    fT1 = Eq.trans (Eq.cong (prm (sp B̄)) y1≡) (prm≡ inv tT1)

    ph0 : ph (sp B̄) (prm (sp u) x0) ≡ p0
    ph0 = Eq.trans (Eq.cong (ph (sp B̄)) y0≡)
            (Eq.trans (Eq.cong (_+ᵖ ph (sp B̄) (prm (sp B) tT)) (Eq.sym (proj₂ b0)))
                      (ph≡ inv tT))

    ph1 : ph (sp B̄) (prm (sp u) x1) ≡ p0
    ph1 = Eq.trans (Eq.cong (ph (sp B̄)) y1≡)
            (Eq.trans (Eq.cong (_+ᵖ ph (sp B̄) (prm (sp B) tT1)) (Eq.sym (proj₂ b1)))
                      (ph≡ inv tT1))

    E0 : ph (sp w) tT ≡ ph (sp u) x0
    E0 = Eq.trans (Eq.cong₂ _+ᵖ_ (proj₂ a0) (Eq.cong (ph (sp u) x0 +ᵖ_) ph0))
                  (+ᵖ-idʳ (ph (sp u) x0))

    E1 : ph (sp w) tT1 ≡ ph (sp u) x1
    E1 = Eq.trans (Eq.cong₂ _+ᵖ_ (proj₂ a1) (Eq.cong (ph (sp u) x1 +ᵖ_) ph1))
                  (+ᵖ-idʳ (ph (sp u) x1))

    cW : Comm ((d ʷ) w) (k top)
    cW = cen-top kw fT fT1
           (Eq.trans E0 (Eq.trans (φ x0 x1 (proj₁ a0) (proj₁ a1)) (Eq.sym E1)))

    cA : (d ʷ) A • k c′ ≈ k top • (d ʷ) A
    cA = Eq.subst (λ z → (d ʷ) A • k c′ ≈ k z • (d ʷ) A) ce′ (ρ-k c′ e′ q′)

    cB : (d ʷ) B • k c ≈ k top • (d ʷ) B
    cB = Eq.subst (λ z → (d ʷ) B • k c ≈ k z • (d ʷ) B) ce (ρ-k c e q)
