------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid rule ki-ki: hybrid letters on disjoint pairs commute
--
-- On N = 4 + m indices.  The far facts at any position come from the
-- top by HybridT.transport: k c passes l j and h j two or more away (the
-- K-free letter fixes c, c + 1 with phase zero), and k i passes k j two
-- or more above it, which the shift chain to j (fixing everything below
-- j) carries to the hypothesis `far-k` at the top.  Two letters on
-- separated pairs (b < c) then commute letter by letter (`kh-sep`), the
-- phase pairs passing by ki-pp.  A crossing pair a < c < b < d is
-- conjugated by the involution (−1)_[s] X_[c,b] into the separated
-- pairs (a, c), (b, d), and a nested pair a < c < d < b by (−1)_[s]
-- X_[d,b] into a crossing one, both by ki-swap and ki-swap′
-- (HybridPair).  So no phase twists arise.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridKK
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n) renaming (<-trans to <ᶠ-trans)
open import Data.Nat using (zero ; _+_ ; _∸_ ; _<_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (ε ; _•_ ; [_]ʷ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_ ; pw ; xw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (kiw)
open import Examples.Groups.Clifford+CS.Auxiliary.NF (suc (suc (suc m)))
  using (KFreeʷ ; gen ; nil ; cat ; kf-px ; sx ; j<sj<N ; n≢sn)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc (suc (suc (suc m))))
  using (Ph ; p0 ; p2 ; _+ᵖ_ ; sp ; ph ; prm ; δ ; phif ; swapF ; swapF-o ; swapF-invol ; eqv)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique (suc (suc (suc m)))
  using (A5 ; sx-off)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k using (d ; dPP ; dKIa)
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
import Examples.Groups.Clifford+CS.Lemma88.HybridCen as HCen
import Examples.Groups.Clifford+CS.Lemma88.HybridT as HT
import Examples.Groups.Clifford+CS.Lemma88.HybridPair as HP
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

open _F,_===_ using (pp-comm)

private
  N′ N : ℕ
  N′ = suc (suc (suc m))
  N  = suc N′

  W : Set
  W = Word (GenP N)

  module FrN = Fr Γ N p p′ l h k

open PB Γ using (_≈_)
open HTop Γ N p p′ l h k using (top ; TopFar)
open HT Γ m p p′ l h k using (σw ; ρw ; kf-sx ; kf-ρw ; sx-ph0)
open HP Γ m p p′ l h k using (δπ)

------------------------------------------------------------------------
-- The shift chain fixes what lies below it

private
  q-tl : ∀ c e → suc (c + suc e) < N → suc (suc c + e) < N
  q-tl c e q = Eq.subst (λ z → suc z < N) (NP.+-suc c e) q

  q-σ : ∀ c e → suc (c + suc e) < N → suc (suc c) < N
  q-σ c e q = NP.≤-<-trans (s≤s (s≤s (NP.m≤m+n c e))) (q-tl c e q)

ρ-lo : ∀ c e → suc (c + e) < N → ∀ t → toℕ t < c →
       prm (sp (ρw c e)) t ≡ t × ph (sp (ρw c e)) t ≡ p0
ρ-lo c zero    q t lt = Eq.refl , Eq.refl
ρ-lo c (suc e) q t lt =
  Eq.trans (Eq.cong (prm (sp (σw c))) (proj₁ ih))
           (Eq.trans (Eq.cong (prm (sp (sx (suc c)))) f0) f1) ,
  Eq.cong₂ _+ᵖ_ (proj₂ ih)
    (Eq.trans (Eq.cong (ph (sp (σw c))) (proj₁ ih))
              (Eq.cong₂ _+ᵖ_ (sx-ph0 c q1 t nc)
                             (Eq.trans (Eq.cong (ph (sp (sx (suc c)))) f0)
                                       (sx-ph0 (suc c) qσ t nsc))))
  where
  qσ = q-σ c e q
  q1 : suc c < N
  q1 = NP.<-trans (NP.n<1+n _) qσ

  ih = ρ-lo (suc c) e (q-tl c e q) t (NP.<-trans lt (NP.n<1+n c))

  nc : toℕ t ≢ c
  nc = NP.<⇒≢ lt

  nsc : toℕ t ≢ suc c
  nsc = NP.<⇒≢ (NP.<-trans lt (NP.n<1+n c))

  nssc : toℕ t ≢ suc (suc c)
  nssc = NP.<⇒≢ (NP.<-trans lt (NP.<-trans (NP.n<1+n c) (NP.n<1+n (suc c))))

  f0 : prm (sp (sx c)) t ≡ t
  f0 = sx-off c (j<sj<N q1) q1 t nc nsc

  f1 : prm (sp (sx (suc c))) t ≡ t
  f1 = sx-off (suc c) q1 qσ t nsc nssc

-- (−1)_[s] X_[x,y] is an involution when s is neither index.
xx-inv : ∀ s x y .(xy : x <ᶠ y) → s ≢ x → s ≢ y →
         PB._≈_ (N F,_===_) (xw s x y xy • xw s x y xy) ε
xx-inv s x y xy sx′ sy =
  A5 (cat (gen (kf-px s x y xy)) (gen (kf-px s x y xy))) nil
     (eqv phs (λ t → swapF-invol x y t))
  where
  u = xw s x y xy

  two : ∀ (β : Bool) → (phif β p2 +ᵖ p0) +ᵖ (phif β p2 +ᵖ p0) ≡ p0
  two Bool.true  = Eq.refl
  two Bool.false = Eq.refl

  phs : ∀ t → ph (sp (u • u)) t ≡ p0
  phs t = Eq.trans (Eq.cong (λ β → (phif (δ s t) p2 +ᵖ p0) +ᵖ (phif β p2 +ᵖ p0))
                            (δπ u s s (swapF-o x y s sx′ sy) t))
                   (two (δ s t))

------------------------------------------------------------------------
-- The decoded statements

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))))
  (shift : ∀ {j} → suc (suc j) < N →
           (l j • l (suc j)) • k j ≈ k (suc j) • (l j • l (suc j)))
  (far-k : ∀ {j} → suc (suc j) ≤ top → k top • k j ≈ k j • k top) where

  open FrN.Facts F
  open FrN.Proofs F
  open Tools Γ hiding (_≈_)
  open HCen.Proofs Γ m p p′ l h k F T sc using (d-≈)
  open HT.Proofs Γ m p p′ l h k F T sc shift using (transport ; d-sx ; dρ-inv ; ρ-k)
  open HP.Proofs Γ m p p′ l h k F T sc shift using (d-ki-pp ; d-ki-swap ; d-ki-swap′)

  private
    le-top : ∀ {c} → suc c < N → c ≤ top
    le-top q = NP.≤-pred (NP.≤-pred q)

    Far : ℕ → ℕ → Set
    Far c j = suc (suc j) ≤ c ⊎ suc (suc c) ≤ j


  ----------------------------------------------------------------------
  -- k c against far K-free letters

  private
    ne-far : ∀ {c j} → Far c j → ∀ {x} → x ≡ c ⊎ x ≡ suc c → x ≢ j × x ≢ suc j
    ne-far (inj₁ le) (inj₁ Eq.refl) =
      (λ e → NP.<⇒≢ (NP.<-trans (NP.n<1+n _) le) (Eq.sym e)) , (λ e → NP.<⇒≢ le (Eq.sym e))
    ne-far (inj₁ le) (inj₂ Eq.refl) =
      (λ e → NP.<⇒≢ (NP.<-trans (NP.n<1+n _) (NP.<-trans le (NP.n<1+n _))) (Eq.sym e)) ,
      (λ e → NP.<⇒≢ (NP.<-trans le (NP.n<1+n _)) (Eq.sym e))
    ne-far (inj₂ le) (inj₁ Eq.refl) =
      (λ e → NP.<⇒≢ (NP.<-trans (NP.n<1+n _) le) e) ,
      (λ e → NP.<⇒≢ (NP.<-trans (NP.n<1+n _) (NP.<-trans le (NP.n<1+n _))) e)
    ne-far (inj₂ le) (inj₂ Eq.refl) =
      (λ e → NP.<⇒≢ le e) , (λ e → NP.<⇒≢ (NP.<-trans le (NP.n<1+n _)) e)

  k-l-far : ∀ {c j} → suc c < N → suc j < N → Far c j → Comm (l j) (k c)
  k-l-far {c} {j} qc qj fr =
    Eq.subst (λ x → Comm x (k c)) (d-sx j qj)
      (transport c c (le-top qc) (le-top qc) (kf-sx j) πa πb φ)
    where
    fix : ∀ t {x} → toℕ t ≡ x → x ≡ c ⊎ x ≡ suc c → prm (sp (sx j)) t ≡ t
    fix t et w = sx-off j (j<sj<N qj) qj t
                   (λ e → proj₁ (ne-far fr w) (Eq.trans (Eq.sym et) e))
                   (λ e → proj₂ (ne-far fr w) (Eq.trans (Eq.sym et) e))

    zero-ph : ∀ t {x} → toℕ t ≡ x → x ≡ c ⊎ x ≡ suc c → ph (sp (sx j)) t ≡ p0
    zero-ph t et w = sx-ph0 j qj t (λ e → proj₁ (ne-far fr w) (Eq.trans (Eq.sym et) e))

    πa : ∀ t → toℕ t ≡ c → toℕ (prm (sp (sx j)) t) ≡ c
    πa t et = Eq.trans (Eq.cong toℕ (fix t et (inj₁ Eq.refl))) et

    πb : ∀ t → toℕ t ≡ suc c → toℕ (prm (sp (sx j)) t) ≡ suc c
    πb t et = Eq.trans (Eq.cong toℕ (fix t et (inj₂ Eq.refl))) et

    φ : ∀ t t′ → toℕ t ≡ c → toℕ t′ ≡ suc c → ph (sp (sx j)) t ≡ ph (sp (sx j)) t′
    φ t t′ et et′ = Eq.trans (zero-ph t et (inj₁ Eq.refl)) (Eq.sym (zero-ph t′ et′ (inj₂ Eq.refl)))

  k-h-far : ∀ {c j} → suc c < N → suc j < N → Far c j → Comm (h j) (k c)
  k-h-far qc qj fr = comm-inv (l-inv qj) (h-inv qj) (k-l-far qc qj fr)

  -- k i against k j, i two or more below: the shift chain to j fixes
  -- i, i + 1 and carries k j to k top.
  k-k-far : ∀ {i j} → suc (suc i) ≤ j → suc j < N → Comm (k i) (k j)
  k-k-far {i} {j} le qj = cancel (begin
    R • (k i • k j)        ≈⟨ sym assoc ⟩
    (R • k i) • k j        ≈⟨ front (k j) cRi ⟩
    (k i • R) • k j        ≈⟨ assoc ⟩
    k i • (R • k j)        ≈⟨ back (k i) cR ⟩
    k i • (k top • R)      ≈⟨ sym assoc ⟩
    (k i • k top) • R      ≈⟨ front R (sym ft) ⟩
    (k top • k i) • R      ≈⟨ assoc ⟩
    k top • (k i • R)      ≈⟨ back (k top) (sym cRi) ⟩
    k top • (R • k i)      ≈⟨ sym assoc ⟩
    (k top • R) • k i      ≈⟨ front (k i) (sym cR) ⟩
    (R • k j) • k i        ≈⟨ assoc ⟩
    R • (k j • k i)        ∎)
    where
    e : ℕ
    e = top ∸ j

    je : j + e ≡ top
    je = NP.m+[n∸m]≡n (le-top qj)

    qe : suc (j + e) < N
    qe = Eq.subst (λ z → suc z < N) (Eq.sym je) (NP.n<1+n (suc top))

    R R̄ : Word X
    R  = (d ʷ) (ρw j e)
    R̄  = (d ʷ) (HT.ρb Γ m p p′ l h k j e)

    cR : R • k j ≈ k top • R
    cR = Eq.subst (λ z → R • k j ≈ k z • R) je (ρ-k j e qe)

    i<j : i < j
    i<j = NP.<-trans (NP.n<1+n i) le

    lo : ∀ t {x} → toℕ t ≡ x → x < j → prm (sp (ρw j e)) t ≡ t × ph (sp (ρw j e)) t ≡ p0
    lo t et lt = ρ-lo j e qe t (Eq.subst (_< j) (Eq.sym et) lt)

    qi : suc i < N
    qi = NP.<-trans (NP.≤-<-trans i<j (NP.n<1+n j)) qj

    cRi : R • k i ≈ k i • R
    cRi = transport i i (le-top qi) (le-top qi)
            (kf-ρw j e)
            (λ t et → Eq.trans (Eq.cong toℕ (proj₁ (lo t et i<j))) et)
            (λ t et → Eq.trans (Eq.cong toℕ (proj₁ (lo t et le))) et)
            (λ t t′ et et′ → Eq.trans (proj₂ (lo t et i<j)) (Eq.sym (proj₂ (lo t′ et′ le))))

    ft : k top • k i ≈ k i • k top
    ft = far-k (NP.≤-trans le (le-top qj))

    cancel : R • (k i • k j) ≈ R • (k j • k i) → k i • k j ≈ k j • k i
    cancel c = begin
      k i • k j                ≈⟨ sym left-unit ⟩
      ε • (k i • k j)          ≈⟨ front _ (sym (dρ-inv j e qe)) ⟩
      (R̄ • R) • (k i • k j)    ≈⟨ assoc ⟩
      R̄ • (R • (k i • k j))    ≈⟨ back R̄ c ⟩
      R̄ • (R • (k j • k i))    ≈⟨ sym assoc ⟩
      (R̄ • R) • (k j • k i)    ≈⟨ front _ (dρ-inv j e qe) ⟩
      ε • (k j • k i)          ≈⟨ left-unit ⟩
      k j • k i                ∎

  ----------------------------------------------------------------------
  -- Letters on separated pairs

  comm-dKIa : ∀ a n {Y : Word X} →
              (∀ j → a ≤ j → j < a + n → Comm (h j) Y × Comm (l j) Y × Comm (k j) Y) →
              Comm (dKIa a n) Y
  comm-dKIa a zero                f = comm-ε
  comm-dKIa a (suc zero)          f = proj₂ (proj₂ (f a NP.≤-refl (Eq.subst (a <_) (Eq.sym (NP.+-comm a 1)) (NP.n<1+n a))))
  comm-dKIa a (suc (suc n)) {Y} f =
    comm-• (proj₁ (f a NP.≤-refl a<))
           (comm-• (comm-dKIa (suc a) (suc n) f′) (proj₁ (proj₂ (f a NP.≤-refl a<))))
    where
    a< : a < a + suc (suc n)
    a< = NP.≤-<-trans (NP.m≤m+n a (suc n)) (Eq.subst (a + suc n <_) (Eq.sym (NP.+-suc a (suc n))) (NP.n<1+n _))

    f′ : ∀ j → suc a ≤ j → j < suc a + suc n → Comm (h j) Y × Comm (l j) Y × Comm (k j) Y
    f′ j le lt = f j (NP.<⇒≤ le) (Eq.subst (j <_) (Eq.sym (NP.+-suc a (suc n))) lt)

  -- Two letters far apart commute.
  private
    far2 : ∀ {j j′} → suc (suc j) ≤ j′ → suc j′ < N →
           (Comm (h j′) (h j) × Comm (l j′) (h j) × Comm (k j′) (h j)) ×
           (Comm (h j′) (l j) × Comm (l j′) (l j) × Comm (k j′) (l j)) ×
           (Comm (h j′) (k j) × Comm (l j′) (k j) × Comm (k j′) (k j))
    far2 {j} {j′} le q′ =
      (comm-inv (l-inv q′) (h-inv q′) lh , lh , comm-sym (k-h-far q′ qj (inj₁ le))) ,
      (far-hl′ q′ le , comm-sym (far-ll q′ le) , comm-sym (k-l-far q′ qj (inj₁ le))) ,
      (k-h-far qj q′ (inj₂ le) , k-l-far qj q′ (inj₂ le) , comm-sym (k-k-far le q′))
      where
      qj : suc j < N
      qj = NP.≤-trans le (NP.<⇒≤ (NP.<-trans (NP.n<1+n j′) q′))

      lh : Comm (l j′) (h j)
      lh = comm-sym (far-hl q′ le)

  kh-sep : ∀ A n C mm → A + n < C → C + mm < N → Comm (dKIa A n) (dKIa C mm)
  kh-sep A n C mm sep qC =
    comm-dKIa A n (λ j aj jn →
      let g = λ j′ (cj : C ≤ j′) (jm : j′ < C + mm) →
                far2 {j} {j′} (NP.≤-trans (NP.≤-trans (s≤s jn) sep) cj)
                     (NP.≤-<-trans jm qC) in
      comm-sym (comm-dKIa C mm (λ j′ cj jm → proj₁ (g j′ cj jm))) ,
      comm-sym (comm-dKIa C mm (λ j′ cj jm → proj₁ (proj₂ (g j′ cj jm)))) ,
      comm-sym (comm-dKIa C mm (λ j′ cj jm → proj₂ (proj₂ (g j′ cj jm)))))

  ----------------------------------------------------------------------
  -- ki-ki

  private
    rel : ∀ {a b : Fin N} → .(a <ᶠ b) → toℕ a < toℕ b
    rel {a} {b} ab = recompute (toℕ a NP.<? toℕ b) ab

    Q : ∀ (a b s : Fin N) → .(a <ᶠ b) → Word X
    Q a b s ab = d (ki a b s ab)

    sep-alg : ∀ {K₁ D₁ K₂ D₂ : Word X} →
              D₁ • (K₂ • D₂) ≈ (K₂ • D₂) • D₁ → D₂ • (K₁ • D₁) ≈ (K₁ • D₁) • D₂ →
              K₁ • K₂ ≈ K₂ • K₁ → D₂ • D₁ ≈ D₁ • D₂ →
              (K₁ • D₁) • (K₂ • D₂) ≈ (K₂ • D₂) • (K₁ • D₁)
    sep-alg {K₁} {D₁} {K₂} {D₂} c₁ c₂ kk dd = begin
      (K₁ • D₁) • (K₂ • D₂)     ≈⟨ assoc ⟩
      K₁ • (D₁ • (K₂ • D₂))     ≈⟨ back K₁ c₁ ⟩
      K₁ • ((K₂ • D₂) • D₁)     ≈⟨ back K₁ assoc ⟩
      K₁ • (K₂ • (D₂ • D₁))     ≈⟨ sym assoc ⟩
      (K₁ • K₂) • (D₂ • D₁)     ≈⟨ cong kk dd ⟩
      (K₂ • K₁) • (D₁ • D₂)     ≈⟨ assoc ⟩
      K₂ • (K₁ • (D₁ • D₂))     ≈⟨ back K₂ (sym assoc) ⟩
      K₂ • ((K₁ • D₁) • D₂)     ≈⟨ back K₂ (sym c₂) ⟩
      K₂ • (D₂ • (K₁ • D₁))     ≈⟨ sym assoc ⟩
      (K₂ • D₂) • (K₁ • D₁)     ∎

    -- Conjugation by an involution.
    flip : ∀ {Xw A B : Word X} → Xw • Xw ≈ ε → A • Xw ≈ Xw • B → Xw • A ≈ B • Xw
    flip {Xw} {A} {B} xx c = begin
      Xw • A                    ≈⟨ sym right-unit ⟩
      (Xw • A) • ε              ≈⟨ back _ (sym xx) ⟩
      (Xw • A) • (Xw • Xw)      ≈⟨ assoc ⟩
      Xw • (A • (Xw • Xw))      ≈⟨ back Xw (sym assoc) ⟩
      Xw • ((A • Xw) • Xw)      ≈⟨ back Xw (front Xw c) ⟩
      Xw • ((Xw • B) • Xw)      ≈⟨ back Xw assoc ⟩
      Xw • (Xw • (B • Xw))      ≈⟨ sym assoc ⟩
      (Xw • Xw) • (B • Xw)      ≈⟨ front _ xx ⟩
      ε • (B • Xw)              ≈⟨ left-unit ⟩
      B • Xw                    ∎

    conj-• : ∀ {U A A′ B B′ : Word X} → U • A ≈ A′ • U → U • B ≈ B′ • U →
             U • (A • B) ≈ (A′ • B′) • U
    conj-• {U} {A} {A′} {B} {B′} cA cB = begin
      U • (A • B)       ≈⟨ sym assoc ⟩
      (U • A) • B       ≈⟨ front B cA ⟩
      (A′ • U) • B      ≈⟨ assoc ⟩
      A′ • (U • B)      ≈⟨ back A′ cB ⟩
      A′ • (B′ • U)     ≈⟨ sym assoc ⟩
      (A′ • B′) • U     ∎

    carry : ∀ {U A B A′ B′ : Word X} → U • U ≈ ε →
            U • A ≈ A′ • U → U • B ≈ B′ • U → A′ ≈ B′ → A ≈ B
    carry {U} {A} {B} {A′} {B′} inv cA cB e = begin
      A                 ≈⟨ sym left-unit ⟩
      ε • A             ≈⟨ front A (sym inv) ⟩
      (U • U) • A       ≈⟨ assoc ⟩
      U • (U • A)       ≈⟨ back U cA ⟩
      U • (A′ • U)      ≈⟨ back U (front U e) ⟩
      U • (B′ • U)      ≈⟨ back U (sym cB) ⟩
      U • (U • B)       ≈⟨ sym assoc ⟩
      (U • U) • B       ≈⟨ front B inv ⟩
      ε • B             ≈⟨ left-unit ⟩
      B                 ∎

    -- The common shape of the crossing and nested reductions.
    by-inv : ∀ {Xw P P′ Q′ Qq : Word X} → Xw • Xw ≈ ε →
             P • Xw ≈ Xw • P′ → Q′ • Xw ≈ Xw • Qq → P′ • Q′ ≈ Q′ • P′ →
             P • Qq ≈ Qq • P
    by-inv xx cP cQ pq =
      carry xx (conj-• (flip xx cP) (sym cQ))
               (conj-• (sym cQ) (flip xx cP)) pq

    ≢< : ∀ {a b : Fin N} → toℕ a < toℕ b → b ≢ a
    ≢< lt e = NP.<⇒≢ lt (Eq.sym (Eq.cong toℕ e))

    <≢ : ∀ {a b : Fin N} → toℕ a < toℕ b → a ≢ b
    <≢ lt e = ≢< lt (Eq.sym e)

  -- Separated: b < c.
  kk-sep : ∀ a b c dd s .(ab : a <ᶠ b) .(cd : c <ᶠ dd) → toℕ b < toℕ c →
           s ≢ a → s ≢ b → s ≢ c → s ≢ dd →
           Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
  kk-sep a b c dd s ab cd bc sa sb sc sd =
    sep-alg (d-ki-pp c dd s a cd (<≢ (NP.<-trans (rel ab) bc))
                                 (<≢ (NP.<-trans (NP.<-trans (rel ab) bc) (rel cd))) sc sd)
            (d-ki-pp a b s c ab (≢< (NP.<-trans (rel ab) bc)) (≢< bc) sa sb)
            (kh-sep (toℕ a) (toℕ b ∸ toℕ a) (toℕ c) (toℕ dd ∸ toℕ c)
                    (Eq.subst (_< toℕ c) (Eq.sym (NP.m+[n∸m]≡n (NP.<⇒≤ (rel ab)))) bc)
                    (Eq.subst (_< N) (Eq.sym (NP.m+[n∸m]≡n (NP.<⇒≤ (rel cd)))) (toℕ<n dd)))
            (fragment (pp-comm c s a s))

  -- Crossing: a < c < b < dd.
  kk-cross : ∀ a b c dd s .(ab : a <ᶠ b) .(cd : c <ᶠ dd) →
             toℕ a < toℕ c → toℕ c < toℕ b → toℕ b < toℕ dd →
             s ≢ a → s ≢ b → s ≢ c → s ≢ dd →
             Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
  kk-cross a b c dd s ab cd ac cb bd sa sb sc sd =
    by-inv (d-≈ (xx-inv s c b cb sc sb))
           (d-ki-swap′ a c b s ac cb sa sc sb)
           (d-ki-swap c b dd s cb bd sc sb sd)
           (kk-sep a c b dd s ac bd cb sa sc sb sd)

  -- Nested: a < c < dd < b.
  kk-nest : ∀ a b c dd s .(ab : a <ᶠ b) .(cd : c <ᶠ dd) →
            toℕ a < toℕ c → toℕ dd < toℕ b →
            s ≢ a → s ≢ b → s ≢ c → s ≢ dd →
            Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
  kk-nest a b c dd s ab cd ac db sa sb sc sd =
    by-inv (d-≈ (xx-inv s dd b db sd sb))
           (d-ki-swap′ a dd b s (NP.<-trans ac (rel cd)) db sa sd sb)
           (d-ki-swap′ c dd b s cd db sc sd sb)
           (kk-cross a dd c b s (NP.<-trans ac (rel cd)) (NP.<-trans (rel cd) db)
                     ac (rel cd) db sa sd sc sb)

  -- Every disjoint configuration.
  d-ki-ki : ∀ a b c dd s .(ab : a <ᶠ b) .(cd : c <ᶠ dd) →
            c ≢ a → c ≢ b → dd ≢ a → dd ≢ b →
            s ≢ a → s ≢ b → s ≢ c → s ≢ dd →
            (d ʷ) (kiw a b s ab • kiw c dd s cd) ≈ (d ʷ) (kiw c dd s cd • kiw a b s ab)
  d-ki-ki a b c dd s ab cd ca cb da db sa sb sc sd =
    go₁ (NP.<-cmp (toℕ b) (toℕ c))
    where
    A = toℕ a ; B = toℕ b ; C = toℕ c ; D = toℕ dd

    ne : ∀ {x y : Fin N} → x ≢ y → toℕ x ≢ toℕ y
    ne n e = n (toℕ-injective e)

    go₄ : Tri (B < D) (B ≡ D) (D < B) → C < A → A < D →
          Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
    go₄ (tri< bd _ _) ca′ ad = sym (kk-nest c dd a b s cd ab ca′ bd sc sd sa sb)
    go₄ (tri≈ _ e _)  ca′ ad = ⊥-elim (ne db (Eq.sym e))
    go₄ (tri> _ _ db′) ca′ ad = sym (kk-cross c dd a b s cd ab ca′ ad db′ sc sd sa sb)

    go₃ : Tri (B < D) (B ≡ D) (D < B) → A < C → C < B →
          Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
    go₃ (tri< bd _ _) ac cb′ = kk-cross a b c dd s ab cd ac cb′ bd sa sb sc sd
    go₃ (tri≈ _ e _)  ac cb′ = ⊥-elim (ne db (Eq.sym e))
    go₃ (tri> _ _ db′) ac cb′ = kk-nest a b c dd s ab cd ac db′ sa sb sc sd

    go₂ : Tri (A < C) (A ≡ C) (C < A) → C < B → A < D →
          Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
    go₂ (tri< ac _ _) cb′ ad = go₃ (NP.<-cmp B D) ac cb′
    go₂ (tri≈ _ e _)  cb′ ad = ⊥-elim (ne ca (Eq.sym e))
    go₂ (tri> _ _ ca′) cb′ ad = go₄ (NP.<-cmp B D) ca′ ad

    go₁′ : Tri (D < A) (D ≡ A) (A < D) → C < B →
           Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
    go₁′ (tri< da′ _ _) cb′ = sym (kk-sep c dd a b s cd ab da′ sc sd sa sb)
    go₁′ (tri≈ _ e _)   cb′ = ⊥-elim (ne da e)
    go₁′ (tri> _ _ ad)  cb′ = go₂ (NP.<-cmp A C) cb′ ad

    go₁ : Tri (B < C) (B ≡ C) (C < B) →
          Q a b s ab • Q c dd s cd ≈ Q c dd s cd • Q a b s ab
    go₁ (tri< bc _ _) = kk-sep a b c dd s ab cd bc sa sb sc sd
    go₁ (tri≈ _ e _)  = ⊥-elim (ne cb (Eq.sym e))
    go₁ (tri> _ _ cb′) = go₁′ (NP.<-cmp D A) cb′
