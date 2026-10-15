------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid rules of P′ on one pair: ki-x, ki-16, ki-ii, ki-sq
--
-- On N = 4 + m indices, each rule at a pair a < b with sink s is the
-- rule at the canonical position — the top pair N − 2, N − 1 with sink
-- N − 3 — conjugated by the K-free word
--
--     u = ρ (b − 1) • L_{a,b} • v,
--
-- the shift chain to the pair b − 1, b (HybridT), the chain down to
-- a, b (HybridPair.lrun), and v = (−1)_[y] X_[y,s] moving the sink
-- wherever those send it to s (`Canon`): u carries every letter of the
-- rule to the canonical one (HybridPair.hyb-conj, sink-conj, `px-conj`)
-- and has a left inverse.  At the canonical position ki-ii is the pair
-- scalar commuting with the hybrid (HybridCen.cz); ki-x, ki-16 and ki-sq
-- there are hypotheses, since they need a fact about the hybrid and the
-- phase pair i_[N−2] i_[N−3]⁻¹ that the scalar and the conjugations by
-- the letters on the pair do not give (scratchpad/four-wire-notes.md).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridOne
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ ; zero) renaming (_<_ to _<ᶠ_ ; suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n ; _≟_)
open import Data.Nat using (zero ; _+_ ; _∸_ ; _<_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (recompute)
open import Word.Base using (ε ; _•_ ; [_]ʷ ; _ʷ)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_ ; pw ; xw)
open import Examples.Groups.Clifford+CS.Auxiliary.Rules using (kiw)
open import Examples.Groups.Clifford+CS.Auxiliary.NF (suc (suc (suc m)))
  using (KFreeʷ ; gen ; nil ; cat ; kf-pp ; kf-px)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc (suc (suc (suc m))))
  using (Ph ; p0 ; p2 ; p3 ; _+ᵖ_ ; +ᵖ-comm ; sp ; ph ; prm ; prm≡ ; ph≡ ; δ ; δ-≢ ; phif
       ; swapF ; swapF-a ; swapF-b ; swapF-o ; _≐_ ; eqv ; idPP ; ≐-trans ; ⊙-cong ; ⊙-idˡ)
open import Examples.Groups.Clifford+CS.Auxiliary.Template (suc (suc (suc m)))
  using (xd ; kf-xd ; xd-prm ; xd-ph ; xd-same ; tx ; emp ; ⌜_⌝ ; _•ᵗ_ ; module At)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique (suc (suc (suc m)))
  using (A5 ; prm-inj)
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
open HCen Γ m p p′ l h k using (tT ; tT1 ; tB ; toT ; toT1 ; toB)
open HT Γ m p p′ l h k using (ρw ; ρb ; kf-ρw ; kf-ρb ; ρ-a ; ρ-b)
open HP Γ m p p′ l h k using (lrun ; hrun ; kf-lrun ; kf-hrun ; lrun-top ; lrun-hi ; δπ)

------------------------------------------------------------------------
-- The canonical position

tT<tT1 : tT <ᶠ tT1
tT<tT1 = Eq.subst₂ _<_ (Eq.sym toT) (Eq.sym toT1) (NP.n<1+n top)

private
  tB≢tT : tB ≢ tT
  tB≢tT e = NP.<⇒≢ (NP.n<1+n (suc m)) (Eq.trans (Eq.sym toB) (Eq.trans (Eq.cong toℕ e) toT))

  tB≢tT1 : tB ≢ tT1
  tB≢tT1 e = NP.<⇒≢ (NP.<-trans (NP.n<1+n (suc m)) (NP.n<1+n top))
                    (Eq.trans (Eq.sym toB) (Eq.trans (Eq.cong toℕ e) toT1))

------------------------------------------------------------------------
-- The deciding letter (−1)_[c] X_[x,y]

private
  xd-fix : ∀ c x y t → t ≢ x → t ≢ y → prm (sp (xd c x y)) t ≡ t
  xd-fix c x y t tx′ ty = go (x ≟ y)
    where
    go : Dec (x ≡ y) → prm (sp (xd c x y)) t ≡ t
    go (yes e) = prm≡ (xd-same c x y e) t
    go (no ne) = Eq.trans (xd-prm c x y t ne) (swapF-o x y t tx′ ty)

  xd-ph0 : ∀ c x y t → t ≢ c → ph (sp (xd c x y)) t ≡ p0
  xd-ph0 c x y t tc = go (x ≟ y)
    where
    go : Dec (x ≡ y) → ph (sp (xd c x y)) t ≡ p0
    go (yes e) = ph≡ (xd-same c x y e) t
    go (no ne) = Eq.trans (xd-ph c x y t ne) (Eq.cong (λ b → phif b p2) (δ-≢ c t tc))

  xd-send : ∀ x y → prm (sp (xd x x y)) x ≡ y
  xd-send x y = go (x ≟ y)
    where
    go : Dec (x ≡ y) → prm (sp (xd x x y)) x ≡ y
    go (yes e) = Eq.trans (prm≡ (xd-same x x y e) x) e
    go (no ne) = Eq.trans (xd-prm x x y x ne) (swapF-a x y)

  -- (−1)_[y] X_[y,s] has the left inverse (−1)_[s] X_[y,s].
  xd-inv : ∀ y s → PB._≈_ (N F,_===_) (xd s y s • xd y y s) ε
  xd-inv y s = go (y ≟ s)
    where
    go : Dec (y ≡ s) → PB._≈_ (N F,_===_) (xd s y s • xd y y s) ε
    go (yes e) = A5 (cat (kf-xd s y s) (kf-xd y y s)) nil
                    (≐-trans (⊙-cong (xd-same s y s e) (xd-same y y s e)) (⊙-idˡ idPP))
    go (no ne) = TA.A5-tmpl (⌜ tx j1 j0 j1 ⌝ •ᵗ ⌜ tx j0 j0 j1 ⌝) emp Eq.refl
      where
      j0 j1 : Fin 2
      j0 = zero
      j1 = fsuc zero

      ι : Fin 2 → Fin N
      ι zero        = y
      ι (fsuc zero) = s

      inj : ∀ {x x′ : Fin 2} → ι x ≡ ι x′ → x ≡ x′
      inj {zero}      {zero}      e = Eq.refl
      inj {zero}      {fsuc zero} e = ⊥-elim (ne e)
      inj {fsuc zero} {zero}      e = ⊥-elim (ne (Eq.sym e))
      inj {fsuc zero} {fsuc zero} e = Eq.refl

      module TA = At ι inj

------------------------------------------------------------------------
-- The decoded statements

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))))
  (shift : ∀ {j} → suc (suc j) < N →
           (l j • l (suc j)) • k j ≈ k (suc j) • (l j • l (suc j)))
  -- ki-x, ki-16 and ki-sq at the canonical position.
  (x₀ : (d ʷ) (kiw tT tT1 tB tT<tT1 • (pw tT1 tB • pw tT1 tB))
        ≈ (d ʷ) (xw tB tT tT1 tT<tT1 • kiw tT tT1 tB tT<tT1))
  (16₀ : (d ʷ) (kiw tT tT1 tB tT<tT1 • (pw tT1 tB • (pw tT1 tB • pw tT1 tB)))
         ≈ (d ʷ) (pw tT1 tB • (kiw tT tT1 tB tT<tT1 • (pw tT1 tB • kiw tT tT1 tB tT<tT1))))
  (sq₀ : (d ʷ) ((kiw tT tT1 tB tT<tT1 • kiw tT tT1 tB tT<tT1) • (pw tT tB • pw tT1 tB))
         ≈ ε) where

  open FrN.Facts F
  open FrN.Proofs F
  open Tools Γ hiding (_≈_)
  open HCen.Proofs Γ m p p′ l h k F T sc using (d-≈ ; cz)
  open HT.Proofs Γ m p p′ l h k F T sc shift using (dρ-inv)
  open HP.Proofs Γ m p p′ l h k F T sc shift using (hyb-conj ; sink-conj ; dHL)

  ----------------------------------------------------------------------
  -- A K-free letter (−1)_[c] X_[x,y], carried

  px-conj : ∀ {u : W} (c x y c′ x′ y′ : Fin N) .(xy : x <ᶠ y) .(xy′ : x′ <ᶠ y′) →
            KFreeʷ u → prm (sp u) c′ ≡ c → prm (sp u) x′ ≡ x → prm (sp u) y′ ≡ y →
            ph (sp u) x′ ≡ ph (sp u) y′ →
            (d ʷ) u • d (px c x y xy) ≈ d (px c′ x′ y′ xy′) • (d ʷ) u
  px-conj {u} c x y c′ x′ y′ xy xy′ ku ec ex ey φ =
    d-≈ (A5 (cat ku (gen (kf-px c x y xy))) (cat (gen (kf-px c′ x′ y′ xy′)) ku)
            (eqv phs pms))
    where
    π = prm (sp u)

    pms : ∀ t → swapF x y (π t) ≡ π (swapF x′ y′ t)
    pms t = go (t ≟ x′) (t ≟ y′)
      where
      go : Dec (t ≡ x′) → Dec (t ≡ y′) → swapF x y (π t) ≡ π (swapF x′ y′ t)
      go (yes Eq.refl) _ =
        Eq.trans (Eq.cong (swapF x y) ex)
          (Eq.trans (swapF-a x y) (Eq.sym (Eq.trans (Eq.cong π (swapF-a x′ y′)) ey)))
      go (no _) (yes Eq.refl) =
        Eq.trans (Eq.cong (swapF x y) ey)
          (Eq.trans (swapF-b x y) (Eq.sym (Eq.trans (Eq.cong π (swapF-b x′ y′)) ex)))
      go (no nx) (no ny) =
        Eq.trans (swapF-o x y (π t) (λ e → nx (prm-inj u (Eq.trans e (Eq.sym ex))))
                                    (λ e → ny (prm-inj u (Eq.trans e (Eq.sym ey)))))
                 (Eq.cong π (Eq.sym (swapF-o x′ y′ t nx ny)))

    phu : ∀ t → ph (sp u) t ≡ ph (sp u) (swapF x′ y′ t)
    phu t = go (t ≟ x′) (t ≟ y′)
      where
      go : Dec (t ≡ x′) → Dec (t ≡ y′) → ph (sp u) t ≡ ph (sp u) (swapF x′ y′ t)
      go (yes Eq.refl) _ = Eq.trans φ (Eq.cong (ph (sp u)) (Eq.sym (swapF-a x′ y′)))
      go (no _) (yes Eq.refl) =
        Eq.trans (Eq.sym φ) (Eq.cong (ph (sp u)) (Eq.sym (swapF-b x′ y′)))
      go (no nx) (no ny) = Eq.cong (ph (sp u)) (Eq.sym (swapF-o x′ y′ t nx ny))

    phs : ∀ t → ph (sp (u • xw c x y xy)) t ≡ ph (sp (xw c′ x′ y′ xy′ • u)) t
    phs t = Eq.trans (Eq.cong₂ _+ᵖ_ (phu t) (Eq.cong (λ b → phif b p2 +ᵖ p0) (δπ u c′ c ec t)))
                     (+ᵖ-comm (ph (sp u) (swapF x′ y′ t)) (phif (δ c′ t) p2 +ᵖ p0))

  ----------------------------------------------------------------------
  -- Carrying a rule

  private
    conj-• : ∀ {U A A′ B B′ : Word X} → U • A ≈ A′ • U → U • B ≈ B′ • U →
             U • (A • B) ≈ (A′ • B′) • U
    conj-• {U} {A} {A′} {B} {B′} cA cB = begin
      U • (A • B)       ≈⟨ sym assoc ⟩
      (U • A) • B       ≈⟨ front B cA ⟩
      (A′ • U) • B      ≈⟨ assoc ⟩
      A′ • (U • B)      ≈⟨ back A′ cB ⟩
      A′ • (B′ • U)     ≈⟨ sym assoc ⟩
      (A′ • B′) • U     ∎

    conj-ε : ∀ {U : Word X} → U • ε ≈ ε • U
    conj-ε = trans right-unit (sym left-unit)

    carry : ∀ {U Ū A B A′ B′ : Word X} → Ū • U ≈ ε →
            U • A ≈ A′ • U → U • B ≈ B′ • U → A′ ≈ B′ → A ≈ B
    carry {U} {Ū} {A} {B} {A′} {B′} inv cA cB e = begin
      A                 ≈⟨ sym left-unit ⟩
      ε • A             ≈⟨ front A (sym inv) ⟩
      (Ū • U) • A       ≈⟨ assoc ⟩
      Ū • (U • A)       ≈⟨ back Ū cA ⟩
      Ū • (A′ • U)      ≈⟨ back Ū (front U e) ⟩
      Ū • (B′ • U)      ≈⟨ back Ū (sym cB) ⟩
      Ū • (U • B)       ≈⟨ sym assoc ⟩
      (Ū • U) • B       ≈⟨ front B inv ⟩
      ε • B             ≈⟨ left-unit ⟩
      B                 ∎

  ----------------------------------------------------------------------
  -- The conjugator to the canonical position

  module Canon (a b s : Fin N) .(ab : a <ᶠ b) (sa : s ≢ a) (sb : s ≢ b) where

    private
      A e₀ c e : ℕ
      A  = toℕ a
      e₀ = toℕ b ∸ suc A
      c  = A + e₀
      e  = top ∸ c

      gap : suc c ≡ toℕ b
      gap = NP.m+[n∸m]≡n (recompute (toℕ a NP.<? toℕ b) ab)

      qc : suc c < N
      qc = Eq.subst (_< N) (Eq.sym gap) (toℕ<n b)

      qAe : A + e₀ < N
      qAe = NP.<-trans (NP.n<1+n _) qc

      ce : c + e ≡ top
      ce = NP.m+[n∸m]≡n (NP.≤-pred (NP.≤-pred qc))

      qce : suc (c + e) < N
      qce = Eq.subst (λ z → suc z < N) (Eq.sym ce) (NP.n<1+n (suc top))

      R L : W
      R = ρw c e
      L = lrun A e₀

      u₁ : W
      u₁ = R • L

      ρT  = ρ-a c e qce tT  (Eq.trans toT (Eq.sym ce))
      ρT1 = ρ-b c e qce tT1 (Eq.trans toT1 (Eq.cong suc (Eq.sym ce)))
      lT  = lrun-top A e₀ qAe (prm (sp R) tT) (proj₁ ρT)
      lT1 = lrun-hi A e₀ qAe (prm (sp R) tT1)
              (Eq.subst (c <_) (Eq.sym (proj₁ ρT1)) (NP.n<1+n c))

      imT : prm (sp u₁) tT ≡ a
      imT = toℕ-injective (proj₁ lT)

      imT1 : prm (sp u₁) tT1 ≡ b
      imT1 = toℕ-injective (Eq.trans (Eq.cong toℕ (proj₁ lT1)) (Eq.trans (proj₁ ρT1) gap))

      phT : ph (sp u₁) tT ≡ p0
      phT = Eq.cong₂ _+ᵖ_ (proj₂ ρT) (proj₂ lT)

      phT1 : ph (sp u₁) tT1 ≡ p0
      phT1 = Eq.cong₂ _+ᵖ_ (proj₂ ρT1) (proj₂ lT1)

      y : Fin N
      y = prm (sp u₁) tB

      ya : a ≢ y
      ya e′ = tB≢tT (prm-inj u₁ (Eq.trans (Eq.sym e′) (Eq.sym imT)))

      yb : b ≢ y
      yb e′ = tB≢tT1 (prm-inj u₁ (Eq.trans (Eq.sym e′) (Eq.sym imT1)))

      v : W
      v = xd y y s

    u : W
    u = u₁ • v

    ku : KFreeʷ u
    ku = cat (cat (kf-ρw c e) (kf-lrun A e₀)) (kf-xd y y s)

    u-T : prm (sp u) tT ≡ a
    u-T = Eq.trans (Eq.cong (prm (sp v)) imT) (xd-fix y y s a ya (λ e′ → sa (Eq.sym e′)))

    u-T1 : prm (sp u) tT1 ≡ b
    u-T1 = Eq.trans (Eq.cong (prm (sp v)) imT1) (xd-fix y y s b yb (λ e′ → sb (Eq.sym e′)))

    u-B : prm (sp u) tB ≡ s
    u-B = xd-send y s

    u-ph : ph (sp u) tT ≡ ph (sp u) tT1
    u-ph = Eq.trans (Eq.cong₂ _+ᵖ_ phT (Eq.trans (Eq.cong (ph (sp v)) imT) (xd-ph0 y y s a ya)))
             (Eq.sym (Eq.cong₂ _+ᵖ_ phT1 (Eq.trans (Eq.cong (ph (sp v)) imT1)
                                                   (xd-ph0 y y s b yb))))

    U Ū : Word X
    U = (d ʷ) u
    Ū = (d ʷ) (xd s y s • (hrun A e₀ • ρb c e))

    inv : Ū • U ≈ ε
    inv = begin
      (V̄ • (H • R̄)) • ((Rd • Ld) • V)     ≈⟨ assoc ⟩
      V̄ • ((H • R̄) • ((Rd • Ld) • V))     ≈⟨ back V̄ assoc ⟩
      V̄ • (H • (R̄ • ((Rd • Ld) • V)))     ≈⟨ back V̄ (back H (back R̄ assoc)) ⟩
      V̄ • (H • (R̄ • (Rd • (Ld • V))))     ≈⟨ back V̄ (back H (sym assoc)) ⟩
      V̄ • (H • ((R̄ • Rd) • (Ld • V)))     ≈⟨ back V̄ (back H (front (Ld • V) (dρ-inv c e qce))) ⟩
      V̄ • (H • (ε • (Ld • V)))            ≈⟨ back V̄ (back H left-unit) ⟩
      V̄ • (H • (Ld • V))                  ≈⟨ back V̄ (sym assoc) ⟩
      V̄ • ((H • Ld) • V)                  ≈⟨ back V̄ (front V (dHL A e₀ qAe)) ⟩
      V̄ • (ε • V)                         ≈⟨ back V̄ left-unit ⟩
      V̄ • V                               ≈⟨ d-≈ (xd-inv y s) ⟩
      ε                                   ∎
      where
      V̄ = (d ʷ) (xd s y s)
      V  = (d ʷ) v
      H  = (d ʷ) (hrun A e₀)
      R̄  = (d ʷ) (ρb c e)
      Rd = (d ʷ) R
      Ld = (d ʷ) L

    -- The letters of the one-pair rules.
    c-ki : U • d (ki a b s ab) ≈ d (ki tT tT1 tB tT<tT1) • U
    c-ki = hyb-conj a b s tT tT1 tB ab tT<tT1 ku u-T u-T1 u-B u-ph

    c-pa : U • d (pp a s) ≈ d (pp tT tB) • U
    c-pa = sink-conj a s tT tB ku u-T u-B

    c-pb : U • d (pp b s) ≈ d (pp tT1 tB) • U
    c-pb = sink-conj b s tT1 tB ku u-T1 u-B

    c-x : U • d (px s a b ab) ≈ d (px tB tT tT1 tT<tT1) • U
    c-x = px-conj s a b tB tT tT1 ab tT<tT1 ku u-B u-T u-T1 u-ph

  ----------------------------------------------------------------------
  -- ki-ii at the canonical position: the pair scalar

  private
    kh≡ : dKIa (toℕ tT) (toℕ tT1 ∸ toℕ tT) ≡ k top
    kh≡ = Eq.trans (Eq.cong₂ (λ x y → dKIa x (y ∸ x)) toT toT1)
                   (Eq.cong (dKIa top) (sA∸A top))

  ii₀ : (d ʷ) (kiw tT tT1 tB tT<tT1 • (pw tT tB • pw tT1 tB))
        ≈ (d ʷ) (pw tT tB • (pw tT1 tB • kiw tT tT1 tB tT<tT1))
  ii₀ = Eq.subst (λ K → (K • D) • (D • E) ≈ D • (E • (K • D))) (Eq.sym kh≡) (begin
    (k top • D) • (D • E)      ≈⟨ assoc ⟩
    k top • (D • (D • E))      ≈⟨ back (k top) (comm-•ʳ refl (fragment (pp-comm tT tB tT1 tB))) ⟩
    k top • ((D • E) • D)      ≈⟨ sym assoc ⟩
    (k top • (D • E)) • D      ≈⟨ front D (sym (cz p3)) ⟩
    ((D • E) • k top) • D      ≈⟨ assoc ⟩
    (D • E) • (k top • D)      ≈⟨ assoc ⟩
    D • (E • (k top • D))      ∎)
    where
    D = dPP (toℕ tT) (toℕ tB)
    E = dPP (toℕ tT1) (toℕ tB)

  ----------------------------------------------------------------------
  -- The rules at every pair

  d-ki-x : ∀ a b s .(ab : a <ᶠ b) → s ≢ a → s ≢ b →
           (d ʷ) (kiw a b s ab • (pw b s • pw b s)) ≈ (d ʷ) (xw s a b ab • kiw a b s ab)
  d-ki-x a b s ab sa sb =
    carry inv (conj-• c-ki (conj-• c-pb c-pb)) (conj-• c-x c-ki) x₀
    where open Canon a b s ab sa sb

  d-ki-16 : ∀ a b s .(ab : a <ᶠ b) → s ≢ a → s ≢ b →
            (d ʷ) (kiw a b s ab • (pw b s • (pw b s • pw b s)))
            ≈ (d ʷ) (pw b s • (kiw a b s ab • (pw b s • kiw a b s ab)))
  d-ki-16 a b s ab sa sb =
    carry inv (conj-• c-ki (conj-• c-pb (conj-• c-pb c-pb)))
              (conj-• c-pb (conj-• c-ki (conj-• c-pb c-ki))) 16₀
    where open Canon a b s ab sa sb

  d-ki-ii : ∀ a b s .(ab : a <ᶠ b) → s ≢ a → s ≢ b →
            (d ʷ) (kiw a b s ab • (pw a s • pw b s))
            ≈ (d ʷ) (pw a s • (pw b s • kiw a b s ab))
  d-ki-ii a b s ab sa sb =
    carry inv (conj-• c-ki (conj-• c-pa c-pb)) (conj-• c-pa (conj-• c-pb c-ki)) ii₀
    where open Canon a b s ab sa sb

  d-ki-sq : ∀ a b s .(ab : a <ᶠ b) → s ≢ a → s ≢ b →
            (d ʷ) ((kiw a b s ab • kiw a b s ab) • (pw a s • pw b s)) ≈ ε
  d-ki-sq a b s ab sa sb =
    carry inv (conj-• (conj-• c-ki c-ki) (conj-• c-pa c-pb)) conj-ε sq₀
    where open Canon a b s ab sa sb
