------------------------------------------------------------------------
-- Presentations of groups
--
-- The decoded hybrid letter on any pair, carried by K-free words, and
-- the hybrid rules of P′ with one hybrid on each side
--
-- On N = 4 + m indices, the decoding of K_[a,b] i_s⁻¹ is
--
--     dKIa a (b − a) • dPP a s,   dKIa a (b − a) = H • k (b − 1) • L
--
-- with L = l (b−2) ⋯ l a and H = h a ⋯ h (b−2) the decodings of the
-- K-free chains `lrun` and `hrun` (`dKIa-split`).  A K-free word u whose
-- phased permutation sends a′, b′ to a, b with equal phases carries the
-- first factor on a, b to the one on a′, b′ (`pair-transport`): L′ u H
-- sends b′ − 1, b′ to b − 1, b, so HybridT.transport applies to it.
-- The phase pair moves by Corollary A.5 (`sink-conj`), so u carries the
-- whole letter (`hyb-conj`), and with u the K-free letter of the rule
-- that gives ki-pp, ki-px, ki-swap and ki-swap′; ki-sink is the
-- telescope of phase pairs.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridPair
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ) renaming (_<_ to _<ᶠ_)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n ; _≟_) renaming (<-trans to <ᶠ-trans)
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
  using (KFreeʷ ; gen ; nil ; cat ; kf-pp ; kf-px ; sx ; sx-letter ; fin ; fin-toℕ
       ; j<sj<N ; n≢sn)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc (suc (suc (suc m))))
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _+ᵖ_ ; +ᵖ-idʳ ; +ᵖ-comm ; sp ; ph ; prm ; prm≡ ; ph≡
       ; δ ; δ-here ; δ-≢ ; phif ; swapF ; swapF-b ; swapF-o ; sound ; eqv)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique (suc (suc (suc m)))
  using (A5 ; prm-inj ; sx-at ; sx-off)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k using (d ; dPP ; dKIa)
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
import Examples.Groups.Clifford+CS.Lemma88.HybridCen as HCen
import Examples.Groups.Clifford+CS.Lemma88.HybridT as HT
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

private
  N′ N : ℕ
  N′ = suc (suc (suc m))
  N  = suc N′

  W : Set
  W = Word (GenP N)

  module FrN = Fr Γ N p p′ l h k

open PB Γ using (_≈_)
open HTop Γ N p p′ l h k using (top ; TopFar)
open HT Γ m p p′ l h k using (hx ; kf-sx ; kf-hx ; sx-hx ; sx-back ; sx-ph0)

private
  infix 4 _≈ᶠ_
  _≈ᶠ_ : W → W → Set
  _≈ᶠ_ = PB._≈_ (N F,_===_)

------------------------------------------------------------------------
-- The chains

-- lrun c e = sx (c+e−1) ⋯ sx c, which sends c + e to c;
-- hrun c e = hx c ⋯ hx (c+e−1), its inverse.
lrun hrun : ℕ → ℕ → W
lrun c zero    = ε
lrun c (suc e) = lrun (suc c) e • sx c
hrun c zero    = ε
hrun c (suc e) = hx c • hrun (suc c) e

kf-lrun : ∀ c e → KFreeʷ (lrun c e)
kf-lrun c zero    = nil
kf-lrun c (suc e) = cat (kf-lrun (suc c) e) (kf-sx c)

kf-hrun : ∀ c e → KFreeʷ (hrun c e)
kf-hrun c zero    = nil
kf-hrun c (suc e) = cat (kf-hx c) (kf-hrun (suc c) e)

private
  q-tl : ∀ c e → c + suc e < N → suc c + e < N
  q-tl c e q = Eq.subst (_< N) (NP.+-suc c e) q

  q-hd : ∀ c e → c + suc e < N → suc c < N
  q-hd c e q = NP.≤-<-trans (s≤s (NP.m≤m+n c e)) (q-tl c e q)

  ne-sj : ∀ j → suc j ≢ j
  ne-sj j e = n≢sn j (Eq.sym e)

lrun-inv : ∀ c e → c + e < N → (lrun c e • hrun c e) ≈ᶠ ε
lrun-inv c zero    q = PB.left-unit
lrun-inv c (suc e) q =
  PB.trans PB.assoc
    (PB.trans (PB.cong PB.refl
                (PB.trans (PB.sym PB.assoc)
                  (PB.trans (PB.cong (sx-hx c (q-hd c e q)) PB.refl) PB.left-unit)))
              (lrun-inv (suc c) e (q-tl c e q)))

-- The phase of sx j at its lower index.
sx-ph2 : ∀ j (q : suc j < N) t → toℕ t ≡ j → ph (sp (sx j)) t ≡ p2
sx-ph2 j q t e =
  Eq.trans (Eq.cong (λ w → ph (sp w) t) (sx-letter j q))
           (Eq.cong (λ b → phif b p2 +ᵖ p0)
                    (Eq.trans (Eq.cong (δ (fin j (j<sj<N q))) t≡) (δ-here (fin j (j<sj<N q)))))
  where
  t≡ : t ≡ fin j (j<sj<N q)
  t≡ = toℕ-injective (Eq.trans e (Eq.sym (fin-toℕ j (j<sj<N q))))

-- How lrun c e acts: c + e goes to c, [c, c + e) up by one with phase
-- two, and everything else stays.
lrun-top : ∀ c e → c + e < N → ∀ t → toℕ t ≡ c + e →
           toℕ (prm (sp (lrun c e)) t) ≡ c × ph (sp (lrun c e)) t ≡ p0
lrun-top c zero    q t et = Eq.trans et (NP.+-identityʳ c) , Eq.refl
lrun-top c (suc e) q t et =
  sx-back c (q-hd c e q) t₁ (proj₁ ih) ,
  Eq.cong₂ _+ᵖ_ (proj₂ ih) (sx-ph0 c (q-hd c e q) t₁ (λ e′ → ne-sj c (Eq.trans (Eq.sym (proj₁ ih)) e′)))
  where
  ih = lrun-top (suc c) e (q-tl c e q) t (Eq.trans et (NP.+-suc c e))
  t₁ = prm (sp (lrun (suc c) e)) t

lrun-hi : ∀ c e → c + e < N → ∀ t → c + e < toℕ t →
          prm (sp (lrun c e)) t ≡ t × ph (sp (lrun c e)) t ≡ p0
lrun-hi c zero    q t lt = Eq.refl , Eq.refl
lrun-hi c (suc e) q t lt =
  Eq.trans (Eq.cong (prm (sp (sx c))) (proj₁ ih)) (sx-off c (j<sj<N qc) qc t nc nsc) ,
  Eq.cong₂ _+ᵖ_ (proj₂ ih) (Eq.trans (Eq.cong (ph (sp (sx c))) (proj₁ ih)) (sx-ph0 c qc t nc))
  where
  qc = q-hd c e q
  lt′ : suc c + e < toℕ t
  lt′ = Eq.subst (_< toℕ t) (NP.+-suc c e) lt
  ih = lrun-hi (suc c) e (q-tl c e q) t lt′

  sc<t : suc c < toℕ t
  sc<t = NP.≤-<-trans (s≤s (NP.m≤m+n c e)) lt′

  nc : toℕ t ≢ c
  nc e′ = NP.<⇒≢ (NP.<-trans (NP.n<1+n c) sc<t) (Eq.sym e′)

  nsc : toℕ t ≢ suc c
  nsc e′ = NP.<⇒≢ sc<t (Eq.sym e′)

lrun-lo : ∀ c e → c + e < N → ∀ t → toℕ t < c →
          prm (sp (lrun c e)) t ≡ t × ph (sp (lrun c e)) t ≡ p0
lrun-lo c zero    q t lt = Eq.refl , Eq.refl
lrun-lo c (suc e) q t lt =
  Eq.trans (Eq.cong (prm (sp (sx c))) (proj₁ ih)) (sx-off c (j<sj<N qc) qc t nc nsc) ,
  Eq.cong₂ _+ᵖ_ (proj₂ ih) (Eq.trans (Eq.cong (ph (sp (sx c))) (proj₁ ih)) (sx-ph0 c qc t nc))
  where
  qc = q-hd c e q
  ih = lrun-lo (suc c) e (q-tl c e q) t (NP.<-trans lt (NP.n<1+n c))

  nc : toℕ t ≢ c
  nc = NP.<⇒≢ lt

  nsc : toℕ t ≢ suc c
  nsc = NP.<⇒≢ (NP.<-trans lt (NP.n<1+n c))

lrun-mid : ∀ c e → c + e < N → ∀ t → c ≤ toℕ t → toℕ t < c + e →
           toℕ (prm (sp (lrun c e)) t) ≡ suc (toℕ t) × ph (sp (lrun c e)) t ≡ p2
lrun-mid c zero    q t le lt =
  ⊥-elim (NP.<⇒≱ (Eq.subst (toℕ t <_) (NP.+-identityʳ c) lt) le)
lrun-mid c (suc e) q t le lt = go (toℕ t NP.≟ c)
  where
  qc = q-hd c e q

  go : Dec (toℕ t ≡ c) →
       toℕ (prm (sp (lrun c (suc e))) t) ≡ suc (toℕ t) × ph (sp (lrun c (suc e))) t ≡ p2
  go (yes tc) =
    Eq.trans (Eq.cong (λ z → toℕ (prm (sp (sx c)) z)) (proj₁ lo))
             (Eq.trans (sx-at c (j<sj<N qc) qc t tc) (Eq.cong suc (Eq.sym tc))) ,
    Eq.cong₂ _+ᵖ_ (proj₂ lo) (Eq.trans (Eq.cong (ph (sp (sx c))) (proj₁ lo)) (sx-ph2 c qc t tc))
    where
    lo = lrun-lo (suc c) e (q-tl c e q) t (Eq.subst (_< suc c) (Eq.sym tc) (NP.n<1+n c))
  go (no tc) =
    Eq.trans (Eq.cong toℕ (sx-off c (j<sj<N qc) qc t₁ nc nsc)) (proj₁ ih) ,
    Eq.trans (Eq.cong₂ _+ᵖ_ (proj₂ ih) (sx-ph0 c qc t₁ nc)) Eq.refl
    where
    le′ : suc c ≤ toℕ t
    le′ = NP.≤∧≢⇒< le (λ e′ → tc (Eq.sym e′))

    ih = lrun-mid (suc c) e (q-tl c e q) t le′ (Eq.subst (toℕ t <_) (NP.+-suc c e) lt)
    t₁ = prm (sp (lrun (suc c) e)) t

    nc : toℕ t₁ ≢ c
    nc e′ = NP.<⇒≢ (NP.<-trans (NP.n<1+n c) (s≤s le′)) (Eq.sym (Eq.trans (Eq.sym (proj₁ ih)) e′))

    nsc : toℕ t₁ ≢ suc c
    nsc e′ = NP.<⇒≢ (s≤s le′) (Eq.sym (Eq.trans (Eq.sym (proj₁ ih)) e′))

------------------------------------------------------------------------
-- Moving a phase pair: Corollary A.5 on the conjugate

-- A permutation sending x′ to x reads δ x through itself as δ x′.
δπ : ∀ (u : W) (x′ x : Fin N) → prm (sp u) x′ ≡ x → ∀ t → δ x (prm (sp u) t) ≡ δ x′ t
δπ u x′ x e t = go (t ≟ x′)
  where
  go : Dec (t ≡ x′) → δ x (prm (sp u) t) ≡ δ x′ t
  go (yes Eq.refl) = Eq.trans (Eq.cong (δ x) e) (Eq.trans (δ-here x) (Eq.sym (δ-here x′)))
  go (no ne) = Eq.trans (δ-≢ x (prm (sp u) t) (λ e′ → ne (prm-inj u (Eq.trans e′ (Eq.sym e)))))
                        (Eq.sym (δ-≢ x′ t ne))

------------------------------------------------------------------------
-- The decoded statements

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))))
  (shift : ∀ {j} → suc (suc j) < N →
           (l j • l (suc j)) • k j ≈ k (suc j) • (l j • l (suc j))) where

  open FrN.Facts F
  open FrN.Proofs F
  open Tools Γ hiding (_≈_)
  open HCen.Proofs Γ m p p′ l h k F T sc using (d-≈)
  open HT.Proofs Γ m p p′ l h k F T sc shift using (transport ; d-sx ; d-hx)

  ----------------------------------------------------------------------
  -- K_[a, a+e+1] i_a⁻¹ = H • k (a + e) • L

  dKIa-split : ∀ a e → a + e < N →
               dKIa a (suc e) ≈ (d ʷ) (hrun a e) • (k (a + e) • (d ʷ) (lrun a e))
  dKIa-split a zero    q =
    Eq.subst (λ z → k a ≈ ε • (k z • ε)) (Eq.sym (NP.+-identityʳ a))
             (sym (trans left-unit right-unit))
  dKIa-split a (suc e) q =
    Eq.subst₂ (λ x y → h a • dKIa (suc a) (suc e) • l a ≈ (x • H′) • (k (a + suc e) • (L′ • y)))
              (Eq.sym (d-hx a qa)) (Eq.sym (d-sx a qa))
      (Eq.subst (λ z → h a • dKIa (suc a) (suc e) • l a ≈ (h a • H′) • (k z • (L′ • l a)))
                (Eq.sym (NP.+-suc a e)) (begin
        h a • (dKIa (suc a) (suc e) • l a)       ≈⟨ back (h a) (front (l a) (dKIa-split (suc a) e (q-tl a e q))) ⟩
        h a • ((H′ • (K • L′)) • l a)             ≈⟨ back (h a) assoc ⟩
        h a • (H′ • ((K • L′) • l a))             ≈⟨ back (h a) (back H′ assoc) ⟩
        h a • (H′ • (K • (L′ • l a)))             ≈⟨ sym assoc ⟩
        (h a • H′) • (K • (L′ • l a))             ∎))
    where
    qa = q-hd a e q
    H′ = (d ʷ) (hrun (suc a) e)
    L′ = (d ʷ) (lrun (suc a) e)
    K  = k (suc a + e)

  dHL : ∀ a e → a + e < N → (d ʷ) (hrun a e) • (d ʷ) (lrun a e) ≈ ε
  dHL a zero    q = left-unit
  dHL a (suc e) q =
    Eq.subst₂ (λ x y → (x • H′) • (L′ • y) ≈ ε) (Eq.sym (d-hx a qa)) (Eq.sym (d-sx a qa)) (begin
      (h a • H′) • (L′ • l a)     ≈⟨ assoc ⟩
      h a • (H′ • (L′ • l a))     ≈⟨ back (h a) (sym assoc) ⟩
      h a • ((H′ • L′) • l a)     ≈⟨ back (h a) (front (l a) (dHL (suc a) e (q-tl a e q))) ⟩
      h a • (ε • l a)             ≈⟨ back (h a) left-unit ⟩
      h a • l a                   ≈⟨ h-inv qa ⟩
      ε                           ∎)
    where
    qa = q-hd a e q
    H′ = (d ʷ) (hrun (suc a) e)
    L′ = (d ʷ) (lrun (suc a) e)

  ----------------------------------------------------------------------
  -- The transport of K_[a,b] i_a⁻¹

  private
    alg2 : ∀ {U H L H′ L′ kc kc′ : Word X} → H • L ≈ ε → H′ • L′ ≈ ε →
           (L′ • (U • H)) • kc ≈ kc′ • (L′ • (U • H)) →
           U • (H • (kc • L)) ≈ (H′ • (kc′ • L′)) • U
    alg2 {U} {H} {L} {H′} {L′} {kc} {kc′} iH iH′ cW = sym (begin
      (H′ • (kc′ • L′)) • U                  ≈⟨ sym right-unit ⟩
      ((H′ • (kc′ • L′)) • U) • ε            ≈⟨ back _ (sym iH) ⟩
      ((H′ • (kc′ • L′)) • U) • (H • L)      ≈⟨ assoc ⟩
      (H′ • (kc′ • L′)) • (U • (H • L))      ≈⟨ assoc ⟩
      H′ • ((kc′ • L′) • (U • (H • L)))      ≈⟨ back H′ assoc ⟩
      H′ • (kc′ • (L′ • (U • (H • L))))      ≈⟨ back H′ (back kc′ (back L′ (sym assoc))) ⟩
      H′ • (kc′ • (L′ • ((U • H) • L)))      ≈⟨ back H′ (back kc′ (sym assoc)) ⟩
      H′ • (kc′ • ((L′ • (U • H)) • L))      ≈⟨ back H′ (sym assoc) ⟩
      H′ • ((kc′ • (L′ • (U • H))) • L)      ≈⟨ back H′ (front L (sym cW)) ⟩
      H′ • (((L′ • (U • H)) • kc) • L)       ≈⟨ back H′ assoc ⟩
      H′ • ((L′ • (U • H)) • (kc • L))       ≈⟨ back H′ assoc ⟩
      H′ • (L′ • ((U • H) • (kc • L)))       ≈⟨ sym assoc ⟩
      (H′ • L′) • ((U • H) • (kc • L))       ≈⟨ front _ iH′ ⟩
      ε • ((U • H) • (kc • L))               ≈⟨ left-unit ⟩
      (U • H) • (kc • L)                     ≈⟨ assoc ⟩
      U • (H • (kc • L))                     ∎)

  pair-transport : ∀ {u : W} (a e a′ e′ : ℕ) → suc (a + e) < N → suc (a′ + e′) < N →
    KFreeʷ u →
    (∀ t → toℕ t ≡ a′ → toℕ (prm (sp u) t) ≡ a) →
    (∀ t → toℕ t ≡ suc (a′ + e′) → toℕ (prm (sp u) t) ≡ suc (a + e)) →
    (∀ t t′ → toℕ t ≡ a′ → toℕ t′ ≡ suc (a′ + e′) → ph (sp u) t ≡ ph (sp u) t′) →
    (d ʷ) u • dKIa a (suc e) ≈ dKIa a′ (suc e′) • (d ʷ) u
  pair-transport {u} a e a′ e′ qb qb′ ku πa πb φ =
    trans (back ((d ʷ) u) (dKIa-split a e qe))
      (trans (alg2 (dHL a e qe) (dHL a′ e′ qe′) cW)
             (front ((d ʷ) u) (sym (dKIa-split a′ e′ qe′))))
    where
    qe : a + e < N
    qe = NP.<-trans (NP.n<1+n _) qb

    qe′ : a′ + e′ < N
    qe′ = NP.<-trans (NP.n<1+n _) qb′

    Lw = lrun a e
    Hw = hrun a e
    L′w = lrun a′ e′

    w : W
    w = L′w • (u • Hw)

    kw : KFreeʷ w
    kw = cat (kf-lrun a′ e′) (cat ku (kf-hrun a e))

    inv = sound (lrun-inv a e qe)

    -- The two points on the far side.
    sA : Fin N
    sA = fin (a + e) qe

    sB : Fin N
    sB = fin (suc (a + e)) qb

    tA = lrun-top a e qe sA (fin-toℕ _ qe)
    hB = lrun-hi a e qe sB (Eq.subst (a + e <_) (Eq.sym (fin-toℕ _ qb)) (NP.n<1+n _))

    -- Where L′ u H sends c′ = a′ + e′ and c′ + 1.
    A0 : ∀ t → toℕ t ≡ a′ + e′ → prm (sp u) (prm (sp L′w) t) ≡ prm (sp Lw) sA
    A0 t et = toℕ-injective (Eq.trans (πa _ (proj₁ (lrun-top a′ e′ qe′ t et)))
                                      (Eq.sym (proj₁ tA)))

    hiB : ∀ t → toℕ t ≡ suc (a′ + e′) →
          prm (sp L′w) t ≡ t × ph (sp L′w) t ≡ p0
    hiB t et = lrun-hi a′ e′ qe′ t (Eq.subst (a′ + e′ <_) (Eq.sym et) (NP.n<1+n _))

    B0 : ∀ t → toℕ t ≡ suc (a′ + e′) → prm (sp u) (prm (sp L′w) t) ≡ prm (sp Lw) sB
    B0 t et = toℕ-injective
                (Eq.trans (Eq.cong (λ z → toℕ (prm (sp u) z)) (proj₁ (hiB t et)))
                  (Eq.trans (πb t et)
                    (Eq.sym (Eq.trans (Eq.cong toℕ (proj₁ hB)) (fin-toℕ _ qb)))))

    πa′ : ∀ t → toℕ t ≡ a′ + e′ → toℕ (prm (sp w) t) ≡ a + e
    πa′ t et = Eq.trans (Eq.cong (λ z → toℕ (prm (sp Hw) z)) (A0 t et))
                        (Eq.trans (Eq.cong toℕ (prm≡ inv sA)) (fin-toℕ _ qe))

    πb′ : ∀ t → toℕ t ≡ suc (a′ + e′) → toℕ (prm (sp w) t) ≡ suc (a + e)
    πb′ t et = Eq.trans (Eq.cong (λ z → toℕ (prm (sp Hw) z)) (B0 t et))
                        (Eq.trans (Eq.cong toℕ (prm≡ inv sB)) (fin-toℕ _ qb))

    -- The phases of H at the two points are zero, being minus L's.
    phHA : ph (sp Hw) (prm (sp Lw) sA) ≡ p0
    phHA = Eq.trans (Eq.cong (_+ᵖ ph (sp Hw) (prm (sp Lw) sA)) (Eq.sym (proj₂ tA)))
                    (ph≡ inv sA)

    phHB : ph (sp Hw) (prm (sp Lw) sB) ≡ p0
    phHB = Eq.trans (Eq.cong (_+ᵖ ph (sp Hw) (prm (sp Lw) sB)) (Eq.sym (proj₂ hB)))
                    (ph≡ inv sB)

    phA : ∀ t → toℕ t ≡ a′ + e′ → ph (sp w) t ≡ ph (sp u) (prm (sp L′w) t)
    phA t et =
      Eq.trans (Eq.cong₂ _+ᵖ_ (proj₂ (lrun-top a′ e′ qe′ t et))
                              (Eq.cong (ph (sp u) (prm (sp L′w) t) +ᵖ_)
                                       (Eq.trans (Eq.cong (ph (sp Hw)) (A0 t et)) phHA)))
               (+ᵖ-idʳ _)

    phB : ∀ t → toℕ t ≡ suc (a′ + e′) → ph (sp w) t ≡ ph (sp u) (prm (sp L′w) t)
    phB t et =
      Eq.trans (Eq.cong₂ _+ᵖ_ (proj₂ (hiB t et))
                              (Eq.cong (ph (sp u) (prm (sp L′w) t) +ᵖ_)
                                       (Eq.trans (Eq.cong (ph (sp Hw)) (B0 t et)) phHB)))
               (+ᵖ-idʳ _)

    φw : ∀ t t′ → toℕ t ≡ a′ + e′ → toℕ t′ ≡ suc (a′ + e′) → ph (sp w) t ≡ ph (sp w) t′
    φw t t′ et et′ =
      Eq.trans (phA t et)
        (Eq.trans (φ _ _ (proj₁ (lrun-top a′ e′ qe′ t et))
                         (Eq.trans (Eq.cong toℕ (proj₁ (hiB t′ et′))) et′))
                  (Eq.sym (phB t′ et′)))

    le-top : ∀ {c} → suc c < N → c ≤ top
    le-top q = NP.≤-pred (NP.≤-pred q)

    cW : (d ʷ) w • k (a + e) ≈ k (a′ + e′) • (d ʷ) w
    cW = transport (a + e) (a′ + e′) (le-top qb) (le-top qb′) kw πa′ πb′ φw

  ----------------------------------------------------------------------
  -- The phase pair, by Corollary A.5

  sink-conj : ∀ {u : W} (a s a′ s′ : Fin N) → KFreeʷ u →
              prm (sp u) a′ ≡ a → prm (sp u) s′ ≡ s →
              (d ʷ) u • d (pp a s) ≈ d (pp a′ s′) • (d ʷ) u
  sink-conj {u} a s a′ s′ ku ea es =
    d-≈ (A5 (cat ku (gen (kf-pp a s))) (cat (gen (kf-pp a′ s′)) ku) (eqv phs (λ _ → Eq.refl)))
    where
    phs : ∀ t → ph (sp (u • pw a s)) t ≡ ph (sp (pw a′ s′ • u)) t
    phs t = Eq.trans (Eq.cong (ph (sp u) t +ᵖ_)
                       (Eq.cong₂ (λ x y → phif x p1 +ᵖ phif y p3)
                                 (δπ u a′ a ea t) (δπ u s′ s es t)))
                     (+ᵖ-comm (ph (sp u) t) _)

  ----------------------------------------------------------------------
  -- The whole letter

  private
    s∸′ : ∀ a e → suc (a + e) ∸ a ≡ suc e
    s∸′ zero    e = Eq.refl
    s∸′ (suc a) e = s∸′ a e

    rel : ∀ {a b : Fin N} → .(a <ᶠ b) → toℕ a < toℕ b
    rel {a} {b} ab = recompute (toℕ a NP.<? toℕ b) ab

    -- A pair a < b written as a , a + 1 + e.
    gap : ∀ {a b : Fin N} → .(a <ᶠ b) → suc (toℕ a + (toℕ b ∸ suc (toℕ a))) ≡ toℕ b
    gap ab = NP.m+[n∸m]≡n (rel ab)

    dk≡ : ∀ (a b : Fin N) .(ab : a <ᶠ b) →
          dKIa (toℕ a) (toℕ b ∸ toℕ a) ≡ dKIa (toℕ a) (suc (toℕ b ∸ suc (toℕ a)))
    dk≡ a b ab = Eq.cong (dKIa (toℕ a))
                         (Eq.trans (Eq.cong (_∸ toℕ a) (Eq.sym (gap ab))) (s∸′ (toℕ a) _))

    ≢< : ∀ {a b : Fin N} → toℕ a < toℕ b → b ≢ a
    ≢< lt e = NP.<⇒≢ lt (Eq.sym (Eq.cong toℕ e))

  hyb-conj : ∀ {u : W} (a b s a′ b′ s′ : Fin N) .(ab : a <ᶠ b) .(ab′ : a′ <ᶠ b′) →
             KFreeʷ u →
             prm (sp u) a′ ≡ a → prm (sp u) b′ ≡ b → prm (sp u) s′ ≡ s →
             ph (sp u) a′ ≡ ph (sp u) b′ →
             (d ʷ) u • d (ki a b s ab) ≈ d (ki a′ b′ s′ ab′) • (d ʷ) u
  hyb-conj {u} a b s a′ b′ s′ ab ab′ ku ea eb es φ =
    Eq.subst₂ (λ x y → U • (x • D) ≈ (y • D′) • U)
              (Eq.sym (dk≡ a b ab)) (Eq.sym (dk≡ a′ b′ ab′)) (begin
      U • (Kh • D)        ≈⟨ sym assoc ⟩
      (U • Kh) • D        ≈⟨ front D kh ⟩
      (Kh′ • U) • D       ≈⟨ assoc ⟩
      Kh′ • (U • D)       ≈⟨ back Kh′ (sink-conj a s a′ s′ ku ea es) ⟩
      Kh′ • (D′ • U)      ≈⟨ sym assoc ⟩
      (Kh′ • D′) • U      ∎)
    where
    U  = (d ʷ) u
    e  = toℕ b ∸ suc (toℕ a)
    e′ = toℕ b′ ∸ suc (toℕ a′)
    Kh  = dKIa (toℕ a) (suc e)
    Kh′ = dKIa (toℕ a′) (suc e′)
    D  = dPP (toℕ a) (toℕ s)
    D′ = dPP (toℕ a′) (toℕ s′)

    kh : U • Kh ≈ Kh′ • U
    kh = pair-transport (toℕ a) e (toℕ a′) e′
           (Eq.subst (_< N) (Eq.sym (gap ab)) (toℕ<n b))
           (Eq.subst (_< N) (Eq.sym (gap ab′)) (toℕ<n b′)) ku
           (λ t et → Eq.trans (Eq.cong (λ z → toℕ (prm (sp u) z)) (toℕ-injective et))
                              (Eq.cong toℕ ea))
           (λ t et → Eq.trans (Eq.cong (λ z → toℕ (prm (sp u) z))
                                       (toℕ-injective (Eq.trans et (gap ab′))))
                              (Eq.trans (Eq.cong toℕ eb) (Eq.sym (gap ab))))
           (λ t t′ et et′ → Eq.trans (Eq.cong (ph (sp u)) (toℕ-injective et))
                              (Eq.trans φ (Eq.cong (ph (sp u))
                                            (Eq.sym (toℕ-injective (Eq.trans et′ (gap ab′)))))))

  ----------------------------------------------------------------------
  -- The rules with one hybrid on each side

  d-ki-sink : ∀ a b s t .(ab : a <ᶠ b) →
              (d ʷ) (kiw a b s ab • pw s t) ≈ (d ʷ) (kiw a b t ab)
  d-ki-sink a b s t ab =
    trans assoc (back (dKIa (toℕ a) (toℕ b ∸ toℕ a)) (tele (toℕ<n a) (toℕ<n s) (toℕ<n t)))

  d-ki-pp : ∀ a b s x .(ab : a <ᶠ b) → x ≢ a → x ≢ b → s ≢ a → s ≢ b →
            (d ʷ) (pw x s • kiw a b s ab) ≈ (d ʷ) (kiw a b s ab • pw x s)
  d-ki-pp a b s x ab xa xb sa sb =
    hyb-conj a b s a b s ab ab (gen (kf-pp x s)) Eq.refl Eq.refl Eq.refl
      (Eq.trans (z a xa sa) (Eq.sym (z b xb sb)))
    where
    z : ∀ y → x ≢ y → s ≢ y → ph (sp (pw x s)) y ≡ p0
    z y xy sy = Eq.cong₂ (λ u v → phif u p1 +ᵖ phif v p3)
                         (δ-≢ x y (λ e → xy (Eq.sym e))) (δ-≢ s y (λ e → sy (Eq.sym e)))

  private
    zx : ∀ s x y .(xy : x <ᶠ y) t → s ≢ t → ph (sp (xw s x y xy)) t ≡ p0
    zx s x y xy t st = Eq.cong (λ u → phif u p2 +ᵖ p0) (δ-≢ s t (λ e → st (Eq.sym e)))

  d-ki-px : ∀ a b s x y .(ab : a <ᶠ b) .(xy : x <ᶠ y) →
            x ≢ a → x ≢ b → y ≢ a → y ≢ b → s ≢ a → s ≢ b → s ≢ x → s ≢ y →
            (d ʷ) (xw s x y xy • kiw a b s ab) ≈ (d ʷ) (kiw a b s ab • xw s x y xy)
  d-ki-px a b s x y ab xy xa xb ya yb sa sb sx′ sy =
    hyb-conj a b s a b s ab ab (gen (kf-px s x y xy))
      (swapF-o x y a (λ e → xa (Eq.sym e)) (λ e → ya (Eq.sym e)))
      (swapF-o x y b (λ e → xb (Eq.sym e)) (λ e → yb (Eq.sym e)))
      (swapF-o x y s sx′ sy)
      (Eq.trans (zx s x y xy a sa) (Eq.sym (zx s x y xy b sb)))

  d-ki-swap : ∀ j kk ll s .(pq : j <ᶠ kk) .(qr : kk <ᶠ ll) → s ≢ j → s ≢ kk → s ≢ ll →
              (d ʷ) (kiw kk ll s qr • xw s j kk pq)
              ≈ (d ʷ) (xw s j kk pq • kiw j ll s (<ᶠ-trans pq qr))
  d-ki-swap j kk ll s pq qr sj sk sl =
    sym (hyb-conj j ll s kk ll s (<ᶠ-trans pq qr) qr (gen (kf-px s j kk pq))
           (swapF-b j kk)
           (swapF-o j kk ll (≢< (NP.<-trans (rel pq) (rel qr))) (≢< (rel qr)))
           (swapF-o j kk s sj sk)
           (Eq.trans (zx s j kk pq kk sk) (Eq.sym (zx s j kk pq ll sl))))

  d-ki-swap′ : ∀ j kk ll s .(pq : j <ᶠ kk) .(qr : kk <ᶠ ll) → s ≢ j → s ≢ kk → s ≢ ll →
               (d ʷ) (kiw j ll s (<ᶠ-trans pq qr) • xw s kk ll qr)
               ≈ (d ʷ) (xw s kk ll qr • kiw j kk s pq)
  d-ki-swap′ j kk ll s pq qr sj sk sl =
    sym (hyb-conj j kk s j ll s pq (<ᶠ-trans pq qr) (gen (kf-px s kk ll qr))
           (swapF-o kk ll j (λ e → ≢< (rel pq) (Eq.sym e))
                            (λ e → ≢< (NP.<-trans (rel pq) (rel qr)) (Eq.sym e)))
           (swapF-b kk ll)
           (swapF-o kk ll s sk sl)
           (Eq.trans (zx s kk ll qr j sj) (Eq.sym (zx s kk ll qr ll sl))))
