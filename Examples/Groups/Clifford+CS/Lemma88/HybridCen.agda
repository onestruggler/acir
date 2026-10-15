------------------------------------------------------------------------
-- Presentations of groups
--
-- The hybrid letter at the top pair commutes with every decoded K-free
-- word that fixes the pair with equal phases
--
-- On N = 4 + m indices, with the top pair N − 2, N − 1: a K-free word w
-- whose phased permutation fixes both indices of the pair and gives them
-- the same phase decodes to a circuit commuting with k (N − 2)
-- (`cen-top`).  The phase is first moved off the pair by the scalar
-- z = i_[N−2] i_[N−3]⁻¹ · i_[N−1] i_[N−3]⁻¹, which commutes with the
-- hybrid (the hypothesis `sc`, in its decoded spelling); what is left
-- fixes the pair with phase zero, and its normal form (Auxiliary.NF)
-- lies below the pair: the i-th run sends its first index to N − i
-- (`Unique.code-at`), so a permutation fixing N − 1 and N − 2 has its
-- first two runs empty and every later one below N − 2, and the atoms
-- have no entry on the pair since its phases are zero.  HybridTop then
-- gives the commutation.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat using (ℕ ; suc)
open import Word.Base using (Word ; WRel)

module Examples.Groups.Clifford+CS.Lemma88.HybridCen
  {X : Set} (Γ : WRel X) (m : ℕ) (p p′ l h k : ℕ → Word X) where

open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin using (Fin ; toℕ ; zero) renaming (suc to fsuc)
open import Data.Fin.Properties using (toℕ-injective ; toℕ<n)
open import Data.List using ([] ; _∷_)
open import Data.Nat using (zero ; _+_ ; _∸_ ; _<_ ; _≤_ ; z≤n ; s≤s)
open import Data.Nat.Properties as NP using ()
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (ε ; _•_ ; [_]ʷ ; _ʷ ; _^_)

import Presentation.Base as PB

open import Examples.Groups.Clifford+CS.Auxiliary.P using (GenP ; pp ; px ; dx ; ki)
open import Examples.Groups.Clifford+CS.Auxiliary.Fragment using (_F,_===_)
open import Examples.Groups.Clifford+CS.Auxiliary.Atoms (suc (suc (suc m)))
  using (atoms ; aw ; PhList ; Incr ; NZL ; NZ ; nz1 ; nz2 ; nz3 ; cons ; z0 ; pn ; negᵖ)
open import Examples.Groups.Clifford+CS.Auxiliary.NF (suc (suc (suc m)))
  using (NF ; Normal ; Reduced ; existence ; KFreeʷ ; permPart ; permFrom ; runFrom
       ; runAt ; runAt≡ ; shift-Ni ; sx ; sx-letter ; fin ; fin-toℕ ; fin≢ ; j<sj<N)
  renaming (cat to kcat)
open import Examples.Groups.Clifford+CS.Auxiliary.PhasedPerm (suc (suc (suc (suc m))))
  using (Ph ; p0 ; p1 ; p2 ; p3 ; _+ᵖ_ ; +ᵖ-idʳ ; sp ; spg ; ph ; prm ; prm≡ ; ph≡
       ; δ ; δ-≢ ; phif ; swapF ; swapF-o ; sound)
open import Examples.Groups.Clifford+CS.Auxiliary.Template (suc (suc (suc m)))
  using (TW ; tp ; emp ; ⌜_⌝ ; _•ᵗ_ ; module At)
open import Examples.Groups.Clifford+CS.Auxiliary.Unique (suc (suc (suc m)))
  using (code-at ; prm-inj ; atoms-prm ; atoms-ph ; phAt ; phAt-head)
open import Examples.Groups.Clifford+CS.Lemma88.Chains p p′ l h k using (d ; dPP ; pp-dn)
import Examples.Groups.Clifford+CS.Lemma88.Fragment as Fr
import Examples.Groups.Clifford+CS.Lemma88.HybridTop as HTop
open import Examples.Groups.Clifford+CS.Tools using (module Tools)

private
  N′ N : ℕ
  N′ = suc (suc (suc m))
  N  = suc N′

  W : Set
  W = Word (GenP N)

  module FrN = Fr Γ N p p′ l h k

open PB Γ using (_≈_)
open HTop Γ N p p′ l h k
  using (top ; TopFar ; LowG ; LowW)
  renaming (gen to lgen ; nil to lnil ; cat to lcat)

------------------------------------------------------------------------
-- The three indices at the top: N − 3, N − 2, N − 1

private
  qB : suc m < N
  qB = s≤s (s≤s (NP.m≤n+m m 2))

  qT : suc (suc m) < N
  qT = s≤s (s≤s (s≤s (NP.n≤1+n m)))

  qT1 : suc (suc (suc m)) < N
  qT1 = NP.n<1+n (suc (suc (suc m)))

tB tT tT1 : Fin N
tB  = fin (suc m) qB
tT  = fin (suc (suc m)) qT
tT1 = fin (suc (suc (suc m))) qT1

toT : toℕ tT ≡ top
toT = fin-toℕ _ qT

toT1 : toℕ tT1 ≡ suc top
toT1 = fin-toℕ _ qT1

private
  topT : top ≤ toℕ tT
  topT = Eq.subst (top ≤_) (Eq.sym (fin-toℕ _ qT)) NP.≤-refl

  topT1 : top ≤ toℕ tT1
  topT1 = Eq.subst (top ≤_) (Eq.sym (fin-toℕ _ qT1)) (NP.n≤1+n top)

------------------------------------------------------------------------
-- Words below the top pair fix it

private
  nlow : ∀ {a t : Fin N} → toℕ a < top → top ≤ toℕ t → t ≢ a
  nlow {a} la le e = NP.<⇒≱ la (Eq.subst (λ y → top ≤ toℕ y) e le)

  low-fixG : ∀ g → LowG g → ∀ t → top ≤ toℕ t → prm (spg g) t ≡ t × ph (spg g) t ≡ p0
  low-fixG (pp a b) (la , lb) t le =
    Eq.refl ,
    Eq.cong₂ (λ x y → phif x p1 +ᵖ phif y p3) (δ-≢ a t (nlow la le)) (δ-≢ b t (nlow lb le))
  low-fixG (px c a b _) (lc , la , lb) t le =
    swapF-o a b t (nlow la le) (nlow lb le) ,
    Eq.cong (λ x → phif x p2 +ᵖ p0) (δ-≢ c t (nlow lc le))
  low-fixG (dx a b c e _ _) (la , lb , lc , le′) t le =
    Eq.trans (Eq.cong (swapF c e) (swapF-o a b t (nlow la le) (nlow lb le)))
             (swapF-o c e t (nlow lc le) (nlow le′ le)) ,
    Eq.refl
  low-fixG (ki _ _ _ _) ()

low-fix : ∀ {u : W} → LowW u → ∀ t → top ≤ toℕ t → prm (sp u) t ≡ t × ph (sp u) t ≡ p0
low-fix (lgen {g} lg) t le = low-fixG g lg t le
low-fix lnil          t le = Eq.refl , Eq.refl
low-fix (lcat {u} {v} lu lv) t le =
  Eq.trans (Eq.cong (prm (sp v)) (proj₁ fu)) (proj₁ fv) ,
  Eq.cong₂ _+ᵖ_ (proj₂ fu) (Eq.trans (Eq.cong (ph (sp v)) (proj₁ fu)) (proj₂ fv))
  where
  fu = low-fix lu t le
  fv = low-fix lv t le

------------------------------------------------------------------------
-- The letters of a normal form below the top pair

private
  low-sx : ∀ v → suc v < top → LowW (sx v)
  low-sx v lt = Eq.subst LowW (Eq.sym (sx-letter v q)) (lgen (a , a , b))
    where
    q : suc v < N
    q = NP.<-trans lt qT

    a : toℕ (fin v (j<sj<N q)) < top
    a = Eq.subst (_< top) (Eq.sym (fin-toℕ v (j<sj<N q))) (NP.<-trans (NP.n<1+n v) lt)

    b : toℕ (fin (suc v) q) < top
    b = Eq.subst (_< top) (Eq.sym (fin-toℕ (suc v) q)) lt

  low-run : ∀ v L → v + L < top → LowW (runFrom v L)
  low-run v zero    lt = lnil
  low-run v (suc L) lt = lcat (low-sx v sv) (low-run (suc v) L lt′)
    where
    lt′ : suc v + L < top
    lt′ = Eq.subst (_< top) (NP.+-suc v L) lt

    sv : suc v < top
    sv = NP.≤-<-trans (s≤s (NP.m≤m+n v L)) lt′

  low-pow : ∀ {u : W} → LowW u → ∀ n → LowW (u ^ n)
  low-pow lu zero          = lnil
  low-pow lu (suc zero)    = lu
  low-pow lu (suc (suc n)) = lcat lu (low-pow lu (suc n))

  low-aw : ∀ x k → toℕ x < top → LowW (aw x k)
  low-aw x k lt = low-pow (lgen (lt , s≤s z≤n)) (pn k)

  nz≢ : ∀ {k : Ph} → NZ k → k ≢ p0
  nz≢ nz1 ()
  nz≢ nz2 ()
  nz≢ nz3 ()

-- The atoms of a list with no phase on the top pair.
low-atoms : ∀ {lo} (L : PhList) → Incr lo L → NZL L →
            phAt tT L ≡ p0 → phAt tT1 L ≡ p0 → LowW (atoms L)
low-atoms []            _          _           eT eT1 = lnil
low-atoms ((x , c) ∷ L) (cons _ i) (cons zc z) eT eT1 =
  lcat (low-aw x c xl) (low-atoms L i z (drop tT topT eT) (drop tT1 topT1 eT1))
  where
  hit : ∀ y → x ≡ y → phAt y ((x , c) ∷ L) ≡ p0 → ⊥
  hit y Eq.refl e = nz≢ zc (Eq.trans (Eq.sym (phAt-head x c L i)) e)

  go : Tri (toℕ x < top) (toℕ x ≡ top) (top < toℕ x) → toℕ x < top
  go (tri< lt _ _) = lt
  go (tri≈ _ eq _) =
    ⊥-elim (hit tT (toℕ-injective (Eq.trans eq (Eq.sym (fin-toℕ _ qT)))) eT)
  go (tri> _ _ gt) =
    ⊥-elim (hit tT1 (toℕ-injective
                      (Eq.trans (NP.≤-antisym (NP.≤-pred (toℕ<n x)) gt)
                                (Eq.sym (fin-toℕ _ qT1))))
                eT1)

  xl : toℕ x < top
  xl = go (NP.<-cmp (toℕ x) top)

  drop : ∀ t → top ≤ toℕ t → phAt t ((x , c) ∷ L) ≡ p0 → phAt t L ≡ p0
  drop t le e = Eq.trans (Eq.sym (Eq.cong (λ b → phif b c +ᵖ phAt t L)
                                          (δ-≢ x t (nlow xl le))))
                         e

------------------------------------------------------------------------
-- A normal form fixing the top pair with phase zero lies below it

module Low {L : PhList} {c : ℕ → ℕ} (nm : Normal L c)
           (fT  : prm (sp (NF L c)) tT  ≡ tT)
           (fT1 : prm (sp (NF L c)) tT1 ≡ tT1)
           (zT  : ph (sp (NF L c)) tT  ≡ p0)
           (zT1 : ph (sp (NF L c)) tT1 ≡ p0) where

  private
    Lh = Normal.lehmer nm

    P P2 P3 : W
    P  = permPart c
    P2 = permFrom 2 top c
    P3 = permFrom 3 (suc m) c

    prmA : ∀ t → prm (sp (NF L c)) t ≡ prm (sp P) t
    prmA t = Eq.cong (prm (sp P)) (atoms-prm L t)

    -- The first run sends its first index to N − 1, which is fixed.
    q1 : c 1 < N
    q1 = s≤s (Lh 1)

    t1≡ : fin (c 1) q1 ≡ tT1
    t1≡ = prm-inj P (toℕ-injective
            (Eq.trans (code-at 1 top c NP.≤-refl Eq.refl Lh (fin (c 1) q1) (fin-toℕ (c 1) q1))
                      (Eq.sym (Eq.trans (Eq.cong toℕ (Eq.trans (Eq.sym (prmA tT1)) fT1))
                                        (fin-toℕ _ qT1)))))

    c1≡ : c 1 ≡ N′
    c1≡ = Eq.trans (Eq.sym (fin-toℕ (c 1) q1)) (Eq.trans (Eq.cong toℕ t1≡) (fin-toℕ _ qT1))

    P≡ : P ≡ ε • P2
    P≡ = Eq.cong (_• P2) (Eq.trans (Eq.cong (runAt 1) c1≡)
                                   (Eq.cong (runFrom N′) (NP.n∸n≡0 N′)))

    prmP : ∀ t → prm (sp P) t ≡ prm (sp P2) t
    prmP t = Eq.cong (λ w → prm (sp w) t) P≡

    -- The second sends its first index to N − 2, which is fixed.
    q2 : c 2 < N
    q2 = NP.≤-<-trans (Lh 2) qT

    t2≡ : fin (c 2) q2 ≡ tT
    t2≡ = prm-inj P2 (toℕ-injective
            (Eq.trans (code-at 2 (suc m) c (s≤s z≤n) Eq.refl Lh (fin (c 2) q2) (fin-toℕ (c 2) q2))
                      (Eq.sym (Eq.trans (Eq.cong toℕ (Eq.trans (Eq.sym (prmP tT))
                                                       (Eq.trans (Eq.sym (prmA tT)) fT)))
                                        (fin-toℕ _ qT)))))

    c2≡ : c 2 ≡ top
    c2≡ = Eq.trans (Eq.sym (fin-toℕ (c 2) q2)) (Eq.trans (Eq.cong toℕ t2≡) (fin-toℕ _ qT))

    P≡′ : P ≡ ε • (ε • P3)
    P≡′ = Eq.trans P≡ (Eq.cong (ε •_)
            (Eq.cong (_• P3) (Eq.trans (Eq.cong (runAt 2) c2≡)
                                       (Eq.cong (runFrom top) (NP.n∸n≡0 top)))))

    -- Every later run lies below N − 2.
    low-perm : ∀ i j → N ∸ i ≡ j → 3 ≤ i → LowW (permFrom i j c)
    low-perm i zero    Ni _  = lnil
    low-perm i (suc j) Ni 3i =
      lcat (Eq.subst LowW (Eq.sym (runAt≡ i (c i) Ni)) (low-run (c i) (suc j ∸ c i) bnd))
           (low-perm (suc i) j (shift-Ni i j Ni) (NP.m≤n⇒m≤1+n 3i))
      where
      vk : c i ≤ suc j
      vk = Eq.subst (c i ≤_) Ni (Lh i)

      sj<top : suc j < top
      sj<top = s≤s (Eq.subst (_≤ suc m) Ni (NP.∸-monoʳ-≤ N 3i))

      bnd : c i + (suc j ∸ c i) < top
      bnd = Eq.subst (_< top) (Eq.sym (NP.m+[n∸m]≡n vk)) sj<top

    lowP3 : LowW P3
    lowP3 = low-perm 3 (suc m) Eq.refl NP.≤-refl

    lowP : LowW P
    lowP = Eq.subst LowW (Eq.sym P≡′) (lcat lnil (lcat lnil lowP3))

    -- So the phases on the pair are the atoms'.
    phl : ∀ t → t ≢ z0 → top ≤ toℕ t → ph (sp (NF L c)) t ≡ p0 → phAt t L ≡ p0
    phl t nz le e =
      Eq.trans (Eq.sym (atoms-ph L t nz))
        (Eq.trans (Eq.sym (+ᵖ-idʳ _))
          (Eq.trans (Eq.cong (ph (sp (atoms L)) t +ᵖ_)
                      (Eq.sym (Eq.trans (Eq.cong (ph (sp P)) (atoms-prm L t))
                                        (proj₂ (low-fix lowP t le)))))
                    e))

    nzT : tT ≢ z0
    nzT e = NP.0≢1+n (Eq.sym (Eq.trans (Eq.sym (fin-toℕ _ qT)) (Eq.cong toℕ e)))

    nzT1 : tT1 ≢ z0
    nzT1 e = NP.0≢1+n (Eq.sym (Eq.trans (Eq.sym (fin-toℕ _ qT1)) (Eq.cong toℕ e)))

  low-NF : LowW (NF L c)
  low-NF = lcat (low-atoms L (Normal.incr nm) (Normal.nz nm)
                           (phl tT nzT topT zT) (phl tT1 nzT1 topT1 zT1))
                lowP

------------------------------------------------------------------------
-- The scalar on the top pair, as a template on N − 3, N − 2, N − 1

private
  ι : Fin 3 → Fin N
  ι zero               = tB
  ι (fsuc zero)        = tT
  ι (fsuc (fsuc zero)) = tT1

  ne : ∀ {j k′} (q : j < N) (q′ : k′ < N) → j < k′ → fin j q ≢ fin k′ q′
  ne q q′ lt = fin≢ q q′ (NP.<⇒≢ lt)

  ιinj : ∀ {x y : Fin 3} → ι x ≡ ι y → x ≡ y
  ιinj {zero}               {zero}               e = Eq.refl
  ιinj {zero}               {fsuc zero}          e = ⊥-elim (ne qB qT (NP.n<1+n _) e)
  ιinj {zero}               {fsuc (fsuc zero)}   e =
    ⊥-elim (ne qB qT1 (NP.<-trans (NP.n<1+n _) (NP.n<1+n _)) e)
  ιinj {fsuc zero}          {zero}               e = ⊥-elim (ne qB qT (NP.n<1+n _) (Eq.sym e))
  ιinj {fsuc zero}          {fsuc zero}          e = Eq.refl
  ιinj {fsuc zero}          {fsuc (fsuc zero)}   e = ⊥-elim (ne qT qT1 (NP.n<1+n _) e)
  ιinj {fsuc (fsuc zero)}   {zero}               e =
    ⊥-elim (ne qB qT1 (NP.<-trans (NP.n<1+n _) (NP.n<1+n _)) (Eq.sym e))
  ιinj {fsuc (fsuc zero)}   {fsuc zero}          e = ⊥-elim (ne qT qT1 (NP.n<1+n _) (Eq.sym e))
  ιinj {fsuc (fsuc zero)}   {fsuc (fsuc zero)}   e = Eq.refl

  module TA = At ι ιinj

  i0 i1 i2 : Fin 3
  i0 = zero
  i1 = fsuc zero
  i2 = fsuc (fsuc zero)

  -- z = i_[N−2] i_[N−3]⁻¹ · i_[N−1] i_[N−3]⁻¹, and the power of it that
  -- cancels a phase φ on the pair.
  zt : TW 3
  zt = ⌜ tp i1 i0 ⌝ •ᵗ ⌜ tp i2 i0 ⌝

  zp : Ph → TW 3
  zp p0 = emp
  zp p1 = zt •ᵗ (zt •ᵗ zt)
  zp p2 = zt •ᵗ zt
  zp p3 = zt

  zph1 : ∀ φ → ph (sp (TA.inst (zp φ))) tT ≡ negᵖ φ
  zph1 p0 = TA.W-ph (zp p0) i1
  zph1 p1 = TA.W-ph (zp p1) i1
  zph1 p2 = TA.W-ph (zp p2) i1
  zph1 p3 = TA.W-ph (zp p3) i1

  zph2 : ∀ φ → ph (sp (TA.inst (zp φ))) tT1 ≡ negᵖ φ
  zph2 p0 = TA.W-ph (zp p0) i2
  zph2 p1 = TA.W-ph (zp p1) i2
  zph2 p2 = TA.W-ph (zp p2) i2
  zph2 p3 = TA.W-ph (zp p3) i2

  zprm1 : ∀ φ → prm (sp (TA.inst (zp φ))) tT ≡ tT
  zprm1 p0 = TA.W-prm (zp p0) i1
  zprm1 p1 = TA.W-prm (zp p1) i1
  zprm1 p2 = TA.W-prm (zp p2) i1
  zprm1 p3 = TA.W-prm (zp p3) i1

  zprm2 : ∀ φ → prm (sp (TA.inst (zp φ))) tT1 ≡ tT1
  zprm2 p0 = TA.W-prm (zp p0) i2
  zprm2 p1 = TA.W-prm (zp p1) i2
  zprm2 p2 = TA.W-prm (zp p2) i2
  zprm2 p3 = TA.W-prm (zp p3) i2

  zinv : ∀ φ → PB._≈_ (N F,_===_) (TA.inst (zp (negᵖ φ)) • TA.inst (zp φ)) ε
  zinv p0 = TA.A5-tmpl (zp (negᵖ p0) •ᵗ zp p0) emp Eq.refl
  zinv p1 = TA.A5-tmpl (zp (negᵖ p1) •ᵗ zp p1) emp Eq.refl
  zinv p2 = TA.A5-tmpl (zp (negᵖ p2) •ᵗ zp p2) emp Eq.refl
  zinv p3 = TA.A5-tmpl (zp (negᵖ p3) •ᵗ zp p3) emp Eq.refl

  neg+ : ∀ φ → negᵖ φ +ᵖ φ ≡ p0
  neg+ p0 = Eq.refl
  neg+ p1 = Eq.refl
  neg+ p2 = Eq.refl
  neg+ p3 = Eq.refl

  ss∸ : ∀ a → suc (suc a) ∸ a ≡ 2
  ss∸ zero    = Eq.refl
  ss∸ (suc a) = ss∸ a

------------------------------------------------------------------------
-- The commutation

module Proofs (F : FrN.Facts) (T : TopFar)
  (sc : (p′ (suc m) • p′ (suc m) • p′ (suc (suc m))) • k top
        ≈ k top • (p′ (suc m) • p′ (suc m) • p′ (suc (suc m)))) where

  open FrN.Facts F
  open FrN.Proofs F
  open Tools Γ hiding (_≈_)
  open HTop.Proofs Γ N p p′ l h k F T using (comm-word)

  private
    kt : Word X
    kt = k top

  -- The decoding respects the K-free congruence.
  d-≈ : ∀ {u t : W} → PB._≈_ (N F,_===_) u t → (d ʷ) u ≈ (d ʷ) t
  d-≈ PB.refl         = refl
  d-≈ (PB.sym e)      = sym (d-≈ e)
  d-≈ (PB.trans e e′) = trans (d-≈ e) (d-≈ e′)
  d-≈ (PB.cong e e′)  = cong (d-≈ e) (d-≈ e′)
  d-≈ PB.assoc        = assoc
  d-≈ PB.left-unit    = left-unit
  d-≈ PB.right-unit   = right-unit
  d-≈ (PB.axiom a)    = fragment a

  -- The scalar commutes with the hybrid.
  private
    dz≡ : (d ʷ) (TA.inst zt) ≡ (p′ (suc m) • ε) • (p′ (suc m) • (p′ (suc (suc m)) • ε))
    dz≡ = Eq.cong₂ _•_
      (Eq.trans (Eq.cong₂ dPP (fin-toℕ _ qT) (fin-toℕ _ qB))
                (Eq.trans (dPP-dn (NP.n≤1+n (suc m))) (Eq.cong (pp-dn (suc m)) (sA∸A (suc m)))))
      (Eq.trans (Eq.cong₂ dPP (fin-toℕ _ qT1) (fin-toℕ _ qB))
                (Eq.trans (dPP-dn (NP.m≤n+m (suc m) 2)) (Eq.cong (pp-dn (suc m)) (ss∸ (suc m)))))

    czt : Comm ((d ʷ) (TA.inst zt)) kt
    czt = Eq.subst (λ w → Comm w kt) (Eq.sym dz≡)
            (comm-respˡ sc (sym (cong right-unit (cong refl right-unit))))

  cz : ∀ φ → Comm ((d ʷ) (TA.inst (zp φ))) kt
  cz p0 = comm-ε
  cz p1 = comm-• czt (comm-• czt czt)
  cz p2 = comm-• czt czt
  cz p3 = czt

  -- With phase zero on the pair: the normal form lies below it.
  cen0 : ∀ {u : W} → KFreeʷ u →
         prm (sp u) tT ≡ tT → prm (sp u) tT1 ≡ tT1 →
         ph (sp u) tT ≡ p0 → ph (sp u) tT1 ≡ p0 → Comm ((d ʷ) u) kt
  cen0 {u} ku fT fT1 zT zT1 =
    comm-respˡ (comm-word (Low.low-NF (Reduced.norm r) (pm fT) (pm fT1) (pz zT) (pz zT1)))
               (sym (d-≈ (Reduced.law r)))
    where
    r = existence ku
    e = sound (Reduced.law r)

    pm : ∀ {t} → prm (sp u) t ≡ t → prm (sp (NF (Reduced.lis r) (Reduced.code r))) t ≡ t
    pm {t} f = Eq.trans (Eq.sym (prm≡ e t)) f

    pz : ∀ {t} → ph (sp u) t ≡ p0 → ph (sp (NF (Reduced.lis r) (Reduced.code r))) t ≡ p0
    pz {t} z = Eq.trans (Eq.sym (ph≡ e t)) z

  -- In general.
  cen-top : ∀ {w : W} → KFreeʷ w →
            prm (sp w) tT ≡ tT → prm (sp w) tT1 ≡ tT1 →
            ph (sp w) tT ≡ ph (sp w) tT1 → Comm ((d ʷ) w) kt
  cen-top {w} kw fT fT1 eph =
    comm-respˡ (comm-• (cz (negᵖ φ)) (cen0 kw′ fT′ fT1′ zT zT1)) (sym (d-≈ wF))
    where
    φ = ph (sp w) tT
    z = TA.inst (zp φ)

    kw′ : KFreeʷ (z • w)
    kw′ = kcat (TA.kf-inst (zp φ)) kw

    fT′ : prm (sp (z • w)) tT ≡ tT
    fT′ = Eq.trans (Eq.cong (prm (sp w)) (zprm1 φ)) fT

    fT1′ : prm (sp (z • w)) tT1 ≡ tT1
    fT1′ = Eq.trans (Eq.cong (prm (sp w)) (zprm2 φ)) fT1

    zT : ph (sp (z • w)) tT ≡ p0
    zT = Eq.trans (Eq.cong₂ _+ᵖ_ (zph1 φ) (Eq.cong (ph (sp w)) (zprm1 φ))) (neg+ φ)

    zT1 : ph (sp (z • w)) tT1 ≡ p0
    zT1 = Eq.trans (Eq.cong₂ _+ᵖ_ (zph2 φ)
                     (Eq.trans (Eq.cong (ph (sp w)) (zprm2 φ)) (Eq.sym eph)))
                   (neg+ φ)

    wF : PB._≈_ (N F,_===_) w (TA.inst (zp (negᵖ φ)) • (z • w))
    wF = PB.trans (PB.sym PB.left-unit)
           (PB.trans (PB.cong (PB.sym (zinv φ)) PB.refl) PB.assoc)
