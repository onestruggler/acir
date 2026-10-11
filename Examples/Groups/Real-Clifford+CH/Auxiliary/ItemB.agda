------------------------------------------------------------------------
-- Presentations of groups
--
-- Item (b) of the Reidemeister–Schreier method
--
-- The second condition of `Theorem410`: for every rule `u === t` of
-- Figure 7 and every coset c, running both sides through the coset
-- action gives equivalent words of P and the same coset.
--
-- By `Frame.by-frame` that is, for each rule, its image under the
-- frame embedding Φ, at any three indices e, f, g away from 0, 1 and
-- the rule — with no case analysis on the indices and none on the
-- coset.  `frame-for` finds the three indices (`Avoid.avoid3`), and
-- the images are one line each: a sign pair squared, two sign pairs
-- commuting, a pair squared (`hh-invol`), a sign pair passing a pair
-- (`comm-zz`), two pairs commuting ((71) and (66)), and the four
-- rules with a Hadamard and an exchange or a sign, which the frame
-- normaliser decides (`by-norm`).
--
-- Figure 7's starred rules are stated at literal indices at widths of
-- the form `suc`, and 2 ^ (3 + m) never reduces to one, so `Item-b`
-- cannot split on a rule directly: `item-b-gen` takes the rule at any
-- width K with K ≡ N and transports its words along that equation
-- (`trW`), the literal indices becoming `subst Fin e k`, which the
-- frame images do not need to be anything in particular.
--
-- (d3*) and (d4*) are proved on their own, in `ItemBd3` and `ItemBd4`:
-- their images under Φ are Hadamard identities of eight and twelve
-- letters, Figure 8's (45) and Figure 11's (80) (from (46), `Eq80`),
-- and (d4*)'s six indices leave no room for a full frame on three
-- qubits.  They are the hypotheses of `Assemble`, which
-- `Theorem410Proof.item-b` discharges.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.ItemB (m : ℕ) where

open import Data.Bool using (_xor_)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-injective ; toℕ-inject≤ ; toℕ-fromℕ<)
open import Data.List using ([] ; _∷_)
open import Data.Nat using (_≤_ ; s≤s ; z≤n) renaming (_^_ to _^ℕ_)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([] ; _∷_)
open import Data.Vec.Relation.Unary.All using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Word.Base using (Word ; ε ; _•_ ; [_]ʷ ; _ᵗ)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.Cosets
  using (Coset ; ⟨ε⟩ ; ⟨M⟩ ; ⟨K⟩ ; ⟨KM⟩)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.RS m using (act ; z₀ ; o₁ ; z₀≢o₁)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Theorem410 m using (Item-b)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Avoid using (Three ; avoid3 ; here ; there)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.NF m using (gen ; cat ; nil ; hf-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.SignedPerm m
  using (δ ; eqv ; xor-self ; xor-comm)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Unique m using (A5-full)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m
  using (Distinct ; []ᵈ ; _∷ᵈ_ ; tz ; ty ; ⌜_⌝ ; _•ᵗ_ ; emp)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m
  using (Eq65 ; eq66 ; comm-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m using (fuse ; hh-invol)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Frame m using (module Frame ; cos)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

import Examples.Groups.Real-Clifford+CH.Auxiliary.Syntactics as G
open G using (_G,_===_ ; −1[_] ; X[_,_] ; H[_,_]
            ; a1* ; a2 ; a3 ; b1* ; b4* ; b6* ; c1 ; c5 ; d2 ; d3* ; d4* ; e2*)

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  ≢sym : ∀ {x y : Fin N} → x ≢ y → y ≢ x
  ≢sym ne e = ne (Eq.sym e)

  hhʷ : Fin N → Fin N → Fin N → Fin N → W
  hhʷ = hh {₃₊ m}

-- An obligation of item (b).
Obl : Coset → Word (G.Gen N) → Word (G.Gen N) → Set
Obl c u t = (proj₁ ((act ᵗ) c u) ≈ proj₁ ((act ᵗ) c t)) ×
            (proj₂ ((act ᵗ) c u) ≡ proj₂ ((act ᵗ) c t))

------------------------------------------------------------------------
-- Choosing the frame

-- Three indices away from 0, 1 and three given ones.
record FrameFor (a b c : Fin N) : Set where
  field
    e f g : Fin N
    ef : e ≢ f
    eg : e ≢ g
    fg : f ≢ g
    ez : e ≢ z₀
    eo : e ≢ o₁
    fz : f ≢ z₀
    fo : f ≢ o₁
    gz : g ≢ z₀
    go : g ≢ o₁
    ae : a ≢ e
    af : a ≢ f
    ag : a ≢ g
    be : b ≢ e
    bf : b ≢ f
    bg : b ≢ g
    ce : c ≢ e
    cf : c ≢ f
    cg : c ≢ g

frame-for : ∀ (a b c : Fin N) → FrameFor a b c
frame-for a b c = record
  { e = e′ ; f = f′ ; g = g′
  ; ef = apart te tf p≢q ; eg = apart te tg p≢r ; fg = apart tf tg q≢r
  ; ez = away te (p∉ here) ; eo = away te (p∉ (there here))
  ; fz = away tf (q∉ here) ; fo = away tf (q∉ (there here))
  ; gz = away tg (r∉ here) ; go = away tg (r∉ (there here))
  ; ae = ≢sym (away te (p∉ (there (there here))))
  ; af = ≢sym (away tf (q∉ (there (there here))))
  ; ag = ≢sym (away tg (r∉ (there (there here))))
  ; be = ≢sym (away te (p∉ (there (there (there here)))))
  ; bf = ≢sym (away tf (q∉ (there (there (there here)))))
  ; bg = ≢sym (away tg (r∉ (there (there (there here)))))
  ; ce = ≢sym (away te (p∉ (there (there (there (there here))))))
  ; cf = ≢sym (away tf (q∉ (there (there (there (there here))))))
  ; cg = ≢sym (away tg (r∉ (there (there (there (there here))))))
  }
  where
  T3 : Three (toℕ z₀ ∷ toℕ o₁ ∷ toℕ a ∷ toℕ b ∷ toℕ c ∷ [])
  T3 = avoid3 _ (s≤s (s≤s (s≤s (s≤s (s≤s z≤n)))))

  open Three T3

  e′ f′ g′ : Fin N
  e′ = fin8 {m} (fromℕ< p<)
  f′ = fin8 {m} (fromℕ< q<)
  g′ = fin8 {m} (fromℕ< r<)

  te : toℕ e′ ≡ p
  te = Eq.trans (toℕ-inject≤ _ _) (toℕ-fromℕ< p<)

  tf : toℕ f′ ≡ q
  tf = Eq.trans (toℕ-inject≤ _ _) (toℕ-fromℕ< q<)

  tg : toℕ g′ ≡ r
  tg = Eq.trans (toℕ-inject≤ _ _) (toℕ-fromℕ< r<)

  away : ∀ {x : Fin N} {k : ℕ} → toℕ x ≡ k → ∀ {y : Fin N} → k ≢ toℕ y → x ≢ y
  away tx ne h = ne (Eq.trans (Eq.sym tx) (Eq.cong toℕ h))

  apart : ∀ {x y : Fin N} {k l : ℕ} → toℕ x ≡ k → toℕ y ≡ l → k ≢ l → x ≢ y
  apart t₁ t₂ ne h = ne (Eq.trans (Eq.sym t₁) (Eq.trans (Eq.cong toℕ h) t₂))

------------------------------------------------------------------------
-- Words at another width

trG : ∀ {K : ℕ} → K ≡ N → G.Gen K → G.Gen N
trG e −1[ i ]    = −1[ Eq.subst Fin e i ]
trG e X[ i , j ] = X[ Eq.subst Fin e i , Eq.subst Fin e j ]
trG e H[ i , j ] = H[ Eq.subst Fin e i , Eq.subst Fin e j ]

trW : ∀ {K : ℕ} → K ≡ N → Word (G.Gen K) → Word (G.Gen N)
trW e [ y ]ʷ   = [ trG e y ]ʷ
trW e ε        = ε
trW e (u • v)  = trW e u • trW e v

private
  trW-refl : ∀ (u : Word (G.Gen N)) → trW Eq.refl u ≡ u
  trW-refl [ −1[ i ] ]ʷ    = Eq.refl
  trW-refl [ X[ i , j ] ]ʷ = Eq.refl
  trW-refl [ H[ i , j ] ]ʷ = Eq.refl
  trW-refl ε               = Eq.refl
  trW-refl (u • v)         = Eq.cong₂ _•_ (trW-refl u) (trW-refl v)

  toℕ-subst : ∀ {K : ℕ} (e : K ≡ N) (i : Fin K) → toℕ (Eq.subst Fin e i) ≡ toℕ i
  toℕ-subst Eq.refl i = Eq.refl

  -- Two literal indices carried to N stay apart.
  lit≢ : ∀ {K : ℕ} (e : K ≡ N) (i j : Fin K) → toℕ i ≢ toℕ j →
         Eq.subst Fin e i ≢ Eq.subst Fin e j
  lit≢ e i j ne h =
    ne (Eq.trans (Eq.sym (toℕ-subst e i)) (Eq.trans (Eq.cong toℕ h) (toℕ-subst e j)))

  -- The literals 0 and 1 carried to N are the action's distinguished
  -- indices.
  lit-z : ∀ {K : ℕ} (e : K ≡ N) (i : Fin K) → toℕ i ≡ 0 → Eq.subst Fin e i ≡ z₀
  lit-z e i h = toℕ-injective (Eq.trans (toℕ-subst e i)
                  (Eq.trans h (Eq.sym (toℕ-inject≤ ₀ _))))

  lit-o : ∀ {K : ℕ} (e : K ≡ N) (i : Fin K) → toℕ i ≡ 1 → Eq.subst Fin e i ≡ o₁
  lit-o e i h = toℕ-injective (Eq.trans (toℕ-subst e i)
                  (Eq.trans h (Eq.sym (toℕ-inject≤ ₁ _))))

------------------------------------------------------------------------
-- The rules

module _ (e65 : Eq65) where

  -- A rule whose indices are among a, b, c, through the frame chosen
  -- for them.
  module With (a b c : Fin N) where
    open FrameFor (frame-for a b c) public
    open Frame e65 z₀ o₁ z₀≢o₁ e f g ef eg fg ez eo fz fo gz go public

    av-a : Av a
    av-a = ae , af , ag

    av-b : Av b
    av-b = be , bf , bg

    av-c : Av c
    av-c = ce , cf , cg

  rule-a1 : ∀ (c : Coset) (i : Fin N) → Obl c (G.−1 i • G.−1 i) ε
  rule-a1 c i =
    W.by-frame c (G.−1 i • G.−1 i) ε (W.av-a , W.av-a) tt (tt , tt) tt (cs c)
      (A5-full (cat (gen (hf-zz i W.g)) (gen (hf-zz i W.g))) nil
               (eqv (λ j → xor-self (δ i j xor δ W.g j)) (λ _ → Eq.refl)))
    where
    module W = With i i i

    cs : ∀ (c : Coset) → cos c (G.−1 i • G.−1 i) ≡ cos c ε
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-a2 : ∀ (c : Coset) (a b : Fin N) → a ≢ b → Obl c (G.X a b • G.X a b) ε
  rule-a2 c a b ab =
    W.by-frame c (G.X a b • G.X a b) ε ((W.av-a , W.av-b) , (W.av-a , W.av-b)) tt
      (ab , ab) tt (cs c)
      (A5-tmpl (⌜ ty ₂ ₀ ₁ ⌝ •ᵗ ⌜ ty ₂ ₀ ₁ ⌝) emp Eq.refl)
    where
    module W = With a b b
    open W.NV (a ∷ b ∷ W.g ∷ [])
              ((≢sym ab ∷ ≢sym W.ag ∷ []) ∷ᵈ (≢sym W.bg ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
              (W.ae ∷ W.be ∷ ≢sym W.eg ∷ []) (W.af ∷ W.bf ∷ ≢sym W.fg ∷ [])

    cs : ∀ (c : Coset) → cos c (G.X a b • G.X a b) ≡ cos c ε
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-a3 : ∀ (c : Coset) (a b : Fin N) → a ≢ b → Obl c (G.H a b • G.H a b) ε
  rule-a3 c a b ab =
    W.by-frame c (G.H a b • G.H a b) ε ((W.av-a , W.av-b) , (W.av-a , W.av-b)) tt
      (ab , ab) tt (cs c)
      (hh-invol e65 a b W.e W.f ab W.ae W.af W.be W.bf W.ef)
    where
    module W = With a b b

    cs : ∀ (c : Coset) → cos c (G.H a b • G.H a b) ≡ cos c ε
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-b1 : ∀ (c : Coset) (i j : Fin N) → Obl c (G.−1 i • G.−1 j) (G.−1 j • G.−1 i)
  rule-b1 c i j =
    W.by-frame c (G.−1 i • G.−1 j) (G.−1 j • G.−1 i) (W.av-a , W.av-b) (W.av-b , W.av-a)
      (tt , tt) (tt , tt) (cs c)
      (A5-full (cat (gen (hf-zz i W.g)) (gen (hf-zz j W.g)))
               (cat (gen (hf-zz j W.g)) (gen (hf-zz i W.g)))
               (eqv (λ k → xor-comm (δ i k xor δ W.g k) (δ j k xor δ W.g k)) (λ _ → Eq.refl)))
    where
    module W = With i j j

    cs : ∀ (c : Coset) → cos c (G.−1 i • G.−1 j) ≡ cos c (G.−1 j • G.−1 i)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  -- (b4*): the sign on j passes the Hadamard on i and k.
  rule-b4 : ∀ (c : Coset) (i j k : Fin N) → i ≢ j → i ≢ k → j ≢ k →
            Obl c (G.−1 j • G.H i k) (G.H i k • G.−1 j)
  rule-b4 c i j k ij ik jk =
    W.by-frame c (G.−1 j • G.H i k) (G.H i k • G.−1 j)
      (W.av-b , (W.av-a , W.av-c)) ((W.av-a , W.av-c) , W.av-b)
      (tt , ik) (ik , tt) (cs c)
      (comm-zz e65 i k W.e W.f ik W.ae W.af W.ce W.cf W.ef j W.g
               (≢sym ij) jk W.be W.bf (≢sym W.ag) (≢sym W.cg) (≢sym W.eg) (≢sym W.fg))
    where
    module W = With i j k

    cs : ∀ (c : Coset) → cos c (G.−1 j • G.H i k) ≡ cos c (G.H i k • G.−1 j)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  -- (b6*): two Hadamards on disjoint pairs commute.  The frame is chosen
  -- for the second pair, the first being 0 1.
  rule-b6 : ∀ (c : Coset) (i j : Fin N) → i ≢ j → i ≢ z₀ → i ≢ o₁ → j ≢ z₀ → j ≢ o₁ →
            Obl c (G.H z₀ o₁ • G.H i j) (G.H i j • G.H z₀ o₁)
  rule-b6 c i j ij iz io jz jo =
    W.by-frame c (G.H z₀ o₁ • G.H i j) (G.H i j • G.H z₀ o₁)
      ((zv , ov) , (W.av-a , W.av-b)) ((W.av-a , W.av-b) , (zv , ov))
      (z₀≢o₁ , ij) (ij , z₀≢o₁) (cs c) img
    where
    module W = With i j j

    zv : W.Av z₀
    zv = ≢sym W.ez , ≢sym W.fz , ≢sym W.gz

    ov : W.Av o₁
    ov = ≢sym W.eo , ≢sym W.fo , ≢sym W.go

    e f : Fin N
    e = W.e
    f = W.f

    swap-f : ∀ (x y : Fin N) → x ≢ y → W.Av x → W.Av y → hhʷ x y e f ≈ hhʷ e f x y
    swap-f x y xy xv yv =
      eq66 e65 x y e f xy (proj₁ xv) (proj₁ (proj₂ xv)) (proj₁ yv) (proj₁ (proj₂ yv)) W.ef

    both : ∀ (x y x′ y′ : Fin N) → x ≢ y → x′ ≢ y′ → W.Av x′ → W.Av y′ →
           hhʷ x y e f • hhʷ x′ y′ e f ≈ hhʷ x y x′ y′
    both x y x′ y′ xy x′y′ xv′ yv′ =
      trans (back (hhʷ x y e f) (swap-f x′ y′ x′y′ xv′ yv′))
            (fuse e65 x y e f x′ y′ xy W.ef x′y′)

    img : hhʷ z₀ o₁ e f • hhʷ i j e f ≈ hhʷ i j e f • hhʷ z₀ o₁ e f
    img = begin
      hhʷ z₀ o₁ e f • hhʷ i j e f   ≈⟨ both z₀ o₁ i j z₀≢o₁ ij W.av-a W.av-b ⟩
      hhʷ z₀ o₁ i j                 ≈⟨ eq66 e65 z₀ o₁ i j z₀≢o₁ (≢sym iz) (≢sym jz)
                                             (≢sym io) (≢sym jo) ij ⟩
      hhʷ i j z₀ o₁                 ≈⟨ sym (both i j z₀ o₁ ij z₀≢o₁ zv ov) ⟩
      hhʷ i j e f • hhʷ z₀ o₁ e f   ∎

    cs : ∀ (c : Coset) → cos c (G.H z₀ o₁ • G.H i j) ≡ cos c (G.H i j • G.H z₀ o₁)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-c1 : ∀ (c : Coset) (a b : Fin N) → a ≢ b →
            Obl c (G.−1 a • G.X a b) (G.X a b • G.−1 b)
  rule-c1 c a b ab =
    W.by-frame c (G.−1 a • G.X a b) (G.X a b • G.−1 b)
      (W.av-a , (W.av-a , W.av-b)) ((W.av-a , W.av-b) , W.av-b) (tt , ab) (ab , tt) (cs c)
      (A5-tmpl (⌜ tz ₀ ₂ ⌝ •ᵗ ⌜ ty ₂ ₀ ₁ ⌝) (⌜ ty ₂ ₀ ₁ ⌝ •ᵗ ⌜ tz ₁ ₂ ⌝) Eq.refl)
    where
    module W = With a b b
    open W.NV (a ∷ b ∷ W.g ∷ [])
              ((≢sym ab ∷ ≢sym W.ag ∷ []) ∷ᵈ (≢sym W.bg ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
              (W.ae ∷ W.be ∷ ≢sym W.eg ∷ []) (W.af ∷ W.bf ∷ ≢sym W.fg ∷ [])

    cs : ∀ (c : Coset) → cos c (G.−1 a • G.X a b) ≡ cos c (G.X a b • G.−1 b)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-c5 : ∀ (c : Coset) (a b d : Fin N) → a ≢ b → a ≢ d → b ≢ d →
            Obl c (G.H a d • G.X b d) (G.X b d • G.H a b)
  rule-c5 c a b d ab ad bd =
    W.by-frame c (G.H a d • G.X b d) (G.X b d • G.H a b)
      ((W.av-a , W.av-c) , (W.av-b , W.av-c)) ((W.av-b , W.av-c) , (W.av-a , W.av-b))
      (ad , bd) (bd , ab) (cs c)
      (by-norm (⌞ hl ₀ ₂ ⌟ •ᶠ ⌞ hf (ty ₃ ₁ ₂) ⌟) (⌞ hf (ty ₃ ₁ ₂) ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟)
               Eq.refl Eq.refl)
    where
    module W = With a b d
    open W.NV (a ∷ b ∷ d ∷ W.g ∷ [])
              ((≢sym ab ∷ ≢sym ad ∷ ≢sym W.ag ∷ []) ∷ᵈ (≢sym bd ∷ ≢sym W.bg ∷ []) ∷ᵈ
               (≢sym W.cg ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
              (W.ae ∷ W.be ∷ W.ce ∷ ≢sym W.eg ∷ []) (W.af ∷ W.bf ∷ W.cf ∷ ≢sym W.fg ∷ [])

    cs : ∀ (c : Coset) → cos c (G.H a d • G.X b d) ≡ cos c (G.X b d • G.H a b)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-d2 : ∀ (c : Coset) (a b : Fin N) → a ≢ b →
            Obl c (G.−1 b • G.H a b) (G.H a b • G.X a b)
  rule-d2 c a b ab =
    W.by-frame c (G.−1 b • G.H a b) (G.H a b • G.X a b)
      (W.av-b , (W.av-a , W.av-b)) ((W.av-a , W.av-b) , (W.av-a , W.av-b)) (tt , ab) (ab , ab)
      (cs c)
      (by-norm (⌞ hf (tz ₁ ₂) ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟) (⌞ hl ₀ ₁ ⌟ •ᶠ ⌞ hf (ty ₂ ₀ ₁) ⌟)
               Eq.refl Eq.refl)
    where
    module W = With a b b
    open W.NV (a ∷ b ∷ W.g ∷ [])
              ((≢sym ab ∷ ≢sym W.ag ∷ []) ∷ᵈ (≢sym W.bg ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
              (W.ae ∷ W.be ∷ ≢sym W.eg ∷ []) (W.af ∷ W.bf ∷ ≢sym W.fg ∷ [])

    cs : ∀ (c : Coset) → cos c (G.−1 b • G.H a b) ≡ cos c (G.H a b • G.X a b)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  rule-e2 : ∀ (c : Coset) (b d : Fin N) → b ≢ d →
            Obl c (G.H d b • G.X b d) (G.X b d • G.H b d)
  rule-e2 c b d bd =
    W.by-frame c (G.H d b • G.X b d) (G.X b d • G.H b d)
      ((W.av-b , W.av-a) , (W.av-a , W.av-b)) ((W.av-a , W.av-b) , (W.av-a , W.av-b))
      ((λ h → bd (Eq.sym h)) , bd) (bd , bd) (cs c)
      (by-norm (⌞ hl ₁ ₀ ⌟ •ᶠ ⌞ hf (ty ₂ ₀ ₁) ⌟) (⌞ hf (ty ₂ ₀ ₁) ⌟ •ᶠ ⌞ hl ₀ ₁ ⌟)
               Eq.refl Eq.refl)
    where
    module W = With b d d
    open W.NV (b ∷ d ∷ W.g ∷ [])
              ((≢sym bd ∷ ≢sym W.ag ∷ []) ∷ᵈ (≢sym W.bg ∷ []) ∷ᵈ [] ∷ᵈ []ᵈ)
              (W.ae ∷ W.be ∷ ≢sym W.eg ∷ []) (W.af ∷ W.bf ∷ ≢sym W.fg ∷ [])

    cs : ∀ (c : Coset) → cos c (G.H d b • G.X b d) ≡ cos c (G.X b d • G.H b d)
    cs ⟨ε⟩  = Eq.refl
    cs ⟨M⟩  = Eq.refl
    cs ⟨K⟩  = Eq.refl
    cs ⟨KM⟩ = Eq.refl

  ----------------------------------------------------------------------
  -- Assembly, with (d3*) and (d4*) as hypotheses

  D3 : Set
  D3 = ∀ {m′ : ℕ} (e : ₄₊ m′ ≡ N) (c : Coset) →
       Obl c (trW e (G.H ₀ ₁ • G.H ₀ ₂ • G.H ₁ ₃ • G.H ₀ ₁ • G.−1 ₀ • G.−1 ₁ • G.H ₀ ₂ • G.H ₁ ₃))
             (trW e (G.H ₀ ₂ • G.H ₁ ₃ • G.H ₀ ₁ • G.−1 ₀ • G.−1 ₁ • G.H ₀ ₂ • G.H ₁ ₃ • G.H ₀ ₁))

  D4 : Set
  D4 = ∀ {m′ : ℕ} (e : ₂₊ (₄₊ m′) ≡ N) (c : Coset) →
       Obl c (trW e (G.H ₀ ₁ • G.H ₀ ₂ • G.H ₁ ₃ • G.H ₀ ₄ • G.H ₁ ₅ • G.H ₀ ₁ • G.−1 ₀ • G.−1 ₁ •
                     G.H ₀ ₄ • G.H ₁ ₅ • G.H ₀ ₂ • G.H ₁ ₃))
             (trW e (G.H ₀ ₂ • G.H ₁ ₃ • G.H ₀ ₄ • G.H ₁ ₅ • G.H ₀ ₁ • G.−1 ₀ • G.−1 ₁ •
                     G.H ₀ ₄ • G.H ₁ ₅ • G.H ₀ ₂ • G.H ₁ ₃ • G.H ₀ ₁))

  module Assemble (d3 : D3) (d4 : D4) where

    item-b-gen : ∀ {K : ℕ} (e : K ≡ N) (c : Coset) {u t : Word (G.Gen K)} →
                 K G, u === t → Obl c (trW e u) (trW e t)
    item-b-gen e       c a1*                   = rule-a1 c (Eq.subst Fin e ₀)
    item-b-gen Eq.refl c (a2 {a = a} {b = b} ab)       = rule-a2 c a b ab
    item-b-gen Eq.refl c (a3 {a = a} {b = b} ab)       = rule-a3 c a b ab
    item-b-gen e       c b1*                   = rule-b1 c (Eq.subst Fin e ₀) (Eq.subst Fin e ₁)
    item-b-gen e       c b4*                   =
      rule-b4 c (Eq.subst Fin e ₀) (Eq.subst Fin e ₁) (Eq.subst Fin e ₂)
              (lit≢ e ₀ ₁ (λ ())) (lit≢ e ₀ ₂ (λ ())) (lit≢ e ₁ ₂ (λ ()))
    item-b-gen e       c b6*                   =
      Eq.subst₂ (λ x y → Obl c (G.H x y • G.H i j) (G.H i j • G.H x y))
                (Eq.sym (lit-z e ₀ Eq.refl)) (Eq.sym (lit-o e ₁ Eq.refl))
                (rule-b6 c i j (lit≢ e ₂ ₃ (λ ()))
                         (λ h → lit≢ e ₂ ₀ (λ ()) (Eq.trans h (Eq.sym (lit-z e ₀ Eq.refl))))
                         (λ h → lit≢ e ₂ ₁ (λ ()) (Eq.trans h (Eq.sym (lit-o e ₁ Eq.refl))))
                         (λ h → lit≢ e ₃ ₀ (λ ()) (Eq.trans h (Eq.sym (lit-z e ₀ Eq.refl))))
                         (λ h → lit≢ e ₃ ₁ (λ ()) (Eq.trans h (Eq.sym (lit-o e ₁ Eq.refl)))))
      where
      i j : Fin N
      i = Eq.subst Fin e ₂
      j = Eq.subst Fin e ₃
    item-b-gen Eq.refl c (c1 {a = a} {b = b} ab)       = rule-c1 c a b ab
    item-b-gen Eq.refl c (c5 {a = a} {b = b} {c = d} ab ad bd) = rule-c5 c a b d ab ad bd
    item-b-gen Eq.refl c (d2 {a = a} {b = b} ab)       = rule-d2 c a b ab
    item-b-gen e       c d3*                   = d3 e c
    item-b-gen e       c d4*                   = d4 e c
    item-b-gen Eq.refl c (e2* {b = b} {c = d} bd)      = rule-e2 c b d bd

    item-b : Item-b
    item-b c {u} {t} r =
      Eq.subst₂ (λ u′ t′ → Obl c u′ t′) (trW-refl u) (trW-refl t) (item-b-gen Eq.refl c r)
