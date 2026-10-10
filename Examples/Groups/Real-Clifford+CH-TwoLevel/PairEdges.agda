------------------------------------------------------------------------
-- Presentations of groups
--
-- The edges at a level L = (p + 1, k, ℓ) with k > 0 that do not go up
-- (Lemma A.8 there), given the edges below L, and given the case the
-- paper's proof does not cover (Hard).
--
-- For a state s at L, with canonical pair P = (i₁, i₂):
--
-- * Z_[c]: the same syllable; Z_[c] H_P = H_P Z_[c] if c ∉ P, and (d1),
--   (d2) give X_P H_P = H_P Z_[i₂] and Z_[i₁] Z_[i₂] X_P H_P = H_P Z_[i₁];
-- * X_[c,d]: X_[c,d] H_P = Hs(τP) X_[c,d], τ = (c d), and τP is a valid
--   pair of X_[c,d]·s (PairValid);
-- * H_[c,d] on a valid pair: PairValid; on two entries of different
--   classes: H_[c,d] keeps the level, and commutes with H_Q for a valid
--   pair Q away from c and d, which exists unless exactly four entries
--   are odd (Hard); on two even entries whose halves have one parity:
--   it keeps the level and commutes with H_P; otherwise H_[c,d] goes up.
-- * Generators beyond p go up (Above).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Nat.Base as ℕ using (ℕ ; zero ; suc)
open import Data.Fin.Base using (Fin ; toℕ)
open import Data.Product.Base using (_,_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction using (EdgesBelow)

module Examples.Groups.Real-Clifford+CH-TwoLevel.PairEdges {n : ℕ} (p : Fin n) (k′ ℓ : ℕ)
  (ih : EdgesBelow {n} (suc (toℕ p) , suc k′ , ℓ)) where

open import Data.Bool.Base using (Bool ; true ; false ; not ; _∨_ ; _∧_ ; _xor_)
import Data.Bool.Properties as BoolP
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Fin.Base as Fin using (_<_ ; _≤_)
import Data.Fin.Properties as FinP
open import Data.Integer.Base as ℤ using (+_)
import Data.Nat.Properties as ℕP
open import Data.List.Relation.Unary.All using (All ; [] ; _∷_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (∃ ; _×_ ; proj₁ ; proj₂)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
open import Data.Unit.Base using (⊤ ; tt)
open import Data.Vec.Base as Vec using (Vec)
open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_ ; _≢_)
open import Relation.Nullary using (Dec ; yes ; no)
open import Relation.Nullary.Decidable using (does ; recompute)
import Relation.Binary.Reasoning.Setoid as SR

open import Quantum.Synthesis.Matrix using (Matrix)
open import Quantum.Synthesis.Ring using (RootTwo)

open import Notations using (auto)
open import Word.Base
import Presentation.Base as PB
import Presentation.Properties as PP
open import Examples.Groups.Clifford+CS-TwoLevel.Ring using (oddℕ ; oddℤ-+ ; oddℤ-*)
open import Examples.Groups.Clifford+CS-TwoLevel.Search using (count ; count-cong ; count-lt)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; Z ; module ZR ; module ZG ; √2ᶻ ; oddᶻ ; rbit ; oddᶻ-+ ; oddᶻ-neg ; rbit-+ ; rbit-neg ; even⇒δ∣)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Lde using (scV ; num ; lde ; lde-char ; Odd ; Even ; Minimal)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Column
open import Examples.Groups.Real-Clifford+CH-TwoLevel.ColumnAction using (Zᶻ ; Xᶻ ; Hᶻ ; actV-H)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics renaming (Z to Zʷ)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Pivot using (pivot ; Beyond ; Lvl ; level ; _<ₗ_ ; <ₗ-irrefl)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Syllable using (Beyond-actM)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Levels using (odd-Z ; lde-Z ; lde-X ; <ₗ-trans)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Counting using (search ; count-split ; count-two)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Derived {n} using (Z-Z ; H-H ; comm-gen)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Symmetric {n} using (τ ; τ-τ ; τ-inj ; Hs ; relabel-H)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Reduction {n} using (Path ; Low ; EdgesAt ; _≤ₗ_)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PathTools {n} using (module Below)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.States {n} using (pivot-stay ; level-of ; ne-𝕀)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Local {n} using (actV-H-same)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.UnitLevel {n} using (Xᶻ-τ ; conj-right)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Above {n} as Above
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairBase p k′ ℓ ih
open import Examples.Groups.Real-Clifford+CH-TwoLevel.PairValid p k′ ℓ ih

open PB (_===_ {n}) hiding (_===_)
open PP (_===_ {n})
open SR word-setoid
open Below {L = L} ih using (bridge)
open ZG using (_:+_ ; _:*_ ; :-_ ; _:-_ ; _:=_ ; con)

------------------------------------------------------------------------
-- The case left open

-- H_[c,d] on two odd entries of different classes, when exactly four
-- entries are odd: the paper's proof of this case (Lemma A.19, its
-- sub-case B) rests on Lemmas A.16 and A.17, which do not hold.
Hard : Set
Hard = ∀ (M : Matrix n n D) .(o : ColOrth M) → level M ≡ L → nodd (num (col M p)) ≡ 4 →
       ∀ c d .(cd : c < d) → Odd (num (col M p) ! c) → Odd (num (col M p) ! d) →
       rbit (num (col M p) ! c) ≢ rbit (num (col M p) ! d) → Path [ H-gen c d cd ]ʷ M o

-- The same, for one state.
Hard′ : (M : Matrix n n D) .(o : ColOrth M) → level M ≡ L → Set
Hard′ M o eq = nodd (num (col M p)) ≡ 4 →
               ∀ c d .(cd : c < d) → Odd (num (col M p) ! c) → Odd (num (col M p) ! d) →
               rbit (num (col M p) ! c) ≢ rbit (num (col M p) ! d) → Path [ H-gen c d cd ]ʷ M o

------------------------------------------------------------------------
-- Parities and words

private
  sym≢ : ∀ {x y : Fin n} → x ≢ y → y ≢ x
  sym≢ ne e = ne (≡.sym e)

  true≢false : true ≢ false
  true≢false ()

  rc : ∀ {a b : Fin n} → .(a < b) → a < b
  rc {a} {b} lt = recompute (a FinP.<? b) lt

  ∧-true : ∀ b → b ∧ true ≡ b
  ∧-true true = ≡.refl
  ∧-true false = ≡.refl

  -- The residue of √2 x is the parity of x.
  rbit-√2 : ∀ x → rbit (√2ᶻ ZR.* x) ≡ oddᶻ x
  rbit-√2 (RootTwo a b) =
    ≡.trans (oddℤ-+ (+ 0 ℤ.* b) (a ℤ.* + 1)) (≡.cong₂ _xor_ (oddℤ-* (+ 0) b) (≡.trans (oddℤ-* a (+ 1)) (∧-true _)))

  rbit-Z : (d : Fin n) (w : Vec Z n) (x : Fin n) → rbit (Zᶻ d w ! x) ≡ rbit (w ! x)
  rbit-Z d w x = at (x FinP.≟ d)
    where
    at : Dec (x ≡ d) → rbit (Zᶻ d w ! x) ≡ rbit (w ! x)
    at (yes ≡.refl) = ≡.trans (≡.cong rbit (set₁-a x (ZR.- (w ! x)) w)) (rbit-neg (w ! x))
    at (no x≢d) = ≡.cong rbit (set₁-≢ d (ZR.- (w ! d)) w x≢d)

  -- Is w one of x, y?
  in2 : Fin n → Fin n → Fin n → Bool
  in2 x y w = does (w FinP.≟ x) ∨ does (w FinP.≟ y)

  in2-true : ∀ {x y w} → in2 x y w ≡ true → w ≡ x ⊎ w ≡ y
  in2-true {x} {y} {w} = go (w FinP.≟ x) (w FinP.≟ y)
    where
    go : (d₁ : Dec (w ≡ x)) (d₂ : Dec (w ≡ y)) → does d₁ ∨ does d₂ ≡ true → w ≡ x ⊎ w ≡ y
    go (yes e) _ _ = inj₁ e
    go (no _) (yes e) _ = inj₂ e
    go (no _) (no _) ()

  in2-false : ∀ {x y w} → in2 x y w ≡ false → w ≢ x × w ≢ y
  in2-false {x} {y} {w} = go (w FinP.≟ x) (w FinP.≟ y)
    where
    go : (d₁ : Dec (w ≡ x)) (d₂ : Dec (w ≡ y)) → does d₁ ∨ does d₂ ≡ false → w ≢ x × w ≢ y
    go (yes _) _ ()
    go (no _) (yes _) ()
    go (no a) (no b) _ = a , b

  -- A level above L is not at most L.
  above : ∀ {x} → L <ₗ x → x ≤ₗ L → ⊥
  above h (inj₁ lt) = <ₗ-irrefl (<ₗ-trans h lt)
  above h (inj₂ ≡.refl) = <ₗ-irrefl h

module _ {a b : Fin n} (ab : a < b) where

  private
    Hab = H a b ab
    Xab = X a b ab
    Za = Zʷ a
    Zb = Zʷ b

  -- X H = H Z_[b].
  XH : Xab • Hab ≈ Hab • Zb
  XH = begin
    Xab • Hab                    ≈⟨ sym left-unit ⟩
    ε • Xab • Hab                ≈⟨ cleft sym (H-H ab) ⟩
    (Hab • Hab) • Xab • Hab      ≈⟨ by-assoc auto ⟩
    Hab • (Hab • Xab) • Hab      ≈⟨ cright cleft sym (axiom (d2 ab)) ⟩
    Hab • (Zb • Hab) • Hab       ≈⟨ by-assoc auto ⟩
    Hab • Zb • (Hab • Hab)       ≈⟨ cright cright H-H ab ⟩
    Hab • Zb • ε                 ≈⟨ cright right-unit ⟩
    Hab • Zb                     ∎

  -- Z_[a] Z_[b] X H = H Z_[a].
  ZZXH : (Za • Zb • Xab) • Hab ≈ Hab • Za
  ZZXH = begin
    (Za • Zb • Xab) • Hab        ≈⟨ assoc ⟩
    Za • (Zb • Xab) • Hab        ≈⟨ cright assoc ⟩
    Za • Zb • (Xab • Hab)        ≈⟨ cright cright XH ⟩
    Za • Zb • (Hab • Zb)         ≈⟨ cright sym assoc ⟩
    Za • (Zb • Hab) • Zb         ≈⟨ sym assoc ⟩
    (Za • Zb • Hab) • Zb         ≈⟨ cleft axiom (d1 ab) ⟩
    (Hab • Za • Zb) • Zb         ≈⟨ assoc ⟩
    Hab • (Za • Zb) • Zb         ≈⟨ cright assoc ⟩
    Hab • Za • (Zb • Zb)         ≈⟨ cright cright Z-Z ⟩
    Hab • Za • ε                 ≈⟨ cright right-unit ⟩
    Hab • Za                     ∎

------------------------------------------------------------------------
-- The edges out of a state at L

module At (s : Matrix n n D) .(o : ColOrth s) (eq : level s ≡ L) where

  open State s o eq

  -- The hard edge H_[c,d] out of s, when it is one.
  HardH : ∀ c d .(cd : c < d) → Set
  HardH c d cd = Odd (W ! c) → Odd (W ! d) → rbit (W ! c) ≢ rbit (W ! d) → nodd W ≡ 4 →
                 Path [ H-gen c d cd ]ʷ s o
  open V1 s o eq using (validEdge)

  private
    P₁₂ = H i₁ i₂ i₁<i₂

    oi₂ : Odd (W ! i₂)
    oi₂ = proj₁ (proj₂ valid₁₂)

    i₂≤p : i₂ ≤ p
    i₂≤p = odd≤ oi₂

    lt₁₂ : level (actM (H-gen i₁ i₂ i₁<i₂) s) <ₗ L
    lt₁₂ = below i₁ i₂ i₁<i₂ valid₁₂

    module Ab = Above.At s o p be

    xor-≢ : ∀ {a b : Bool} → a ≢ b → a xor b ≡ true
    xor-≢ {true} {true} ne = ⊥-elim (ne ≡.refl)
    xor-≢ {true} {false} _ = ≡.refl
    xor-≢ {false} {true} _ = ≡.refl
    xor-≢ {false} {false} ne = ⊥-elim (ne ≡.refl)

    xor-≡ : ∀ {a b : Bool} → a ≡ b → a xor b ≡ false
    xor-≡ {true} ≡.refl = ≡.refl
    xor-≡ {false} ≡.refl = ≡.refl

    -- Even and odd entries differ.
    eo≢ : ∀ {x y} → Even (W ! x) → Odd (W ! y) → x ≢ y
    eo≢ ex oy ≡.refl = true≢false (≡.trans (≡.sym oy) ex)

  ----------------------------------------------------------------------
  -- Z_[c], c ≤ p

  zEdge : ∀ c → c ≤ p → Path (Zʷ c) s o
  zEdge c c≤p = by (c FinP.≟ i₁) (c FinP.≟ i₂)
    where
    ZM = actM (Z-gen c) s
    eqZ : level ZM ≡ L
    eqZ = mono-L (Z-gen c) tt c≤p s eq
    module SZ = State ZM (ColOrth-actMʷ (Zʷ c) o) eqZ
    WZ : SZ.W ≡ Zᶻ c W
    WZ = ≡.trans (≡.cong num (col-actM (Z-gen c) s p)) (proj₂ (lde-Z c (col s p)))
    keep : ∀ {x y} → Valid W x y → Valid SZ.W x y
    keep {x} {y} (ox , oy , r) =
      ≡.trans (≡.cong (λ w → oddᶻ (w ! x)) WZ) (≡.trans (odd-Z c W x) ox) ,
      ≡.trans (≡.cong (λ w → oddᶻ (w ! y)) WZ) (≡.trans (odd-Z c W y) oy) ,
      ≡.trans (≡.cong (λ w → rbit (w ! x)) WZ)
        (≡.trans (rbit-Z c W x) (≡.trans r (≡.sym (≡.trans (≡.cong (λ w → rbit (w ! y)) WZ) (rbit-Z c W y)))))
    pZ : Path P₁₂ ZM (ColOrth-actMʷ (Zʷ c) o)
    pZ = V1.validEdge ZM (ColOrth-actMʷ (Zʷ c) o) eqZ i₁ i₂ i₁<i₂ (keep valid₁₂)
    sq : (V : Word (Gen n)) → Low L V (actMʷ P₁₂ s) → V • P₁₂ ≈ P₁₂ • Zʷ c → Path (Zʷ c) s o
    sq V lw rel = bridge (Z-gen c) s o P₁₂ P₁₂ V canonical pZ lw rel
    H₁ = actM (H-gen i₁ i₂ i₁<i₂) s
    by : Dec (c ≡ i₁) → Dec (c ≡ i₂) → Path (Zʷ c) s o
    by (yes ≡.refl) _ = sq (Zʷ c • Zʷ i₂ • X c i₂ i₁<i₂) lowV (ZZXH i₁<i₂)
      where
      l₁ = X-low i₁<i₂ i₂≤p H₁ lt₁₂
      l₂ = Z-low i₂≤p (actM (X-gen c i₂ i₁<i₂) H₁) l₁
      l₃ = Z-low c≤p (actM (Z-gen i₂) (actM (X-gen c i₂ i₁<i₂) H₁)) l₂
      lowV : Low L (Zʷ c • Zʷ i₂ • X c i₂ i₁<i₂) H₁
      lowV = ((lt₁₂ , l₁) , (l₁ , l₂)) , (l₂ , l₃)
    by (no _) (yes ≡.refl) = sq (X i₁ c i₁<i₂) (lt₁₂ , X-low i₁<i₂ c≤p H₁ lt₁₂) (XH i₁<i₂)
    by (no c≢i₁) (no c≢i₂) =
      sq (Zʷ c) (lt₁₂ , Z-low c≤p H₁ lt₁₂) (comm-gen (Z-gen c) (H-gen i₁ i₂ i₁<i₂) ((c≢i₁ ∷ c≢i₂ ∷ []) ∷ []))

  ----------------------------------------------------------------------
  -- X_[c,d], d ≤ p

  xEdge′ : ∀ c d .(cd : c < d) → d ≤ p → Path [ X-gen c d cd ]ʷ s o
  xEdge′ c d cd d≤p =
    bridge (X-gen c d cd) s o P₁₂ (Hs (τ c d i₁) (τ c d i₂)) (X c d cd) canonical pHs
      (lt₁₂ , X-low cd d≤p _ lt₁₂) (conj-right cd (relabel-H (rc cd) i₁<i₂))
    where
    c≢d = <⇒≢ cd
    XM = actM (X-gen c d cd) s
    eqX : level XM ≡ L
    eqX = mono-L (X-gen c d cd) tt d≤p s eq
    module SX = State XM (ColOrth-actMʷ (X c d cd) o) eqX
    WX : SX.W ≡ Xᶻ c d W
    WX = ≡.trans (≡.cong num (col-actM (X-gen c d cd) s p)) (proj₂ (lde-X c d cd (col s p)))
    e : ∀ x → SX.W ! τ c d x ≡ W ! x
    e x = ≡.trans (≡.cong (_! τ c d x) WX) (≡.trans (Xᶻ-τ c d c≢d W (τ c d x)) (≡.cong (W !_) (τ-τ c d x c≢d)))
    vlX : Valid SX.W (τ c d i₁) (τ c d i₂)
    vlX = ≡.trans (≡.cong oddᶻ (e i₁)) oi₁ , ≡.trans (≡.cong oddᶻ (e i₂)) oi₂ ,
          ≡.trans (≡.cong rbit (e i₁)) (≡.trans (proj₂ (proj₂ valid₁₂)) (≡.cong rbit (≡.sym (e i₂))))
    pHs : Path (Hs (τ c d i₁) (τ c d i₂)) XM (ColOrth-actMʷ (X c d cd) o)
    pHs = V2.hsEdge XM (ColOrth-actMʷ (X c d cd) o) eqX (τ c d i₁) (τ c d i₂) (λ q → <⇒≢ i₁<i₂ (τ-inj c d c≢d q)) vlX

  xAll : ∀ c d .(cd : c < d) → Path [ X-gen c d cd ]ʷ s o
  xAll c d cd = by (p FinP.<? d)
    where
    by : Dec (p < d) → Path [ X-gen c d cd ]ʷ s o
    by (yes p<d) = Ab.edge-X c d cd p<d
    by (no p≮d) = xEdge′ c d cd (ℕP.≮⇒≥ p≮d)

  ----------------------------------------------------------------------
  -- H_[c,d], d ≤ p, at the same scale

  module HCD {c d : Fin n} .(cd : c < d) (d≤p : d ≤ p) (α β : Z)
             (sum : W ! c ZR.+ W ! d ≡ √2ᶻ ZR.* α) (dif : W ! c ZR.- W ! d ≡ √2ᶻ ZR.* β) where

    c≢d : c ≢ d
    c≢d = <⇒≢ cd

    HM = actM (H-gen c d cd) s

    w′ : Vec Z n
    w′ = set₂ c d α β W

    colH : col HM p ≡ scV k w′
    colH = ≡.trans (col-actM (H-gen c d cd) s p)
             (≡.trans (≡.cong (actV (H-gen c d cd)) colM) (actV-H-same c d cd k W α β sum dif))

    -- With an odd entry, H_[c,d]·s has pivot p and exponent k.
    module Odd′ (ox : ∃ λ x → Odd (w′ ! x)) where

      pvH : pivot HM ≡ just p
      pvH = pivot-stay (H-gen c d cd) s d≤p pv (ne-𝕀 HM p k′ w′ colH (inj₂ ox))

      levelH : level HM ≡ (suc (toℕ p) , k , nodd w′)
      levelH = level-of HM pvH k w′ colH (inj₂ ox)

      numH : num (col HM p) ≡ w′
      numH = proj₂ (lde-char k w′ colH (inj₂ ox))

      -- If the odd entries are those of W, it lies at L.
      at-L : (∀ x → oddᶻ (w′ ! x) ≡ oddᶻ (W ! x)) → level HM ≡ L
      at-L same = ≡.trans levelH (≡.cong (λ m → suc (toℕ p) , k , m)
                    (≡.trans (count-cong (λ x → oddᶻ (w′ ! x)) (λ x → oddᶻ (W ! x)) same) ℓM))

      keep : ∀ {q q′} → q ≢ c → q ≢ d → q′ ≢ c → q′ ≢ d → Valid W q q′ → Valid (num (col HM p)) q q′
      keep {q} {q′} qc qd q′c q′d (oq , oq′ , r) =
        ≡.trans (≡.cong oddᶻ eq₁) oq , ≡.trans (≡.cong oddᶻ eq₂) oq′ ,
        ≡.trans (≡.cong rbit eq₁) (≡.trans r (≡.cong rbit (≡.sym eq₂)))
        where
        eq₁ : num (col HM p) ! q ≡ W ! q
        eq₁ = ≡.trans (≡.cong (_! q) numH) (set₂-≢ c d α β W qc qd)
        eq₂ : num (col HM p) ! q′ ≡ W ! q′
        eq₂ = ≡.trans (≡.cong (_! q′) numH) (set₂-≢ c d α β W q′c q′d)

    -- The parities of the new entries.
    par-c : oddᶻ (w′ ! c) ≡ oddᶻ α
    par-c = ≡.cong oddᶻ (set₂-a c d α β W)
    par-d : oddᶻ (w′ ! d) ≡ oddᶻ β
    par-d = ≡.cong oddᶻ (set₂-b c d α β W c≢d)
    par-o : ∀ {x} → x ≢ c → x ≢ d → w′ ! x ≡ W ! x
    par-o x≢c x≢d = set₂-≢ c d α β W x≢c x≢d

    -- After H on a valid pair q, q′ away from c and d, H_[c,d] lies
    -- below L, if its odd new entries are at odd entries of W.
    after : ∀ q q′ .(qq : q < q′) → Valid W q q′ → c ≢ q → c ≢ q′ → d ≢ q → d ≢ q′ →
            (Odd α → Odd (W ! c)) → (Odd β → Odd (W ! d)) →
            level (actM (H-gen c d cd) (actM (H-gen q q′ qq) s)) <ₗ L
    after q q′ qq vl cq cq′ dq dq′ oα oβ = low N₂ be₂ w″ col₂ (≡.subst (nodd w″ ℕ.<_) ℓM fewer)
      where
      S₁ = stepM q q′ qq vl
      w₁ = PairStep.w′ S₁
      N₁ = actM (H-gen q q′ qq) s
      N₂ = actM (H-gen c d cd) N₁
      sc : w₁ ! c ≡ W ! c
      sc = PairStep.same S₁ c cq cq′
      sd : w₁ ! d ≡ W ! d
      sd = PairStep.same S₁ d dq dq′
      w″ = set₂ c d α β w₁
      col₂ : col N₂ p ≡ scV k w″
      col₂ = ≡.trans (col-actM (H-gen c d cd) N₁ p)
               (≡.trans (≡.cong (actV (H-gen c d cd)) (PairStep.col′ S₁))
                  (actV-H-same c d cd k w₁ α β (≡.trans (≡.cong₂ ZR._+_ sc sd) sum) (≡.trans (≡.cong₂ ZR._-_ sc sd) dif)))
      be₂ : Beyond p N₂
      be₂ = Beyond-actM (H-gen c d cd) {p} {N₁} d≤p (Beyond-actM (H-gen q q′ qq) {p} {s} (odd≤ (proj₁ (proj₂ vl))) be)
      imp : ∀ x → oddᶻ (w″ ! x) ≡ true → oddᶻ (W ! x) ≡ true
      imp x ox = at (x FinP.≟ c) (x FinP.≟ d)
        where
        at : Dec (x ≡ c) → Dec (x ≡ d) → oddᶻ (W ! x) ≡ true
        at (yes ≡.refl) _ = oα (≡.trans (≡.sym (≡.cong oddᶻ (set₂-a x d α β w₁))) ox)
        at (no _) (yes ≡.refl) = oβ (≡.trans (≡.sym (≡.cong oddᶻ (set₂-b c x α β w₁ c≢d))) ox)
        at (no x≢c) (no x≢d) = from₁ (x FinP.≟ q) (x FinP.≟ q′)
          where
          o₁ : oddᶻ (w₁ ! x) ≡ true
          o₁ = ≡.trans (≡.cong oddᶻ (≡.sym (set₂-≢ c d α β w₁ x≢c x≢d))) ox
          from₁ : Dec (x ≡ q) → Dec (x ≡ q′) → oddᶻ (W ! x) ≡ true
          from₁ (yes ≡.refl) _ = ⊥-elim (true≢false (≡.trans (≡.sym o₁) (PairStep.ev-i S₁)))
          from₁ (no _) (yes ≡.refl) = ⊥-elim (true≢false (≡.trans (≡.sym o₁) (PairStep.ev-j S₁)))
          from₁ (no x≢q) (no x≢q′) = ≡.trans (≡.cong oddᶻ (≡.sym (PairStep.same S₁ x x≢q x≢q′))) o₁
      fewer : nodd w″ ℕ.< nodd W
      fewer = count-lt (λ x → oddᶻ (W ! x)) (λ x → oddᶻ (w″ ! x)) q imp (proj₁ vl)
                (≡.trans (≡.cong oddᶻ (set₂-≢ c d α β w₁ (sym≢ cq) (sym≢ dq))) (PairStep.ev-i S₁))

    -- The square with the edge H on a valid pair q, q′ away from c and d.
    square-cd : ∀ q q′ .(qq : q < q′) → Valid W q q′ → c ≢ q → c ≢ q′ → d ≢ q → d ≢ q′ →
                (Odd α → Odd (W ! c)) → (Odd β → Odd (W ! d)) →
                (ox : ∃ λ x → Odd (w′ ! x)) → (∀ x → oddᶻ (w′ ! x) ≡ oddᶻ (W ! x)) →
                Path [ H-gen c d cd ]ʷ s o
    square-cd q q′ qq vl cq cq′ dq dq′ oα oβ ox same =
      bridge (H-gen c d cd) s o (H q q′ qq) (H q q′ qq) (H c d cd) (validEdge q q′ qq vl) pQ
        (below q q′ qq vl , after q q′ qq vl cq cq′ dq dq′ oα oβ)
        (comm-gen (H-gen c d cd) (H-gen q q′ qq) ((cq ∷ cq′ ∷ []) ∷ (dq ∷ dq′ ∷ []) ∷ []))
      where
      open Odd′ ox
      pQ : Path (H q q′ qq) HM (ColOrth-actMʷ (H c d cd) o)
      pQ = V1.validEdge HM (ColOrth-actMʷ (H c d cd) o) (at-L same) q q′ qq (keep (sym≢ cq) (sym≢ dq) (sym≢ cq′) (sym≢ dq′) vl)

  ----------------------------------------------------------------------
  -- Two odd entries of different classes

  delta : ∀ c d .(cd : c < d) → d ≤ p → (oc : Odd (W ! c)) (od : Odd (W ! d)) (rcd : rbit (W ! c) ≢ rbit (W ! d)) →
          (nodd W ≡ 4 → Path [ H-gen c d cd ]ʷ s o) → Path [ H-gen c d cd ]ʷ s o
  delta c d cd d≤p oc od rcd hard = find-c (search (Cls κc) (in2 c c′))
    where
    κc = rbit (W ! c)
    κd = rbit (W ! d)
    sumE : Even (W ! c ZR.+ W ! d)
    sumE = ≡.trans (oddᶻ-+ (W ! c) (W ! d)) (≡.cong₂ _xor_ oc od)
    difE : Even (W ! c ZR.- W ! d)
    difE = ≡.trans (oddᶻ-+ (W ! c) (ZR.- (W ! d))) (≡.cong₂ _xor_ oc (≡.trans (oddᶻ-neg (W ! d)) od))
    Dα = even⇒δ∣ (W ! c ZR.+ W ! d) sumE
    Dβ = even⇒δ∣ (W ! c ZR.- W ! d) difE
    α = proj₁ Dα
    β = proj₁ Dβ
    open HCD {c} {d} cd d≤p α β (proj₂ Dα) (proj₂ Dβ)
    oα : Odd α
    oα = ≡.trans (≡.sym (rbit-√2 α))
           (≡.trans (≡.cong rbit (≡.sym (proj₂ Dα))) (≡.trans (rbit-+ (W ! c) (W ! d)) (xor-≢ rcd)))
    oβ : Odd β
    oβ = ≡.trans (≡.sym (rbit-√2 β))
           (≡.trans (≡.cong rbit (≡.sym (proj₂ Dβ)))
             (≡.trans (rbit-+ (W ! c) (ZR.- (W ! d))) (≡.trans (≡.cong (κc xor_) (rbit-neg (W ! d))) (xor-≢ rcd))))
    same : ∀ x → oddᶻ (w′ ! x) ≡ oddᶻ (W ! x)
    same x = at (x FinP.≟ c) (x FinP.≟ d)
      where
      at : Dec (x ≡ c) → Dec (x ≡ d) → oddᶻ (w′ ! x) ≡ oddᶻ (W ! x)
      at (yes ≡.refl) _ = ≡.trans par-c (≡.trans oα (≡.sym oc))
      at (no _) (yes ≡.refl) = ≡.trans par-d (≡.trans oβ (≡.sym od))
      at (no x≢c) (no x≢d) = ≡.cong oddᶻ (par-o x≢c x≢d)
    ox : ∃ λ x → Odd (w′ ! x)
    ox = c , ≡.trans par-c oα

    -- With a valid pair away from c and d.
    with-pair : ∀ x y → x ≢ y → Odd (W ! x) → Odd (W ! y) → rbit (W ! x) ≡ rbit (W ! y) →
                c ≢ x → c ≢ y → d ≢ x → d ≢ y → Path [ H-gen c d cd ]ʷ s o
    with-pair x y x≢y ox′ oy r cx cy dx dy = by (FinP.<-cmp x y)
      where
      by : Tri (x < y) (x ≡ y) (y < x) → Path [ H-gen c d cd ]ʷ s o
      by (tri< lt _ _) = square-cd x y lt (ox′ , oy , r) cx cy dx dy (λ _ → oc) (λ _ → od) ox same
      by (tri≈ _ e _) = ⊥-elim (x≢y e)
      by (tri> _ _ gt) = square-cd y x gt (oy , ox′ , ≡.sym r) cy cx dy dx (λ _ → oc) (λ _ → od) ox same

    Pc = partner c oc
    c′ = proj₁ Pc
    c′≢c = proj₁ (proj₂ Pc)
    oc′ = proj₁ (proj₂ (proj₂ Pc))
    rc′ = proj₂ (proj₂ (proj₂ Pc))
    Pd = partner d od
    d′ = proj₁ Pd
    d′≢d = proj₁ (proj₂ Pd)
    od′ = proj₁ (proj₂ (proj₂ Pd))
    rd′ = proj₂ (proj₂ (proj₂ Pd))

    -- Members of different classes differ.
    cls≢ : ∀ {x y} → rbit (W ! x) ≢ rbit (W ! y) → x ≢ y
    cls≢ ne ≡.refl = ne ≡.refl

    count2 : ∀ b x x′ → x ≢ x′ → Odd (W ! x) → Odd (W ! x′) → rbit (W ! x) ≡ b → rbit (W ! x′) ≡ b →
             (∀ y → Cls b y ≡ true → in2 x x′ y ≡ true) → count (Cls b) ≡ 2
    count2 b x x′ ne ox′ ox″ rx rx′ all =
      count-two (Cls b) x x′ ne (≡.subst (λ b′ → Cls b′ x ≡ true) rx (cls-true x ox′))
        (≡.subst (λ b′ → Cls b′ x′ ≡ true) rx′ (cls-true x′ ox″)) (λ y cy → in2-true (all y cy))

    four : ∀ b₁ b₂ → b₁ ≢ b₂ → count (Cls b₁) ≡ 2 → count (Cls b₂) ≡ 2 → nodd W ≡ 4
    four true true ne _ _ = ⊥-elim (ne ≡.refl)
    four false false ne _ _ = ⊥-elim (ne ≡.refl)
    four true false _ e₁ e₂ = ≡.trans split (≡.cong₂ ℕ._+_ e₁ e₂)
      where split = count-split (λ x → oddᶻ (W ! x)) (λ x → rbit (W ! x))
    four false true _ e₁ e₂ = ≡.trans split (≡.cong₂ ℕ._+_ e₂ e₁)
      where split = count-split (λ x → oddᶻ (W ! x)) (λ x → rbit (W ! x))

    find-d : count (Cls κc) ≡ 2 →
             (∃ λ y → Cls κd y ≡ true × in2 d d′ y ≡ false) ⊎ (∀ y → Cls κd y ≡ true → in2 d d′ y ≡ true) →
             Path [ H-gen c d cd ]ʷ s o
    find-d _ (inj₁ (d″ , cy , f)) =
      with-pair d′ d″ (λ e → proj₂ (in2-false f) (≡.sym e)) od′ (proj₁ (cls-spec κd d″ cy))
        (≡.trans rd′ (≡.sym (proj₂ (cls-spec κd d″ cy))))
        (cls≢ (λ e → rcd (≡.trans e rd′))) (cls≢ (λ e → rcd (≡.trans e (proj₂ (cls-spec κd d″ cy)))))
        (sym≢ d′≢d) (sym≢ (proj₁ (in2-false f)))
    find-d cc (inj₂ all) =
      hard (four κc κd rcd cc (count2 κd d d′ (sym≢ d′≢d) od od′ ≡.refl rd′ all))

    find-c : (∃ λ y → Cls κc y ≡ true × in2 c c′ y ≡ false) ⊎ (∀ y → Cls κc y ≡ true → in2 c c′ y ≡ true) →
             Path [ H-gen c d cd ]ʷ s o
    find-c (inj₁ (c″ , cy , f)) =
      with-pair c′ c″ (λ e → proj₂ (in2-false f) (≡.sym e)) oc′ (proj₁ (cls-spec κc c″ cy))
        (≡.trans rc′ (≡.sym (proj₂ (cls-spec κc c″ cy))))
        (sym≢ c′≢c) (sym≢ (proj₁ (in2-false f)))
        (cls≢ (λ e → rcd (≡.trans (≡.sym rc′) (≡.sym e))))
        (cls≢ (λ e → rcd (≡.trans (≡.sym (proj₂ (cls-spec κc c″ cy))) (≡.sym e))))
    find-c (inj₂ all) =
      find-d (count2 κc c c′ (sym≢ c′≢c) oc oc′ ≡.refl rc′ all) (search (Cls κd) (in2 d d′))

  ----------------------------------------------------------------------
  -- Two even entries

  beta : ∀ c d .(cd : c < d) → d ≤ p → Even (W ! c) → Even (W ! d) →
         level (actM (H-gen c d cd) s) ≤ₗ L → Path [ H-gen c d cd ]ʷ s o
  beta c d cd d≤p ec ed le = by (oddᶻ x BoolP.≟ oddᶻ y)
    where
    Dx = even⇒δ∣ (W ! c) ec
    Dy = even⇒δ∣ (W ! d) ed
    x = proj₁ Dx
    y = proj₁ Dy
    sumH : W ! c ZR.+ W ! d ≡ √2ᶻ ZR.* (x ZR.+ y)
    sumH = ≡.trans (≡.cong₂ ZR._+_ (proj₂ Dx) (proj₂ Dy))
            (ZG.solve 2 (λ x y → con √2ᶻ :* x :+ con √2ᶻ :* y := con √2ᶻ :* (x :+ y)) ≡.refl x y)
    difH : W ! c ZR.- W ! d ≡ √2ᶻ ZR.* (x ZR.- y)
    difH = ≡.trans (≡.cong₂ ZR._-_ (proj₂ Dx) (proj₂ Dy))
            (ZG.solve 2 (λ x y → con √2ᶻ :* x :- con √2ᶻ :* y := con √2ᶻ :* (x :- y)) ≡.refl x y)
    open HCD {c} {d} cd d≤p (x ZR.+ y) (x ZR.- y) sumH difH
    pα : oddᶻ (x ZR.+ y) ≡ oddᶻ x xor oddᶻ y
    pα = oddᶻ-+ x y
    pβ : oddᶻ (x ZR.- y) ≡ oddᶻ x xor oddᶻ y
    pβ = ≡.trans (oddᶻ-+ x (ZR.- y)) (≡.cong (oddᶻ x xor_) (oddᶻ-neg y))
    i₁≢c : i₁ ≢ c
    i₁≢c = sym≢ (eo≢ ec oi₁)
    i₁≢d : i₁ ≢ d
    i₁≢d = sym≢ (eo≢ ed oi₁)
    i₂≢c : i₂ ≢ c
    i₂≢c = sym≢ (eo≢ ec oi₂)
    i₂≢d : i₂ ≢ d
    i₂≢d = sym≢ (eo≢ ed oi₂)
    by : Dec (oddᶻ x ≡ oddᶻ y) → Path [ H-gen c d cd ]ʷ s o
    -- The halves have one parity: H_[c,d] keeps the level.
    by (yes e) = square-cd i₁ i₂ i₁<i₂ valid₁₂ (sym≢ i₁≢c) (sym≢ i₂≢c) (sym≢ i₁≢d) (sym≢ i₂≢d)
                   (λ h → ⊥-elim (true≢false (≡.trans (≡.sym h) evα)))
                   (λ h → ⊥-elim (true≢false (≡.trans (≡.sym h) evβ)))
                   (i₁ , ≡.trans (≡.cong oddᶻ (par-o i₁≢c i₁≢d)) oi₁) same
      where
      evα : Even (x ZR.+ y)
      evα = ≡.trans pα (xor-≡ e)
      evβ : Even (x ZR.- y)
      evβ = ≡.trans pβ (xor-≡ e)
      same : ∀ z → oddᶻ (w′ ! z) ≡ oddᶻ (W ! z)
      same z = at (z FinP.≟ c) (z FinP.≟ d)
        where
        at : Dec (z ≡ c) → Dec (z ≡ d) → oddᶻ (w′ ! z) ≡ oddᶻ (W ! z)
        at (yes ≡.refl) _ = ≡.trans par-c (≡.trans evα (≡.sym ec))
        at (no _) (yes ≡.refl) = ≡.trans par-d (≡.trans evβ (≡.sym ed))
        at (no z≢c) (no z≢d) = ≡.cong oddᶻ (par-o z≢c z≢d)
    -- Different parities: two more odd entries, H_[c,d] goes up.
    by (no ne) = ⊥-elim (above up le)
      where
      oα : Odd (x ZR.+ y)
      oα = ≡.trans pα (xor-≢ ne)
      open Odd′ (c , ≡.trans par-c oα)
      imp : ∀ z → oddᶻ (W ! z) ≡ true → oddᶻ (w′ ! z) ≡ true
      imp z oz = at (z FinP.≟ c) (z FinP.≟ d)
        where
        at : Dec (z ≡ c) → Dec (z ≡ d) → oddᶻ (w′ ! z) ≡ true
        at (yes ≡.refl) _ = ⊥-elim (true≢false (≡.trans (≡.sym oz) ec))
        at (no _) (yes ≡.refl) = ⊥-elim (true≢false (≡.trans (≡.sym oz) ed))
        at (no z≢c) (no z≢d) = ≡.trans (≡.cong oddᶻ (par-o z≢c z≢d)) oz
      more : ℓ ℕ.< nodd w′
      more = ≡.subst (ℕ._< nodd w′) ℓM
               (count-lt (λ z → oddᶻ (w′ ! z)) (λ z → oddᶻ (W ! z)) c imp (≡.trans par-c oα) ec)
      up : L <ₗ level HM
      up = ≡.subst (L <ₗ_) (≡.sym levelH) (inj₂ (≡.refl , inj₂ (≡.refl , more)))

  ----------------------------------------------------------------------
  -- One odd entry: H_[c,d] raises the exponent

  gamma : ∀ c d .(cd : c < d) → d ≤ p → oddᶻ (W ! c) xor oddᶻ (W ! d) ≡ true →
          level (actM (H-gen c d cd) s) ≤ₗ L → ⊥
  gamma c d cd d≤p x le = above up le
    where
    HM = actM (H-gen c d cd) s
    w′ = Hᶻ c d W
    colH : col HM p ≡ scV (suc k) w′
    colH = ≡.trans (col-actM (H-gen c d cd) s p) (≡.trans (≡.cong (actV (H-gen c d cd)) colM) (actV-H c d cd k W))
    oc : Odd (w′ ! c)
    oc = ≡.trans (≡.cong oddᶻ (set₂-a c d (W ! c ZR.+ W ! d) (W ! c ZR.- W ! d) (Vec.map (√2ᶻ ZR.*_) W)))
           (≡.trans (oddᶻ-+ (W ! c) (W ! d)) x)
    pvH : pivot HM ≡ just p
    pvH = pivot-stay (H-gen c d cd) s d≤p pv (ne-𝕀 HM p k w′ colH (inj₂ (c , oc)))
    up : L <ₗ level HM
    up = ≡.subst (L <ₗ_) (≡.sym (level-of HM pvH (suc k) w′ colH (inj₂ (c , oc))))
           (inj₂ (≡.refl , inj₁ (ℕP.n<1+n k)))

  hEdge : ∀ c d .(cd : c < d) → d ≤ p → level (actM (H-gen c d cd) s) ≤ₗ L → HardH c d cd →
          Path [ H-gen c d cd ]ʷ s o
  hEdge c d cd d≤p le hard = by (oddᶻ (W ! c)) (oddᶻ (W ! d)) ≡.refl ≡.refl
    where
    by : ∀ u v → oddᶻ (W ! c) ≡ u → oddᶻ (W ! d) ≡ v → Path [ H-gen c d cd ]ʷ s o
    by true true oc od = by-r (rbit (W ! c) BoolP.≟ rbit (W ! d))
      where
      by-r : Dec (rbit (W ! c) ≡ rbit (W ! d)) → Path [ H-gen c d cd ]ʷ s o
      by-r (yes r) = validEdge c d cd (oc , od , r)
      by-r (no r) = delta c d cd d≤p oc od r (hard oc od r)
    by true false oc ed = ⊥-elim (gamma c d cd d≤p (≡.cong₂ _xor_ oc ed) le)
    by false true ec od = ⊥-elim (gamma c d cd d≤p (≡.cong₂ _xor_ ec od) le)
    by false false ec ed = beta c d cd d≤p ec ed le

  ----------------------------------------------------------------------
  -- All edges that do not go up

  -- What an edge needs besides its level: for H, the hard case.
  Needs : Gen n → Set
  Needs (H-gen c d cd) = HardH c d cd
  Needs _ = ⊤

  edgesWith : ∀ (g : Gen n) → level (actM g s) ≤ₗ L → Needs g → Path [ g ]ʷ s o
  edgesWith (Z-gen c) _ _ = by (p FinP.<? c)
    where
    by : Dec (p < c) → Path (Zʷ c) s o
    by (yes p<c) = Ab.edge-Z c p<c
    by (no p≮c) = zEdge c (ℕP.≮⇒≥ p≮c)
  edgesWith (X-gen c d cd) _ _ = xAll c d cd
  edgesWith (H-gen c d cd) le hard = by (p FinP.<? d)
    where
    by : Dec (p < d) → Path [ H-gen c d cd ]ʷ s o
    by (yes p<d) = Ab.edge-H c d cd p<d xAll
    by (no p≮d) = hEdge c d cd (ℕP.≮⇒≥ p≮d) le hard

  -- Given the hard edges of s.
  edges : Hard′ s o eq → ∀ (g : Gen n) → level (actM g s) ≤ₗ L → Path [ g ]ʷ s o
  edges hard (Z-gen c) le = edgesWith (Z-gen c) le tt
  edges hard (X-gen c d cd) le = edgesWith (X-gen c d cd) le tt
  edges hard (H-gen c d cd) le = edgesWith (H-gen c d cd) le (λ oc od r n4 → hard n4 c d cd oc od r)

edgesAt : Hard → EdgesAt L
edgesAt hard g M o eq le = At.edges M o eq (λ n4 → hard M o eq n4) g le
