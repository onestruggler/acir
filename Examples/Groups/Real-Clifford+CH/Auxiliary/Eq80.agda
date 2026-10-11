------------------------------------------------------------------------
-- Presentations of groups
--
-- Figure 11's (80), from Figure 8's (46)
--
--     (H_[0,1] H_[0,2]) (H_[1,3] H_[0,4]) (H_[1,5] H_[0,1]) ((−1)_[1] (−1)_[0])
--       (H_[0,4] H_[1,5]) (H_[0,2] H_[1,3])
--   ≈ (H_[0,2] H_[1,3]) (H_[0,4] H_[1,5]) ((−1)_[1] (−1)_[0])
--       (H_[0,1] H_[0,4]) (H_[1,5] H_[0,2]) (H_[1,3] H_[0,1])
--
-- The paper's proof, a chain of twenty-seven lines: conjugate by
-- σ = ((−1)_[6] X_[2,3]) ((−1)_[2] (−1)_[3]), carry σ⁻¹ across the
-- letters to the right (Corollary A.10 there, one Hadamard pair at a
-- time), regroup the pairs with (70), (73) and (66) until the word is
-- σ (46)ₗ σ⁻¹, apply (46), and undo it all on the other side.  Each
-- line was checked numerically (`scratchpad/t80.py`).
--
-- The words are lists of letters (`⟪_⟫`) and each line is obtained
-- from the previous one by replacing a segment (`step`), so only the
-- replaced letters are ever written.  The A.10 moves are decided by
-- the frame normaliser (`FrameNorm.by-norm`) with a frame pair of the
-- two or three indices the move does not touch — on three qubits the
-- chain as a whole uses all eight, so no single frame would do — and
-- the two moves that touch seven indices carry a Hadamard-free word
-- across a pair with matching signs (`Move.hh-pass`), which needs no
-- frame.  Indices are the numerals 0 … 7 at every width (`Gray.fin8`),
-- and distinctness of numerals is decided (`nodup`, `fresh`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat using (ℕ)

module Examples.Groups.Real-Clifford+CH.Auxiliary.Eq80 (m : ℕ) where

open import Data.Bool using (Bool ; true ; false ; T)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ-inject≤)
open import Data.List using (List ; [] ; _∷_ ; _++_ ; take ; drop)
open import Data.List.Properties using (take++drop≡id)
open import Data.Nat using (zero ; suc ; _+_) renaming (_^_ to _^ℕ_ ; _≟_ to _≟ℕ_)
open import Data.Product using (_,_ ; proj₁ ; proj₂)
open import Data.Unit using (tt)
open import Data.Vec as Vec using (Vec ; [] ; _∷_ ; lookup)
open import Data.Vec.Relation.Unary.All using (All ; [] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_)
open import Relation.Nullary using (yes ; no)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₅ ; ₆ ; ₇ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Auxiliary.P using (GenP)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure8 using (_P,_===_ ; r46)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Gray using (fin8)
open import Examples.Groups.Real-Clifford+CH.Encoding using (hh ; zz ; zx ; xx ; hhℕ ; zzℕ)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.LowGens m using (hhℕ-hh)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.DE m using (zzℕ-zz)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Template m
  using (Distinct ; []ᵈ ; _∷ᵈ_ ; lookup-inj ; allAt ; tz ; ty ; tx ; ⌜_⌝ ; _•ᵗ_ ; emp
        ; TW ; module At)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Figure10 m using (Eq65 ; eq66 ; eq70)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Fuse m
  using (fuse ; hh-invol ; eq73 ; mkOff)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.Move m using (hh-pass)
open import Examples.Groups.Real-Clifford+CH.Auxiliary.FrameNorm m using (module Norm)
open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)

open Tools (m P,_===_)

private
  N : ℕ
  N = 2 ^ℕ (₃₊ m)

  W : Set
  W = Word (GenP (₃₊ m))

  refl≡ : ∀ {u v : W} → u ≡ v → u ≈ v
  refl≡ Eq.refl = refl

------------------------------------------------------------------------
-- Words as lists of letters, and replacing a segment

⟪_⟫ : List W → W
⟪ [] ⟫         = ε
⟪ x ∷ [] ⟫     = x
⟪ x ∷ y ∷ xs ⟫ = x • ⟪ y ∷ xs ⟫

private
  ⟪⟫-∷ : ∀ (x : W) (xs : List W) → ⟪ x ∷ xs ⟫ ≈ x • ⟪ xs ⟫
  ⟪⟫-∷ x []       = sym right-unit
  ⟪⟫-∷ x (y ∷ xs) = refl

  ⟪⟫-++ : ∀ (xs ys : List W) → ⟪ xs ++ ys ⟫ ≈ ⟪ xs ⟫ • ⟪ ys ⟫
  ⟪⟫-++ []       ys = sym left-unit
  ⟪⟫-++ (x ∷ xs) ys =
    trans (⟪⟫-∷ x (xs ++ ys))
    (trans (back x (⟪⟫-++ xs ys))
    (trans (sym assoc) (front ⟪ ys ⟫ (sym (⟪⟫-∷ x xs)))))

  seg : ∀ (p x y s : List W) → ⟪ x ⟫ ≈ ⟪ y ⟫ → ⟪ p ++ x ++ s ⟫ ≈ ⟪ p ++ y ++ s ⟫
  seg p x y s e =
    trans (⟪⟫-++ p (x ++ s))
    (trans (back ⟪ p ⟫ (trans (⟪⟫-++ x s) (trans (front ⟪ s ⟫ e) (sym (⟪⟫-++ y s)))))
           (sym (⟪⟫-++ p (y ++ s))))

  drop-drop′ : ∀ (k n : ℕ) (xs : List W) → drop n (drop k xs) ≡ drop (k + n) xs
  drop-drop′ zero    n xs       = Eq.refl
  drop-drop′ (suc k) zero    [] = Eq.refl
  drop-drop′ (suc k) (suc n) [] = Eq.refl
  drop-drop′ (suc k) n (x ∷ xs) = drop-drop′ k n xs

-- Replace the n letters from position k by ys.
step : ∀ (k n : ℕ) (xs ys : List W) → ⟪ take n (drop k xs) ⟫ ≈ ⟪ ys ⟫ →
       ⟪ xs ⟫ ≈ ⟪ take k xs ++ ys ++ drop (k + n) xs ⟫
step k n xs ys e =
  trans (refl≡ (Eq.cong ⟪_⟫ split))
  (trans (seg (take k xs) (take n (drop k xs)) ys (drop n (drop k xs)) e)
         (refl≡ (Eq.cong (λ r → ⟪ take k xs ++ ys ++ r ⟫) (drop-drop′ k n xs))))
  where
  split : xs ≡ take k xs ++ (take n (drop k xs) ++ drop n (drop k xs))
  split = Eq.trans (Eq.sym (take++drop≡id k xs))
                   (Eq.cong (take k xs ++_) (Eq.sym (take++drop≡id n (drop k xs))))

-- A chain of replacements, each segment's equation typed by the line it
-- is applied to, so that no intermediate line need be written.
record Step (xs : List W) : Set where
  constructor at
  field
    k n : ℕ
    ys  : List W
    e   : ⟪ take n (drop k xs) ⟫ ≈ ⟪ ys ⟫

next : ∀ {xs : List W} → Step xs → List W
next {xs} (at k n ys _) = take k xs ++ ys ++ drop (k + n) xs

infixr 4 _▸_
data Chain : List W → List W → Set where
  done : ∀ {xs : List W} → Chain xs xs
  _▸_  : ∀ {xs zs : List W} (s : Step xs) → Chain (next s) zs → Chain xs zs

run : ∀ {xs zs : List W} → Chain xs zs → ⟪ xs ⟫ ≈ ⟪ zs ⟫
run done                   = refl
run {xs} (at k n ys e ▸ c) = trans (step k n xs ys e) (run c)

------------------------------------------------------------------------
-- The numerals as indices

lit : Fin 8 → Fin N
lit = fin8 {m}

private
  tlit : ∀ (i : Fin 8) → toℕ (lit i) ≡ toℕ i
  tlit i = toℕ-inject≤ i _

  lit≢ : ∀ (i j : Fin 8) → toℕ i ≢ toℕ j → lit i ≢ lit j
  lit≢ i j ne h = ne (Eq.trans (Eq.sym (tlit i)) (Eq.trans (Eq.cong toℕ h) (tlit j)))

  -- Whether a numeral is none of a vector's, and whether a vector's
  -- numerals are distinct — decided, so that `tt` proves them.
  fresh : Fin 8 → ∀ {k : ℕ} → Vec (Fin 8) k → Bool
  fresh x []       = true
  fresh x (y ∷ ys) with toℕ y ≟ℕ toℕ x
  ... | yes _ = false
  ... | no  _ = fresh x ys

  nodup : ∀ {k : ℕ} → Vec (Fin 8) k → Bool
  nodup []       = true
  nodup (x ∷ xs) with fresh x xs
  ... | true  = nodup xs
  ... | false = false

  fresh-ok : ∀ (x : Fin 8) {k : ℕ} (ys : Vec (Fin 8) k) → T (fresh x ys) →
             All (λ y → y ≢ lit x) (Vec.map lit ys)
  fresh-ok x []       _ = []
  fresh-ok x (y ∷ ys) t with toℕ y ≟ℕ toℕ x
  ... | yes _ = ⊥-elim t
  ... | no ne = lit≢ y x ne ∷ fresh-ok x ys t

  nodup-ok : ∀ {k : ℕ} (v : Vec (Fin 8) k) → T (nodup v) → Distinct (Vec.map lit v)
  nodup-ok []       _ = []ᵈ
  nodup-ok (x ∷ xs) t with fresh x xs | fresh-ok x xs
  ... | true  | ok = ok tt ∷ᵈ nodup-ok xs t
  ... | false | _  = ⊥-elim t

------------------------------------------------------------------------
-- The letters of the chain

P : Fin 8 → Fin 8 → Fin 8 → Fin 8 → W
P a b c d = hh {₃₊ m} (lit a) (lit b) (lit c) (lit d)

Z : Fin 8 → Fin 8 → W
Z a b = zz {₃₊ m} (lit a) (lit b)

Y : Fin 8 → Fin 8 → Fin 8 → W
Y c a b = zx {₃₊ m} (lit c) (lit a) (lit b)

X : Fin 8 → Fin 8 → Fin 8 → Fin 8 → W
X a b c d = xx {₃₊ m} (lit a) (lit b) (lit c) (lit d)

-- The two sides of (80).
L80 R80 : List W
L80 = P ₀ ₁ ₀ ₂ ∷ P ₁ ₃ ₀ ₄ ∷ P ₁ ₅ ₀ ₁ ∷ Z ₁ ₀ ∷ P ₀ ₄ ₁ ₅ ∷ P ₀ ₂ ₁ ₃ ∷ []
R80 = P ₀ ₂ ₁ ₃ ∷ P ₀ ₄ ₁ ₅ ∷ Z ₁ ₀ ∷ P ₀ ₁ ₀ ₄ ∷ P ₁ ₅ ₀ ₂ ∷ P ₁ ₃ ₀ ₁ ∷ []

module _ (e65 : Eq65) where

  private
    -- A template on some numerals, and the normaliser on them with a
    -- frame pair of two others.
    module L {k : ℕ} (v : Vec (Fin 8) k) (nd : T (nodup v)) =
      At (lookup (Vec.map lit v)) (lookup-inj (nodup-ok v nd))

    module F {k : ℕ} (v : Vec (Fin 8) k) (e f : Fin 8) (nd : T (nodup v))
             (fe : T (fresh e v)) (ff : T (fresh f v)) (ef : toℕ e ≢ toℕ f) =
      Norm e65 (lookup (Vec.map lit v)) (lookup-inj (nodup-ok v nd)) (lit e) (lit f)
           (lit≢ e f ef) (allAt (fresh-ok e v fe)) (allAt (fresh-ok f v ff))

    d : ∀ (i j : Fin 8) → toℕ i ≢ toℕ j → lit i ≢ lit j
    d = lit≢

    off : ∀ (a b c e : Fin 8) → toℕ a ≢ toℕ c → toℕ a ≢ toℕ e →
          toℕ b ≢ toℕ c → toℕ b ≢ toℕ e → _
    off a b c e ac ae bc be = mkOff (d a c ac) (d a e ae) (d b c bc) (d b e be)

    ----------------------------------------------------------------------
    -- The segments

    s0 : ε ≈ Y ₆ ₂ ₃ • Z ₂ ₃ • Z ₂ ₃ • Y ₆ ₂ ₃
    s0 = A5-tmpl emp (⌜ ty ₂ ₀ ₁ ⌝ •ᵗ ⌜ tz ₀ ₁ ⌝ •ᵗ ⌜ tz ₀ ₁ ⌝ •ᵗ ⌜ ty ₂ ₀ ₁ ⌝) Eq.refl
      where open L (₂ ∷ ₃ ∷ ₆ ∷ []) tt

    s1 : Z ₂ ₃ • Y ₆ ₂ ₃ • P ₀ ₁ ₀ ₂ ≈ P ₀ ₁ ₀ ₃ • Y ₂ ₀ ₃ • Y ₆ ₂ ₃
    s1 = by-norm (⌞ hf (tz ₂ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟ •ᶠ ⌞ hp ₀ ₁ ₀ ₂ ⌟)
                 (⌞ hp ₀ ₁ ₀ ₃ ⌟ •ᶠ ⌞ hf (ty ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₆ ∷ []) ₄ ₅ tt tt tt (λ ())

    s2 : Y ₂ ₀ ₃ • Y ₆ ₂ ₃ • P ₁ ₃ ₀ ₄ ≈ P ₁ ₂ ₃ ₄ • X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃
    s2 = by-norm (⌞ hf (ty ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟ •ᶠ ⌞ hp ₁ ₃ ₀ ₄ ⌟)
                 (⌞ hp ₁ ₂ ₃ ₄ ⌟ •ᶠ ⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₄ ∷ ₆ ∷ []) ₅ ₇ tt tt tt (λ ())

    s3 : X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ • P ₁ ₅ ₀ ₁ ≈ P ₂ ₅ ₃ ₂ • X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃
    s3 = by-norm (⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟ •ᶠ ⌞ hp ₁ ₄ ₀ ₁ ⌟)
                 (⌞ hp ₂ ₄ ₃ ₂ ⌟ •ᶠ ⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₅ ∷ ₆ ∷ []) ₄ ₇ tt tt tt (λ ())

    s4 : X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ • Z ₁ ₀ ≈ Z ₂ ₃ • X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃
    s4 = A5-tmpl (⌜ tx ₁ ₂ ₀ ₃ ⌝ •ᵗ ⌜ ty ₄ ₂ ₃ ⌝ •ᵗ ⌜ tz ₁ ₀ ⌝)
                 (⌜ tz ₂ ₃ ⌝ •ᵗ ⌜ tx ₁ ₂ ₀ ₃ ⌝ •ᵗ ⌜ ty ₄ ₂ ₃ ⌝) Eq.refl
      where open L (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₆ ∷ []) tt

    -- The Hadamard-free word carries the pair across with matching
    -- signs; seven indices, so no frame, and none is needed.
    s5 : X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ • P ₀ ₄ ₁ ₅ ≈ P ₃ ₄ ₂ ₅ • X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃
    s5 = trans (sym assoc)
           (hh-pass e65 (inst tu) (inst tu′) (hf-inst tu) (hf-inst tu′) (inv-tmpl tu tu′ Eq.refl)
                    (lit ₃) (lit ₄) (lit ₂) (lit ₅) (lit ₀) (lit ₄) (lit ₁) (lit ₅)
                    (prm-at tu ₃) (prm-at tu ₄) (prm-at tu ₂) (prm-at tu ₅)
                    (Eq.trans (sgn-at tu ₃) (Eq.sym (sgn-at tu ₄)))
                    (Eq.trans (sgn-at tu ₂) (Eq.sym (sgn-at tu ₅)))
                    (d ₃ ₄ (λ ())) (d ₃ ₂ (λ ())) (d ₃ ₅ (λ ()))
                    (d ₄ ₂ (λ ())) (d ₄ ₅ (λ ())) (d ₂ ₅ (λ ())))
      where
      open L (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₄ ∷ ₅ ∷ ₆ ∷ []) tt

      tu tu′ : TW 7
      tu  = ⌜ tx ₁ ₂ ₀ ₃ ⌝ •ᵗ ⌜ ty ₆ ₂ ₃ ⌝
      tu′ = ⌜ ty ₆ ₂ ₃ ⌝ •ᵗ ⌜ tx ₁ ₂ ₀ ₃ ⌝

    s6 : X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ • P ₀ ₂ ₁ ₃ ≈ P ₀ ₃ ₁ ₂ • Z ₂ ₃ • Y ₆ ₂ ₃
    s6 = by-norm (⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟ •ᶠ ⌞ hp ₀ ₂ ₁ ₃ ⌟)
                 (⌞ hp ₀ ₃ ₁ ₂ ⌟ •ᶠ ⌞ hf (tz ₂ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₆ ∷ []) ₄ ₅ tt tt tt (λ ())

    s7 : ε ≈ P ₇ ₆ ₄ ₅ • P ₇ ₆ ₄ ₅
    s7 = sym (hh-invol e65 (lit ₇) (lit ₆) (lit ₄) (lit ₅) (d ₇ ₆ (λ ())) (d ₇ ₄ (λ ()))
                        (d ₇ ₅ (λ ())) (d ₆ ₄ (λ ())) (d ₆ ₅ (λ ())) (d ₄ ₅ (λ ())))

    -- (73) and (66) at literal indices.
    e73 : ∀ (a b c d′ e f g h : Fin 8) → toℕ a ≢ toℕ b → toℕ c ≢ toℕ d′ →
          toℕ e ≢ toℕ f → toℕ g ≢ toℕ h →
          toℕ c ≢ toℕ e → toℕ c ≢ toℕ f → toℕ d′ ≢ toℕ e → toℕ d′ ≢ toℕ f →
          P a b c d′ • P e f g h ≈ P a b e f • P c d′ g h
    e73 a b c d′ e f g h ab cd ef gh ce cf de df =
      eq73 e65 (lit a) (lit b) (lit c) (lit d′) (lit e) (lit f) (lit g) (lit h)
           (d a b ab) (d c d′ cd) (d e f ef) (d g h gh)
           (mkOff (d c e ce) (d c f cf) (d d′ e de) (d d′ f df))

    e66 : ∀ (a b c d′ : Fin 8) → toℕ a ≢ toℕ b → toℕ a ≢ toℕ c → toℕ a ≢ toℕ d′ →
          toℕ b ≢ toℕ c → toℕ b ≢ toℕ d′ → toℕ c ≢ toℕ d′ → P a b c d′ ≈ P c d′ a b
    e66 a b c d′ ab ac ad bc bd cd =
      eq66 e65 (lit a) (lit b) (lit c) (lit d′) (d a b ab) (d a c ac) (d a d′ ad)
           (d b c bc) (d b d′ bd) (d c d′ cd)

    s8 : P ₂ ₅ ₃ ₂ • P ₇ ₆ ₄ ₅ ≈ P ₂ ₅ ₇ ₆ • P ₃ ₂ ₄ ₅
    s8 = e73 ₂ ₅ ₃ ₂ ₇ ₆ ₄ ₅ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s9 : P ₂ ₅ ₇ ₆ ≈ P ₇ ₆ ₂ ₅
    s9 = e66 ₂ ₅ ₇ ₆ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s10 : P ₁ ₂ ₃ ₄ • P ₇ ₆ ₂ ₅ ≈ P ₁ ₂ ₇ ₆ • P ₃ ₄ ₂ ₅
    s10 = e73 ₁ ₂ ₃ ₄ ₇ ₆ ₂ ₅ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s11 : P ₁ ₂ ₇ ₆ ≈ P ₇ ₆ ₁ ₂
    s11 = e66 ₁ ₂ ₇ ₆ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s12 : P ₀ ₁ ₀ ₃ • P ₇ ₆ ₁ ₂ ≈ P ₀ ₁ ₇ ₆ • P ₀ ₃ ₁ ₂
    s12 = e73 ₀ ₁ ₀ ₃ ₇ ₆ ₁ ₂ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    -- (46), its numerals as indices.
    r46ₗ r46ᵣ : List W
    r46ₗ = P ₀ ₁ ₇ ₆ ∷ P ₀ ₃ ₁ ₂ ∷ P ₃ ₄ ₂ ₅ ∷ P ₃ ₂ ₄ ₅ ∷ P ₇ ₆ ₄ ₅ ∷ Z ₂ ₃ ∷
           P ₃ ₄ ₂ ₅ ∷ P ₀ ₃ ₁ ₂ ∷ []
    r46ᵣ = P ₀ ₃ ₁ ₂ ∷ P ₃ ₄ ₂ ₅ ∷ Z ₂ ₃ ∷ P ₇ ₆ ₄ ₅ ∷ P ₃ ₂ ₄ ₅ ∷ P ₃ ₄ ₂ ₅ ∷
           P ₀ ₃ ₁ ₂ ∷ P ₀ ₁ ₇ ₆ ∷ []

    hℕ : ∀ (i j k l : Fin 8) → hhℕ {₃₊ m} (toℕ i) (toℕ j) (toℕ k) (toℕ l) ≡ P i j k l
    hℕ i j k l =
      Eq.trans (Eq.cong₂ (λ p q → hhℕ {₃₊ m} p q (toℕ k) (toℕ l)) (Eq.sym (tlit i)) (Eq.sym (tlit j)))
      (Eq.trans (Eq.cong₂ (λ p q → hhℕ {₃₊ m} (toℕ (lit i)) (toℕ (lit j)) p q)
                          (Eq.sym (tlit k)) (Eq.sym (tlit l)))
                (hhℕ-hh (lit i) (lit j) (lit k) (lit l)))

    zℕ : ∀ (i j : Fin 8) → zzℕ {₃₊ m} (toℕ i) (toℕ j) ≡ Z i j
    zℕ i j = Eq.trans (Eq.cong₂ (zzℕ {₃₊ m}) (Eq.sym (tlit i)) (Eq.sym (tlit j)))
                      (zzℕ-zz (lit i) (lit j))

    s13 : ⟪ r46ₗ ⟫ ≈ ⟪ r46ᵣ ⟫
    s13 = Eq.subst₂ (λ A B → A ≈ B)
            (Eq.cong₂ _•_ (hℕ ₀ ₁ ₇ ₆) (Eq.cong₂ _•_ (hℕ ₀ ₃ ₁ ₂) (Eq.cong₂ _•_ (hℕ ₃ ₄ ₂ ₅)
              (Eq.cong₂ _•_ (hℕ ₃ ₂ ₄ ₅) (Eq.cong₂ _•_ (hℕ ₇ ₆ ₄ ₅) (Eq.cong₂ _•_ (zℕ ₂ ₃)
              (Eq.cong₂ _•_ (hℕ ₃ ₄ ₂ ₅) (hℕ ₀ ₃ ₁ ₂))))))))
            (Eq.cong₂ _•_ (hℕ ₀ ₃ ₁ ₂) (Eq.cong₂ _•_ (hℕ ₃ ₄ ₂ ₅) (Eq.cong₂ _•_ (zℕ ₂ ₃)
              (Eq.cong₂ _•_ (hℕ ₇ ₆ ₄ ₅) (Eq.cong₂ _•_ (hℕ ₃ ₂ ₄ ₅) (Eq.cong₂ _•_ (hℕ ₃ ₄ ₂ ₅)
              (Eq.cong₂ _•_ (hℕ ₀ ₃ ₁ ₂) (hℕ ₀ ₁ ₇ ₆))))))))
            (axiom r46)

    s14 : P ₇ ₆ ₄ ₅ • P ₃ ₂ ₄ ₅ ≈ P ₃ ₂ ₇ ₆
    s14 = trans (e73 ₇ ₆ ₄ ₅ ₃ ₂ ₄ ₅ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
          (trans (back (P ₇ ₆ ₃ ₂) (eq70 e65 (lit ₄) (lit ₅) (d ₄ ₅ (λ ()))))
          (trans right-unit (e66 ₇ ₆ ₃ ₂ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))))

    s15 : P ₃ ₂ ₇ ₆ • P ₃ ₄ ₂ ₅ ≈ P ₃ ₂ ₃ ₄ • P ₇ ₆ ₂ ₅
    s15 = e73 ₃ ₂ ₇ ₆ ₃ ₄ ₂ ₅ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s16 : P ₇ ₆ ₂ ₅ ≈ P ₂ ₅ ₇ ₆
    s16 = e66 ₇ ₆ ₂ ₅ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s17 : P ₂ ₅ ₇ ₆ • P ₀ ₃ ₁ ₂ ≈ P ₂ ₅ ₀ ₃ • P ₇ ₆ ₁ ₂
    s17 = e73 ₂ ₅ ₇ ₆ ₀ ₃ ₁ ₂ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

    s18 : P ₇ ₆ ₁ ₂ • P ₀ ₁ ₇ ₆ ≈ P ₁ ₂ ₇ ₆ • P ₇ ₆ ₀ ₁
    s18 = cong (e66 ₇ ₆ ₁ ₂ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
               (e66 ₀ ₁ ₇ ₆ (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))

    s19 : P ₁ ₂ ₇ ₆ • P ₇ ₆ ₀ ₁ ≈ P ₁ ₂ ₀ ₁
    s19 = fuse e65 (lit ₁) (lit ₂) (lit ₇) (lit ₆) (lit ₀) (lit ₁)
               (d ₁ ₂ (λ ())) (d ₇ ₆ (λ ())) (d ₀ ₁ (λ ()))

    s20 : P ₁ ₂ ₀ ₁ • Z ₂ ₃ • Y ₆ ₂ ₃ ≈ Y ₃ ₁ ₂ • Y ₆ ₂ ₃ • P ₁ ₃ ₀ ₁
    s20 = by-norm (⌞ hp ₁ ₂ ₀ ₁ ⌟ •ᶠ ⌞ hf (tz ₂ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟)
                  (⌞ hf (ty ₃ ₁ ₂) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟ •ᶠ ⌞ hp ₁ ₃ ₀ ₁ ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₆ ∷ []) ₄ ₅ tt tt tt (λ ())

    s21 : P ₂ ₅ ₀ ₃ • Y ₃ ₁ ₂ • Y ₆ ₂ ₃ ≈ X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ • P ₁ ₅ ₀ ₂
    s21 = by-norm (⌞ hp ₂ ₄ ₀ ₃ ⌟ •ᶠ ⌞ hf (ty ₃ ₁ ₂) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟)
                  (⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟ •ᶠ ⌞ hp ₁ ₄ ₀ ₂ ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₅ ∷ ₆ ∷ []) ₄ ₇ tt tt tt (λ ())

    s22 : P ₃ ₂ ₃ ₄ • X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ ≈ X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ • P ₀ ₁ ₀ ₄
    s22 = by-norm (⌞ hp ₃ ₂ ₃ ₄ ⌟ •ᶠ ⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟)
                  (⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₅ ₂ ₃) ⌟ •ᶠ ⌞ hp ₀ ₁ ₀ ₄ ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₄ ∷ ₆ ∷ []) ₅ ₇ tt tt tt (λ ())

    s25 : P ₀ ₃ ₁ ₂ • X ₁ ₂ ₀ ₃ • Y ₆ ₂ ₃ ≈ Z ₂ ₃ • Y ₆ ₂ ₃ • P ₀ ₂ ₁ ₃
    s25 = by-norm (⌞ hp ₀ ₃ ₁ ₂ ⌟ •ᶠ ⌞ hf (tx ₁ ₂ ₀ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟)
                  (⌞ hf (tz ₂ ₃) ⌟ •ᶠ ⌞ hf (ty ₄ ₂ ₃) ⌟ •ᶠ ⌞ hp ₀ ₂ ₁ ₃ ⌟) Eq.refl Eq.refl
      where open F (₀ ∷ ₁ ∷ ₂ ∷ ₃ ∷ ₆ ∷ []) ₄ ₅ tt tt tt (λ ())

  ----------------------------------------------------------------------
  -- The chain

  eq80 : ⟪ L80 ⟫ ≈ ⟪ R80 ⟫
  eq80 = run {L80} {R80}
    ( at 0 0 (Y ₆ ₂ ₃ ∷ Z ₂ ₃ ∷ Z ₂ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s0
    ▸ at 2 3 (P ₀ ₁ ₀ ₃ ∷ Y ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s1
    ▸ at 3 3 (P ₁ ₂ ₃ ₄ ∷ X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s2
    ▸ at 4 3 (P ₂ ₅ ₃ ₂ ∷ X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s3
    ▸ at 5 3 (Z ₂ ₃ ∷ X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s4
    ▸ at 6 3 (P ₃ ₄ ₂ ₅ ∷ X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s5
    ▸ at 7 3 (P ₀ ₃ ₁ ₂ ∷ Z ₂ ₃ ∷ Y ₆ ₂ ₃ ∷ []) s6
    ▸ at 5 0 (P ₇ ₆ ₄ ₅ ∷ P ₇ ₆ ₄ ₅ ∷ []) s7
    ▸ at 4 2 (P ₂ ₅ ₇ ₆ ∷ P ₃ ₂ ₄ ₅ ∷ []) s8
    ▸ at 4 1 (P ₇ ₆ ₂ ₅ ∷ []) s9
    ▸ at 3 2 (P ₁ ₂ ₇ ₆ ∷ P ₃ ₄ ₂ ₅ ∷ []) s10
    ▸ at 3 1 (P ₇ ₆ ₁ ₂ ∷ []) s11
    ▸ at 2 2 (P ₀ ₁ ₇ ₆ ∷ P ₀ ₃ ₁ ₂ ∷ []) s12
    ▸ at 2 8 r46ᵣ s13
    ▸ at 5 2 (P ₃ ₂ ₇ ₆ ∷ []) s14
    ▸ at 5 2 (P ₃ ₂ ₃ ₄ ∷ P ₇ ₆ ₂ ₅ ∷ []) s15
    ▸ at 6 1 (P ₂ ₅ ₇ ₆ ∷ []) s16
    ▸ at 6 2 (P ₂ ₅ ₀ ₃ ∷ P ₇ ₆ ₁ ₂ ∷ []) s17
    ▸ at 7 2 (P ₁ ₂ ₇ ₆ ∷ P ₇ ₆ ₀ ₁ ∷ []) s18
    ▸ at 7 2 (P ₁ ₂ ₀ ₁ ∷ []) s19
    ▸ at 7 3 (Y ₃ ₁ ₂ ∷ Y ₆ ₂ ₃ ∷ P ₁ ₃ ₀ ₁ ∷ []) s20
    ▸ at 6 3 (X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ P ₁ ₅ ₀ ₂ ∷ []) s21
    ▸ at 5 3 (X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ P ₀ ₁ ₀ ₄ ∷ []) s22
    ▸ at 4 3 (X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ Z ₁ ₀ ∷ []) (sym s4)
    ▸ at 3 3 (X ₁ ₂ ₀ ₃ ∷ Y ₆ ₂ ₃ ∷ P ₀ ₄ ₁ ₅ ∷ []) (sym s5)
    ▸ at 2 3 (Z ₂ ₃ ∷ Y ₆ ₂ ₃ ∷ P ₀ ₂ ₁ ₃ ∷ []) s25
    ▸ at 0 4 [] (sym s0)
    ▸ done )
