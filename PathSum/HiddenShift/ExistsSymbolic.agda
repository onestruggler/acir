------------------------------------------------------------------------
-- Presentations of groups
--
-- The rewrite rules find |s⟩|s⟩: a complete reduction of the circuit
-- of figure 3(b), for every size
--
-- Section 5.2 of Amy's "Towards Large-scale Functional Verification of
-- Universal Quantum Circuits" (QPL 2018) reports that the calculus
-- "finds the correct output |s⟩ or |s⟩|s⟩ even without providing the
-- specification".  PathSum.HiddenShift.Reduces proves that every
-- reduction by figure 2's rules which removes all path variables of
-- figure 3(b)'s path-sum -- the symbolic-shift circuit SSᶜ gs with its
-- data register read as 0, set0ᶜ (dataMask n) ⟦ SSᶜ gs ⟧ -- ends at
-- |x_d, x_s⟩ ↦ |x_s, x_s⟩ (symbolic-reduces).  This module proves that
-- one exists, for every m and every list of monomials gs
-- (symbolic-exists), so that the calculus does find |s⟩|s⟩ on the
-- circuit's own path-sum, definition 2.9's (symbolic-finds) -- as
-- PathSum.HiddenShift.Exists finds |s⟩ on the composite of
-- PathSum.HiddenShift.
--
-- The reduction is PathSum.HiddenShift.Exists's three passes
-- (PathSum.HiddenShift.MainPasses), run on the labelled machine of
-- PathSum.HiddenShift.Engine.  What is new is the path-sum it runs on:
--
-- * Its values (tracks₀).  Along a path the circuit's phase and outputs
--   are read by PathSum.CRK.Trace, layer by layer
--   (PathSum.HiddenShift.Runs): the Hadamard layers put the path's
--   bits y₁, y₂, y₃ on the data register, the CNOTs from the shift
--   register add x_s to it and take it off again, and the oracles read
--   it; the phase is ½ times f(y₁ ⊕ x_s) + y₁·y₂ + f̃(y₂) + y₂·y₃ and
--   the outputs are y₃ and x_s (runs-SS).  Regrouped by block
--   (Layout.blocks-par) this is Blocks' Fblk with the shift halves
--   s_L, s_R the input's -- the phase depends on the input, which is
--   why the machine and PathSum.HiddenShift.TrackX track values at
--   every input.
-- * Its variables' labels.  ⟦ C ⟧ numbers a Hadamard's variable by the
--   Hadamards after it, so the variables are the third layer's, the
--   second's, the first's, each layer's wire w at n-1-w (posR, labR).
--   The quotients of the second and third passes are the input
--   variables s_L,i and s_R,i, and the first pass's is a_i ⊕ s_L,i.
--
-- By construction the chain has 6m = 3n steps, 3m of each of [HH] and
-- [Elim], taking the 3n path variables and the normalisation 3n to
-- none; the step count is not stated.  The chain is given, not
-- searched for.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Data.Nat.Base using (ℕ)

module PathSum.HiddenShift.ExistsSymbolic (M₀ : ℕ) where

open import Data.Bool.Base using (Bool; true; false; _xor_; if_then_else_)
open import Data.Bool.Properties using (xor-identityʳ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using
  (Fin; zero; suc; toℕ; opposite; splitAt; cast; _↑ˡ_; _↑ʳ_)
open import Data.Integer.Base using (+_; 0ℤ; _-_; _*_)
open import Data.Integer.Divisibility.Signed using (_∣_)
open import Data.Integer.Properties using (+-identityˡ)
open import Data.List.Base using (List; _++_)
open import Data.Nat.Base using (zero; suc) renaming (_+_ to _ℕ+_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Sum.Properties using (inj₁-injective)
open import Data.Unit.Base using (tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

import Data.Fin.Properties as Fin
import Data.Nat.Solver as ℕSolver

open import PathSum.Ancilla.Register M₀ using (mask; set0ᶜ; eval-set0ᶜ)
open import PathSum.Assign using ([_]ᶻ)
open import PathSum.Base using (PathSum; phase; out)
open import PathSum.CRK.Trace M₀ using
  (Stream; shift; trace; str; pathOf-str; eval-⟦⟧; outBit-⟦⟧; norm-++)
open import PathSum.Denotation M₀ using (Assign)
open import PathSum.HiddenShift.Blocks
open import PathSum.HiddenShift.Circuit M₀ using
  (fTerms; f̃Terms; oracleᶠ; oracleᵈ; sum-f; sum-f̃)
open import PathSum.HiddenShift.Engine M₀ using (qin)
open import PathSum.HiddenShift.Gates M₀ using
  (Term; sumᵇ; sumᵇ-resp; upper; norm-upper; oracle; norm-oracle)
open import PathSum.HiddenShift.Layers M₀ using (hadamards; norm-hadamards)
open import PathSum.HiddenShift.Layout using
  (sel-ˡ; sel-ʳ; split-inv; wl; wl-↑ˡ; wl-↑ʳ; wl-inv; hs-par; blocks-par)
open import PathSum.HiddenShift.Reduces M₀ using (symbolic-reduces)
open import PathSum.HiddenShift.Runs M₀ using
  (Runs; runs-φ; runs-v; Runs-++; Runs-cong; Runs-resp; Runs-upper;
   Runs-hadamards; Runs-oracle; Runs-cnots; hbits)
open import PathSum.HiddenShift.Symbolic M₀ using
  (SSᶜ; cnots; norm-cnots; norm-SSᶜ; dataMask; copy; ⧺-cong₂)
open import PathSum.HiddenShift.TrackX M₀ using (Tracksˣ)
open import PathSum.HiddenShift.Walsh using
  (0ᵃ; _⊕ᵃ_; _⧺_; ⧺-↑ˡ; ⧺-↑ʳ; ⧺-split; dot; dot-cong; dot-0ˡ; lhalf;
   rhalf; mm)
open import PathSum.Polynomial using (x[_]; μ; eval; _≈[_]_; 0ᴾ)
open import PathSum.Polynomial.Bind using (odd)

import PathSum.HiddenShift.MainPasses M₀ as MP

private
  M : ℕ
  M = suc (suc (suc M₀))

open import PathSum.CRK.Circuit M using
  (Circuit; norm; paths; paths≡norm; ⟦_⟧)
open import PathSum.Full M using (_⟶ᶠ*_; εᶠ)
open import PathSum.Order M using (pow)
open import PathSum.Reduction M using (½)

open ℕSolver.+-*-Solver using (solve; con; _:+_; _:=_)


------------------------------------------------------------------------
-- Small facts

private
  t≢f : true ≢ false
  t≢f ()

  xor-back : ∀ a b → (a xor b) xor b ≡ a
  xor-back false false = refl
  xor-back false true  = refl
  xor-back true  false = refl
  xor-back true  true  = refl

  _≟⊥_ : DecidableEquality ⊥
  () ≟⊥ _


------------------------------------------------------------------------
-- The reduction, for one list of monomials

module _ {m : ℕ} (gs : List (Term m)) where

  private
    n : ℕ
    n = m ℕ+ m

  -- The labels: the six blocks, and nothing else.

  L : Set
  L = Lbl m ⊎ ⊥

  -- The shift register, and its two halves.

  xsOf : Assign (n ℕ+ n) → Assign n
  xsOf x j = x (n ↑ʳ j)

  private
    sL sR : Assign (n ℕ+ n) → Fin m → Bool
    sL x = lhalf {m} (xsOf x)
    sR x = rhalf {m} (xsOf x)

  -- The values: the phase is ½ Fblk of the blocks, with the shift the
  -- input's; the outputs are e and h on the data register and the
  -- shift register itself; a removed block label keeps Blocks' value.

  Fs : Assign (n ℕ+ n) → (L → Bool) → Bool
  Fs x Z = Phase.Fblk (sumᵇ gs) (sumᵇ-resp gs) (sL x) (sR x)
                      (λ ℓ → Z (inj₁ ℓ))

  Gs : Fin (n ℕ+ n) → Assign (n ℕ+ n) → (L → Bool) → Bool
  Gs w x Z = ((λ i → Gblk i (λ ℓ → Z (inj₁ ℓ))) ⧺ xsOf x) w

  dflts : Assign (n ℕ+ n) → L → (L → Bool) → Bool
  dflts x (inj₁ ℓ) Z = Phase.dflt (sumᵇ gs) (sumᵇ-resp gs) (sL x) (sR x) ℓ
                                  (λ ℓ′ → Z (inj₁ ℓ′))
  dflts x (inj₂ ()) Z

  private
    G-main : ∀ x (Z Z′ : L → Bool) →
             (∀ i → Z (inj₁ (E₃ , i)) ≡ Z′ (inj₁ (E₃ , i))) →
             (∀ i → Z (inj₁ (H₃ , i)) ≡ Z′ (inj₁ (H₃ , i))) →
             ∀ w → Gs w x Z ≡ Gs w x Z′
    G-main x Z Z′ hE hH w = ⧺-cong₂ {k = n} {l = n}
      (Gblk-cong {Z = λ ℓ → Z (inj₁ ℓ)} {Z′ = λ ℓ → Z′ (inj₁ ℓ)} hE hH)
      (λ _ → refl) w

    -- The three passes, on any path-sum over K variables.

    module P {K : ℕ} (ξ₀ : PathSum (n ℕ+ n) K K) =
      MP.Passes _≟⊥_ (sumᵇ gs) (sumᵇ-resp gs) sL sR
        (λ i → qin (n ↑ʳ (i ↑ˡ m))) (λ i → qin (n ↑ʳ (m ↑ʳ i)))
        (λ _ _ _ _ → tt) (λ _ _ _ _ → tt)
        (λ _ _ _ → refl) (λ _ _ _ → refl)
        Fs Gs dflts (λ _ _ _ → refl) (λ _ _ _ → refl) G-main ξ₀

    -- Before the first pass every label is a path variable.

    Ret₀ : L → Bool
    Ret₀ (inj₁ ℓ) = Ret₁ (λ _ → false) ℓ
    Ret₀ (inj₂ ())

    -- A labelled path-sum with these values, whose normalisation is its
    -- number of path variables, reduces completely.

    complete′ : ∀ {k K} (ξ : PathSum (n ℕ+ n) k K) → k ≡ K →
                (lab : Fin K → L) (ρ : Assign (n ℕ+ n) → Assign K → L → Bool) →
                Tracksˣ ξ (λ x y → Fs x (ρ x y)) (λ w x y → Gs w x (ρ x y)) →
                (∀ x y p → ρ x y (lab p) ≡ y p) →
                (∀ x y ℓ → Ret₀ ℓ ≡ false → ρ x y ℓ ≡ dflts x ℓ (ρ x y)) →
                (∀ ℓ → Ret₀ ℓ ≡ true → Σ (Fin K) (λ p → lab p ≡ ℓ)) →
                (∀ p → Ret₀ (lab p) ≡ true) →
                (∀ p q → lab p ≡ lab q → p ≡ q) →
                Σ (PathSum (n ℕ+ n) 0 0) (λ ζ → ξ ⟶ᶠ* ζ)
    complete′ {K = K} ξ refl lab ρ tr rd df fd on ij =
      P.complete ξ
        (P.State-resp ξ Ret₀-M (P.stage K ξ lab ρ εᶠ tr rd df fd on ij))
      where
      Ret₀-M : ∀ ℓ → Ret₀ ℓ ≡ P.RetM₁ ξ (λ _ → false) ℓ
      Ret₀-M (inj₁ ℓ) = refl
      Ret₀-M (inj₂ ())

  ----------------------------------------------------------------------
  -- The circuit's layers along a path

  private
    A cn O Xc Dc : Circuit (n ℕ+ n)
    A  = upper n (hadamards n)
    cn = cnots {n} {n} (λ i → i)
    O  = upper n (oracleᶠ gs)
    Xc = cn ++ (O ++ cn)
    Dc = upper n (oracleᵈ gs)

    -- Each layer, on a data register Y and a shift register xs.

    L-A : ∀ s (Y xs : Assign n) →
          Runs A s (Y ⧺ xs) (dot Y (hbits n s)) (hbits n s ⧺ xs)
    L-A s Y xs = Runs-resp
      (dot-cong {u = λ i → (Y ⧺ xs) (i ↑ˡ n)} {u′ = Y}
                (λ i → ⧺-↑ˡ Y xs i) (λ _ → refl))
      (⧺-cong₂ {k = n} {l = n} (λ _ → refl) (λ j → ⧺-↑ʳ Y xs j))
      (Runs-upper n (hadamards n)
        (Runs-hadamards n s (λ i → (Y ⧺ xs) (i ↑ˡ n))))

    L-cn : ∀ s (Y xs : Assign n) → Runs cn s (Y ⧺ xs) false ((Y ⊕ᵃ xs) ⧺ xs)
    L-cn s Y xs = Runs-resp refl
      (⧺-cong₂ {k = n} {l = n}
               (λ i → cong₂ _xor_ (⧺-↑ˡ Y xs i) (⧺-↑ʳ Y xs i))
               (λ j → ⧺-↑ʳ Y xs j))
      (Runs-cnots {n} {n} (λ i → i) s (Y ⧺ xs))

    L-O : ∀ (ts : List (Term n)) s (Y xs : Assign n) →
          Runs (upper n (oracle ts)) s (Y ⧺ xs) (sumᵇ ts Y) (Y ⧺ xs)
    L-O ts s Y xs = Runs-resp
      (sumᵇ-resp ts (λ i → (Y ⧺ xs) (i ↑ˡ n)) Y (λ i → ⧺-↑ˡ Y xs i))
      (⧺-cong₂ {k = n} {l = n} (λ i → ⧺-↑ˡ Y xs i) (λ j → ⧺-↑ʳ Y xs j))
      (Runs-upper n (oracle ts) (Runs-oracle ts s (λ i → (Y ⧺ xs) (i ↑ˡ n))))

    L-X : ∀ s (Y xs : Assign n) →
          Runs Xc s (Y ⧺ xs)
               (false xor (sumᵇ (fTerms gs) (Y ⊕ᵃ xs) xor false))
               (((Y ⊕ᵃ xs) ⊕ᵃ xs) ⧺ xs)
    L-X s Y xs = Runs-++ cn (O ++ cn) (L-cn _ Y xs)
      (Runs-++ O cn (L-O (fTerms gs) _ (Y ⊕ᵃ xs) xs) (L-cn s (Y ⊕ᵃ xs) xs))

  -- The streams the layers read (the last Hadamard layer the path's
  -- own, each earlier layer the stream past the later layers'
  -- Hadamards), and the bits the Hadamard layers put on the data
  -- register.

  s₁ s₂ s₃ sA : Stream → Stream
  s₁ s = shift (norm A) s
  s₂ s = shift (norm Dc) (s₁ s)
  s₃ s = shift (norm A) (s₂ s)
  sA s = shift (norm Xc) (s₃ s)

  Y₁ Y₂ Y₃ : Stream → Assign (m ℕ+ m)
  Y₁ s = hbits n (sA s)
  Y₂ s = hbits n (s₂ s)
  Y₃ s = hbits n s

  -- The parity the circuit adds, layer by layer.

  β* : Stream → Assign (m ℕ+ m) → Bool
  β* s xs =
    (((dot (0ᵃ {n}) (Y₁ s) xor
       (false xor (sumᵇ (fTerms gs) (Y₁ s ⊕ᵃ xs) xor false))) xor
      dot ((Y₁ s ⊕ᵃ xs) ⊕ᵃ xs) (Y₂ s)) xor
     sumᵇ (f̃Terms gs) (Y₂ s)) xor
    dot (Y₂ s) (Y₃ s)

  -- Figure 3(b) along a path, from data |0⟩ and shift xs: phase ½ β*,
  -- wires y₃ and xs.

  runs-SS : ∀ (s : Stream) (xs : Assign n) →
            Runs (SSᶜ gs) s (0ᵃ {n} ⧺ xs) (β* s xs) (Y₃ s ⧺ xs)
  runs-SS s xs =
    Runs-++ (((A ++ Xc) ++ A) ++ Dc) A
      (Runs-++ ((A ++ Xc) ++ A) Dc
        (Runs-++ (A ++ Xc) A
          (Runs-++ A Xc (L-A (sA s) (0ᵃ {n}) xs) (L-X (s₃ s) (Y₁ s) xs))
          (L-A (s₂ s) ((Y₁ s ⊕ᵃ xs) ⊕ᵃ xs) xs))
        (L-O (f̃Terms gs) (s₁ s) (Y₂ s) xs))
      (L-A s (Y₂ s) xs)

  ----------------------------------------------------------------------
  -- The path variables, labelled

  -- ⟦ C ⟧'s variables in order: the third layer's, the second's, the
  -- first's, wire w of a layer at n-1-w.

  private
    Kr : ℕ
    Kr = n ℕ+ (n ℕ+ n)

    fE fC fA : Fin n → Lbl m
    fE q = wl E₃ H₃ (opposite q)
    fC q = wl C₂ D₂ (opposite q)
    fA q = wl A₁ B₁ (opposite q)

    f₂₁ : Fin (n ℕ+ n) → Lbl m
    f₂₁ p = [ fC , fA ]′ (splitAt n p)

  labR : Fin (n ℕ+ (n ℕ+ n)) → Lbl m
  labR p = [ fE , f₂₁ ]′ (splitAt n p)

  posR : Lbl m → Fin (n ℕ+ (n ℕ+ n))
  posR (A₁ , i) = n ↑ʳ (n ↑ʳ opposite (i ↑ˡ m))
  posR (B₁ , i) = n ↑ʳ (n ↑ʳ opposite (m ↑ʳ i))
  posR (C₂ , i) = n ↑ʳ (opposite (i ↑ˡ m) ↑ˡ n)
  posR (D₂ , i) = n ↑ʳ (opposite (m ↑ʳ i) ↑ˡ n)
  posR (E₃ , i) = opposite (i ↑ˡ m) ↑ˡ (n ℕ+ n)
  posR (H₃ , i) = opposite (m ↑ʳ i) ↑ˡ (n ℕ+ n)

  -- They are inverse.

  labR-posR : ∀ ℓ → labR (posR ℓ) ≡ ℓ
  labR-posR (A₁ , i) = trans (sel-ʳ n (n ℕ+ n) fE f₂₁ _)
    (trans (sel-ʳ n n fC fA _)
      (trans (cong (wl A₁ B₁) (Fin.opposite-involutive (i ↑ˡ m)))
             (wl-↑ˡ A₁ B₁ i)))
  labR-posR (B₁ , i) = trans (sel-ʳ n (n ℕ+ n) fE f₂₁ _)
    (trans (sel-ʳ n n fC fA _)
      (trans (cong (wl A₁ B₁) (Fin.opposite-involutive (m ↑ʳ i)))
             (wl-↑ʳ A₁ B₁ i)))
  labR-posR (C₂ , i) = trans (sel-ʳ n (n ℕ+ n) fE f₂₁ _)
    (trans (sel-ˡ n n fC fA _)
      (trans (cong (wl C₂ D₂) (Fin.opposite-involutive (i ↑ˡ m)))
             (wl-↑ˡ C₂ D₂ i)))
  labR-posR (D₂ , i) = trans (sel-ʳ n (n ℕ+ n) fE f₂₁ _)
    (trans (sel-ˡ n n fC fA _)
      (trans (cong (wl C₂ D₂) (Fin.opposite-involutive (m ↑ʳ i)))
             (wl-↑ʳ C₂ D₂ i)))
  labR-posR (E₃ , i) = trans (sel-ˡ n (n ℕ+ n) fE f₂₁ _)
    (trans (cong (wl E₃ H₃) (Fin.opposite-involutive (i ↑ˡ m)))
           (wl-↑ˡ E₃ H₃ i))
  labR-posR (H₃ , i) = trans (sel-ˡ n (n ℕ+ n) fE f₂₁ _)
    (trans (cong (wl E₃ H₃) (Fin.opposite-involutive (m ↑ʳ i)))
           (wl-↑ʳ E₃ H₃ i))

  posR-labR : ∀ p → posR (labR p) ≡ p
  posR-labR = split-inv n (n ℕ+ n) fE f₂₁ posR (λ p → p) layer₃ rest
    where
    layer₃ : ∀ q → posR (fE q) ≡ q ↑ˡ (n ℕ+ n)
    layer₃ q = trans
      (wl-inv E₃ H₃ posR (λ w → opposite w ↑ˡ (n ℕ+ n))
              (λ _ → refl) (λ _ → refl) (opposite q))
      (cong (_↑ˡ (n ℕ+ n)) (Fin.opposite-involutive q))

    layer₂ : ∀ q → posR (fC q) ≡ n ↑ʳ (q ↑ˡ n)
    layer₂ q = trans
      (wl-inv C₂ D₂ posR (λ w → n ↑ʳ (opposite w ↑ˡ n))
              (λ _ → refl) (λ _ → refl) (opposite q))
      (cong (λ t → n ↑ʳ (t ↑ˡ n)) (Fin.opposite-involutive q))

    layer₁ : ∀ q → posR (fA q) ≡ n ↑ʳ (n ↑ʳ q)
    layer₁ q = trans
      (wl-inv A₁ B₁ posR (λ w → n ↑ʳ (n ↑ʳ opposite w))
              (λ _ → refl) (λ _ → refl) (opposite q))
      (cong (λ t → n ↑ʳ (n ↑ʳ t)) (Fin.opposite-involutive q))

    rest : ∀ p → posR (f₂₁ p) ≡ n ↑ʳ p
    rest = split-inv n n fC fA posR (λ p → n ↑ʳ p) layer₂ layer₁

  ----------------------------------------------------------------------
  -- The circuit's path-sum, labelled

  private
    ξS : PathSum (n ℕ+ n) (norm (SSᶜ gs)) (paths (SSᶜ gs))
    ξS = set0ᶜ (dataMask n) ⟦ SSᶜ gs ⟧

    K : ℕ
    K = paths (SSᶜ gs)

    eK : K ≡ Kr
    eK = trans (paths≡norm (SSᶜ gs))
               (trans (norm-SSᶜ gs) (solve 1 (λ a →
                  (((a :+ con 0) :+ a) :+ con 0) :+ a := a :+ (a :+ a)) refl n))

    lab₀ : Fin K → L
    lab₀ p = inj₁ (labR (cast eK p))

    -- A present label is read at its position.

    ρ₀ : Assign (n ℕ+ n) → Assign K → L → Bool
    ρ₀ x y (inj₁ ℓ) = str y (toℕ (posR ℓ))
    ρ₀ x y (inj₂ ())

    reads₀ : ∀ x y p → ρ₀ x y (lab₀ p) ≡ y p
    reads₀ x y p = trans
      (cong (λ t → str y (toℕ t)) (posR-labR (cast eK p)))
      (trans (cong (str y) (Fin.toℕ-cast eK p)) (pathOf-str y p))

    dflts₀ : ∀ x y ℓ → Ret₀ ℓ ≡ false → ρ₀ x y ℓ ≡ dflts x ℓ (ρ₀ x y)
    dflts₀ x y (inj₁ ℓ) R = ⊥-elim (t≢f (trans (sym (Ret₁-all ℓ)) R))
    dflts₀ x y (inj₂ ()) R

    find₀ : ∀ ℓ → Ret₀ ℓ ≡ true → Σ (Fin K) (λ p → lab₀ p ≡ ℓ)
    find₀ (inj₁ ℓ) _ = cast (sym eK) (posR ℓ) ,
      cong inj₁ (trans (cong labR (Fin.cast-involutive eK (sym eK) (posR ℓ)))
                       (labR-posR ℓ))
    find₀ (inj₂ ()) _

    only₀ : ∀ p → Ret₀ (lab₀ p) ≡ true
    only₀ p = Ret₁-all (labR (cast eK p))

    inj₀ : ∀ p q → lab₀ p ≡ lab₀ q → p ≡ q
    inj₀ p q e = trans (sym (Fin.cast-involutive (sym eK) eK p))
      (trans (cong (cast (sym eK)) casts)
             (Fin.cast-involutive (sym eK) eK q))
      where
      casts : cast eK p ≡ cast eK q
      casts = trans (sym (posR-labR (cast eK p)))
        (trans (cong posR (inj₁-injective e)) (posR-labR (cast eK q)))

    -- The layers' bits are the labelled path's.

    nA : norm A ≡ n
    nA = trans (norm-upper n (hadamards n)) (norm-hadamards n)

    nC : norm cn ≡ 0
    nC = norm-cnots {n} {n} (λ i → i)

    nX : norm Xc ≡ 0
    nX = trans (norm-++ cn (O ++ cn))
      (cong₂ _ℕ+_ nC (trans (norm-++ O cn)
        (cong₂ _ℕ+_
          (trans (norm-upper n (oracleᶠ gs)) (norm-oracle (fTerms gs)))
                    nC)))

    nD : norm Dc ≡ 0
    nD = trans (norm-upper n (oracleᵈ gs)) (norm-oracle (f̃Terms gs))

    toℕ-↑ʳ↑ʳ : (q : Fin n) → toℕ (n ↑ʳ (n ↑ʳ q)) ≡ n ℕ+ (n ℕ+ toℕ q)
    toℕ-↑ʳ↑ʳ q = trans (Fin.toℕ-↑ʳ n (n ↑ʳ q)) (cong (n ℕ+_) (Fin.toℕ-↑ʳ n q))

    toℕ-↑ʳ↑ˡ : (q : Fin n) → toℕ (n ↑ʳ (q ↑ˡ n)) ≡ n ℕ+ toℕ q
    toℕ-↑ʳ↑ˡ q = trans (Fin.toℕ-↑ʳ n (q ↑ˡ n)) (cong (n ℕ+_) (Fin.toℕ-↑ˡ q n))

    pos₁ : ∀ s w → Y₁ s w ≡ s (toℕ (n ↑ʳ (n ↑ʳ opposite w)))
    pos₁ s w = cong s (trans
      (cong₂ (λ a b → (((toℕ (opposite w) ℕ+ a) ℕ+ b) ℕ+ norm Dc) ℕ+ b) nX nA)
      (trans (cong (λ d → (((toℕ (opposite w) ℕ+ 0) ℕ+ n) ℕ+ d) ℕ+ n) nD)
        (trans (solve 2 (λ t a → (((t :+ con 0) :+ a) :+ con 0) :+ a :=
                                 a :+ (a :+ t)) refl (toℕ (opposite w)) n)
               (sym (toℕ-↑ʳ↑ʳ (opposite w))))))

    pos₂ : ∀ s w → Y₂ s w ≡ s (toℕ (n ↑ʳ (opposite w ↑ˡ n)))
    pos₂ s w = cong s (trans
      (cong₂ (λ d a → (toℕ (opposite w) ℕ+ d) ℕ+ a) nD nA)
      (trans (solve 2 (λ t a → (t :+ con 0) :+ a := a :+ t) refl
                      (toℕ (opposite w)) n)
             (sym (toℕ-↑ʳ↑ˡ (opposite w)))))

    pos₃ : ∀ s w → Y₃ s w ≡ s (toℕ (opposite w ↑ˡ (n ℕ+ n)))
    pos₃ s w = cong s (sym (Fin.toℕ-↑ˡ (opposite w) (n ℕ+ n)))

    -- The data register starts at 0, the shift register at the input.

    prepared : ∀ x w → mask (dataMask n) x w ≡ (0ᵃ {n} ⧺ xsOf x) w
    prepared x w = trans (sym (⧺-split n n (mask (dataMask n) x) w))
      (⧺-cong₂ {k = n} {l = n} left right w)
      where
      left : ∀ i → mask (dataMask n) x (i ↑ˡ n) ≡ 0ᵃ {n} i
      left i = cong (λ b → if b then false else x (i ↑ˡ n))
                    (⧺-↑ˡ (λ (_ : Fin n) → true) (λ (_ : Fin n) → false) i)

      right : ∀ j → mask (dataMask n) x (n ↑ʳ j) ≡ xsOf x j
      right j = cong (λ b → if b then false else x (n ↑ʳ j))
                     (⧺-↑ʳ (λ (_ : Fin n) → true) (λ (_ : Fin n) → false) j)

    -- The parity is Fblk of the labelled path.

    βF : ∀ x y → β* (str y) (xsOf x) ≡ Fs x (ρ₀ x y)
    βF x y = trans simplify
      (blocks-par (sumᵇ gs) (sumᵇ-resp gs) xs (Y₁ s) (Y₂ s) (Y₃ s)
                  (λ ℓ → ρ₀ x y (inj₁ ℓ))
                  (λ i → pos₁ s (i ↑ˡ m)) (λ i → pos₁ s (m ↑ʳ i))
                  (λ i → pos₂ s (i ↑ˡ m)) (λ i → pos₂ s (m ↑ʳ i))
                  (λ i → pos₃ s (i ↑ˡ m)) (λ i → pos₃ s (m ↑ʳ i)))
      where
      s : Stream
      s = str y

      xs : Assign n
      xs = xsOf x

      S : Bool
      S = sumᵇ (fTerms gs) (Y₁ s ⊕ᵃ xs)

      first : dot (0ᵃ {n}) (Y₁ s) xor (false xor (S xor false)) ≡
              mm (sumᵇ gs) (Y₁ s ⊕ᵃ xs)
      first = trans (cong (_xor (false xor (S xor false))) (dot-0ˡ (Y₁ s)))
                    (trans (xor-identityʳ S) (sum-f gs (Y₁ s ⊕ᵃ xs)))

      simplify : β* s xs ≡ hs-par (sumᵇ gs) xs (Y₁ s) (Y₂ s) (Y₃ s)
      simplify = cong₂ _xor_
        (cong₂ _xor_
          (cong₂ _xor_ first
            (dot-cong (λ i → xor-back (Y₁ s i) (xs i)) (λ _ → refl)))
          (sum-f̃ gs (Y₂ s)))
        refl

    -- The outputs: y₃ on the data register, the shift on its own.

    Y₃-Gblk : ∀ x y i → Y₃ (str y) i ≡ Gblk i (λ ℓ → ρ₀ x y (inj₁ ℓ))
    Y₃-Gblk x y i = sym (split-inv m m
      (λ j → ρ₀ x y (inj₁ (E₃ , j))) (λ j → ρ₀ x y (inj₁ (H₃ , j)))
      (λ b → b) (Y₃ (str y))
      (λ j → sym (pos₃ (str y) (j ↑ˡ m))) (λ j → sym (pos₃ (str y) (m ↑ʳ j)))
      i)

    tracks₀ : Tracksˣ ξS (λ x y → Fs x (ρ₀ x y)) (λ w x y → Gs w x (ρ₀ x y))
    tracks₀ = record { phase-atˣ = ph ; out-atˣ = ob }
      where
      R : ∀ x y → Runs (SSᶜ gs) (str y) (mask (dataMask n) x)
                       (β* (str y) (xsOf x)) (Y₃ (str y) ⧺ xsOf x)
      R x y = Runs-cong (prepared x) (runs-SS (str y) (xsOf x))

      ph : ∀ x y → pow M ∣ (eval (phase ξS) x y - ½ * [ Fs x (ρ₀ x y) ]ᶻ)
      ph x y = subst (pow M ∣_)
        (cong₂ _-_ (sym evalEq)
               (trans (+-identityˡ _) (cong (λ b → ½ * [ b ]ᶻ) (βF x y))))
        (runs-φ (R x y) 0ℤ)
        where
        evalEq : eval (phase ξS) x y ≡
                 proj₁ (trace (SSᶜ gs) (str y) (0ℤ , mask (dataMask n) x))
        evalEq = trans (eval-set0ᶜ (dataMask n) (phase ⟦ SSᶜ gs ⟧) x y)
                       (eval-⟦⟧ (SSᶜ gs) (mask (dataMask n) x) y)

      ob : ∀ w x y → odd (eval (out ξS w) x y) ≡ Gs w x (ρ₀ x y)
      ob w x y = trans
        (cong odd (eval-set0ᶜ (dataMask n) (out ⟦ SSᶜ gs ⟧ w) x y))
        (trans (outBit-⟦⟧ (SSᶜ gs) (mask (dataMask n) x) y w)
          (trans (runs-v (R x y) 0ℤ w)
                 (⧺-cong₂ {k = n} {l = n} (Y₃-Gblk x y) (λ _ → refl) w)))

  ----------------------------------------------------------------------
  -- The theorems

  -- Figure 3(b)'s path-sum, with the data register read as 0, reduces
  -- by figure 2's rules to one with no path variables ...

  symbolic-exists :
    Σ (PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) 0 0) (λ ζ →
      set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧ ⟶ᶠ* ζ)
  symbolic-exists = complete′ ξS (sym (paths≡norm (SSᶜ gs))) lab₀ ρ₀ tracks₀
                              reads₀ dflts₀ find₀ only₀ inj₀

  -- ... and that one is |x_d, x_s⟩ ↦ |x_s, x_s⟩, coefficient by
  -- coefficient: the calculus finds |s⟩|s⟩ with the shift symbolic.

  symbolic-finds :
    Σ (PathSum ((m ℕ+ m) ℕ+ (m ℕ+ m)) 0 0) (λ ζ →
      (set0ᶜ (dataMask (m ℕ+ m)) ⟦ SSᶜ gs ⟧ ⟶ᶠ* ζ) ×
      (∀ w → out ζ w ≈[ + 2 ] μ x[ copy (m ℕ+ m) w ]) ×
      (phase ζ ≈[ pow M ] 0ᴾ))
  symbolic-finds =
    proj₁ symbolic-exists , proj₂ symbolic-exists ,
    proj₂ (symbolic-reduces gs (proj₂ symbolic-exists))
