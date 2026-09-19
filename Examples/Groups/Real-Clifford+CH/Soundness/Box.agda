------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantics of the multi-controlled box, and soundness of the
-- equation schema (19)
--
-- Clément's Definition 2.4 builds the k-controlled "dashed box" Λ□ k
-- out of controlled-H and swap gates by recursion on k; his Proposition
-- 3.1 says that Equation (19), which asserts that the (n − 1)-
-- controlled box commutes with Z on its extra qubit, is sound "by a
-- straightforward induction".  The induction is this module: it
-- proves that Λ□ k denotes what the paper says it denotes, the
-- diagonal operator
--
--     Λ□ k  ↦  (1/√2)^ℓ · diag (x ↦ −1 if wires 1 … k are all set, else 1),
--
-- with ℓ its number of letters and wire 0 idle.  Equation (19) follows,
-- since diagonal operators commute.
--
-- The recursive step is where the work is.  The k + 3 controlled box is
-- CCZX ∘ Λ□′ ∘ CCXZ ∘ Λ□′, with Λ□′ the (k + 2)-controlled box shifted
-- up and conjugated by the transposition of wires 0 and 2.  The
-- induction hypothesis gives Λ□′ as a diagonal operator controlled by
-- wire 0 and the top wires; CCZX and CCXZ act on the bottom three
-- wires only.  Writing all four factors as operators on the bottom
-- three wires CONTROLLED by the top ones (Operators.ctrl), the mixed
-- product law ctrl-⊙ reduces the whole product to two identities of
-- 8 × 8 matrices, checked by `refl` in BoxMatrices.
--
-- The operator reading ⟦_⟧ₒ is abstract (see Interpretation), so the
-- product structure of the box is opened with its unfolding lemmas,
-- and the padded three-wire words are identified with their
-- polymorphic spellings by the checker comparing WORDS.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.Soundness.Box where

open import Data.Bool using (Bool ; true ; false ; _∧_ ; if_then_else_)
open import Data.Bool.Properties using (∧-identityʳ ; ∧-zeroʳ)
open import Data.Nat using (ℕ) renaming (_+_ to _+ℕ_)
open import Data.Product using (_,_)
open import Data.Vec using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

import Data.Nat.Properties as NP

open import Notations using (₀ ; ₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation
open import Examples.Groups.Real-Clifford+CH.Soundness.Operators
open import Examples.Groups.Real-Clifford+CH.Soundness.BoxMatrices

private
  variable
    k n : ℕ

------------------------------------------------------------------------
-- Preliminaries

private
  -- Reading a stored identity as one about operators at width k.
  by-trie : (w : Circuit k) (c : 𝔽) (f : Bits k → 𝔽) →
            ⟦ w ⟧M ≡ scaleM c (matOf (diag f)) → ⟦ w ⟧ₒ ≐ (c · diag f)
  by-trie w c f eq =
    ≐-trans (⟦⟧-ix w)
      (≐-trans (ix-≡ eq)
        (≐-trans (ix-scaleM c (matOf (diag f))) (·-cong Eq.refl (ix-matOf (diag f)))))

  emb-≡ : {M N : Mat 3} → M ≡ N → emb {3} {n} M ≐ emb N
  emb-≡ {M = M} Eq.refl = ≐-refl (emb M)

  sgn-∧ : ∀ (a t : Bool) → sgn (a ∧ t) ≡ (if t then sgn a else 1#)
  sgn-∧ a true  = Eq.cong sgn (∧-identityʳ a)
  sgn-∧ a false = Eq.cong sgn (∧-zeroʳ a)

  sgn-∧∧ : ∀ (b c t : Bool) → (if t then sgn (b ∧ c) else 1#) ≡ sgn (b ∧ (c ∧ t))
  sgn-∧∧ b c true  = Eq.cong (λ □ → sgn (b ∧ □)) (Eq.sym (∧-identityʳ c))
  sgn-∧∧ b c false =
    Eq.sym (Eq.cong sgn (Eq.trans (Eq.cong (b ∧_) (∧-zeroʳ c)) (∧-zeroʳ b)))

  open Solver

------------------------------------------------------------------------
-- The pieces of the recursive step, at k + 3 controls
--
-- Widths: the box lives on ₄₊ k wires, the smaller box on ₃₊ k.

private
  -- The scalars of the smaller box and of the conjugated shifted box
  -- (those of the transposition and of the two controlled gates, cτ
  -- and cC, come with their matrices).
  c₂ cT : (k : ℕ) → 𝔽
  c₂ k = √2^ len (Λ□ (₂₊ k))
  cT k = √2^ len (τ₀₂-conj (Λ□ (₂₊ k) ↑))

  -- The phase of the conjugated, shifted box: wire 0 and the wires
  -- above 2 are its controls.
  g′ : Bits (₄₊ k) → 𝔽
  g′ (a ∷ _ ∷ _ ∷ u) = sgn (a ∧ allT u)

  -- The operators.
  P D₂ D′ A A′ : (k : ℕ) → Op (₄₊ k)
  P  k = permOp
  D₂ k = diag (tl (phase (₂₊ k)))
  D′ k = diag g′
  A  k = emb {3} {₁₊ k} Cm
  A′ k = emb {3} {₁₊ k} C′m

  -- The two controlled gates and the transposition, as operators: the
  -- polymorphic word at width k + 4 is the closed word padded, and
  -- localise reads the padded word as its stored matrix.
  A-emb : (k : ℕ) → ⟦ CCZX {₁₊ k} ⟧ₒ ≐ A k
  A-emb k = ≐-trans (localise {3} {₁₊ k} CCZX₀) (emb-≡ Cm-def)

  A′-emb : (k : ℕ) → ⟦ CCXZ {₁₊ k} ⟧ₒ ≐ A′ k
  A′-emb k = ≐-trans (localise {3} {₁₊ k} CCXZ₀) (emb-≡ C′m-def)

  τ-op : (k : ℕ) → ⟦ τ₀₂ {₁₊ k} ⟧ₒ ≐ (cτ · P k)
  τ-op k =
    ≐-trans (localise {3} {₁₊ k} τ₀₂₀)
      (≐-trans (emb-≡ τ-perm)
        (≐-trans (≐-sym (·-emb cτ permM)) (·-cong Eq.refl emb-perm)))

  -- The shifted smaller box.
  shift : (k : ℕ) → ⟦ Λ□ (₂₊ k) ⟧ₒ ≐ (c₂ k · diag (phase (₂₊ k))) →
          ⟦ Λ□ (₂₊ k) ↑ ⟧ₒ ≐ (c₂ k · D₂ k)
  shift k ih = ≐-trans (up-word (Λ□ (₂₊ k)))
                 (≐-trans (up-cong ih)
                   (≐-trans (up-· (c₂ k) (diag (phase (₂₊ k))))
                            (·-cong Eq.refl (up-diag (phase (₂₊ k))))))

  scalarT : (k : ℕ) → cτ * (c₂ k * cτ) ≡ cT k
  scalarT k = begin
    cτ * (√2^ len (Λ□ (₂₊ k)) * cτ)
      ≡⟨ Eq.cong (λ □ → cτ * (√2^ □ * cτ)) (Eq.sym (len-↑ (Λ□ (₂₊ k)))) ⟩
    cτ * (√2^ len (Λ□ (₂₊ k) ↑) * cτ)
      ≡⟨ Eq.cong (cτ *_) (Eq.sym (√2^-+ (len (Λ□ (₂₊ k) ↑)) ℓτ)) ⟩
    cτ * √2^ (len (Λ□ (₂₊ k) ↑) +ℕ ℓτ)
      ≡⟨ Eq.sym (√2^-+ ℓτ (len (Λ□ (₂₊ k) ↑) +ℕ ℓτ)) ⟩
    √2^ (ℓτ +ℕ (len (Λ□ (₂₊ k) ↑) +ℕ ℓτ)) ∎
    where open Eq.≡-Reasoning

  g′-eq : (k : ℕ) → ∀ (x : Bits (₄₊ k)) → tl (phase (₂₊ k)) (sw x) ≡ g′ x
  g′-eq k (a ∷ b ∷ c ∷ u) = Eq.refl

  -- The conjugated shifted box is diagonal.
  T-diag : (k : ℕ) → ⟦ Λ□ (₂₊ k) ⟧ₒ ≐ (c₂ k · diag (phase (₂₊ k))) →
           ⟦ τ₀₂-conj (Λ□ (₂₊ k) ↑) ⟧ₒ ≐ (cT k · D′ k)
  T-diag k ih =
    ≐-trans (⟦⟧ₒ-•₃ τ₀₂ (Λ□ (₂₊ k) ↑) τ₀₂)
     (≐-trans (⊙-cong (τ-op k) (⊙-cong (shift k ih) (τ-op k)))
      (≐-trans (⊙-cong (≐-refl (cτ · P k)) (·-⊙ˡ (c₂ k) (D₂ k) (cτ · P k)))
       (≐-trans (⊙-cong (≐-refl (cτ · P k)) (·-cong Eq.refl (·-⊙ʳ cτ (D₂ k) (P k))))
        (≐-trans (⊙-cong (≐-refl (cτ · P k)) (·-assoc (c₂ k) cτ (D₂ k ⊙ P k)))
         (≐-trans (·-⊙ˡ cτ (P k) ((c₂ k * cτ) · (D₂ k ⊙ P k)))
          (≐-trans (·-cong Eq.refl (·-⊙ʳ (c₂ k * cτ) (P k) (D₂ k ⊙ P k)))
           (≐-trans (·-assoc cτ (c₂ k * cτ) (P k ⊙ (D₂ k ⊙ P k)))
            (·-cong (scalarT k)
              (≐-trans (perm-conj (tl (phase (₂₊ k)))) (diag-cong (g′-eq k)))))))))))

  -- The four factors as controlled operators, and their product.
  g′-ctrl : (k : ℕ) → D′ k ≐ ctrl (diag z₀) Idₒ allT
  g′-ctrl k = ≐-sym (≐-trans (ctrl-diag z₀ allT)
                       (diag-cong (λ { (a ∷ b ∷ c ∷ u) → Eq.sym (sgn-∧ a (allT u)) })))

  ccz-eq : (k : ℕ) → ∀ (x : Bits (₄₊ k)) → ctrlPhase ccz allT x ≡ phase (₃₊ k) x
  ccz-eq k (a ∷ b ∷ c ∷ u) = sgn-∧∧ b c (allT u)

  set : (ix Cm ⊙ (diag z₀ ⊙ (ix C′m ⊙ diag z₀))) ≐ (cC · diag ccz)
  set =
    ≐-trans (⊙-cong (≐-refl (ix Cm))
               (⊙-cong (≐-sym D3-ix) (⊙-cong (≐-refl (ix C′m)) (≐-sym D3-ix))))
      (≐-trans (⊙-cong (≐-refl (ix Cm)) (⊙-cong (≐-refl (ix D3)) (≐-sym (ix-mul C′m D3))))
        (≐-trans (⊙-cong (≐-refl (ix Cm)) (≐-sym (ix-mul D3 (mulM C′m D3))))
          (≐-trans (≐-sym (ix-mul Cm (mulM D3 (mulM C′m D3))))
            (≐-trans (ix-≡ step-set)
              (≐-trans (ix-scaleM cC (matOf (diag ccz)))
                       (·-cong Eq.refl (ix-matOf (diag ccz))))))))

  unset : (ix Cm ⊙ (Idₒ ⊙ (ix C′m ⊙ Idₒ))) ≐ (cC · Idₒ)
  unset =
    ≐-trans (⊙-cong (≐-refl (ix Cm))
               (⊙-cong (≐-sym ix-id) (⊙-cong (≐-refl (ix C′m)) (≐-sym ix-id))))
      (≐-trans (⊙-cong (≐-refl (ix Cm)) (⊙-cong (≐-refl (ix idM)) (≐-sym (ix-mul C′m idM))))
        (≐-trans (⊙-cong (≐-refl (ix Cm)) (≐-sym (ix-mul idM (mulM C′m idM))))
          (≐-trans (≐-sym (ix-mul Cm (mulM idM (mulM C′m idM))))
            (≐-trans (ix-≡ step-unset)
              (≐-trans (ix-scaleM cC idM) (·-cong Eq.refl ix-id))))))

  K K′ Dc : (k : ℕ) → Op (₄₊ k)
  K  k = ctrl (ix Cm) (ix Cm) allT
  K′ k = ctrl (ix C′m) (ix C′m) allT
  Dc k = ctrl (diag z₀) Idₒ allT

  core : (k : ℕ) → (A k ⊙ (D′ k ⊙ (A′ k ⊙ D′ k))) ≐ (cC · diag (phase (₃₊ k)))
  core k =
    ≐-trans (⊙-cong (emb-ctrl Cm allT)
               (⊙-cong (g′-ctrl k) (⊙-cong (emb-ctrl C′m allT) (g′-ctrl k))))
      (≐-trans (⊙-cong (≐-refl (K k))
                 (⊙-cong (≐-refl (Dc k)) (ctrl-⊙ (ix C′m) (diag z₀) (ix C′m) Idₒ allT)))
        (≐-trans (⊙-cong (≐-refl (K k))
                   (ctrl-⊙ (diag z₀) (ix C′m ⊙ diag z₀) Idₒ (ix C′m ⊙ Idₒ) allT))
          (≐-trans (ctrl-⊙ (ix Cm) (diag z₀ ⊙ (ix C′m ⊙ diag z₀))
                           (ix Cm) (Idₒ ⊙ (ix C′m ⊙ Idₒ)) allT)
            (≐-trans (ctrl-cong set unset)
              (≐-trans (ctrl-· cC (diag ccz) Idₒ allT)
                (·-cong Eq.refl
                  (≐-trans (ctrl-diag ccz allT) (diag-cong (ccz-eq k)))))))))

  -- The powers of √2 add up to the number of letters of the box.
  scalar : (k : ℕ) → (cT k * cT k) * cC ≡ √2^ len (Λ□ (₃₊ k))
  scalar k = begin
    (cT k * cT k) * cC
      ≡⟨ Eq.cong ((cT k * cT k) *_) (√2^-+ (len CCZX₀) (len CCXZ₀)) ⟩
    (cT k * cT k) * (√2^ len CCZX₀ * √2^ len CCXZ₀)
      ≡⟨ rearrange (cT k) (√2^ len CCZX₀) (√2^ len CCXZ₀) ⟩
    √2^ len CCZX₀ * (cT k * (√2^ len CCXZ₀ * cT k))
      ≡⟨ Eq.cong (λ □ → √2^ len CCZX₀ * (cT k * □))
                 (Eq.sym (√2^-+ (len CCXZ₀) (len (τ₀₂-conj (Λ□ (₂₊ k) ↑))))) ⟩
    √2^ len CCZX₀ * (cT k * √2^ (len CCXZ₀ +ℕ len (τ₀₂-conj (Λ□ (₂₊ k) ↑))))
      ≡⟨ Eq.cong (√2^ len CCZX₀ *_)
                 (Eq.sym (√2^-+ (len (τ₀₂-conj (Λ□ (₂₊ k) ↑)))
                                 (len CCXZ₀ +ℕ len (τ₀₂-conj (Λ□ (₂₊ k) ↑))))) ⟩
    √2^ len CCZX₀ *
      √2^ (len (τ₀₂-conj (Λ□ (₂₊ k) ↑)) +ℕ (len CCXZ₀ +ℕ len (τ₀₂-conj (Λ□ (₂₊ k) ↑))))
      ≡⟨ Eq.sym (√2^-+ (len CCZX₀)
                        (len (τ₀₂-conj (Λ□ (₂₊ k) ↑)) +ℕ (len CCXZ₀ +ℕ len (τ₀₂-conj (Λ□ (₂₊ k) ↑))))) ⟩
    √2^ len (Λ□ (₃₊ k)) ∎
    where
    open Eq.≡-Reasoning
    rearrange : ∀ t a c → (t * t) * (a * c) ≡ a * (t * (c * t))
    rearrange = solve 3 (λ t a c → ((t ⊗ t) ⊗ (a ⊗ c)) , (a ⊗ (t ⊗ (c ⊗ t))))
      (λ {_} {_} {_} → Eq.refl)

  main : (k : ℕ) → ⟦ Λ□ (₂₊ k) ⟧ₒ ≐ (c₂ k · diag (phase (₂₊ k))) →
         ⟦ Λ□ (₃₊ k) ⟧ₒ ≐ ((√2^ len (Λ□ (₃₊ k))) · diag (phase (₃₊ k)))
  main k ih =
    ≐-trans (⟦⟧ₒ-•₄ CCZX (τ₀₂-conj (Λ□ (₂₊ k) ↑)) CCXZ (τ₀₂-conj (Λ□ (₂₊ k) ↑)))
     (≐-trans (⊙-cong (A-emb k) (⊙-cong (T-diag k ih) (⊙-cong (A′-emb k) (T-diag k ih))))
      (≐-trans (⊙-cong (≐-refl (A k)) (⊙-cong (≐-refl (cT k · D′ k)) (·-⊙ʳ (cT k) (A′ k) (D′ k))))
       (≐-trans (⊙-cong (≐-refl (A k)) (·-⊙ (cT k) (cT k) (D′ k) (A′ k ⊙ D′ k)))
        (≐-trans (·-⊙ʳ (cT k * cT k) (A k) (D′ k ⊙ (A′ k ⊙ D′ k)))
         (≐-trans (·-cong Eq.refl (core k))
          (≐-trans (·-assoc (cT k * cT k) cC (diag (phase (₃₊ k))))
                   (·-cong (scalar k) (≐-refl (diag (phase (₃₊ k)))))))))))

------------------------------------------------------------------------
-- The semantics of the multi-controlled box

Λ□-sem : (k : ℕ) → ⟦ Λ□ k ⟧ₒ ≐ ((√2^ len (Λ□ k)) · diag (phase k))
Λ□-sem 0 = by-trie (Λ□ 0) (√2^ len (Λ□ 0)) (phase 0) b0
Λ□-sem 1 = by-trie (Λ□ 1) (√2^ len (Λ□ 1)) (phase 1) b1
Λ□-sem 2 = by-trie (Λ□ 2) (√2^ len (Λ□ 2)) (phase 2) b2
Λ□-sem (₃₊ k) = main k (Λ□-sem (₂₊ k))

------------------------------------------------------------------------
-- Soundness of Equation (19)
--
-- The box is diagonal, Z is diagonal, and diagonal operators commute;
-- the two sides have the same number of letters.

box-Z-sound : (k : ℕ) → ⟦ Z ↓ • Λ□ (₄₊ k) ⟧ ~ ⟦ Λ□ (₄₊ k) • Z ↓ ⟧
box-Z-sound k =
  ~-reflexive {l = len (Z ↓ • Λ□ (₄₊ k))} {len (Λ□ (₄₊ k) • Z ↓)}
              {M = ⟦ Z ↓ • Λ□ (₄₊ k) ⟧ₒ} {⟦ Λ□ (₄₊ k) • Z ↓ ⟧ₒ}
    (NP.+-comm 1 (len (Λ□ (₄₊ k))))
    (≐-trans (⟦⟧ₒ-• (Z ↓) (Λ□ (₄₊ k)))
      (≐-trans (⊙-cong Z-diag (Λ□-sem (₄₊ k)))
        (≐-trans (·-⊙ʳ c (diag zph) (diag (phase (₄₊ k))))
          (≐-trans (·-cong Eq.refl (diag-comm zph (phase (₄₊ k))))
            (≐-trans (≐-sym (·-⊙ˡ c (diag (phase (₄₊ k))) (diag zph)))
              (≐-trans (⊙-cong (≐-sym (Λ□-sem (₄₊ k))) (≐-sym Z-diag))
                       (≐-sym (⟦⟧ₒ-• (Λ□ (₄₊ k)) (Z ↓)))))))))
  where
  c = √2^ len (Λ□ (₄₊ k))
