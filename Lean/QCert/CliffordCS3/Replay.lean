/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Rewrite certificates with wider positions

The existing numeric rewriter supports arbitrary positions, but its
25-bit packed format leaves only 12 bits for a position. The three-qubit
certificates include words longer than 4096 letters. Use 32-bit steps
here (19 position bits), avoiding thousands of repeated prefix letters
in auxiliary context rules. Every step uses the same proved rewriter.
-/
import QCert.CliffordT2.FastRewrite

namespace QCert

universe u
variable {α : Type u} {Γ : WRel α} {κ : α → ℕ}

/-- Replay 32-bit packed steps on numeric words. -/
def runWide (tbl : List CRule) (n : ℕ) : ℕ → ℕ → Option ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Option ℕ) (fun _ c => some c)
    (fun _ ih code c =>
      match stepC tbl c (code % 4294967296) with
      | some c' => ih (code / 4294967296) c'
      | none => none) n

def runWideChunks (tbl : List CRule) : List (ℕ × ℕ) → ℕ → Option ℕ
  | [], c => some c
  | (n, code) :: cs, c =>
    match runWide tbl n code c with
    | some c' => runWideChunks tbl cs c'
    | none => none

theorem runWide_sound (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (n : ℕ) :
    ∀ (code : ℕ) (w : List α) (c' : ℕ),
      runWide (compileRules κ rules) n code (enc κ w) = some c' →
      ∃ w', c' = enc κ w' ∧ Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction n with
  | zero =>
    intro code w c' h
    simp only [runWide, Nat.rec_zero, Option.some.injEq] at h
    exact ⟨w, h.symm, Derivable.refl _⟩
  | succ n ih =>
    intro code w c' h
    simp only [runWide] at h
    split at h
    · rename_i c₁ h₁
      obtain ⟨w₁, rfl, d₁⟩ := stepC_sound hκ hinj rules h₁
      obtain ⟨w₂, rfl, d₂⟩ := ih (code / 4294967296) w₁ c' h
      exact ⟨w₂, rfl, d₁.trans d₂⟩
    · simp at h

theorem runWideChunks_sound (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (cs : List (ℕ × ℕ)) :
    ∀ (w : List α) (c' : ℕ), runWideChunks (compileRules κ rules) cs (enc κ w) = some c' →
      ∃ w', c' = enc κ w' ∧ Derivable Γ (FreeMonoid.ofList w) (FreeMonoid.ofList w') := by
  induction cs with
  | nil =>
    intro w c' h
    simp only [runWideChunks, Option.some.injEq] at h
    exact ⟨w, h.symm, Derivable.refl _⟩
  | cons nc cs ih =>
    intro w c' h
    obtain ⟨n, code⟩ := nc
    simp only [runWideChunks] at h
    split at h
    · rename_i c₁ h₁
      obtain ⟨w₁, rfl, d₁⟩ := runWide_sound hκ hinj rules n code w c₁ h₁
      obtain ⟨w₂, rfl, d₂⟩ := ih w₁ c' h
      exact ⟨w₂, rfl, d₁.trans d₂⟩
    · simp at h

def Rule.byWideChunks (hκ : ∀ a, 0 < κ a ∧ κ a < 16) (hinj : Function.Injective κ)
    (rules : List (Rule Γ)) (l r : List α) (cs : List (ℕ × ℕ))
    (h : runWideChunks (compileRules κ rules) cs (enc κ l) = some (enc κ r)) : Rule Γ :=
  ⟨l, r, by
    obtain ⟨w', hw', d⟩ := runWideChunks_sound hκ hinj rules cs _ _ h
    have e := enc_injective hκ hinj hw'
    subst e
    exact d⟩

end QCert
