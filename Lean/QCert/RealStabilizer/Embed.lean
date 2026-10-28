/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits as Clifford circuits

Every real stabilizer gate is a Clifford gate (Selinger's): `-1 = ω⁴`,
`Z = S²`, and `H`, `CZ` are the same.  A word of real letters is read as a
word of Clifford letters (`embW`), and its real matrix, read in `ℂ`, is the
matrix of that Clifford word (`sem_embW`).  So the action of Clifford
circuits on Pauli operators (`SelingerClifford.actW`, conjugation by the
matrix) serves for real circuits too: real circuits with the same matrix act
alike (`actW_eq_of_sem`).
-/
import QCert.RealStabilizer.Relator
import QCert.RealStabilizer.Semantics
import QCert.SelingerClifford.Unique

namespace QCert.RealStabilizer

open Matrix Circuit

noncomputable section

/-! ### Gates on a wire -/

section Place

variable {R : Type*} [CommRing R]

/-- A one-wire operator on the wire `i` of `n` (the identity if it does not
fit). -/
def place1 (G : Op R 2 1) : (n i : ℕ) → Op R 2 n
  | _ + 1, 0 => onBottom G
  | n + 1, i + 1 => onTop 1 (place1 G n i)
  | 0, _ => 1

/-- A two-wire operator on the wires `i, i + 1` of `n`. -/
def place2 (G : Op R 2 2) : (n i : ℕ) → Op R 2 n
  | n + 1, i + 1 => onTop 1 (place2 G n i)
  | _ + 2, 0 => onBottom G
  | _, _ => 1

theorem place1_mul (A B : Op R 2 1) : ∀ n i, place1 (A * B) n i = place1 A n i * place1 B n i
  | _ + 1, 0 => onBottom_mul A B
  | n + 1, i + 1 => by simp only [place1]; rw [place1_mul A B n i, onTop_mul]
  | 0, _ => by simp [place1]

variable {S' : Type*} [CommRing S'] (f : R →+* S')

theorem onBottom_map {n k : ℕ} (G : Op R 2 k) :
    (onBottom (n := n) G).map f = onBottom (G.map f) := by
  ext s t; simp only [Matrix.map_apply, onBottom_apply]; split_ifs <;> simp

theorem onTop_map {n k : ℕ} (M : Op R 2 n) : (onTop k M).map f = onTop k (M.map f) := by
  ext s t; simp only [Matrix.map_apply, onTop_apply]; split_ifs <;> simp

theorem map_one' {n : ℕ} : (1 : Op R 2 n).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)

theorem place1_map (G : Op R 2 1) : ∀ n i, (place1 G n i).map f = place1 (G.map f) n i
  | _ + 1, 0 => onBottom_map f G
  | n + 1, i + 1 => by simp only [place1]; rw [onTop_map, place1_map G n i]
  | 0, _ => by simp only [place1]; exact map_one' f

theorem place2_map (G : Op R 2 2) : ∀ n i, (place2 G n i).map f = place2 (G.map f) n i
  | n + 1, i + 1 => by simp only [place2]; rw [onTop_map, place2_map G n i]
  | _ + 2, 0 => onBottom_map f G
  | 0, _ => by simp only [place2]; exact map_one' f
  | 1, 0 => by simp only [place2]; exact map_one' f

end Place

/-! ### The two semantics on a wire -/

theorem sem_onW1 (g : Gate 1) : ∀ n i, (S.sem n (onW1 g n i)).1 = place1 (S.gate1 g).1 n i
  | _ + 1, 0 => by
    show (FreeMonoid.lift S.gen (FreeMonoid.of _)).1 = _
    rw [FreeMonoid.lift_eval_of]; rfl
  | n + 1, i + 1 => by
    simp only [onW1, place1]
    rw [S.sem_shift]
    show onTop 1 _ = _
    rw [sem_onW1 g n i]
  | 0, _ => by simp [onW1, place1]

theorem sem_onW2 (g : Gate 2) : ∀ n i, (S.sem n (onW2 g n i)).1 = place2 (S.gate2 g).1 n i
  | n + 1, i + 1 => by
    simp only [onW2, place2]
    rw [S.sem_shift]
    show onTop 1 _ = _
    rw [sem_onW2 g n i]
  | _ + 2, 0 => by
    show (FreeMonoid.lift S.gen (FreeMonoid.of _)).1 = _
    rw [FreeMonoid.lift_eval_of]; rfl
  | 0, _ => by simp [onW2, place2]
  | 1, 0 => by simp [onW2, place2]

theorem ssem_onW1 (g : SelingerClifford.Gate 1) : ∀ n i,
    (SelingerClifford.S.sem n (SelingerClifford.onW1 g n i)).1 =
      place1 (SelingerClifford.S.gate1 g).1 n i
  | _ + 1, 0 => by
    show (FreeMonoid.lift SelingerClifford.S.gen (FreeMonoid.of _)).1 = _
    rw [FreeMonoid.lift_eval_of]; rfl
  | n + 1, i + 1 => by
    simp only [SelingerClifford.onW1, place1]
    rw [SelingerClifford.S.sem_shift]
    show onTop 1 _ = _
    rw [ssem_onW1 g n i]
  | 0, _ => by simp [SelingerClifford.onW1, place1]

theorem ssem_onW2 (g : SelingerClifford.Gate 2) : ∀ n i,
    (SelingerClifford.S.sem n (SelingerClifford.onW2 g n i)).1 =
      place2 (SelingerClifford.S.gate2 g).1 n i
  | n + 1, i + 1 => by
    simp only [SelingerClifford.onW2, place2]
    rw [SelingerClifford.S.sem_shift]
    show onTop 1 _ = _
    rw [ssem_onW2 g n i]
  | _ + 2, 0 => by
    show (FreeMonoid.lift SelingerClifford.S.gen (FreeMonoid.of _)).1 = _
    rw [FreeMonoid.lift_eval_of]; rfl
  | 0, _ => by simp [SelingerClifford.onW2, place2]
  | 1, 0 => by simp [SelingerClifford.onW2, place2]

/-! ### The gate matrices in `ℂ` -/

theorem ofMat_map {R S' : Type*} [CommRing R] [CommRing S'] (f : R →+* S') {k : ℕ}
    (M : Matrix (Fin (2 ^ k)) (Fin (2 ^ k)) R) : (ofMat M).map f = ofMat (M.map f) := rfl

theorem matH_map : matH.map Complex.ofRealHom = SelingerClifford.matH := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matH, SelingerClifford.matH, SelingerClifford.invSqrt2, invSqrt2]

theorem matZ_map : matZ.map Complex.ofRealHom = SelingerClifford.matS * SelingerClifford.matS := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matZ, SelingerClifford.matS, Matrix.mul_apply, Fin.sum_univ_two]

theorem matCZ_map : matCZ.map Complex.ofRealHom = SelingerClifford.matCZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matCZ, SelingerClifford.matCZ]

/-! ### Words -/

/-- The Clifford letters of a real letter: `-1 = ω⁴`, `Z = S²`. -/
def embL : Lt → List SelingerClifford.Lt
  | .neg => List.replicate 4 .om
  | .H i => [.H i]
  | .Z i => [.S i, .S i]
  | .CZ i => [.CZ i]

/-- The Clifford word of a real word. -/
def embW (l : List Lt) : List SelingerClifford.Lt := l.flatMap embL

@[simp] theorem embW_nil : embW [] = [] := rfl
@[simp] theorem embW_cons (a : Lt) (l : List Lt) : embW (a :: l) = embL a ++ embW l := rfl
@[simp] theorem embW_append (l l' : List Lt) : embW (l ++ l') = embW l ++ embW l' := by
  simp [embW, List.flatMap_append]

theorem swc_single (n : ℕ) (a : SelingerClifford.Lt) :
    SelingerClifford.wc n [a] = SelingerClifford.Lt.circ n a := by
  simp [SelingerClifford.wc]

theorem sem_letter (n : ℕ) (a : Lt) :
    (S.sem n (a.circ n)).1.map Complex.ofRealHom =
      (SelingerClifford.S.sem n (SelingerClifford.wc n (embL a))).1 := by
  cases a with
  | neg =>
    rw [show embL .neg = List.replicate 4 .om from rfl, SelingerClifford.sem_om_pow, ω_pow_four]
    show (FreeMonoid.lift S.gen (FreeMonoid.of _)).1.map _ = _
    rw [FreeMonoid.lift_eval_of]
    show (((-1 : ℝ)) • (1 : Op ℝ 2 n)).map Complex.ofRealHom = _
    ext s t
    simp [Matrix.one_apply]
    split_ifs <;> simp
  | H i =>
    rw [show embL (.H i) = [.H i] from rfl, swc_single]
    show (S.sem n (onW1 Gate.H n i)).1.map _ = (SelingerClifford.S.sem n
      (SelingerClifford.onW1 SelingerClifford.Gate.H n i)).1
    rw [sem_onW1, ssem_onW1, place1_map]
    show place1 ((ofMat matH).map _) n i = place1 (ofMat SelingerClifford.matH) n i
    rw [ofMat_map, matH_map]
  | Z i =>
    rw [show embL (.Z i) = [.S i, .S i] from rfl]
    simp only [SelingerClifford.wc, one_mul, map_mul, Submonoid.coe_mul]
    show (S.sem n (onW1 Gate.Z n i)).1.map _ = (SelingerClifford.S.sem n
      (SelingerClifford.onW1 SelingerClifford.Gate.S n i)).1 * (SelingerClifford.S.sem n
      (SelingerClifford.onW1 SelingerClifford.Gate.S n i)).1
    rw [sem_onW1, ssem_onW1, place1_map, ← place1_mul]
    show place1 ((ofMat matZ).map _) n i =
      place1 (ofMat SelingerClifford.matS * ofMat SelingerClifford.matS) n i
    rw [ofMat_map, matZ_map, SelingerClifford.ofMat_mul]
  | CZ i =>
    rw [show embL (.CZ i) = [.CZ i] from rfl, swc_single]
    show (S.sem n (onW2 Gate.CZ n i)).1.map _ = (SelingerClifford.S.sem n
      (SelingerClifford.onW2 SelingerClifford.Gate.CZ n i)).1
    rw [sem_onW2, ssem_onW2, place2_map]
    show place2 ((ofMat matCZ).map _) n i = place2 (ofMat SelingerClifford.matCZ) n i
    rw [ofMat_map, matCZ_map]

/-- **The real matrix of a word, read in `ℂ`, is the matrix of its Clifford
word.** -/
theorem sem_embW (n : ℕ) : ∀ l : List Lt,
    (S.sem n (wc n l)).1.map Complex.ofRealHom =
      (SelingerClifford.S.sem n (SelingerClifford.wc n (embW l))).1
  | [] => by simp only [wc, map_one, embW_nil, SelingerClifford.wc]; exact map_one' _
  | a :: l => by
    rw [embW_cons, SelingerClifford.wc_append, wc, map_mul, map_mul, Submonoid.coe_mul,
      Submonoid.coe_mul, Matrix.map_mul, sem_embW n l, sem_letter]

theorem embL_hi (a : Lt) : ∀ b ∈ embL a, b.hi = a.hi := by
  cases a <;> simp [embL, SelingerClifford.Lt.hi, Lt.hi]

theorem embW_hi {n : ℕ} {l : List Lt} (h : ∀ a ∈ l, a.hi ≤ n) : ∀ b ∈ embW l, b.hi ≤ n := by
  intro b hb
  obtain ⟨a, ha, hb⟩ := List.mem_flatMap.1 hb
  rw [embL_hi a b hb]; exact h a ha

/-- **Real circuits with the same matrix act alike on Pauli operators.** -/
theorem actW_eq_of_sem {n : ℕ} {l l' : List Lt} (hl : ∀ a ∈ l, a.hi ≤ n)
    (hl' : ∀ a ∈ l', a.hi ≤ n) (h : S.sem n (wc n l) = S.sem n (wc n l'))
    (P : SelingerClifford.PD n) :
    SelingerClifford.actW (embW l) (SelingerClifford.toPS P) =
      SelingerClifford.actW (embW l') (SelingerClifford.toPS P) := by
  rw [← SelingerClifford.toPS_actC_wc _ (embW_hi hl), ← SelingerClifford.toPS_actC_wc _ (embW_hi hl')]
  congr 1
  apply SelingerClifford.actC_eq_of_sem
  apply Subtype.ext
  rw [← sem_embW, ← sem_embW, h]

theorem embL_upBy (s : ℕ) (a : Lt) :
    embL (a.upBy s) = (embL a).map (SelingerClifford.Lt.upBy s) := by
  cases a <;> rfl

theorem embW_upN (s : ℕ) (l : List Lt) :
    embW (upN s l) = SelingerClifford.upN s (embW l) := by
  rw [upN_eq, SelingerClifford.upN_eq]
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, embW_cons, List.map_append, ih, embL_upBy]

end

end QCert.RealStabilizer
