/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Clifford circuits (Selinger): the Pauli action, letter by letter

The action of `Pauli` (`actC`, which follows the generators: gates on the
bottom wires and circuits moved up) read on Pauli data indexed by all
natural numbers (`PS`), letter by letter (`actLt`, `actW`, time order): a
letter at the wire `i` changes the data at `i` (and `i + 1`) only.  The two
agree (`toPS_actC_wc`), and data on `n` wires are determined by their
reading (`toPS_inj`).
-/
import QCert.SelingerClifford.Pauli
import QCert.SelingerClifford.Letters

namespace QCert.SelingerClifford

/-! ### Pauli data on all wires -/

/-- Pauli data on all wires: `i^c ⊗ⱼ X^{a j} Z^{b j}`. -/
@[ext] structure PS where
  c : Fin 4
  a : ℕ → Fin 2
  b : ℕ → Fin 2

/-- A one-wire action `f` at the wire `i`. -/
def act1PS (f : PD 1 → PD 1) (i : ℕ) (P : PS) : PS :=
  let Q := f ⟨0, fun _ => P.a i, fun _ => P.b i⟩
  ⟨Q.c + P.c, Function.update P.a i (Q.a 0), Function.update P.b i (Q.b 0)⟩

/-- A two-wire action `f` at the wires `i, i + 1`. -/
def act2PS (f : PD 2 → PD 2) (i : ℕ) (P : PS) : PS :=
  let Q := f ⟨0, ![P.a i, P.a (i + 1)], ![P.b i, P.b (i + 1)]⟩
  ⟨Q.c + P.c, Function.update (Function.update P.a i (Q.a 0)) (i + 1) (Q.a 1),
    Function.update (Function.update P.b i (Q.b 0)) (i + 1) (Q.b 1)⟩

/-- The action of a letter. -/
def actLt : Lt → PS → PS
  | .om => id
  | .H i => act1PS actH i
  | .S i => act1PS actS i
  | .CZ i => act2PS actCZ i

/-- The action of a word of letters, in time order. -/
def actW : List Lt → PS → PS
  | [], P => P
  | a :: l, P => actW l (actLt a P)

theorem actW_append (l l' : List Lt) (P : PS) : actW (l ++ l') P = actW l' (actW l P) := by
  induction l generalizing P with
  | nil => rfl
  | cons a l ih => exact ih _

/-- The reading of Pauli data on `n` wires (identity above). -/
def toPS {n : ℕ} (P : PD n) : PS :=
  ⟨P.c, fun x => if h : x < n then P.a ⟨x, h⟩ else 0,
    fun x => if h : x < n then P.b ⟨x, h⟩ else 0⟩

theorem toPS_inj {n : ℕ} {P Q : PD n} (h : toPS P = toPS Q) : P = Q := by
  have hc := congrArg PS.c h
  have ha := congrArg PS.a h
  have hb := congrArg PS.b h
  refine PD.ext hc (funext fun x => ?_) (funext fun x => ?_)
  · have := congrFun ha x; simpa [toPS, x.2] using this
  · have := congrFun hb x; simpa [toPS, x.2] using this

/-- Data with one more wire at the bottom. -/
def consPS (x z : Fin 2) (Q : PS) : PS :=
  ⟨Q.c, fun w => Nat.casesOn w x Q.a, fun w => Nat.casesOn w z Q.b⟩

theorem act1PS_cons (f : PD 1 → PD 1) (i : ℕ) (x z : Fin 2) (Q : PS) :
    act1PS f (i + 1) (consPS x z Q) = consPS x z (act1PS f i Q) := by
  ext w
  · rfl
  · cases w <;> simp [act1PS, consPS, Function.update]
  · cases w <;> simp [act1PS, consPS, Function.update]

theorem act2PS_cons (f : PD 2 → PD 2) (i : ℕ) (x z : Fin 2) (Q : PS) :
    act2PS f (i + 1) (consPS x z Q) = consPS x z (act2PS f i Q) := by
  ext w
  · rfl
  · cases w <;> simp [act2PS, consPS, Function.update]
  · cases w <;> simp [act2PS, consPS, Function.update]

/-! ### The generators, read on all wires -/

/-- The data on the top `m` of `m + 1` wires. -/
def PD.hi {m : ℕ} (P : PD (m + 1)) : PD m :=
  ⟨P.c, (split 2 m 1 P.a).2, (split 2 m 1 P.b).2⟩

theorem toPS_cons {m : ℕ} (P : PD (m + 1)) :
    toPS P = consPS (P.a 0) (P.b 0) (toPS P.hi) := by
  ext w
  · rfl
  · cases w with
    | zero => simp [toPS, consPS]
    | succ w =>
      simp only [toPS, consPS, PD.hi, split, Equiv.coe_fn_mk]
      by_cases h : w < m
      · rw [dif_pos (by omega), dif_pos h]; congr 3; omega
      · rw [dif_neg (by omega), dif_neg h]
  · cases w with
    | zero => simp [toPS, consPS]
    | succ w =>
      simp only [toPS, consPS, PD.hi, split, Equiv.coe_fn_mk]
      by_cases h : w < m
      · rw [dif_pos (by omega), dif_pos h]; congr 3; omega
      · rw [dif_neg (by omega), dif_neg h]

theorem embedHi_hi {m : ℕ} (f : PD m → PD m) (P : PD (m + 1)) :
    (embedHi (k := 1) f P).hi = f P.hi := by
  simp only [embedHi, PD.hi, Equiv.apply_symm_apply]

theorem embedHi_a0 {m : ℕ} (f : PD m → PD m) (P : PD (m + 1)) :
    (embedHi (k := 1) f P).a 0 = P.a 0 := by
  simp [embedHi, split]

theorem embedHi_b0 {m : ℕ} (f : PD m → PD m) (P : PD (m + 1)) :
    (embedHi (k := 1) f P).b 0 = P.b 0 := by
  simp [embedHi, split]

theorem toPS_embedHi {m : ℕ} (f : PD m → PD m) (P : PD (m + 1)) :
    toPS (embedHi (k := 1) f P) = consPS (P.a 0) (P.b 0) (toPS (f P.hi)) := by
  rw [toPS_cons, embedHi_hi, embedHi_a0, embedHi_b0]

theorem embedHi_comp {m : ℕ} (f g : PD m → PD m) (P : PD (m + 1)) :
    embedHi (k := 1) f (embedHi (k := 1) g P) = embedHi (k := 1) (f ∘ g) P := by
  simp only [embedHi, Equiv.apply_symm_apply, Function.comp]

theorem embedHi_id {m : ℕ} (P : PD (m + 1)) : embedHi (k := 1) id P = P := by
  simp only [embedHi, id, Prod.mk.eta, Equiv.symm_apply_apply]

theorem actC_shift {m : ℕ} (w : Circ m) (P : PD (m + 1)) :
    actC (m + 1) (Circuit.shift w) P = embedHi (k := 1) (actC m w) P := by
  induction w using FreeMonoid.inductionOn' generalizing P with
  | one => exact (embedHi_id P).symm
  | mul_of g w ih =>
    have e : (actC m (FreeMonoid.of g * w) : PD m → PD m) = actGen g ∘ actC m w :=
      funext fun Q => actC_of g w Q
    rw [map_mul, Circuit.shift_of, actC_of, ih, e]
    exact embedHi_comp _ _ P

theorem toPS_embedLo1 {m : ℕ} (f : PD 1 → PD 1) (P : PD (m + 1)) :
    toPS (embedLo (m := m) (k := 1) f P) = act1PS f 0 (toPS P) := by
  have e : (⟨0, (split 2 m 1 P.a).1, (split 2 m 1 P.b).1⟩ : PD 1) =
      ⟨0, fun _ => (toPS P).a 0, fun _ => (toPS P).b 0⟩ := by
    ext i
    · rfl
    · rw [Fin.fin_one_eq_zero i]; simp [split, toPS]
    · rw [Fin.fin_one_eq_zero i]; simp [split, toPS]
  ext w
  · simp only [toPS, embedLo, act1PS, e]
  · simp only [toPS, embedLo, act1PS, Function.update, split, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk]
    by_cases h0 : w = 0
    · subst h0; simp
    · rw [dif_neg h0]
      by_cases h : w < m + 1
      · rw [dif_pos h, dif_pos h, dif_neg (by omega)]; congr 3; omega
      · rw [dif_neg h, dif_neg h]
  · simp only [toPS, embedLo, act1PS, Function.update, split, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk]
    by_cases h0 : w = 0
    · subst h0; simp
    · rw [dif_neg h0]
      by_cases h : w < m + 1
      · rw [dif_pos h, dif_pos h, dif_neg (by omega)]; congr 3; omega
      · rw [dif_neg h, dif_neg h]

theorem toPS_embedLo2 {m : ℕ} (f : PD 2 → PD 2) (P : PD (m + 2)) :
    toPS (embedLo (m := m) (k := 2) f P) = act2PS f 0 (toPS P) := by
  have e : (⟨0, (split 2 m 2 P.a).1, (split 2 m 2 P.b).1⟩ : PD 2) =
      ⟨0, ![(toPS P).a 0, (toPS P).a 1], ![(toPS P).b 0, (toPS P).b 1]⟩ := by
    ext i
    · rfl
    · fin_cases i <;> simp [split, toPS]
    · fin_cases i <;> simp [split, toPS]
  set Q := f ⟨0, ![(toPS P).a 0, (toPS P).a 1], ![(toPS P).b 0, (toPS P).b 1]⟩ with hQ
  have hE : embedLo (m := m) (k := 2) f P = ⟨Q.c + P.c,
      (split 2 m 2).symm (Q.a, (split 2 m 2 P.a).2),
      (split 2 m 2).symm (Q.b, (split 2 m 2 P.b).2)⟩ := by
    simp only [embedLo]; rw [e]
  have hA : act2PS f 0 (toPS P) = ⟨Q.c + P.c,
      Function.update (Function.update (toPS P).a 0 (Q.a 0)) 1 (Q.a 1),
      Function.update (Function.update (toPS P).b 0 (Q.b 0)) 1 (Q.b 1)⟩ := rfl
  rw [hE, hA]
  ext w
  · rfl
  · simp only [toPS, Function.update, split, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    by_cases h1 : w = 1
    · subst h1; simp
    by_cases h0 : w = 0
    · subst h0; simp
    rw [dif_neg h1, dif_neg h0]
    by_cases h : w < m + 2
    · rw [dif_pos h, dif_pos h, dif_neg (by omega)]; congr 3; omega
    · rw [dif_neg h, dif_neg h]
  · simp only [toPS, Function.update, split, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    by_cases h1 : w = 1
    · subst h1; simp
    by_cases h0 : w = 0
    · subst h0; simp
    rw [dif_neg h1, dif_neg h0]
    by_cases h : w < m + 2
    · rw [dif_pos h, dif_pos h, dif_neg (by omega)]; congr 3; omega
    · rw [dif_neg h, dif_neg h]

theorem actC_gen {n : ℕ} (g : Gen Gate n) (P : PD n) :
    actC n (FreeMonoid.of g) P = actGen g P := by
  simpa using actC_of g 1 P

theorem toPS_onW1 (g : Gate 1) (f : PD 1 → PD 1) (hf : act1 g = f) :
    ∀ (n i : ℕ), i + 1 ≤ n → ∀ P : PD n, toPS (actC n (onW1 g n i) P) = act1PS f i (toPS P)
  | 0, _, h, _ => by omega
  | m + 1, 0, _, P => by
    show toPS (actC (m + 1) (FreeMonoid.of (Gen.gate1 g)) P) = _
    rw [actC_gen]
    show toPS (embedLo (act1 g) P) = _
    rw [hf, toPS_embedLo1]
  | m + 1, i + 1, h, P => by
    show toPS (actC (m + 1) (Circuit.shift (onW1 g m i)) P) = _
    rw [actC_shift, toPS_embedHi, toPS_onW1 g f hf m i (by omega), toPS_cons P, act1PS_cons]

theorem toPS_onW2 (g : Gate 2) :
    ∀ (n i : ℕ), i + 2 ≤ n → ∀ P : PD n,
      toPS (actC n (onW2 g n i) P) = act2PS actCZ i (toPS P)
  | 0, _, h, _ => by omega
  | 1, _, h, _ => by omega
  | m + 2, 0, _, P => by
    show toPS (actC (m + 2) (FreeMonoid.of (Gen.gate2 g)) P) = _
    rw [actC_gen]
    exact toPS_embedLo2 actCZ P
  | m + 1, i + 1, h, P => by
    show toPS (actC (m + 1) (Circuit.shift (onW2 g m i)) P) = _
    rw [actC_shift, toPS_embedHi, toPS_onW2 g m i (by omega), toPS_cons P, act2PS_cons]

theorem toPS_actC_circ {n : ℕ} (a : Lt) (ha : a.hi ≤ n) (P : PD n) :
    toPS (actC n (Lt.circ n a) P) = actLt a (toPS P) := by
  cases a with
  | om => show toPS (actC n (FreeMonoid.of (Gen.gate0 Gate.ω)) P) = _; rw [actC_gen]; rfl
  | H i => exact toPS_onW1 Gate.H actH rfl n i ha P
  | S i => exact toPS_onW1 Gate.S actS rfl n i ha P
  | CZ i => exact toPS_onW2 Gate.CZ n i ha P

/-- **The action of a word, letter by letter.** -/
theorem toPS_actC_wc {n : ℕ} : ∀ (l : List Lt), (∀ a ∈ l, a.hi ≤ n) → ∀ P : PD n,
    toPS (actC n (wc n l) P) = actW l (toPS P)
  | [], _, P => rfl
  | a :: l, hl, P => by
    show toPS (actC n (wc n l * Lt.circ n a) P) = _
    rw [map_mul]
    show toPS (actC n (wc n l) (actC n (Lt.circ n a) P)) = _
    rw [toPS_actC_wc l (fun b hb => hl b (by simp [hb])), toPS_actC_circ a (hl a (by simp))]
    rfl

end QCert.SelingerClifford
