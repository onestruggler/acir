/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Lemma A.4 and Corollary A.5

Lemma A.4: every proper Hadamard-free word over `𝒫_{2ⁿ}` is derivably equal
to a normal form (`nf_exists`), and a normal form is determined by its
signed permutation (`nf_unique`): the runs by where the permutation sends
the top indices (`perm_top`, `code_unique`), then the signs.  Our normal
form is a sign part `∏ (-1)_[0](-1)_[x]` followed by runs; the paper's (B)
pairs the signs differently, which does not matter for Corollary A.5.

Corollary A.5 (`A5`): two proper Hadamard-free words with the same matrix
are equal by the equations of Figure 8.
-/
import QCert.RealCliffordCH.Sec8.A.NFExist

namespace QCert.RealCliffordCH.Sec8

variable {n : ℕ}

/-! ## The normal form in natural-number letters -/

/-- `σ_j` as an `NL` letter. -/
def sgNL (j : ℕ) : NL := .zx j j (j + 1)

/-- The permutation part. -/
def PNL (d : ℕ → ℕ) (m : ℕ) : List NL := (pidx d m).map sgNL

/-- The sign part. -/
def SWL (b : ℕ → Bool) (xs : List ℕ) : List NL := xs.flatMap fun x => if b x then [.zz 0 x] else []

theorem PN_eq_map (d : ℕ → ℕ) (m : ℕ) : PN n d m = (PNL d m).map (NL.toPG n) := by
  simp only [PN, PNL, sgL, List.map_map]; rfl

theorem SWl_eq_map (b : ℕ → Bool) (xs : List ℕ) : SWl n b xs = (SWL b xs).map (NL.toPG n) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [SWl_cons, ih]; simp only [SWL, List.flatMap_cons, List.map_append]
    congr 1; split_ifs <;> rfl

theorem permL_append (l₁ l₂ : List NL) (x : ℕ) : permL (l₁ ++ l₂) x = permL l₁ (permL l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons y l ih => simp only [List.cons_append, permL, ih]

theorem negL_cons (y : NL) (l : List NL) (x : ℕ) :
    negL (y :: l) x = (y.neg (permL l x) ^^ negL l x) := by
  simp only [negL]; cases y.neg (permL l x) <;> simp

theorem negL_append (l₁ l₂ : List NL) (x : ℕ) :
    negL (l₁ ++ l₂) x = (negL l₁ (permL l₂ x) ^^ negL l₂ x) := by
  induction l₁ with
  | nil => simp [negL]
  | cons y l ih => rw [List.cons_append, negL_cons, negL_cons, ih, permL_append, Bool.xor_assoc]

theorem permL_SWL (b : ℕ → Bool) (xs : List ℕ) (x : ℕ) : permL (SWL b xs) x = x := by
  induction xs with
  | nil => rfl
  | cons y xs ih =>
    simp only [SWL, List.flatMap_cons] at ih ⊢
    rw [permL_append, ih]; split_ifs <;> rfl

theorem negL_SWL (b : ℕ → Bool) {x : ℕ} (hx : 1 ≤ x) :
    ∀ xs : List ℕ, xs.Nodup → negL (SWL b xs) x = (decide (x ∈ xs) && b x)
  | [], _ => rfl
  | y :: xs, hnd => by
    rw [List.nodup_cons] at hnd
    have ih := negL_SWL b hx xs hnd.2
    have hp := permL_SWL b xs x
    simp only [SWL, List.flatMap_cons] at ih hp ⊢
    rw [negL_append, ih, hp]
    by_cases hy : x = y
    · subst hy; cases hb : b x <;> simp [hb, negL, permL, NL.neg, hnd.1, show x ≠ 0 by omega]
    · cases hb : b y <;> simp [hb, negL, permL, NL.neg, hy, show x ≠ 0 by omega]

theorem permL_sgs_fix {x : ℕ} : ∀ js : List ℕ, (∀ j ∈ js, j + 1 < x) →
    permL (js.map sgNL) x = x
  | [], _ => rfl
  | j :: js, h => by
    simp only [List.map_cons, permL, NL.perm, sgNL]
    rw [permL_sgs_fix js fun i hi => h i (List.mem_cons_of_mem _ hi)]
    have := h j (by simp); simp only [swN]; split_ifs <;> omega

theorem permL_run (D : ℕ) : ∀ k, permL ((List.range' D k).map sgNL) (D + k) = D
  | 0 => rfl
  | k + 1 => by
    rw [List.range'_succ, List.map_cons]
    simp only [permL, NL.perm, sgNL]
    rw [show D + (k + 1) = D + 1 + k by omega, permL_run (D + 1) k]
    simp [swN]

theorem swN_inj (a b : ℕ) : Function.Injective (swN a b) := by
  intro x y h; unfold swN at h; split_ifs at h <;> omega

theorem permL_sgs_inj : ∀ js : List ℕ, Function.Injective (permL (js.map sgNL))
  | [] => fun _ _ h => h
  | j :: js => fun x y h => permL_sgs_inj js (swN_inj j (j + 1) h)

theorem perm_top {d : ℕ → ℕ} {m : ℕ} (hd : Code d (m + 1)) : permL (PNL d (m + 1)) m = d m := by
  simp only [PNL, pidx, List.map_append]
  rw [permL_append, permL_sgs_fix (pidx d m) (pidx_lt fun k hk => hd k (by omega))]
  have := permL_run (d m) (m - d m)
  rwa [show d m + (m - d m) = m by have := hd m (by omega); omega] at this

theorem code_unique {d d' : ℕ → ℕ} : ∀ m, Code d m → Code d' m →
    (∀ x, permL (PNL d m) x = permL (PNL d' m) x) → ∀ k < m, d k = d' k
  | 0, _, _, _, k, hk => absurd hk (by omega)
  | m + 1, hd, hd', h, k, hk => by
    have htop : d m = d' m := by rw [← perm_top hd, ← perm_top hd', h]
    have hrest : ∀ x, permL (PNL d m) x = permL (PNL d' m) x := by
      intro x
      have := h x
      simp only [PNL, pidx, List.map_append, permL_append, htop] at this
      exact permL_sgs_inj _ this
    by_cases e : k = m
    · subst e; exact htop
    · exact code_unique m (fun i hi => hd i (by omega)) (fun i hi => hd' i (by omega)) hrest k
        (by omega)

/-! ## Signed permutations of words -/

theorem spL_perm_bij {N : ℕ} (x : PG N) : Function.Bijective (spL x).perm := by
  cases x with
  | zz a c => exact Function.bijective_id
  | zx a c d => exact (Equiv.swap c d).bijective
  | xx a b c d => exact (Equiv.swap a b).bijective.comp (Equiv.swap c d).bijective
  | hh a b c d => exact Function.bijective_id

theorem spW_perm_bij {N : ℕ} (w : Word (PG N)) : Function.Bijective (spW w).perm := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact Function.bijective_id
  | mul_of x w ih =>
    rw [map_mul, spW, FreeMonoid.lift_eval_of, ← spW]
    exact (spL_perm_bij x).comp ih

theorem SP.cancel_right {N : ℕ} {A B X : SP N} (hX : Function.Surjective X.perm)
    (h : A * X = B * X) : A = B := by
  apply SP.ext <;> funext j <;> obtain ⟨i, rfl⟩ := hX j
  · exact congrFun (congrArg SP.perm h) i
  · have := congrFun (congrArg SP.neg h) i
    simp only [SP.mul_neg] at this
    revert this
    cases A.neg (X.perm i) <;> cases B.neg (X.perm i) <;> cases X.neg i <;> simp

theorem spW_wordOf_append {N : ℕ} (l l' : List (PG N)) :
    spW (wordOf (l ++ l')) = spW (wordOf l) * spW (wordOf l') := by
  rw [wordOf, FreeMonoid.ofList_append, map_mul]; rfl

/-! ## Uniqueness -/

theorem SWL_bd (b : ℕ → Bool) : ∀ x ∈ SWL b (sidx n), x.Bd n := by
  intro x hx
  simp only [SWL, List.mem_flatMap] at hx
  obtain ⟨y, hy, hx⟩ := hx
  split_ifs at hx with h
  · simp only [List.mem_singleton] at hx; subst hx
    exact ⟨Nat.two_pow_pos n, sidx_lt y hy⟩
  · simp at hx

theorem PNL_bd {d : ℕ → ℕ} (hd : Code d (2 ^ n)) : ∀ x ∈ PNL d (2 ^ n), x.Bd n := by
  intro x hx
  simp only [PNL, List.mem_map] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  have := pidx_lt hd j hj
  exact ⟨by omega, by omega, by omega⟩

/-- A normal form is determined by its signed permutation (Lemma A.4,
uniqueness). -/
theorem nf_unique {b b' : ℕ → Bool} {d d' : ℕ → ℕ} (hd : Code d (2 ^ n)) (hd' : Code d' (2 ^ n))
    (h : spW (wordOf (NFW n b d)) = spW (wordOf (NFW n b' d'))) : NFW n b d = NFW n b' d' := by
  unfold NFW at h ⊢
  rw [spW_wordOf_append, spW_wordOf_append] at h
  -- the sign parts permute nothing
  have hS : ∀ c : ℕ → Bool, ∀ j : Fin (2 ^ n), (spW (wordOf (SWl n c (sidx n)))).perm j = j := by
    intro c j
    apply Fin.ext
    rw [SWl_eq_map, (spW_NL (SWL_bd c) j).1, permL_SWL]
  have hperm : ∀ x < 2 ^ n, permL (PNL d (2 ^ n)) x = permL (PNL d' (2 ^ n)) x := by
    intro x hx
    have := congrFun (congrArg SP.perm h) ⟨x, hx⟩
    simp only [SP.mul_perm, hS] at this
    have e := congrArg Fin.val this
    rwa [PN_eq_map, PN_eq_map, (spW_NL (PNL_bd hd) _).1, (spW_NL (PNL_bd hd') _).1] at e
  have hperm' : ∀ x, permL (PNL d (2 ^ n)) x = permL (PNL d' (2 ^ n)) x := by
    intro x
    by_cases hx : x < 2 ^ n
    · exact hperm x hx
    · rw [PNL, PNL, permL_sgs_fix _ (fun j hj => by have := pidx_lt hd j hj; omega),
        permL_sgs_fix _ (fun j hj => by have := pidx_lt hd' j hj; omega)]
  have hdd := code_unique (2 ^ n) hd hd' hperm'
  have hP : PN n d (2 ^ n) = PN n d' (2 ^ n) := PN_congr hdd
  rw [hP] at h ⊢
  have hSW := SP.cancel_right (spW_perm_bij _).2 h
  have hb : ∀ x ∈ sidx n, b x = b' x := by
    intro x hx
    have hx1 : 1 ≤ x := by simp only [sidx, List.mem_range'] at hx; omega
    have := congrFun (congrArg SP.neg hSW) ⟨x, sidx_lt x hx⟩
    rw [SWl_eq_map, SWl_eq_map, (spW_NL (SWL_bd b) _).2, (spW_NL (SWL_bd b') _).2,
      negL_SWL b hx1 _ sidx_nodup, negL_SWL b' hx1 _ sidx_nodup] at this
    simpa [hx] using this
  rw [SWl_congr hb]

/-! ## Corollary A.5 -/

theorem NFW_empty : NFW n (fun _ => false) (fun k => k) = [] := by
  have hp : ∀ m, pidx (fun k => k) m = [] := by
    intro m; induction m with
    | zero => rfl
    | succ m ih => simp [pidx, ih]
  simp [NFW, SWl, PN, hp, sgL]

theorem nf_of (hN : 4 ≤ 2 ^ n) {l : List (PG (2 ^ n))} (hl : ∀ x ∈ l, x.HF ∧ x.Proper) :
    ∃ b d, Code d (2 ^ n) ∧ DH n l (NFW n b d) := by
  obtain ⟨b, d, hd, h⟩ := nf_exists hN l hl (fun _ => false) (fun k => k) (fun k _ => le_rfl)
  rw [NFW_empty, List.nil_append] at h
  exact ⟨b, d, hd, h⟩

/-- **Corollary A.5**: two proper Hadamard-free words with the same matrix are
equal by the equations of Figure 8. -/
theorem A5 (hN : 4 ≤ 2 ^ n) {l l' : List (PG (2 ^ n))} (hl : ∀ x ∈ l, x.HF ∧ x.Proper)
    (hl' : ∀ x ∈ l', x.HF ∧ x.Proper) (h : pSem (wordOf l) = pSem (wordOf l')) : D8 n l l' := by
  obtain ⟨b, d, hd, h1⟩ := nf_of hN hl
  obtain ⟨b', d', hd', h2⟩ := nf_of hN hl'
  have hw : ∀ (k : List (PG (2 ^ n))), (∀ x ∈ k, x.HF ∧ x.Proper) →
      pSem (wordOf k) = spMat (spW (wordOf k)) := fun k hk =>
    pWord_eq_spMat _ _ (fun x hx => (hk x (by simpa [wordOf] using hx)).1)
      (fun x hx => (hk x (by simpa [wordOf] using hx)).2)
  have hs : spW (wordOf l) = spW (wordOf l') := spMat_inj (by rw [← hw l hl, ← hw l' hl', h])
  have hn : NFW n b d = NFW n b' d' :=
    nf_unique hd hd' (by rw [← DH.spW h1, ← DH.spW h2, hs])
  exact DH.toD8 (h1.trans (hn ▸ h2.symm))

end QCert.RealCliffordCH.Sec8
