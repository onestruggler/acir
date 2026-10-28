/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Real stabilizer circuits: distinct normal forms denote distinct operators

Propositions 4.11–4.15 of Makary, Ross and Selinger, in the form completeness
needs: two normal circuits with the same matrix are equal (`normal_unique'`).
A real circuit acts on Pauli operators as its Clifford word does (`Embed`),
so Selinger's action (`SelingerClifford.actW`, with its injectivity and
locality lemmas) is used as it is.  As in the paper:

* each derived generator sends certain Pauli operators to others
  (Proposition 4.10, decided on its own wires: `fA` … `fEZ`): `A_i` sends
  `Z`, `X` or `XZ` to `Z` (on a simple wire) or `XZ` (on a double one), a `B`
  gate sends `Z` or `XZ` below and `I`, `X`, `Z` or `XZ` above to `Z` or `XZ`
  above, `D_ℓ` sends `I`, `X`, `Z` or `XZ` below and `X Z^t` above to
  `X Z^{t'}` below, `C`, `E` fix `Z`, `X` up to a sign;
* a Z-circuit `L` sends a Pauli operator `encL L` to `Z` on its top wire and
  is determined by it (Proposition 4.11: `encL_spec`, `encL_inj`); an
  X-circuit sends `encDC` to `X` on the wire `0` and is determined by it
  (Proposition 4.12), and sends `Z` on the top wire to `Z` on the wire `0`
  (Proposition 4.13, `DC_Z`);
* so two normal forms that act alike have the same `L`, `M` and, by
  induction on the width, differ at most in their scalar (Proposition 4.15,
  `nf_act_unique`), which the matrix fixes.
-/
import QCert.RealStabilizer.NormalForm
import QCert.RealStabilizer.Embed

namespace QCert.RealStabilizer

open SelingerClifford (PS PD actW actC toPS toPD set1 set2 set1_set1 set1_self set2_set2
  set2_self set1_c set2_c set2_a0 set2_b0 set2_a1 set2_b1 set2_a set2_b box_at place_merge1
  place_merge2 toPD1_pick toPD2_pick ZPS X0PS Supp actW_inj actW_surj actW_supp supp_toPS
  toPS_toPD IPS actW_IPS actW_up consPS consPS_inj ZPS_zero X0PS_eq supp_ZPS supp_X0PS
  supp_cons actW_append)

/-! ### Bounds and shifts of the boxes -/

theorem upN_bA (s i a : ℕ) : upN s (bA i a) = bA i (s + a) := by
  unfold bA; split <;> simp [upN_eq, Lt.upBy]

theorem upN_bB (s j a : ℕ) : upN s (bB j a) = bB j (s + a) := by
  unfold bB; split <;> simp [upN_eq, Lt.upBy] <;> omega

theorem upN_bC (s k a : ℕ) : upN s (bC k a) = bC k (s + a) := by
  unfold bC; split <;> simp [upN_eq, Lt.upBy]

theorem upN_bD (s l a : ℕ) : upN s (bD l a) = bD l (s + a) := by
  unfold bD; split <;> simp [upN_eq, Lt.upBy] <;> omega

theorem bnd_bA (i a : ℕ) : Bnd (a + 1) (bA i a) := by
  unfold bA; split <;> simp [Bnd, Lt.hi]

theorem bnd_bB (j a : ℕ) : Bnd (a + 2) (bB j a) := by
  unfold bB; split <;> simp [Bnd, Lt.hi]

theorem bnd_bC (k a : ℕ) : Bnd (a + 1) (bC k a) := by
  unfold bC; split <;> simp [Bnd, Lt.hi]

theorem bnd_bD (l a : ℕ) : Bnd (a + 2) (bD l a) := by
  unfold bD; split <;> simp [Bnd, Lt.hi]

theorem bnd_bE (h a : ℕ) : Bnd (a + 1) (bE h a) := by
  unfold bE; split <;> simp [Bnd, Lt.hi]

theorem bnd_mono {k k' : ℕ} {l : List Lt} (h : Bnd k l) (hk : k ≤ k') : Bnd k' l :=
  fun a ha => (h a ha).trans hk

theorem bnd_append' {k : ℕ} {l l' : List Lt} (h : Bnd k l) (h' : Bnd k l') : Bnd k (l ++ l') := by
  intro a ha
  rcases List.mem_append.1 ha with ha | ha
  exacts [h a ha, h' a ha]

theorem bnd_BC : ∀ (t : Ty) (c : ℕ) (js : List (Fin 4)) (k : Fin 2),
    Bnd (c + js.length + 1) (BC t c js k)
  | _, c, [], k => by simpa [BC] using bnd_bC (k.val + 1) c
  | t, c, j :: js, k => by
    simp only [BC, List.length_cons]
    exact bnd_append' (bnd_mono (bnd_bB _ c) (by omega))
      (by have := bnd_BC (tB t j) (c + 1) js k; rwa [show c + 1 + js.length + 1 =
        c + (js.length + 1) + 1 by omega] at this)

theorem bnd_DC : ∀ (ls : List (Fin 4)) (h : Fin 2), Bnd (ls.length + 1) (DC ls h)
  | [], h => by simpa [DC] using bnd_bE (h.val + 1) 0
  | l :: ls, h => by
    simp only [DC, List.length_cons]
    exact bnd_append' (bnd_bD _ _) (bnd_mono (bnd_DC ls h) (by omega))

theorem ZNormal.hi {n : ℕ} (L : ZNormal n) : Bnd n L.word := by
  have h := L.h
  exact bnd_append' (bnd_mono (bnd_bA _ _) (by omega)) (by have := bnd_BC (tA L.i) L.a L.js L.k; rwa [h] at this)

theorem XNormal.hi {n : ℕ} (M : XNormal n) : Bnd n M.word := by
  have := bnd_DC M.ls M.h; rwa [M.hl] at this

/-! ### The boxes on Pauli operators (Proposition 4.10) -/

/-- The Pauli operator `X^x Z` of a wire of type `t`: `Z` or `XZ`. -/
def tyX (t : Ty) : Fin 2 := if t then 1 else 0

/-- The operator `A_{i+1}` sends to `Z` or `XZ`: `Z`, `X`, `XZ`. -/
def xA : Fin 3 → Fin 2 := ![0, 1, 1]
def zA : Fin 3 → Fin 2 := ![1, 0, 1]
/-- The operator above the lower wire that the `B` gate `j` (and the `D`
gate `j`, below its upper wire) takes: `I`, `X`, `Z`, `XZ`. -/
def xQ : Fin 4 → Fin 2 := ![0, 1, 0, 1]
def zQ : Fin 4 → Fin 2 := ![0, 0, 1, 1]
/-- The phases of `C_{k+1}` and `E_{h+1}`. -/
def cC : Fin 2 → Fin 4 := ![0, 2]
def cE : Fin 2 → Fin 4 := ![0, 2]
/-- `D₄` exchanges `X` and `XZ` on its way down. -/
def dD : Fin 4 → Fin 2 := ![0, 0, 0, 1]

/-- The Clifford action of a real word on its own wires. -/
abbrev actR (k : ℕ) (l : List Lt) : PD k → PD k :=
  actC k (SelingerClifford.wc k (embW l))

theorem fA : ∀ (i : Fin 3) (p : Fin 4), actR 1 (bA (i.val + 1) 0)
    ⟨p, ![xA i], ![zA i]⟩ = ⟨p, ![tyX (tA i)], ![1]⟩ := by decide +kernel
theorem fB : ∀ (t : Ty) (j p : Fin 4), actR 2 (bB (j.val + 1) 0)
    ⟨p, ![tyX t, xQ j], ![1, zQ j]⟩ = ⟨p, ![0, tyX (tB t j)], ![0, 1]⟩ := by decide +kernel
theorem fC : ∀ (k : Fin 2) (p : Fin 4), actR 1 (bC (k.val + 1) 0)
    ⟨p + cC k, ![0], ![1]⟩ = ⟨p, ![0], ![1]⟩ := by decide +kernel
theorem fD : ∀ (l p : Fin 4) (t : Fin 2), actR 2 (bD (l.val + 1) 0)
    ⟨p, ![xQ l, 1], ![zQ l, t]⟩ = ⟨p, ![1, 0], ![t + dD l, 0]⟩ := by decide +kernel
theorem fDZ : ∀ (l p : Fin 4), actR 2 (bD (l.val + 1) 0)
    ⟨p, ![0, 0], ![0, 1]⟩ = ⟨p, ![0, 0], ![1, 0]⟩ := by decide +kernel
theorem fE : ∀ (h : Fin 2) (p : Fin 4), actR 1 (bE (h.val + 1) 0)
    ⟨p + cE h, ![1], ![0]⟩ = ⟨p, ![1], ![0]⟩ := by decide +kernel
theorem fEZ : ∀ (h : Fin 2) (p : Fin 4), actR 1 (bE (h.val + 1) 0)
    ⟨p, ![0], ![1]⟩ = ⟨p, ![0], ![1]⟩ := by decide +kernel

theorem shiftE {f : ℕ → ℕ → List Lt} (hf : ∀ s i a, upN s (f i a) = f i (s + a)) (i c : ℕ) :
    embW (f i c) = SelingerClifford.upN c (embW (f i 0)) := by
  rw [← embW_upN, hf, Nat.add_zero]

theorem boxA (i : Fin 3) (a : ℕ) (P : PS) (h1 : P.a a = xA i) (h2 : P.b a = zA i) :
    actW (embW (bA (i.val + 1) a)) P = set1 P a (tyX (tA i)) 1 P.c := by
  rw [shiftE upN_bA, box_at _ (embW_hi (bnd_bA _ 0)) a P (toPD1_pick a P _ _ _ rfl h1 h2)
    (fA i _), place_merge1]

theorem boxB (t : Ty) (j : Fin 4) (c : ℕ) (P : PS) (h1 : P.a c = tyX t) (h2 : P.b c = 1)
    (h3 : P.a (c + 1) = xQ j) (h4 : P.b (c + 1) = zQ j) :
    actW (embW (bB (bIdx t j) c)) P = set2 P c 0 0 (tyX (tB t j)) 1 P.c := by
  rw [bB_idx, shiftE upN_bB, box_at _ (embW_hi (bnd_bB _ 0)) c P
    (toPD2_pick c P _ _ _ _ _ rfl h1 h2 h3 h4) (fB t j _), place_merge2]

theorem boxC (k : Fin 2) (c : ℕ) (P : PS) (h1 : P.a c = 0) (h2 : P.b c = 1) :
    actW (embW (bC (k.val + 1) c)) P = set1 P c 0 1 (P.c - cC k) := by
  rw [shiftE upN_bC, box_at _ (embW_hi (bnd_bC _ 0)) c P
    (toPD1_pick c P _ _ _ (sub_add_cancel P.c (cC k)).symm h1 h2) (fC k _), place_merge1]

theorem boxD (l : Fin 4) (d : ℕ) (P : PS) (h1 : P.a d = xQ l) (h2 : P.b d = zQ l)
    (h3 : P.a (d + 1) = 1) :
    actW (embW (bD (l.val + 1) d)) P = set2 P d 1 (P.b (d + 1) + dD l) 0 0 P.c := by
  rw [shiftE upN_bD, box_at _ (embW_hi (bnd_bD _ 0)) d P
    (toPD2_pick d P _ _ _ _ _ rfl h1 h2 h3 rfl) (fD l _ _), place_merge2]

theorem boxDZ (l : Fin 4) (d : ℕ) (P : PS) (h1 : P.a d = 0) (h2 : P.b d = 0)
    (h3 : P.a (d + 1) = 0) (h4 : P.b (d + 1) = 1) :
    actW (embW (bD (l.val + 1) d)) P = set2 P d 0 1 0 0 P.c := by
  rw [shiftE upN_bD, box_at _ (embW_hi (bnd_bD _ 0)) d P
    (toPD2_pick d P _ _ _ _ _ rfl h1 h2 h3 h4) (fDZ l _), place_merge2]

theorem boxE (h : Fin 2) (P : PS) (h1 : P.a 0 = 1) (h2 : P.b 0 = 0) :
    actW (embW (bE (h.val + 1) 0)) P = set1 P 0 1 0 (P.c - cE h) := by
  have e : embW (bE (h.val + 1) 0) = SelingerClifford.upN 0 (embW (bE (h.val + 1) 0)) := rfl
  rw [e, box_at _ (embW_hi (bnd_bE _ 0)) 0 P
    (toPD1_pick 0 P _ _ _ (sub_add_cancel P.c (cE h)).symm h1 h2) (fE h _), place_merge1]

theorem boxEZ (h : Fin 2) (P : PS) (h1 : P.a 0 = 0) (h2 : P.b 0 = 1) :
    actW (embW (bE (h.val + 1) 0)) P = set1 P 0 0 1 P.c := by
  have e : embW (bE (h.val + 1) 0) = SelingerClifford.upN 0 (embW (bE (h.val + 1) 0)) := rfl
  rw [e, box_at _ (embW_hi (bnd_bE _ 0)) 0 P (toPD1_pick 0 P _ _ _ rfl h1 h2) (fEZ h _),
    place_merge1]

/-! ### Proposition 4.11: Z-circuits -/

/-- The Pauli operator the ladder `BC t c js k` sends to `Z` on its top wire:
`Z` or `XZ` on the wire `c` (by its type), and above it the operators the
`B` gates take. -/
def encBC : Ty → ℕ → List (Fin 4) → Fin 2 → PS
  | t, c, [], k => ⟨cC k, fun x => if x = c then tyX t else 0, fun x => if x = c then 1 else 0⟩
  | t, c, j :: js, k => set2 (encBC (tB t j) (c + 1) js k) c (tyX t) 1 (xQ j) (zQ j)
      (encBC (tB t j) (c + 1) js k).c

theorem encBC_below : ∀ (js : List (Fin 4)) (t : Ty) (c : ℕ) (k : Fin 2) (x : ℕ), x < c →
    (encBC t c js k).a x = 0 ∧ (encBC t c js k).b x = 0
  | [], t, c, k, x, h => by simp [encBC, show x ≠ c by omega]
  | j :: js, t, c, k, x, h => by
    simp only [encBC]
    rw [set2_a _ _ _ _ _ _ _ (by omega) (by omega), set2_b _ _ _ _ _ _ _ (by omega) (by omega)]
    exact encBC_below js (tB t j) (c + 1) k x (by omega)

theorem encBC_at (js : List (Fin 4)) (t : Ty) (c : ℕ) (k : Fin 2) :
    (encBC t c js k).a c = tyX t ∧ (encBC t c js k).b c = 1 := by
  cases js with
  | nil => simp [encBC]
  | cons j js => exact ⟨set2_a0 _ _ _ _ _ _ _, set2_b0 _ _ _ _ _ _ _⟩

theorem encBC_spec : ∀ (js : List (Fin 4)) (t : Ty) (c : ℕ) (k : Fin 2), tBs t js = false →
    actW (embW (BC t c js k)) (encBC t c js k) = ZPS (c + js.length)
  | [], t, c, k, ht => by
    simp only [tBs] at ht
    subst ht
    simp only [BC]
    rw [boxC k c _ (encBC_at [] false c k).1 (encBC_at [] false c k).2]
    ext y <;> simp only [set1, encBC, ZPS, Function.update_apply, sub_self, List.length_nil,
      Nat.add_zero] <;> split_ifs <;> rfl
  | j :: js, t, c, k, ht => by
    simp only [BC, embW_append, actW_append, encBC]
    rw [boxB t j c _ (set2_a0 _ _ _ _ _ _ _) (set2_b0 _ _ _ _ _ _ _) (set2_a1 _ _ _ _ _ _ _)
      (set2_b1 _ _ _ _ _ _ _), set2_set2, set2_c]
    have hb := encBC_below js (tB t j) (c + 1) k c (by omega)
    have ha := encBC_at js (tB t j) (c + 1) k
    rw [set2_self hb.1 hb.2 ha.1 ha.2, encBC_spec js (tB t j) (c + 1) k ht]
    congr 1; simp; omega

/-- The Pauli operator a Z-circuit sends to `Z` on the top wire. -/
def encL {n : ℕ} (L : ZNormal n) : PS :=
  set1 (encBC (tA L.i) L.a L.js L.k) L.a (xA L.i) (zA L.i) (encBC (tA L.i) L.a L.js L.k).c

/-- **Proposition 4.11, existence**: `L • encL L = Z` on the top wire. -/
theorem encL_spec {n : ℕ} (L : ZNormal n) : actW (embW L.word) (encL L) = ZPS (n - 1) := by
  simp only [ZNormal.word, embW_append, actW_append, encL]
  rw [boxA L.i L.a _ (by simp [set1]) (by simp [set1]), set1_set1, set1_c]
  have ha := encBC_at L.js (tA L.i) L.a L.k
  rw [set1_self ha.1 ha.2, encBC_spec _ _ _ _ L.ht]
  congr 1; have := L.h; omega

theorem cC_inj : ∀ k k' : Fin 2, cC k = cC k' → k = k' := by decide
theorem cE_inj : ∀ h h' : Fin 2, cE h = cE h' → h = h' := by decide
theorem Q_inj : ∀ j j' : Fin 4, xQ j = xQ j' → zQ j = zQ j' → j = j' := by decide
theorem A_inj : ∀ i i' : Fin 3, xA i = xA i' → zA i = zA i' → i = i' := by decide
theorem A_ne : ∀ i : Fin 3, ¬ (xA i = 0 ∧ zA i = 0) := by decide

theorem encBC_inj : ∀ (js js' : List (Fin 4)) (t : Ty) (c : ℕ) (k k' : Fin 2),
    js.length = js'.length → encBC t c js k = encBC t c js' k' → js = js' ∧ k = k'
  | [], [], _, c, k, k', _, h => ⟨rfl, cC_inj k k' (congrArg PS.c h)⟩
  | j :: js, j' :: js', t, c, k, k', hl, h => by
    simp only [encBC] at h
    have hj : j = j' := Q_inj j j'
      (by have := congrArg (fun P => P.a (c + 1)) h; simpa [set2_a1] using this)
      (by have := congrArg (fun P => P.b (c + 1)) h; simpa [set2_b1] using this)
    subst hj
    have e : ∀ (js : List (Fin 4)) (k : Fin 2),
        set2 (set2 (encBC (tB t j) (c + 1) js k) c (tyX t) 1 (xQ j) (zQ j)
          (encBC (tB t j) (c + 1) js k).c) c 0 0 (tyX (tB t j)) 1
          (encBC (tB t j) (c + 1) js k).c = encBC (tB t j) (c + 1) js k := by
      intro js k
      have hb := encBC_below js (tB t j) (c + 1) k c (by omega)
      have ha := encBC_at js (tB t j) (c + 1) k
      rw [set2_set2]
      exact set2_self hb.1 hb.2 ha.1 ha.2
    have h' := congrArg (fun P => set2 P c 0 0 (tyX (tB t j)) 1 P.c) h
    simp only [set2_c] at h'
    rw [e, e] at h'
    obtain ⟨h1, h2⟩ := encBC_inj js js' (tB t j) (c + 1) k k' (by simpa using hl) h'
    exact ⟨by rw [h1], h2⟩
  | [], _ :: _, _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, _, hl, _ => by simp at hl

/-- **Proposition 4.11, uniqueness**: a Z-circuit is determined by the
operator it sends to `Z` on the top wire. -/
theorem encL_inj {n : ℕ} {L L' : ZNormal n} (h : encL L = encL L') : L = L' := by
  obtain ⟨a, i, js, k, hn, ht⟩ := L
  obtain ⟨a', i', js', k', hn', ht'⟩ := L'
  simp only [encL] at h
  have key : ∀ {a a' : ℕ} {i i' : Fin 3} {js js' : List (Fin 4)} {k k' : Fin 2},
      a < a' → set1 (encBC (tA i) a js k) a (xA i) (zA i) (encBC (tA i) a js k).c ≠
        set1 (encBC (tA i') a' js' k') a' (xA i') (zA i') (encBC (tA i') a' js' k').c := by
    intro a a' i i' js js' k k' hlt he
    have h1 := congrArg (fun P => P.a a) he
    have h2 := congrArg (fun P => P.b a) he
    simp only [set1, Function.update_apply, if_true, show a ≠ a' by omega, if_false] at h1 h2
    exact A_ne i ⟨h1.trans (encBC_below js' (tA i') a' k' a hlt).1,
      h2.trans (encBC_below js' (tA i') a' k' a hlt).2⟩
  obtain rfl : a = a' := by
    rcases lt_trichotomy a a' with hlt | heq | hlt
    · exact absurd h (key hlt)
    · exact heq
    · exact absurd h.symm (key hlt)
  have hi : i = i' := A_inj i i'
    (by have := congrArg (fun P => P.a a) h; simpa [set1] using this)
    (by have := congrArg (fun P => P.b a) h; simpa [set1] using this)
  subst hi
  have e : ∀ (js : List (Fin 4)) (k : Fin 2),
      set1 (set1 (encBC (tA i) a js k) a (xA i) (zA i) (encBC (tA i) a js k).c) a (tyX (tA i)) 1
        (encBC (tA i) a js k).c = encBC (tA i) a js k := by
    intro js k
    have ha := encBC_at js (tA i) a k
    rw [set1_set1]
    exact set1_self ha.1 ha.2
  have h' := congrArg (fun P => set1 P a (tyX (tA i)) 1 P.c) h
  simp only [set1_c] at h'
  rw [e, e] at h'
  obtain ⟨rfl, rfl⟩ := encBC_inj js js' (tA i) a k k' (by omega) h'
  rfl

/-! ### Propositions 4.12 and 4.13: X-circuits -/

/-- The Pauli operator the ladder `DC ls h` sends to `X` on the wire `0`:
`X` or `XZ` on its top wire, below it the operators the `D` gates take. -/
def encDC : List (Fin 4) → Fin 2 → PS
  | [], h => ⟨cE h, fun x => if x = 0 then 1 else 0, fun _ => 0⟩
  | l :: ls, h => set2 (encDC ls h) ls.length (xQ l) (zQ l) 1
      ((encDC ls h).b ls.length + dD l) (encDC ls h).c

theorem encDC_top (ls : List (Fin 4)) (h : Fin 2) : (encDC ls h).a ls.length = 1 := by
  cases ls with
  | nil => simp [encDC]
  | cons l ls => exact set2_a1 _ _ _ _ _ _ _

theorem encDC_above : ∀ (ls : List (Fin 4)) (h : Fin 2) (x : ℕ), ls.length < x →
    (encDC ls h).a x = 0 ∧ (encDC ls h).b x = 0
  | [], h, x, hx => by simp [encDC, show x ≠ 0 by simp at hx; omega]
  | l :: ls, h, x, hx => by
    simp only [encDC]
    simp only [List.length_cons] at hx
    rw [set2_a _ _ _ _ _ _ _ (by omega) (by omega), set2_b _ _ _ _ _ _ _ (by omega) (by omega)]
    exact encDC_above ls h x (by omega)

theorem fin2_add_add : ∀ x y : Fin 2, x + y + y = x := by decide

/-- Undoing a step of `encDC`. -/
def recD (d : ℕ) (l : Fin 4) (P : PS) : PS := set2 P d 1 (P.b (d + 1) + dD l) 0 0 P.c

theorem unD (ls : List (Fin 4)) (h : Fin 2) (l : Fin 4) (d : ℕ) (hd : d = ls.length) :
    recD d l (set2 (encDC ls h) d (xQ l) (zQ l) 1 ((encDC ls h).b d + dD l)
      (encDC ls h).c) = encDC ls h := by
  subst hd
  have ht := encDC_top ls h
  have hab := encDC_above ls h (ls.length + 1) (by omega)
  simp only [recD, set2_b1, set2_c, fin2_add_add]
  rw [set2_set2]
  exact set2_self ht rfl hab.1 hab.2

/-- **Proposition 4.12, existence**: `M • encDC = X` on the wire `0`. -/
theorem encDC_spec : ∀ (ls : List (Fin 4)) (h : Fin 2),
    actW (embW (DC ls h)) (encDC ls h) = X0PS
  | [], h => by
    simp only [DC]
    rw [boxE h _ (by simp [encDC]) (by simp [encDC])]
    ext y <;> simp only [set1, encDC, X0PS, Function.update_apply, sub_self] <;>
      split_ifs <;> simp_all
  | l :: ls, h => by
    simp only [DC, embW_append, actW_append, encDC]
    rw [boxD l ls.length _ (set2_a0 _ _ _ _ _ _ _) (set2_b0 _ _ _ _ _ _ _)
      (set2_a1 _ _ _ _ _ _ _)]
    have := unD ls h l ls.length rfl
    simp only [recD, set2_b1, set2_c] at this
    rw [set2_b1, set2_c, this, encDC_spec ls h]

/-- **Proposition 4.13**: an X-circuit sends `Z` on the top wire to `Z` on
the wire `0`. -/
theorem DC_Z : ∀ (ls : List (Fin 4)) (h : Fin 2),
    actW (embW (DC ls h)) (ZPS ls.length) = ZPS 0
  | [], h => by
    simp only [DC, List.length_nil]
    rw [boxEZ h _ (by simp [ZPS]) (by simp [ZPS])]
    exact set1_self (by simp [ZPS]) (by simp [ZPS])
  | l :: ls, h => by
    simp only [DC, embW_append, actW_append, List.length_cons]
    rw [boxDZ l ls.length _ (by simp [ZPS]) (by simp [ZPS]) (by simp [ZPS]) (by simp [ZPS])]
    have e : set2 (ZPS (ls.length + 1)) ls.length 0 1 0 0 (ZPS (ls.length + 1)).c =
        ZPS ls.length := by
      ext y <;> simp only [set2, ZPS, Function.update_apply] <;> split_ifs <;> first | rfl | omega
    rw [e, DC_Z ls h]

theorem encDC_inj : ∀ (ls ls' : List (Fin 4)) (h h' : Fin 2),
    ls.length = ls'.length → encDC ls h = encDC ls' h' → ls = ls' ∧ h = h'
  | [], [], h, h', _, he => ⟨rfl, cE_inj h h' (congrArg PS.c he)⟩
  | l :: ls, l' :: ls', h, h', hl, he => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    simp only [encDC] at he
    have hl' : l = l' := Q_inj l l'
      (by have := congrArg (fun P => P.a ls.length) he; simpa [set2_a0, hl] using this)
      (by have := congrArg (fun P => P.b ls.length) he; simpa [set2_b0, hl] using this)
    subst hl'
    rw [← hl] at he
    have hr := congrArg (recD ls.length l) he
    rw [unD ls h l ls.length rfl, unD ls' h' l ls.length hl] at hr
    obtain ⟨h1, h2⟩ := encDC_inj ls ls' h h' hl hr
    exact ⟨by rw [h1], h2⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

/-- **Proposition 4.12, uniqueness**: an X-circuit is determined by the
operator it sends to `X` on the wire `0`. -/
theorem encM_inj {n : ℕ} {M M' : XNormal n} (h : encDC M.ls M.h = encDC M'.ls M'.h) :
    M = M' := by
  obtain ⟨ls, hh, hl⟩ := M
  obtain ⟨ls', hh', hl'⟩ := M'
  obtain ⟨rfl, rfl⟩ := encDC_inj ls ls' hh hh' (by omega) h
  rfl

/-! ### Supports -/

theorem encBC_above : ∀ (js : List (Fin 4)) (t : Ty) (c : ℕ) (k : Fin 2) (x : ℕ),
    c + js.length < x → (encBC t c js k).a x = 0 ∧ (encBC t c js k).b x = 0
  | [], t, c, k, x, h => by simp [encBC, show x ≠ c by simp at h; omega]
  | j :: js, t, c, k, x, h => by
    simp only [encBC]
    simp only [List.length_cons] at h
    rw [set2_a _ _ _ _ _ _ _ (by omega) (by omega), set2_b _ _ _ _ _ _ _ (by omega) (by omega)]
    exact encBC_above js (tB t j) (c + 1) k x (by omega)

theorem supp_encL {n : ℕ} (L : ZNormal n) : Supp n (encL L) := by
  intro x hx
  have h := L.h
  simp only [encL, set1, Function.update_apply, show x ≠ L.a by omega, if_false]
  exact encBC_above L.js (tA L.i) L.a L.k x (by omega)

theorem supp_encDC (ls : List (Fin 4)) (h : Fin 2) : Supp (ls.length + 1) (encDC ls h) :=
  fun x hx => encDC_above ls h x (by omega)

/-! ### Proposition 4.15 -/

theorem embL_up (a : Lt) : embL a.up = (embL a).map SelingerClifford.Lt.up := by
  cases a <;> rfl

theorem embW_map_up (l : List Lt) : embW (l.map Lt.up) = (embW l).map SelingerClifford.Lt.up := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, embW_cons, List.map_append, ih, embL_up]

theorem up_hi (a : Lt) : a.up.hi = a.hi + 1 ∨ a = .neg := by
  cases a <;> simp [Lt.up, Lt.hi]

theorem NF.word_hi : ∀ {n : ℕ} (N : NF n), Bnd n N.word
  | _, .scalar p => fun a ha => by rw [List.eq_of_mem_replicate ha]; simp [Lt.hi]
  | n + 1, .cons L M N => by
    simp only [NF.word]
    refine bnd_append' (bnd_append' L.hi M.hi) ?_
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    rcases up_hi b with e | e
    · rw [e]; have := NF.word_hi N b hb; omega
    · subst e; simp [Lt.up, Lt.hi]

/-- The scalar of a normal form. -/
def NF.sc : {n : ℕ} → NF n → Fin 2
  | _, .scalar p => p
  | _, .cons _ _ N => N.sc

/-- The normal form with another scalar. -/
def NF.setSc : {n : ℕ} → NF n → Fin 2 → NF n
  | _, .scalar _, q => .scalar q
  | _, .cons L M N, q => .cons L M (N.setSc q)

theorem NF.setSc_sc : ∀ {n : ℕ} (N : NF n), N.setSc N.sc = N
  | _, .scalar _ => rfl
  | _, .cons L M N => by simp only [NF.setSc, NF.sc, NF.setSc_sc N]

theorem NF.word_setSc : ∀ {n : ℕ} (N : NF n) (q : Fin 2),
    (N.setSc q).word = (N.setSc 0).word ++ List.replicate q.val .neg
  | _, .scalar _, q => by simp [NF.setSc, NF.word]
  | _, .cons L M N, q => by
    simp only [NF.setSc, NF.word, NF.word_setSc N q, List.map_append, List.append_assoc]
    simp [List.map_replicate, Lt.up]

/-- **Proposition 4.15, uniqueness up to the scalar**: two normal forms that
act alike on Pauli operators differ at most in their scalar. -/
theorem nf_act_unique : ∀ (n : ℕ) (N N' : NF n),
    (∀ P : PD n, actW (embW N.word) (toPS P) = actW (embW N'.word) (toPS P)) →
      N' = N.setSc N'.sc
  | 0, .scalar _, .scalar _, _ => rfl
  | n + 1, .cons L M N, .cons L' M' N', h => by
    have hup : ∀ (N : NF n), ∀ a ∈ embW (N.word.map Lt.up), a.hi ≤ n + 1 := by
      intro N
      apply embW_hi
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      rcases up_hi b with e | e
      · rw [e]; have := NF.word_hi N b hb; omega
      · subst e; simp [Lt.up, Lt.hi]
    have hML : M.ls.length = n := by have := M.hl; omega
    have hML' : M'.ls.length = n := by have := M'.hl; omega
    have split3 : ∀ (L : ZNormal (n + 1)) (M : XNormal (n + 1)) (N : NF n) (X : PS),
        actW (embW (NF.cons L M N).word) X =
          actW (embW (N.word.map Lt.up)) (actW (embW M.word) (actW (embW L.word) X)) := by
      intro L M N X
      simp only [NF.word, embW_append, actW_append]
    have fixZ : ∀ N : NF n, actW (embW (N.word.map Lt.up)) (ZPS 0) = ZPS 0 := by
      intro N; rw [embW_map_up, ZPS_zero, actW_up, actW_IPS]
    have fixX : ∀ N : NF n, actW (embW (N.word.map Lt.up)) X0PS = X0PS := by
      intro N; rw [embW_map_up, X0PS_eq, actW_up, actW_IPS]
    have hL : ∀ L : ZNormal (n + 1), ∀ a ∈ embW L.word, a.hi ≤ n + 1 := fun L => embW_hi L.hi
    have hM : ∀ M : XNormal (n + 1), ∀ a ∈ embW M.word, a.hi ≤ n + 1 := fun M => embW_hi M.hi
    -- Proposition 4.11: the Z-circuits agree
    obtain rfl : L = L' := by
      have h1 := h (toPD (n + 1) (encL L))
      rw [toPS_toPD (supp_encL L), split3, split3, encL_spec, Nat.add_sub_cancel] at h1
      have hZ : actW (embW M.word) (ZPS n) = ZPS 0 := by
        have := DC_Z M.ls M.h; rw [hML] at this; exact this
      rw [hZ, fixZ] at h1
      have h2 : actW (embW M'.word) (actW (embW L'.word) (encL L)) = ZPS 0 := by
        refine actW_inj (hup N') (actW_supp (hM M') (actW_supp (hL L') (supp_encL L)))
          (supp_ZPS (by omega)) ?_
        rw [← h1, fixZ]
      have hZ' : actW (embW M'.word) (ZPS n) = ZPS 0 := by
        have := DC_Z M'.ls M'.h; rw [hML'] at this; exact this
      have h3 : actW (embW L'.word) (encL L) = ZPS n :=
        actW_inj (hM M') (actW_supp (hL L') (supp_encL L)) (supp_ZPS (by omega))
          (h2.trans hZ'.symm)
      have h4 := encL_spec L'
      rw [Nat.add_sub_cancel] at h4
      exact encL_inj (actW_inj (hL L') (supp_encL L) (supp_encL L') (h3.trans h4.symm))
    -- Proposition 4.12: the X-circuits agree
    obtain rfl : M = M' := by
      have hs : Supp (n + 1) (encDC M.ls M.h) := by
        have := supp_encDC M.ls M.h; rwa [hML] at this
      obtain ⟨Q, hQ⟩ := actW_surj (hL L) hs
      have h1 := h Q
      rw [split3, split3, hQ] at h1
      have h1' : actW (embW (N.word.map Lt.up)) (actW (embW M.word) (encDC M.ls M.h)) = X0PS := by
        rw [show actW (embW M.word) (encDC M.ls M.h) = X0PS from encDC_spec M.ls M.h, fixX]
      rw [h1'] at h1
      have h2 : actW (embW M'.word) (encDC M.ls M.h) = X0PS := by
        refine actW_inj (hup N') (actW_supp (hM M') hs) (supp_X0PS (by omega)) ?_
        rw [← h1, fixX]
      have h3 := encDC_spec M'.ls M'.h
      have h4 : encDC M.ls M.h = encDC M'.ls M'.h :=
        actW_inj (hM M') hs (by have := supp_encDC M'.ls M'.h; rwa [hML'] at this)
          (h2.trans h3.symm)
      exact encM_inj h4
    -- the rest is a normal form on the top `n` wires
    have hrest : ∀ P : PD n, actW (embW N.word) (toPS P) = actW (embW N'.word) (toPS P) := by
      intro P
      have hLM : ∀ a ∈ embW L.word ++ embW M.word, a.hi ≤ n + 1 := by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        exacts [hL L a ha, hM M a ha]
      obtain ⟨Q, hQ⟩ := actW_surj hLM (supp_cons P)
      have hQ' : actW (embW M.word) (actW (embW L.word) (toPS Q)) = consPS 0 0 (toPS P) := by
        rw [← actW_append]; exact hQ
      have h1 := h Q
      rw [split3, split3, hQ', embW_map_up, embW_map_up, actW_up, actW_up] at h1
      exact consPS_inj h1
    have := nf_act_unique n N N' hrest
    show NF.cons L M N' = NF.cons L M (N.setSc N'.sc)
    exact congrArg (NF.cons L M) this

/-! ### The scalar -/

theorem sem_neg_pow {n : ℕ} (q : ℕ) :
    (S.sem n (wc n (List.replicate q .neg))).1 = (-1 : ℝ) ^ q • 1 := by
  induction q with
  | zero => simp [wc]
  | succ q ih =>
    rw [List.replicate_succ, wc, map_mul, Submonoid.coe_mul, ih]
    show ((-1 : ℝ) ^ q • 1) * (S.gen (Gen.gate0 Gate.neg)).1 = _
    show ((-1 : ℝ) ^ q • 1) * (((-1 : ℝ)) • 1) = _
    simp only [smul_mul_smul_comm, mul_one, pow_succ]

/-- **Proposition 4.15**: distinct normal forms denote distinct operators. -/
theorem normal_unique' {n : ℕ} (N N' : NF n) (h : S.sem n N.circ = S.sem n N'.circ) :
    N = N' := by
  have hact : ∀ P : PD n, actW (embW N.word) (toPS P) = actW (embW N'.word) (toPS P) :=
    actW_eq_of_sem (NF.word_hi N) (NF.word_hi N') h
  have e := nf_act_unique n N N' hact
  have hw : ∀ q : Fin 2, S.sem n (N.setSc q).circ =
      S.sem n (wc n (List.replicate q.val .neg)) * S.sem n (N.setSc 0).circ := by
    intro q
    simp only [NF.circ, NF.word_setSc N q, wc_append, map_mul]
  have h' : S.sem n (N.setSc N.sc).circ = S.sem n (N.setSc N'.sc).circ := by
    rw [NF.setSc_sc, ← e]; exact h
  rw [hw N.sc, hw N'.sc] at h'
  have h'' := mul_right_cancel h'
  have hv := congrArg Subtype.val h''
  rw [sem_neg_pow, sem_neg_pow] at hv
  have hq := congrFun (congrFun hv (fun _ => 0)) (fun _ => 0)
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at hq
  have key : ∀ a b : Fin 2, (-1 : ℝ) ^ (a : ℕ) = (-1) ^ (b : ℕ) → a = b := by
    intro a b hab; fin_cases a <;> fin_cases b <;> first | rfl | norm_num at hab
  have hsc : N.sc = N'.sc := key _ _ hq
  rw [e, ← hsc, NF.setSc_sc]

end QCert.RealStabilizer
