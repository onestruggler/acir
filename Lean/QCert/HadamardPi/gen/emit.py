from deriv import lean_word
from good4 import good
def lean_good(name, w, par):
    U, j = good(w, par)
    assert j is not None
    vec = ", ".join(f"⟨{e.x.lean()}, {e.y.lean()}⟩" for e in U)
    return (f"theorem {name} : Good4 {par} {lean_word(w)} := by\n"
            f"  intro a b c mm hs\n"
            f"  refine ⟨![{vec}], fun j => ?_, {j}, ?_⟩\n"
            f"  · fin_cases j <;> apply Zsqrtd.ext <;>\n"
            f"      simp [scw, scg, hcntw, hcnt, pow_succ, mul_assoc] <;> omega\n"
            f"  · simp only [Matrix.cons_val, Int.not_odd_iff_even, Int.even_iff]; omega\n")
