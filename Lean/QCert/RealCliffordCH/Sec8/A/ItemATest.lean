import QCert.RealCliffordCH.Sec8.A.ItemATools
namespace QCert.RealCliffordCH.Sec8
example {n g y : ℕ} (h8 : 8 ≤ 2 ^ n) (hg : g < 2 ^ n) (hy : y < 2 ^ n) :
    ∀ x ∈ [NL.zx g 1 y, NL.zz 1 g], x.Bd n := by
  simp only [List.forall_mem_cons, NL.Bd, List.mem_nil_iff, false_implies, implies_true, and_true]
  trace_state
  omega
end QCert.RealCliffordCH.Sec8
