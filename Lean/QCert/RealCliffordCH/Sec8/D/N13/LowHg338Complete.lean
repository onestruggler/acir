/- Every colouring of (338) on four wires. -/
import QCert.RealCliffordCH.Sec8.D.N13.E338Merge
import QCert.RealCliffordCH.Sec8.D.N13.LowHg338

namespace QCert.RealCliffordCH.Sec8.D.N13

theorem comm338_all_4 (ih : IH 4) (x y : ℕ → Bool) (c : Bool) :
    Comm 4 (bA 4 x c) (mc 4 .hg [1, 0] (colOn 2 4 y)) :=
  comm338_from_diff 4 (by omega) ih (fun x y hxy c => comm338_4 ih x y hxy c)
    (comm335_4 ih) x y c

end QCert.RealCliffordCH.Sec8.D.N13
