/- Small-width commutation certificates for box and controlled H. -/
import QCert.RealCliffordCH.Sec8.D.W4.B4
import QCert.RealCliffordCH.Sec8.D.W4.HgMerge
import QCert.RealCliffordCH.Sec8.D.W4.BoxCommLow

namespace QCert.RealCliffordCH.Sec8.D.W4LowHg
open Circuit WE WS Net
open Eng (L)
open W4 (tH tZ tC tK tS tg tp)
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def L207f2 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .hg [0, 1] [(3, true), (2, false)]]

def R207f2 : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T207f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .hg [0, 1] [(3, true), (2, true)]], [tg .hg [0, 1] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run207f2 : check 3 T207f2 L207f2 R207f2
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t207f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L207f2) (wcT 4 R207f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, true), (2, true)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (W4.t207 ih) (AllD.nil 4))) run207f2

def L207f2f3 : List Tk := [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .hg [0, 1] [(3, false), (2, false)]]

def R207f2f3 : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]]

def T207f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [0], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [0]])]

theorem run207f2f3 : check 3 T207f2f3 L207f2f3 R207f2f3
    [.rw 1 0 true,
    .sem 1 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [0]] 1,
    .sem 2 2 [] 0,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .sem 1 2 [tp 1 [L.H 0, L.Z 0, L.H 0] [0], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 1,
    .sem 2 2 [] 0] = true := by
  decide +kernel

theorem t207f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L207f2f3) (wcT 4 R207f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (t207f2 ih) (AllD.nil 4))) run207f2f3

def L194f2 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def R194f2 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]]

def T194f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]])]

theorem run194f2 : check 3 T194f2 L194f2 R194f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem t194f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L194f2) (wcT 4 R194f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, false), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .hg [1, 0] [(3, true), (2, true)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (W4.t194 ih) (AllD.nil 4)))) run194f2

def L195f2 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def R195f2 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]]

def T195f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, false), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]])]

theorem run195f2 : check 3 T195f2 L195f2 R195f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem t195f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L195f2) (wcT 4 R195f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [0] [(3, false), (2, false), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .hg [1, 0] [(3, true), (2, true)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (W4.t195 ih) (AllD.nil 4)))) run195f2

def L195f2f3 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def R195f2f3 : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]]

def T195f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, false), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, false), (2, false)]]),
  ([tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]])]

theorem run195f2f3 : check 3 T195f2f3 L195f2f3 R195f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem t195f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L195f2f3) (wcT 4 R195f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [0] [(3, false), (2, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .hg [1, 0] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (t195f2 ih) (AllD.nil 4)))) run195f2f3

def L197f2 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [1] [(3, false), (2, true), (0, true)]]

def R197f2 : List Tk := [tg .box [1] [(3, false), (2, true), (0, true)], tg .hg [1, 0] [(3, true), (2, false)]]

def T197f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [1] [(3, false), (2, false), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [1] [(3, false), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tg .hg [1, 0] [(3, true), (2, true)], tg .box [1] [(3, false), (2, false), (0, true)]], [tg .box [1] [(3, false), (2, false), (0, true)], tg .hg [1, 0] [(3, true), (2, true)]])]

theorem run197f2 : check 3 T197f2 L197f2 R197f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem t197f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 L197f2) (wcT 4 R197f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .box [1] [(3, false), (2, false), (0, true)] [(3, false), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .hg [1, 0] [(3, true), (2, true)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (W4.t197 ih) (AllD.nil 4)))) run197f2

def L197f2f3 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [1] [(3, true), (2, true), (0, true)]]

def R197f2f3 : List Tk := [tg .box [1] [(3, true), (2, true), (0, true)], tg .hg [1, 0] [(3, false), (2, false)]]

def T197f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [1] [(3, false), (2, true), (0, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [1] [(3, true), (2, true), (0, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, false), (2, false)]]),
  ([tg .hg [1, 0] [(3, true), (2, false)], tg .box [1] [(3, false), (2, true), (0, true)]], [tg .box [1] [(3, false), (2, true), (0, true)], tg .hg [1, 0] [(3, true), (2, false)]])]

theorem run197f2f3 : check 3 T197f2f3 L197f2f3 R197f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem t197f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 L197f2f3) (wcT 4 R197f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .box [1] [(3, false), (2, true), (0, true)] [(3, true), (2, true), (0, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .hg [1, 0] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (t197f2 ih) (AllD.nil 4)))) run197f2f3

def LHg337BaseFF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]]

def RHg337BaseFF : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def THg337BaseFF : Tbl := [([tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]])]

theorem runHg337BaseFF : check 3 THg337BaseFF LHg337BaseFF RHg337BaseFF
    [.rw 0 0 true] = true := by
  decide +kernel

theorem tHg337BaseFF (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFF) (wcT 4 RHg337BaseFF) :=
  check_sound ih (AllD.cons (rel_entry (W4.havail4b ih) [0] (by decide +kernel) (t197f2f3 ih)) (AllD.nil 4)) runHg337BaseFF

def LHg337BaseFFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]]

def RHg337BaseFFf2 : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def THg337BaseFFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg337BaseFFf2 : check 3 THg337BaseFFf2 LHg337BaseFFf2 RHg337BaseFFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseFFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFFf2) (wcT 4 RHg337BaseFFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, false), (2, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseFF ih) (AllD.nil 4)))) runHg337BaseFFf2

def LHg337BaseFFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]]

def RHg337BaseFFf3 : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def THg337BaseFFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg337BaseFFf3 : check 3 THg337BaseFFf3 LHg337BaseFFf3 RHg337BaseFFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseFFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFFf3) (wcT 4 RHg337BaseFFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseFF ih) (AllD.nil 4)))) runHg337BaseFFf3

def LHg337BaseFFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [0, 1] [(3, true), (2, true)]]

def RHg337BaseFFf2f3 : List Tk := [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def THg337BaseFFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHg337BaseFFf2f3 : check 3 THg337BaseFFf2f3 LHg337BaseFFf2f3 RHg337BaseFFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseFFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFFf2f3) (wcT 4 RHg337BaseFFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseFFf2 ih) (AllD.nil 4)))) runHg337BaseFFf2f3

def LHg337BaseFT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]]

def RHg337BaseFT : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def THg337BaseFT : Tbl := [([tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]])]

theorem runHg337BaseFT : check 3 THg337BaseFT LHg337BaseFT RHg337BaseFT
    [.rw 0 0 true] = true := by
  decide +kernel

theorem tHg337BaseFT (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFT) (wcT 4 RHg337BaseFT) :=
  check_sound ih (AllD.cons (rel_entry (W4.havail4b ih) [0] (by decide +kernel) (W4.t196f2 ih)) (AllD.nil 4)) runHg337BaseFT

def LHg337BaseFTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [0, 1] [(3, true), (2, true)]]

def RHg337BaseFTf2 : List Tk := [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def THg337BaseFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg337BaseFTf2 : check 3 THg337BaseFTf2 LHg337BaseFTf2 RHg337BaseFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseFTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFTf2) (wcT 4 RHg337BaseFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, true), (2, false)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseFT ih) (AllD.nil 4)))) runHg337BaseFTf2

def LHg337BaseFTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]]

def RHg337BaseFTf3 : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def THg337BaseFTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg337BaseFTf3 : check 3 THg337BaseFTf3 LHg337BaseFTf3 RHg337BaseFTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseFTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFTf3) (wcT 4 RHg337BaseFTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseFT ih) (AllD.nil 4)))) runHg337BaseFTf3

def LHg337BaseFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]]

def RHg337BaseFTf2f3 : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def THg337BaseFTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [0, 1] [(3, true), (2, true)]], [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHg337BaseFTf2f3 : check 3 THg337BaseFTf2f3 LHg337BaseFTf2f3 RHg337BaseFTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseFTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseFTf2f3) (wcT 4 RHg337BaseFTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, true), (2, true)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseFTf2 ih) (AllD.nil 4)))) runHg337BaseFTf2f3

def LHg337BaseTF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]]

def RHg337BaseTF : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def THg337BaseTF : Tbl := [([tg .hg [0, 1] [(2, true), (3, false)]], [tg .hg [0, 1] [(3, false), (2, true)]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .hg [0, 1] [(2, true), (3, false)], tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)], tg .hg [0, 1] [(2, true), (3, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)]]),
  ([tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(2, true), (3, false)]])]

theorem runHg337BaseTF : check 3 THg337BaseTF LHg337BaseTF RHg337BaseTF
    [.rw 1 0 true,
    .rw 0 1 true,
    .rw 0 2 true,
    .rw 1 3 true,
    .rw 0 4 true] = true := by
  decide +kernel

theorem tHg337BaseTF (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseTF) (wcT 4 RHg337BaseTF) :=
  check_sound ih (AllD.cons (g_entry .hg [0, 1] [(2, true), (3, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(2, true), (3, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [0, 2] (by decide +kernel) (W4.t196f2 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (3, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .hg [0, 1] [(3, false), (2, true)] [(2, true), (3, false)] (by decide +kernel)) (AllD.nil 4)))))) runHg337BaseTF

def LHg337BaseTFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]]

def RHg337BaseTFf2 : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def THg337BaseTFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg337BaseTFf2 : check 3 THg337BaseTFf2 LHg337BaseTFf2 RHg337BaseTFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseTFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseTFf2) (wcT 4 RHg337BaseTFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, false), (2, true)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseTF ih) (AllD.nil 4)))) runHg337BaseTFf2

def LHg337BaseTFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, true)]]

def RHg337BaseTFf3 : List Tk := [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def THg337BaseTFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg337BaseTFf3 : check 3 THg337BaseTFf3 LHg337BaseTFf3 RHg337BaseTFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseTFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseTFf3) (wcT 4 RHg337BaseTFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseTF ih) (AllD.nil 4)))) runHg337BaseTFf3

def LHg337BaseTFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]]

def RHg337BaseTFf2f3 : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def THg337BaseTFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHg337BaseTFf2f3 : check 3 THg337BaseTFf2f3 LHg337BaseTFf2f3 RHg337BaseTFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg337BaseTFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg337BaseTFf2f3) (wcT 4 RHg337BaseTFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg337BaseTFf2 ih) (AllD.nil 4)))) runHg337BaseTFf2f3

def LHg338BaseFF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]]

def RHg338BaseFF : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def THg338BaseFF : Tbl := [([tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]])]

theorem runHg338BaseFF : check 3 THg338BaseFF LHg338BaseFF RHg338BaseFF
    [.rw 0 0 true] = true := by
  decide +kernel

theorem tHg338BaseFF (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFF) (wcT 4 RHg338BaseFF) :=
  check_sound ih (AllD.cons (t195f2f3 ih) (AllD.nil 4)) runHg338BaseFF

def LHg338BaseFFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, false)]]

def RHg338BaseFFf1 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def THg338BaseFFf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseFFf1 : check 3 THg338BaseFFf1 LHg338BaseFFf1 RHg338BaseFFf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [] 0,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf1) (wcT 4 RHg338BaseFFf1) :=
  check_sound ih (AllD.cons (rel_entry (W4.havail4b ih) [0] (by decide +kernel) (t207f2f3 ih)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFF ih) (AllD.nil 4)))) runHg338BaseFFf1

def LHg338BaseFFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]]

def RHg338BaseFFf2 : List Tk := [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def THg338BaseFFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseFFf2 : check 3 THg338BaseFFf2 LHg338BaseFFf2 RHg338BaseFFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf2) (wcT 4 RHg338BaseFFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [1, 0] [(3, false), (2, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseFF ih) (AllD.nil 4)))) runHg338BaseFFf2

def LHg338BaseFFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [1, 0] [(3, false), (2, true)]]

def RHg338BaseFFf1f2 : List Tk := [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def THg338BaseFFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runHg338BaseFFf1f2 : check 3 THg338BaseFFf1f2 LHg338BaseFFf1f2 RHg338BaseFFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf1f2) (wcT 4 RHg338BaseFFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [1, 0] [(3, false), (2, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFFf1 ih) (AllD.nil 4)))) runHg338BaseFFf1f2

def LHg338BaseFFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]]

def RHg338BaseFFf3 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def THg338BaseFFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseFFf3 : check 3 THg338BaseFFf3 LHg338BaseFFf3 RHg338BaseFFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf3) (wcT 4 RHg338BaseFFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseFF ih) (AllD.nil 4)))) runHg338BaseFFf3

def LHg338BaseFFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .hg [1, 0] [(3, true), (2, false)]]

def RHg338BaseFFf1f3 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def THg338BaseFFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runHg338BaseFFf1f3 : check 3 THg338BaseFFf1f3 LHg338BaseFFf1f3 RHg338BaseFFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf1f3) (wcT 4 RHg338BaseFFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFFf1 ih) (AllD.nil 4)))) runHg338BaseFFf1f3

def LHg338BaseFFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def RHg338BaseFFf2f3 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def THg338BaseFFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHg338BaseFFf2f3 : check 3 THg338BaseFFf2f3 LHg338BaseFFf2f3 RHg338BaseFFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf2f3) (wcT 4 RHg338BaseFFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseFFf2 ih) (AllD.nil 4)))) runHg338BaseFFf2f3

def LHg338BaseFFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .hg [1, 0] [(3, true), (2, true)]]

def RHg338BaseFFf1f2f3 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def THg338BaseFFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runHg338BaseFFf1f2f3 : check 3 THg338BaseFFf1f2f3 LHg338BaseFFf1f2f3 RHg338BaseFFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFFf1f2f3) (wcT 4 RHg338BaseFFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFFf1f2 ih) (AllD.nil 4)))) runHg338BaseFFf1f2f3

def LHg338BaseFT : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]]

def RHg338BaseFT : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]]

def THg338BaseFT : Tbl := [([tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]])]

theorem runHg338BaseFT : check 3 THg338BaseFT LHg338BaseFT RHg338BaseFT
    [.rw 0 0 true] = true := by
  decide +kernel

theorem tHg338BaseFT (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFT) (wcT 4 RHg338BaseFT) :=
  check_sound ih (AllD.cons (t194f2 ih) (AllD.nil 4)) runHg338BaseFT

def LHg338BaseFTf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, true), (2, false)]]

def RHg338BaseFTf1 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def THg338BaseFTf1 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .hg [1, 0] [(3, true), (2, false)]], [tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]], [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseFTf1 : check 3 THg338BaseFTf1 LHg338BaseFTf1 RHg338BaseFTf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 0 0 false,
    .sem 1 2 [] 0,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf1) (wcT 4 RHg338BaseFTf1) :=
  check_sound ih (AllD.cons (rel_entry (W4.havail4b ih) [0] (by decide +kernel) (t207f2 ih)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFT ih) (AllD.nil 4)))) runHg338BaseFTf1

def LHg338BaseFTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def RHg338BaseFTf2 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]]

def THg338BaseFTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]], [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseFTf2 : check 3 THg338BaseFTf2 LHg338BaseFTf2 RHg338BaseFTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf2) (wcT 4 RHg338BaseFTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [1, 0] [(3, true), (2, false)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseFT ih) (AllD.nil 4)))) runHg338BaseFTf2

def LHg338BaseFTf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [1, 0] [(3, true), (2, true)]]

def RHg338BaseFTf1f2 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def THg338BaseFTf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, true), (2, false)]], [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runHg338BaseFTf1f2 : check 3 THg338BaseFTf1f2 LHg338BaseFTf1f2 RHg338BaseFTf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf1f2) (wcT 4 RHg338BaseFTf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [1, 0] [(3, true), (2, false)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFTf1 ih) (AllD.nil 4)))) runHg338BaseFTf1f2

def LHg338BaseFTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]]

def RHg338BaseFTf3 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, false), (2, true), (1, true)]]

def THg338BaseFTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]], [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseFTf3 : check 3 THg338BaseFTf3 LHg338BaseFTf3 RHg338BaseFTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf3) (wcT 4 RHg338BaseFTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseFT ih) (AllD.nil 4)))) runHg338BaseFTf3

def LHg338BaseFTf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, false)]]

def RHg338BaseFTf1f3 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def THg338BaseFTf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, true), (2, false)]], [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runHg338BaseFTf1f3 : check 3 THg338BaseFTf1f3 LHg338BaseFTf1f3 RHg338BaseFTf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf1f3) (wcT 4 RHg338BaseFTf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFTf1 ih) (AllD.nil 4)))) runHg338BaseFTf1f3

def LHg338BaseFTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]]

def RHg338BaseFTf2f3 : List Tk := [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, false), (2, false), (1, true)]]

def THg338BaseFTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]], [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHg338BaseFTf2f3 : check 3 THg338BaseFTf2f3 LHg338BaseFTf2f3 RHg338BaseFTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf2f3) (wcT 4 RHg338BaseFTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, true), (2, true)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseFTf2 ih) (AllD.nil 4)))) runHg338BaseFTf2f3

def LHg338BaseFTf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .hg [1, 0] [(3, false), (2, true)]]

def RHg338BaseFTf1f2f3 : List Tk := [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def THg338BaseFTf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [1, 0] [(3, true), (2, true)]], [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runHg338BaseFTf1f2f3 : check 3 THg338BaseFTf1f2f3 LHg338BaseFTf1f2f3 RHg338BaseFTf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseFTf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseFTf1f2f3) (wcT 4 RHg338BaseFTf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, true), (2, true)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseFTf1f2 ih) (AllD.nil 4)))) runHg338BaseFTf1f2f3

def LHg338BaseTF : List Tk := [tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]]

def RHg338BaseTF : List Tk := [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]]

def THg338BaseTF : Tbl := [([tg .hg [1, 0] [(2, true), (3, false)]], [tg .hg [1, 0] [(3, false), (2, true)]]),
  ([tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(3, true), (2, true), (1, true)]]),
  ([tg .hg [1, 0] [(2, true), (3, false)], tg .box [0] [(2, true), (3, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)], tg .hg [1, 0] [(2, true), (3, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, true), (1, true)]]),
  ([tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(2, true), (3, false)]])]

theorem runHg338BaseTF : check 3 THg338BaseTF LHg338BaseTF RHg338BaseTF
    [.rw 1 0 true,
    .rw 0 1 true,
    .rw 0 2 true,
    .rw 1 3 true,
    .rw 0 4 true] = true := by
  decide +kernel

theorem tHg338BaseTF (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTF) (wcT 4 RHg338BaseTF) :=
  check_sound ih (AllD.cons (g_entry .hg [1, 0] [(2, true), (3, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(2, true), (3, true), (1, true)] [(3, true), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [2] (by decide +kernel) (t194f2 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(2, true), (3, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .hg [1, 0] [(3, false), (2, true)] [(2, true), (3, false)] (by decide +kernel)) (AllD.nil 4)))))) runHg338BaseTF

def LHg338BaseTFf1 : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, true)]]

def RHg338BaseTFf1 : List Tk := [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def THg338BaseTFf1 : Tbl := [([tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(2, true), (3, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .hg [1, 0] [(2, true), (3, false)]], [tg .hg [1, 0] [(2, true), (3, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]]),
  ([tg .hg [1, 0] [(2, true), (3, false)]], [tg .hg [1, 0] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [1], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [1]], [tg .box [0] [(3, true), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseTFf1 : check 3 THg338BaseTFf1 LHg338BaseTFf1 RHg338BaseTFf1
    [.sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 0 false,
    .rw 1 1 true,
    .rw 2 2 false,
    .rw 0 3 true,
    .sem 2 2 [] 0,
    .rw 1 4 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [1], tp 1 [L.H 0, L.Z 0, L.H 0] [1]] 0,
    .rw 1 2 true,
    .rw 0 1 false,
    .rw 0 0 true,
    .sem 1 2 [] 0,
    .rw 1 3 false] = true := by
  decide +kernel

theorem tHg338BaseTFf1 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf1) (wcT 4 RHg338BaseTFf1) :=
  check_sound ih (AllD.cons (g_entry .hg [1, 0] [(3, false), (2, true)] [(2, true), (3, false)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [0, 2] (by decide +kernel) (t207f2 ih)) (AllD.cons (g_entry .hg [1, 0] [(2, true), (3, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 1 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseTF ih) (AllD.nil 4)))))) runHg338BaseTFf1

def LHg338BaseTFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]]

def RHg338BaseTFf2 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, true)]]

def THg338BaseTFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseTFf2 : check 3 THg338BaseTFf2 LHg338BaseTFf2 RHg338BaseTFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseTFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf2) (wcT 4 RHg338BaseTFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [1, 0] [(3, false), (2, true)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseTF ih) (AllD.nil 4)))) runHg338BaseTFf2

def LHg338BaseTFf1f2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [1, 0] [(3, false), (2, false)]]

def RHg338BaseTFf1f2 : List Tk := [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def THg338BaseTFf1f2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [1, 0] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [1, 0] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runHg338BaseTFf1f2 : check 3 THg338BaseTFf1f2 LHg338BaseTFf1f2 RHg338BaseTFf1f2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseTFf1f2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf1f2) (wcT 4 RHg338BaseTFf1f2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [1, 0] [(3, false), (2, true)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseTFf1 ih) (AllD.nil 4)))) runHg338BaseTFf1f2

def LHg338BaseTFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, true)], tg .hg [1, 0] [(3, true), (2, true)]]

def RHg338BaseTFf3 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, false), (2, true), (1, true)]]

def THg338BaseTFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runHg338BaseTFf3 : check 3 THg338BaseTFf3 LHg338BaseTFf3 RHg338BaseTFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseTFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf3) (wcT 4 RHg338BaseTFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseTF ih) (AllD.nil 4)))) runHg338BaseTFf3

def LHg338BaseTFf1f3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .hg [1, 0] [(3, true), (2, true)]]

def RHg338BaseTFf1f3 : List Tk := [tg .hg [1, 0] [(3, true), (2, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def THg338BaseTFf1f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [1, 0] [(3, false), (2, true)]], [tg .hg [1, 0] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runHg338BaseTFf1f3 : check 3 THg338BaseTFf1f3 LHg338BaseTFf1f3 RHg338BaseTFf1f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseTFf1f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf1f3) (wcT 4 RHg338BaseTFf1f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseTFf1 ih) (AllD.nil 4)))) runHg338BaseTFf1f3

def LHg338BaseTFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, true)], tg .hg [1, 0] [(3, true), (2, false)]]

def RHg338BaseTFf2f3 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, false), (2, false), (1, true)]]

def THg338BaseTFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHg338BaseTFf2f3 : check 3 THg338BaseTFf2f3 LHg338BaseTFf2f3 RHg338BaseTFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseTFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf2f3) (wcT 4 RHg338BaseTFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (tHg338BaseTFf2 ih) (AllD.nil 4)))) runHg338BaseTFf2f3

def LHg338BaseTFf1f2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .hg [1, 0] [(3, true), (2, false)]]

def RHg338BaseTFf1f2f3 : List Tk := [tg .hg [1, 0] [(3, true), (2, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def THg338BaseTFf1f2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [1, 0] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [1, 0] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [1, 0] [(3, false), (2, false)]], [tg .hg [1, 0] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runHg338BaseTFf1f2f3 : check 3 THg338BaseTFf1f2f3 LHg338BaseTFf1f2f3 RHg338BaseTFf1f2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tHg338BaseTFf1f2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHg338BaseTFf1f2f3) (wcT 4 RHg338BaseTFf1f2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [1, 0] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tHg338BaseTFf1f2 ih) (AllD.nil 4)))) runHg338BaseTFf1f2f3

def LHgDeff2 : List Tk := [tg .hg [0, 1] [(3, true), (2, false)]]

def RHgDeff2 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def THgDeff2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, true), (2, false)]]),
  ([tg .hg [0, 1] [(3, true), (2, true)]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(3, true), (2, true), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, true)]])]

theorem runHgDeff2 : check 3 THgDeff2 LHgDeff2 RHgDeff2
    [.rw 0 0 true,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 5 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .sem 0 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 3,
    .sem 1 2 [] 0,
    .rw 1 2 false,
    .sem 2 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 3,
    .sem 3 2 [] 0] = true := by
  decide +kernel

theorem tHgDeff2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHgDeff2) (wcT 4 RHgDeff2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, true), (2, true)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (W4.tHgDef ih) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, true)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.nil 4)))) runHgDeff2

def LHgDeff2f3 : List Tk := [tg .hg [0, 1] [(3, false), (2, false)]]

def RHgDeff2f3 : List Tk := [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(3, false), (2, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]

def THgDeff2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, false), (2, false)]]),
  ([tg .hg [0, 1] [(3, true), (2, false)]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, true)]])]

theorem runHgDeff2f3 : check 3 THgDeff2f3 LHgDeff2f3 RHgDeff2f3
    [.rw 0 0 true,
    .rw 1 1 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 5 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .sem 0 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 2,
    .sem 1 2 [] 0,
    .rw 1 2 false,
    .sem 2 2 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 2,
    .sem 3 2 [] 0] = true := by
  decide +kernel

theorem tHgDeff2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LHgDeff2f3) (wcT 4 RHgDeff2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (tHgDeff2 ih) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, true)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.nil 4)))) runHgDeff2f3

def LCtrlHg337FF : List Tk := [tp 2 [L.C 0] [2, 3], tg .hg [0, 1] [(3, false), (2, false)]]

def RCtrlHg337FF : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tp 2 [L.C 0] [2, 3]]

def TCtrlHg337FF : Tbl := [([tg .hg [0, 1] [(3, false), (2, false)]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(3, false), (2, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]),
  ([tg .box [0] [(1, true), (3, false), (2, false)]], [tg .box [0] [(3, false), (2, false), (1, true)]]),
  ([tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [2, 3], tg .box [0] [(1, true), (3, false), (2, false)]], [tg .box [0] [(1, true), (3, false), (2, false)], tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [2, 3]]),
  ([tg .box [0] [(3, false), (2, false), (1, true)]], [tg .box [0] [(1, true), (3, false), (2, false)]])]

theorem runCtrlHg337FF : check 3 TCtrlHg337FF LCtrlHg337FF RCtrlHg337FF
    [.rw 1 0 false,
    .sem 0 1 [tC 2] 0,
    .sem 1 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 0,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sem 10 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 0 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 2 1 true,
    .sem 1 1 [tp 2 [L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1, L.C 0, L.H 1, L.Z 1, L.H 1, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.H 1, L.Z 1, L.H 1] [2, 3]] 0,
    .rw 1 2 false,
    .sem 2 1 [tp 2 [L.C 0] [2, 3]] 0,
    .rw 1 3 true,
    .sem 2 1 [tC 2] 0,
    .sem 3 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sem 12 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 2 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tCtrlHg337FF (ih : IH 4) : Derivable (theory 4) (wcT 4 LCtrlHg337FF) (wcT 4 RCtrlHg337FF) :=
  check_sound ih (AllD.cons (tHgDeff2f3 ih) (AllD.cons (g_entry .box [0] [(1, true), (3, false), (2, false)] [(3, false), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [2, 1] (by decide +kernel) (W4Low.tControlCZ00f1f2 ih)) (AllD.cons (g_entry .box [0] [(3, false), (2, false), (1, true)] [(1, true), (3, false), (2, false)] (by decide +kernel)) (AllD.nil 4))))) runCtrlHg337FF

def LWhiteHg337FF : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, false)]]

def RWhiteHg337FF : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TWhiteHg337FF : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (1, true), (2, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (1, false), (2, true)]]),
  ([tg .box [0] [(3, true), (1, true), (2, true)], tg .box [0] [(3, true), (1, false), (2, true)]], [tp 2 [L.C 0] [2, 3]]),
  ([tp 2 [L.C 0] [2, 3], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tp 2 [L.C 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runWhiteHg337FF : check 3 TWhiteHg337FF LWhiteHg337FF RWhiteHg337FF
    [.rw 0 0 true,
    .rw 1 1 false,
    .rw 2 2 false,
    .rw 1 3 false,
    .rw 1 4 false,
    .rw 0 5 false,
    .rw 2 3 true,
    .rw 3 2 true,
    .rw 2 1 true,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tWhiteHg337FF (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FF) (wcT 4 RWhiteHg337FF) :=
  check_sound ih (AllD.cons (W4.t166 ih) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(3, true), (1, true), (2, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, false)] [(3, true), (1, false), (2, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [1] (by decide +kernel) (W4.t170a ih)) (AllD.cons (tCtrlHg337FF ih) (AllD.cons (tHg337BaseFF ih) (AllD.nil 4))))))) runWhiteHg337FF

def LWhiteHg337FFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [0, 1] [(3, false), (2, true)]]

def RWhiteHg337FFf2 : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TWhiteHg337FFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runWhiteHg337FFf2 : check 3 TWhiteHg337FFf2 LWhiteHg337FFf2 RWhiteHg337FFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337FFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FFf2) (wcT 4 RWhiteHg337FFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, false), (2, false)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337FF ih) (AllD.nil 4)))) runWhiteHg337FFf2

def LWhiteHg337FFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .hg [0, 1] [(3, true), (2, false)]]

def RWhiteHg337FFf3 : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TWhiteHg337FFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runWhiteHg337FFf3 : check 3 TWhiteHg337FFf3 LWhiteHg337FFf3 RWhiteHg337FFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337FFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FFf3) (wcT 4 RWhiteHg337FFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337FF ih) (AllD.nil 4)))) runWhiteHg337FFf3

def LWhiteHg337FFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .hg [0, 1] [(3, true), (2, true)]]

def RWhiteHg337FFf2f3 : List Tk := [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TWhiteHg337FFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runWhiteHg337FFf2f3 : check 3 TWhiteHg337FFf2f3 LWhiteHg337FFf2f3 RWhiteHg337FFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337FFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FFf2f3) (wcT 4 RWhiteHg337FFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337FFf2 ih) (AllD.nil 4)))) runWhiteHg337FFf2f3

def LCtrlHg337FT : List Tk := [tp 2 [L.C 0] [2, 3], tg .hg [0, 1] [(3, true), (2, false)]]

def RCtrlHg337FT : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tp 2 [L.C 0] [2, 3]]

def TCtrlHg337FT : Tbl := [([tg .hg [0, 1] [(3, true), (2, false)]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(3, true), (2, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]),
  ([tg .box [0] [(1, true), (3, true), (2, false)]], [tg .box [0] [(3, true), (2, false), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [2, 3], tg .box [0] [(1, true), (3, true), (2, false)]], [tg .box [0] [(1, true), (3, true), (2, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, false), (1, true)]], [tg .box [0] [(1, true), (3, true), (2, false)]])]

theorem runCtrlHg337FT : check 3 TCtrlHg337FT LCtrlHg337FT RCtrlHg337FT
    [.rw 1 0 false,
    .sem 0 1 [tC 2] 0,
    .sem 1 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 0,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sem 10 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 0 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 2 1 true,
    .sem 1 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [2, 3]] 0,
    .rw 1 2 false,
    .sem 2 1 [tp 2 [L.C 0] [2, 3]] 0,
    .rw 1 3 true,
    .sem 2 1 [tC 2] 0,
    .sem 3 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sem 12 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 2 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tCtrlHg337FT (ih : IH 4) : Derivable (theory 4) (wcT 4 LCtrlHg337FT) (wcT 4 RCtrlHg337FT) :=
  check_sound ih (AllD.cons (tHgDeff2 ih) (AllD.cons (g_entry .box [0] [(1, true), (3, true), (2, false)] [(3, true), (2, false), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [2, 1] (by decide +kernel) (W4Low.tControlCZ01f1 ih)) (AllD.cons (g_entry .box [0] [(3, true), (2, false), (1, true)] [(1, true), (3, true), (2, false)] (by decide +kernel)) (AllD.nil 4))))) runCtrlHg337FT

def LWhiteHg337FT : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, true), (2, false)]]

def RWhiteHg337FT : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TWhiteHg337FT : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (1, true), (2, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (1, false), (2, true)]]),
  ([tg .box [0] [(3, true), (1, true), (2, true)], tg .box [0] [(3, true), (1, false), (2, true)]], [tp 2 [L.C 0] [2, 3]]),
  ([tp 2 [L.C 0] [2, 3], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tp 2 [L.C 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runWhiteHg337FT : check 3 TWhiteHg337FT LWhiteHg337FT RWhiteHg337FT
    [.rw 0 0 true,
    .rw 1 1 false,
    .rw 2 2 false,
    .rw 1 3 false,
    .rw 1 4 false,
    .rw 0 5 false,
    .rw 2 3 true,
    .rw 3 2 true,
    .rw 2 1 true,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tWhiteHg337FT (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FT) (wcT 4 RWhiteHg337FT) :=
  check_sound ih (AllD.cons (W4.t166 ih) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(3, true), (1, true), (2, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, false)] [(3, true), (1, false), (2, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [1] (by decide +kernel) (W4.t170a ih)) (AllD.cons (tCtrlHg337FT ih) (AllD.cons (tHg337BaseFT ih) (AllD.nil 4))))))) runWhiteHg337FT

def LWhiteHg337FTf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [0, 1] [(3, true), (2, true)]]

def RWhiteHg337FTf2 : List Tk := [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TWhiteHg337FTf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runWhiteHg337FTf2 : check 3 TWhiteHg337FTf2 LWhiteHg337FTf2 RWhiteHg337FTf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337FTf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FTf2) (wcT 4 RWhiteHg337FTf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, true), (2, false)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337FT ih) (AllD.nil 4)))) runWhiteHg337FTf2

def LWhiteHg337FTf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, false)]]

def RWhiteHg337FTf3 : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TWhiteHg337FTf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, true), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, true), (2, false)]], [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runWhiteHg337FTf3 : check 3 TWhiteHg337FTf3 LWhiteHg337FTf3 RWhiteHg337FTf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337FTf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FTf3) (wcT 4 RWhiteHg337FTf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, true), (2, false)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337FT ih) (AllD.nil 4)))) runWhiteHg337FTf3

def LWhiteHg337FTf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .hg [0, 1] [(3, false), (2, true)]]

def RWhiteHg337FTf2f3 : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TWhiteHg337FTf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, true), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, false), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [0, 1] [(3, true), (2, true)]], [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runWhiteHg337FTf2f3 : check 3 TWhiteHg337FTf2f3 LWhiteHg337FTf2f3 RWhiteHg337FTf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337FTf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337FTf2f3) (wcT 4 RWhiteHg337FTf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, true), (2, true)] [(3, false), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337FTf2 ih) (AllD.nil 4)))) runWhiteHg337FTf2f3

def LCtrlHg337TF : List Tk := [tp 2 [L.C 0] [2, 3], tg .hg [0, 1] [(3, false), (2, true)]]

def RCtrlHg337TF : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tp 2 [L.C 0] [2, 3]]

def TCtrlHg337TF : Tbl := [([tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(2, true), (3, false)]]),
  ([tg .hg [0, 1] [(2, true), (3, false)]], [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1], tg .box [0] [(2, true), (3, false), (1, true)], tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]]),
  ([tg .box [0] [(2, true), (3, false), (1, true)]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tg .box [0] [(1, true), (2, true), (3, false)]], [tg .box [0] [(3, false), (2, true), (1, true)]]),
  ([tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [3, 2], tg .box [0] [(1, true), (2, true), (3, false)]], [tg .box [0] [(1, true), (2, true), (3, false)], tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [3, 2]]),
  ([tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(1, true), (2, true), (3, false)]]),
  ([tg .box [0] [(3, false), (2, true), (1, true)]], [tg .box [0] [(2, true), (3, false), (1, true)]])]

theorem runCtrlHg337TF : check 3 TCtrlHg337TF LCtrlHg337TF RCtrlHg337TF
    [.rw 1 0 false,
    .rw 1 1 false,
    .rw 2 2 false,
    .sem 0 1 [tC 2] 0,
    .sem 1 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 0,
    .sw 1,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sem 10 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 0 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 2 3 true,
    .sem 1 1 [tp 2 [L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0, L.C 0, L.H 0, L.Z 0, L.H 0, L.H 0, L.Z 0, L.H 0] [3, 2]] 0,
    .rw 1 4 false,
    .sem 2 1 [tp 2 [L.C 0] [2, 3]] 0,
    .rw 1 5 true,
    .sem 2 1 [tC 2] 0,
    .sem 3 1 [tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tK 0, tH 1, tZ 0, tS 0] 2,
    .sw 2,
    .sw 3,
    .sw 4,
    .sw 5,
    .sw 6,
    .sw 7,
    .sw 8,
    .sw 9,
    .sw 10,
    .sw 11,
    .sem 12 1 [tp 2 [L.C 0] [2, 3]] 0,
    .sem 2 10 [tp 2 [L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.K 0, L.H 1, L.Z 0, L.S 0] [0, 1]] 2,
    .rw 1 6 false,
    .rw 0 1 true,
    .rw 0 0 true] = true := by
  decide +kernel

theorem tCtrlHg337TF (ih : IH 4) : Derivable (theory 4) (wcT 4 LCtrlHg337TF) (wcT 4 RCtrlHg337TF) :=
  check_sound ih (AllD.cons (g_entry .hg [0, 1] [(3, false), (2, true)] [(2, true), (3, false)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [2] (by decide +kernel) (tHgDeff2 ih)) (AllD.cons (g_entry .box [0] [(2, true), (3, false), (1, true)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(1, true), (2, true), (3, false)] [(3, false), (2, true), (1, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [1, 2, 1] (by decide +kernel) (W4Low.tControlCZ01f1 ih)) (AllD.cons (g_entry .box [0] [(3, false), (2, true), (1, true)] [(1, true), (2, true), (3, false)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, false), (2, true), (1, true)] [(2, true), (3, false), (1, true)] (by decide +kernel)) (AllD.nil 4)))))))) runCtrlHg337TF

def LWhiteHg337TF : List Tk := [tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, true)]]

def RWhiteHg337TF : List Tk := [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, false)]]

def TWhiteHg337TF : Tbl := [([tg .box [0] [(3, true), (2, true), (1, true)], tg .box [0] [(3, true), (2, true), (1, true)]], []),
  ([tg .box [0] [(3, true), (2, true), (1, true)]], [tg .box [0] [(3, true), (1, true), (2, true)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)]], [tg .box [0] [(3, true), (1, false), (2, true)]]),
  ([tg .box [0] [(3, true), (1, true), (2, true)], tg .box [0] [(3, true), (1, false), (2, true)]], [tp 2 [L.C 0] [2, 3]]),
  ([tp 2 [L.C 0] [2, 3], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tp 2 [L.C 0] [2, 3]]),
  ([tg .box [0] [(3, true), (2, true), (1, true)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, true)]])]

theorem runWhiteHg337TF : check 3 TWhiteHg337TF LWhiteHg337TF RWhiteHg337TF
    [.rw 0 0 true,
    .rw 1 1 false,
    .rw 2 2 false,
    .rw 1 3 false,
    .rw 1 4 false,
    .rw 0 5 false,
    .rw 2 3 true,
    .rw 3 2 true,
    .rw 2 1 true,
    .rw 1 0 false] = true := by
  decide +kernel

theorem tWhiteHg337TF (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337TF) (wcT 4 RWhiteHg337TF) :=
  check_sound ih (AllD.cons (W4.t166 ih) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, true)] [(3, true), (1, true), (2, true)] (by decide +kernel)) (AllD.cons (g_entry .box [0] [(3, true), (2, true), (1, false)] [(3, true), (1, false), (2, true)] (by decide +kernel)) (AllD.cons (rel_entry (W4.havail4b ih) [1] (by decide +kernel) (W4.t170a ih)) (AllD.cons (tCtrlHg337TF ih) (AllD.cons (tHg337BaseTF ih) (AllD.nil 4))))))) runWhiteHg337TF

def LWhiteHg337TFf2 : List Tk := [tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [0, 1] [(3, false), (2, false)]]

def RWhiteHg337TFf2 : List Tk := [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, false)]]

def TWhiteHg337TFf2 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .hg [0, 1] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .hg [0, 1] [(3, false), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [2], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [2]], [tg .box [0] [(3, true), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runWhiteHg337TFf2 : check 3 TWhiteHg337TFf2 LWhiteHg337TFf2 RWhiteHg337TFf2
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [2], tp 1 [L.H 0, L.Z 0, L.H 0] [2]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337TFf2 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337TFf2) (wcT 4 RWhiteHg337TFf2) :=
  check_sound ih (AllD.cons (x81_entry 2 .hg [0, 1] [(3, false), (2, true)] [(3, false), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 2 .box [0] [(3, true), (2, true), (1, false)] [(3, true), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337TF ih) (AllD.nil 4)))) runWhiteHg337TFf2

def LWhiteHg337TFf3 : List Tk := [tg .box [0] [(3, false), (2, true), (1, false)], tg .hg [0, 1] [(3, true), (2, true)]]

def RWhiteHg337TFf3 : List Tk := [tg .hg [0, 1] [(3, true), (2, true)], tg .box [0] [(3, false), (2, true), (1, false)]]

def TWhiteHg337TFf3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, true)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, true)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, true), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, true), (1, false)]]),
  ([tg .box [0] [(3, true), (2, true), (1, false)], tg .hg [0, 1] [(3, false), (2, true)]], [tg .hg [0, 1] [(3, false), (2, true)], tg .box [0] [(3, true), (2, true), (1, false)]])]

theorem runWhiteHg337TFf3 : check 3 TWhiteHg337TFf3 LWhiteHg337TFf3 RWhiteHg337TFf3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337TFf3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337TFf3) (wcT 4 RWhiteHg337TFf3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, true)] [(3, true), (2, true)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, true), (1, false)] [(3, false), (2, true), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337TF ih) (AllD.nil 4)))) runWhiteHg337TFf3

def LWhiteHg337TFf2f3 : List Tk := [tg .box [0] [(3, false), (2, false), (1, false)], tg .hg [0, 1] [(3, true), (2, false)]]

def RWhiteHg337TFf2f3 : List Tk := [tg .hg [0, 1] [(3, true), (2, false)], tg .box [0] [(3, false), (2, false), (1, false)]]

def TWhiteHg337TFf2f3 : Tbl := [([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .hg [0, 1] [(3, false), (2, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .hg [0, 1] [(3, true), (2, false)]]),
  ([tp 1 [L.H 0, L.Z 0, L.H 0] [3], tg .box [0] [(3, true), (2, false), (1, false)], tp 1 [L.H 0, L.Z 0, L.H 0] [3]], [tg .box [0] [(3, false), (2, false), (1, false)]]),
  ([tg .box [0] [(3, true), (2, false), (1, false)], tg .hg [0, 1] [(3, false), (2, false)]], [tg .hg [0, 1] [(3, false), (2, false)], tg .box [0] [(3, true), (2, false), (1, false)]])]

theorem runWhiteHg337TFf2f3 : check 3 TWhiteHg337TFf2f3 LWhiteHg337TFf2f3 RWhiteHg337TFf2f3
    [.rw 1 0 true,
    .rw 0 1 true,
    .sem 2 2 [] 0,
    .rw 1 2 false,
    .sem 2 0 [tp 1 [L.H 0, L.Z 0, L.H 0] [3], tp 1 [L.H 0, L.Z 0, L.H 0] [3]] 0,
    .rw 0 0 false,
    .rw 1 1 false] = true := by
  decide +kernel

theorem tWhiteHg337TFf2f3 (ih : IH 4) : Derivable (theory 4) (wcT 4 LWhiteHg337TFf2f3) (wcT 4 RWhiteHg337TFf2f3) :=
  check_sound ih (AllD.cons (x81_entry 3 .hg [0, 1] [(3, false), (2, false)] [(3, true), (2, false)] (by decide +kernel)) (AllD.cons (x81_entry 3 .box [0] [(3, true), (2, false), (1, false)] [(3, false), (2, false), (1, false)] (by decide +kernel)) (AllD.cons (tWhiteHg337TFf2 ih) (AllD.nil 4)))) runWhiteHg337TFf2f3

end QCert.RealCliffordCH.Sec8.D.W4LowHg
