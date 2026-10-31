import time
from pathlib import Path
from b1gen import B1
from b1emit import emit, verify
from b2q1 import M8, STD as STD8
if __name__ == '__main__':
    t = time.time()
    B = B1(M8, STD8, True)
    assert verify(B, 8)
    k = emit(B, 8, 'QCert.CliffordCS3.Macro8', 'QCert.CliffordCS3.M8',
             '# Three qubits: the macro alphabet of `U₈(ℤ[1/2, i])`', STD8,
             str(Path(__file__).resolve().parent.parent / 'Macro8.lean'))
    print('rules', k, '%.1fs' % (time.time() - t))
