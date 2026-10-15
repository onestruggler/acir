# Clement's schema (19) on five wires, the core: CZ(a,b) on the dashed
# wire a of the four-wire box BOX(a; u, c, e) passes it, by four-wire
# windows (engine.move_left).   python3 w5_19.py
import derivn, engine
from derivn import Derivation, show
L = {}
B = ('BOX', 0, 2, 1, 3)
d = Derivation('test', [B, ('CZ', 0, 4)], [('CZ', 0, 4), B], L)
m = engine.move_left(d, 1, 1, 0)
print('block', m, show(d.cur))
engine.refold_boxes(d, m, len(d.cur), [B])
print(show(d.cur)); d.done()
