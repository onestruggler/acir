from eng import *
X0='hzh'; X1='HZH'
cn = drawn('h','C','h'); cnw = drawn(X1, cn, X1)
cn10 = drawn('S', cn, 'S'); cn10w = drawn(X0, cn10, X0)
czw = drawn(X1,'C',X1); czw0 = drawn(X0,'C',X0); czww = drawn(X1, X0, 'C', X1, X0)
chw = drawn(X1,'K',X1); ch10 = drawn('S','K','S'); ch10w = drawn(X0, ch10, X0)
zw0 = drawn(X0,'z',X0); zw1 = drawn(X1,'Z',X1)
box1 = drawn('Z', zw1)
SWAPW = 'hHChHChHC'
BASE = [
 ('e1', 'hh', ''), ('e2', 'zz', ''), ('e3', 'zh'*8, ''),
 ('e1u', 'HH', ''), ('e2u', 'ZZ', ''), ('e3u', 'ZH'*8, ''),
 ('e4', 'CC', ''), ('e5', 'KK', ''),
 ('e6', czw+'C', 'z'), ('e7', chw+'K', 'h'),
 ('e9', 'SC', 'CS'), ('e10', czw+'K', 'K'+czw),
 ('e11', 'HKZHK', 'KHKZH'),
 ('f1', 'SZ', 'zS'), ('f2', 'SH', 'hS'), ('g', 'SS', ''),
 ('def8', 'S', SWAPW),
]
AUX = [
 ('81', drawn(X0,X0), ''), ('82', drawn(cn,cn), ''), ('83', drawn(cnw,cnw), ''),
 ('84', drawn(cn,cnw), X0), ('85', drawn(cn,cnw), drawn(cnw,cn)),
 ('86', 'S', drawn(cn,cn10,cn)), ('87', drawn(cn,'S'), drawn(cn10,cn)),
 ('88', drawn(cn,X0), cnw), ('89', drawn(cnw,X0), cn),
 ('90', drawn('C',czw), drawn(czw,'C')), ('91', drawn('C',czw0), drawn(czw0,'C')),
 ('92', drawn('K',chw), drawn(chw,'K')), ('93', drawn('K','h'), drawn('h','K')),
 ('94', drawn('K',cnw), drawn(cnw,'K')), ('95', drawn(chw,cn), drawn(cn,chw)),
 ('96', drawn(cn,czw), drawn(czw,cn)), ('97', drawn(cn,'C'), drawn(czw0,cn)),
 ('98', drawn(cn,'C',cn), czw0), ('99', drawn(ch10w,czw), drawn(czw,ch10w)),
 ('100', drawn(cn,X0), drawn(X0,cn)), ('101', drawn(X0,cn,X0), cn),
 ('102', drawn(cn,'K',cn), drawn(X0,'K',X0)), ('103', drawn('K',cn,'K'), 'C'),
 ('104', drawn(cn,'S',cn), cn10), ('105', drawn(cn10,chw,cn10), drawn(cn,ch10w,cn)),
 ('106', drawn(X1,cn,ch10,cn,X1), drawn(X0,cn10,'K',cn10,X0)),
 ('107', drawn(cn10w,cn,ch10,cn,cn10w), drawn(X0,chw,X0)),
 ('108', drawn(cnw,X0,cn10,'K',cn10,X0,cnw), drawn(X1,ch10,X1)),
 ('109', drawn(box1,'K'), drawn('K',box1)),
 ('110', drawn(chw,'H',zw1,chw,'H'), drawn('H',zw1,chw,'H',chw)),
]
if __name__ == '__main__':
    print(eq('S', SWAPW))
    for n,l,r in BASE: assert eq(l,r), n
    for n,l,r in AUX: print(n, eq(l,r))
