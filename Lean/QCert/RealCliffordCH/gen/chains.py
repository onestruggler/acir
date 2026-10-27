from auxeqs import *
# extra one-wire lemmas (Lemma 7.1 steps), on wire 1
EXTRA_BEFORE = {
 '81': [('cn10d', cn10, drawn('H','C','H')), ('SX1', drawn('S',X1), drawn(X0,'S')),
        ('Sczww', drawn('S',czww), drawn(czww,'S'))],
 '109': [('P109', drawn(czww,'K'), drawn('K',czww))],
}
ONEW = [
 ('L71a', drawn('H','Z',box1), drawn(box1,'H','Z')),
 ('L71b', drawn(box1,'H','Z'), drawn('H',zw1)),
]
CHAINS = {
 'Sczww': [drawn('S',czww), drawn(X0,X1,'S','C',X1,X0), drawn(X0,X1,'C','S',X1,X0),
           drawn(X0,X1,'C',X0,X1,'S'), drawn(czww,'S')],
 'P109': [drawn(czww,'K'), drawn('S','S',czww,'K'), drawn('S',czww,'S','K'), drawn('S',czww,ch10,'S'), drawn('S',X0,czw,ch10w,X0,'S'),
          drawn('S',X0,ch10w,czw,X0,'S'), drawn('S',ch10,czww,'S'), drawn('K',czww)],
 '86': ['S', drawn('h','S','H'), drawn('h','C','H','h','C','H','h','C','H','h','H'),
        drawn('h','C','H','h','C','H','h','C','h'), drawn(cn,cn10,cn)],
 '96': [drawn(cn,czw), drawn('K',chw,'C',chw,'K',czw), drawn('K',chw,chw,'C','K',czw),
        drawn('K','C','K',czw), drawn(czw,'K','C','K'), drawn(czw,'K',chw,chw,'C','K'),
        drawn(czw,'K',chw,'C',chw,'K'), drawn(czw,cn)],
 '102': [drawn(cn,'K',cn), drawn(cn,cnw,cnw,'K',cn), drawn(cn,cnw,'K',cnw,cn), drawn(X0,'K',X0)],
 '105': [drawn(cn10,chw,cn10), drawn(cn10,cn,chw,cn,cn10), drawn(cn,'S',chw,'S',cn), drawn(cn,ch10w,cn)],
 '106': [drawn(X1,cn,ch10,cn,X1), drawn(X1,X0,cn,ch10w,cn,X0,X1), drawn(X1,X0,cn10,chw,cn10,X0,X1),
         drawn(X0,X1,'H','C','H',chw,'H','C','H',X1,X0), drawn(X0,'H','C','H',X1,chw,X1,'H','C','H',X0),
         drawn(X0,'H','C','H','K','H','C','H',X0), drawn(X0,cn10,'K',cn10,X0)],
 '107': [drawn(cn10w,cn,ch10,cn,cn10w), drawn(X0,cn10,cn,ch10w,cn,cn10,X0),
         drawn(X0,cn10,cn10,chw,cn10,cn10,X0),
         drawn(X0,'H','C','H','H','C','H',chw,'H','C','H','H','C','H',X0), drawn(X0,chw,X0)],
 '109': [drawn(box1,'K'), drawn('Z',czw,czww,'K'), drawn('Z',czw,'K',czww), drawn('Z','K',czw,czww),
         drawn('Z','K',zw1), drawn('Z','K',chw,chw,zw1), drawn('Z','h',chw,zw1),
         drawn('h','C',czw0,chw,zw1), drawn('h','C',chw,czw0,zw1), drawn('h',chw,'C',czw0,zw1),
         drawn('h',chw,'Z',zw1), drawn('K',chw,chw,'Z',zw1), drawn('K','Z',zw1), drawn('K',box1)],
 '110': [drawn(chw,'H',zw1,chw,'H'), drawn('K','K',chw,'H',zw1,chw,'K','K','H'),
         drawn('K','h','h','H',zw1,'K','H'), drawn('K','H',zw1,'K','H'),
         drawn('K','H','Z',box1,'K','H'), drawn('K',box1,'H','Z','K','H'),
         drawn(box1,'K','H','Z','K','H'), drawn(box1,'H','Z','K','H','K'),
         drawn('H',zw1,'K','H','K'), drawn('H',zw1,chw,chw,'K','H','K'),
         drawn('H',zw1,chw,chw,'K','H','K',chw,chw),
         drawn('H',zw1,chw,'H',chw)],
}
for n, ch in CHAINS.items():
    for i, w in enumerate(ch):
        assert eq(w, ch[0]), (n, i)
print('chains ok')
