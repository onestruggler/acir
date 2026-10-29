from emit import *
import pickle, time
t=time.time()
lib = build_lib(6, 5, 2)
print('lib', len(lib), round(time.time()-t,1), flush=True)
A=[H(0,1)]; Q=[H(0,2),H(1,3)]; R=[H(0,4),H(1,5)]; Z01=[Z(0),Z(1)]
P=[X(0,2),X(1,3)]; Rp=[H(2,4),H(3,5)]; B=[H(2,3)]; Z23=[Z(2),Z(3)]; H45=[H(4,5)]
W46L = A+Q+Rp+B+H45+H45+[Z(3),Z(2)]+Rp+Q
W46R = Q+Rp+[Z(3),Z(2)]+H45+B+H45+Rp+Q+A
assert eq(6,W46L,W46R)
fw = [L21,
      A+Q+P+P+R+A+Z01+R+P+P+Q,
      A+Q+P+P+R+P+P+A+P+P+Z01+P+P+R+P+P+Q,
      A+Z23+Q+P+R+P+P+A+P+P+Z01+P+P+R+P+P+Q,
      A+Z23+Q+Rp+P+A+P+P+Z01+P+P+R+P+P+Q,
      A+Z23+Q+Rp+B+P+Z01+P+P+R+P+P+Q,
      A+Z23+Q+Rp+B+Z23+P+R+P+P+Q,
      A+Z23+Q+Rp+B+Z23+Rp+P+Q,
      A+Z23+Q+Rp+B+Z23+Rp+Q+Z23,
      Z23+A+Q+Rp+B+Z23+Rp+Q+Z23,
      Z23+A+Q+Rp+B+H45+H45+Z23+Rp+Q+Z23,
      Z23+W46L+Z23]
bw = [R21,
      Q+P+P+R+A+Z01+R+Q+A,
      Q+P+P+R+P+P+A+P+P+Z01+P+P+R+P+P+Q+A,
      Z23+Q+P+R+P+P+A+P+P+Z01+P+P+R+P+P+Q+A,
      Z23+Q+Rp+P+A+P+P+Z01+P+P+R+P+P+Q+A,
      Z23+Q+Rp+B+P+Z01+P+P+R+P+P+Q+A,
      Z23+Q+Rp+B+Z23+P+R+P+P+Q+A,
      Z23+Q+Rp+B+Z23+Rp+P+Q+A,
      Z23+Q+Rp+B+Z23+Rp+Q+Z23+A,
      Z23+Q+Rp+B+Z23+Rp+Q+A+Z23,
      Z23+Q+Rp+Z23+B+Rp+Q+A+Z23,
      Z23+Q+Rp+Z23+H45+B+H45+Rp+Q+A+Z23,
      Z23+W46R+Z23]
for w in fw: assert eq(6,w,L21), w
for w in bw: assert eq(6,w,R21), w
full = fw + bw[::-1]
E=[('w46', W46L, W46R)]
steps, bad = solve_chain(6, full, lib, 5, rules=E, depth=3)
print('steps', None if steps is None else len(steps), round(time.time()-t,1))
if steps:
    pickle.dump((full, E, emit_steps(6, steps, 5, ['w46'])), open('c21.pkl','wb'))
