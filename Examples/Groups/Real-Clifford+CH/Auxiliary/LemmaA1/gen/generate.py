# Regenerate LemmaA1/Base.agda, More.agda, D3.agda and D4.agda from the
# derivations in spec_*.py.  Every step is checked numerically as it is
# generated (gen_a1.py, gen_chain.py); the chains of D3 and D4 are also
# checked against the paper's lines (spec_d3.py, spec_d4.py).
# Run from anywhere: python3 generate.py
import contextlib, io, os, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.dirname(HERE)
sys.path.insert(0, HERE)
os.chdir(HERE)

def read(name):
    return open(os.path.join(HERE, name), encoding='utf-8').read()

def write(name, text):
    with open(os.path.join(OUT, name), 'w', encoding='utf-8', newline='') as f:
        f.write(text)

def run_spec(name):
    return subprocess.run([sys.executable, name], capture_output=True, text=True,
                          encoding='utf-8', check=True, cwd=HERE).stdout

write('Base.agda', read('base_head.txt') + run_spec('spec_base.py').rstrip('\n') + '\n')
write('More.agda', read('more_head.txt') + run_spec('spec_more.py').rstrip('\n') + '\n')

with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
    import spec_d3, spec_d4

write('D3.agda', read('d3_head.txt') + spec_d3.L.agda_segments('d3-chain') + '''
-- (d3) at the indices 0, 1, 2, 3.
d3₀ : (H ₂ ₃ • H ₀ ₂ • H ₁ ₃) ^ 4 ≈ H ₀ ₁ • H ₂ ₃
d3₀ = trans (by-assoc Eq.refl) d3-chain
''')
write('D4.agda', read('d4_head.txt') + spec_d4.L.agda_segments('d4-chain') + '''
-- (d4) at the indices 0, 1, 4, 5, 2, 3.
d4₀ : (H ₀ ₄ • H ₁ ₅ • H ₀ ₁ • H ₀ ₄ • H ₁ ₅ • X ₄ ₂ • X ₅ ₃) ^ 3 ≈
      H ₄ ₂ • H ₅ ₃ • H ₂ ₃ • H ₄ ₂ • H ₅ ₃ • X ₄ ₂ • X ₅ ₃
d4₀ = trans (by-assoc Eq.refl) d4-chain
''')
print('regenerated Base, More, D3, D4')
