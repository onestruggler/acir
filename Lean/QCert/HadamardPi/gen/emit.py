from deriv import lean_word
from good4 import good
def lean_good(name, w, par):
    # the Lean proof decides `good4Chk par w` by evaluation (`GoodCheck.lean`); the symbolic
    # computation here only confirms that the word is good before emitting the theorem
    U, j = good(w, par)
    assert j is not None
    return (f"theorem {name} : Good4 {par} {lean_word(w)} := good4_of_chk (by decide +kernel)\n")
