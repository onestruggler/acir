"""Gamma-distance from E of gE for some elements g (ball of radius 2)."""
import pickle, os, time
from lat import G, e8_roots, orbit, THETA
from tree import word_matrix, mat_mul
from tree2 import key

def ball2():
    if os.path.exists("ball2.pkl"):
        return pickle.load(open("ball2.pkl", "rb"))
    E = frozenset(e8_roots())
    H0E = frozenset(G["H0"](v) for v in E)
    ot = orbit(H0E, THETA)
    reps = list(ot.values())
    T = [word_matrix((w + " H0").strip()) for w in reps]
    dist = {key(word_matrix("")): (0, "")}
    for i, Ti in enumerate(T):
        dist[key(Ti)] = (1, reps[i] + " H0")
    for i, Ti in enumerate(T):
        for j, Tj in enumerate(T):
            k = key(mat_mul(Ti, Tj))
            if k not in dist:
                dist[k] = (2, (reps[i] + " H0 " + reps[j] + " H0").strip())
    pickle.dump((dist, reps), open("ball2.pkl", "wb"))
    return dist, reps

if __name__ == "__main__":
    t = time.time()
    dist, reps = ball2()
    print("ball", len(dist), round(time.time() - t))
    tests = {
        "CCZ": "H0 CCX0 H0",
        "Z0": "Z0", "CZ01": "CZ01",
        "M7 sign on 111": "CCZ",
        "ctrlHH (wire2=0 ctrl)": "X2 CCX0 X2",  # placeholder replaced below
        "H0": "H0", "H0H1": "HH01", "HHH": "HHH",
        "H0 CCX1 H0": "H0 CCX1 H0",
        "H0 CCX1": "H0 CCX1",
    }
    for name, w in tests.items():
        k = key(word_matrix(w))
        print(name, "->", dist.get(k, (">2",))[0])
