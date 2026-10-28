"""Paths: intermediate search results go to gen/work (not committed), the
recorded inputs of the emitters to gen/data, and the generated modules to
the folder above."""
import os

GEN = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.join(GEN, "work")
DATA = os.path.join(GEN, "data")
LEAN = os.path.dirname(GEN)
os.makedirs(WORK, exist_ok=True)


def work(fn):
    return os.path.join(WORK, fn)


def data(fn):
    return os.path.join(DATA, fn)


def module(name):
    return os.path.join(LEAN, name)


def bfs_cmd(name):
    """The command running the compiled search `name` (bfs or bfs7); on
    Windows the Linux binary is run through WSL."""
    exe = os.path.join(GEN, name)
    if os.name == "nt":
        p = exe.replace("\\", "/")
        return ["wsl", "--exec", "/mnt/" + p[0].lower() + p[2:]]
    return [exe]
