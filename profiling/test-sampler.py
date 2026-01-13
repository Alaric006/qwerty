#!/usr/bin/env python3

"""
Perform the Bernstein—Vazirani algorithm on a provided bitstring, printing the
bitstring determined by both the quantum algorithm and classical algorithm.
"""

from argparse import ArgumentParser
from qwerty import *
from qwerty.kernel import _reset_compiler_state

def bv(oracle, acc=None):
    @qpu[[N]]
    def kernel():
        return ('p'**N | oracle.sign
                       | pm**N >> std**N
                       | measure**N)

    return kernel(acc=acc)

def get_black_box(secret_string):
    @classical[[N]]
    def f(x: bit[N]) -> bit:
        return (secret_string & x).xor_reduce()
    return f

def naive_classical(f, n_bits):
    secret_found = bit[n_bits](0)
    x = bit[n_bits](0b1 << (n_bits-1))
    for i in range(n_bits):
        secret_found[i] = f(x)
        x = x >> 1
    return secret_found

if __name__ == '__main__':
    for i in range(0, 5000):
        _reset_compiler_state()
        secret_str = bit.from_str("1000")
        n_bits = len(secret_str)
        black_box = get_black_box(secret_str)

        print('Classical:', naive_classical(black_box, n_bits))
        print('Quantum:  ', bv(black_box, acc=None))
