#!/usr/bin/env python3
"""
Try the substitution c_n = b_n + 1/2 to simplify the recurrence
Actually, work with 2c_n = 2b_n + 1 to avoid fractions
"""

def compute_sequence():
    """Compute b_n and analyze the pattern"""
    b = [0]
    for i in range(20):
        b_next = 2*b[-1]**2 + b[-1] + 1
        b.append(b_next)
    return b

def analyze_transformation():
    """
    Let's try: b_{n+1} = 2b_n^2 + b_n + 1

    This can be written as:
    b_{n+1} + 1/2 = 2b_n^2 + b_n + 3/2 = 2b_n^2 + b_n + 1/2 + 1
                   = (2b_n + 1)^2 / 2

    So if c_n = b_n + 1/2, then:
    c_{n+1} = (2b_n + 1)^2 / 2 = ((2b_n + 1)^2) / 2

    Or: 2c_n = 2b_n + 1, so:
    2c_{n+1} = (2c_n - 1 + 1)^2 / ... wait this doesn't work out cleanly
    """

    b = compute_sequence()

    print("Testing the relation b_{n+1} + 1/2 = (2b_n + 1)^2 / 2:")
    for n in range(5):
        lhs = b[n+1] + 0.5
        rhs = (2*b[n] + 1)**2 / 2
        print(f"n={n}: LHS={lhs}, RHS={rhs}, Equal: {abs(lhs - rhs) < 0.001}")

    print("\nThis means: 2b_{n+1} + 1 = (2b_n + 1)^2")
    print("So if we define d_n = 2b_n + 1, then d_{n+1} = d_n^2")

    print("\nVerifying d_{n+1} = d_n^2:")
    for n in range(8):
        d_n = 2*b[n] + 1
        d_n1 = 2*b[n+1] + 1
        print(f"n={n}: d_n = {d_n}, d_n^2 = {d_n**2}, d_{{n+1}} = {d_n1}, Equal: {d_n**2 == d_n1}")

def analyze_d_sequence():
    """Analyze the sequence d_n = 2b_n + 1"""
    b = compute_sequence()

    print("\n" + "="*60)
    print("Sequence d_n = 2b_n + 1 (satisfies d_{n+1} = d_n^2)")
    print("="*60)

    d = [2*b[n] + 1 for n in range(len(b))]

    print("\nFirst few terms:")
    for n in range(10):
        print(f"d_{n} = {d[n]}")

    print("\nCheck: d_n = d_0^(2^n)")
    print(f"d_0 = {d[0]}")
    for n in range(1, 8):
        expected = d[0] ** (2**n)
        actual = d[n]
        match = (expected == actual)
        print(f"n={n}: d_0^(2^{n}) matches d_{n}: {match}")

def main():
    analyze_transformation()
    analyze_d_sequence()

if __name__ == "__main__":
    main()
