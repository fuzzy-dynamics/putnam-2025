#!/usr/bin/env python3
"""
Find the correct transformation
"""
import sys
sys.set_int_max_str_digits(100000)

def v2(n):
    if n == 0:
        return float('inf')
    count = 0
    while n % 2 == 0:
        count += 1
        n //= 2
    return count

def compute_sequence():
    b = [0]
    for i in range(20):
        b_next = 2*b[-1]**2 + b[-1] + 1
        b.append(b_next)
    return b

def check_recurrence():
    """
    b_{n+1} = 2b_n^2 + b_n + 1

    Let me check: 2b_{n+1} + 1 = ?
    2b_{n+1} + 1 = 2(2b_n^2 + b_n + 1) + 1 = 4b_n^2 + 2b_n + 3

    And (2b_n + 1)^2 = 4b_n^2 + 4b_n + 1

    These differ by 2b_n + 2 = 2(b_n + 1).

    So: 2b_{n+1} + 1 = (2b_n + 1)^2 - 2(b_n + 1)
                      = (2b_n + 1)^2 - 2b_n - 2
    """
    b = compute_sequence()

    print("Checking: 2b_{n+1} + 1 = (2b_n + 1)^2 - 2b_n - 2")
    for n in range(8):
        lhs = 2*b[n+1] + 1
        rhs = (2*b[n] + 1)**2 - 2*b[n] - 2
        print(f"n={n}: Equal: {lhs == rhs}")

    print("\nSimplifying: 2b_{n+1} = 4b_n^2 + 2b_n + 2 - 2b_n - 2 = 4b_n^2")
    print("Wait, that's just the recurrence again.")

    print("\n" + "="*60)
    print("Key insight: Look at 2b_n + 1")
    print("="*60)

    d = [2*b[n] + 1 for n in range(len(b))]
    print("\nd_n = 2b_n + 1:")
    for n in range(10):
        print(f"d_{n} = {d[n]}, v_2(d_{n}) = {v2(d[n])}")

    print("\nFrom the recurrence:")
    print("d_{n+1} = 2b_{n+1} + 1 = 2(2b_n^2 + b_n + 1) + 1 = 4b_n^2 + 2b_n + 3")
    print("        = (2b_n + 1)^2 + (2b_n + 1) + 1 - 2b_n - 1")
    print("        = d_n^2 + d_n - 2b_n")

    print("\nActually: 4b_n^2 + 2b_n + 3 = (2b_n)^2 + 2b_n + 3")
    print("And (2b_n + 1)^2 = 4b_n^2 + 4b_n + 1")
    print("Difference: 2b_n + 2")

    print("\nSo: d_{n+1} = d_n^2 - 2b_n - 2 = d_n^2 - (d_n - 1) - 2 = d_n^2 - d_n - 1")

    print("\nVerifying d_{n+1} = d_n^2 - d_n - 1:")
    for n in range(8):
        lhs = d[n+1]
        rhs = d[n]**2 - d[n] - 1
        equal = (lhs == rhs)
        print(f"n={n}: {equal}")
        if not equal:
            print(f"  LHS={lhs}, RHS={rhs}")

    print("\n" + "="*60)
    print("Aha! So d_{n+1} = d_n(d_n - 1) - 1 = d_n^2 - d_n - 1")
    print("="*60)

def analyze_d_modulo_powers():
    """Analyze d_n modulo powers of 2"""
    b = compute_sequence()
    d = [2*b[n] + 1 for n in range(len(b))]

    print("\nAnalyzing d_n modulo powers of 2:")
    print(f"{'n':<4} {'d_n mod 8':<12} {'d_n mod 16':<12} {'v_2(d_n-1)':<15}")
    for n in range(10):
        print(f"{n:<4} {d[n] % 8:<12} {d[n] % 16:<12} {v2(d[n]-1):<15}")

    print("\n" + "="*60)
    print("For n = 2^k:")
    print("="*60)
    for k in range(1, 5):
        n = 2**k
        if n < len(d):
            print(f"k={k}, n=2^{k}={n}:")
            print(f"  d_{{{n}}} = 2b_{{{n}}} + 1")
            print(f"  v_2(d_{{{n}}} - 1) = v_2(2b_{{{n}}}) = {v2(d[n]-1)}")
            print(f"  Since b_{{{n}}} = 2^{{{v2(b[n])}}} · (odd), we have:")
            print(f"  v_2(d_{{{n}}} - 1) = 1 + v_2(b_{{{n}}}) = 1 + {v2(b[n])} = {v2(d[n]-1)}")
            print()

def main():
    check_recurrence()
    analyze_d_modulo_powers()

if __name__ == "__main__":
    main()
