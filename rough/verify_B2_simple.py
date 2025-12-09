"""
Numerical verification of Putnam 2025 B2 solution using only numpy.

Problem: Prove x_1 < x_2 where:
- x_1 = x-coordinate of centroid of region R under f(x)
- x_2 = x-coordinate of centroid of solid of revolution about x-axis

Tests various strictly increasing continuous functions f: [0,1] -> [0, infinity).
"""

import numpy as np


def integrate_1d(func, a=0, b=1, n=10000):
    """Numerical integration using trapezoidal rule."""
    x = np.linspace(a, b, n)
    y = func(x)
    return np.trapz(y, x)


def integrate_2d(func, a=0, b=1, n=200):
    """Numerical double integration using trapezoidal rule."""
    x = np.linspace(a, b, n)
    y = np.linspace(a, b, n)
    X, Y = np.meshgrid(x, y)
    Z = func(X, Y)
    # Integrate over y first, then x
    dx = (b - a) / (n - 1)
    dy = (b - a) / (n - 1)
    return np.trapz(np.trapz(Z, axis=0) * dx, x) * dy / dx


def compute_x1(f, a=0, b=1):
    """
    Compute x-coordinate of centroid of 2D region.
    x_1 = integral(x * f(x) dx) / integral(f(x) dx)
    """
    numerator = integrate_1d(lambda x: x * f(x), a, b)
    denominator = integrate_1d(lambda x: f(x), a, b)
    return numerator / denominator


def compute_x2(f, a=0, b=1):
    """
    Compute x-coordinate of centroid of solid of revolution.
    x_2 = integral(x * f(x)^2 dx) / integral(f(x)^2 dx)
    """
    numerator = integrate_1d(lambda x: x * f(x)**2, a, b)
    denominator = integrate_1d(lambda x: f(x)**2, a, b)
    return numerator / denominator


def verify_double_integral(f, a=0, b=1):
    """
    Verify that the double integral I > 0.
    I = integral integral (y - x) * f(x) * f(y) * [f(y) - f(x)] dx dy
    """
    def integrand(x, y):
        return (y - x) * f(x) * f(y) * (f(y) - f(x))

    result = integrate_2d(integrand, a, b)
    return result


def verify_expansion(f, a=0, b=1):
    """
    Verify that I = 2 * [integral(x*f^2)*integral(f) - integral(x*f)*integral(f^2)]
    """
    # Compute I directly
    I_direct = verify_double_integral(f, a, b)

    # Compute via expansion
    int_xf2 = integrate_1d(lambda x: x * f(x)**2, a, b)
    int_f = integrate_1d(lambda x: f(x), a, b)
    int_xf = integrate_1d(lambda x: x * f(x), a, b)
    int_f2 = integrate_1d(lambda x: f(x)**2, a, b)

    I_expansion = 2 * (int_xf2 * int_f - int_xf * int_f2)

    return I_direct, I_expansion, abs(I_direct - I_expansion)


def test_function(name, f, a=0, b=1):
    """Test a specific function."""
    print(f"\n{'='*60}")
    print(f"Testing: {name}")
    print(f"{'='*60}")

    # Compute centroids
    x1 = compute_x1(f, a, b)
    x2 = compute_x2(f, a, b)

    print(f"x_1 = {x1:.10f}")
    print(f"x_2 = {x2:.10f}")
    print(f"x_2 - x_1 = {x2 - x1:.10f}")
    print(f"x_1 < x_2: {x1 < x2}")

    # Verify double integral
    I = verify_double_integral(f, a, b)
    print(f"\nDouble integral I = {I:.10f}")
    print(f"I > 0: {I > 0}")

    # Verify expansion
    I_direct, I_expansion, error = verify_expansion(f, a, b)
    print(f"\nExpansion verification:")
    print(f"  I (direct) = {I_direct:.10f}")
    print(f"  I (expansion) = {I_expansion:.10f}")
    print(f"  Error = {error:.2e}")

    # Verify the inequality from expansion
    int_xf2 = integrate_1d(lambda x: x * f(x)**2, a, b)
    int_f = integrate_1d(lambda x: f(x), a, b)
    int_xf = integrate_1d(lambda x: x * f(x), a, b)
    int_f2 = integrate_1d(lambda x: f(x)**2, a, b)

    lhs = int_xf2 * int_f
    rhs = int_xf * int_f2
    print(f"\nInequality check:")
    print(f"  int(x*f^2)*int(f) = {lhs:.10f}")
    print(f"  int(x*f)*int(f^2) = {rhs:.10f}")
    print(f"  Difference = {lhs - rhs:.10f}")
    print(f"  LHS > RHS: {lhs > rhs}")

    return x1 < x2 and I > 0


def main():
    """Run all tests."""
    print("PUTNAM 2025 B2 - NUMERICAL VERIFICATION")
    print("="*60)

    all_passed = True

    # Test 1: f(x) = x
    all_passed &= test_function("f(x) = x", lambda x: x)

    # Test 2: f(x) = x^2
    all_passed &= test_function("f(x) = x^2", lambda x: x**2)

    # Test 3: f(x) = e^x - 1
    all_passed &= test_function("f(x) = e^x - 1", lambda x: np.exp(x) - 1)

    # Test 4: f(x) = sqrt(x)
    all_passed &= test_function("f(x) = sqrt(x)", lambda x: np.sqrt(x))

    # Test 5: f(x) = x^3
    all_passed &= test_function("f(x) = x^3", lambda x: x**3)

    # Test 6: f(x) = tan(pi*x/4) (maps [0,1] to [0, 1])
    all_passed &= test_function("f(x) = tan(pi*x/4)", lambda x: np.tan(np.pi * x / 4))

    # Test 7: f(x) = ln(1 + x)
    all_passed &= test_function("f(x) = ln(1 + x)", lambda x: np.log(1 + x))

    # Test 8: f(x) = x / (1 - x/2) (strictly increasing, convex)
    all_passed &= test_function("f(x) = x / (1 - x/2)", lambda x: x / (1 - x/2))

    # Test 9: f(x) = sinh(x)
    all_passed &= test_function("f(x) = sinh(x)", lambda x: np.sinh(x))

    # Test 10: Very steep function f(x) = e^(5*x) - 1
    all_passed &= test_function("f(x) = e^(5*x) - 1", lambda x: np.exp(5*x) - 1)

    print(f"\n{'='*60}")
    print(f"FINAL RESULT: {'ALL TESTS PASSED' if all_passed else 'SOME TESTS FAILED'}")
    print(f"{'='*60}")

    return all_passed


if __name__ == "__main__":
    success = main()
    exit(0 if success else 1)
