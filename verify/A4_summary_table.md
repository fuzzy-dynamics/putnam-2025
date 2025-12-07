# Putnam 2025 A4 - Numerical Testing Summary

## Test Results Summary

### Simple Weyl Construction Test (A_i = X^a Z^b)

| n    | k    | n=k²? | sqrt(n) | Expected | Weyl Pattern Matches | Result  |
|------|------|-------|---------|----------|---------------------|---------|
| 4    | 2    | YES   | 2.00    | k=2      | NO (3 mismatches)   | FAILED  |
| 9    | 3    | YES   | 3.00    | k=3      | NO (15 mismatches)  | FAILED  |
| 16   | 4    | YES   | 4.00    | k=4      | NO (44 mismatches)  | FAILED  |
| 25   | 5    | YES   | 5.00    | k=5      | NO (75 mismatches)  | FAILED  |
| 36   | 6    | YES   | 6.00    | k=6      | NO (171 mismatches) | FAILED  |
| 49   | 7    | YES   | 7.00    | k=7      | NO (203 mismatches) | FAILED  |
| 64   | 8    | YES   | 8.00    | k=8      | NO (384 mismatches) | FAILED  |
| 81   | 9    | YES   | 9.00    | k=9      | NO (495 mismatches) | FAILED  |
| 100  | 10   | YES   | 10.00   | k=10     | NO (755 mismatches) | FAILED  |
| 121  | 11   | YES   | 11.00   | k=11     | NO (759 mismatches) | FAILED  |
| 144  | 12   | YES   | 12.00   | k=12     | NO (1500 mismatches)| FAILED  |
| 169  | 13   | YES   | 13.00   | k=13     | NO (1235 mismatches)| FAILED  |
| 196  | 14   | YES   | 14.00   | k=14     | NO (1995 mismatches)| FAILED  |
| 225  | 15   | YES   | 15.00   | k=15     | NO (2475 mismatches)| FAILED  |
| 2025 | 45   | YES   | 45.00   | k=45     | NO (69435 mismatches)| FAILED |

**Conclusion:** Simple Weyl construction X^a Z^b does NOT work for ANY tested value!

### Pattern of Mismatches

For all tested cases, the primary mismatch pattern is:
1. **Should NOT commute but DO:** Pairs like (0,2), (0,3), etc. in cycle are not adjacent, but Weyl matrices commute
2. **Should commute but DON'T:** Pairs like (1,2) are adjacent in cycle, but Weyl matrices don't commute

The Weyl commutation condition is: bc ≡ ad (mod k) where i=ak+b, j=ck+d
This does NOT match cycle adjacency condition: |i-j| ∈ {1, n-1}

### Independent Set Analysis

| n    | sqrt(n) | Max Independent Set | Can find size=sqrt(n)? | Spacing |
|------|---------|---------------------|------------------------|---------|
| 4    | 2       | 2                   | YES                    | 2       |
| 9    | 3       | 4                   | YES                    | 3       |
| 16   | 4       | 8                   | YES                    | 4       |
| 25   | 5       | 12                  | YES                    | 5       |
| 49   | 7       | 24                  | YES                    | 7       |
| 100  | 10      | 50                  | YES                    | 10      |
| 2025 | 45      | 1012                | YES                    | 45      |

**Observation:** For cycle C_n, we can always find an independent set of size ceil(sqrt(n)) by taking vertices {0, k, 2k, 3k, ...} with spacing k = ceil(sqrt(n)).

**However:** This does NOT prove that k matrices require dimension k!

### Numerical Optimization Attempts

Attempted gradient descent to find matrices for small n:

| n  | k tested | Result         | Note                          |
|----|----------|----------------|-------------------------------|
| 5  | 2,3,4    | All failed     | No convergence                |
| 6  | 2,3,4    | All failed     | No convergence                |
| 7  | 2,3,4    | All failed     | No convergence                |
| 8  | 2,3,4    | All failed     | No convergence                |
| 9  | 3,4,5    | All failed     | No convergence                |
| 10 | 3,4,5    | All failed     | No convergence                |
| 15 | 3,4,5    | All failed     | No convergence                |
| 20 | 4,5,6    | All failed     | No convergence                |
| 25 | 5,6,7    | All failed     | Numerical instability (NaN)   |

**Conclusion:** Numerical optimization is extremely difficult, suggesting:
- Problem is highly constrained
- Random initialization doesn't work
- Need structured/algebraic construction

## Key Questions

1. **What is the correct construction?**
   - Not A_i = X^a Z^b
   - Possibly A_i = ζ^f(a,b) X^a Z^b with special phase function f?
   - Or completely different approach?

2. **What is the actual lower bound?**
   - Independent set argument is insufficient
   - Need representation-theoretic proof
   - Or explicit proof that k < 45 fails

3. **What is minimum k as function of n?**
   - For perfect squares n = m²: k = m?
   - For general n: k = ceil(sqrt(n))?
   - Or different formula?

## Theoretical Claims to Verify

From the solution file:

- [X] VERIFIED: Can find independent set of size 45 in C_2025
- [ ] UNVERIFIED: This implies k ≥ 45 (argument incomplete)
- [ ] UNVERIFIED: Orthogonal rank(C_2025) = 45
- [ ] FAILED: Weyl construction with k=45 works (construction incorrect)

## Recommendations

1. **Find correct Weyl phase function:**
   - Systematically solve for f(a,b) that makes A_i = ζ^f(a,b) X^a Z^b work
   - Or determine if phase modification is sufficient

2. **Verify lower bound rigorously:**
   - Use representation theory of commutator algebras
   - Or find explicit obstruction for k < 45

3. **Test small cases explicitly:**
   - For n=4, k=2: can we construct matrices?
   - For n=9, k=3: can we construct matrices?
   - Build intuition from small cases

4. **Search Putnam archives:**
   - Has this type of problem appeared before?
   - Are there known techniques for matrix commutativity patterns?
