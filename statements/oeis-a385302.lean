import Mathlib

/-!
# A385302: Least common multiple of {n^n-1, n^(n-1)-1, ..., n-1}.

Source: https://oeis.org/A385302
Credit: @agchua

Formula section of A385302 (by Avery Diep, Jun 24 2025):
  Conjecture: a(n) = Product_{k=1..n} Cyclotomic[k, n], i.e., a(n) = A156291(A000217(n)-1).

The sequence A385302 has offset 0, with a(0) = 1 (empty lcm), a(1) = 0, a(2) = 3, a(3) = 104,
a(4) = 5355. The first equality holds for all n >= 0 (empty product 1 at n = 0, and
Phi_1(1) = 0 at n = 1). A000217(n) = n*(n+1)/2 are the triangular numbers and A156291 is the
1-indexed triangle read by rows T(r, m) = Product_{k=1..r} Phi_k(m + 1) for 1 <= m <= r
(offset 1), so A000217(n) - 1 >= 1 for n >= 2, giving the second equality for all n >= 2.
-/

namespace OMA.S_oeis_a385302

/-- A385302(n): least common multiple of {n^k - 1 | 1 <= k <= n}, with a(0) = 1. -/
def a (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).lcm (fun k => n ^ k - 1)

/-- A000217(n): the n-th triangular number n*(n+1)/2. -/
def tri (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A156291(j) for j >= 1: 1-indexed flattening by rows of the triangle
    T(r, m) = Product_{k=1..r} Phi_k(m + 1) for r >= 1 and 1 <= m <= r. -/
noncomputable def A156291 (j : ℕ) : ℤ :=
  if 1 ≤ j then
    let r := sInf {r : ℕ | j ≤ tri r}
    let m := j - tri (r - 1)
    ∏ k ∈ Finset.Icc 1 r, (Polynomial.cyclotomic k ℤ).eval ((m + 1 : ℕ) : ℤ)
  else 0

/-- Conjecture of A385302: a(n) equals Product_{k=1..n} Phi_k(n) for all n >= 0,
    and equivalently A156291(A000217(n) - 1) for all n >= 2. -/
theorem main :
    (∀ n : ℕ, (a n : ℤ) = ∏ k ∈ Finset.Icc 1 n, (Polynomial.cyclotomic k ℤ).eval (n : ℤ)) ∧
    (∀ n : ℕ, 2 ≤ n → (a n : ℤ) = A156291 (tri n - 1)) := by
  sorry

end OMA.S_oeis_a385302
