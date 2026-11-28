import Mathlib

/-!
# A303273: Array T(n,k) = binomial(n, 2) + k*n + 1 read by antidiagonals

Source: https://oeis.org/A303273 (conjectures in the comments of the entry)

Conjectures: T(2*n,n+4) = A186353(4*n+1); T(2*n,n+5) = A184103(8*n+1);
T(n+2,2*n) = A249013(5*n+4).

Conventions:
* `T n k` (n, k >= 0, offset 0 as in the entry) is binomial(n, 2) + k*n + 1.
* A186353 (offset 1) is the adjusted joint rank sequence of f(i) = 2i - 1 (the odd numbers)
  and g(j) = j(j+1)/2 (the triangular numbers), with f(i) after g(j) when f(i) = g(j):
  A186353(n) is the position of g(n) in the merged list. The terms placed before or at g(n)
  are g(1), ..., g(n) (g is strictly increasing) and the odd numbers f(i) < g(n) (an odd
  number equal to g(n) comes after it), so A186353(n) = n + #{i >= 1 : 2i - 1 < g(n)};
  such i satisfy i <= g(n), so the count is taken over i in [1, g(n)].
* A184103 (offset 1): a(n) = n - 1 + ceiling(n^2/16), with the ceiling taken in ℚ.
* A249013 (offset 1): a(n) = floor((n - 1) * (n + 4) / 10), with the floor taken in ℚ.
* The three identities are stated for every n >= 0 (all indices are then in range), in the
  integers.
-/

namespace OMA.S_oeis_a303273

/-- T(n,k) = binomial(n, 2) + k*n + 1. -/
def T (n k : ℕ) : ℕ := n.choose 2 + k * n + 1

/-- A186353(n): the joint rank of the n-th triangular number among the odd numbers and the
triangular numbers (odd numbers placed after equal triangular numbers). -/
def A186353 (n : ℕ) : ℕ :=
  n + ((Finset.Icc 1 (n * (n + 1) / 2)).filter fun i => 2 * i - 1 < n * (n + 1) / 2).card

/-- A184103(n) = n - 1 + ceiling(n^2/16). -/
noncomputable def A184103 (n : ℕ) : ℤ := (n : ℤ) - 1 + ⌈((n : ℚ) ^ 2 / 16)⌉

/-- A249013(n) = floor((n - 1) * (n + 4) / 10). -/
noncomputable def A249013 (n : ℕ) : ℤ := ⌊(((n : ℚ) - 1) * ((n : ℚ) + 4) / 10)⌋

theorem main : ∀ n : ℕ,
    T (2 * n) (n + 4) = A186353 (4 * n + 1) ∧
    (T (2 * n) (n + 5) : ℤ) = A184103 (8 * n + 1) ∧
    (T (n + 2) (2 * n) : ℤ) = A249013 (5 * n + 4) := by
  sorry

end OMA.S_oeis_a303273
