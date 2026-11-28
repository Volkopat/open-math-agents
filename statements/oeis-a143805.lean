import Mathlib

/-!
# A143805: Eigensequence of triangle A130534.

Source: https://oeis.org/A143805
Credit: @Harsha0912

A130534 is the triangle T(n, k), 0 <= k <= n, of coefficients of (x+1)(x+2)...(x+n) in increasing
powers of x (T(n, k) = |s(n+1, k+1)|). Its eigensequence (offset 0) is a(0) = 1 and
a(n) = Sum_{k=0..n-1} T(n-1, k) * a(k) for n > 0 (equivalently the entry's formula
a(n) = Sum_{k=0..n-1} (-1)^(n-k-1) * Stirling1(n, k+1) * a(k)).

Conjecture (Mikhail Kurkov): a(n) = R(n, 0) where R(n, k) = R(n-1, n-1) + Sum_{j=0..k-1} (j+1)*R(n-1, j)
for 0 <= k <= n with R(0, 0) = 1. `R` below is that recursion; values with k > n are never used.
-/

namespace OMA.S_oeis_a143805

/-- A130534: coefficients of (x+1)(x+2)...(x+n), so T(n+1, k) = (n+1) T(n, k) + T(n, k-1). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | n + 1, 0 => (n + 1) * T n 0
  | n + 1, k + 1 => (n + 1) * T n (k + 1) + T n k

/-- A143805: a(0) = 1, a(n) = Sum_{k=0..n-1} T(n-1, k) * a(k). -/
def a : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ k : Fin (n + 1), T n k * a k
decreasing_by all_goals omega

/-- Kurkov's triangle: R(0, 0) = 1, R(n, k) = R(n-1, n-1) + Sum_{j=0..k-1} (j+1) * R(n-1, j). -/
def R : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, k => R n n + ∑ j ∈ Finset.range k, (j + 1) * R n j

theorem main : ∀ n : ℕ, a n = R n 0 := by
  sorry

end OMA.S_oeis_a143805
