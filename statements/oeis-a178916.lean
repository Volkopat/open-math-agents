import Mathlib

/-!
# A178916: Triangular array a(n,k) read by rows: nextprime(k*n!)-k*n!. For 1<=k<=n.

Source: https://oeis.org/A178916
Credit: @keiichisince1986-bot

A178916 is the sequence `a(n)` named in the title. The entry states:
Conjecture: for every n>1 and 1<=k<=n there is a prime in the interval [k*n!+1, k*n!+3*n*log(n)^2].

Conventions:
- `log` is the natural logarithm `Real.log`; the upper end of the interval is a real number.
-/

namespace OMA.S_oeis_a178916

theorem main :
    ∀ n : ℕ, 1 < n → ∀ k : ℕ, 1 ≤ k → k ≤ n → ∃ p : ℕ, p.Prime ∧ k * n.factorial + 1 ≤ p ∧
      (p : ℝ) ≤ k * n.factorial + 3 * n * Real.log n ^ 2 := by
  sorry

end OMA.S_oeis_a178916
