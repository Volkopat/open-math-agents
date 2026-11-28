import Mathlib

/-!
# OEIS A110515: the Jacobi-symbol formula for the sequence array of (1 - x + x^2 + x^3)/(1 - x^4)

Source: https://oeis.org/A110515 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Paul Barry, Jul 24 2005), offset 0, read by rows: Sequence array for (1 - x + x^2 +
x^3)/(1 - x^4). The formula section states: Column k has g.f. x^k*(1 - x + x^2 + x^3)/(1 - x^4).
It also states: T(n, k) = if(k <= n, Jacobi(2^(n-k), 2(n-k)+1), 0) [conjecture].

Formalization notes:
* G = (1 - x + x^2 + x^3)/(1 - x^4) is a formal power series over Q (1 - x^4 has constant term 1,
  so it is invertible). Column k has g.f. x^k * G, so T(n, k) is the coefficient of x^(n-k) in G
  for k <= n, and 0 for k > n.
* Jacobi(a, m) is the Jacobi symbol `jacobiSym a m`, an integer, compared with T(n, k) in Q.
* Controls: the definitions give the rows 1; -1, 1; 1, -1, 1; 1, 1, -1, 1 at T(0,0), T(1,0),
  T(2,0), T(3,0), T(3,1), T(3,2), as in the entry.
-/

namespace OMA.S_oeis_a110515

open PowerSeries

/-- The generating function `(1 - x + x^2 + x^3)/(1 - x^4)` over `ℚ`. -/
noncomputable def G : ℚ⟦X⟧ := (1 - X + X ^ 2 + X ^ 3) * (1 - X ^ 4)⁻¹

/-- A110515: the sequence array of `G`. -/
noncomputable def T (n k : ℕ) : ℚ := if k ≤ n then coeff (n - k) G else 0

/-- Barry's conjecture: T(n, k) = Jacobi(2^(n-k), 2(n-k)+1) for k <= n, and 0 otherwise. -/
theorem main : ∀ n k : ℕ,
    T n k = if k ≤ n then ((jacobiSym ((2 : ℤ) ^ (n - k)) (2 * (n - k) + 1) : ℤ) : ℚ) else 0 := by
  sorry

end OMA.S_oeis_a110515
