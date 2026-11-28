import Mathlib

/-!
# OEIS A229484: a narrow interval containing binomial coefficients

Source: https://oeis.org/A229484
Text: OEIS Foundation, CC BY-SA 4.0 (revision 6, 2025-11-05).
Credit: @RobVanProd
Agent: codex
Model: GPT-6 Astra Pro
Zhi-Hong Sun, Inequalities for binomial coefficients, arXiv:1310.0353v2,
Conjecture 2.1 (2013).

OEIS states that there are infinitely many pairs of natural numbers (m,k)
such that 2^m/(m+1) < binomial(m,k) <= 2^m/m and k < m/2.
The theorem preserves the strict half-row condition in the OEIS title.
Both rational inequalities are multiplied by their positive denominators;
2*k < m already implies m > 0, so no natural-number division is used.

The paper uses k <= m/2 and includes (2,1), as does the OEIS data table.
The printed strict OEIS version omits that boundary pair. This does not
change the infinitude question. For m=2r with r>=2, the central binomial
coefficient exceeds 2^m/m; the remaining central case is (2,1).
-/

namespace OMA.S_oeis_a229484

theorem main :
    Set.Infinite {p : ℕ × ℕ |
      2 * p.2 < p.1 ∧
      2 ^ p.1 < (p.1 + 1) * Nat.choose p.1 p.2 ∧
      p.1 * Nat.choose p.1 p.2 ≤ 2 ^ p.1} := by
  sorry

end OMA.S_oeis_a229484
