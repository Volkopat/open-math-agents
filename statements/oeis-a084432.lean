import Mathlib

/-!
# A084432: Expansion of 2/(1-x) + Sum_{k>=0} t^2(3-t)/(1+t)/(1-t)^2, where t=x^2^k.

Source: https://oeis.org/A084432
Credit: @rickmanelius

Conjecture (Joseph M. Shunia, Aug 27 2024): a(n) is the number of integer solutions (x,y,z) to
the Diophantine equation 2^x*(y+z) = n, where 0 <= x,y,z <= n.

Formalization notes:
* Power series in x are `PowerSeries ℚ`, with `X` for x. Dividing by a power series whose
  constant coefficient is nonzero is multiplying by its inverse (`PowerSeries` over a field has
  an inverse; 1 - x, 1 + t and (1 - t)^2 all have constant coefficient 1). So 2/(1-x) is
  `2 * (1 - X)⁻¹`, and the k-th summand t^2(3-t)/(1+t)/(1-t)^2 with t = x^(2^k) is `term k`,
  written with `X ^ 2 ^ k` (that is, X ^ (2 ^ k)) in place of t. Here x^2^k is x^(2^k), as in
  the PARI program of the entry (x^2^k) and its formula G.f.: A(x) = Sum_{k>=0}
  (1/(1 - x^(2^k))^2 - 1); the reading (x^2)^k would give t = 1 for k = 0.
* The k-th summand is t^2 = x^(2^(k+1)) times a power series, so only finitely many summands
  (those with 2^(k+1) ≤ n) have a nonzero coefficient of x^n. The coefficient of x^n in the
  infinite sum is the sum of these coefficients over all k ≥ 0, written as a `finsum`.
* The offset is 1: a(n), for n ≥ 1, is the coefficient of x^n (the constant coefficient 2 is not
  a term). These definitions give 2, 5, 4, 10, 6, 11, 8, 19, 10, 17, ..., matching the 74 listed
  terms (checked by computer with exact rational arithmetic).
* The solutions (x, y, z) are counted with x, y, z natural numbers in [0, n] (the integers with
  0 <= x,y,z <= n), as triples (x, (y, z)) in `Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n`.
  The count is a natural number, cast to ℚ to compare it with a(n).
* The conjecture is stated for every n ≥ 1 (the offset).
-/

namespace OMA.S_oeis_a084432

open PowerSeries

/-- The summand t^2 (3 - t) / (1 + t) / (1 - t)^2 with t = x^(2^k), as a power series in x. -/
noncomputable def term (k : ℕ) : PowerSeries ℚ :=
  (X ^ 2 ^ k) ^ 2 * (3 - X ^ 2 ^ k) * (1 + X ^ 2 ^ k)⁻¹ * ((1 - X ^ 2 ^ k) ^ 2)⁻¹

/-- A084432(n) for n ≥ 1: the coefficient of x^n in 2/(1-x) + Sum_{k>=0} term k. -/
noncomputable def a (n : ℕ) : ℚ := coeff n (2 * (1 - X)⁻¹) + ∑ᶠ k : ℕ, coeff n (term k)

/-- Shunia's conjecture: for n ≥ 1, a(n) is the number of triples (x, y, z) with
0 ≤ x, y, z ≤ n and 2^x * (y + z) = n. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    a n = (((Finset.Icc 0 n ×ˢ Finset.Icc 0 n ×ˢ Finset.Icc 0 n).filter
      (fun s : ℕ × ℕ × ℕ => 2 ^ s.1 * (s.2.1 + s.2.2) = n)).card : ℚ) := by
  sorry

end OMA.S_oeis_a084432
