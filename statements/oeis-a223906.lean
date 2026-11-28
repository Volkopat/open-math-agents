import Mathlib

/-!
# A223906: Poly-Cauchy numbers of the second kind -hat c_3^(-n)

Source: https://oeis.org/A223906
Credit: @ivillar

The poly-Cauchy numbers of the second kind (Komatsu) are, for n ≥ 0 and integer k,
  hat c_n^(k) = (-1)^n * Sum_{m=0..n} |stirling1(n,m)| / (m+1)^k,
where |stirling1(n,m)| are the unsigned Stirling numbers of the first kind (Mathlib's
`Nat.stirlingFirst`), as in the comment of A223906. The sequence (offset 1, Takao Komatsu) is
a(n) = -hat c_3^(-n).

Conjecture (Colin Barker, Mar 31 2013):
  a(n) = 2^(1+n) + 3^(1+n) + 4^n, and
  G.f.: -x*(144*x^2 - 102*x + 17) / ((2*x - 1)*(3*x - 1)*(4*x - 1)),
i.e. Sum_{n ≥ 1} a(n) x^n equals that rational function, taken as a formal power series over ℚ.
-/

namespace OMA.S_oeis_a223906

open PowerSeries

/-- Poly-Cauchy number of the second kind hat c_n^(k). -/
noncomputable def hatC (n : ℕ) (k : ℤ) : ℚ :=
  (-1) ^ n * ∑ m ∈ Finset.range (n + 1), (Nat.stirlingFirst n m : ℚ) / ((m : ℚ) + 1) ^ k

/-- a(n) = -hat c_3^(-n). -/
noncomputable def a (n : ℕ) : ℚ := -hatC 3 (-(n : ℤ))

/-- Barker's conjecture: the closed form for n ≥ 1 and the generating function
(the coefficient of x^0 is 0 since the sequence starts at n = 1). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → a n = 2 ^ (1 + n) + 3 ^ (1 + n) + 4 ^ n) ∧
    mk (fun n => if n = 0 then 0 else a n) =
      (-X * (144 * X ^ 2 - 102 * X + 17)) * ((2 * X - 1) * (3 * X - 1) * (4 * X - 1))⁻¹ := by
  sorry

end OMA.S_oeis_a223906
