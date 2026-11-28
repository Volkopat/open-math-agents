import Mathlib

/-!
# A363152: the denominator of Sum_j Bernoulli(j,1)*Bernoulli(2n-j,1) is cubefree

Source: https://oeis.org/A363152

A363152 (offset 0): `a(n) = denominator(Sum_{j=0..2*n} Bernoulli(j, 1) * Bernoulli(2*n - j, 1))`:
1, 12, 180, 630, 2100, 3465, 6306300, 30030, …  The sums themselves are
`r(n) = 1, 7/12, -7/180, 23/630, -121/2100, 481/3465, …`.

Conjecture (Peter Luschny, May 18 2023): `a(n)` is cubefree. (An integer is cubefree if it is
not divisible by the cube of a prime number.)

Conventions:
- `Bernoulli(j, 1)` is the value at 1 of the `j`-th Bernoulli polynomial, i.e. the Bernoulli
  number with the convention `B_1 = +1/2`. This is Mathlib's `bernoulli'` (`bernoulli' 0 = 1`,
  `bernoulli' 1 = 1/2`, `bernoulli' 2 = 1/6`, …).
- The sum is formed in `ℚ` over `j` in `Finset.range (2*n + 1)`, and `a n` is its denominator in
  lowest terms (`Rat.den`). The subtraction `2*n - j` is exact for `j ≤ 2*n`.
- Cubefree is stated as in the entry: no prime `p` has `p^3` dividing `a n`.
-/

namespace OMA.S_oeis_a363152

/-- A363152: the denominator of `Sum_{j=0..2n} B'_j * B'_{2n-j}`, with `B'_1 = 1/2`. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (2 * n + 1), bernoulli' j * bernoulli' (2 * n - j)).den

theorem main : ∀ n p : ℕ, Nat.Prime p → ¬ p ^ 3 ∣ a n := by
  sorry

end OMA.S_oeis_a363152
