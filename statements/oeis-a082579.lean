import Mathlib

/-!
# A082579: Expansion of e.g.f.: exp( x/(1-x)^2 ).

Source: https://oeis.org/A082579
Credit: @maaaakks

Conjecture (Peter Bala, Nov 14 2017, quoted from the OEIS entry):
"It appears that the sequence taken modulo 10 is periodic with period 5. More generally,
we conjecture that for k = 2,3,4,... the difference a(n+k) - a(n) is divisible by k: if true,
then for each k the sequence a(n) taken modulo k would be periodic with period dividing k."
(The entry adds: "The above conjecture is true - see the Bala link.")

Definition. The offset is 0. We use the explicit formula from the entry
(SageMath/Magma programs of G. C. Greubel, equivalent to the formula
`a(n) = n! * Sum_{k=0..n} binomial(n+k-1, 2*k-1)/k!`):
  `a(n) = Sum_{k=0..n} n!/k! * binomial(n+k-1, n-k)`.
It equals the e.g.f. coefficients because
`exp(f) = Sum_k f^k / k!` with `f = x/(1-x)^2`, and
`[x^n] f^k = [x^(n-k)] (1-x)^(-2k) = binomial(n+k-1, n-k)`, so
`n! [x^n] exp(f) = Sum_{k=0..n} n!/k! * binomial(n+k-1, n-k)`.
In Lean, `n.factorial / k.factorial` is exact for `k ≤ n`, and truncated subtraction gives the
right boundary values: the `k = 0` term is `binomial(0,0) = 1` for `n = 0` and
`binomial(n-1, n) = 0` for `n ≥ 1`. This reproduces the OEIS data
1, 1, 5, 31, 241, 2261, 24781, ... (checked for n = 0..20).
-/

namespace OMA.S_oeis_a082579

/-- A082579: `a n = ∑_{k=0}^{n} n!/k! * C(n+k-1, n-k)`, i.e. `n! [x^n] exp(x/(1-x)^2)`. -/
def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.factorial / k.factorial * (n + k - 1).choose (n - k)

theorem main : ∀ k : ℕ, 2 ≤ k → ∀ n : ℕ, (k : ℤ) ∣ (a (n + k) : ℤ) - (a n : ℤ) := by
  sorry

end OMA.S_oeis_a082579
