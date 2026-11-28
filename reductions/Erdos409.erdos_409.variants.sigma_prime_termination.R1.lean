import FormalConjectures.ErdosProblems.«409»

-- Reduction Erdos409.erdos_409.variants.sigma_prime_termination.R1
-- Credit: @sanjog-p

/-!
# A kernel-checked initial range, and the open rest

The question asks whether iterating `m ↦ σ(m) - 1` from any `n > 1` always reaches a prime.
For composite `m > 1` the map strictly increases `m`, so the question is whether an orbit can
avoid the primes forever; no argument is known.

* `H1`: the statement for `1 < n ≤ 300`. A finite check: every orbit reaches a prime within 6
  steps and stays below 2100; divisor sums and primality are computed in the Lean kernel.
* `H2`: the statement for every `n > 300`. This is the open question.
-/

namespace OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1

/-- The verified range. -/
def H1 : Prop := ∀ n : ℕ, 1 < n → n ≤ 300 →
  ∃ i, ((fun m => ArithmeticFunction.sigma 1 m - 1)^[i] n).Prime

/-- The open part. -/
def H2 : Prop := ∀ n : ℕ, 300 < n →
  ∃ i, ((fun m => ArithmeticFunction.sigma 1 m - 1)^[i] n).Prime

theorem main : H1 → H2 → type_of% @Erdos409.erdos_409.variants.sigma_prime_termination := by
  intro h1 h2 n hn
  by_cases h : n ≤ 300
  · exact h1 n hn h
  · exact h2 n (by omega)

end OMA.R_Erdos409_erdos_409_variants_sigma_prime_termination_R1
