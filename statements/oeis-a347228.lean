import Mathlib

/-!
# A347228: Dirichlet inverse of A344695(n) = gcd(sigma(n), psi(n))

Source: https://oeis.org/A347228

Conjecture (OEIS A347228):
No zeros occur in the Dirichlet inverse of `A344695(n) = gcd(σ(n), ψ(n))`, where `σ(n)`
is the sum of divisors (A000203) and `ψ(n)` is Dedekind's psi function (A001615).

Conventions:
- Offset: `1`; first terms of A347228: `1, -3, -4, 8, -6, 12, -8, -24, 15, 18, -12, ...`.
- Checked up to `n = 2^21`.
- For `n ≥ 1`, Dedekind's psi function is `ψ(n) = ∏_{p ∣ n} p^{v_p(n) - 1} * (p + 1)`.
- The Dirichlet inverse `a : ℕ → ℤ` of `A344695` is uniquely characterized on `n ≥ 1` by
  `a 1 = 1` and `∑ d ∈ n.divisors, (a344695 (n / d) : ℤ) * a d = 0` for all `n ≥ 2`.
-/

namespace OMA.S_oeis_a347228

/-- Sum of positive divisors `σ(n)` of `n : ℕ` (OEIS A000203). -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Dedekind's psi function `ψ(n)` for `n ≥ 1` (OEIS A001615). -/
def psi (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

/-- `gcd(σ(n), ψ(n))` (OEIS A344695). -/
def a344695 (n : ℕ) : ℕ :=
  Nat.gcd (sigma n) (psi n)

/-- Predicate stating that `a : ℕ → ℤ` is the Dirichlet inverse of `A344695` (OEIS A347228). -/
def IsDirichletInv (a : ℕ → ℤ) : Prop :=
  a 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → ∑ d ∈ n.divisors, (a344695 (n / d) : ℤ) * a d = 0

/-- Conjecture: the Dirichlet inverse of `gcd(σ(n), ψ(n))` has no zero terms for `n ≥ 1`. -/
theorem main :
    ∀ a : ℕ → ℤ, IsDirichletInv a → ∀ n : ℕ, 1 ≤ n → a n ≠ 0 := by
  sorry

end OMA.S_oeis_a347228
