import Mathlib

/-!
# OEIS A000089: Dirichlet inverse of the number of square roots of `-1`

Source: https://oeis.org/A000089
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of solutions of `x² + 1 ≡ 0 (mod n)`. Conjecture (Mathar, 2010; marked
correct in the entry): the Dirichlet inverse of `a`, `1, -1, 0, 1, -2, 0, 0, -1, 0, 2, …`, equals
A091400 apart from signs, where `A091400(n) = ∏_{odd primes p ∣ n} (1 + (-1/p))`
(`(-1/p) = 1` if `p ≡ 1 (mod 4)` and `-1` if `p ≡ 3 (mod 4)`).

Conventions:
* Arithmetic functions are Mathlib's `ArithmeticFunction ℤ` with Dirichlet convolution as
  multiplication; `a(1) = 1`, so the inverse exists, and `main` quantifies over any `g` with
  `a * g = 1`.
* 'Apart from signs' means `|g(n)| = A091400(n)` for all `n ≥ 1`.
-/

namespace OMA.S_oeis_a000089

open ArithmeticFunction

/-- Number of `x mod n` with `x² + 1 ≡ 0 (mod n)` (and `0` at `n = 0`). -/
def a : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else
      (((Finset.range n).filter fun x => (x ^ 2 + 1) % n = 0).card : ℤ), by simp⟩

/-- `(-1/p)` for odd primes. -/
def chi (p : ℕ) : ℤ := if p % 4 = 1 then 1 else -1

/-- A091400. -/
def A091400 (n : ℕ) : ℤ :=
  ∏ p ∈ n.primeFactors.filter (fun p => p ≠ 2), (1 + chi p)

/-- The Dirichlet inverse of `a` is A091400 up to sign. -/
theorem main : ∀ g : ArithmeticFunction ℤ, a * g = 1 → ∀ n : ℕ, 1 ≤ n → |g n| = A091400 n := by
  sorry

end OMA.S_oeis_a000089
