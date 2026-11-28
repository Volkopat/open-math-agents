import Mathlib

/-!
# Almost-primes produced by `n² + n + (d+1)/4` for a positive proportion of discriminants?

Source: https://mathoverflow.net/questions/515446
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (asker): do there exist constants `θ > 0` and `α > 0` such that for a positive
proportion of fundamental discriminants `d ≤ Y` (as `Y → ∞`) there is an integer `n` with
`1 ≤ n ≤ d^θ` for which `n² + n + (d+1)/4` is either a `P_r`-number for some fixed `r`, or at
least has a prime factor larger than `d^α`?

Conventions:
* `(d + 1)/4` must be an integer, so the discriminants are `-d` with `d ≡ 3 (mod 4)`; `-d` is then
  fundamental iff `d` is squarefree. 'Positive proportion' means: some `c > 0` with, for all large
  `Y`, at least `c ·` (number of such `d ≤ Y`) of them good.
* A `P_r`-number has at most `r` prime factors counted with multiplicity (`Ω ≤ r`); `r` is fixed
  in advance along with `θ, α`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_mo_515446

open ArithmeticFunction

/-- `d` gives a fundamental discriminant `-d` with `(d+1)/4` integral. -/
def Admissible (d : ℕ) : Prop := d % 4 = 3 ∧ Squarefree d

/-- `d` is good for `θ, α, r`. -/
def Good (θ α : ℝ) (r d : ℕ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ (d : ℝ) ^ θ ∧
    (cardFactors (n ^ 2 + n + (d + 1) / 4) ≤ r ∨
      ∃ p : ℕ, p.Prime ∧ p ∣ n ^ 2 + n + (d + 1) / 4 ∧ (d : ℝ) ^ α < p)

/-- A positive proportion of admissible `d` are good. -/
theorem main : ∃ (θ α : ℝ) (r : ℕ) (c : ℝ), 0 < θ ∧ 0 < α ∧ 0 < c ∧ ∃ Y₀ : ℕ, ∀ Y ≥ Y₀,
    c * ({d : ℕ | d ≤ Y ∧ Admissible d}.ncard : ℝ) ≤
      ({d : ℕ | d ≤ Y ∧ Admissible d ∧ Good θ α r d}.ncard : ℝ) := by
  sorry

end OMA.S_mo_515446
