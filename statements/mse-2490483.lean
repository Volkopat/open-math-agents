import Mathlib

/-!
# The set of numbers of the form `q₁ + q₂² + q₃³ + q₄⁴ + q₅⁵` where all `q_k` are primes

Source: https://math.stackexchange.com/questions/2490483 (2017).
Credit: @jagraj28

Conjecture of the post: every prime number greater than `109` is of the form
`q₁ + q₂ ^ 2 + q₃ ^ 3 + q₄ ^ 4 + q₅ ^ 5` with all `q_k` prime. The post tests it for primes
below `70000`, where the exceptions are `2, 3, …, 61` and `109`. The one answer gives only a
heuristic argument; the post's two further observations (for 4 and 3 terms) are not stated.

Formalization notes:
* The primes `q₁, …, q₅` need not be distinct.
* A direct search recomputes the post's list of exceptional primes below `70000`.
-/

namespace OMA.S_mse_2490483

/-- Every prime greater than `109` is `q₁ + q₂² + q₃³ + q₄⁴ + q₅⁵` with all `q_k` prime. -/
theorem main :
    ∀ p : ℕ, p.Prime → 109 < p →
      ∃ q₁ q₂ q₃ q₄ q₅ : ℕ, q₁.Prime ∧ q₂.Prime ∧ q₃.Prime ∧ q₄.Prime ∧ q₅.Prime ∧
        p = q₁ + q₂ ^ 2 + q₃ ^ 3 + q₄ ^ 4 + q₅ ^ 5 := by
  sorry

end OMA.S_mse_2490483
