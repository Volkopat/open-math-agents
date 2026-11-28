import Mathlib

/-!
# Are the totients of Fibonacci numbers eventually distinct?

Source: https://math.stackexchange.com/questions/1595838

Let `F₁ = F₂ = 1`, `Fₙ = Fₙ₋₁ + Fₙ₋₂`. For any `n, m > 8` (with `n ≠ m`), is it always true
that `φ(Fₙ) ≠ φ(Fₘ)`, where `φ` is Euler's totient function? (Small coincidences exist:
`φ(F₅) = φ(F₆)` and `φ(F₇) = φ(F₈)`.)

Formalization notes:
* `main` states the question in its "yes" reading, as asked.
* Mathlib's `Nat.fib` has `Nat.fib 1 = Nat.fib 2 = 1`, matching the source's indexing.
-/

namespace OMA.S_mse_1595838

/-- For distinct `n, m > 8`, `φ(Fₙ) ≠ φ(Fₘ)`. -/
theorem main : ∀ n m : ℕ, 8 < n → 8 < m → n ≠ m →
    (Nat.fib n).totient ≠ (Nat.fib m).totient := by
  sorry

end OMA.S_mse_1595838
