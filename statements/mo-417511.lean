import Mathlib

/-!
# A conjecture about prime test

Source: https://mathoverflow.net/questions/417511 (CC BY-SA 4.0).

Conjecture: if `φ(m) < φ(n)` for all `m < n`, then `n` is a prime number. (For `n = pq` a
counterexample would need no prime between `(p-1)(q-1)` and `pq`, as the asker notes.)

Formalization notes:
* `φ` is Mathlib's `Nat.totient`; `m` ranges over the positive integers `1 ≤ m < n`.
* The index starts at `n ≥ 2`. For `n = 1` the hypothesis holds vacuously (there is no positive
  `m < 1`) while `1` is not prime, so the literal statement fails at this degenerate value and the
  standard reading excludes it.
* Checked numerically: no counterexample with `2 ≤ n < 200000`.
-/

namespace OMA.S_mo_417511

/-- If `φ(m) < φ(n)` for every positive `m < n`, then `n ≥ 2` is prime. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (∀ m : ℕ, 1 ≤ m → m < n → m.totient < n.totient) → n.Prime := by
  sorry

end OMA.S_mo_417511
