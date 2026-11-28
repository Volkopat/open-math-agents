import Mathlib

/-!
# Is `X = (n-1)^n + n` always composite for `n ≥ 4`?

Source: https://math.stackexchange.com/questions/3897185 (2020).
Credit: @jagraj28

The post states the proposition: for every integer `n ≥ 4`, `X = (n-1)^n + n` is composite.
The post and its one answer prove it in some residue classes (for example `3 ∣ X` when
`n ≡ 2 (mod 3)`, and `n + 1 ∣ X` when `n + 1` is prime), but not in general. A comment reports no
prime `X` for `n ≤ 15000`.

Formalization notes:
* `n` is a natural number with `4 ≤ n`, so `n - 1` is the true difference.
* "Composite" is stated as "not prime": `X ≥ 3 ^ 4 + 4 = 85 > 1` for `n ≥ 4`, so for this `X` the
  two are the same.
* The bound `n ≥ 4` is needed: `X = 3` for `n = 2` and `X = 11` for `n = 3` are prime.
-/

namespace OMA.S_mse_3897185

/-- `(n - 1) ^ n + n` is not prime for every `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n → ¬ Nat.Prime ((n - 1) ^ n + n) := by
  sorry

end OMA.S_mse_3897185
