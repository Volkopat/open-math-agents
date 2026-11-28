import Mathlib

/-!
# Finiteness of primes of the form `6^(2*n) + 1`

Vassilis Parassidis asks whether these prime values form a finite set.
The index ranges over all natural numbers, so the set includes the value 2 at index 0.

Source: https://math.stackexchange.com/questions/95119
Credit: @thematthewdunlop-cpu
-/

namespace OMA.S_mse_95119

theorem main :
    {p : ℕ | p.Prime ∧ ∃ n : ℕ, p = 6 ^ (2 * n) + 1}.Finite := by
  sorry

end OMA.S_mse_95119
