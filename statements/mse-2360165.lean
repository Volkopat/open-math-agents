import Mathlib.Data.Nat.Totient
import Mathlib.Data.ENat.Lattice
import Mathlib.Order.LiminfLimsup

/-!
# Euler Totient of Numbers Between Twin Primes

Source: https://math.stackexchange.com/questions/2360165/euler-totient-of-numbers-between-twin-primes
Question by user56983, 2017-07-16 (CC BY-SA 3.0).
Credit: @etaubman

The source explicitly defines liminf as the limit of tail infima as the lower
cutoff tends to infinity. We use the complete lattice of extended natural
numbers, so an infinite limit is represented by top. The sequence lambda+k+1
enumerates exactly the natural numbers strictly larger than lambda. This is
not the stronger, different statement comparing phi(lambda) to every later
individual totient value.
-/

namespace OMA.S_mse_2360165

noncomputable def tailTotientLiminf (lambda : ℕ) : ℕ∞ :=
  Filter.liminf (fun k : ℕ => (Nat.totient (lambda + k + 1) : ℕ∞)) Filter.atTop

theorem main : ∀ lambda : ℕ, Nat.Prime (lambda - 1) → Nat.Prime (lambda + 1) →
    (Nat.totient lambda : ℕ∞) ≤ tailTotientLiminf lambda := by
  sorry

end OMA.S_mse_2360165
