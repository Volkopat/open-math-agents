import Mathlib

/-!
# OEIS A393867

Let `F` be the generating function of A393866 with constant coefficient one
and let `G = X F′ / F`. The positive-degree coefficients of `G` form A393867.
The conjectures assert that all these coefficients are odd and that the
coefficient at each index `n > 1` is divisible by the `n`th prime.

Sources: https://oeis.org/A393867 and https://oeis.org/A393866
Credit: @wtho704
-/

namespace OMA.S_oeis_a393867

open PowerSeries

/-- The `n`th prime with indexing starting at one. -/
noncomputable def primeAt (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The coefficient recurrence defining A393866. -/
def DefiningRecurrence (F : PowerSeries ℤ) : Prop :=
  ∀ n : ℕ, 0 < n →
    let p := primeAt n
    coeff n (F ^ p) = (p : ℤ) * coeff (n - 1) (F ^ p)

theorem main : ∀ F G : PowerSeries ℤ, constantCoeff F = 1 → DefiningRecurrence F →
    F * G = X * derivative ℤ F →
      (∀ n : ℕ, 1 < n → (primeAt n : ℤ) ∣ coeff n G) ∧
        ∀ n : ℕ, 0 < n → Odd (coeff n G) := by
  sorry

end OMA.S_oeis_a393867
