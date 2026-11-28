import Mathlib.Data.Nat.Prime.Nth
import Mathlib.GroupTheory.Perm.Sign

/-!
# Chen primes and permutations

Source: https://mathoverflow.net/questions/315679
Credit: @matteotalluri1998-cell

The source indexes the first (n) primes by (1,ldots,n).
Here `Fin n` uses indices starting at zero, so `Nat.nth Nat.Prime 0` is 2.
A permutation is even when its sign is 1 and odd when its sign is -1.
-/

namespace OMA.S_mo_315679

def PrimeProductsMinusTwo {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, Nat.Prime (Nat.nth Nat.Prime i * Nat.nth Nat.Prime (σ i) - 2)

/-- Both parity assertions in Sun's conjecture. -/
theorem main :
    (∀ n : ℕ, 0 < n → ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = 1 ∧
      PrimeProductsMinusTwo σ) ∧
    (∀ n : ℕ, 2 < n → ∃ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ = -1 ∧
      PrimeProductsMinusTwo σ) := by
  sorry

end OMA.S_mo_315679
