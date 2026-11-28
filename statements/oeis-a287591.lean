import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Rotkiewicz's conjecture on Carmichael numbers near primes

Source: https://oeis.org/A287591
Credit: @luciusacarr

The conjecture in the OEIS comments allows either neighbor at distance two
to be prime. The tabulated sequence requires both.
-/

namespace OMA.S_oeis_a287591

/-- A composite number satisfying Fermat's congruence for every coprime base. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a.Coprime n → Nat.ModEq n (a ^ (n - 1)) 1

theorem main : Set.Infinite {n : ℕ | IsCarmichael n ∧
    ((n - 2).Prime ∨ (n + 2).Prime)} := by
  sorry

end OMA.S_oeis_a287591
