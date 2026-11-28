import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Card
import Mathlib.Data.Fin.VecNotation

/-!
# OEIS A002071

The comments give conditional counts of consecutive positive integers whose
prime factors are bounded by the nth prime. The hypothesis is the stated
effective abc bound with exponent two. The counts start at the twentieth prime.
Source: https://oeis.org/A002071
-/

namespace OMA.S_oeis_a002071

def smoothPairs (bound : ℕ) : Set ℕ :=
  {x | 0 < x ∧ ∀ p : ℕ, p.Prime → p ∣ x * (x + 1) → p ≤ bound}

def effectiveAbc : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → a.Coprime b →
    a + b < ((a * b * (a + b)).primeFactors.prod id) ^ 2

def counts : Fin 17 → ℕ :=
  ![4839, 6040, 7441, 9179, 11134, 13374, 16167, 19507, 23367,
    27949, 33233, 39283, 46166, 54150, 63428, 74007, 86125]

theorem main :
    effectiveAbc →
      ∀ i : Fin 17, (smoothPairs (Nat.nth Nat.Prime (19 + i.val))).ncard = counts i := by
  sorry

end OMA.S_oeis_a002071
