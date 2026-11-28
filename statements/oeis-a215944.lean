import Mathlib.NumberTheory.FermatPsp

/-!
# Coman's conjecture on nested base-two Fermat pseudoprimes

Marius Coman, OEIS A215944, https://oeis.org/A215944 (OEIS Foundation, CC BY-SA 4.0).
The title describes the three-prime-factor sequence, but the conjecture in the
comments is about all base-two Fermat pseudoprimes having a smaller such
divisor. The author also reports checking examples with four prime factors.
The parameters in the three-factor representation are natural numbers.
-/

namespace OMA.S_oeis_a215944

/-- The three-factor representation in the OEIS conjecture. -/
def hasComanForm (N : ℕ) : Prop :=
  ∃ p m n : ℕ, N = p * ((m + 1) * p - m) * ((n + 1) * p - n)

theorem main :
    ∀ N : ℕ, Nat.FermatPsp N 2 →
      (∃ d : ℕ, d < N ∧ d ∣ N ∧ Nat.FermatPsp d 2) →
      ¬hasComanForm N →
      ∃ k : ℕ, N = 5461 * (42 * k - 13) := by
  sorry

end OMA.S_oeis_a215944
