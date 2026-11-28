import Mathlib

/-!
# OEIS A386963

Sources: https://oeis.org/A386963 and https://oeis.org/A065090.
Robert Israel observed that this follows from the natural density zero of the primes.

The entry asks whether the gaps equal to 2 have natural density one.
A065090 lists the positive integers that are not odd primes. Its odd entries are the
odd nonprimes, starting with 1. Their positions in A065090 are the counts of terms that
strictly precede them. We use zero-based indices for both enumerations. Subtracting
successive positions gives the displayed A386963 values, beginning 5, 4, 4, 3, 2.
-/

namespace OMA.S_oeis_a386963

open Filter Topology

/-- The predicate defining A065090. -/
abbrev isA065090 (m : ℕ) : Prop := 0 < m ∧ (Even m ∨ ¬ Nat.Prime m)

/-- The odd values in A065090, in increasing order. -/
noncomputable def oddValue (n : ℕ) : ℕ := Nat.nth (fun m => Odd m ∧ ¬ Nat.Prime m) n

/-- The zero-based position of the nth odd value in A065090. -/
noncomputable def pos (n : ℕ) : ℕ := Nat.count isA065090 (oddValue n)

/-- The consecutive gaps between these positions. -/
noncomputable def a (n : ℕ) : ℕ := pos (n + 1) - pos n

theorem main :
    Tendsto (fun N : ℕ => (((Finset.range N).filter (fun i => a i = 2)).card : ℝ) / (N : ℝ))
      atTop (𝓝 1) := by
  sorry

end OMA.S_oeis_a386963
