import Mathlib

/-!
# A249596: moving the leading binary digit to the units place

A249596 (offset 1) is the binary analogue of A097717. A165781 (offset 0)
uses the multiplicative order of two modulo `2*k+1`. The conjecture below
keeps the indices as printed in A249596. With these offsets its two sides
already differ at `n = 2`.

Sources: https://oeis.org/A249596, https://oeis.org/A097717,
https://oeis.org/A165781 and https://oeis.org/A002326
(OEIS Foundation, CC BY-SA 4.0). Credit: @Solitude1312
-/

namespace OMA.S_oeis_a249596

/-- Remove the leading binary 1 from a positive integer and append it on the right. -/
def rotate (m : ℕ) : ℕ := 2 * (m - 2 ^ Nat.log 2 m) + 1

/-- The least positive integer whose exact quotient by n is its rotation. -/
noncomputable def a249596 (n : ℕ) : ℕ := sInf {m : ℕ | 0 < m ∧ m = n * rotate m}

/-- Least positive d with 2^d congruent to 1 modulo 2k+1, including d = 1 at k = 0. -/
noncomputable def period (k : ℕ) : ℕ :=
  sInf {d : ℕ | 0 < d ∧ 2 * k + 1 ∣ 2 ^ d - 1}

noncomputable def a165781 (k : ℕ) : ℕ := (2 ^ period k - 1) / (2 * k + 1)

theorem main : ∀ n : ℕ, 1 ≤ n → a249596 n = n * a165781 n := by
  sorry

end OMA.S_oeis_a249596
