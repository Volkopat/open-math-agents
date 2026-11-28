import Mathlib

/-!
# A379399: Numbers that can be written in exactly four different ways as a sum of at most nine positive third powers.

Source: https://oeis.org/A379399
Credit: @darealpandaboi

Conjecture: this sequence is finite and a(66) = 455 is the last term (verified up to 10^8).

Translation notes.
* A way is a partition of n (order of summands ignored) into at most nine parts, each a positive
  cube: a Nat.Partition n with at most 9 parts, all of the form k^3.
* Both claims are stated: the set of n with exactly four ways is finite, and 455 is its largest
  element. This reproduces all 66 listed terms, ending with 338, 366, 455, and finds no other term
  up to 20000 (checked by computer); the index 66 is then implied.
-/

namespace OMA.S_oeis_a379399

/-- The number of ways to write n as a sum of at most nine positive cubes. -/
noncomputable def ways (n : ℕ) : ℕ :=
  {π : n.Partition | π.parts.card ≤ 9 ∧ ∀ x ∈ π.parts, ∃ k : ℕ, x = k ^ 3}.ncard

theorem main : {n : ℕ | ways n = 4}.Finite ∧ IsGreatest {n : ℕ | ways n = 4} 455 := by
  sorry

end OMA.S_oeis_a379399
