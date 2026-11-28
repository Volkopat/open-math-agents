import OMAStatements.S_oeis_a274139
import Mathlib

/-!
# A274139: the identity `a(n) = 2 b(n)²` fails at `n = 2`

The odd part of `2` is `1`, so `a 2 = 2 ^ 1 = 2`.  The only pair `(k, j)` with
`2 ^ k (2 j + 1) = 3` is `(0, 1)`, so `b 2 = 2 ^ 1 = 2` and `2 b(2)² = 8 ≠ 2`.
-/

namespace OMA.S_oeis_a274139

lemma a_two : a 2 = 2 := by
  have h : Nat.factorization 2 2 = 1 := by
    simpa using Nat.Prime.factorization_self Nat.prime_two
  simp [a, oddPart, h]

lemma b_two : b 2 = 2 := by decide

end OMA.S_oeis_a274139

open OMA.S_oeis_a274139 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a274139.main) := by
  intro h
  have h2 := h 2 (by norm_num)
  rw [a_two, b_two] at h2
  omega
