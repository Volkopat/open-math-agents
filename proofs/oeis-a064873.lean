import OMAStatements.S_oeis_a064873
import Mathlib

namespace OMA.A064873Proof

open OMA.S_oeis_a064873

/-- Lagrange: every `n` has a first part. -/
theorem ex4 (n : ℕ) : ∃ k : ℕ, ∃ y z w : ℕ, k ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, h⟩

/-- `a064873 n` is a first part. -/
theorem a_spec (n : ℕ) : ∃ y z w : ℕ, a064873 n ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n := by
  classical
  exact Nat.find_spec (p := fun k => ∃ y z w : ℕ, k ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) (ex4 n)

/-- `a064873 n` is at most every first part. -/
theorem a_min (n k y z w : ℕ) (h : k ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) : a064873 n ≤ k := by
  classical
  exact Nat.find_min' (p := fun k => ∃ y z w : ℕ, k ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = n) (ex4 n) ⟨y, z, w, h⟩

/-- `a064874 n` is a second part after `a064873 n`. -/
theorem b_spec (n : ℕ) : ∃ z w : ℕ, a064873 n ^ 2 + a064874 n ^ 2 + z ^ 2 + w ^ 2 = n := by
  classical
  exact Nat.find_spec (p := fun j => ∃ z w : ℕ, a064873 n ^ 2 + j ^ 2 + z ^ 2 + w ^ 2 = n) (a_spec n)

/-- `a064874 n` is at most every second part after `a064873 n`. -/
theorem b_min (n j z w : ℕ) (h : a064873 n ^ 2 + j ^ 2 + z ^ 2 + w ^ 2 = n) : a064874 n ≤ j := by
  classical
  exact Nat.find_min' (p := fun j => ∃ z w : ℕ, a064873 n ^ 2 + j ^ 2 + z ^ 2 + w ^ 2 = n) (a_spec n)
    ⟨z, w, h⟩

end OMA.A064873Proof

open OMA.S_oeis_a064873 OMA.A064873Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a064873.main := by
  intro n
  -- the minimal decomposition of `n` is `(a064873 n, a064874 n, c, d)`
  obtain ⟨c, d, hn⟩ := b_spec n
  have hm : n - a064874 n ^ 2 = a064873 n ^ 2 + c ^ 2 + d ^ 2 := by omega
  rw [hm]
  -- `m = a064873 n ^ 2 + c ^ 2 + d ^ 2` has first part `0`
  have h0 : a064873 (a064873 n ^ 2 + c ^ 2 + d ^ 2) = 0 := by
    have := a_min (a064873 n ^ 2 + c ^ 2 + d ^ 2) 0 (a064873 n) c d (by omega)
    omega
  apply le_antisymm
  · -- a second part `j` of `m` gives the decomposition `(j, a064874 n, x, y)` of `n`
    obtain ⟨x, y, hxy⟩ := b_spec (a064873 n ^ 2 + c ^ 2 + d ^ 2)
    rw [h0] at hxy
    exact a_min n _ (a064874 n) x y (by omega)
  · -- `a064873 n` is a second part of `m`
    exact b_min _ (a064873 n) c d (by rw [h0]; omega)
