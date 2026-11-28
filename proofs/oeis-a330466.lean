import OMAStatements.S_oeis_a330466
import Mathlib

/-!
# A330466: row sums of the gap-two partition triangle

The `k` parts `a + 1, a + 3, …, a + 2k - 1` add up to `k * (a + k)`.  So for `n > 0` a number
`k` occurs in row `n` exactly when `n = k * (a + k)` for some `a`, i.e. when `k` is a divisor
of `n` with `k * k ≤ n`, i.e. `k ≤ √n`.  Summing `k` over those `k` gives the claim.
-/

namespace OMA.S_oeis_a330466

open Finset

/-- Closed form of the partition total. -/
lemma partitionTotal_eq (a k : ℕ) : partitionTotal a k = k * (a + k) := by
  unfold partitionTotal
  induction k with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; ring

/-- `k` occurs in row `n > 0` iff `k` is a divisor of `n` not exceeding `√n`. -/
lemma exists_iff {n k : ℕ} (hn : 0 < n) :
    (∃ a : ℕ, partitionTotal a k = n) ↔ k ∈ n.divisors.filter (fun d => d ≤ n.sqrt) := by
  rw [mem_filter, Nat.mem_divisors, Nat.le_sqrt]
  constructor
  · rintro ⟨a, ha⟩
    rw [partitionTotal_eq] at ha
    refine ⟨⟨⟨a + k, ha.symm⟩, hn.ne'⟩, ?_⟩
    rw [← ha]
    exact Nat.mul_le_mul_left k (Nat.le_add_left k a)
  · rintro ⟨⟨⟨c, hc⟩, -⟩, hk⟩
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; omega)
    have hkc : k ≤ c := by
      rw [hc] at hk
      exact Nat.le_of_mul_le_mul_left hk hk0
    exact ⟨c - k, by rw [partitionTotal_eq, hc]; congr 1; omega⟩

end OMA.S_oeis_a330466

open OMA.S_oeis_a330466 Finset in
theorem OMA.solution : type_of% @OMA.S_oeis_a330466.main := by
  intro n hn
  have hrow : ∀ k, rowEntry n k = if k ∈ n.divisors.filter (fun d => d ≤ n.sqrt) then k else 0 := by
    intro k
    unfold rowEntry
    simp only [exists_iff hn]
  simp only [hrow]
  rw [sum_ite_mem]
  refine sum_congr ?_ fun _ _ => rfl
  ext k
  simp only [mem_inter, mem_range, mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · rintro h
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn h.1.1), h⟩
