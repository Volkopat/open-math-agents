import OMAStatements.S_oeis_a222945
import Mathlib

/-!
Credit: @ivillar
Proof: for n ≥ 2 the set of sums is exactly the interval [-2n, 2n]. Taking k = 0 gives every
s in it as s = floor(s/2) + ceil(s/2). Conversely, if one of i, j, k is 0 the sum has absolute
value at most 2n; otherwise x + y + z ≤ x*y*z + 2 ≤ n + 2 ≤ 2n for x, y, z ≥ 1 the absolute
values. So a(n) = 4n + 1. The numbers ending in 01 are those m ≡ 1 (mod 4) with m > 1, whose
(n-1)-th element (counting from 0) is 4n + 1.
-/

namespace OMAA222945Helpers
open OMA.S_oeis_a222945

instance decEndsIn01 : DecidablePred endsIn01 := fun m =>
  inferInstanceAs (Decidable ((Nat.digits 2 m).take 2 = [1, 0]))

theorem endsIn01_iff (m : ℕ) : endsIn01 m ↔ m % 4 = 1 ∧ 1 < m := by
  unfold endsIn01
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m
    · simp
    · rw [Nat.digits_def' (by norm_num) (by norm_num)]
      simp
  · rw [Nat.digits_def' (by norm_num) (by omega),
      Nat.digits_def' (by norm_num) (by omega : 0 < m / 2)]
    simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true]
    omega

theorem count_block (k : ℕ) : Nat.count (fun x => endsIn01 (4 * k + 5 + x)) 4 = 1 := by
  rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl]
  simp only [Nat.count_succ, Nat.count_zero, endsIn01_iff]
  split_ifs <;> omega

theorem count_eq (k : ℕ) : Nat.count endsIn01 (4 * k + 5) = k := by
  induction k with
  | zero =>
    rw [Nat.count_eq_card_filter_range, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rw [endsIn01_iff]
    simp only [Finset.mem_range] at hx
    omega
  | succ k ih =>
    rw [show 4 * (k + 1) + 5 = (4 * k + 5) + 4 by ring, Nat.count_add, ih, count_block]

theorem nth_eq (k : ℕ) : Nat.nth endsIn01 k = 4 * k + 5 := by
  have hp : endsIn01 (4 * k + 5) := (endsIn01_iff _).2 ⟨by omega, by omega⟩
  have h := Nat.nth_count hp
  rwa [count_eq] at h

theorem sums_eq (n : ℕ) (hn : 2 ≤ n) : sums n = Finset.Icc (-(2 * (n : ℤ))) (2 * n) := by
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  ext s
  simp only [sums, Finset.mem_image, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Prod.exists]
  constructor
  · rintro ⟨i, j, k, ⟨⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩, ⟨hk1, hk2⟩⟩, hp⟩, rfl⟩
    by_cases h0 : i = 0 ∨ j = 0 ∨ k = 0
    · rcases h0 with rfl | rfl | rfl <;> constructor <;> linarith
    · simp only [not_or] at h0
      obtain ⟨hi0, hj0, hk0⟩ := h0
      have hx : 1 ≤ |i| := Int.one_le_abs hi0
      have hy : 1 ≤ |j| := Int.one_le_abs hj0
      have hz : 1 ≤ |k| := Int.one_le_abs hk0
      rw [abs_mul, abs_mul] at hp
      have hxy : 1 ≤ |i| * |j| := by nlinarith
      have key : |i| + |j| + |k| ≤ |i| * |j| * |k| + 2 := by
        nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy),
          mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hz)]
      have habs : |i + j + k| ≤ 2 * (n : ℤ) := by
        have := abs_add_three i j k
        linarith
      exact abs_le.1 habs
  · rintro ⟨hs1, hs2⟩
    refine ⟨s / 2, s - s / 2, 0, ⟨⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩,
      by simp⟩, by ring⟩

end OMAA222945Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a222945.main := by
  intro n hn
  unfold OMA.S_oeis_a222945.a OMA.S_oeis_a222945.A004766
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  rw [OMAA222945Helpers.sums_eq (k + 2) hn, show k + 2 - 1 = k + 1 by omega,
    OMAA222945Helpers.nth_eq, Int.card_Icc]
  omega
