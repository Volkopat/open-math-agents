import OMAStatements.S_oeis_a135231
import Mathlib

/-!
Credit: @ivillar, original proof in PR #16445.
Summing the Pascal column gives a signed sum of powers of two. The signed sums at
consecutive indices add to a power of two, which yields the Jacobsthal recurrence
directly. Its shifted terms give the row sums and the generating-function coefficients.
-/

namespace OMAA135231Helpers
open PowerSeries OMA.S_oeis_a135231

theorem choose_sum (n j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ Finset.range (n + 1), (j.choose k : ℤ) = 2 ^ j := by
  rw [← Finset.sum_subset (s₁ := Finset.range (j + 1)) (Finset.range_mono (by omega))
    (fun k _ hk => by
      have : j < k := by simpa [Finset.mem_range] using hk
      simp [Nat.choose_eq_zero_of_lt this])]
  exact_mod_cast Nat.sum_range_choose j

theorem rowsum (n : ℕ) : a n = ∑ i ∈ Finset.range (n + 1), A103451 n i *
    ∑ j ∈ Finset.range (n + 1), S i j * 2 ^ j := by
  unfold a T
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← Finset.mul_sum, choose_sum n j (by have := Finset.mem_range.mp hj; omega)]
  ring

def g (n : ℕ) : ℤ := ∑ j ∈ Finset.range (n + 1), S n j * 2 ^ j

theorem g_step (n : ℕ) : g (n + 1) + g n = 2 ^ (n + 1) := by
  have h : ∑ j ∈ Finset.range (n + 1), S (n + 1) j * 2 ^ j = -g n := by
    unfold g
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    simp [S, show j ≤ n by omega, show j ≤ n + 1 by omega,
      show n + 1 - j = n - j + 1 by omega, pow_succ]
  change (∑ j ∈ Finset.range (n + 2), S (n + 1) j * 2 ^ j) + g n = _
  rw [Finset.sum_range_succ, h]
  simp [S]

theorem jac (n : ℕ) : g n = A001045 (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih0 ih1 =>
    have h := g_step n
    have h' := g_step (n + 1)
    rw [pow_succ] at h'
    change g (n + 2) + g (n + 1) = _ at h'
    change g (n + 2) = A001045 (n + 2) + 2 * A001045 (n + 1)
    rw [← ih1, ← ih0]
    omega

theorem closed (n : ℕ) (hn : 0 < n) : a n = A001045 (n + 1) + 1 := by
  have hzero : ∑ j ∈ Finset.range (n + 1), S 0 j * 2 ^ j = 1 := by
    rw [Finset.sum_eq_single_of_mem 0 (by simp)]
    · simp [S]
    · intro j _ hj
      simp [S, hj]
  have hs : ∑ i ∈ Finset.range n, A103451 n i *
      ∑ j ∈ Finset.range (n + 1), S i j * 2 ^ j = 1 := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hn)]
    · simp [A103451, hzero]
    · intro i hi h0
      have hi' := Finset.mem_range.mp hi
      simp [A103451, h0, show i ≠ n by omega]
  rw [rowsum, Finset.sum_range_succ, hs]
  change 1 + A103451 n n * g n = _
  simp [A103451, jac, add_comm]

theorem rec (n : ℕ) (hn : 3 < n) : a n = 2 * a (n - 1) + a (n - 2) - 2 * a (n - 3) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  simp (disch := omega) only [Nat.add_sub_assoc, closed]
  have h (k : ℕ) : A001045 (k + 2) = A001045 (k + 1) + 2 * A001045 k := rfl
  have h₄ := h (m + 3)
  have h₃ := h (m + 2)
  norm_num [Nat.add_assoc] at h₄ h₃ ⊢
  omega

end OMAA135231Helpers

open PowerSeries OMA.S_oeis_a135231 OMAA135231Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a135231.main := by
  refine ⟨?_, rec, closed⟩
  let f := mk a
  have e : f * ((X - 1) * (X + 1) * (2 * X - 1)) =
      f - C 2 * (X ^ 1 * f) - X ^ 2 * f + C 2 * (X ^ 3 * f) := by
    rw [map_ofNat C 2]
    ring
  have e' : (-2 * X ^ 3 - X ^ 2 + 1 : ℤ⟦X⟧) = 1 - X ^ 2 - C 2 * X ^ 3 := by
    rw [map_ofNat C 2]
    ring
  change f * _ = _
  rw [e, e']
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', f, coeff_mk, coeff_one, coeff_X_pow]
  by_cases hn : n < 4
  · interval_cases n <;> decide
  · simp (disch := omega)
    have := rec n (by omega)
    omega
