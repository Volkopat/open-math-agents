import OMAStatements.S_oeis_a103528
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
Each multiple-of-2^k rounding jumps by 2^k precisely upon reaching
that multiple. Above the binary logarithm the rounded terms vanish,
so the upper limit may be extended before differencing.
-/

open Finset
open OMA.S_oeis_a103528

namespace BinaryDifferences

lemma full_sum (n : ℕ) : b n = ∑ k ∈ range (n+1), c (n-k) k := by
  by_cases h : n=0
  · simp [h, b]
  unfold b
  apply Finset.sum_subset (Finset.range_mono (by have := Nat.log_le_self 2 n; omega))
  intro k _ hk
  have hlog : Nat.log 2 n < k := by simpa using hk
  have hp : n < 2^k := (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) h).mp hlog
  have ht := (Nat.sub_le n k).trans_lt hp
  simp [c, Nat.mod_eq_of_lt ht]

lemma rounded (t k : ℕ) : c t k = (t/2^k)*2^k := by
  unfold c
  have h := Nat.mod_add_div t (2^k)
  rw [Nat.mul_comm] at h
  omega

lemma jump (n k : ℕ) (hk : k ≤ n) :
    c (n+1-k) k = c (n-k) k +
      (if (n+1) % (2^k) = k % (2^k) then 2^k else 0) := by
  have eq : n+1-k=n-k+1 := by omega
  have hd : (n+1) % (2^k) = k % (2^k) ↔ 2^k ∣ (n-k)+1 := by
    rw [← eq, ← Nat.modEq_iff_dvd' (hk.trans (Nat.le_succ n))]
    exact eq_comm
  rw [rounded, rounded, eq]
  by_cases h : 2^k ∣ n-k+1
  · simp [hd.mpr h, Nat.succ_div_of_dvd, h, Nat.add_mul]
  · rw [if_neg (fun hh => h (hd.mp hh))]
    simp [Nat.succ_div_of_not_dvd, h]

lemma correction (n : ℕ) :
    (∑ k ∈ range (n+1), if (n+1) % (2^k) = k % (2^k) then 2^k else 0) =
      1+2*term (n+1) := by
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.mod_one, if_true]
  unfold term
  rw [Nat.add_sub_cancel, Finset.mul_sum, Nat.add_comm 1]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp [pow_succ, Nat.mul_comm]

lemma shift (n : ℕ) : b (n+1) = b n + (1+2*term (n+1)) := by
  rw [full_sum (n+1), Finset.sum_range_succ, Nat.sub_self]
  simp only [c, Nat.zero_mod, Nat.sub_zero, Nat.add_zero]
  change (∑ k ∈ range (n+1), c (n+1-k) k) = _
  rw [← correction, full_sum n, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k hk => jump n k (by have := Finset.mem_range.mp hk; omega)

end BinaryDifferences

theorem OMA.solution : type_of% @OMA.S_oeis_a103528.main := by
  refine ⟨by simp [term], ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := BinaryDifferences.shift k
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  omega
