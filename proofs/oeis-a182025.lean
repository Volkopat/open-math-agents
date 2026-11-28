import OMAStatements.S_oeis_a182025

-- Problem: A182025: a(n) = 31*binomial(2*n,n-4) + Sum_{i=1..n-4} binomial(2*n,n-4-i)*(4+i).
-- Upstream: formal-conjectures statements/oeis-a182025.lean:0 (declaration OMA.S_oeis_a182025.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open scoped BigOperators

namespace OMA.P_oeis_a182025

private lemma weighted_prefix (n k : ℕ) (hk : k ≤ n) :
    2 * (∑ j ∈ Finset.range k, (n - j) * (2 * n).choose j) =
      k * (2 * n).choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih (by omega)]
    rw [← Nat.mul_assoc, ← Nat.add_mul, show k + 2 * (n - k) = 2 * n - k by omega]
    rw [Nat.mul_comm (2 * n - k), Nat.mul_comm (k + 1), Nat.choose_succ_right_eq]

private lemma weighted_tail (n : ℕ) (hn : 4 ≤ n) :
    2 * (∑ i ∈ Finset.Icc 1 (n - 4), (2 * n).choose (n - 4 - i) * (4 + i)) =
      (n - 4) * (2 * n).choose (n - 4) := by
  have h :
      (∑ i ∈ Finset.Icc 1 (n - 4), (2 * n).choose (n - 4 - i) * (4 + i)) =
      ∑ i ∈ Finset.Ico 1 (n - 4 + 1),
        (n - (n - 4 - i)) * (2 * n).choose (n - 4 - i) := by
    refine Finset.sum_congr (by ext i; simp) fun i hi => ?_
    have hi' := Finset.mem_Icc.mp hi
    rw [show n - (n - 4 - i) = 4 + i by omega, Nat.mul_comm]
  rw [h, Finset.sum_Ico_reflect (fun j => (n - j) * (2 * n).choose j) 1
    (n := n - 4) (m := n - 4 + 1) le_rfl, Nat.sub_self, Nat.add_sub_cancel,
    Nat.Ico_zero_eq_range]
  exact weighted_prefix n (n - 4) (by omega)

end OMA.P_oeis_a182025

open OMA.S_oeis_a182025 OMA.P_oeis_a182025 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182025.main := by
  have hclosed (n : ℕ) : 2 * a n = ((n : ℤ) + 58) * ((2 * n).choose (n + 4) : ℤ) := by
    by_cases hn : n < 4
    · simp [a, hn, Nat.choose_eq_zero_of_lt (show 2 * n < n + 4 by omega)]
    · have h4 : 4 ≤ n := by omega
      have ht := congrArg (Nat.cast : ℕ → ℤ) (weighted_tail n h4)
      push_cast [Nat.cast_sum, Nat.cast_sub h4] at ht
      have hs : (2 * n).choose (n + 4) = (2 * n).choose (n - 4) :=
        Nat.choose_symm_of_eq_add (by omega)
      rw [a, if_neg hn, hs]
      linear_combination ht
  have hR : ∀ j : ℕ, ((j : ℤ) + 8) * (j : ℤ) * ((2 * j + 8).choose (j + 8) : ℤ)
      = 2 * ((j : ℤ) + 4) * (2 * (j : ℤ) + 7) * ((2 * j + 6).choose (j + 7) : ℤ) := by
    intro j
    have s1 := Nat.add_one_mul_choose_eq (2 * j + 6) (j + 7)
    have s2 := Nat.choose_mul_succ_eq (2 * j + 7) (j + 8)
    rw [show 2 * j + 6 + 1 = 2 * j + 7 by omega, show j + 7 + 1 = j + 8 by omega] at s1
    rw [show 2 * j + 7 + 1 - (j + 8) = j by omega, show 2 * j + 7 + 1 = 2 * j + 8 by omega] at s2
    have t1 : (2 * (j : ℤ) + 7) * ((2 * j + 6).choose (j + 7) : ℤ)
        = ((2 * j + 7).choose (j + 8) : ℤ) * ((j : ℤ) + 8) := by
      exact_mod_cast s1
    have t2 : ((2 * j + 7).choose (j + 8) : ℤ) * (2 * (j : ℤ) + 8)
        = ((2 * j + 8).choose (j + 8) : ℤ) * (j : ℤ) := by
      exact_mod_cast s2
    linear_combination -((j : ℤ) + 8) * t2 - (2 * (j : ℤ) + 8) * t1
  intro n hn
  rcases Nat.lt_or_ge n 5 with h | h
  · interval_cases n <;> norm_num [a]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rw [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega]
  have h2 := hclosed (m + 5)
  have h1 := hclosed (m + 4)
  have h0 := hclosed (m + 3)
  have R1 := hR (m + 1)
  have R0 := hR m
  rw [show 2 * (m + 5) = 2 * m + 10 by ring, show m + 5 + 4 = m + 9 by ring] at h2
  rw [show 2 * (m + 4) = 2 * m + 8 by ring, show m + 4 + 4 = m + 8 by ring] at h1
  rw [show 2 * (m + 3) = 2 * m + 6 by ring, show m + 3 + 4 = m + 7 by ring] at h0
  rw [show 2 * (m + 1) + 8 = 2 * m + 10 by ring, show m + 1 + 8 = m + 9 by ring,
    show 2 * (m + 1) + 6 = 2 * m + 8 by ring, show m + 1 + 7 = m + 8 by ring] at R1
  apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
  push_cast at h2 h1 h0 R1 ⊢
  linear_combination 558 * ((m : ℤ) + 1) * ((m : ℤ) + 9) * h2
    + 7 * (-631 * ((m : ℤ) + 5) ^ 2 + 777 * ((m : ℤ) + 5) + 4600) * h1
    + 4370 * ((m : ℤ) + 4) * (2 * (m : ℤ) + 7) * h0
    + 558 * ((m : ℤ) + 63) * R1 - 2185 * ((m : ℤ) + 61) * R0
