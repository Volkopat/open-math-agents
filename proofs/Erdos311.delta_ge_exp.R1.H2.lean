import OMAReductions.R_Erdos311_delta_ge_exp_R1

-- Step Erdos311.delta_ge_exp.R1.H2: hypothesis H2 of reduction Erdos311.delta_ge_exp.R1
-- Credit: @ihateSAS
-- H2 := ∀ N : ℕ, 1 / ((Nat.lcmUpto N : ℝ)) ≤ Erdos311.delta N

open Finset

/-- Multiplying `1 - ∑_{n ∈ A} 1/n` by `lcm(1,…,N)` clears every denominator, so the product is
an integer. -/
lemma OMA.lcmUpto_mul_sub_sum_int (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) :
    ∃ k : ℤ, ((Nat.lcmUpto N : ℕ) : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) = k := by
  set L : ℕ := Nat.lcmUpto N with hL
  refine ⟨(L : ℤ) - ((∑ n ∈ A, L / n : ℕ) : ℤ), ?_⟩
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Nat.cast_sum, mul_sub, mul_one,
    Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnI : n ∈ Icc 1 N := hA hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hnI).1
  have hdvd : n ∣ L := by
    simpa [hL, Nat.lcmUpto] using (Finset.dvd_lcm (f := id) hnI)
  rw [Nat.cast_div hdvd (by exact_mod_cast hn0)]
  ring

theorem OMA.solution : OMA.R_Erdos311_delta_ge_exp_R1.H2 := by
  intro N
  have hL : 0 < (Nat.lcmUpto N : ℝ) := by exact_mod_cast Nat.lcmUpto_pos N
  apply le_csInf
  · exact ⟨1, one_ne_zero, ∅, Finset.empty_subset _, by simp⟩
  · rintro x ⟨hx, A, hA, rfl⟩
    obtain ⟨k, hk⟩ := OMA.lcmUpto_mul_sub_sum_int N A hA
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact mul_ne_zero hL.ne' (abs_ne_zero.mp hx) (by simpa using hk)
    rw [div_le_iff₀ hL, ← abs_of_pos hL, ← abs_mul, mul_comm, hk, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk0
