import FormalConjectures.ErdosProblems.«311»

/-! Multiplying by the least common multiple turns each nonzero difference into a nonzero integer. -/

-- Original proof by @ashnewmanjones.
open Finset

theorem OMA.solution : type_of% @Erdos311.delta_ge_inv_lcm := by
  intro N
  set L := (Icc 1 N).lcm id
  have hL : (0 : ℝ) < L := by
    exact_mod_cast (show 0 < L by simp [L, Nat.pos_iff_ne_zero, Finset.lcm_eq_zero_iff])
  unfold Erdos311.delta
  apply le_csInf
  · exact ⟨1, one_ne_zero, ∅, empty_subset _, by simp⟩
  · rintro x ⟨hx, A, hA, rfl⟩
    let s : ℕ := ∑ n ∈ A, L / n
    let k : ℤ := (L : ℤ) - (s : ℤ)
    have h (n) (hn : n ∈ A) : (↑(L / n) : ℝ) = (L : ℝ) * (1 / n) := by
      have hn0 := Nat.ne_of_gt (mem_Icc.mp (hA hn)).1
      have hnL : n ∣ L := dvd_lcm (f := id) (hA hn)
      rw [Nat.cast_div hnL (by exact_mod_cast hn0)]
      ring
    have hk : (k : ℝ) = (L : ℝ) * (1 - ∑ n ∈ A, (1 : ℝ) / n) := by
      dsimp only [k, s]
      rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, Nat.cast_sum, mul_sub,
        mul_one, mul_sum, sum_congr rfl h]
    have hk0 : k ≠ 0 := by
      intro hzero
      rw [hzero, Int.cast_zero] at hk
      exact mul_ne_zero hL.ne' (abs_ne_zero.mp hx) hk.symm
    rw [div_le_iff₀ hL, mul_comm, ← abs_of_pos hL, ← abs_mul, ← hk, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk0
