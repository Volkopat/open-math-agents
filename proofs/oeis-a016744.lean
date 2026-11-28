import OMAStatements.S_oeis_a016744
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a016744.main := by
  have h4 : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ)) ^ 4) (Real.pi ^ 4 / 90) := by
    simpa using hasSum_zeta_four
  have hs : HasSum (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1) ^ 4) (Real.pi ^ 4 / 90) := by
    have := (hasSum_nat_add_iff' 1).mpr (by simpa using h4)
    simpa using this
  have e1 : (fun n : ℕ ↦ (1 : ℝ) / (2 * ((n : ℝ) + 1)) ^ 4)
      = fun n : ℕ ↦ (1/16) * (1 / ((n : ℝ) + 1) ^ 4) := by
    funext n; field_simp; ring
  have h1 : HasSum (fun n : ℕ ↦ (1 : ℝ) / (2 * ((n : ℝ) + 1)) ^ 4) (Real.pi ^ 4 / 1440) := by
    rw [e1]
    have := hs.mul_left ((1:ℝ)/16)
    have e : Real.pi ^ 4 / 1440 = 1/16 * (Real.pi ^ 4 / 90) := by ring
    rw [e]; exact this
  refine ⟨h1, ?_⟩
  have hO : HasSum (fun k : ℕ ↦ (1 : ℝ) / (2 * (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 4)
      (Real.pi ^ 4 / 1440 / 16) := by
    have e2 : (fun k : ℕ ↦ (1 : ℝ) / (2 * (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 4)
        = fun k : ℕ ↦ (1/256) * (1 / ((k : ℝ) + 1) ^ 4) := by
      funext k; push_cast; field_simp; ring
    rw [e2]
    have := hs.mul_left ((1:ℝ)/256)
    have e : Real.pi ^ 4 / 1440 / 16 = 1/256 * (Real.pi ^ 4 / 90) := by ring
    rw [e]; exact this
  have hse : Summable (fun k : ℕ ↦ (1 : ℝ) / (2 * (((2 * k : ℕ) : ℝ) + 1)) ^ 4) :=
    h1.summable.comp_injective (i := fun k : ℕ => 2 * k) (mul_right_injective₀ (two_ne_zero))
  have e := HasSum.even_add_odd (f := fun n : ℕ ↦ (1 : ℝ) / (2 * ((n : ℝ) + 1)) ^ 4) hse.hasSum hO
  have hE : HasSum (fun k : ℕ ↦ (1 : ℝ) / (2 * (((2 * k : ℕ) : ℝ) + 1)) ^ 4)
      (Real.pi ^ 4 / 1440 - Real.pi ^ 4 / 1440 / 16) := by
    have u := h1.unique e
    have : (∑' k : ℕ, (1 : ℝ) / (2 * (((2 * k : ℕ) : ℝ) + 1)) ^ 4)
        = Real.pi ^ 4 / 1440 - Real.pi ^ 4 / 1440 / 16 := by linarith
    rw [← this]; exact hse.hasSum
  have fe : (fun k : ℕ ↦ (-1 : ℝ) ^ (2 * k + 2) / (2 * (((2 * k : ℕ) : ℝ) + 1)) ^ 4)
      = fun k : ℕ ↦ (1 : ℝ) / (2 * (((2 * k : ℕ) : ℝ) + 1)) ^ 4 := by
    funext k
    rw [Even.neg_one_pow ⟨k + 1, by ring⟩]
  have fo : (fun k : ℕ ↦ (-1 : ℝ) ^ (2 * k + 1 + 2) / (2 * (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 4)
      = fun k : ℕ ↦ -((1 : ℝ) / (2 * (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 4) := by
    funext k
    rw [Odd.neg_one_pow ⟨k + 1, by ring⟩]
    ring
  have key := HasSum.even_add_odd
    (f := fun n : ℕ ↦ (-1 : ℝ) ^ (n + 2) / (2 * ((n : ℝ) + 1)) ^ 4)
    (by show HasSum (fun k : ℕ ↦ (-1 : ℝ) ^ (2 * k + 2) / (2 * (((2 * k : ℕ) : ℝ) + 1)) ^ 4) _; rw [fe]; exact hE)
    (by show HasSum (fun k : ℕ ↦ (-1 : ℝ) ^ (2 * k + 1 + 2) / (2 * (((2 * k + 1 : ℕ) : ℝ) + 1)) ^ 4) _; rw [fo]; exact hO.neg)
  have ev : Real.pi ^ 4 / 1440 - Real.pi ^ 4 / 1440 / 16 + -(Real.pi ^ 4 / 1440 / 16)
      = 7 * Real.pi ^ 4 / 11520 := by ring
  rw [ev] at key
  exact key
