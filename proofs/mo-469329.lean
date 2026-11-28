import OMAStatements.S_mo_469329
-- Retains @caa1982's logarithmic lower-bound proof from PR #28814.
-- Standard reciprocal and logarithm bounds finish the existing estimates.

open OMA.S_mo_469329

lemma seq_pos (T : ℕ) (hT : 1 ≤ T) : ∀ r, 0 < seq T r
  | 0 => by
    simp only [seq]
    have : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  | r + 1 => by
    simp only [seq]
    have := seq_pos T hT r
    positivity

lemma log_step (T : ℕ) (hT : 1 ≤ T) (n : ℕ) :
    Real.log (seq T n) - Real.log (seq T 0) ≤ ∑ r ∈ Finset.range n, seq T r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp := seq_pos T hT n
    have h1 : seq T (n + 1) = seq T n * (1 + seq T n) := by
      simp only [seq]; ring
    have h2 : Real.log (seq T (n + 1)) = Real.log (seq T n) + Real.log (1 + seq T n) := by
      rw [h1, Real.log_mul hp.ne' (by linarith)]
    have h3 : Real.log (1 + seq T n) ≤ seq T n := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + seq T n by linarith)
      linarith
    linarith

lemma inv_step (T : ℕ) (hT : 1 ≤ T) (n : ℕ) :
    1 / seq T n ≤ 1 / seq T 0 - n + ∑ r ∈ Finset.range n, seq T r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp := seq_pos T hT n
    have h1 : seq T (n + 1) = seq T n * (1 + seq T n) := by
      simp only [seq]; ring
    have key : 1 / seq T (n + 1) ≤ 1 / seq T n - 1 + seq T n := by
      rw [h1]
      have hq : 0 < 1 + seq T n := by linarith
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [sq_nonneg (seq T n), mul_pos hp hp, mul_pos (mul_pos hp hp) hp]
    push_cast
    linarith

theorem OMA.solution : type_of% @OMA.S_mo_469329.main := by
  refine ⟨1 / 2, by norm_num, 1, fun T hT => ?_⟩
  set S := ∑ r ∈ Finset.range T, seq T r with hS
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have h0 : seq T 0 = 1 / (T : ℝ) := rfl
  have hpT := seq_pos T hT T
  have hA := log_step T hT T
  have hB := inv_step T hT T
  rw [h0, one_div_one_div] at hB
  have hB' : 1 / seq T T ≤ S := by linarith
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hB'
  -- seq T T ≥ 1 / S
  have hlog1 : Real.log (1 / S) ≤ Real.log (seq T T) :=
    Real.log_le_log (by positivity) ((one_div_le hpT hSpos).mp hB')
  rw [one_div, Real.log_inv] at hlog1
  rw [h0, one_div, Real.log_inv] at hA
  linarith [Real.log_le_self hSpos.le]
