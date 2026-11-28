import OMAReductions.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1
import Mathlib

/-! Extend a finite sequence by choosing a denominator past the exponential
of the required bound on its logarithmic weight. -/

theorem OMA.solution : OMA.R_FlintCooksonHills_cookson_hills_series_converges_R1_H1_R1.H2 := by
  classical
  intro ν hν approx m X D
  let w (q : ℕ → ℕ) (i : ℕ) : ℝ := Nat.ceil (Real.log (q i))
  change ∃ (p : ℕ → ℤ) (q : ℕ → ℕ), ∀ n < m,
    2 ≤ q n ∧ p n ≠ 0 ∧ |Real.pi - (p n : ℝ) / q n| ≤ (q n : ℝ) ^ (-ν) ∧
    X < w q n ∧ D * ((List.range n).reverse.map (w q)).prod < w q n
  have chooseAbove (T : ℝ) :
      ∃ (p : ℤ) (q : ℕ), 2 ≤ q ∧ p ≠ 0 ∧
        |Real.pi - (p : ℝ) / q| ≤ (q : ℝ) ^ (-ν) ∧ T < (Nat.ceil (Real.log q) : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp T)
    obtain ⟨p, q, hq, hclose⟩ := approx (max 2 N)
    have hq2 : 2 ≤ q := (le_max_left 2 N).trans hq
    have hqN : N ≤ q := (le_max_right 2 N).trans hq
    have hlog : T < Real.log q :=
      (Real.lt_log_iff_exp_lt (by positivity : 0 < (q : ℝ))).mpr
        (hN.trans_le (by exact_mod_cast hqN))
    have hp : p ≠ 0 := by
      intro hz
      have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
      have hpow : (q : ℝ) ^ (-ν) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
      simp [hz, abs_of_pos Real.pi_pos] at hclose
      linarith [Real.pi_gt_three]
    exact ⟨p, q, hq2, hp, hclose, hlog.trans_le (Nat.le_ceil _)⟩
  induction m with
  | zero => exact ⟨fun _ => 0, fun _ => 0, by omega⟩
  | succ m ih =>
    obtain ⟨p,q,h⟩ := ih
    let bound := D * ((List.range m).reverse.map (w q)).prod
    obtain ⟨a,b,hb,ha,hclose,hbig⟩ := chooseAbove (max X bound)
    let p' := Function.update p m a
    let q' := Function.update q m b
    have weights {n : ℕ} (hn : n ≤ m) :
        (List.range n).reverse.map (w q') = (List.range n).reverse.map (w q) := by
      apply List.map_congr_left
      intro i hi
      have hin := List.mem_range.mp (List.mem_reverse.mp hi)
      have hne : i ≠ m := by omega
      simp [q', w, Function.update_of_ne hne]
    refine ⟨p',q',?_⟩
    intro n hn
    by_cases hm : n = m
    · subst n
      rw [weights (le_refl m)]
      simpa [p', q', w, bound] using
        (show 2 ≤ b ∧ a ≠ 0 ∧ |Real.pi - (a : ℝ) / b| ≤ (b : ℝ) ^ (-ν) ∧
          X < (Nat.ceil (Real.log b) : ℝ) ∧ bound < (Nat.ceil (Real.log b) : ℝ) from
          ⟨hb,ha,hclose,(le_max_left X bound).trans_lt hbig,(le_max_right X bound).trans_lt hbig⟩)
    · have hlt : n < m := by omega
      rw [weights hlt.le]
      simpa [p', q', w, Function.update_of_ne hm] using h n hlt
