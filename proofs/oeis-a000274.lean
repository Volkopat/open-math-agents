import OMAStatements.S_oeis_a000274
import Mathlib.Combinatorics.Derangements.Exponential

open Filter
open scoped Topology

private noncomputable def r (n : ℕ) : ℝ := (numDerangements n : ℝ) / n.factorial

private lemma r_step (n : ℕ) : r (n + 1) = r n - (-1 : ℝ) ^ n / (n + 1).factorial := by
  have hD : (numDerangements (n + 1) : ℝ) = ((n : ℝ) + 1) * numDerangements n - (-1 : ℝ) ^ n := by
    exact_mod_cast numDerangements_succ n
  have h1 : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1 ≠ 0 := by positivity
  dsimp [r]; rw [hD, sub_div, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]; congr 1; field_simp

private lemma s_step (n : ℕ) : (-1 : ℝ) ^ n * r (n + 2) < (-1 : ℝ) ^ n * r n := by
  have h2 : r (n + 2) = r n - (-1 : ℝ) ^ n * (1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ)) := by
    rw [r_step (n + 1), r_step n, pow_succ]; ring
  have hg : 0 < 1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ) :=
    sub_pos.2 (one_div_lt_one_div_of_lt (by positivity) (by exact_mod_cast Nat.factorial_lt_of_lt (by omega) (by omega)))
  have hs : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h2]; nlinarith [congrArg (· * (1 / ((n + 1).factorial : ℝ) - 1 / ((n + 2).factorial : ℝ))) hs]

private lemma s_lt (n : ℕ) : (-1 : ℝ) ^ n * Real.exp (-1) < (-1 : ℝ) ^ n * r n := by
  have hle (m : ℕ) : (-1 : ℝ) ^ m * Real.exp (-1) ≤ (-1 : ℝ) ^ m * r m := by
    let f k := (-1 : ℝ) ^ m * r (m + 2 * k)
    have hl : Tendsto f atTop (𝓝 ((-1 : ℝ) ^ m * Real.exp (-1))) :=
      (numDerangements_tendsto_inv_e.comp (tendsto_atTop_atTop.2 fun a => ⟨a, by omega⟩)).const_mul _
    have hf : Antitone f := antitone_nat_of_succ_le fun k => by
      have h := (s_step (m + 2 * k)).le
      have hp : (-1 : ℝ) ^ (m + 2 * k) = (-1 : ℝ) ^ m := by rw [pow_add, pow_mul]; norm_num
      rw [hp] at h
      simpa [f, show m + 2 * (k + 1) = m + 2 * k + 2 by omega] using h
    simpa [f] using le_of_tendsto' hl fun k => hf (Nat.zero_le k)
  have h := hle (n + 2)
  have hp : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by rw [pow_add]; norm_num
  rw [hp] at h
  exact h.trans_lt (s_step n)

private lemma fl (n : ℕ) : ⌊(n.factorial : ℝ) / Real.exp 1⌋ = (numDerangements n : ℤ) - if Even n then 1 else 0 := by
  have hp : 0 < (n.factorial : ℝ) := by positivity
  have hfac : (n.factorial : ℝ) / (n + 1).factorial ≤ 1 :=
    (div_le_one (by positivity)).2 (by exact_mod_cast Nat.factorial_le (Nat.le_succ n))
  have h1 := s_lt n; have h2 := s_lt (n + 1)
  have hr : r n * n.factorial = numDerangements n := div_mul_cancel₀ _ hp.ne'
  have hr' : r (n + 1) * n.factorial = numDerangements n - (-1 : ℝ) ^ n * ((n.factorial : ℝ) / (n + 1).factorial) := by
    rw [r_step, sub_mul, hr]; ring
  apply Int.floor_eq_iff.2
  rw [div_eq_mul_inv, ← Real.exp_neg]
  by_cases he : Even n
  · rw [he.neg_one_pow, one_mul] at h1 hr'
    rw [pow_succ, he.neg_one_pow] at h2
    have ha := mul_lt_mul_of_pos_right h1 hp
    have hb := mul_lt_mul_of_pos_right (show r (n + 1) < Real.exp (-1) by linarith) hp
    rw [if_pos he]; push_cast; constructor <;> linarith
  · have ho := Nat.not_even_iff_odd.1 he
    rw [ho.neg_one_pow] at h1 hr'
    rw [pow_succ, ho.neg_one_pow] at h2
    have ha := mul_lt_mul_of_pos_right (show r n < Real.exp (-1) by linarith) hp
    have hb := mul_lt_mul_of_pos_right (show Real.exp (-1) < r (n + 1) by linarith) hp
    rw [if_neg he]; push_cast; constructor <;> linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a000274.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  unfold OMA.S_oeis_a000274.a
  rw [Nat.add_sub_cancel, fl, fl, numDerangements_succ]
  by_cases he : Even k
  · rw [if_neg (by simpa [Nat.even_add_one] using he), if_pos he, he.neg_one_pow]; push_cast; ring
  · rw [if_pos (Nat.even_add_one.2 he), if_neg he, (Nat.not_even_iff_odd.1 he).neg_one_pow]; push_cast; ring
