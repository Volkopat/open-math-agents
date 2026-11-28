import OMAStatements.S_erdos_415

-- Reduction erdos-415.R1 of Erdős Problem 415
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: let R(n) be the length of the longest run phi(m+1) < phi(m+2) < ... < phi(m+k)
-- with m + k ≤ n. If every ordering pattern of length k appears below n, then in particular
-- the increasing pattern does, so F(n) ≤ R(n) (H1, elementary). Pollack, Pomerance and
-- Treviño (2013) proved R(n) = o(log log log n) (H2, a known theorem not in Mathlib; it is
-- the source of the negative answer cited on erdosproblems.com/415). main: for n ≥ 21 the
-- denominator L(n) = log log log n is nonnegative, so 0 ≤ F/L ≤ R/L eventually, hence
-- F/L → 0 by the squeeze theorem, which contradicts F/L → c > 0.
-- No computer search was used.

namespace OMA.R_erdos_415_R1

open Filter Topology OMA.S_erdos_415

/-- The combinatorial half: F(n) is at most the longest increasing run of φ below n. -/
def H1 : Prop :=
  ∀ n : ℕ, F n ≤ sSup {k : ℕ | ∃ m : ℕ, m + k ≤ n ∧
    ∀ i j : Fin k, i < j → Nat.totient (m + 1 + i) < Nat.totient (m + 1 + j)}

/-- The analytic half (Pollack-Pomerance-Treviño): the longest increasing run of φ below n
is o(log log log n). -/
def H2 : Prop :=
  Tendsto (fun n : ℕ => ((sSup {k : ℕ | ∃ m : ℕ, m + k ≤ n ∧
    ∀ i j : Fin k, i < j → Nat.totient (m + 1 + i) < Nat.totient (m + 1 + j)} : ℕ) : ℝ) /
      Real.log (Real.log (Real.log n))) atTop (𝓝 0)

theorem main : H1 → H2 → type_of% @OMA.S_erdos_415.main := by
  intro h1 h2 ⟨c, hc, hF⟩
  have he1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have he3 : Real.exp 3 < 21 := by
    have h := Real.exp_one_lt_d9
    have hp := Real.exp_pos 1
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
    nlinarith
  have hL : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (Real.log (Real.log n)) := by
    filter_upwards [eventually_ge_atTop 21] with n hn
    have hn' : (21 : ℝ) ≤ n := by exact_mod_cast hn
    have hpos : (0 : ℝ) < n := by linarith
    have h1le : Real.exp 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hpos]
      have := Real.exp_le_exp.mpr he1.le
      linarith
    apply Real.log_nonneg
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.log n) := Real.log_le_log (Real.exp_pos 1) h1le
  have h0 : Tendsto (fun n : ℕ => (F n : ℝ) / Real.log (Real.log (Real.log n))) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 ?_ ?_
    · filter_upwards [hL] with n hn
      exact div_nonneg (Nat.cast_nonneg _) hn
    · filter_upwards [hL] with n hn
      exact div_le_div_of_nonneg_right (by exact_mod_cast h1 n) hn
  have := tendsto_nhds_unique hF h0
  linarith

end OMA.R_erdos_415_R1
