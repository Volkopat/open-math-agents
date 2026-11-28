import OMAStatements.S_mo_351446
import Mathlib

-- Problem: mo-351446, for reals a_1..a_k in (0,1) with sum < 1 there are infinitely many n
-- with sum of the fractional parts of n a_i less than 1.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Fix a bound A and put M = A + 1. The vectors of fractional parts of j M a_i (j = 0, 1, ...)
-- lie in the compact cube [0,1]^k, so a subsequence converges; two of its terms, with indices
-- j < j', differ by less than a small d in every coordinate. For m = (j' - j) M >= M all
-- m a_i are within d of an integer, hence the fractional part of (m + 1) a_i is a_i plus an
-- error of size < d, and the sum is less than (sum a_i) + k d < 1.

open Filter Topology in
theorem OMA.solution : type_of% @OMA.S_mo_351446.main := by
  intro k α hα hsum
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine Set.infinite_of_forall_exists_gt (fun a => ⟨a + 1, ⟨by omega, by simp⟩, by omega⟩)
  have hne : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  obtain ⟨i₀, hi₀⟩ := Finite.exists_min α
  have hgap : 0 < 1 - ∑ i, α i := by linarith
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  set δ := min (α i₀) ((1 - ∑ i, α i) / ((k : ℝ) + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (hα i₀).1 (div_pos hgap hk0)
  have hδα : ∀ i, δ ≤ α i := by
    intro i
    rw [hδdef]
    exact (min_le_left _ _).trans (hi₀ i)
  have hδk : (k : ℝ) * δ + δ ≤ 1 - ∑ i, α i := by
    have := (le_div_iff₀ hk0).mp (hδdef.le.trans (min_le_right _ _))
    nlinarith
  refine Set.infinite_of_forall_exists_gt (fun a => ?_)
  let x : ℕ → Fin k → ℝ := fun j i => Int.fract ((j : ℝ) * ((a : ℝ) + 1) * α i)
  have hx : ∀ j, x j ∈ Set.pi Set.univ (fun _ : Fin k => Set.Icc (0 : ℝ) 1) := by
    intro j i _
    dsimp only [x]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  obtain ⟨y, -, φ, hφ, hlim⟩ :=
    (isCompact_univ_pi (fun _ : Fin k => isCompact_Icc)).tendsto_subseq hx
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (δ / 2) (by positivity)
  have h1 := hN N le_rfl
  have h2 := hN (N + 1) (Nat.le_succ N)
  dsimp only [Function.comp_apply] at h1 h2
  have hφlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  have hd : dist (x (φ (N + 1))) (x (φ N)) < δ :=
    (dist_triangle_right _ _ y).trans_lt (by linarith)
  have hdiff : ∀ i, -δ < x (φ (N + 1)) i - x (φ N) i ∧ x (φ (N + 1)) i - x (φ N) i < δ := by
    intro i
    simpa only [Real.dist_eq, abs_lt] using (dist_pi_lt_iff hδpos).mp hd i
  have hn : (((φ (N + 1) - φ N) * (a + 1) + 1 : ℕ) : ℝ) =
      ((φ (N + 1) : ℝ) - (φ N : ℝ)) * ((a : ℝ) + 1) + 1 := by
    push_cast [Nat.cast_sub hφlt.le]
    ring
  have hfr : ∀ i, Int.fract ((((φ (N + 1) - φ N) * (a + 1) + 1 : ℕ) : ℝ) * α i) =
      x (φ (N + 1)) i - x (φ N) i + α i := by
    intro i
    obtain ⟨hlo, hhi⟩ := hdiff i
    have h3 : α i ≤ ∑ j, α j :=
      Finset.single_le_sum (fun j _ => (hα j).1.le) (Finset.mem_univ i)
    have h4 : δ ≤ (k : ℝ) * δ := le_mul_of_one_le_left hδpos.le hk1
    have hδi := hδα i
    rw [hn, Int.fract_eq_iff]
    refine ⟨by linarith, by linarith,
      ⌊(φ (N + 1) : ℝ) * ((a : ℝ) + 1) * α i⌋ - ⌊(φ N : ℝ) * ((a : ℝ) + 1) * α i⌋, ?_⟩
    have e1 := Int.self_sub_fract ((φ (N + 1) : ℝ) * ((a : ℝ) + 1) * α i)
    have e2 := Int.self_sub_fract ((φ N : ℝ) * ((a : ℝ) + 1) * α i)
    have e3 : (((φ (N + 1) : ℝ) - (φ N : ℝ)) * ((a : ℝ) + 1) + 1) * α i =
        (φ (N + 1) : ℝ) * ((a : ℝ) + 1) * α i - (φ N : ℝ) * ((a : ℝ) + 1) * α i + α i := by
      ring
    dsimp only [x]
    push_cast
    linarith
  have h5 : a + 1 ≤ (φ (N + 1) - φ N) * (a + 1) := Nat.le_mul_of_pos_left _ (by omega)
  refine ⟨(φ (N + 1) - φ N) * (a + 1) + 1, ⟨Nat.succ_pos _, ?_⟩,
    Nat.lt_succ_of_le (le_trans (Nat.le_succ a) h5)⟩
  rw [Finset.sum_congr rfl (fun i _ => hfr i), Finset.sum_add_distrib]
  have hle : ∑ i : Fin k, (x (φ (N + 1)) i - x (φ N) i) ≤ ∑ _i : Fin k, δ :=
    Finset.sum_le_sum (fun i _ => (hdiff i).2.le)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hle
  linarith
