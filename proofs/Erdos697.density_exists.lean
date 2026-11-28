import FormalConjectures.ErdosProblems.«697»

/-!
Count the complete periods and bound the contribution of the final partial period.
The periodicity argument follows @VinnyMo's proof in PR #752.
-/

open Filter Set
open scoped Topology

theorem OMA.solution : type_of% @Erdos697.density_exists := by
  classical
  intro m α
  let B := Real.exp ((m : ℝ) ^ α)
  let period := (⌈B⌉₊).factorial
  let p (n : ℕ) := ∃ d : ℕ, d ≡ 1 [MOD m] ∧ (d : ℝ) ∈ Ioo 1 B ∧ d ∣ n
  let count := Nat.count p
  have hp (n : ℕ) : p (n + period) ↔ p n := by
    refine exists_congr fun d => and_congr_right fun _ => and_congr_right fun hd => ?_
    have hdiv : d ∣ period :=
      Nat.dvd_factorial (by exact_mod_cast zero_lt_one.trans hd.1) (Nat.lt_ceil.mpr hd.2).le
    exact (Nat.dvd_add_iff_left hdiv).symm
  have shift (n : ℕ) : Nat.count (fun k => p (k + period)) n = count n := by
    simp only [count, Nat.count_eq_card_filter_range]
    congr 1
    ext k
    simp [hp]
  have blocks (q r : ℕ) : count (q * period + r) = q * count period + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * period + r) = _
      rw [Nat.succ_mul, add_right_comm, Nat.count_add', shift]
      rw [ih, Nat.succ_mul, add_right_comm]
  have decompose (n : ℕ) : count n = n / period * count period + count (n % period) := by
    simpa [Nat.div_add_mod, mul_comm] using blocks (n / period) (n % period)
  have full : Tendsto (fun n : ℕ => ((n / period : ℕ) : ℝ) / n) atTop (𝓝 (period : ℝ)⁻¹) := by
    simpa only [Function.comp_def, ← div_eq_inv_mul, Nat.floor_div_eq_div] using
      (tendsto_nat_floor_mul_div_atTop (a := (period : ℝ)⁻¹) (by positivity)).comp
        tendsto_natCast_atTop_atTop
  have rest : Tendsto (fun n : ℕ => (count (n % period) : ℝ) / n) atTop (𝓝 0) :=
    squeeze_zero (fun _ => by positivity)
      (fun n => div_le_div_of_nonneg_right (by exact_mod_cast Nat.count_le (p := p)) (by positivity))
      (tendsto_mod_div_atTop_nhds_zero_nat (Nat.factorial_pos _))
  refine ⟨(period : ℝ)⁻¹ * count period, ?_⟩
  have limit := (full.mul_const (count period : ℝ)).add rest
  rw [add_zero] at limit
  refine limit.congr fun n => ?_
  have hcard : ({k | p k} ∩ Iio n).ncard = count n := by
    rw [show {k | p k} ∩ Iio n = ↑((Finset.range n).filter p) by ext k; simp [and_comm],
      Set.ncard_coe_finset, ← Nat.count_eq_card_filter_range]
  change _ = (({k | p k} ∩ univ ∩ Iio n).ncard : ℝ) / ((univ ∩ Iio n).ncard : ℝ)
  rw [inter_univ, univ_inter, ncard_Iio_nat, hcard, decompose n, Nat.cast_add,
    Nat.cast_mul, add_div, div_mul_eq_mul_div]
