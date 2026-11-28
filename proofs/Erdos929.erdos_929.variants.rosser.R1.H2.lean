import OMAReductions.R_Erdos929_erdos_929_variants_rosser_R1

/-!
The density of a periodic set is the proportion of its elements in one period.
This simplifies the limit argument in @loremcdmx's proof in PR #3607.
-/

open Filter Set
open scoped Topology

theorem OMA.solution : OMA.R_Erdos929_erdos_929_variants_rosser_R1.H2 := by
  classical
  intro S period hperiod hp
  let p : ℕ → Prop := fun n => n ∈ S
  let count := Nat.count p
  have shift (n : ℕ) : Nat.count (fun k => p (k + period)) n = count n := by
    simp only [count, Nat.count_eq_card_filter_range]
    congr 1
    ext k
    simp [p, hp]
  have blocks (q r : ℕ) : count (q * period + r) = q * count period + count r := by
    induction q with
    | zero => simp
    | succ q ih =>
      change Nat.count p ((q + 1) * period + r) = _
      rw [Nat.succ_mul, add_right_comm, Nat.count_add', shift, ih, Nat.succ_mul, add_right_comm]
  let density : ℝ := (period : ℝ)⁻¹ * count period
  have hdensity : S.HasDensity density := by
    have full : Tendsto (fun n : ℕ => ((n / period : ℕ) : ℝ) / n) atTop (𝓝 (period : ℝ)⁻¹) := by
      simpa only [Function.comp_def, ← div_eq_inv_mul, Nat.floor_div_eq_div] using
        (tendsto_nat_floor_mul_div_atTop (a := (period : ℝ)⁻¹) (by positivity)).comp
          tendsto_natCast_atTop_atTop
    have rest : Tendsto (fun n : ℕ => (count (n % period) : ℝ) / n) atTop (𝓝 0) :=
      squeeze_zero (fun _ => by positivity)
        (fun _ => div_le_div_of_nonneg_right (by exact_mod_cast Nat.count_le (p := p)) (by positivity))
        (tendsto_mod_div_atTop_nhds_zero_nat hperiod)
    have limit := (full.mul_const (count period : ℝ)).add rest
    rw [add_zero] at limit
    refine limit.congr fun n => ?_
    have hcard : (S ∩ Iio n).ncard = count n := by
      rw [show S ∩ Iio n = ↑((Finset.range n).filter p) by ext k; simp [p, and_comm],
        ncard_coe_finset, ← Nat.count_eq_card_filter_range]
    have hcount : count n = n / period * count period + count (n % period) := by
      simpa [Nat.div_add_mod, mul_comm] using blocks (n / period) (n % period)
    simp only [partialDensity, inter_univ, univ_inter, ncard_Iio_nat, hcard, hcount,
      Nat.cast_add, Nat.cast_mul, add_div, div_mul_eq_mul_div]
  have hpos : 0 < density ↔ S.Nonempty := by
    have hpR : 0 < (period : ℝ) := by exact_mod_cast hperiod
    have block_pos : 0 < count period ↔ ∃ k < period, k ∈ S := by
      simp [count, Nat.count_eq_card_filter_range, Finset.card_pos, Finset.Nonempty, p]
    dsimp only [density]
    rw [mul_pos_iff_of_pos_left (inv_pos.mpr hpR), Nat.cast_pos, block_pos]
    constructor
    · rintro ⟨k, -, hk⟩
      exact ⟨k, hk⟩
    · rintro ⟨n, hn⟩
      have per : Function.Periodic p period := fun k => propext (hp k)
      have hmod := per.nat_mul (n / period) (n % period)
      change p (n % period + n / period * period) = p (n % period) at hmod
      rw [Nat.mod_add_div'] at hmod
      exact ⟨n % period, Nat.mod_lt n hperiod, Eq.mp hmod hn⟩
  constructor
  · rintro ⟨r, hr, hlim⟩
    exact hpos.mp (tendsto_nhds_unique hlim hdensity ▸ hr)
  · exact fun h => ⟨density, hpos.mpr h, hdensity⟩
