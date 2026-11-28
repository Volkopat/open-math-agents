import FormalConjectures.Arxiv.«2406.10319».StableMatchingHyperbola
import Mathlib.Tactic

/-!
# A projected-rank reduction for the stable-matching hyperbola

Credit: @Pixelstorm44. The wife-rank threshold and concentration of the
rank product suffice for the joint threshold, for the same threshold sequence.
-/
open Filter MeasureTheory StableMarriage Arxiv.«2406.10319»
open scoped Topology

namespace OMA.R_Arxiv_2406_10319_pittel_hyperbola_threshold_R2

-- Product concentration above the logarithmic lower bound.
def H1 : Prop := ∀ ρ > (0 : ℝ), Tendsto (fun n : ℕ ↦
    ⨆ p : {p : unitInterval // (9 / 4 : ℝ) * (Real.log n)^2 / n < (p : ℝ)},
      marketLaw n p.1 {ω | ∃ M, IsPartialStable ω.1 ω.2 M ∧
        let s := Real.sqrt ((p : ℝ) * (n : ℝ)^3)
        ρ < |((totalWifeRank ω.1 ω.2 M : ℝ) / s) *
          ((totalHusbandRank ω.1 ω.2 M : ℝ) / s) - 1|}) atTop (𝓝 0)

-- Threshold for wife ranks alone. Above it, only one fixed target at a
-- time needs to be hit. Below it, covering the whole interval is unlikely.
def H2 : Prop :=
  let hit (n : ℕ) (p : unitInterval) (t ρ : ℝ) : Set (Profile n × Admissibility n) :=
    {ω | ∃ M, IsPartialStable ω.1 ω.2 M ∧
      |(totalWifeRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p : ℝ) * (n : ℝ)^3) - t| ≤ ρ}
  ∃ a : ℕ → Set.Ioo (0 : ℝ) 1,
    let d (n : ℕ) := min (a n : ℝ) (1 - (a n : ℝ))
    (∀ᶠ n : ℕ in atTop, (9 / 4 : ℝ) * (Real.log n)^2 / n < (a n : ℝ)) ∧
    ∀ δ ∈ Set.Ioo (0 : ℝ) 1,
      (∀ t ∈ Set.Icc (2 / 3 : ℝ) (3 / 2), ∀ ρ > (0 : ℝ), Tendsto (fun n : ℕ ↦
        ⨆ p : {p : unitInterval // (a n : ℝ) + δ * d n ≤ (p : ℝ)},
          marketLaw n p.1 (hit n p.1 t ρ)ᶜ) atTop (𝓝 0)) ∧
      ∃ ε > (0 : ℝ), Tendsto (fun n : ℕ ↦
        ⨆ p : {p : unitInterval // (p : ℝ) ≤ (a n : ℝ) - δ * d n},
          marketLaw n p.1 {ω | ∀ t ∈ Set.Icc (2 / 3 : ℝ) (3 / 2),
            ω ∈ hit n p.1 t ε}) atTop (𝓝 0)

lemma reciprocal_control {q r t ρ : ℝ} (ht : t ∈ Set.Icc (2 / 3 : ℝ) (3 / 2))
    (hρ : ρ ≤ 1 / 12) (hq : |q - t| ≤ 2 * ρ) (hp : |q * r - 1| ≤ ρ) :
    |r - t⁻¹| ≤ 10 * ρ := by
  have ht0 : 0 < t := by linarith [ht.1]
  have hq0 : 1 / 2 ≤ q := by linarith [(abs_le.mp hq).1, ht.1]
  have hi : |t⁻¹| ≤ 2 := by
    rw [abs_of_pos (inv_pos.mpr ht0), inv_eq_one_div, div_le_iff₀ ht0]
    linarith [ht.1]
  have heq : q * (r - t⁻¹) = (q*r - 1) + (t-q)*t⁻¹ := by
    field_simp
    ring
  have bound : q * |r - t⁻¹| ≤ ρ + (2 * ρ) * 2 := calc
    q * |r - t⁻¹| = |q * (r - t⁻¹)| := by rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ q)]
    _ ≤ |q*r - 1| + |(t-q)*t⁻¹| := heq ▸ abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul, abs_sub_comm t q]
      exact add_le_add hp (mul_le_mul hq hi (abs_nonneg _) ((abs_nonneg _).trans hq))
  nlinarith [mul_nonneg (sub_nonneg.mpr hq0) (abs_nonneg (r - t⁻¹))]

theorem main : H1 → H2 → type_of% @Arxiv.«2406.10319».pittel_hyperbola_threshold := by
  classical
  intro hprod hproj
  obtain ⟨a, ha, h⟩ := hproj
  refine ⟨a, ha, ?_⟩
  intro δ hδ
  obtain ⟨habove, hbelow⟩ := h δ hδ
  constructor
  · intro ε hε
    let ρ := min (ε / 12) (1 / 12)
    have hρ : 0 < ρ := lt_min (by positivity) (by norm_num)
    have hρε : ρ ≤ ε / 12 := min_le_left _ _
    obtain ⟨S, hS, hf, hcover⟩ := finite_cover_balls_of_compact
      (isCompact_Icc (a := (2 / 3 : ℝ)) (b := 3 / 2)) hρ
    let U (n : ℕ) := {p : unitInterval //
      (a n : ℝ) + δ * min (a n : ℝ) (1 - (a n : ℝ)) ≤ (p : ℝ)}
    let V (n : ℕ) := {p : unitInterval // (9 / 4 : ℝ) * (Real.log n)^2 / n < (p : ℝ)}
    let bad (n : ℕ) (p : unitInterval) : Set (Profile n × Admissibility n) :=
      {ω | ∃ M, IsPartialStable ω.1 ω.2 M ∧
        let s := Real.sqrt ((p : ℝ) * (n : ℝ)^3)
        ρ < |((totalWifeRank ω.1 ω.2 M : ℝ) / s) *
          ((totalHusbandRank ω.1 ω.2 M : ℝ) / s) - 1|}
    let miss (n : ℕ) (p : unitInterval) (t : ℝ) : Set (Profile n × Admissibility n) :=
      {ω | ∃ M, IsPartialStable ω.1 ω.2 M ∧
        |(totalWifeRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p : ℝ) * (n : ℝ)^3) - t| ≤ ρ}ᶜ
    have hnet : Tendsto (fun n : ℕ ↦ ∑ t ∈ hf.toFinset,
        ⨆ p : U n, marketLaw n p.1 (miss n p.1 t)) atTop (𝓝 0) := by
      simpa only [Finset.sum_const_zero] using tendsto_finsetSum hf.toFinset (fun t ht ↦
        habove t (hS (hf.mem_toFinset.mp ht)) ρ hρ)
    have hprob : Tendsto (fun n : ℕ ↦ ⨆ p : V n, marketLaw n p.1 (bad n p.1)) atTop (𝓝 0) :=
      hprod ρ hρ
    have hsum := hprob.add hnet
    rw [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ ↦ bot_le) ?_
    filter_upwards [ha, eventually_gt_atTop 0] with n hn hn0
    refine iSup_le fun (p : U n) ↦ ?_
    have hd : 0 ≤ min (a n : ℝ) (1 - (a n : ℝ)) :=
      le_min (a n).2.1.le (sub_nonneg.mpr (a n).2.2.le)
    have hap : (a n : ℝ) ≤ (p.1 : ℝ) := by
      have := p.2
      linarith [mul_nonneg hδ.1.le hd]
    let v : V n := ⟨p.1, hn.trans_le hap⟩
    have sub : (hyperbolaEvent n p.1 ε)ᶜ ⊆ bad n p.1 ∪ ⋃ t ∈ hf.toFinset, miss n p.1 t := by
      intro ω hω
      by_contra hnone
      have good (M) (hM : IsPartialStable ω.1 ω.2 M) :
          |((totalWifeRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p.1 : ℝ) * (n : ℝ)^3)) *
           ((totalHusbandRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p.1 : ℝ) * (n : ℝ)^3)) - 1| ≤ ρ :=
        le_of_not_gt fun he ↦ hnone (Or.inl ⟨M,hM,he⟩)
      apply hω
      refine ⟨hn0, (a n).2.1.trans_le hap, fun M hM ↦ (good M hM).trans (by linarith), ?_⟩
      intro t ht
      obtain ⟨u, hu, hdist⟩ := Set.mem_iUnion₂.mp (hcover ht)
      have htu : |t-u| < ρ := by simpa [Metric.mem_ball, Real.dist_eq] using hdist
      have hm : ω ∉ miss n p.1 u := fun hu' ↦
        hnone (Or.inr (Set.mem_iUnion₂.mpr ⟨u, hf.mem_toFinset.mpr hu, hu'⟩))
      obtain ⟨M, hM, hq⟩ := not_not.mp hm
      let q := (totalWifeRank ω.1 ω.2 M : ℝ) / Real.sqrt ((p.1 : ℝ) * (n : ℝ)^3)
      have hqt : |q-t| ≤ 2 * ρ := by
        have := abs_sub_le q u t
        rw [abs_sub_comm u t] at this
        change |q-u| ≤ ρ at hq
        linarith
      refine ⟨M, hM, max_le (hqt.trans (by linarith)) ?_⟩
      exact (reciprocal_control ht (min_le_right _ _) hqt (good M hM)).trans (by linarith)
    calc
      _ ≤ _ := measure_mono sub
      _ ≤ _ := measure_union_le _ _
      _ ≤ marketLaw n p.1 (bad n p.1) + ∑ t ∈ hf.toFinset, marketLaw n p.1 (miss n p.1 t) :=
        add_le_add le_rfl (measure_biUnion_finset_le _ _)
      _ ≤ _ := add_le_add (le_iSup (fun v : V n ↦ marketLaw n v.1 (bad n v.1)) v)
        (Finset.sum_le_sum fun t _ ↦ le_iSup (fun u : U n ↦ marketLaw n u.1 (miss n u.1 t)) p)
  · obtain ⟨ε, hε, hlim⟩ := hbelow
    refine ⟨ε, hε, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ ↦ bot_le) (fun n ↦ iSup_mono fun p ↦ measure_mono ?_)⟩
    intro ω hω t ht
    obtain ⟨M,hM,hb⟩ := hω.2.2.2 t ht
    exact ⟨M,hM,(le_max_left _ _).trans hb⟩

end OMA.R_Arxiv_2406_10319_pittel_hyperbola_threshold_R2
