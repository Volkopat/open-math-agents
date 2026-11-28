import FormalConjectures.Wikipedia.InscribedSquare
import Mathlib

/-! A measure-theoretic step for positive-area traces and an integer-lattice
question for null traces. The compactness argument preserves a positive lower
bound on the physical side length while the grid error goes to zero. -/

namespace OMA.R_InscribedSquare_inscribed_square_problem_R1

open Filter MeasureTheory Set Topology
open scoped ENNReal EuclideanGeometry Pointwise

/-- Four translates of a positive-area compact set have a common point for
every sufficiently small axis-aligned square pattern. -/
def H1 : Prop :=
  ∀ K : Set ℝ², IsCompact K → 0 < volume K →
    ∀ᶠ h : ℝ in 𝓝 0, ∃ a : ℝ², a ∈ K ∧ a + !₂[h, 0] ∈ K ∧
      a + !₂[h, 0] + !₂[0, h] ∈ K ∧ a + !₂[0, h] ∈ K

/-- On arbitrarily fine grids, the four-mesh neighborhood of a null Jordan
trace contains a lattice square of side at least one fixed positive number.
The integer pair u,v specifies a side and its quarter-turn specifies the next. -/
def H2 : Prop :=
  ∀ (γ : Circle → ℝ²), IsEmbedding γ → volume (Set.range γ) = 0 →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (i j u v : ℤ),
      let h : ℝ := 1 / ((m : ℝ) + 1)
      let grid (s t : ℤ) : ℝ² := !₂[(s : ℝ) * h, (t : ℝ) * h]
      let a := grid i j
      let b := grid u v
      let d := grid (-v) u
      let z : Fin 4 → ℝ² := ![a, a + b, a + b + d, a + d]
      4 * h ≤ ε ∧ ρ ≤ dist (z 0) (z 1) ∧
        ∀ k, ∃ t, dist (z k) (γ t) ≤ 4 * h

/-- The part of a compact set that a small translation sends outside the set
has arbitrarily small measure. -/
theorem small_translation_loss (K : Set ℝ²) (hK : IsCompact K) {e : ℝ≥0∞} (he : e ≠ 0) :
    ∀ᶠ v : ℝ² in 𝓝 0, volume {a | a ∈ K ∧ a + v ∉ K} < e := by
  filter_upwards [eventually_nhds_zero_measure_vadd_sdiff_lt hK hK.isClosed he (μ := volume)]
    with v hv
  calc
    volume {a | a ∈ K ∧ a + v ∉ K}
        ≤ volume ((fun a : ℝ² => a + v) ⁻¹' ((v +ᵥ K) \ K)) := by
          apply measure_mono
          intro a ha
          exact ⟨⟨a, ha.1, add_comm v a⟩, ha.2⟩
    _ = volume ((v +ᵥ K) \ K) := measure_preimage_add_right volume v _
    _ < e := hv

/-- Every sufficiently small axis-aligned square has a translate with all four
vertices in any fixed compact planar set of positive area. -/
theorem positive_area_overlap (K : Set ℝ²) (hK : IsCompact K) (hm : 0 < volume K) :
    ∀ᶠ h : ℝ in 𝓝 0, ∃ a : ℝ², a ∈ K ∧ a + !₂[h, 0] ∈ K ∧
      a + !₂[h, 0] + !₂[0, h] ∈ K ∧ a + !₂[0, h] ∈ K := by
  let M := (volume K).toReal
  have hfin : volume K ≠ ∞ := hK.measure_lt_top.ne
  have hM : 0 < M := ENNReal.toReal_pos hm.ne' hfin
  let e := ENNReal.ofReal (M / 4)
  have he : 0 < e := ENNReal.ofReal_pos.mpr (by linarith)
  have three : e + e + e < volume K := by
    calc
      e + e + e = ENNReal.ofReal (M / 4 + M / 4 + M / 4) := by
        simp only [e, ENNReal.ofReal_add (by linarith : 0 ≤ M / 4) (by linarith : 0 ≤ M / 4),
          ENNReal.ofReal_add (by linarith : 0 ≤ M / 4 + M / 4) (by linarith : 0 ≤ M / 4)]
      _ < ENNReal.ofReal M := (ENNReal.ofReal_lt_ofReal_iff hM).mpr (by linarith)
      _ = volume K := ENNReal.ofReal_toReal hfin
  let bad (v : ℝ²) : Set ℝ² := {a | a ∈ K ∧ a + v ∉ K}
  have loss : ∀ᶠ v : ℝ² in 𝓝 0, volume (bad v) < e :=
    small_translation_loss K hK he.ne'
  let X (h : ℝ) : ℝ² := h • !₂[(1 : ℝ), 0]
  let Y (h : ℝ) : ℝ² := h • !₂[(0 : ℝ), 1]
  have axis (w : ℝ²) : Tendsto (fun h : ℝ => h • w) (𝓝 0) (𝓝 0) := by
    have hc : Continuous (fun h : ℝ => h • w) := by fun_prop
    simpa only [zero_smul] using hc.tendsto (0 : ℝ)
  have hx : Tendsto X (𝓝 0) (𝓝 0) := axis _
  have hy : Tendsto Y (𝓝 0) (𝓝 0) := axis _
  have hxy : Tendsto (fun h => X h + Y h) (𝓝 0) (𝓝 0) := by simpa using hx.add hy
  filter_upwards [hx.eventually loss, hy.eventually loss, hxy.eventually loss] with h bx by' bxy
  have not_cover : ¬ K ⊆ (bad (X h) ∪ bad (Y h)) ∪ bad (X h + Y h) := by
    intro cover
    apply (not_lt_of_ge (measure_mono (μ := volume) cover))
    calc
      volume ((bad (X h) ∪ bad (Y h)) ∪ bad (X h + Y h))
          ≤ volume (bad (X h) ∪ bad (Y h)) + volume (bad (X h + Y h)) :=
            measure_union_le _ _
      _ ≤ (volume (bad (X h)) + volume (bad (Y h))) + volume (bad (X h + Y h)) :=
            add_le_add (measure_union_le _ _) le_rfl
      _ ≤ e + e + e := add_le_add (add_le_add bx.le by'.le) bxy.le
      _ < volume K := three
  obtain ⟨a, ha, good⟩ := Set.not_subset.mp not_cover
  have ax : a + X h ∈ K := by
    by_contra hbad
    exact good (.inl (.inl ⟨ha, hbad⟩))
  have ay : a + Y h ∈ K := by
    by_contra hbad
    exact good (.inl (.inr ⟨ha, hbad⟩))
  have axy : a + (X h + Y h) ∈ K := by
    by_contra hbad
    exact good (.inr ⟨ha, hbad⟩)
  have ex : X h = !₂[h, 0] := by ext k; fin_cases k <;> simp [X, PiLp.smul_apply]
  have ey : Y h = !₂[0, h] := by ext k; fin_cases k <;> simp [Y, PiLp.smul_apply]
  exact ⟨a, ha, ex ▸ ax, by simpa [ex, ey, add_assoc] using axy, ey ▸ ay⟩

/-- The midpoint, diagonal and side identities hold even at zero scale. -/
theorem square_identities (a : ℝ²) (x y : ℝ) :
    let b : ℝ² := !₂[x, y]
    let d : ℝ² := !₂[-y, x]
    a + (a + b + d) = (a + b) + (a + d) ∧
      dist a (a + b + d) = dist (a + b) (a + d) ∧
      dist a (a + b) = dist (a + b) (a + b + d) := by
  dsimp only
  refine ⟨by abel, ?_, ?_⟩ <;>
    apply (sq_eq_sq₀ dist_nonneg dist_nonneg).mp <;>
    rw [EuclideanSpace.dist_sq_eq, EuclideanSpace.dist_sq_eq] <;>
    simp [Fin.sum_univ_two, Real.dist_eq, sq_abs, PiLp.add_apply] <;> ring

/-- Extract four limiting parameters simultaneously. The lower bound keeps
both adjacent sides positive in the limit. -/
theorem inscribe_of_approx (γ : Circle → ℝ²) (hc : Continuous γ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ (z : Fin 4 → ℝ²) (t : Fin 4 → Circle),
      z 0 + z 2 = z 1 + z 3 ∧ dist (z 0) (z 2) = dist (z 1) (z 3) ∧
      dist (z 0) (z 1) = dist (z 1) (z 2) ∧ ρ ≤ dist (z 0) (z 1) ∧
      ∀ k, dist (z k) (γ (t k)) ≤ ε) :
    ∃ t₁ t₂ t₃ t₄, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 := by
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have he (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose z t hmid hdiag hside hbound hnear using fun n => ha (ε n) (he n)
  obtain ⟨s, φ, hφ, hs⟩ := CompactSpace.tendsto_subseq t
  have he0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hz (k : Fin 4) : Tendsto (fun n => z (φ n) k) atTop (𝓝 (γ (s k))) := by
    have ht := hc.continuousAt.tendsto.comp ((tendsto_pi_nhds.mp hs) k)
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hnear0 : Tendsto (fun n => dist (z (φ n) k) (γ (t (φ n) k))) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun n => hnear (φ n) k) (he0.comp hφ.tendsto_atTop)
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle (z (φ n) k) (γ (t (φ n) k)) (γ (s k)))
      (by simpa using hnear0.add (tendsto_iff_dist_tendsto_zero.mp ht))
  have mid := tendsto_nhds_unique_of_eventuallyEq ((hz 0).add (hz 2))
    ((hz 1).add (hz 3)) (Eventually.of_forall (fun n => hmid (φ n)))
  have diag := tendsto_nhds_unique_of_eventuallyEq ((hz 0).dist (hz 2))
    ((hz 1).dist (hz 3)) (Eventually.of_forall (fun n => hdiag (φ n)))
  have side := tendsto_nhds_unique_of_eventuallyEq ((hz 0).dist (hz 1))
    ((hz 1).dist (hz 2)) (Eventually.of_forall (fun n => hside (φ n)))
  have pos : 0 < dist (γ (s 0)) (γ (s 1)) :=
    hρ.trans_le (ge_of_tendsto' ((hz 0).dist (hz 1)) (fun n => hbound (φ n)))
  have pos' := side ▸ pos
  exact ⟨s 0, s 1, s 2, s 3, mid, diag, dist_pos.mp pos, dist_pos.mp pos',
    by rw [side, div_self pos'.ne']⟩

/-- Turn a common point of four translates into four parameters on the curve. -/
theorem inscribe_of_overlap (overlap : H1) (γ : Circle → ℝ²) (hc : Continuous γ)
    (hm : 0 < volume (Set.range γ)) :
    ∃ t₁ t₂ t₃ t₄, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 := by
  have hK := isCompact_range hc
  obtain ⟨δ, hδ, inside⟩ := Metric.eventually_nhds_iff.mp
    (overlap (Set.range γ) hK hm)
  let h := δ / 2
  have hh : 0 < h := half_pos hδ
  obtain ⟨a, ⟨p, hp⟩, ⟨q, hq⟩, ⟨r, hr⟩, ⟨s, hs⟩⟩ :=
    inside (y := h) (by simpa [Real.dist_eq, h, abs_of_pos hδ] using half_lt_self hδ)
  obtain ⟨hm, hd, he⟩ := square_identities a h 0
  simp only [neg_zero] at hm hd he
  have hab : a ≠ a + !₂[h, 0] := by
    intro e
    have e₀ := congrArg (fun v : ℝ² => v 0) e
    simp [PiLp.add_apply] at e₀
    exact hh.ne' e₀
  have hbc := he ▸ dist_pos.mpr hab
  refine ⟨p, q, r, s, ?_⟩
  rw [hp, hq, hr, hs]
  exact ⟨hm, hd, hab, dist_pos.mp hbc, by rw [he, div_self hbc.ne']⟩

/-- An unconditional instance of the exact square predicate. -/
theorem square_of_positive_trace (γ : Circle → ℝ²) (hc : Continuous γ)
    (hm : 0 < volume (Set.range γ)) :
    ∃ t₁ t₂ t₃ t₄, InscribedSquare.IsRectangle (γ t₁) (γ t₂) (γ t₃) (γ t₄) 1 :=
  inscribe_of_overlap positive_area_overlap γ hc hm

theorem main : H1 → H2 → type_of% @InscribedSquare.inscribed_square_problem := by
  intro overlap lattice γ hγ
  by_cases hnull : volume (Set.range γ) = 0
  · obtain ⟨ρ, hρ, hgrid⟩ := lattice γ hγ hnull
    apply inscribe_of_approx γ hγ.continuous ρ hρ
    intro ε hε
    obtain ⟨m, i, j, u, v, hmesh, hbound, hnear⟩ := hgrid ε hε
    let h : ℝ := 1 / ((m : ℝ) + 1)
    let a : ℝ² := !₂[(i : ℝ) * h, (j : ℝ) * h]
    let b : ℝ² := !₂[(u : ℝ) * h, (v : ℝ) * h]
    let d : ℝ² := !₂[-((v : ℝ) * h), (u : ℝ) * h]
    let z : Fin 4 → ℝ² := ![a, a + b, a + b + d, a + d]
    have near (k : Fin 4) : ∃ t, dist (z k) (γ t) ≤ 4 * h := by
      simpa [z, a, b, d, h, neg_mul] using hnear k
    choose t ht using near
    obtain ⟨hm, hd, hs⟩ := square_identities a ((u : ℝ) * h) ((v : ℝ) * h)
    exact ⟨z, t, hm, hd, hs, hbound, fun k => (ht k).trans hmesh⟩
  · exact inscribe_of_overlap overlap γ hγ.continuous (pos_iff_ne_zero.mpr hnull)

end OMA.R_InscribedSquare_inscribed_square_problem_R1
