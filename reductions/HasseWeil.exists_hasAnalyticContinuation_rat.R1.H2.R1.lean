import OMAReductions.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Complex.Convex

-- Reduction HasseWeil.exists_hasAnalyticContinuation_rat.R1.H2.R1 of step HasseWeil.exists_hasAnalyticContinuation_rat.R1.H2
-- Credit: @Karataam

/-! The entire continuation of `L(E, s)` over `ℚ` follows from an entire completed L-function
`Λ(s) = (2π)^(-s) Γ(s) L(E, s)` that is only required to match on the real ray `s > 2`
(this is what the Mellin transform of the attached cusp form along the imaginary axis gives),
together with analyticity of `L(E, s)` on `Re s > 3/2`. Divide by `(2π)^(-s) Γ(s)` (using that
`1/Γ` is entire), then use the identity principle: the real ray accumulates inside the connected
half-plane `Re s > 3/2`. -/

open scoped Topology

namespace OMA.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1_H2_R1

-- An entire completed L-function, matching `(2π)^(-s) Γ(s) L(E, s)` on the real ray `s > 2`.
def H1 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧
      ∀ x : ℝ, 2 < x →
        Λ x = ((2 * Real.pi : ℝ) : ℂ) ^ (-(x : ℂ)) * Complex.Gamma x * E.LSeries x

-- Analyticity of the elliptic-curve series on the half-plane of absolute convergence.
def H2 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    AnalyticOnNhd ℂ E.LSeries {s | (3 / 2 : ℝ) < s.re}

lemma frequently_real_ray :
    ∃ᶠ z in 𝓝[≠] (3 : ℂ), ∃ x : ℝ, 2 < x ∧ z = (x : ℂ) := by
  have ht : Filter.Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] (3 : ℝ)) (𝓝[≠] (3 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := (Complex.continuous_ofReal.tendsto (3 : ℝ))
      simpa using this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (fun h : (x : ℂ) = 3 => hx (by exact_mod_cast h))
  refine ht.frequently ?_
  have hev : ∀ᶠ x in 𝓝[≠] (3 : ℝ), 2 < x :=
    nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (2 : ℝ) < 3))
  exact (hev.mono fun x hx => ⟨x, hx, rfl⟩).frequently

theorem main : H1 → H2 → OMA.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1.H2 := by
  intro completed analyticSeries E hE
  obtain ⟨Λ, hΛ, hΛx⟩ := @completed E hE
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]; exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  let L : ℂ → ℂ := fun z => Λ z * c ^ z * (Complex.Gamma z)⁻¹
  have hLd : Differentiable ℂ L := by
    intro z
    exact ((hΛ z).mul ((differentiableAt_id).const_cpow (Or.inl hc0))).mul
      (Complex.differentiable_one_div_Gamma z)
  have hLa : ∀ z, AnalyticAt ℂ L z := fun z => hLd.analyticAt z
  have hreal : ∀ x : ℝ, 2 < x → L x = E.LSeries x := by
    intro x hx
    have hG : Complex.Gamma (x : ℂ) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hcx : c ^ (x : ℂ) ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; exact fun h => hc0 h.1
    simp only [L, hΛx x hx, Complex.cpow_neg]
    field_simp
  refine ⟨L, hLa, fun s hs => ?_⟩
  have hU : AnalyticOnNhd ℂ L {z | (3 / 2 : ℝ) < z.re} := fun z _ => hLa z
  have hfreq : ∃ᶠ z in 𝓝[≠] (3 : ℂ), L z = E.LSeries z :=
    frequently_real_ray.mono fun z ⟨x, hx, hz⟩ => hz ▸ hreal x hx
  exact hU.eqOn_of_preconnected_of_frequently_eq (@analyticSeries E hE)
    (convex_halfSpace_re_gt (3 / 2 : ℝ)).isPreconnected
    (show (3 : ℂ) ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} by norm_num) hfreq
    (show s ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} by show (3 / 2 : ℝ) < s.re; linarith)

end OMA.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1_H2_R1
