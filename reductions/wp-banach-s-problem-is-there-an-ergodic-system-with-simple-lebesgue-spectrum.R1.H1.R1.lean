import OMAReductions.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1
import Mathlib
-- Adapted from OpenAI, openai/math @3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0.
namespace OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1_H1_R1
open MeasureTheory Filter
open scoped Topology

def H1 : Prop :=
  let X := UnitAddCircle × UnitAddCircle × UnitAddCircle
  let m : Measure UnitAddCircle := AddCircle.haarAddCircle
  let μ : Measure X := m.prod (m.prod m)
  ∀ a : ℕ → C(X,ℂ), ((∀ i x, star (a i x) = a i x) ∧ (∀ i, ∫ x, a i x ∂μ = 0) ∧ (∀ i x, ‖a i x‖ ≤ 1)) →
    ∃ (A : ℕ → ℤ → C(X,X)) (p : ∀ n k, MeasurePreserving (A n k) μ μ) (v : ℕ → Lp ℂ 2 μ),
      let w := fun n k => Lp.compMeasurePreserving (A n k) (p n k) (v n)
      (∀ n x, A n 0 x = x) ∧ (∀ n (i j : ℤ) x, A n (i+j) x = A n i (A n j x)) ∧ (∀ k, CauchySeq (fun n => A n k)) ∧ CauchySeq v ∧
      (∀ k j : ℤ, ∀ᶠ n in atTop, inner ℂ (w n k) (w n j) = if k=j then 1 else 0) ∧
      (∀ k, ∀ᶠ n in atTop, inner ℂ ((memLp_const (1 : ℂ) : MemLp (fun _ : X => (1 : ℂ)) 2 μ).toLp _) (w n k) = 0) ∧
      ∀ i (ε : ℝ), 0 < ε → ∃ c : ℤ →₀ ℂ, ∀ᶠ n in atTop,
        dist (ContinuousMap.toLp 2 μ ℂ (a i)) (c.sum (fun k b => b • w n k)) ≤ ε

def H2 : Prop :=
  let X := UnitAddCircle × UnitAddCircle × UnitAddCircle
  let m : Measure UnitAddCircle := AddCircle.haarAddCircle
  let μ : Measure X := m.prod (m.prod m)
  ∀ (A : ℕ → ℤ → C(X,X)) (p : ∀ n k, MeasurePreserving (A n k) μ μ) (v : ℕ → Lp ℂ 2 μ),
    (∀ n x, A n 0 x = x) → (∀ n (i j : ℤ) x, A n (i+j) x = A n i (A n j x)) → (∀ k, CauchySeq (fun n => A n k)) → CauchySeq v →
    ∃ (T : X ≃ᵐ X) (h : MeasurePreserving T μ μ) (f : Lp ℂ 2 μ), ∀ k : ℤ,
      Tendsto (fun n => Lp.compMeasurePreserving (A n k) (p n k) (v n)) atTop
        (𝓝 (match k with
          | .ofNat j => (Lp.compMeasurePreserving T h)^[j] f
          | .negSucc j => (Lp.compMeasurePreserving T.symm (h.symm T))^[j+1] f))

open OMA.S_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum
theorem main : H1 → H2 → OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1.H1 := by
  intro stage realize a ha
  obtain ⟨A,p,v,h0,hadd,hA,hv,hm,hz,ht⟩ := stage a ha
  obtain ⟨T,h,f,hL⟩ := realize A p v h0 hadd hA hv
  let w := fun n k => Lp.compMeasurePreserving (A n k) (p n k) (v n)
  have L (k : ℤ) : Tendsto (fun n => w n k) atTop (𝓝 (orbit T h f k)) := by
    cases k <;> apply hL
  let S := Submodule.span ℂ (Set.range (orbit T h f))
  refine ⟨T,h,f,orthonormal_iff_ite.mpr (fun i j => ?_),?_,fun i => ?_⟩
  · exact tendsto_nhds_unique ((L i).inner (𝕜 := ℂ) (L j)) (tendsto_const_nhds.congr' ((hm i j).mono (fun _ e => e.symm)))
  · apply S.topologicalClosure_minimal _ (Submodule.isClosed_orthogonal _)
    apply Submodule.span_le.mpr
    rintro _ ⟨k,rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    exact tendsto_nhds_unique (tendsto_const_nhds.inner (𝕜 := ℂ) (L k)) (tendsto_const_nhds.congr' ((hz k).mono (fun _ e => e.symm)))
  · apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨c,hc⟩ := ht i (ε/2) (half_pos hε)
    refine ⟨c.sum (fun k b => b • orbit T h f k), Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩)), ?_⟩
    have hc' := tendsto_finsetSum c.support (fun k _ => (L k).const_smul (c k))
    exact (le_of_tendsto (tendsto_const_nhds.dist hc') hc).trans_lt (half_lt_self hε)
end OMA.R_wp_banach_s_problem_is_there_an_ergodic_system_with_simple_lebesgue_spectrum_R1_H1_R1
