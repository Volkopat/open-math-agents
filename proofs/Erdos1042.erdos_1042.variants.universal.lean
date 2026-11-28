import FormalConjectures.ErdosProblems.«1042»
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Connected.Basic

section
-- CircleAverageBounds
open Metric Real Complex InnerProductSpace

namespace Erdos1042.TwoCircles

/-- Harnack bounds in terms of the displacement from the center. -/
theorem harmonic_ball_estimate {u : ℂ → ℝ} {c w : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (closedBall c R)) (hn : ∀ z ∈ sphere c R, 0 ≤ u z)
    (hw : dist w c < R) :
    ((R - dist w c) / (R + dist w c)) * u c ≤ u w ∧
      u w ≤ ((R + dist w c) / (R - dist w c)) * u c := by
  have hw' : w ∈ ball c R := mem_ball.mpr (by linarith)
  have huc : ContinuousOn u (sphere c R) := fun z hz ↦
    (hu z (sphere_subset_closedBall hz)).1.continuousAt.continuousWithinAt
  have hkernel : ContinuousOn (poissonKernel c w) (sphere c R) := by
    change ContinuousOn (fun z ↦ (‖z - c‖ ^ 2 - ‖w - c‖ ^ 2) /
      ‖z - c - (w - c)‖ ^ 2) (sphere c R)
    have hne : ∀ z ∈ sphere c R, ‖z - c - (w - c)‖ ^ 2 ≠ 0 := by
      intro z hz
      rw [sub_sub_sub_cancel_right]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (fun heq ↦ by
        subst z
        linarith [mem_sphere.mp hz, mem_ball.mp hw'])))
    exact ContinuousOn.div (by fun_prop) (by fun_prop) hne
  have hki : CircleIntegrable (fun z ↦ poissonKernel c w z * u z) c R :=
    (hkernel.mul huc).circleIntegrable hR.le
  have hui := huc.circleIntegrable hR.le
  have hmean : Real.circleAverage u c R = u c := by
    apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
    simpa [abs_of_pos hR] using hu
  have hpoisson : Real.circleAverage (fun z ↦ poissonKernel c w z * u z) c R = u w :=
    hu.circleAverage_poissonKernel_smul hw'
  have hl : ∀ z ∈ sphere c R, ((R - dist w c) / (R + dist w c)) ≤ poissonKernel c w z := by
    intro z hz
    rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
    simpa only [dist_eq_norm] using le_re_herglotzRieszKernel hz hw'
  have hh : ∀ z ∈ sphere c R, poissonKernel c w z ≤ ((R + dist w c) / (R - dist w c)) := by
    intro z hz
    rw [poissonKernel_eq_re_herglotzRieszKernel, Function.comp_apply, herglotzRieszKernel_def]
    simpa only [dist_eq_norm] using re_herglotzRieszKernel_le hz hw'
  constructor
  · have h := Real.circleAverage_mono (hui.const_smul (a := ((R - dist w c) / (R + dist w c)))) hki (fun z hz ↦ by
      rw [abs_of_pos hR] at hz
      exact mul_le_mul_of_nonneg_right (hl z hz) (hn z hz))
    rw [Real.circleAverage_smul, hmean, hpoisson] at h
    exact h
  · have h := Real.circleAverage_mono hki (hui.const_smul (a := ((R + dist w c) / (R - dist w c)))) (fun z hz ↦ by
      rw [abs_of_pos hR] at hz
      exact mul_le_mul_of_nonneg_right (hh z hz) (hn z hz))
    rw [Real.circleAverage_smul, hmean, hpoisson] at h
    exact h

theorem harmonic_variation {u : ℂ → ℝ} {w : ℂ} {R : ℝ} (hR : 0 < R)
    (hu : HarmonicOnNhd u (closedBall 0 R)) (hn : ∀ z ∈ closedBall (0 : ℂ) R, 0 ≤ u z)
    (hw : ‖w‖ ≤ R / 2) : |u w - u 0| ≤ (4 * ‖w‖ / R) * u 0 := by
  have h0 : 0 ≤ u 0 := hn 0 (by simp [hR.le])
  obtain ⟨hl, hh⟩ := harmonic_ball_estimate hR hu
    (fun z hz ↦ hn z (sphere_subset_closedBall hz)) (by rw [dist_zero_right]; linarith : dist w 0 < R)
  rw [dist_zero_right] at hl hh
  have hpos : 0 < R - ‖w‖ := by linarith
  have hh' : (R + ‖w‖) / (R - ‖w‖) ≤ 1 + 4 * ‖w‖ / R := by
    rw [div_le_iff₀ hpos, ← sub_nonneg]
    apply (mul_nonneg_iff_of_pos_left hR).mp
    have hh' := mul_nonneg (norm_nonneg w) (show 0 ≤ R - 2*‖w‖ by linarith)
    calc
      0 ≤ 2 * (‖w‖ * (R - 2*‖w‖)) := by positivity
      _ = R * ((1 + 4 * ‖w‖ / R) * (R - ‖w‖) - (R + ‖w‖)) := by field_simp; ring
  have hl' : 1 - 4 * ‖w‖ / R ≤ (R - ‖w‖) / (R + ‖w‖) := by
    rw [le_div_iff₀ (by positivity), ← sub_nonneg]
    apply (mul_nonneg_iff_of_pos_left hR).mp
    calc
      0 ≤ 2 * ‖w‖ * (R + 2 * ‖w‖) := by positivity
      _ = R * ((R - ‖w‖) - (1 - 4 * ‖w‖ / R) * (R + ‖w‖)) := by field_simp; ring
  rw [abs_le]
  constructor
  · have hx := (mul_le_mul_of_nonneg_right hl' h0).trans hl
    linarith
  · have hx := hh.trans (mul_le_mul_of_nonneg_right hh' h0)
    linarith

end Erdos1042.TwoCircles
end

section
-- CircleDiameter
open Metric Filter Finset
open scoped BigOperators ENNReal

namespace Erdos1042.TwoCircles

private theorem card_lt_pairs {n : ℕ} (s : Finset (Fin n)) :
    ((s ×ˢ s).filter (fun ij ↦ ij.1 < ij.2)).card = s.card.choose 2 := by
  classical
  have heq : s.offDiag = (s ×ˢ s).filter (fun ij ↦ ij.1 < ij.2) ∪
      (s ×ˢ s).filter (fun ij ↦ ij.2 < ij.1) := by
    ext ⟨i,j⟩
    simp only [mem_offDiag, mem_union, mem_filter, mem_product]
    rw [ne_iff_lt_or_gt]
    tauto
  have hd : Disjoint ((s ×ˢ s).filter (fun ij ↦ ij.1 < ij.2))
      ((s ×ˢ s).filter (fun ij ↦ ij.2 < ij.1)) := by
    exact Finset.disjoint_left.mpr fun _ hi hj ↦ (mem_filter.mp hi).2.not_gt (mem_filter.mp hj).2
  have hm : ((s ×ˢ s).filter (fun ij ↦ ij.1 < ij.2)).map (Equiv.prodComm _ _).toEmbedding =
      (s ×ˢ s).filter (fun ij ↦ ij.2 < ij.1) := by
    ext ⟨i,j⟩
    simp [and_comm]
  have ht := congrArg Finset.card hm
  rw [card_map] at ht
  have h := congrArg Finset.card heq
  rw [Nat.choose_two_right]
  rw [offDiag_card, card_union_of_disjoint hd, ← ht, ← two_mul, ← Nat.mul_sub_one] at h
  omega

private def pairSet (n : ℕ) : Finset (Fin n × Fin n) :=
  (univ ×ˢ univ).filter (fun ij ↦ ij.1 < ij.2)

private lemma mem_pairSet {n : ℕ} {p : Fin n × Fin n} : p ∈ pairSet n ↔ p.1 < p.2 := by
  simp [pairSet]

private lemma card_pairSet (n : ℕ) : (pairSet n).card = n.choose 2 := by
  rw [pairSet, card_lt_pairs, card_univ, Fintype.card_fin]

noncomputable def pairProduct {n : ℕ} (z : Fin n → ℂ) : ℝ≥0∞ :=
  ∏ ij ∈ pairSet n, edist (z ij.1) (z ij.2)

theorem pairProduct_eq {n : ℕ} (z : Fin n → ℂ) :
    pairProduct z = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, edist (z i) (z j) := by
  classical
  let e : (Σ _ : Fin n, Fin n) ↪ Fin n × Fin n :=
    ⟨fun p ↦ (p.1, p.2), fun p q hp ↦ by cases p; cases q; simpa using hp⟩
  have h : pairSet n = (univ.sigma (fun i : Fin n ↦ Ioi i)).map e := by
    ext ⟨i,j⟩
    rw [mem_pairSet, Finset.mem_map]
    constructor
    · intro hij
      exact ⟨⟨i,j⟩, by simp [hij], rfl⟩
    · rintro ⟨⟨a,b⟩, hab, he⟩
      change (a,b) = (i,j) at he
      cases he
      simpa using hab
  rw [pairProduct, h, prod_map, prod_sigma]
  rfl

theorem pairProduct_cons {n : ℕ} (w : ℂ) (z : Fin n → ℂ) :
    pairProduct (Fin.cons w z) = (∏ j, edist w (z j)) * pairProduct z := by
  classical
  rw [pairProduct_eq, Fin.prod_univ_succ, pairProduct_eq]
  have hm (i : Fin n) : Ioi (Fin.succ i) = (Ioi i).map (Fin.succEmb n) := by
    ext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp
    · simp
  have hm0 : Ioi (0 : Fin (n+1)) = univ.map (Fin.succEmb n) := by
    ext j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
  simp only [hm, hm0, prod_map, Fin.coe_succEmb, Fin.cons_zero, Fin.cons_succ]

theorem capacity_lower_of_greedy {F : Set ℂ} {D : ℝ≥0∞}
    (h : ∀ (n : ℕ) (z : Fin n → ℂ), (∀ i, z i ∈ F) →
      ∃ w ∈ F, D ^ n ≤ ∏ j, edist w (z j)) :
    D ≤ transfiniteDiameter F := by
  have hh (n : ℕ) : ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧ D ^ (n.choose 2) ≤ pairProduct z := by
    induction n with
    | zero => exact ⟨Fin.elim0, (fun i ↦ Fin.elim0 i), by simp [pairProduct, pairSet]⟩
    | succ n ih =>
      obtain ⟨z, hz, hprod⟩ := ih
      obtain ⟨w, hw, hmul⟩ := h n z hz
      refine ⟨Fin.cons w z, (fun i ↦ Fin.cases hw hz i), ?_⟩
      rw [pairProduct_cons, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]
      exact mul_le_mul' hmul hprod
  unfold transfiniteDiameter
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine le_iInf fun m ↦ ?_
  let n := max m 2
  obtain ⟨z, hz, hp⟩ := hh n
  have hc : (0 : ℝ) < (n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (le_max_right m 2)
  exact (calc
    D = (D ^ (n.choose 2)) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hc.ne', ENNReal.rpow_one]
    _ ≤ (pairProduct z) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) :=
      ENNReal.rpow_le_rpow hp (by positivity)
    _ ≤ nthDiameter F n := by
      rw [pairProduct_eq, nthDiameter]
      exact le_iSup_of_le z (le_iSup (fun _ : ∀ i, z i ∈ F ↦ _) hz)).trans
    (le_iSup_of_le n (le_iSup (fun _ : n ≥ m ↦ nthDiameter F n) (le_max_left m 2)))

theorem capacity_le_of_pair_bound {F : Set ℂ} {D : ℝ≥0∞}
    (h : ∀ n ≥ 4, ∀ z : Fin n → ℂ, (∀ i, z i ∈ F) → pairProduct z ≤ D ^ (n.choose 2)) :
    transfiniteDiameter F ≤ D := by
  unfold transfiniteDiameter
  rw [limsup_eq_iInf_iSup_of_nat]
  apply iInf_le_of_le 4
  refine iSup_le fun n ↦ iSup_le fun hn ↦ ?_
  unfold nthDiameter
  refine iSup_le fun z ↦ iSup_le fun hz ↦ ?_
  have hc : (0 : ℝ) < (n.choose 2 : ℕ) := by
    exact_mod_cast Nat.choose_pos (show 2 ≤ n by omega)
  rw [← pairProduct_eq]
  calc
    _ ≤ (D ^ (n.choose 2)) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) :=
      ENNReal.rpow_le_rpow (h n hn z hz) (by positivity)
    _ = D := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, mul_one_div_cancel hc.ne', ENNReal.rpow_one]

theorem pair_bound_of_two_sets {F A B : Set ℂ} (hF : F ⊆ A ∪ B) {D : ℝ≥0∞}
    (hD : ∀ x ∈ F, ∀ y ∈ F, edist x y ≤ 4 * D)
    (hA : ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ (1/4096 : ℝ≥0∞) * D)
    (hB : ∀ x ∈ B, ∀ y ∈ B, edist x y ≤ (1/4096 : ℝ≥0∞) * D)
    {n : ℕ} (hn : 4 ≤ n) (z : Fin n → ℂ)
    (hz : ∀ i, z i ∈ F) : pairProduct z ≤ D ^ (n.choose 2) := by
  classical
  let s := univ.filter (fun i ↦ z i ∈ A)
  let u : Finset (Fin n × Fin n) := (pairSet n).filter fun ij ↦ ij.1 ∈ s ↔ ij.2 ∈ s
  have hu : u ⊆ pairSet n := filter_subset _ _
  have hcounts : u.card = s.card.choose 2 + (n - s.card).choose 2 := by
    let p : Finset (Fin n × Fin n) := (s ×ˢ s).filter (fun ij ↦ ij.1 < ij.2)
    let q : Finset (Fin n × Fin n) := (sᶜ ×ˢ sᶜ).filter (fun ij ↦ ij.1 < ij.2)
    have he : u = p ∪ q := by
      ext ⟨i,j⟩
      simp only [u, p, q, mem_filter, mem_pairSet, mem_union, mem_product, mem_compl]
      tauto
    have hd : Disjoint p q := by
      refine Finset.disjoint_left.mpr fun x hp hq ↦ ?_
      exact (mem_compl.mp (mem_product.mp (mem_filter.mp hq).1).1)
        (mem_product.mp (mem_filter.mp hp).1).1
    rw [he, card_union_of_disjoint hd]
    dsimp only [p, q]
    rw [card_lt_pairs, card_lt_pairs, card_compl, Fintype.card_fin]
  have hlarge : n.choose 2 ≤ 5 * u.card := by
    rw [hcounts]
    have hs : s.card ≤ n := by simpa using card_le_univ s
    have hnum : (n.choose 2 : ℝ) ≤ 5 * ((s.card.choose 2 : ℝ) + ((n - s.card).choose 2 : ℝ)) := by
      rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_sub hs]
      have hnr : (4 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 2 * s.card), mul_nonneg (sub_nonneg.mpr hnr) (show (0 : ℝ) ≤ n by positivity)]
    exact_mod_cast hnum
  have hp (ij : Fin n × Fin n) (hij : ij ∈ pairSet n) :
      edist (z ij.1) (z ij.2) ≤ (if ij ∈ u then (1/4096 : ℝ≥0∞) else 4) * D := by
    split_ifs with hh
    · have hh' := (mem_filter.mp hh).2
      by_cases ha : z ij.1 ∈ A
      · exact hA _ ha _ (by simpa [s] using hh'.mp (by simp [s, ha]))
      · refine hB _ ((hF (hz _)).resolve_left ha) _ ((hF (hz _)).resolve_left ?_)
        simpa [s] using mt hh'.mpr (show ij.1 ∉ s by simp [s, ha])
    · exact hD _ (hz _) _ (hz _)
  unfold pairProduct
  refine (Finset.prod_le_prod' hp).trans ?_
  rw [Finset.prod_mul_distrib, prod_const, card_pairSet]
  suffices hh : (∏ ij ∈ pairSet n, if ij ∈ u then (1/4096 : ℝ≥0∞) else 4) ≤ 1 by
    simpa only [one_mul] using mul_le_mul' hh (le_refl (D ^ (n.choose 2)))
  rw [← prod_sdiff hu]
  have h₁ : (∏ x ∈ pairSet n \ u, if x ∈ u then (1 / 4096 : ℝ≥0∞) else 4) =
      (4 : ℝ≥0∞) ^ (n.choose 2 - u.card) := by
    rw [← card_pairSet n, ← card_sdiff_of_subset hu, ← prod_const]
    exact prod_congr rfl (fun x hx ↦ if_neg (mem_sdiff.mp hx).2)
  have h₂ : (∏ x ∈ u, if x ∈ u then (1 / 4096 : ℝ≥0∞) else 4) =
      (1 / 4096 : ℝ≥0∞) ^ u.card := by
    rw [← prod_const]
    exact prod_congr rfl (fun x hx ↦ if_pos hx)
  rw [h₁, h₂]
  have hc : n.choose 2 - u.card ≤ 6 * u.card := by omega
  have hpow : (4 : ℝ≥0∞) ^ (n.choose 2 - u.card) ≤ (4 : ℝ≥0∞) ^ (6 * u.card) :=
    pow_le_pow_right' (by norm_num) hc
  refine (mul_le_mul' hpow le_rfl).trans_eq ?_
  rw [pow_mul, ← mul_pow, show (4 : ℝ≥0∞) ^ (6 : ℕ) * (1 / 4096) = 1 by
    norm_num
    exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]

theorem diameter_scale {F : Set ℂ} {t : ℝ} (ht : 0 < t) :
    transfiniteDiameter ((fun z : ℂ ↦ (t : ℂ) * z) '' F) =
      ENNReal.ofReal t * transfiniteDiameter F := by
  classical
  let T := ENNReal.ofReal t
  let G := (fun z : ℂ ↦ (t : ℂ) * z) '' F
  have hT0 : T ≠ 0 := (ENNReal.ofReal_pos.mpr ht).ne'
  have hTtop : T ≠ ⊤ := ENNReal.ofReal_ne_top
  have hp (n : ℕ) (z : Fin n → ℂ) :
      pairProduct (fun i ↦ (t : ℂ) * z i) = T ^ (n.choose 2) * pairProduct z := by
    have he (x y : ℂ) : edist ((t : ℂ) * x) ((t : ℂ) * y) = T * edist x y := by
      simp only [edist_dist, dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ht.le, T, ENNReal.ofReal_mul ht.le]
    simp only [pairProduct, he, Finset.prod_mul_distrib, prod_const, card_pairSet]
  have hnd (n : ℕ) (hn : 2 ≤ n) : nthDiameter G n = T * nthDiameter F n := by
    have hpow : (0 : ℝ) < (n.choose 2 : ℕ) := by exact_mod_cast Nat.choose_pos hn
    have he (z : Fin n → ℂ) :
        pairProduct (fun i ↦ (t : ℂ) * z i) ^ (1 / ((n.choose 2 : ℕ) : ℝ)) =
          T * pairProduct z ^ (1 / ((n.choose 2 : ℕ) : ℝ)) := by
      rw [hp, ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_natCast T,
        ← ENNReal.rpow_mul, mul_one_div_cancel hpow.ne', ENNReal.rpow_one]
    simp only [nthDiameter, ← pairProduct_eq, ENNReal.mul_iSup]
    apply le_antisymm
    · refine iSup_le fun w ↦ iSup_le fun hw ↦ ?_
      choose z hz hzw using hw
      have hw' : w = fun i ↦ (t : ℂ) * z i := funext fun i ↦ (hzw i).symm
      rw [hw', he]
      exact le_iSup_of_le z (le_iSup (fun _ : ∀ i, z i ∈ F ↦ _) hz)
    · refine iSup_le fun z ↦ iSup_le fun hz ↦ ?_
      rw [← he]
      exact le_iSup_of_le (fun i ↦ (t : ℂ) * z i)
        (le_iSup (fun _ : ∀ i, (t : ℂ) * z i ∈ G ↦ _) (fun i ↦ ⟨z i, hz i, rfl⟩))
  have hev : nthDiameter G =ᶠ[atTop] fun n ↦ T * nthDiameter F n :=
    (eventually_ge_atTop 2).mono fun n hn ↦ hnd n hn
  change transfiniteDiameter G = T * transfiniteDiameter F
  unfold transfiniteDiameter
  rw [Filter.limsup_congr hev]
  simp only [limsup_eq_iInf_iSup_of_nat, ENNReal.mul_iInf_of_ne hT0 hTtop, ENNReal.mul_iSup]

end Erdos1042.TwoCircles
end

section
-- CircleComponents
open Set Metric Polynomial Filter
open scoped BigOperators Topology

namespace Erdos1042.TwoCircles

noncomputable def rootProduct {n : ℕ} (a : Fin n → ℂ) (c : ℂ) : ℂ[X] :=
  C c * ∏ i, (X - C (a i))

theorem rootProduct_eval {n : ℕ} (a : Fin n → ℂ) (c z : ℂ) :
    (rootProduct a c).eval z = c * ∏ i, (z - a i) := by
  simp [rootProduct, eval_prod]

theorem rootProduct_degree {n : ℕ} (a : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    (rootProduct a c).natDegree = n := by
  simp [rootProduct, natDegree_C_mul hc]

theorem rootProduct_zero_iff {n : ℕ} (a : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0) (z : ℂ) :
    (rootProduct a c).eval z = 0 ↔ ∃ i, a i = z := by
  simp only [rootProduct_eval, mul_eq_zero, hc, false_or, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero]
  exact exists_congr (fun _ ↦ eq_comm)

theorem norm_not_local_min {p : ℂ[X]} (hp : p.natDegree ≠ 0) {z : ℂ}
    (hz : p.eval z ≠ 0) : ¬ IsLocalMin (fun w ↦ ‖p.eval w‖) z := by
  intro hm
  obtain ⟨V, hV, hVo, hzV⟩ := _root_.mem_nhds_iff.mp hm
  have ho : IsOpen (p.eval '' V) := (p.isOpenQuotientMap_eval hp).isOpenMap V hVo
  have hz' : p.eval z ∈ p.eval '' V := ⟨z, hzV, rfl⟩
  have ht : Tendsto (fun t : ℝ ↦ (t : ℂ) * p.eval z) (𝓝[<] 1) (𝓝 (p.eval z)) := by
    have h : Continuous (fun t : ℝ ↦ (t : ℂ) * p.eval z) := by fun_prop
    simpa using (h.continuousAt (x := (1 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have he := ht.eventually (ho.mem_nhds hz')
  have h01 : ∀ᶠ t : ℝ in 𝓝[<] 1, t ∈ Ioo 0 1 := Ioo_mem_nhdsLT (by norm_num)
  obtain ⟨t, ht₁, w, hw, heq⟩ := (h01.and he).exists
  have hmin := hV hw
  change ‖p.eval z‖ ≤ ‖p.eval w‖ at hmin
  change p.eval w = (t : ℂ) * p.eval z at heq
  rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht₁.1.le] at hmin
  nlinarith [norm_pos_iff.mpr hz, ht₁.2]

theorem sublevel_open (p : ℂ[X]) : IsOpen (Erdos1047.strictSublevelSet p 1) := by
  exact isOpen_lt (p.continuous.norm) continuous_const

theorem component_closure_inside {S : Set ℂ} (hS : IsOpen S) {z y : ℂ}
    (hy : y ∈ closure (connectedComponentIn S z)) (hyS : y ∈ S) :
    y ∈ connectedComponentIn S z := by
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.mp hS y hyS
  obtain ⟨w, hw, hw'⟩ := Metric.mem_closure_iff.mp hy r hr
  have hwb : w ∈ ball y r := mem_ball.mpr (by rwa [dist_comm])
  have he := (convex_ball y r).isPreconnected.subset_connectedComponentIn hwb hb
  rw [connectedComponentIn_eq hw]
  exact he (mem_ball_self hr)

theorem rootProduct_bounded {n : ℕ} (a : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0)
    (hn : n ≠ 0) : Bornology.IsBounded (Erdos1047.strictSublevelSet (rootProduct a c) 1) := by
  classical
  let M : ℝ := ∑ i, ‖a i‖
  have hMa (i : Fin n) : ‖a i‖ ≤ M :=
    Finset.single_le_sum (f := fun j ↦ ‖a j‖) (fun j _ ↦ norm_nonneg (a j)) (Finset.mem_univ i)
  let R := max (‖c‖⁻¹) 1
  have hR : 1 ≤ R := le_max_right _ _
  apply (isBounded_closedBall (x := (0 : ℂ)) (r := M + R)).subset
  intro z hz
  rw [mem_closedBall_zero_iff]
  by_contra! h
  have hf (i : Fin n) : R ≤ ‖z - a i‖ := by
    have hh := norm_add_le (z - a i) (a i)
    rw [sub_add_cancel] at hh
    linarith [hMa i]
  have hf' : R ≤ ∏ i, ‖z - a i‖ := by
    calc
      R = R ^ (1 : ℕ) := (pow_one _).symm
      _ ≤ R ^ n := pow_le_pow_right₀ hR (by omega)
      _ ≤ ∏ i, ‖z - a i‖ := by
        simpa using Finset.prod_le_prod (s := Finset.univ) (f := fun _ ↦ R)
          (fun _ _ ↦ zero_le_one.trans hR) (fun i _ ↦ hf i)
  change ‖(rootProduct a c).eval z‖ < 1 at hz
  rw [rootProduct_eval, norm_mul, norm_prod] at hz
  have hpos := norm_pos_iff.mpr hc
  have hv : ‖c‖⁻¹ ≤ ∏ i, ‖z - a i‖ := (le_max_left _ _).trans hf'
  have := (inv_le_iff_one_le_mul₀ hpos).mp hv
  linarith

theorem rootProduct_component_root {n : ℕ} {a : Fin n → ℂ} {c : ℂ} (hc : c ≠ 0)
    (hn : n ≠ 0) {z : ℂ} (hz : z ∈ Erdos1047.strictSublevelSet (rootProduct a c) 1) :
    ∃ i, a i ∈ connectedComponentIn (Erdos1047.strictSublevelSet (rootProduct a c) 1) z := by
  let p := rootProduct a c
  let S := Erdos1047.strictSublevelSet p 1
  let U := connectedComponentIn S z
  have hzU : z ∈ U := mem_connectedComponentIn hz
  have hK : IsCompact (closure U) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,
      ((rootProduct_bounded a hc hn).subset (connectedComponentIn_subset _ _)).closure⟩
  obtain ⟨w, hw, hm⟩ := hK.exists_isMinOn ⟨z, subset_closure hzU⟩ p.continuous.norm.continuousOn
  have hwS : w ∈ S := by
    change ‖p.eval w‖ < 1
    exact lt_of_le_of_lt (hm (subset_closure hzU)) hz
  have hwU : w ∈ U := component_closure_inside (sublevel_open p) hw hwS
  have hmin : IsLocalMin (fun w ↦ ‖p.eval w‖) w :=
    hm.localize.isLocalMin
      (mem_of_superset ((sublevel_open p).connectedComponentIn.mem_nhds hwU) subset_closure)
  have h0 : p.eval w = 0 := by
    by_contra hne
    exact norm_not_local_min (by simpa [p, rootProduct_degree a hc] using hn) hne hmin
  obtain ⟨i, rfl⟩ := (rootProduct_zero_iff a hc w).mp h0
  exact ⟨i, hwU⟩

theorem rootProduct_component_range {n : ℕ} {a : Fin n → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hn : n ≠ 0) :
    Erdos1047.componentsIn (Erdos1047.strictSublevelSet (rootProduct a c) 1) =
      range (fun i ↦ connectedComponentIn (Erdos1047.strictSublevelSet (rootProduct a c) 1) (a i)) := by
  ext U
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨i, hi⟩ := rootProduct_component_root hc hn hz
    exact ⟨i, (connectedComponentIn_eq hi).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨a i, ?_, rfl⟩
    change ‖(rootProduct a c).eval (a i)‖ < 1
    simp [(rootProduct_zero_iff a hc (a i)).mpr ⟨i, rfl⟩]

theorem distinct_component_of_full {n : ℕ} {a : Fin n → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hn : n ≠ 0) (hfull : numComponents (rootProduct a c) = n) :
    Function.Injective (fun i ↦
      connectedComponentIn (Erdos1047.strictSublevelSet (rootProduct a c) 1) (a i)) := by
  have hh := hfull
  rw [numComponents, rootProduct_component_range hc hn, ← image_univ] at hh
  have hi := Set.injOn_of_ncard_image_eq (hh.trans (by simp))
  exact injOn_univ.mp hi

theorem full_component_unique {n : ℕ} {a : Fin n → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hn : n ≠ 0) (hfull : numComponents (rootProduct a c) = n)
    {z : ℂ} (hz : z ∈ Erdos1047.strictSublevelSet (rootProduct a c) 1) :
    ∃ i, ∀ j, a j ∈ connectedComponentIn (Erdos1047.strictSublevelSet (rootProduct a c) 1) z ↔ j = i := by
  obtain ⟨i, hi⟩ := rootProduct_component_root hc hn hz
  refine ⟨i, fun j ↦ ⟨fun hj ↦ ?_, by rintro rfl; exact hi⟩⟩
  exact distinct_component_of_full hc hn hfull ((connectedComponentIn_eq hj).symm.trans
    (connectedComponentIn_eq hi))

theorem monic_rootProduct_repr {p : ℂ[X]} {n : ℕ} (hp : p.Monic) (hd : p.natDegree = n) :
    ∃ a : Fin n → ℂ, p = rootProduct a 1 ∧ ∀ i, a i ∈ p.roots := by
  classical
  let l := p.roots.toList
  have hlen : l.length = n := by
    rw [Multiset.length_toList, ← (IsAlgClosed.splits p).natDegree_eq_card_roots, hd]
  let a : Fin n → ℂ := fun i ↦ l[Fin.cast hlen.symm i]
  have ha : ∀ i, a i ∈ p.roots := fun i ↦ by
    rw [← Multiset.mem_toList]
    exact List.get_mem _ _
  refine ⟨a, ?_, ha⟩
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
  simp only [rootProduct, map_one, one_mul]
  have h1 : (p.roots.map (fun x ↦ X - C x)).prod =
      (l.map (fun x ↦ X - C x)).prod := by simp [l]
  rw [h1, ← Fin.prod_univ_fun_getElem, ← (Fin.castOrderIso hlen.symm).toEquiv.prod_comp]
  rfl

end Erdos1042.TwoCircles
end

section
-- CircleModel
open Metric Set Filter
open scoped BigOperators ENNReal ComplexConjugate

namespace Erdos1042.TwoCircles

noncomputable def mapA (t : ℝ) (w : ℂ) : ℂ := (t : ℂ) / (1 - w)
noncomputable def mapB (t : ℝ) (w : ℂ) : ℂ := (t : ℂ) - mapA t w

noncomputable def circlePair (t r s : ℝ) : Set ℂ :=
  mapA t '' sphere 0 r ∪ mapB t '' sphere 0 s

noncomputable def circleCenter (t r : ℝ) : ℂ := ((t / (1-r^2) : ℝ) : ℂ)
noncomputable def circleRadius (t r : ℝ) : ℝ := t / (1-r^2) * r

theorem den_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < ‖1-w‖ := by
  apply norm_pos_iff.mpr
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simp [he] at hw

theorem norm_one_sub_ge (w : ℂ) : 1 - ‖w‖ ≤ ‖1-w‖ := by
  have h := norm_add_le (1-w) w
  simpa only [sub_add_cancel, norm_one, sub_le_iff_le_add] using h

theorem mapA_analytic (t : ℝ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (mapA t) w := by
  unfold mapA
  fun_prop (disch := exact norm_ne_zero_iff.mp (den_pos hw).ne')

theorem mapB_analytic (t : ℝ) {w : ℂ} (hw : ‖w‖ < 1) : AnalyticAt ℂ (mapB t) w := by
  unfold mapB
  exact analyticAt_const.sub (mapA_analytic t hw)

theorem circlePair_compact (t : ℝ) {r s : ℝ} (hr : r < 1) (hs : s < 1) :
    IsCompact (circlePair t r s) := by
  apply IsCompact.union
  · exact (isCompact_sphere 0 r).image_of_continuousOn (fun w hw ↦
      (mapA_analytic t ((mem_sphere_zero_iff_norm.mp hw).trans_lt hr)).continuousAt.continuousWithinAt)
  · exact (isCompact_sphere 0 s).image_of_continuousOn (fun w hw ↦
      (mapB_analytic t ((mem_sphere_zero_iff_norm.mp hw).trans_lt hs)).continuousAt.continuousWithinAt)

theorem circlePair_scale {t r s : ℝ} :
    circlePair t r s = (fun z : ℂ ↦ (t : ℂ) * z) '' circlePair 1 r s := by
  unfold circlePair
  rw [image_union, image_image, image_image]
  congr 2 <;> funext w <;> simp [mapA,mapB,div_eq_mul_inv,mul_sub]

theorem dist_mapA_center {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r < 1) {w : ℂ}
    (hw : ‖w‖ < 1) : ‖mapA t w - circleCenter t r‖ =
      (t / (1-r^2)) * (‖w - (r^2 : ℝ)‖ / ‖1-w‖) := by
  have hd : 0 < 1-r^2 := by nlinarith
  have hdc : (1 : ℂ) - (r : ℂ)^2 ≠ 0 := by exact_mod_cast hd.ne'
  have h1 := norm_ne_zero_iff.mp (den_pos hw).ne'
  have he : mapA t w - circleCenter t r = (circleCenter t r) * ((w - (r^2 : ℝ)) / (1-w)) := by
    unfold mapA circleCenter
    push_cast
    field_simp
    ring
  rw [he, norm_mul, norm_div, circleCenter, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem mapA_boundary {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r < 1) {w : ℂ}
    (hw : ‖w‖ = r) : ‖mapA t w - circleCenter t r‖ = circleRadius t r := by
  have hn : ‖w - (r^2 : ℝ)‖ = r * ‖1-w‖ := by
    have h : w - (r^2 : ℝ) = w * (1 - conj w) := by
      rw [mul_sub, mul_one, Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]
    rw [h, norm_mul, hw]
    congr 1
    rw [← Complex.norm_conj (1-w)]
    simp
  rw [dist_mapA_center ht hr hr' (hw.trans_lt hr'), hn, mul_div_cancel_right₀ _ (den_pos (hw.trans_lt hr')).ne', circleRadius]

theorem mapB_boundary {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r < 1) {w : ℂ}
    (hw : ‖w‖ = r) : ‖mapB t w - ((t : ℂ) - circleCenter t r)‖ = circleRadius t r := by
  rw [mapB, sub_sub_sub_cancel_left, norm_sub_rev]
  exact mapA_boundary ht hr hr' hw

theorem mapA_core {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r ≤ 1/100) {w : ℂ}
    (hw : ‖w‖ ≤ r/2) : ‖mapA t w - circleCenter t r‖ ≤ (3/4) * circleRadius t r := by
  have hw' : ‖w‖ < 1 := by linarith
  rw [dist_mapA_center ht hr (by linarith) hw', circleRadius, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (div_nonneg ht.le (show 0 ≤ 1-r^2 by nlinarith))
  rw [div_le_iff₀ (den_pos hw')]
  have he : ‖w - (r^2 : ℝ)‖ ≤ r/2+r^2 := by
    have h := norm_sub_le w ((r^2 : ℝ) : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h
    linarith
  have hden : 1-r/2 ≤ ‖1-w‖ := by linarith [norm_one_sub_ge w]
  have h₁ := mul_le_mul_of_nonneg_left hden (show 0 ≤ (3/4 : ℝ)*r by positivity)
  nlinarith [mul_nonneg hr.le (show 0 ≤ 1/100-r by linarith)]

theorem mapB_core {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r ≤ 1/100) {w : ℂ}
    (hw : ‖w‖ ≤ r/2) : ‖mapB t w - ((t : ℂ) - circleCenter t r)‖ ≤ (3/4) * circleRadius t r := by
  rw [mapB, sub_sub_sub_cancel_left, norm_sub_rev]
  exact mapA_core ht hr hr' hw

theorem radius_pos {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r ≤ 1/100) :
    0 < circleRadius t r := by
  unfold circleRadius
  have hd : 0 < 1-r^2 := by nlinarith
  positivity

theorem radius_le {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r ≤ 1/100) :
    circleRadius t r ≤ 2*t*r := by
  unfold circleRadius
  gcongr
  rw [div_le_iff₀ (by nlinarith : 0 < 1-r^2)]
  have h₁ : (1/2 : ℝ) ≤ 1-r^2 := by nlinarith
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr h₁)]

theorem mapA_close {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖mapA t w - (t : ℂ)‖ ≤ 2*t*‖w‖ := by
  have h' : ‖w‖ < 1 := by linarith
  have hd := norm_ne_zero_iff.mp (den_pos h').ne'
  have he : mapA t w - (t : ℂ) = (t : ℂ) * w / (1-w) := by unfold mapA; field_simp; ring
  rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, div_le_iff₀ (den_pos h')]
  have h₁ : (1/2 : ℝ) ≤ ‖1-w‖ := by linarith [norm_one_sub_ge w]
  nlinarith [mul_nonneg (show 0 ≤ t*‖w‖ by positivity) (sub_nonneg.mpr h₁)]

theorem mapB_close {t : ℝ} (ht : 0 < t) {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖mapB t w‖ ≤ 2*t*‖w‖ := by
  rw [mapB, norm_sub_rev]
  exact mapA_close ht hw

theorem center_close {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (hr' : r ≤ 1/100) :
    ‖circleCenter t r - (t : ℂ)‖ ≤ circleRadius t r := by
  have hd : 0 < 1-r^2 := by nlinarith
  rw [circleCenter, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, circleRadius]
  have he : t / (1-r^2) - t = (t/(1-r^2))*r^2 := by field_simp; ring
  rw [he, abs_of_nonneg (by positivity)]
  gcongr
  nlinarith

theorem foreign_far_A {t r s : ℝ} (ht : 0 < t)
    (hr : 0 < r) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    {w : ℂ} (hw : ‖w‖ = s) : 1001 * circleRadius t r ≤ ‖mapB t w - circleCenter t r‖ := by
  have hR := radius_le ht hr (by linarith)
  have hc := (center_close ht hr (by linarith)).trans hR
  have hb := mapB_close ht (w := w) (by rw [hw]; linarith)
  rw [hw] at hb
  have ht' : ‖(t : ℂ)‖ = t := by simp [Complex.norm_real, abs_of_pos ht]
  have h := norm_add_le ((t : ℂ) - circleCenter t r) (circleCenter t r)
  rw [sub_add_cancel, ht', norm_sub_rev (t : ℂ)] at h
  have h' := norm_add_le (circleCenter t r - mapB t w) (mapB t w)
  rw [sub_add_cancel, norm_sub_rev (circleCenter t r)] at h'
  have hr₂ := mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ 2*t)
  have hs₂ := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ 2*t)
  linarith

theorem foreign_far_B {t r s : ℝ} (ht : 0 < t)
    (hs : 0 < s) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    {w : ℂ} (hw : ‖w‖ = r) :
    1001 * circleRadius t s ≤ ‖mapA t w - ((t : ℂ) - circleCenter t s)‖ := by
  have he : mapA t w - ((t : ℂ) - circleCenter t s) = -(mapB t w - circleCenter t s) := by
    unfold mapB
    ring
  rw [he, norm_neg]
  exact foreign_far_A ht hs hs' hr' hw

theorem mapA_sub_mapA_norm {t : ℝ} (ht : 0 < t) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖mapA t z - mapA t w‖ = t * ‖z-w‖ / (‖1-z‖ * ‖1-w‖) := by
  have h1 := norm_ne_zero_iff.mp (den_pos hz).ne'
  have h2 := norm_ne_zero_iff.mp (den_pos hw).ne'
  have he : mapA t z - mapA t w = (t : ℂ) * (z-w) / ((1-z)*(1-w)) := by
    unfold mapA
    field_simp
    ring
  rw [he,norm_div,norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg ht.le]

theorem mapB_sub_mapA_norm {t : ℝ} (ht : 0 < t) {z w : ℂ} (hz : ‖z‖ < 1) (hw : ‖w‖ < 1) :
    ‖mapB t z - mapA t w‖ = t * ‖1-z*w‖ / (‖1-z‖ * ‖1-w‖) := by
  have h1 := norm_ne_zero_iff.mp (den_pos hz).ne'
  have h2 := norm_ne_zero_iff.mp (den_pos hw).ne'
  have he : mapB t z - mapA t w = -(t : ℂ) * (1-z*w) / ((1-z)*(1-w)) := by
    unfold mapB mapA
    field_simp
    ring
  rw [he,norm_div,norm_mul,norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg ht.le]

theorem circlePair_upper {t r s : ℝ} (ht : 0 < t) (hr : 0 < r) (_hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000) :
    transfiniteDiameter (circlePair t r s) ≤ ENNReal.ofReal (t/2) := by
  let A := mapA t '' sphere (0 : ℂ) r
  let B := mapB t '' sphere (0 : ℂ) s
  have hA (x : ℂ) (hx : x ∈ A) : dist x (t : ℂ) ≤ 2*t*r := by
    rcases hx with ⟨w,hw,rfl⟩
    rw [mem_sphere_zero_iff_norm] at hw
    simpa only [dist_eq_norm, hw] using mapA_close ht (by rw [hw]; linarith : ‖w‖ ≤ 1/2)
  have hB (x : ℂ) (hx : x ∈ B) : dist x 0 ≤ 2*t*s := by
    rcases hx with ⟨w,hw,rfl⟩
    rw [mem_sphere_zero_iff_norm] at hw
    simpa only [dist_zero_right, hw] using mapB_close ht (by rw [hw]; linarith : ‖w‖ ≤ 1/2)
  have ht0 : dist (t : ℂ) 0 = t := by simp [Complex.norm_real, Real.norm_of_nonneg ht.le]
  have ha' : 2*t*r ≤ t/16384 := by nlinarith [mul_le_mul_of_nonneg_left hr' ht.le]
  have hb' : 2*t*s ≤ t/16384 := by nlinarith [mul_le_mul_of_nonneg_left hs' ht.le]
  have hab (x y : ℂ) (hx : x ∈ A) (hy : y ∈ B) : dist x y ≤ 2*t := by
    have h := dist_triangle4 x (t : ℂ) 0 y
    rw [ht0, dist_comm 0 y] at h
    linarith [hA x hx,hB y hy]
  have ha (x y : ℂ) (hx : x ∈ A) (hy : y ∈ A) : dist x y ≤ t/8192 := by
    have h := dist_triangle x (t : ℂ) y
    rw [dist_comm (t : ℂ) y] at h
    linarith [hA x hx,hA y hy]
  have hb (x y : ℂ) (hx : x ∈ B) (hy : y ∈ B) : dist x y ≤ t/8192 := by
    have h := dist_triangle x 0 y
    rw [dist_comm 0 y] at h
    linarith [hB x hx,hB y hy]
  apply capacity_le_of_pair_bound
  intro n hn z hz
  apply pair_bound_of_two_sets (F := circlePair t r s) (A := A) (B := B) (fun _ hx ↦ hx) ?_ ?_ ?_ hn z hz
  · intro x hx y hy
    have hh : dist x y ≤ 2*t := by
      rcases hx with hx|hx <;> rcases hy with hy|hy
      · linarith [ha x y hx hy]
      · exact hab x y hx hy
      · rw [dist_comm]; exact hab y x hy hx
      · linarith [hb x y hx hy]
    rw [edist_dist, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · intro x hx y hy
    rw [edist_dist, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4096), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith [ha x y hx hy])
  · intro x hx y hy
    rw [edist_dist, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<4096), ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith [hb x y hx hy])

theorem circlePair_not_ball {t r s : ℝ} (ht : 2 ≤ t) (hr : 0 < r) (hs : 0 < s)
    (hr' : r < 1) (hs' : s < 1) (c : ℂ) : ¬ circlePair t r s ⊆ closedBall c 1 := by
  intro h
  have ha : (r : ℂ) ∈ sphere (0 : ℂ) r := by simp [Complex.norm_real, Real.norm_of_nonneg hr.le]
  have hb : (s : ℂ) ∈ sphere (0 : ℂ) s := by simp [Complex.norm_real, Real.norm_of_nonneg hs.le]
  have ha' := mem_closedBall.mp (h (Or.inl ⟨(r : ℂ), ha, rfl⟩ : mapA t (r : ℂ) ∈ circlePair t r s))
  have hb' := mem_closedBall.mp (h (Or.inr ⟨(s : ℂ), hb, rfl⟩ : mapB t (s : ℂ) ∈ circlePair t r s))
  have hfar : 2 < dist (mapA t (r : ℂ)) (mapB t (s : ℂ)) := by
    have h1 : t < t / (1-r) := by
      apply (lt_div_iff₀ (by linarith : 0 < 1-r)).mpr
      nlinarith [mul_pos (show 0 < t by linarith) hr]
    have h2 : t < t / (1-s) := by
      apply (lt_div_iff₀ (by linarith : 0 < 1-s)).mpr
      nlinarith [mul_pos (show 0 < t by linarith) hs]
    have he : mapA t (r : ℂ) - mapB t (s : ℂ) = ((t/(1-r) - (t-t/(1-s)) : ℝ) : ℂ) := by
      simp [mapA,mapB]
    rw [dist_eq_norm, he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hh := dist_triangle (mapA t (r : ℂ)) c (mapB t (s : ℂ))
  rw [dist_comm c] at hh
  linarith

end Erdos1042.TwoCircles
end

section
-- CircleObstruction
open Metric Set Polynomial Filter
open scoped BigOperators Topology ComplexConjugate

namespace Erdos1042.TwoCircles

theorem log_rootProduct {n : ℕ} (a : Fin n → ℂ) {c x : ℂ} (hc : c ≠ 0)
    (hx : ∀ i, x ≠ a i) :
    Real.log ‖(rootProduct a c).eval x‖ = Real.log ‖c‖ + ∑ i, Real.log ‖x - a i‖ := by
  rw [rootProduct_eval, norm_mul, norm_prod,
    Real.log_mul (norm_ne_zero_iff.mpr hc), Real.log_prod]
  · exact fun i _ ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx i))
  · exact Finset.prod_ne_zero_iff.mpr (fun i _ ↦ norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hx i)))

private def inward (x : ℂ) (t : ℝ) : ℂ := ((1-t : ℝ) : ℂ) * x

private theorem inward_dist {x : ℂ} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 ≤ t) :
    ‖inward x t - x‖ = t := by
  have he : inward x t - x = -(t : ℂ) * x := by unfold inward; push_cast; ring
  rw [he, norm_mul, norm_neg, hx, mul_one, Complex.norm_real, Real.norm_of_nonneg ht]

private theorem log_inward_general {x a : ℂ} (hx : ‖x‖ = 1) {t : ℝ} (ht : 0 ≤ t)
    (ha : x ≠ a) (hb : inward x t ≠ a) :
    Real.log ‖inward x t - a‖ - Real.log ‖x - a‖ ≤ t / ‖x-a‖ := by
  have hp : 0 < ‖x-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr ha)
  have hp' : 0 < ‖inward x t-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hb)
  rw [← Real.log_div hp'.ne' hp.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hp' hp)).trans ?_
  have hh := norm_add_le (inward x t - x) (x-a)
  rw [sub_add_sub_cancel, inward_dist hx ht] at hh
  rw [sub_le_iff_le_add, ← div_self hp.ne', ← add_div, div_le_div_iff_of_pos_right hp]
  exact hh

private theorem log_inward_circle {x a : ℂ} (hx : ‖x‖ = 1) (ha : ‖a‖ = 1) {t : ℝ}
    (ht : 0 ≤ t) (hsmall : t ≤ ‖x-a‖ ^ 2 / 2) (hna : x ≠ a) (hnb : inward x t ≠ a) :
    Real.log ‖inward x t - a‖ - Real.log ‖x-a‖ ≤ -t/4 := by
  have hp : 0 < ‖x-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hna)
  have hp' : 0 < ‖inward x t-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hnb)
  have hs : ‖inward x t - a‖ ^ 2 = (1-t)*‖x-a‖^2+t^2 := by
    unfold inward
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_sub, Complex.normSq_mul]
    simp only [Complex.normSq_ofReal, Complex.normSq_eq_norm_sq x,
      Complex.normSq_eq_norm_sq a, hx, ha, one_pow]
    push_cast
    rw [mul_assoc]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : ‖inward x t - a‖ ^ 2 / ‖x-a‖ ^ 2 ≤ 1-t/2 := by
    rw [div_le_iff₀ (by positivity), hs]
    nlinarith [mul_nonneg ht (sub_nonneg.mpr hsmall)]
  have hpos : 0 < ‖inward x t-a‖ ^ 2 / ‖x-a‖ ^ 2 := by positivity
  have hlog := Real.log_le_sub_one_of_pos hpos
  rw [Real.log_div (pow_ne_zero _ hp'.ne') (pow_ne_zero _ hp.ne'), Real.log_pow, Real.log_pow] at hlog
  linarith

private theorem norm_shift_root_ge {x a : ℂ} (hx : ‖x‖ ≤ 1) (ha : 1 ≤ ‖a‖)
    {δ : ℝ} (hδ : 0 ≤ δ) : ‖x-a‖ ≤ ‖x - ((1+δ : ℝ) : ℂ)*a‖ := by
  have hd : (x * conj a).re ≤ ‖a‖ ^ 2 := by
    have h := Complex.re_le_norm (x * conj a)
    rw [norm_mul, Complex.norm_conj] at h
    apply h.trans
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (norm_nonneg a),
      mul_nonneg (sub_nonneg.mpr ha) (norm_nonneg a)]
  have h : ‖x - ((1+δ : ℝ) : ℂ)*a‖^2 - ‖x-a‖^2 =
      δ*(2*(‖a‖^2-(x*conj a).re)+δ*‖a‖^2) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub,
      Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq a]
    have hh : conj (((1+δ : ℝ) : ℂ)*a) = ((1+δ : ℝ) : ℂ)*conj a := by simp
    rw [hh, ← mul_left_comm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hpos : 0 ≤ δ*(2*(‖a‖^2-(x*conj a).re)+δ*‖a‖^2) :=
    mul_nonneg hδ (add_nonneg (mul_nonneg zero_le_two (sub_nonneg.mpr hd)) (by positivity))
  nlinarith [norm_nonneg (x - a), norm_nonneg (x - ((1+δ : ℝ) : ℂ)*a)]

private theorem norm_shift_root_le {x a : ℂ} (hx : ‖x‖ ≤ 3/4) (ha : 1 ≤ ‖a‖)
    {δ : ℝ} (hδ : 0 ≤ δ) : ‖x - ((1+δ : ℝ) : ℂ)*a‖ ≤ (1+4*δ)*‖x-a‖ := by
  have h := norm_add_le (x-a) (-((δ:ℂ)*a))
  rw [show x-a + -((δ:ℂ)*a) = x-((1+δ : ℝ) : ℂ)*a by push_cast; ring, norm_neg,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hδ] at h
  have hh := norm_add_le (a-x) x
  rw [sub_add_cancel, norm_sub_rev] at hh
  have hkey : ‖a‖ ≤ 4*‖x-a‖ := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hkey hδ]

/-- A polynomial whose roots are separated by the unit lemniscate cannot be very
    small deep inside one of its circles of roots. The proof moves the one root of
    the component radially outward, and uses minimum modulus on the truncated component. -/
theorem log_lower_inside_cluster {n : ℕ} (hn : 100 ≤ n) (a : Fin n → ℂ) {c : ℂ} (hc : c ≠ 0)
    (I : Finset (Fin n)) (hI : (n : ℝ)/10 ≤ I.card)
    (hnear : ∀ i ∈ I, ‖a i‖ = 1) (hfar : ∀ i ∉ I, 1001 ≤ ‖a i‖)
    (hfull : numComponents (rootProduct a c) = n) {z : ℂ} (hz : ‖z‖ ≤ 3/4) :
    -(4000 : ℝ)/n ≤ Real.log ‖(rootProduct a c).eval z‖ := by
  classical
  let p := rootProduct a c
  let S := Erdos1047.strictSublevelSet p 1
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha (i : Fin n) : 1 ≤ ‖a i‖ := by
    by_cases hi : i ∈ I
    · rw [hnear i hi]
    · exact (by norm_num : (1 : ℝ) ≤ 1001).trans (hfar i hi)
  by_cases hzS : z ∈ S
  · obtain ⟨i, hi⟩ := full_component_unique hc hn0 hfull hzS
    let U := connectedComponentIn S z
    let K := closure U ∩ closedBall (0 : ℂ) 1
    let δ : ℝ := 1000 / (n : ℝ)
    have hδ : 0 < δ := by positivity
    let b : Fin n → ℂ := Function.update a i (((1+δ : ℝ) : ℂ)*a i)
    let g := rootProduct b c
    have hu : IsOpen U := (sublevel_open p).connectedComponentIn
    have hzK : z ∈ K := ⟨subset_closure (mem_connectedComponentIn hzS),
      mem_closedBall_zero_iff.mpr (by linarith)⟩
    have hbi : b i = ((1+δ : ℝ) : ℂ)*a i := Function.update_self ..
    have hbj (j : Fin n) (hj : j ≠ i) : b j = a j := Function.update_of_ne hj ..
    have hbB : 1+δ ≤ ‖b i‖ := by
      rw [hbi, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact le_mul_of_one_le_right (by positivity) (ha i)
    have hroot (w : ℂ) (hw : w ∈ K) (j : Fin n) : w ≠ b j := by
      intro hwj
      by_cases hj : j = i
      · subst j
        have h := mem_closedBall_zero_iff.mp hw.2
        rw [hwj] at h
        linarith
      · rw [hbj j hj] at hwj
        have hws : w ∈ S := by
          change ‖p.eval w‖ < 1
          rw [(rootProduct_zero_iff a hc w).mpr ⟨j, hwj.symm⟩, norm_zero]
          norm_num
        have hwu := component_closure_inside (sublevel_open p) hw.1 hws
        rw [hwj] at hwu
        exact hj ((hi j).mp hwu)
    have hg0 (w : ℂ) (hw : w ∈ K) : g.eval w ≠ 0 := by
      rw [ne_eq, rootProduct_zero_iff b hc]
      exact fun ⟨j, hj⟩ ↦ hroot w hw j hj.symm
    have hprod (w : ℂ) :
        ‖p.eval w‖ = ‖w-a i‖ * (‖c‖ * ∏ j ∈ Finset.univ.erase i, ‖w-a j‖) ∧
        ‖g.eval w‖ = ‖w-b i‖ * (‖c‖ * ∏ j ∈ Finset.univ.erase i, ‖w-a j‖) := by
      simp only [p, g, rootProduct_eval, norm_mul, norm_prod]
      constructor
      · rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ ‖w - a j‖) (Finset.mem_univ i)]
        ring
      · rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ ‖w - b j‖) (Finset.mem_univ i)]
        have he : (∏ j ∈ Finset.univ.erase i, ‖w-b j‖) = ∏ j ∈ Finset.univ.erase i, ‖w-a j‖ :=
          Finset.prod_congr rfl (fun j hj ↦ by rw [hbj j (Finset.mem_erase.mp hj).1])
        rw [he]
        ring
    have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).inter_left isClosed_closure
    have hmin : ∀ w ∈ K, 1 ≤ ‖g.eval w‖ := by
      obtain ⟨w, hw, hm⟩ := hK.exists_isMinOn ⟨z, hzK⟩ g.continuous.norm.continuousOn
      suffices hh : 1 ≤ ‖g.eval w‖ from fun x hx ↦ hh.trans (hm hx)
      by_contra! hl
      have hwB := mem_closedBall_zero_iff.mp hw.2
      have hpg : ‖p.eval w‖ ≤ ‖g.eval w‖ := by
        rw [(hprod w).1, (hprod w).2, hbi]
        exact mul_le_mul_of_nonneg_right (norm_shift_root_ge hwB (ha i) hδ.le) (by positivity)
      have hwS : w ∈ S := hpg.trans_lt hl
      have hwU : w ∈ U := component_closure_inside (sublevel_open p) hw.1 hwS
      by_cases hbnd : ‖w‖ < 1
      · have hk : K ∈ 𝓝 w := by
          refine mem_of_superset (inter_mem (hu.mem_nhds hwU)
            (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hbnd))) ?_
          exact fun x hx ↦ ⟨subset_closure hx.1, ball_subset_closedBall hx.2⟩
        exact norm_not_local_min (by dsimp only [g]; rw [rootProduct_degree b hc]; exact hn0) (hg0 w hw)
          (hm.localize.isLocalMin hk)
      have hws : ‖w‖ = 1 := le_antisymm hwB (le_of_not_gt hbnd)
      have ht : Tendsto (inward w) (𝓝[>] 0) (𝓝 w) := by
        have he : inward w 0 = w := by simp [inward]
        simpa only [he] using ((show Continuous (inward w) by unfold inward; fun_prop).continuousAt
          (x := 0)).tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      have hUev := ht.eventually (hu.mem_nhds hwU)
      have htev : ∀ᶠ t : ℝ in 𝓝[>] 0, t ∈ Ioo 0 1 := Ioo_mem_nhdsGT (by norm_num)
      have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ j, t < ‖w - b j‖^2 / 2 := by
        apply Filter.eventually_all.mpr
        intro j
        have hp' : 0 < ‖w-b j‖ ^ 2 / 2 := by positivity [norm_pos_iff.mpr (sub_ne_zero.mpr (hroot w hw j))]
        exact nhdsWithin_le_nhds (Iio_mem_nhds hp')
      obtain ⟨t, ht01, htU, ht'⟩ := (htev.and (hUev.and hsmall)).exists
      have htK : inward w t ∈ K := ⟨subset_closure htU, by
        rw [mem_closedBall_zero_iff, inward, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (by linarith [ht01.2]), hws, mul_one]; linarith [ht01.1]⟩
      let d := fun j ↦ Real.log ‖inward w t-b j‖ - Real.log ‖w-b j‖
      have hdne (j : Fin n) : d j ≤ t / ‖w-b j‖ :=
        log_inward_general hws ht01.1.le (hroot w hw j) (hroot _ htK j)
      have hdi : d i ≤ t / δ := by
        apply (hdne i).trans
        apply div_le_div_of_nonneg_left ht01.1.le hδ
        have hh := norm_add_le (b i - w) w
        rw [sub_add_cancel, norm_sub_rev, hws] at hh
        linarith
      have hsum : (∑ j, d j) ≤ -(t/4) * (I.erase i).card + (t/1000) * n + t/δ := by
        let A := I.erase i
        let B := Finset.univ \ insert i A
        have hadd : (∑ j, d j) = d i + (∑ j ∈ A, d j) + ∑ j ∈ B, d j := by
          rw [← Finset.sum_sdiff (Finset.subset_univ (insert i A)), Finset.sum_insert (by simp [A])]
          ring
        rw [hadd]
        have hA : (∑ j ∈ A, d j) ≤ (A.card : ℝ)*(-t/4) := by
          rw [← nsmul_eq_mul]
          apply Finset.sum_le_card_nsmul
          intro j hj
          have hj' := Finset.mem_erase.mp hj
          exact log_inward_circle hws (by rw [hbj j hj'.1]; exact hnear j hj'.2)
            ht01.1.le (ht' j).le (hroot _ hw j) (hroot _ htK j)
        have hB : (∑ j ∈ B, d j) ≤ (B.card : ℝ)*(t/1000) := by
          rw [← nsmul_eq_mul]
          apply Finset.sum_le_card_nsmul
          intro j hj
          have hh := Finset.mem_sdiff.mp hj
          have hj' : j ≠ i := fun he ↦ hh.2 (he ▸ Finset.mem_insert_self i A)
          have hj'' : j ∉ I := fun he ↦ hh.2 (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hj', he⟩))
          apply (hdne j).trans
          apply div_le_div_of_nonneg_left ht01.1.le (by norm_num)
          have hh' := norm_add_le (b j-w) w
          rw [sub_add_cancel, norm_sub_rev, hws] at hh'
          rw [hbj j hj'] at hh' ⊢
          linarith [hfar j hj'']
        have hBc : (B.card : ℝ) ≤ n := by exact_mod_cast (by simpa using B.card_le_univ : B.card ≤ n)
        change _ ≤ -(t/4) * (A.card : ℝ) + (t/1000) * n + t/δ
        linarith [mul_le_mul_of_nonneg_right hBc (div_nonneg ht01.1.le (by norm_num : (0:ℝ) ≤ 1000))]
      have hcard : (I.erase i).card + 1 ≥ I.card := by
        by_cases hi' : i ∈ I
        · rw [Finset.card_erase_of_mem hi']; have := Finset.card_pos.mpr ⟨i,hi'⟩; omega
        · rw [Finset.erase_eq_of_notMem hi']; omega
      have hcr : (I.erase i).card + 1 ≥ (I.card : ℝ) := by exact_mod_cast hcard
      have hnr : (100 : ℝ) ≤ n := by exact_mod_cast hn
      have hneg : -(t/4) * ((I.erase i).card : ℝ) + (t/1000) * n + t/δ < 0 := by
        have hδ' : t/δ = t*n/1000 := by dsimp [δ]; field_simp
        rw [hδ']
        have hlarge : (n : ℝ)/20 ≤ (I.erase i).card := by linarith
        nlinarith [mul_le_mul_of_nonneg_left hlarge ht01.1.le, mul_pos ht01.1 hnpos]
      have hlogs : Real.log ‖g.eval (inward w t)‖ < Real.log ‖g.eval w‖ := by
        have hh := hsum.trans_lt hneg
        rw [log_rootProduct b hc (hroot _ htK), log_rootProduct b hc (hroot _ hw)]
        dsimp [d] at hh
        rw [Finset.sum_sub_distrib] at hh
        linarith
      exact not_lt_of_ge (Real.log_le_log (norm_pos_iff.mpr (hg0 w hw)) (hm htK)) hlogs
    have hpz : 0 < ‖p.eval z‖ := by
      apply norm_pos_iff.mpr
      rw [ne_eq, rootProduct_zero_iff a hc]
      rintro ⟨j,hj⟩
      have h := ha j
      rw [hj] at h
      linarith
    have hle : ‖g.eval z‖ ≤ (1+4*δ)*‖p.eval z‖ := by
       rw [(hprod z).2, (hprod z).1, hbi]
       simpa only [mul_assoc] using
         mul_le_mul_of_nonneg_right (norm_shift_root_le hz (ha i) hδ.le)
           (mul_nonneg (norm_nonneg c) (Finset.prod_nonneg
             (s := Finset.univ.erase i) (f := fun j ↦ ‖z - a j‖) (fun _ _ ↦ norm_nonneg _)))
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1) ((hmin z hzK).trans hle)
    rw [Real.log_one, Real.log_mul (by positivity) hpz.ne'] at hlog
    have hlog' := Real.log_le_sub_one_of_pos (show 0 < 1+4*δ by positivity)
    dsimp [δ] at hlog hlog'
    change -(4000 : ℝ)/n ≤ Real.log ‖p.eval z‖
    have he : 4 * (1000 / (n : ℝ)) = 4000 / n := by ring
    have he' : -(4000 : ℝ) / n = -(4000 / n) := neg_div ..
    rw [he']
    rw [he] at hlog hlog'
    linarith
  · change ¬ ‖p.eval z‖ < 1 at hzS
    exact (div_nonpos_of_nonpos_of_nonneg (by norm_num : -(4000 : ℝ) ≤ 0)
      (Nat.cast_nonneg n)).trans
      (Real.log_nonneg (le_of_not_gt hzS))

private theorem numComponents_of_eval_homeomorph {p q : ℂ[X]} (e : ℂ ≃ₜ ℂ)
    (h : ∀ w, q.eval w = p.eval (e w)) : numComponents q = numComponents p := by
  let U := Erdos1047.strictSublevelSet q 1
  let V := Erdos1047.strictSublevelSet p 1
  have he : e '' U = V := by
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩
      change ‖q.eval w‖ < 1 at hw
      change ‖p.eval (e w)‖ < 1
      rwa [← h]
    · intro hx
      change ‖p.eval x‖ < 1 at hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      change ‖q.eval (e.symm x)‖ < 1
      simpa only [h, e.apply_symm_apply] using hx
  have hc : Erdos1047.componentsIn V = (fun s : Set ℂ ↦ e '' s) '' Erdos1047.componentsIn U := by
    rw [← he]
    ext W
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨connectedComponentIn U x, ⟨x, hx, rfl⟩, e.image_connectedComponentIn hx⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨e x, mem_image_of_mem e hx, e.image_connectedComponentIn hx⟩
  change (Erdos1047.componentsIn U).ncard = (Erdos1047.componentsIn V).ncard
  rw [hc, Set.ncard_image_of_injective _ e.injective.image_injective]

/-- The interior bound in coordinates centered at the circle of roots. -/
theorem log_lower_inside_affine {n : ℕ} (hn : 100 ≤ n) (a : Fin n → ℂ)
    (I : Finset (Fin n)) (hI : (n : ℝ)/10 ≤ I.card)
    (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hnear : ∀ i ∈ I, ‖a i - c‖ = R) (hfar : ∀ i ∉ I, 1001 * R ≤ ‖a i - c‖)
    (hfull : numComponents (rootProduct a 1) = n) {z : ℂ}
    (hz : ‖z - c‖ ≤ (3/4) * R) :
    -(4000 : ℝ)/n ≤ Real.log ‖(rootProduct a 1).eval z‖ := by
  have hr : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  let e := (Homeomorph.mulLeft₀ (R : ℂ) hr).trans (Homeomorph.addLeft c)
  have he (w : ℂ) : e w = c + (R : ℂ) * w := rfl
  let b := fun i ↦ (a i - c) / (R : ℂ)
  let d : ℂ := (R : ℂ)^n
  have hd : d ≠ 0 := pow_ne_zero _ hr
  have hEval (w : ℂ) : (rootProduct b d).eval w = (rootProduct a 1).eval (e w) := by
    rw [rootProduct_eval, rootProduct_eval, one_mul, he]
    have h₁ : d = ∏ _ : Fin n, (R : ℂ) := by simp [d]
    rw [h₁, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    dsimp [b]
    field_simp
    ring
  have hnorm (i : Fin n) : ‖b i‖ = ‖a i - c‖ / R := by
    simp [b, Complex.norm_real, abs_of_pos hR]
  have hnear' (i : Fin n) (hi : i ∈ I) : ‖b i‖ = 1 := by
    rw [hnorm, hnear i hi, div_self hR.ne']
  have hfar' (i : Fin n) (hi : i ∉ I) : 1001 ≤ ‖b i‖ := by
    rw [hnorm, le_div_iff₀ hR]
    exact hfar i hi
  have hz' : ‖(z-c)/(R : ℂ)‖ ≤ 3/4 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, div_le_iff₀ hR]
    exact hz
  have he' : e ((z-c)/(R : ℂ)) = z := by rw [he]; field_simp; ring
  have hfull' := (numComponents_of_eval_homeomorph e hEval).trans hfull
  simpa only [hEval, he'] using log_lower_inside_cluster hn b hd I hI hnear' hfar' hfull' hz'

end Erdos1042.TwoCircles
end

section
-- CircleGreedy
open Metric Set Filter Polynomial
open scoped BigOperators ENNReal

namespace Erdos1042.TwoCircles

/-- If every monic polynomial with roots in `F` has maximum modulus at least `exp (n L)`
on `F`, appending one point at a time gives the corresponding lower capacity bound. -/
theorem circle_capacity_by_max {F : Set ℂ} {L : ℝ}
    (h : ∀ (n : ℕ) (a : Fin n → ℂ), (∀ i, a i ∈ F) →
      ∃ w ∈ F, Real.exp (n*L) ≤ ‖(rootProduct a 1).eval w‖) :
    ENNReal.ofReal (Real.exp L) ≤ transfiniteDiameter F := by
  apply capacity_lower_of_greedy
  intro n a ha
  obtain ⟨w, hw, hprod⟩ := h n a ha
  refine ⟨w, hw, ?_⟩
  rw [← ENNReal.ofReal_pow (Real.exp_pos L).le, ← Real.exp_nat_mul]
  rw [rootProduct_eval, one_mul, norm_prod] at hprod
  have he : (∏ i, edist w (a i)) = ENNReal.ofReal (∏ i, ‖w-a i‖) := by
    simp_rw [edist_dist, dist_eq_norm]
    exact (ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦ norm_nonneg _)).symm
  rw [he]
  exact ENNReal.ofReal_le_ofReal hprod

theorem circlePair_normalized {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hpos : 0 < transfiniteDiameter (circlePair 1 r s)) :
    ∃ t : ℝ, 2 ≤ t ∧ transfiniteDiameter (circlePair t r s) = 1 := by
  let E := transfiniteDiameter (circlePair 1 r s)
  have hE : E ≤ ENNReal.ofReal (1/2) := circlePair_upper zero_lt_one hr hs hr' hs'
  have htop : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hE
  let D := E.toReal
  have hD : 0 < D := ENNReal.toReal_pos hpos.ne' htop
  have hD' : D ≤ 1/2 := by
    simpa only [D, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1/2)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hE
  refine ⟨1/D, (le_div_iff₀ hD).mpr (by linarith), ?_⟩
  rw [circlePair_scale, diameter_scale (one_div_pos.mpr hD)]
  change ENNReal.ofReal (1/D) * E = 1
  rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (by positivity)]
  change ENNReal.ofReal (1/D * D) = 1
  rw [one_div_mul_cancel hD.ne', ENNReal.ofReal_one]

end Erdos1042.TwoCircles
end

section
-- CircleProfiles
open Metric Set Filter Polynomial
open scoped BigOperators ComplexConjugate

namespace Erdos1042.TwoCircles

/-- The root indices and their coordinates on the two circles. -/
structure CircleCoordinates {n : ℕ} (t r s : ℝ) (a : Fin n → ℂ) where
  left : Finset (Fin n)
  coord : Fin n → ℂ
  norm_left : ∀ i ∈ left, ‖coord i‖ = r
  norm_right : ∀ i ∉ left, ‖coord i‖ = s
  root_left : ∀ i ∈ left, a i = mapA t (coord i)
  root_right : ∀ i ∉ left, a i = mapB t (coord i)

theorem CircleCoordinates.exists_of_mem {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}
    (h : ∀ i, a i ∈ circlePair t r s) : Nonempty (CircleCoordinates t r s a) := by
  classical
  let I := Finset.univ.filter fun i ↦ a i ∈ mapA t '' sphere (0 : ℂ) r
  have hu (i : Fin n) : ∃ u : ℂ, if i ∈ I then ‖u‖ = r ∧ a i = mapA t u
      else ‖u‖ = s ∧ a i = mapB t u := by
    by_cases hi : i ∈ I
    · obtain ⟨u, hu, he⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨u, by simpa [hi] using And.intro (mem_sphere_zero_iff_norm.mp hu) he.symm⟩
    · have ha : a i ∉ mapA t '' sphere (0 : ℂ) r := by simpa [I] using hi
      obtain ⟨u, hu, he⟩ := (h i).resolve_left ha
      exact ⟨u, by simpa [hi] using And.intro (mem_sphere_zero_iff_norm.mp hu) he.symm⟩
  choose u hu using hu
  have hA i (hi : i ∈ I) : ‖u i‖ = r ∧ a i = mapA t (u i) := by simpa [hi] using hu i
  have hB i (hi : i ∉ I) : ‖u i‖ = s ∧ a i = mapB t (u i) := by simpa [hi] using hu i
  exact ⟨⟨I, u, fun i hi ↦ (hA i hi).1, fun i hi ↦ (hB i hi).1,
    fun i hi ↦ (hA i hi).2, fun i hi ↦ (hB i hi).2⟩⟩

namespace CircleCoordinates

variable {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}

def swap (C : CircleCoordinates t r s a) : CircleCoordinates t s r (fun i ↦ (t : ℂ) - a i) where
  left := C.leftᶜ
  coord := C.coord
  norm_left i hi := C.norm_right i (Finset.mem_compl.mp hi)
  norm_right i hi := C.norm_left i (by simpa using hi)
  root_left i hi := by
    rw [C.root_right i (Finset.mem_compl.mp hi), mapB, sub_sub_cancel]
  root_right i hi := by
    rw [C.root_left i (show i ∈ C.left by simpa using hi), mapB]

theorem card_add (C : CircleCoordinates t r s a) :
    (C.left.card : ℝ) + ((C.leftᶜ).card : ℝ) = n := by
  exact_mod_cast (by simp [Finset.card_compl, show C.left.card ≤ n by simpa using C.left.card_le_univ] :
    C.left.card + (C.leftᶜ).card = n)

end CircleCoordinates

noncomputable def logA {n : ℕ} (t : ℝ) (a : Fin n → ℂ) (w : ℂ) : ℝ :=
  Real.log ‖(rootProduct a 1).eval (mapA t w)‖

noncomputable def logB {n : ℕ} (t : ℝ) (a : Fin n → ℂ) (w : ℂ) : ℝ :=
  Real.log ‖(rootProduct a 1).eval (mapB t w)‖

noncomputable def coordinateSum {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) (x : ℝ) : ℝ :=
  ∑ i ∈ I, Real.log ‖1 - (x : ℂ) * v i‖

theorem coordinateSum_zero {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) :
    coordinateSum I v 0 = 0 := by simp [coordinateSum]

theorem coordinateSum_continuousAt_zero {n : ℕ} (I : Finset (Fin n)) (v : Fin n → ℂ) :
    ContinuousAt (coordinateSum I v) 0 := by
  unfold coordinateSum
  change Tendsto _ _ _
  exact tendsto_finsetSum I (fun i _ ↦ by
    have h : Continuous (fun x : ℝ ↦ ‖1 - (x : ℂ) * v i‖) := by fun_prop
    exact (Real.continuousAt_log (by simp : ‖1 - ((0 : ℝ) : ℂ) * v i‖ ≠ 0)).comp
      (f := fun x : ℝ ↦ ‖1 - (x : ℂ) * v i‖) (h.continuousAt (x := 0)))

private theorem mul_norm_lt_one {z w : ℂ} (hz : ‖z‖ ≤ 1) (hw : ‖w‖ < 1) : ‖z * w‖ < 1 := by
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hz (norm_nonneg w)).trans_lt (by simpa using hw)

theorem mapA_avoids_roots {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}
    (C : CircleCoordinates t r s a) (ht : 0 < t) (hr : r < 1) (hs : s < 1)
    {w : ℂ} (hw : ‖w‖ < r) (i : Fin n) : mapA t w ≠ a i := by
  have hw' := hw.trans hr
  apply sub_ne_zero.mp (norm_pos_iff.mp ?_)
  by_cases hi : i ∈ C.left
  · have hv := (C.norm_left i hi).trans_lt hr
    have h : w ≠ C.coord i := by
      intro he
      rw [he, C.norm_left i hi] at hw
      exact (lt_irrefl _ hw)
    rw [C.root_left i hi, mapA_sub_mapA_norm ht hw' hv]
    exact div_pos (mul_pos ht (norm_pos_iff.mpr (sub_ne_zero.mpr h)))
      (mul_pos (den_pos hw') (den_pos hv))
  · have hv := (C.norm_right i hi).trans_lt hs
    rw [C.root_right i hi, norm_sub_rev, mapB_sub_mapA_norm ht hv hw']
    exact div_pos (mul_pos ht (den_pos (mul_norm_lt_one hv.le hw')))
      (mul_pos (den_pos hv) (den_pos hw'))

theorem mapA_eval_pos {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}
    (C : CircleCoordinates t r s a) (ht : 0 < t) (hr : r < 1) (hs : s < 1)
    {w : ℂ} (hw : ‖w‖ < r) : 0 < ‖(rootProduct a 1).eval (mapA t w)‖ := by
  rw [norm_pos_iff, ne_eq, rootProduct_zero_iff a one_ne_zero]
  exact fun ⟨i, hi⟩ ↦ mapA_avoids_roots C ht hr hs hw i hi.symm

private theorem reflect_eval_norm {n : ℕ} (t : ℝ) (a : Fin n → ℂ) (w : ℂ) :
    ‖(rootProduct (fun i ↦ (t : ℂ) - a i) 1).eval w‖ =
      ‖(rootProduct a 1).eval ((t : ℂ) - w)‖ := by
  simp only [rootProduct_eval, one_mul, norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [norm_sub_rev w]
  congr 1
  ring

theorem logA_swap {n : ℕ} (t : ℝ) (a : Fin n → ℂ) (w : ℂ) :
    logA t (fun i ↦ (t : ℂ) - a i) w = logB t a w := by
  simp only [logA, logB, reflect_eval_norm, mapB]

theorem mapB_eval_pos {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}
    (C : CircleCoordinates t r s a) (ht : 0 < t) (hr : r < 1) (hs : s < 1)
    {w : ℂ} (hw : ‖w‖ < s) : 0 < ‖(rootProduct a 1).eval (mapB t w)‖ := by
  simpa only [reflect_eval_norm, mapB] using mapA_eval_pos C.swap ht hs hr hw

theorem logA_harmonic {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hr : 0 < r) (hr' : r < 1) (hs' : s < 1) :
    InnerProductSpace.HarmonicOnNhd (logA t a) (closedBall (0 : ℂ) (r/2)) := by
  intro w hw
  have hw' : ‖w‖ < r := (mem_closedBall_zero_iff.mp hw).trans_lt (by linarith)
  have ha : AnalyticAt ℂ (rootProduct a 1).eval (mapA t w) :=
    (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (rootProduct a 1)) _ (mem_univ _)
  have han := ha.comp (mapA_analytic t (hw'.trans hr'))
  apply han.harmonicAt_log_norm
  change (rootProduct a 1).eval (mapA t w) ≠ 0
  rw [ne_eq, rootProduct_zero_iff a one_ne_zero]
  exact fun ⟨i,hi⟩ ↦ mapA_avoids_roots C ht hr' hs' hw' i hi.symm

theorem logB_harmonic {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hs : 0 < s) (hr' : r < 1) (hs' : s < 1) :
    InnerProductSpace.HarmonicOnNhd (logB t a) (closedBall (0 : ℂ) (s/2)) := by
  simpa only [funext (logA_swap t a)] using logA_harmonic C.swap ht hs hs' hr'

theorem mapA_eval_le_of_boundary {n : ℕ} {t r : ℝ} {a : Fin n → ℂ} {M : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hM : ∀ z ∈ mapA t '' sphere (0 : ℂ) r,
      ‖(rootProduct a 1).eval z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖(rootProduct a 1).eval (mapA t w)‖ ≤ M := by
  let f : ℂ → ℂ := (rootProduct a 1).eval ∘ mapA t
  have hD : ∀ z ∈ closedBall (0 : ℂ) r, DifferentiableAt ℂ f z := by
    intro z hz
    have ha : AnalyticAt ℂ (rootProduct a 1).eval (mapA t z) :=
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) (rootProduct a 1)) _ (mem_univ _)
    exact (ha.comp (mapA_analytic t ((mem_closedBall_zero_iff.mp hz).trans_lt hr'))).differentiableAt
  refine Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) r) isBounded_ball
    ⟨fun z hz ↦ (hD z (ball_subset_closedBall hz)).differentiableWithinAt, ?_⟩ ?_ ?_
  · rw [closure_ball _ hr.ne']
    exact fun z hz ↦ (hD z hz).continuousAt.continuousWithinAt
  · rw [frontier_ball _ hr.ne']
    exact fun z hz ↦ hM _ ⟨z, hz, rfl⟩
  · rw [closure_ball _ hr.ne']
    exact mem_closedBall_zero_iff.mpr hw

theorem mapB_eval_le_of_boundary {n : ℕ} {t r : ℝ} {a : Fin n → ℂ} {M : ℝ}
    (hr : 0 < r) (hr' : r < 1) (hM : ∀ z ∈ mapB t '' sphere (0 : ℂ) r,
      ‖(rootProduct a 1).eval z‖ ≤ M) {w : ℂ} (hw : ‖w‖ ≤ r) :
    ‖(rootProduct a 1).eval (mapB t w)‖ ≤ M := by
  rw [mapB, ← reflect_eval_norm]
  apply mapA_eval_le_of_boundary hr hr' _ hw
  rintro _ ⟨z,hz,rfl⟩
  rw [reflect_eval_norm]
  exact hM _ ⟨z,hz,rfl⟩

private theorem real_distance_on_circle {r x : ℝ} {u : ℂ} (hr : 0 < r) (hu : ‖u‖ = r) :
    ‖(x : ℂ) - u‖ = r * ‖1 - ((x/r^2 : ℝ) : ℂ)*u‖ := by
  have hmul : u * conj u = ((r^2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]
  have hc : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have h : (x : ℂ) - u = -u * (1 - ((x/r^2 : ℝ) : ℂ)*conj u) := by
    calc
      _ = -u + ((x/r^2 : ℝ) : ℂ) * (u * conj u) := by
        rw [hmul]
        push_cast
        field_simp
        ring
      _ = _ := by ring
  rw [h, norm_mul, norm_neg, hu, ← Complex.norm_conj (1 - ((x/r^2 : ℝ) : ℂ)*u)]
  simp

private theorem log_dist_A_left {t r x : ℝ} {v : ℂ} (ht : 0 < t) (hr : 0 < r) (hr' : r < 1)
    (hv : ‖v‖ = r) (hx : |x| < r) :
    Real.log ‖mapA t (x : ℂ) - mapA t v‖ = Real.log t - Real.log ‖1-v‖ + Real.log r +
      Real.log ‖1 - ((x/r^2 : ℝ) : ℂ) * v‖ - Real.log (1-x) := by
  have hx' : ‖(x : ℂ)‖ < r := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx
  have hw := den_pos (hx'.trans hr')
  have hv' := den_pos (hv.trans_lt hr')
  have hne : (x : ℂ) ≠ v := fun he ↦ by rw [he, hv] at hx'; exact lt_irrefl _ hx'
  have he : ‖1 - (x : ℂ)‖ = 1-x := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [(abs_lt.mp hx).2])]
  rw [mapA_sub_mapA_norm ht (hx'.trans hr') (hv.trans_lt hr'),
    Real.log_div (mul_ne_zero ht.ne' (norm_pos_iff.mpr (sub_ne_zero.mpr hne)).ne')
      (mul_ne_zero hw.ne' hv'.ne'), Real.log_mul ht.ne' (norm_pos_iff.mpr (sub_ne_zero.mpr hne)).ne',
    Real.log_mul hw.ne' hv'.ne', real_distance_on_circle hr hv, he]
  have hpos : 0 < ‖1 - ((x/r^2 : ℝ) : ℂ) * v‖ := by
    have h := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    rw [real_distance_on_circle hr hv] at h
    exact (mul_pos_iff_of_pos_left hr).mp h
  rw [Real.log_mul hr.ne' hpos.ne']
  ring

private theorem log_dist_A_right {t s x : ℝ} {v : ℂ} (ht : 0 < t) (hs' : s < 1)
    (hv : ‖v‖ = s) (hx : |x| < 1) :
    Real.log ‖mapA t (x : ℂ) - mapB t v‖ = Real.log t - Real.log ‖1-v‖ +
      Real.log ‖1 - (x : ℂ) * v‖ - Real.log (1-x) := by
  have hx' : ‖(x : ℂ)‖ < 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx
  have hv' := hv.trans_lt hs'
  have hw := den_pos hx'
  have hp := den_pos (mul_norm_lt_one hv'.le hx')
  have hq := den_pos hv'
  have he : ‖1 - (x : ℂ)‖ = 1-x := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (by linarith [(abs_lt.mp hx).2])]
  rw [norm_sub_rev, mapB_sub_mapA_norm ht hv' hx',
    Real.log_div (mul_ne_zero ht.ne' hp.ne') (mul_ne_zero hq.ne' hw.ne'),
    Real.log_mul ht.ne' hp.ne', Real.log_mul hq.ne' hw.ne', mul_comm v, he]
  ring

noncomputable def logBase {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a) : ℝ :=
  n * Real.log t - coordinateSum C.left C.coord 1 - coordinateSum C.leftᶜ C.coord 1

theorem logA_formula {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hr : 0 < r) (hr' : r < 1) (hs' : s < 1) {x : ℝ} (hx : |x| < r) :
    logA t a (x : ℂ) = logBase C + C.left.card * Real.log r +
      coordinateSum C.left C.coord (x/r^2) + coordinateSum C.leftᶜ C.coord x - n * Real.log (1-x) := by
  have hw : ‖(x : ℂ)‖ < r := by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx
  let g (i : Fin n) := Real.log ‖mapA t (x : ℂ) - a i‖
  have hL (i : Fin n) (hi : i ∈ C.left) : g i =
      Real.log t - Real.log ‖1-C.coord i‖ + Real.log r +
        Real.log ‖1 - ((x/r^2 : ℝ) : ℂ) * C.coord i‖ - Real.log (1-x) := by
    dsimp [g]
    rw [C.root_left i hi]
    exact log_dist_A_left ht hr hr' (C.norm_left i hi) hx
  have hR (i : Fin n) (hi : i ∈ C.leftᶜ) : g i =
      Real.log t - Real.log ‖1-C.coord i‖ +
        Real.log ‖1 - (x : ℂ) * C.coord i‖ - Real.log (1-x) := by
    dsimp [g]
    rw [C.root_right i (Finset.mem_compl.mp hi)]
    exact log_dist_A_right ht hs' (C.norm_right i (Finset.mem_compl.mp hi)) (hx.trans hr')
  rw [logA, log_rootProduct a one_ne_zero (mapA_avoids_roots C ht hr' hs' hw), norm_one,
    Real.log_one, zero_add]
  change (∑ i, g i) = _
  rw [← Finset.sum_add_sum_compl C.left g, Finset.sum_congr rfl hL, Finset.sum_congr rfl hR]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    coordinateSum, logBase, Complex.ofReal_one, one_mul]
  rw [← C.card_add]
  ring

theorem logB_formula {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hs : 0 < s) (hr' : r < 1) (hs' : s < 1) {x : ℝ} (hx : |x| < s) :
    logB t a (x : ℂ) = logBase C + (C.leftᶜ).card * Real.log s +
      coordinateSum C.leftᶜ C.coord (x/s^2) + coordinateSum C.left C.coord x - n * Real.log (1-x) := by
  have hc : logBase C.swap = logBase C := by simp only [logBase, CircleCoordinates.swap, compl_compl]; ring
  have h := logA_formula C.swap ht hs hs' hr' hx
  rw [hc, logA_swap] at h
  simpa only [CircleCoordinates.swap, compl_compl] using h

theorem log_centers {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) (hr' : r < 1) (hs' : s < 1) :
    logA t a 0 = logBase C + C.left.card * Real.log r ∧
      logB t a 0 = logBase C + (C.leftᶜ).card * Real.log s := by
  constructor
  · simpa [coordinateSum_zero] using logA_formula C ht hr hr' hs' (x := 0) (by simpa using hr)
  · simpa [coordinateSum_zero] using logB_formula C ht hs hr' hs' (x := 0) (by simpa using hs)

end Erdos1042.TwoCircles
end

section
-- CircleBalance
open Metric Set Filter Polynomial InnerProductSpace
open scoped BigOperators ENNReal Topology

namespace Erdos1042.TwoCircles

private noncomputable def q (r s : ℝ) : ℝ := r^2*s^2

private noncomputable def balanceTerm (r s : ℝ) (j : ℕ) : ℝ :=
  let x := (q r s)^j
  (Real.log (1-q r s*x) - Real.log (1-r^2*x)) +
    (Real.log (1-q r s*x) - Real.log (1-s^2*x))

noncomputable def balanceLevel (t r s θ : ℝ) : ℝ :=
  Real.log t + θ * Real.log r + ∑' j : ℕ, balanceTerm r s j

private theorem small_sq {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1/100000000) : r^2 ≤ r/4 := by
  nlinarith [mul_nonneg hr.le (show 0 ≤ 1/4-r by linarith)]

private theorem q_bounds {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000) :
    0 ≤ q r s ∧ q r s ≤ r^2 ∧ q r s ≤ s^2 ∧ q r s ≤ 1/2 := by
  have hR : r^2 ≤ 1/2 := (small_sq hr hr').trans (by linarith)
  have hS : s^2 ≤ 1/2 := (small_sq hs hs').trans (by linarith)
  unfold q
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · exact mul_le_of_le_one_right (sq_nonneg _) (hS.trans (by norm_num))
  · exact mul_le_of_le_one_left (sq_nonneg _) (hR.trans (by norm_num))
  · exact (mul_le_of_le_one_right (sq_nonneg _) (hS.trans (by norm_num))).trans hR

private theorem neg_log_one_sub_le {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1/2) :
    - Real.log (1-x) ≤ 2*x := by
  have hpos : 0 < 1-x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have h' : (1-x)⁻¹ ≤ 1+2*x := by
    rw [← one_div, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hx (show 0 ≤ 1-2*x by linarith)]
  linarith

private theorem balanceTerm_bounds {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000) (j : ℕ) :
    0 ≤ balanceTerm r s j ∧ balanceTerm r s j ≤ 4 * (1/2 : ℝ)^j := by
  obtain ⟨hQ₀, hQR, hQS, hQ⟩ := q_bounds hr hs hr' hs'
  let x := (q r s)^j
  have hx : 0 ≤ x := pow_nonneg hQ₀ _
  have hx₁ : x ≤ 1 := pow_le_one₀ hQ₀ (hQ.trans (by norm_num))
  have hx₂ : x ≤ (1/2 : ℝ)^j := pow_le_pow_left₀ hQ₀ hQ _
  have hxQ : 0 ≤ q r s*x := mul_nonneg hQ₀ hx
  have hxR : 0 ≤ r^2*x := by positivity
  have hxS : 0 ≤ s^2*x := by positivity
  have hR : r^2*x ≤ 1/2 := (mul_le_of_le_one_right (sq_nonneg _) hx₁).trans
    ((small_sq hr hr').trans (by linarith))
  have hS : s^2*x ≤ 1/2 := (mul_le_of_le_one_right (sq_nonneg _) hx₁).trans
    ((small_sq hs hs').trans (by linarith))
  have h₁ := mul_le_mul_of_nonneg_right hQR hx
  have h₂ := mul_le_mul_of_nonneg_right hQS hx
  have hlg := Real.log_nonpos (show 0 ≤ 1-q r s*x by linarith) (by linarith)
  change 0 ≤ (Real.log (1-q r s*x) - Real.log (1-r^2*x)) + _ ∧
    (Real.log (1-q r s*x) - Real.log (1-r^2*x)) +
      (Real.log (1-q r s*x) - Real.log (1-s^2*x)) ≤ _
  constructor
  · have h₁' := Real.log_le_log (show 0 < 1-r^2*x by linarith) (show 1-r^2*x ≤ 1-q r s*x by linarith)
    have h₂' := Real.log_le_log (show 0 < 1-s^2*x by linarith) (show 1-s^2*x ≤ 1-q r s*x by linarith)
    linarith
  · have hR' : r^2*x ≤ x := mul_le_of_le_one_left hx ((small_sq hr hr').trans (by linarith))
    have hS' : s^2*x ≤ x := mul_le_of_le_one_left hx ((small_sq hs hs').trans (by linarith))
    linarith [neg_log_one_sub_le hxR hR, neg_log_one_sub_le hxS hS]

private theorem balanceTerm_summable {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000) : Summable (balanceTerm r s) := by
  refine ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)).mul_left 4).of_norm_bounded ?_
  intro j
  obtain ⟨h₀,h₁⟩ := balanceTerm_bounds hr hs hr' hs' j
  rwa [Real.norm_of_nonneg h₀]

theorem le_balanceLevel {t r s θ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000) :
    Real.log t + θ * Real.log r ≤ balanceLevel t r s θ := by
  apply le_add_of_nonneg_right
  exact tsum_nonneg (fun i ↦ (balanceTerm_bounds hr hs hr' hs' i).1)

private noncomputable def delta (f : ℂ → ℝ) (x : ℝ) : ℝ := f (x : ℂ) - f 0

private noncomputable def balanceDelta {n : ℕ} (t r s : ℝ) (a : Fin n → ℂ) (j : ℕ) : ℝ :=
  let x := (q r s)^j
  (delta (logA t a) (r^2*x) - delta (logA t a) (q r s*x)) +
    (delta (logB t a) (s^2*x) - delta (logB t a) (q r s*x))

private noncomputable def sumBoth {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}
    (C : CircleCoordinates t r s a) (x : ℝ) : ℝ :=
  coordinateSum C.left C.coord x + coordinateSum C.leftᶜ C.coord x

private theorem balanceDelta_eq {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (j : ℕ) : balanceDelta t r s a j = n * balanceTerm r s j +
      (sumBoth C ((q r s)^j) - sumBoth C ((q r s)^(j+1))) := by
  let Q := q r s
  let x := Q^j
  have hr₁ : r < 1 := by linarith
  have hs₁ : s < 1 := by linarith
  obtain ⟨hQ₀, hQR, hQS, hQ⟩ := q_bounds hr hs hr' hs'
  have hx : 0 ≤ x := pow_nonneg hQ₀ _
  have hx' : x ≤ 1 := pow_le_one₀ hQ₀ (hQ.trans (by norm_num))
  have hxR : |r^2*x| < r := by
    rw [abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right (sq_nonneg _) hx').trans_lt ((small_sq hr hr').trans_lt (by linarith))
  have hxS : |s^2*x| < s := by
    rw [abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_right (sq_nonneg _) hx').trans_lt ((small_sq hs hs').trans_lt (by linarith))
  have hxQ : |Q*x| ≤ r^2*x ∧ |Q*x| ≤ s^2*x := by
    rw [abs_of_nonneg (mul_nonneg hQ₀ hx)]
    exact ⟨mul_le_mul_of_nonneg_right hQR hx, mul_le_mul_of_nonneg_right hQS hx⟩
  have hxQr : |Q*x| < r := hxQ.1.trans_lt ((le_abs_self _).trans_lt hxR)
  have hxQs : |Q*x| < s := hxQ.2.trans_lt ((le_abs_self _).trans_lt hxS)
  have heA : r^2*x/r^2 = x := by field_simp
  have heB : s^2*x/s^2 = x := by field_simp
  have heQr : Q*x/r^2 = s^2*x := by dsimp [Q, q]; field_simp
  have heQs : Q*x/s^2 = r^2*x := by dsimp [Q, q]; field_simp
  have he : Q^(j+1) = Q*x := pow_succ' _ _
  change (delta (logA t a) (r^2*x) - delta (logA t a) (Q*x)) +
    (delta (logB t a) (s^2*x) - delta (logB t a) (Q*x)) =
      n * ((Real.log (1-Q*x) - Real.log (1-r^2*x)) +
        (Real.log (1-Q*x) - Real.log (1-s^2*x))) + (sumBoth C x - sumBoth C (Q^(j+1)))
  rw [delta, delta, delta, delta, logA_formula C ht hr hr₁ hs₁ hxR,
    logA_formula C ht hr hr₁ hs₁ hxQr, logB_formula C ht hs hr₁ hs₁ hxS,
    logB_formula C ht hs hr₁ hs₁ hxQs, heA, heB, heQr, heQs, he, sumBoth, sumBoth]
  ring

private theorem balanceDelta_bound {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ}
    (hr : 0 < r) (hs : 0 < s) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hLA : ∀ x : ℝ, |x| ≤ r/4 → |delta (logA t a) x| ≤ 8*|x|/r*A)
    (hLB : ∀ x : ℝ, |x| ≤ s/4 → |delta (logB t a) x| ≤ 8*|x|/s*B) (j : ℕ) :
    |balanceDelta t r s a j| ≤ (1/24 : ℝ)*(1/2 : ℝ)^j*(A+B) := by
  let Q := q r s
  let x := Q^j
  obtain ⟨hQ₀, hQR, hQS, hQ⟩ := q_bounds hr hs hr' hs'
  have hx : 0 ≤ x := pow_nonneg hQ₀ _
  have hx' : x ≤ 1 := pow_le_one₀ hQ₀ (hQ.trans (by norm_num))
  have hxx : x ≤ (1/2 : ℝ)^j := pow_le_pow_left₀ hQ₀ hQ _
  have hAux {R D : ℝ} {f : ℂ → ℝ} (hR : 0 < R) (hR' : R ≤ 1/100000000)
      (hD : 0 ≤ D) (hQR : Q ≤ R^2) (hf : ∀ y : ℝ, |y| ≤ R/4 → |delta f y| ≤ 8*|y|/R*D) :
      |delta f (R^2*x) - delta f (Q*x)| ≤ (1/24 : ℝ)*(1/2 : ℝ)^j*D := by
    have hRx : |R^2*x| = R^2*x := abs_of_nonneg (by positivity)
    have hQx : |Q*x| = Q*x := abs_of_nonneg (mul_nonneg hQ₀ hx)
    have hq : Q*x ≤ R^2*x := mul_le_mul_of_nonneg_right hQR hx
    have hRsmall : R^2*x ≤ R/4 := (mul_le_of_le_one_right (sq_nonneg _) hx').trans (small_sq hR hR')
    have h₁ := hf (R^2*x) (by rwa [hRx])
    have h₂ := hf (Q*x) (by rw [hQx]; exact hq.trans hRsmall)
    rw [hRx] at h₁
    rw [hQx] at h₂
    have hd := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 8)) hR.le) hD
    calc
      _ ≤ |delta f (R^2*x)| + |delta f (Q*x)| := abs_sub _ _
      _ ≤ 16*R*x*D := by
        have he : 8*(R^2*x)/R*D = 8*R*x*D := by field_simp
        linarith [h₂.trans hd]
      _ ≤ (1/24 : ℝ)*(1/2 : ℝ)^j*D := by
        gcongr
        linarith
  change |(delta (logA t a) (r^2*x) - delta (logA t a) (Q*x)) +
    (delta (logB t a) (s^2*x) - delta (logB t a) (Q*x))| ≤ _
  refine (abs_add_le _ _).trans ?_
  linarith [hAux hr hr' hA hQR hLA, hAux hs hs' hB hQS hLB]

/-- The balanced evaluation differs from a weighted sum of two center values by at most
one twelfth of the available Harnack deviations. Alternating the two Möbius identities
cancels the terms depending on the angular coordinates of the individual roots. -/
theorem balance_error {n : ℕ} {t r s θ : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (ht : 0 < t) (hr : 0 < r) (hs : 0 < s) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hθ : θ * Real.log r = (1-θ) * Real.log s) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hLA : ∀ x : ℝ, |x| ≤ r/4 → |logA t a (x : ℂ) - logA t a 0| ≤ 8*|x|/r*A)
    (hLB : ∀ x : ℝ, |x| ≤ s/4 → |logB t a (x : ℂ) - logB t a 0| ≤ 8*|x|/s*B) :
    |(n : ℝ) * balanceLevel t r s θ - (θ * logA t a 0 + (1-θ) * logB t a 0)| ≤ (A+B)/12 := by
  obtain ⟨hQ₀, _, _, hQ⟩ := q_bounds hr hs hr' hs'
  obtain ⟨hcA, hcB⟩ := log_centers C ht hr hs (by linarith) (by linarith)
  let W := θ * logA t a 0 + (1-θ) * logB t a 0
  have hW : W = n*(Real.log t+θ*Real.log r) - sumBoth C 1 := by
    dsimp only [W]
    rw [hcA, hcB]
    have he := C.card_add
    simp only [logBase, sumBoth]
    linear_combination (θ * Real.log r) * he - (C.leftᶜ.card : ℝ) * hθ
  have heq (m : ℕ) : (∑ j ∈ Finset.range m, balanceDelta t r s a j) =
      n*(Real.log t+θ*Real.log r + ∑ j ∈ Finset.range m, balanceTerm r s j) -
        sumBoth C ((q r s)^m) - W := by
    induction m with
    | zero => simp [hW]
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, balanceDelta_eq C ht hr hs hr' hs' m]
      ring
  have hg : Summable (fun i : ℕ ↦ (1/2 : ℝ)^i) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum (m : ℕ) : |∑ j ∈ Finset.range m, balanceDelta t r s a j| ≤ (A+B)/12 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum (fun j _ ↦
      balanceDelta_bound hr hs hr' hs' hA hB hLA hLB j)).trans ?_)
    have he' (j : ℕ) : (1/24 : ℝ)*(1/2 : ℝ)^j*(A+B) = ((1/24 : ℝ)*(A+B))*(1/2 : ℝ)^j := by ring
    simp_rw [he', ← Finset.mul_sum]
    have hs' : (∑ j ∈ Finset.range m, (1/2 : ℝ)^j) ≤ 2 := by
      have hh := hg.sum_le_tsum (Finset.range m) (fun j _ ↦ by positivity)
      rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)] at hh
      norm_num at hh ⊢
      exact hh
    have h := mul_le_mul_of_nonneg_left hs' (show 0 ≤ (1/24 : ℝ)*(A+B) by positivity)
    convert h using 1
    ring
  have hpow : Tendsto (fun m : ℕ ↦ (q r s)^m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hQ₀ (hQ.trans_lt (by norm_num))
  have hcont : ContinuousAt (sumBoth C) 0 :=
    (coordinateSum_continuousAt_zero C.left C.coord).add (coordinateSum_continuousAt_zero C.leftᶜ C.coord)
  have htail : Tendsto (fun m : ℕ ↦ sumBoth C ((q r s)^m)) atTop (𝓝 0) := by
    have he' : sumBoth C 0 = 0 := by simp [sumBoth, coordinateSum_zero]
    exact he' ▸ hcont.tendsto.comp hpow
  have hL := (balanceTerm_summable hr hs hr' hs').hasSum.tendsto_sum_nat
  have hconst : Tendsto (fun _ : ℕ ↦ Real.log t+θ*Real.log r) atTop (𝓝 (Real.log t+θ*Real.log r)) :=
    tendsto_const_nhds
  have hlim : Tendsto (fun m : ℕ ↦ |n*(Real.log t+θ*Real.log r + ∑ j ∈ Finset.range m, balanceTerm r s j)
      - sumBoth C ((q r s)^m) - W|) atTop (𝓝 |n*balanceLevel t r s θ - W|) := by
    simpa only [sub_zero, balanceLevel] using
      ((((hconst.add hL).const_mul (n : ℝ)).sub htail).sub tendsto_const_nhds (b := W)).abs
  exact le_of_tendsto' hlim fun m ↦ heq m ▸ hsum m

theorem upper_log_variation {f : ℂ → ℝ} {r M : ℝ} (hr : 0 < r)
    (hf : HarmonicOnNhd f (closedBall 0 (r/2))) (hM : ∀ z ∈ closedBall 0 (r/2), f z ≤ M)
    {x : ℝ} (hx : |x| ≤ r/4) : |f (x : ℂ) - f 0| ≤ 8*|x|/r*(M-f 0) := by
  have hw : ‖(x : ℂ)‖ ≤ (r/2)/2 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have h := harmonic_variation (half_pos hr) ((harmonicOnNhd_const M).sub hf)
    (fun z hz ↦ sub_nonneg.mpr (hM z hz)) hw
  simp only [Pi.sub_apply, Complex.norm_real, Real.norm_eq_abs] at h
  have he : M - f (x : ℂ) - (M-f 0) = -(f (x : ℂ)-f 0) := by ring
  rw [he, abs_neg] at h
  convert h using 1
  ring

theorem lower_log_variation {f : ℂ → ℝ} {r E : ℝ} (hr : 0 < r)
    (hf : HarmonicOnNhd f (closedBall 0 (r/2))) (hE : ∀ z ∈ closedBall 0 (r/2), E ≤ f z)
    {x : ℝ} (hx : |x| ≤ r/4) : |f (x : ℂ) - f 0| ≤ 8*|x|/r*(f 0-E) := by
  have hw : ‖(x : ℂ)‖ ≤ (r/2)/2 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  have h := harmonic_variation (half_pos hr) (hf.sub (harmonicOnNhd_const E))
    (fun z hz ↦ sub_nonneg.mpr (hE z hz)) hw
  simp only [Pi.sub_apply, Complex.norm_real, Real.norm_eq_abs] at h
  have he : f (x : ℂ)-E - (f 0-E) = f (x : ℂ)-f 0 := by ring
  rw [he] at h
  convert h using 1
  ring

/-- A lower bound for capacity, obtained by the greedy product construction. -/
theorem capacity_ge_balanceLevel {t r s θ : ℝ} (ht : 0 < t) (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hθ₀ : 1/3 ≤ θ) (hθ₁ : θ ≤ 2/3) (hθ : θ * Real.log r = (1-θ) * Real.log s) :
    ENNReal.ofReal (Real.exp (balanceLevel t r s θ)) ≤ transfiniteDiameter (circlePair t r s) := by
  apply circle_capacity_by_max
  intro n a ha
  obtain ⟨C⟩ := CircleCoordinates.exists_of_mem ha
  have hr₁ : r < 1 := by linarith
  have hs₁ : s < 1 := by linarith
  have hF : (circlePair t r s).Nonempty := by
    exact ⟨mapA t (r : ℂ), Or.inl ⟨(r : ℂ), by simp [Complex.norm_real, abs_of_pos hr], rfl⟩⟩
  obtain ⟨w, hw, hm⟩ := (circlePair_compact t hr₁ hs₁).exists_isMaxOn hF
    (rootProduct a 1).continuous.norm.continuousOn
  let N := ‖(rootProduct a 1).eval w‖
  let M := Real.log N
  have hpA (z : ℂ) (hz : z ∈ closedBall 0 (r/2)) : ‖(rootProduct a 1).eval (mapA t z)‖ ≤ N :=
    mapA_eval_le_of_boundary hr hr₁ (fun _ hz ↦ hm (Or.inl hz))
      ((mem_closedBall_zero_iff.mp hz).trans (by linarith))
  have hpB (z : ℂ) (hz : z ∈ closedBall 0 (s/2)) : ‖(rootProduct a 1).eval (mapB t z)‖ ≤ N :=
    mapB_eval_le_of_boundary hs hs₁ (fun _ hz ↦ hm (Or.inr hz))
      ((mem_closedBall_zero_iff.mp hz).trans (by linarith))
  have hlA (z : ℂ) (hz : z ∈ closedBall 0 (r/2)) : logA t a z ≤ M :=
    Real.log_le_log (mapA_eval_pos C ht hr₁ hs₁ ((mem_closedBall_zero_iff.mp hz).trans_lt (by linarith))) (hpA z hz)
  have hlB (z : ℂ) (hz : z ∈ closedBall 0 (s/2)) : logB t a z ≤ M :=
    Real.log_le_log (mapB_eval_pos C ht hr₁ hs₁ ((mem_closedBall_zero_iff.mp hz).trans_lt (by linarith))) (hpB z hz)
  have hzeroA : (0 : ℂ) ∈ closedBall 0 (r/2) := mem_closedBall_self (by positivity)
  have hzeroB : (0 : ℂ) ∈ closedBall 0 (s/2) := mem_closedBall_self (by positivity)
  have hA := sub_nonneg.mpr (hlA 0 hzeroA)
  have hB := sub_nonneg.mpr (hlB 0 hzeroB)
  have h := balance_error C ht hr hs hr' hs' hθ hA hB
    (fun _ hx ↦ upper_log_variation hr (logA_harmonic C ht hr hr₁ hs₁) hlA hx)
    (fun _ hx ↦ upper_log_variation hs (logB_harmonic C ht hs hr₁ hs₁) hlB hx)
  have hh : (n : ℝ)*balanceLevel t r s θ ≤ M := by
    have h₁ := mul_nonneg (show 0 ≤ θ-1/12 by linarith) hA
    have h₂ := mul_nonneg (show 0 ≤ (1-θ)-1/12 by linarith) hB
    linarith [(abs_le.mp h).2]
  have hp : 0 < N := (mapA_eval_pos C ht hr₁ hs₁ (w := 0) (by simpa using hr)).trans_le (hpA 0 hzeroA)
  exact ⟨w, hw, (Real.le_log_iff_exp_le hp).mp hh⟩

end Erdos1042.TwoCircles
end

section
-- CircleCounterexample
open Metric Set Filter Polynomial
open scoped BigOperators ENNReal

/-! The two components of the set are Möbius images of circles of radii `r` and `s`.
The transfinite diameter is normalized by scaling their common separation parameter `t`.
Full separation gives lower bounds for the log modulus in both disks via
`log_lower_inside_affine`. The alternating evaluation identity `balance_error`, also
used to bound the capacity by the greedy product construction, then bounds the
difference between the two center values. In the Möbius coordinates this difference
is exactly `k * log r - l * log s`, where `k` and `l` count the two sets of roots.
The choice `log s / log r = √2` makes this difference too large for any such counts. -/

namespace Erdos1042.TwoCircles

private theorem abs_log_norm_one_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    |Real.log ‖1-z‖| ≤ 2*‖z‖ := by
  have h₁ := norm_one_sub_ge z
  have h₂ := norm_sub_le (1 : ℂ) z
  rw [norm_one] at h₂
  have hpos : 0 < ‖1-z‖ := by linarith
  have hinv : ‖1-z‖⁻¹ ≤ 1+2*‖z‖ := by
    rw [← one_div, div_le_iff₀ hpos]
    have h := mul_le_mul_of_nonneg_left h₁ (show 0 ≤ 1+2*‖z‖ by positivity)
    nlinarith [mul_nonneg (norm_nonneg z) (show 0 ≤ 1-2*‖z‖ by linarith)]
  rw [abs_le]
  constructor
  · linarith [Real.one_sub_inv_le_log_of_pos hpos]
  · linarith [Real.log_le_sub_one_of_pos hpos, norm_nonneg z]

private theorem abs_sum_coords_le {n : ℕ} (I : Finset (Fin n)) (u : Fin n → ℂ) {r : ℝ}
    (hr : r ≤ 1/100000000) (hu : ∀ i ∈ I, ‖u i‖ = r) :
    |coordinateSum I u 1| ≤ (I.card : ℝ)/100 := by
  simp only [coordinateSum, Complex.ofReal_one, one_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _ ∈ I, (1/100 : ℝ) := Finset.sum_le_sum fun i hi ↦ by
      have h := hu i hi
      have h₁ := abs_log_norm_one_sub_le (show ‖u i‖ ≤ 1/2 by rw [h]; linarith)
      rw [h] at h₁
      linarith
    _ = _ := by simp [nsmul_eq_mul, div_eq_mul_inv]

private theorem logA_lower_core {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (hn : 100 ≤ n) (ht : 0 < t) (hr : 0 < r) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hcnt : (n : ℝ)/10 ≤ C.left.card) (hfull : numComponents (rootProduct a 1) = n)
    (w : ℂ) (hw : w ∈ closedBall 0 (r/2)) : -(4000 : ℝ)/n ≤ logA t a w := by
  refine log_lower_inside_affine hn a C.left hcnt (circleCenter t r) (radius_pos ht hr (by linarith)) ?_ ?_ hfull ?_
  · intro i hi
    rw [C.root_left i hi]
    exact mapA_boundary ht hr (by linarith) (C.norm_left i hi)
  · intro i hi
    rw [C.root_right i hi]
    exact foreign_far_A ht hr hr' hs' (C.norm_right i hi)
  · exact mapA_core ht hr (by linarith) (mem_closedBall_zero_iff.mp hw)

private theorem logB_lower_core {n : ℕ} {t r s : ℝ} {a : Fin n → ℂ} (C : CircleCoordinates t r s a)
    (hn : 100 ≤ n) (ht : 0 < t) (hs : 0 < s) (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hcnt : (n : ℝ)/10 ≤ (C.leftᶜ).card) (hfull : numComponents (rootProduct a 1) = n)
    (w : ℂ) (hw : w ∈ closedBall 0 (s/2)) : -(4000 : ℝ)/n ≤ logB t a w := by
  refine log_lower_inside_affine hn a C.leftᶜ hcnt ((t : ℂ) - circleCenter t s) (radius_pos ht hs (by linarith)) ?_ ?_ hfull ?_
  · intro i hi
    rw [C.root_right i (Finset.mem_compl.mp hi)]
    exact mapB_boundary ht hs (by linarith) (C.norm_right i (Finset.mem_compl.mp hi))
  · intro i hi
    have hi' : i ∈ C.left := by simpa using hi
    rw [C.root_left i hi']
    exact foreign_far_B ht hs hr' hs' (C.norm_left i hi')
  · exact mapB_core ht hs (by linarith) (mem_closedBall_zero_iff.mp hw)

private theorem normalized_level_nonpos {t r s θ : ℝ} (ht : 0 < t) (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hθ₀ : 1/3 ≤ θ) (hθ₁ : θ ≤ 2/3) (hθ : θ * Real.log r = (1-θ) * Real.log s)
    (hcap : transfiniteDiameter (circlePair t r s) = 1) : balanceLevel t r s θ ≤ 0 := by
  have h := capacity_ge_balanceLevel ht hr hs hr' hs' hθ₀ hθ₁ hθ
  rw [hcap, ← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff zero_le_one] at h
  exact Real.exp_le_one_iff.mp h

private theorem log_of_small_radius {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1/100000000) :
    Real.log r ≤ -10 := by
  have h := Real.log_le_log hr (show r ≤ (1/2 : ℝ)^20 by exact hr'.trans (by norm_num))
  rw [Real.log_pow, show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  have h' := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h h'
  linarith

/-- All roots must be apportioned between the two circles in their prescribed
logarithmic ratio, up to an error of order `1/n` in the actual counts. -/
private theorem balanced_counts_bound {n : ℕ} {t r s θ : ℝ} {a : Fin n → ℂ}
    (C : CircleCoordinates t r s a) (hn : 100 ≤ n) (ht : 2 ≤ t) (hr : 0 < r) (hs : 0 < s)
    (hr' : r ≤ 1/100000000) (hs' : s ≤ 1/100000000)
    (hθ₀ : 1/3 ≤ θ) (hθ₁ : θ ≤ 2/3) (hθ : θ * Real.log r = (1-θ) * Real.log s)
    (hcap : transfiniteDiameter (circlePair t r s) = 1)
    (hfull : numComponents (rootProduct a 1) = n) :
    |(C.left.card : ℝ)*Real.log r - (C.leftᶜ.card : ℝ)*Real.log s| ≤ 24000/(n : ℝ) := by
  have ht' : 0 < t := by linarith
  have hr₁ : r < 1 := by linarith
  have hs₁ : s < 1 := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₀ : (0 : ℝ) ≤ n := hn'.le
  let A := logA t a 0
  let B := logB t a 0
  let E : ℝ := 4000/n
  have hE : 0 ≤ E := by positivity
  obtain ⟨hcA, hcB⟩ := log_centers C ht' hr hs hr₁ hs₁
  change A = _ at hcA
  change B = _ at hcB
  have hL := normalized_level_nonpos ht' hr hs hr' hs' hθ₀ hθ₁ hθ hcap
  have hLL := le_balanceLevel (t := t) (θ := θ) hr hs hr' hs'
  have hbase : logBase C ≤ n*(-θ*Real.log r+1/100) := by
    have hA := (abs_le.mp (abs_sum_coords_le C.left C.coord hr' C.norm_left)).1
    have hB := (abs_le.mp (abs_sum_coords_le C.leftᶜ C.coord hs'
      (fun i hi ↦ C.norm_right i (Finset.mem_compl.mp hi)))).1
    have hT : Real.log t ≤ -θ*Real.log r := by linarith
    unfold logBase
    linarith [C.card_add, mul_le_mul_of_nonneg_left hT hn₀]
  have hbase' : logBase C ≤ n*(-(1-θ)*Real.log s+1/100) := by
    have he' : -θ*Real.log r = -(1-θ)*Real.log s := by linarith
    rwa [← he']
  have hlogA' := log_of_small_radius hr hr'
  have hlogB' := log_of_small_radius hs hs'
  have hsmall : E ≤ (n : ℝ)/2 := by
    dsimp [E]
    rw [div_le_iff₀ hn']
    have hnr : (100 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_nonneg (sub_nonneg.mpr hnr) hn₀]
  have hOver {k x α L : ℝ} (hx : x = logBase C+k*L) (hbase : logBase C ≤ n*(-α*L+1/100))
      (hα : α ≤ 2/3) (hL : L ≤ -10) (hk : (9/10 : ℝ)*n < k) : x < -E := by
    have hk' : (1/5 : ℝ)*n ≤ k-α*n := by linarith [mul_le_mul_of_nonneg_right hα hn₀]
    have h₁ := mul_le_mul_of_nonpos_right hk' (show L ≤ 0 by linarith)
    have h₂ := mul_le_mul_of_nonneg_left hL (show 0 ≤ (1/5 : ℝ)*n by positivity)
    nlinarith
  have hcntA : (n : ℝ)/10 ≤ C.left.card := by
    by_contra! hk
    have hk' : (9/10 : ℝ)*n < (C.leftᶜ).card := by linarith [C.card_add]
    have hcntB : (n : ℝ)/10 ≤ (C.leftᶜ).card := by linarith
    have hB : -E ≤ B := by
      simpa only [E, neg_div] using
        (logB_lower_core C hn ht' hs hr' hs' hcntB hfull 0 (mem_closedBall_self (by positivity)))
    exact (not_lt_of_ge hB) (hOver hcB hbase' (by linarith) hlogB' hk')
  have hcntB : (n : ℝ)/10 ≤ (C.leftᶜ).card := by
    by_contra! hk
    have hk' : (9/10 : ℝ)*n < (C.left.card : ℝ) := by linarith [C.card_add]
    have hcntA' : (n : ℝ)/10 ≤ C.left.card := by linarith
    have hA : -E ≤ A := by
      simpa only [E, neg_div] using
        (logA_lower_core C hn ht' hr hr' hs' hcntA' hfull 0 (mem_closedBall_self (by positivity)))
    exact (not_lt_of_ge hA) (hOver hcA hbase hθ₁ hlogA' hk')
  have hLA : ∀ w ∈ closedBall (0 : ℂ) (r/2), -E ≤ logA t a w := fun w hw ↦ by
    simpa only [E, neg_div] using logA_lower_core C hn ht' hr hr' hs' hcntA hfull w hw
  have hLB : ∀ w ∈ closedBall (0 : ℂ) (s/2), -E ≤ logB t a w := fun w hw ↦ by
    simpa only [E, neg_div] using logB_lower_core C hn ht' hs hr' hs' hcntB hfull w hw
  have hA : 0 ≤ A+E := by
    have h := hLA 0 (mem_closedBall_self (by positivity))
    linarith
  have hB : 0 ≤ B+E := by
    have h := hLB 0 (mem_closedBall_self (by positivity))
    linarith
  have h := balance_error C ht' hr hs hr' hs' hθ hA hB
    (fun x hx ↦ by
      simpa only [A, sub_neg_eq_add] using lower_log_variation hr (logA_harmonic C ht' hr hr₁ hs₁) hLA hx)
    (fun x hx ↦ by
      simpa only [B, sub_neg_eq_add] using lower_log_variation hs (logB_harmonic C ht' hs hr₁ hs₁) hLB hx)
  change |(n : ℝ)*balanceLevel t r s θ - (θ*A+(1-θ)*B)| ≤ (A+E+(B+E))/12 at h
  have hsum : (A+E) + (B+E) ≤ 4*E := by
    have h₁ := mul_nonneg (show 0 ≤ θ-1/3 by linarith) hA
    have h₂ := mul_nonneg (show 0 ≤ (1-θ)-1/3 by linarith) hB
    have h₃ := mul_nonpos_of_nonneg_of_nonpos hn₀ hL
    linarith [(abs_le.mp h).1]
  have hdiff : |A-B| ≤ 6*E := by
    rw [abs_le]
    constructor <;> linarith
  rw [hcA, hcB, add_sub_add_left_eq_sub] at hdiff
  convert hdiff using 1
  dsimp [E]
  ring

private theorem sqrt_two_bounds : 1 ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

private theorem sqrt_two_root_gap {n k l : ℕ} (hn : 0 < n) (hkl : (k : ℝ) + l = n) :
    ¬ |(k : ℝ)*(-100000) - (l : ℝ)*(-100000*Real.sqrt 2)| ≤ 24000/(n : ℝ) := by
  let α := Real.sqrt 2
  obtain ⟨hα₁, hα₂⟩ := sqrt_two_bounds
  change 1 ≤ α at hα₁
  change α ≤ 2 at hα₂
  have hαsq : α^2 = 2 := Real.sq_sqrt (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hplus : 0 < (k : ℝ) + α*l := by nlinarith [mul_le_mul_of_nonneg_right hα₁ hl]
  have hne : (k : ℝ) - α*l ≠ 0 := by
    intro he
    by_cases hl₀ : l = 0
    · subst l
      norm_num at hkl he
      linarith
    · have hl' : (l : ℝ) ≠ 0 := by exact_mod_cast hl₀
      have heq : α = (k : ℝ) / l := (eq_div_iff hl').mpr (by linarith)
      exact irrational_sqrt_two.ne_rational (k : ℤ) (l : ℤ) (by simpa only [Int.cast_natCast] using heq)
  have hprod : ((k : ℝ)-α*l)*((k : ℝ)+α*l) = (((k : ℤ)^2 - 2*(l : ℤ)^2 : ℤ) : ℝ) := by
    push_cast
    linear_combination -(l : ℝ)^2 * hαsq
  have hne' : (k : ℤ)^2 - 2*(l : ℤ)^2 ≠ 0 := by
    intro he
    rw [he, Int.cast_zero] at hprod
    exact mul_ne_zero hne hplus.ne' hprod
  have hgap : (1 : ℝ) ≤ |(k : ℝ)-α*l| * ((k : ℝ)+α*l) := by
    rw [← abs_of_pos hplus, ← abs_mul, hprod, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hne'
  intro h
  change |(k : ℝ)*(-100000) - (l : ℝ)*(-100000*α)| ≤ 24000/(n : ℝ) at h
  rw [show (k : ℝ)*(-100000) - (l : ℝ)*(-100000*α) = (-100000 : ℝ)*((k : ℝ)-α*l) by ring,
    abs_mul, show |(-100000 : ℝ)| = 100000 by norm_num] at h
  have h₁ := (le_div_iff₀ hn').mp h
  have h₂ : (k : ℝ)+α*l ≤ 2*n := by nlinarith [mul_le_mul_of_nonneg_right hα₂ hl]
  have h₃ := mul_le_mul_of_nonneg_left h₂ (abs_nonneg ((k : ℝ)-α*l))
  nlinarith

/-- A compact counterexample of capacity one, with no fully separated polynomial in
any degree at least one hundred. -/
theorem two_circle_counterexample : ∃ F : Set ℂ, IsClosed F ∧ transfiniteDiameter F = 1 ∧
    (∀ c : ℂ, ¬ F ⊆ closedBall c 1) ∧
    ∀ n ≥ 100, ∀ f : ℂ[X], MonicWithRootsIn F n f → numComponents f ≠ n := by
  let α := Real.sqrt 2
  let r := Real.exp (-100000)
  let s := Real.exp (-100000*α)
  let θ := α/(1+α)
  obtain ⟨hα₁,hα₂⟩ := sqrt_two_bounds
  change 1 ≤ α at hα₁
  change α ≤ 2 at hα₂
  have hr : 0 < r := Real.exp_pos _
  have hs : 0 < s := Real.exp_pos _
  have hr' : r ≤ 1/100000000 := by
    have hlog : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith
    have h : r ≤ (1/2 : ℝ)^27 := by
      apply (Real.le_log_iff_exp_le (by positivity : 0 < (1/2 : ℝ)^27)).mp
      rw [Real.log_pow, show (1/2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      norm_num
      linarith
    exact h.trans (by norm_num)
  have hs' : s ≤ 1/100000000 := by
    apply le_trans _ hr'
    exact Real.exp_le_exp.mpr (by linarith)
  have hα : 0 < 1+α := by linarith
  have hθ₀ : 1/3 ≤ θ := (le_div_iff₀ hα).mpr (by linarith)
  have hθ₁ : θ ≤ 2/3 := (div_le_iff₀ hα).mpr (by linarith)
  have hlogR : Real.log r = -100000 := Real.log_exp _
  have hlogS : Real.log s = -100000*α := Real.log_exp _
  have hθ : θ*Real.log r = (1-θ)*Real.log s := by
    rw [hlogR,hlogS]
    dsimp [θ]
    field_simp
    ring
  have hpos : 0 < transfiniteDiameter (circlePair 1 r s) :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).trans_le
      (capacity_ge_balanceLevel zero_lt_one hr hs hr' hs' hθ₀ hθ₁ hθ)
  obtain ⟨t,ht,hcap⟩ := circlePair_normalized hr hs hr' hs' hpos
  refine ⟨circlePair t r s, (circlePair_compact t (by linarith) (by linarith)).isClosed, hcap,
    circlePair_not_ball ht hr hs (by linarith) (by linarith), ?_⟩
  rintro n hn f ⟨hm,hd,hroots⟩ hfull
  obtain ⟨a,ha,ha'⟩ := monic_rootProduct_repr hm hd
  obtain ⟨C⟩ := CircleCoordinates.exists_of_mem (fun i ↦ hroots (a i) (ha' i))
  rw [ha] at hfull
  have h := balanced_counts_bound C hn ht hr hs hr' hs' hθ₀ hθ₁ hθ hcap hfull
  rw [hlogR,hlogS] at h
  exact sqrt_two_root_gap (by omega) C.card_add h

end Erdos1042.TwoCircles
end

open Filter Polynomial Erdos1042 in
theorem OMA.disproof : ¬ (type_of% @Erdos1042.erdos_1042.variants.universal) := by
  intro h
  obtain ⟨F, hclosed, hcap, hball, hfail⟩ := Erdos1042.TwoCircles.two_circle_counterexample
  obtain ⟨n, hn, f, hf, hfull⟩ := frequently_atTop.mp (h F hclosed hcap hball) 100
  exact hfail n hn f hf hfull
