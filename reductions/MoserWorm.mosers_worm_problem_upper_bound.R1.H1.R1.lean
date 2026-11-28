import OMAReductions.R_MoserWorm_mosers_worm_problem_upper_bound_R1

/-!
# Support inequalities for polygonal worms

Sorting the sample times bounds the length of the polygonal chain by one.
The placement then follows from a rotation satisfying the support constraints
for Deng's exact triangle and the finite translation criterion. These are
the support formulation in Section 2.2 and the universal cover in Corollary 7.2
of Zhipeng Deng, [Balanced Support Calibrations for Moser's Worm Problem](https://arxiv.org/html/2609.04591v1).
-/

open EuclideanGeometry
open scoped BigOperators

namespace OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1_H1_R1

private theorem time_telescope {m : ℕ} (t : Fin (m + 1) → ℝ) :
    (∑ i : Fin m, (t i.succ - t i.castSucc)) = t (Fin.last m) - t 0 := by
  rw [Finset.sum_sub_distrib]
  linarith only [Fin.sum_univ_succ t, Fin.sum_univ_castSucc t]

private theorem sorted_sample_length {m : ℕ} {s : Finset (Set.Icc (0 : ℝ) 1)}
    (hs : s.card = m + 1) (g : ↥s → ℝ²) (hg : LipschitzWith 1 g) :
    let p := g ∘ s.orderIsoOfFin hs
    (∑ i : Fin m, dist (p i.castSucc) (p i.succ)) ≤ 1 := by
  let f := s.orderIsoOfFin hs
  let t (i : Fin (m + 1)) : ℝ := (f i).val.val
  let p := g ∘ f
  change (∑ i : Fin m, dist (p i.castSucc) (p i.succ)) ≤ 1
  have hStep (i : Fin m) : dist (p i.castSucc) (p i.succ) ≤ t i.succ - t i.castSucc := by
    have hi : i.castSucc ≤ i.succ := Fin.le_iff_val_le_val.mpr (Nat.le_succ _)
    have ht : t i.castSucc ≤ t i.succ := f.monotone hi
    have hd := hg.dist_le_mul (f i.castSucc) (f i.succ)
    simp only [NNReal.coe_one, one_mul] at hd
    change dist (p i.castSucc) (p i.succ) ≤ dist (t i.castSucc) (t i.succ) at hd
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht)] at hd
    linarith only [hd]
  calc
    _ ≤ ∑ i : Fin m, (t i.succ - t i.castSucc) := Finset.sum_le_sum (fun i _ => hStep i)
    _ = t (Fin.last m) - t 0 := time_telescope t
    _ ≤ 1 := by
      have h0 : 0 ≤ t 0 := (f 0).val.property.1
      have h1 : t (Fin.last m) ≤ 1 := (f (Fin.last m)).val.property.2
      linarith only [h0,h1]

/-- Deng's scaled triangle admits a proper orientation satisfying the support
inequalities for every chain of length at most one. -/
def H1 : Prop :=
  ∀ (m : ℕ) (p : Fin (m + 1) → ℝ²),
    (∑ i : Fin m, dist (p i.castSucc) (p i.succ)) ≤ 1 →
    let q : ℝ := Real.sqrt 625565 * (82074390584 / 84861020075)
    ∃ e : ℝ² ≃ₗᵢ[ℝ] ℝ², e.toLinearEquiv.det = 1 ∧
      ∀ i j k : Fin (m + 1),
        ((e (p i)) 0 - (e (p j)) 0) / (197 / q) +
          ((e (p i)) 1 + (e (p j)) 1 - 2 * (e (p k)) 1) / (766 / q) ≤ 2

/-- A translation exists whenever the support inequalities hold for a finite indexed sample. -/
def H2 : Prop :=
  ∀ (ι : Type) [Fintype ι] (a b : ℝ), 0 < a → 0 < b → ∀ f : ι → ℝ²,
    (∀ i j k : ι,
      ((f i) 0 - (f j) 0) / a + ((f i) 1 + (f j) 1 - 2 * (f k) 1) / b ≤ 2) →
    ∃ v : ℝ², ∀ i : ι, let x := f i + v
      0 ≤ x 1 ∧ |x 0| / a + x 1 / b ≤ 1

theorem main : H1 → H2 → OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.H1 := by
  intro hOrientation hTranslation s g hg
  by_cases hs : s.Nonempty
  · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finset.card_pos.mpr hs).ne'
    let f := s.orderIsoOfFin hm
    let p := g ∘ f
    obtain ⟨e, he, hSupport⟩ := hOrientation m p (sorted_sample_length hm g hg)
    let q : ℝ := Real.sqrt 625565 * (82074390584 / 84861020075)
    have hq : 0 < q := by dsimp only [q]; positivity
    obtain ⟨v, hv⟩ := hTranslation (Fin (m + 1)) (197 / q) (766 / q)
      (div_pos (by norm_num) hq) (div_pos (by norm_num) hq) (fun i => e (p i)) hSupport
    refine ⟨e, v, he, ?_⟩
    intro i
    have hmem := OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1.deng_triangle_containment
      (hv (f.symm i))
    simpa only [p, Function.comp_apply, f.apply_symm_apply, Set.mem_ofPred_eq] using hmem
  · refine ⟨LinearIsometryEquiv.refl ℝ ℝ², 0, by simp, ?_⟩
    intro i
    exact (hs ⟨i.val, i.property⟩).elim

end OMA.R_MoserWorm_mosers_worm_problem_upper_bound_R1_H1_R1
