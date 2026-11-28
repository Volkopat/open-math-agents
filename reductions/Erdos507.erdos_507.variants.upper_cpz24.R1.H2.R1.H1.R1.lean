import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Cohen, Pohoata and Zakharov introduce the point-line coordinates `(a,b,c)`
in §1.4 of https://arxiv.org/html/2409.07658v2#S1.SS4. Two choices of
dominant coordinate suffice for arbitrary directions. On a common integer
mesh with denominator equal to the number of points, the incidence
residual is the integer numerator in H1. If rounding identifies two base
points, the integer residual for that pair is zero. Otherwise apply H1.
Hypothesis H2 and a five-term bound on the change of the residual transfer
either integer estimate to the original real configuration.
-/

namespace OMA.Erdos507DominantChart

open Finset

private theorem coord_eq_or_eq_other (k l : Fin 2) : l = k ∨ l = (1 - k) := by
  fin_cases k <;> fin_cases l <;> decide

/-- A direction with maximal absolute coordinate has a well-defined bounded slope. -/
private theorem dominant_nonzero (k : Fin 2) (d : (EuclideanSpace ℝ (Fin 2))) (hd : d ≠ 0)
    (h : |d ((1 - k))| ≤ |d k|) : d k ≠ 0 := by
  intro hk
  apply hd
  ext l
  rcases coord_eq_or_eq_other k l with rfl | rfl
  · simpa only [PiLp.zero_apply] using hk
  · simp only [hk, abs_zero] at h
    simpa only [PiLp.zero_apply, abs_eq_zero] using le_antisymm h (abs_nonneg _)

/-- The two coordinate orderings are two charts for directions in the plane.
One chart contains at least half of an indexed family of directions. -/
private theorem exists_dominant_chart {m : ℕ} (d : Fin m → (EuclideanSpace ℝ (Fin 2))) :
    ∃ (k : Fin 2) (S : Finset (Fin m)), m ≤ 2 * S.card ∧
      ∀ i ∈ S, |d i ((1 - k))| ≤ |d i k| := by
  classical
  let P (i : Fin m) : Prop := |d i 1| ≤ |d i 0|
  let A := (univ : Finset (Fin m)).filter P
  let B := (univ : Finset (Fin m)).filter (fun i => ¬ P i)
  have hcard : A.card + B.card = m := by
    simpa only [A, B, Finset.card_univ, Fintype.card_fin] using
      (card_filter_add_card_filter_not (s := (univ : Finset (Fin m))) P)
  by_cases h : m ≤ 2 * A.card
  · exact ⟨0, A, h, fun i hi => (mem_filter.mp hi).2⟩
  · refine ⟨1, B, by omega, fun i hi => ?_⟩
    exact (lt_of_not_ge (mem_filter.mp hi).2).le

/-- The point on a line with a prescribed dominant coordinate bounds its
distance by the vertical coordinate residual in that chart. -/
theorem infDist_le_residual (z p d : (EuclideanSpace ℝ (Fin 2))) (k : Fin 2) (hd : d k ≠ 0) :
    Metric.infDist z (AffineSubspace.mk' p (ℝ ∙ d) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ≤
      |z ((1 - k)) - p ((1 - k)) - (d ((1 - k)) / d k) * (z k - p k)| := by
  let t := (z k - p k) / d k
  let q := p + t • d
  have hq : q ∈ AffineSubspace.mk' p (ℝ ∙ d) := by
    apply AffineSubspace.mem_mk'.2
    change p + t • d - p ∈ ℝ ∙ d
    rw [add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  refine (Metric.infDist_le_dist_of_mem hq).trans_eq ?_
  have h0 : (z - q) k = 0 := by
    simp only [q, t, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ hd]
    ring
  have h1 : (z - q) ((1 - k)) =
      z ((1 - k)) - p ((1 - k)) - (d ((1 - k)) / d k) * (z k - p k) := by
    simp only [q, t, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
  fin_cases k <;> simp_all [Real.norm_eq_abs, Real.sqrt_sq_eq_abs]

private theorem square_dist_le_two (z p : (EuclideanSpace ℝ (Fin 2)))
    (hz : ∀ k, z k ∈ Set.Icc (0 : ℝ) 1) (hp : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1) :
    dist z p ≤ 2 := by
  have h (k : Fin 2) : |z k - p k| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith only [(hz k).1, (hp k).2],
      by linarith only [(hz k).2, (hp k).1]⟩
  have hsq (k : Fin 2) : dist (z k) (p k) ^ 2 ≤ 1 := by
    rw [Real.dist_eq]
    nlinarith only [h k, abs_nonneg (z k - p k)]
  have hsum : dist z p ^ 2 ≤ 2 := by
    rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two]
    linarith only [hsq 0, hsq 1]
  nlinarith only [hsum, dist_nonneg (x := z) (y := p)]

private theorem rpow_subset_rate {m s : ℕ} (hmpos : 0 < m) (hs : 0 < s) (h : m ≤ 2 * s)
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    (s : ℝ) ^ (-a) ≤ 2 * (m : ℝ) ^ (-a) := by
  have hm : (0 : ℝ) ≤ m := by positivity
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hms : (m : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast h
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hconst : (2 : ℝ) ^ a ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) ha'
  have hpower : (m : ℝ) ^ a ≤ 2 * (s : ℝ) ^ a := calc
    _ ≤ (2 * (s : ℝ)) ^ a := Real.rpow_le_rpow hm hms ha
    _ = (2 : ℝ) ^ a * (s : ℝ) ^ a := Real.mul_rpow (by norm_num) hsR.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hsR.le _)
  have hspow := Real.rpow_pos_of_pos hsR a
  have hmpow := Real.rpow_pos_of_pos hmR a
  rw [Real.rpow_neg hsR.le, Real.rpow_neg hmR.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ hmpow).2
  calc
    _ ≤ ((s : ℝ) ^ a)⁻¹ * (2 * (s : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_left hpower (inv_nonneg.mpr hspow.le)
    _ = 2 := by rw [mul_left_comm, inv_mul_cancel₀ hspow.ne', mul_one]

/-- A scalar estimate in the bounded-slope chart gives the arbitrary-direction
unit-square incidence estimate with the same exponent. -/
theorem unit_square_of_scalar (hscalar : (
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (I : Type) [Fintype I], 2 ≤ Fintype.card I →
      ∀ a b c : I → ℝ, Function.Injective (fun i => (a i, b i)) →
      (∀ i, a i ∈ Set.Icc (0 : ℝ) 1 ∧ b i ∈ Set.Icc (0 : ℝ) 1 ∧ |c i| ≤ 1) →
      ∃ i j, i ≠ j ∧
        |b i - b j - c j * (a i - a j)| ≤ C * (Fintype.card I : ℝ) ^ (-(2 / 3 : ℝ) + ε)
)) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
    ∀ x d : Fin m → (EuclideanSpace ℝ (Fin 2)),
      Function.Injective x → (∀ i k, x i k ∈ Set.Icc (0 : ℝ) 1) → (∀ i, d i ≠ 0) →
      ∃ i j, i ≠ j ∧ Metric.infDist (x i)
        (AffineSubspace.mk' (x j) (ℝ ∙ d j) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ≤
          C * (m : ℝ) ^ (-(2 / 3 : ℝ) + ε) := by
  classical
  intro ε hε
  let η := min ε (1 / 3)
  have hη : 0 < η := lt_min hε (by norm_num)
  have hηε : η ≤ ε := min_le_left _ _
  have hη' : η ≤ 1 / 3 := min_le_right _ _
  obtain ⟨C, hC, H⟩ := hscalar η hη
  let a := (2 / 3 : ℝ) - η
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have ha' : a ≤ 1 := by dsimp [a]; linarith
  refine ⟨max (2 * C) 6, by positivity, ?_⟩
  intro m hm x d hx hbox hd
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hr := Real.rpow_le_rpow_of_exponent_le
    (x := (m : ℝ)) hm1 (show -a ≤ -(2 / 3 : ℝ) + ε by dsimp [a]; linarith)
  by_cases hm4 : 4 ≤ m
  · obtain ⟨k, S, hsize, hS⟩ := exists_dominant_chart d
    let aa (i : S) := x i k
    let bb (i : S) := x i ((1 - k))
    let cc (i : S) := d i ((1 - k)) / d i k
    have hdir (i : S) : d i k ≠ 0 := dominant_nonzero k (d i) (hd i) (hS i i.property)
    have hs : 2 ≤ Fintype.card S := by rw [Fintype.card_coe]; omega
    have hinj : Function.Injective (fun i : S => (aa i, bb i)) := by
      intro i j hij
      apply Subtype.ext
      apply hx
      ext l
      rcases coord_eq_or_eq_other k l with rfl | rfl
      · exact congrArg Prod.fst hij
      · exact congrArg Prod.snd hij
    have hcoord (i : S) : aa i ∈ Set.Icc 0 1 ∧ bb i ∈ Set.Icc 0 1 ∧ |cc i| ≤ 1 := by
      refine ⟨hbox i k, hbox i ((1 - k)), ?_⟩
      dsimp [cc]
      rw [abs_div, div_le_iff₀ (abs_pos.mpr (hdir i)), one_mul]
      exact hS i i.property
    obtain ⟨i, j, hij, hbound⟩ := H S hs aa bb cc hinj hcoord
    refine ⟨i, j, fun h => hij (Subtype.ext h), ?_⟩
    refine (infDist_le_residual (x i) (x j) (d j) k (hdir j)).trans (hbound.trans ?_)
    have hrate : (Fintype.card S : ℝ) ^ (-(2 / 3 : ℝ) + η) ≤
        2 * (m : ℝ) ^ (-a) := by
      rw [Fintype.card_coe, show -(2 / 3 : ℝ) + η = -a by dsimp [a]; ring]
      exact rpow_subset_rate (by omega) (by rw [Fintype.card_coe] at hs; omega) hsize ha ha'
    calc
      _ ≤ C * (2 * (m : ℝ) ^ (-a)) := mul_le_mul_of_nonneg_left hrate hC.le
      _ = (2 * C) * (m : ℝ) ^ (-a) := by ring
      _ ≤ max (2 * C) 6 * (m : ℝ) ^ (-(2 / 3 : ℝ) + ε) :=
        mul_le_mul (le_max_left _ _) hr (Real.rpow_nonneg hm0 _) (by positivity)
  · let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, by omega⟩
    refine ⟨i, j, by intro h; have := congrArg Fin.val h; contradiction, ?_⟩
    have hdist : Metric.infDist (x i)
        (AffineSubspace.mk' (x j) (ℝ ∙ d j) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ≤ 2 :=
      (Metric.infDist_le_dist_of_mem (AffineSubspace.self_mem_mk' (x j) (ℝ ∙ d j))).trans
        (square_dist_le_two _ _ (hbox _) (hbox _))
    have h3 : (m : ℝ) ≤ 3 := by exact_mod_cast (show m ≤ 3 by omega)
    have hpow : (m : ℝ) ^ a ≤ 3 := by
      calc
        (m : ℝ) ^ a ≤ (m : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 ha'
        _ = m := Real.rpow_one _
        _ ≤ 3 := h3
    have h2 : (2 : ℝ) ≤ 6 * (m : ℝ) ^ (-a) := by
      rw [Real.rpow_neg hm0, ← div_eq_mul_inv, le_div_iff₀
        (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < m) a)]
      linarith
    exact hdist.trans (h2.trans
      (mul_le_mul (le_max_right _ _) hr (Real.rpow_nonneg hm0 _) (by positivity)))


end OMA.Erdos507DominantChart

namespace OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1

/-- The incidence estimate for distinct lattice points with slopes on the same mesh.
The integer residual is the vertical distance multiplied by the denominator squared. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ (I : Type) [Fintype I], 2 ≤ Fintype.card I →
    let q := Fintype.card I
    ∀ A B S : I → ℤ,
    Function.Injective (fun i => (A i, B i)) →
    (∀ i, 0 ≤ A i ∧ A i ≤ q ∧ 0 ≤ B i ∧ B i ≤ q ∧ -(q : ℤ) ≤ S i ∧ S i ≤ q) →
    ∃ i j, i ≠ j ∧
      (((q : ℤ) * (B i - B j) - S j * (A i - A j)).natAbs : ℝ) ≤
        (q : ℝ)^2 * (C * (Fintype.card I : ℝ) ^ (-(2 / 3 : ℝ) + ε))

/-- Rounding on any fixed grid preserves the coordinate and slope bounds and approximates each entry. -/
def H2 : Prop :=
  ∀ (I : Type) (q : ℕ), 0 < q →
  ∀ a b s : I → ℝ,
  (∀ i, a i ∈ Set.Icc (0 : ℝ) 1 ∧ b i ∈ Set.Icc (0 : ℝ) 1 ∧ |s i| ≤ 1) →
  ∃ A B S : I → ℤ,
    (∀ i, 0 ≤ A i ∧ A i ≤ q ∧ 0 ≤ B i ∧ B i ≤ q ∧ -(q : ℤ) ≤ S i ∧ S i ≤ q) ∧
    ∀ i, |a i - (A i : ℝ) / q| < 1 / (q : ℝ) ∧
      |b i - (B i : ℝ) / q| < 1 / (q : ℝ) ∧ |s i - (S i : ℝ) / q| < 1 / (q : ℝ)

section

private theorem abs_residual_error
    {a₀ a₁ b₀ b₁ s A₀ A₁ B₀ B₁ S δ : ℝ}
    (hA₀ : |a₀ - A₀| < δ) (hA₁ : |a₁ - A₁| < δ)
    (hB₀ : |b₀ - B₀| < δ) (hB₁ : |b₁ - B₁| < δ)
    (hS : |s - S| < δ) (hs : |s| ≤ 1) (hA : |A₀ - A₁| ≤ 1) :
    |(b₀ - b₁ - s * (a₀ - a₁)) - (B₀ - B₁ - S * (A₀ - A₁))| < 5 * δ := by
  have hA' : |(a₀ - A₀) - (a₁ - A₁)| < 2 * δ :=
    (abs_sub _ _).trans_lt (by linarith only [hA₀, hA₁])
  have hB' : |(b₀ - B₀) - (b₁ - B₁)| < 2 * δ :=
    (abs_sub _ _).trans_lt (by linarith only [hB₀, hB₁])
  have hp : |s * ((a₀ - A₀) - (a₁ - A₁))| < 2 * δ := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans_eq (one_mul _)).trans_lt hA'
  have hq : |(s - S) * (A₀ - A₁)| < δ := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left hA (abs_nonneg _)).trans_eq (mul_one _)).trans_lt hS
  rw [show (b₀ - b₁ - s * (a₀ - a₁)) - (B₀ - B₁ - S * (A₀ - A₁)) =
      ((b₀ - B₀) - (b₁ - B₁)) - (s * ((a₀ - A₀) - (a₁ - A₁)) + (s - S) * (A₀ - A₁))
    by ring]
  calc
    _ ≤ |(b₀ - B₀) - (b₁ - B₁)| +
        |s * ((a₀ - A₀) - (a₁ - A₁)) + (s - S) * (A₀ - A₁)| := abs_sub _ _
    _ ≤ |(b₀ - B₀) - (b₁ - B₁)| +
        (|s * ((a₀ - A₀) - (a₁ - A₁))| + |(s - S) * (A₀ - A₁)|) :=
      add_le_add_right (abs_add_le _ _) _
    _ < 5 * δ := by linarith only [hB', hp, hq]

private theorem scalar_of_grid (hGrid : H1) (hApprox : H2) : (
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (I : Type) [Fintype I], 2 ≤ Fintype.card I →
      ∀ a b c : I → ℝ, Function.Injective (fun i => (a i, b i)) →
      (∀ i, a i ∈ Set.Icc (0 : ℝ) 1 ∧ b i ∈ Set.Icc (0 : ℝ) 1 ∧ |c i| ≤ 1) →
      ∃ i j, i ≠ j ∧
        |b i - b j - c j * (a i - a j)| ≤ C * (Fintype.card I : ℝ) ^ (-(2 / 3 : ℝ) + ε)
) := by
  classical
  intro ε hε
  obtain ⟨C, hC, hCbound⟩ := hGrid ε hε
  refine ⟨C + 5, by positivity, ?_⟩
  intro I _ hI a b s _ hbox
  let q := Fintype.card I
  let R : ℝ := (q : ℝ) ^ (-(2 / 3 : ℝ) + ε)
  have hq : 0 < q := by dsimp [q]; omega
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR : 0 < R := Real.rpow_pos_of_pos hqR _
  have hmesh : 1 / (q : ℝ) ≤ R := by
    simpa only [Real.rpow_neg_one, one_div] using
      (Real.rpow_le_rpow_of_exponent_le hq1
        (show (-1 : ℝ) ≤ -(2 / 3 : ℝ) + ε by linarith only [hε]))
  obtain ⟨A, B, S, hbox', hclose⟩ := hApprox I q hq a b s hbox
  have hex : ∃ i j, i ≠ j ∧
      (((q : ℤ) * (B i - B j) - S j * (A i - A j)).natAbs : ℝ) ≤
        (q : ℝ)^2 * (C * R) := by
    by_cases hinj : Function.Injective (fun i => (A i, B i))
    · exact hCbound I hI A B S hinj hbox'
    · have hcollision : ∃ i j, (A i, B i) = (A j, B j) ∧ i ≠ j := by
        by_contra hnone
        apply hinj
        intro i j he
        by_contra hne
        exact hnone ⟨i, j, he, hne⟩
      obtain ⟨i, j, he, hij⟩ := hcollision
      refine ⟨i, j, hij, ?_⟩
      have ha : A i = A j := congrArg Prod.fst he
      have hb : B i = B j := congrArg Prod.snd he
      simp only [ha, hb, sub_self, mul_zero, Int.natAbs_zero, Nat.cast_zero]
      positivity
  obtain ⟨i, j, hij, hbound⟩ := hex
  let U (i : I) : ℝ := (A i : ℝ) / q
  let V (i : I) : ℝ := (B i : ℝ) / q
  let W (i : I) : ℝ := (S i : ℝ) / q
  have hqSq : (0 : ℝ) < (q : ℝ)^2 := by positivity
  have hnum : (q : ℝ)^2 * (V i - V j - W j * (U i - U j)) =
      ((((q : ℤ) * (B i - B j) - S j * (A i - A j)) : ℤ) : ℝ) := by
    dsimp [U, V, W]
    push_cast
    field_simp [hqR.ne']
  have hbound' : |V i - V j - W j * (U i - U j)| ≤ C * R := by
    apply le_of_mul_le_mul_left _ hqSq
    rw [Nat.cast_natAbs, Int.cast_abs, ← hnum, abs_mul, abs_of_nonneg hqSq.le] at hbound
    exact hbound
  have hu (i : I) : U i ∈ Set.Icc 0 1 := by
    refine ⟨div_nonneg (by exact_mod_cast (hbox' i).1) hqR.le, (div_le_iff₀ hqR).2 ?_⟩
    simpa only [one_mul] using (show (A i : ℝ) ≤ q by exact_mod_cast (hbox' i).2.1)
  have hu' : |U i - U j| ≤ 1 := abs_le.mpr
    ⟨by linarith only [(hu i).1, (hu j).2], by linarith only [(hu i).2, (hu j).1]⟩
  have herr := abs_residual_error (hclose i).1 (hclose j).1 (hclose i).2.1
    (hclose j).2.1 (hclose j).2.2 (hbox j).2.2 hu'
  refine ⟨i, j, hij, ?_⟩
  calc
    _ ≤ |(b i - b j - s j * (a i - a j)) - (V i - V j - W j * (U i - U j))| +
        |V i - V j - W j * (U i - U j)| := by
      simpa only [sub_add_cancel] using
        (abs_add_le ((b i - b j - s j * (a i - a j)) - (V i - V j - W j * (U i - U j)))
          (V i - V j - W j * (U i - U j)))
    _ ≤ (C + 5) * R := by linarith only [herr, hbound', hmesh]

theorem main : H1 → H2 →
    OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1.H1 := by
  intro hGrid hApprox
  exact OMA.Erdos507DominantChart.unit_square_of_scalar (scalar_of_grid hGrid hApprox)

end

end OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1_H1_R1
