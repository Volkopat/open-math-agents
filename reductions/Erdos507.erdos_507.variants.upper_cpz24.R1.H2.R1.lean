import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Tactic.Linarith

/-!
The unit-square estimate is Corollary 1.2 of Cohen, Pohoata and Zakharov,
https://arxiv.org/html/2409.07658v2. Orthogonal projection gives a line
parameter. Rescaling the disk to the square and accounting for the floor
of n/8 change the constant by at most an absolute factor. A separate
limit step combines the fixed-exponent estimates.
-/

namespace OMA.Erdos507UnitSquareTransfer

private theorem abs_coord_le_norm (z : EuclideanSpace ℝ (Fin 2)) (k : Fin 2) :
    |z k| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z k

/-- Euclidean distance to the line through a point in a given direction is
attained by some parameter in that direction. -/
theorem exists_parameter_of_infDist_le (z a d : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    (h : Metric.infDist z
      (AffineSubspace.mk' a (ℝ ∙ d) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ≤ R) :
    ∃ t : ℝ, ‖z - a - t • d‖ ≤ R := by
  let L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)) := AffineSubspace.mk' a (ℝ ∙ d)
  let _ : Nonempty L := ⟨⟨a, AffineSubspace.self_mem_mk' a _⟩⟩
  let p : L := EuclideanGeometry.orthogonalProjection L z
  have hp : (p : EuclideanSpace ℝ (Fin 2)) - a ∈ ℝ ∙ d :=
    AffineSubspace.mem_mk'.mp p.property
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hp
  have hp' : (p : EuclideanSpace ℝ (Fin 2)) = t • d + a := sub_eq_iff_eq_add.mp ht.symm
  have hd : dist z (p : EuclideanSpace ℝ (Fin 2)) ≤ R :=
    (EuclideanGeometry.dist_orthogonalProjection_eq_infDist L z).le.trans h
  refine ⟨t, ?_⟩
  rw [sub_sub, add_comm a (t • d), ← hp', ← dist_eq_norm]
  exact hd

/-- A norm estimate on the unit square gives twice that radius on the disk,
in each coordinate. The dilation changes the line parameter by a factor of two. -/
theorem disk_coordinate_bound_of_square_bound {m : ℕ} {R : ℝ}
    (hsquare : ∀ x d : Fin m → EuclideanSpace ℝ (Fin 2),
      Function.Injective x → (∀ i k, x i k ∈ Set.Icc (0 : ℝ) 1) →
      (∀ i, d i ≠ 0) → ∃ i j, i ≠ j ∧ ∃ t : ℝ, ‖x i - x j - t • d j‖ ≤ R)
    (x d : Fin m → EuclideanSpace ℝ (Fin 2))
    (hx : Function.Injective x) (hball : ∀ i, x i ∈ Metric.closedBall 0 1)
    (hdir : ∀ i, d i ≠ 0) :
    ∃ i j, i ≠ j ∧ ∃ t : ℝ, ∀ k : Fin 2,
      |x i k - x j k - t * d j k| ≤ 2 * R := by
  let y (i : Fin m) : EuclideanSpace ℝ (Fin 2) :=
    WithLp.toLp 2 fun k => (x i k + 1) / 2
  have hyinj : Function.Injective y := by
    intro i j hij
    apply hx
    ext k
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z k) hij
    change (x i k + 1) / 2 = (x j k + 1) / 2 at h
    linarith only [h]
  have hy : ∀ i k, y i k ∈ Set.Icc (0 : ℝ) 1 := by
    intro i k
    have hnorm : ‖x i‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hball i
    have h := (abs_coord_le_norm (x i) k).trans hnorm
    rw [abs_le] at h
    change 0 ≤ (x i k + 1) / 2 ∧ (x i k + 1) / 2 ≤ 1
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  obtain ⟨i, j, hij, t, ht⟩ := hsquare y d hyinj hy hdir
  refine ⟨i, j, hij, 2 * t, fun k => ?_⟩
  have h := (abs_coord_le_norm (y i - y j - t • d j) k).trans ht
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h
  change |(x i k + 1) / 2 - (x j k + 1) / 2 - t * d j k| ≤ R at h
  rw [show x i k - x j k - (2 * t) * d j k =
    2 * ((x i k + 1) / 2 - (x j k + 1) / 2 - t * d j k) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

private theorem floor_eighth_rate {n : ℕ} (hn : 16 ≤ n) {ε : ℝ}
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 3) :
    ((n / 8 : ℕ) : ℝ) ^ (-(2 / 3 : ℝ) + ε) ≤
      16 * (n : ℝ) ^ (-(2 / 3 : ℝ) + ε) := by
  let m := n / 8
  let a := (2 / 3 : ℝ) - ε
  have ha : 0 ≤ a := by dsimp [a]; linarith only [hε']
  have ha₁ : a ≤ 1 := by dsimp [a]; linarith only [hε]
  have hm : 0 < m := by dsimp [m]; omega
  have hnm : n ≤ 16 * m := by dsimp [m]; omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnmR : (n : ℝ) ≤ 16 * (m : ℝ) := by exact_mod_cast hnm
  have hconst : (16 : ℝ) ^ a ≤ 16 := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 16) ha₁)
  have hpower : (n : ℝ) ^ a ≤ 16 * (m : ℝ) ^ a := by
    calc
      _ ≤ (16 * (m : ℝ)) ^ a := Real.rpow_le_rpow hnR.le hnmR ha
      _ = (16 : ℝ) ^ a * (m : ℝ) ^ a := Real.mul_rpow (by norm_num) hmR.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hmR.le _)
  have hmpow := Real.rpow_pos_of_pos hmR a
  have hnpow := Real.rpow_pos_of_pos hnR a
  change (m : ℝ) ^ (-(2 / 3 : ℝ) + ε) ≤ 16 * (n : ℝ) ^ (-(2 / 3 : ℝ) + ε)
  rw [show -(2 / 3 : ℝ) + ε = -a by dsimp [a]; ring,
    Real.rpow_neg hmR.le, Real.rpow_neg hnR.le, ← div_eq_mul_inv]
  apply (le_div_iff₀ hnpow).2
  calc
    _ ≤ ((m : ℝ) ^ a)⁻¹ * (16 * (m : ℝ) ^ a) :=
      mul_le_mul_of_nonneg_left hpower (inv_nonneg.mpr hmpow.le)
    _ = 16 := by rw [mul_left_comm, inv_mul_cancel₀ hmpow.ne', mul_one]

/-- Transfer the fixed-exponent square estimate to the exact coordinate error
and number of points of Erdős 507's assigned-line hypothesis. -/
theorem fixed_epsilon_disk_of_square
    (hsquare : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
      ∀ x d : Fin m → EuclideanSpace ℝ (Fin 2),
        Function.Injective x → (∀ i k, x i k ∈ Set.Icc (0 : ℝ) 1) →
        (∀ i, d i ≠ 0) →
        ∃ i j, i ≠ j ∧ ∃ t : ℝ, ‖x i - x j - t • d j‖ ≤ C * (m : ℝ) ^ (-(2 / 3 : ℝ) + ε))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n → ∀ x d : Fin (n / 8) → EuclideanSpace ℝ (Fin 2),
      Function.Injective x → (∀ i, x i ∈ Metric.closedBall 0 1) →
      (∀ i, d i ≠ 0) → ∃ i j, i ≠ j ∧ ∃ t : ℝ, ∀ k : Fin 2,
        |x i k - x j k - t * d j k| ≤ C / (n : ℝ) ^ (2 / 3 : ℝ) * (n : ℝ) ^ ε := by
  let σ := min ε (1 / 3)
  have hσ : 0 < σ := lt_min hε (by norm_num)
  have hσ₁ : σ ≤ 1 / 3 := min_le_right _ _
  have hσε : σ ≤ ε := min_le_left _ _
  obtain ⟨C, hC, hsq⟩ := hsquare σ hσ
  refine ⟨32 * C, mul_pos (by norm_num) hC, ?_⟩
  intro n hn x d hx hb hd
  have hm : 2 ≤ n / 8 := by omega
  obtain ⟨i, j, hij, t, ht⟩ := disk_coordinate_bound_of_square_bound (hsq (n / 8) hm) x d hx hb hd
  refine ⟨i, j, hij, t, fun k => (ht k).trans ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  calc
    _ ≤ 2 * (C * (16 * (n : ℝ) ^ (-(2 / 3 : ℝ) + σ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (floor_eighth_rate hn hσ.le hσ₁) hC.le) (by norm_num)
    _ = (32 * C) * (n : ℝ) ^ (-(2 / 3 : ℝ) + σ) := by ring
    _ ≤ (32 * C) * (n : ℝ) ^ (-(2 / 3 : ℝ) + ε) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn₁ (add_le_add le_rfl hσε)) (by positivity)
    _ = _ := by
      rw [Real.rpow_add hnR, Real.rpow_neg hnR.le]
      ring

end OMA.Erdos507UnitSquareTransfer

namespace OMA.Erdos507IncidenceAssembly

open Filter Topology

theorem vanishing_incidence
    (transfer : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 16 ≤ n →
      ∀ x d : Fin (n / 8) → EuclideanSpace ℝ (Fin 2), Function.Injective x →
        (∀ i, x i ∈ Metric.closedBall 0 1) → (∀ i, d i ≠ 0) →
        ∃ i j, i ≠ j ∧ ∃ t : ℝ, ∀ k : Fin 2,
          |x i k - x j k - t * d j k| ≤ C / (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ε)
    (assemble : ∀ W : ℕ → ℝ → Prop,
      (∀ n, ∀ ⦃a b : ℝ⦄, a ≤ b → W n a → W n b) →
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n in atTop, W n (C * (n : ℝ) ^ ε)) →
      ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop, W n ((n : ℝ) ^ e n)) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∃ B : ℝ, 0 < B ∧
      ∀ᶠ n : ℕ in atTop, ∀ x d : Fin (n / 8) → EuclideanSpace ℝ (Fin 2),
        Function.Injective x → (∀ i, x i ∈ Metric.closedBall 0 1) → (∀ i, d i ≠ 0) →
        ∃ i j, i ≠ j ∧ ∃ t : ℝ, ∀ k : Fin 2,
          |x i k - x j k - t * d j k| ≤ B / (n : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ e n := by
  let W (n : ℕ) (r : ℝ) :=
    ∀ x d : Fin (n / 8) → EuclideanSpace ℝ (Fin 2),
      Function.Injective x → (∀ i, x i ∈ Metric.closedBall 0 1) → (∀ i, d i ≠ 0) →
      ∃ i j, i ≠ j ∧ ∃ t : ℝ, ∀ k : Fin 2,
        |x i k - x j k - t * d j k| ≤ r / (n : ℝ) ^ ((2 : ℝ) / 3)
  have hmono : ∀ n, ∀ ⦃a b : ℝ⦄, a ≤ b → W n a → W n b := by
    intro n a b hab ha x d hx hxBall hd
    obtain ⟨i, j, hij, t, ht⟩ := ha x d hx hxBall hd
    exact ⟨i, j, hij, t, fun k => (ht k).trans (div_le_div_of_nonneg_right hab
      (Real.rpow_nonneg (Nat.cast_nonneg n) _))⟩
  have hsmall (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, ∀ᶠ n in atTop, W n (C * (n : ℝ) ^ ε) := by
    obtain ⟨C, _, hC⟩ := transfer ε hε
    refine ⟨C, ?_⟩
    filter_upwards [eventually_ge_atTop (16 : ℕ)] with n hn
    intro x d hx hxBall hd
    simpa only [div_mul_eq_mul_div] using hC n hn x d hx hxBall hd
  obtain ⟨e, he, hh⟩ := assemble W hmono hsmall
  refine ⟨e, he, 1, zero_lt_one, ?_⟩
  filter_upwards [hh] with n hw
  intro x d hx hxBall hd
  simpa only [div_mul_eq_mul_div, one_mul] using hw x d hx hxBall hd

end OMA.Erdos507IncidenceAssembly

namespace OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1

open Filter Topology

/-- The fixed-exponent unit-square incidence estimate. -/
def H1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 2 ≤ m →
    ∀ x d : Fin m → EuclideanSpace ℝ (Fin 2),
      Function.Injective x → (∀ i k, x i k ∈ Set.Icc (0 : ℝ) 1) → (∀ i, d i ≠ 0) →
      ∃ i j, i ≠ j ∧ Metric.infDist (x i)
        (AffineSubspace.mk' (x j) (ℝ ∙ d j) : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) ≤
          C * (m : ℝ) ^ (-(2 / 3 : ℝ) + ε)

/-- Monotone bounds at all fixed powers give an eventual bound with a vanishing exponent. -/
def H2 : Prop :=
  ∀ W : ℕ → ℝ → Prop,
    (∀ n, ∀ ⦃a b : ℝ⦄, a ≤ b → W n a → W n b) →
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ᶠ n in atTop, W n (C * (n : ℝ) ^ ε)) →
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧ ∀ᶠ n in atTop, W n ((n : ℝ) ^ e n)

theorem main : H1 → H2 → OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1.H2 := by
  intro hsquare hlimit
  apply OMA.Erdos507IncidenceAssembly.vanishing_incidence _ hlimit
  apply OMA.Erdos507UnitSquareTransfer.fixed_epsilon_disk_of_square
  intro ε hε
  obtain ⟨C, hC, h⟩ := hsquare ε hε
  refine ⟨C, hC, ?_⟩
  intro m hm x d hx hcoords hdir
  obtain ⟨i, j, hij, hdist⟩ := h m hm x d hx hcoords hdir
  exact ⟨i, j, hij, OMA.Erdos507UnitSquareTransfer.exists_parameter_of_infDist_le _ _ _ _ hdist⟩

end OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1_H2_R1
