import OMAReductions.R_Green100_green_100_variants_operator_norm_R1_H1_R1_H1_R1
import Mathlib

/-!
Relative Property (FH) for the pair consisting of the integral two-dimensional
affine group and its translation lattice. Credit: @AlfredMelson.

The relative spectral-gap argument below is from the merged Green100 part ii
proof by @zzzfu411 (commit 31c74f617). We apply it to the two standard integral
shears. For a Hilbert cocycle c, its orbit defines the positive semidefinite
kernel exp(-t ||c(g)-c(h)||²). Its cyclic representation turns the spectral
gap into an inequality for Gaussian displacements. Taking the right derivative
at zero bounds the original cocycle uniformly on all translations.
-/

/- Relative spectral gap, excerpted from the proof of Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H2 by @zzzfu411 (commit 31c74f617). -/
namespace OMA.Green100H2

open Filter Matrix Finset
open scoped Topology ComplexOrder BigOperators Matrix InnerProductSpace commutatorElement

noncomputable section

/- ### 1. Unitary representations, invariant subspaces, and spectral gap -/

section AbstractGap

lemma hasOrthProj_of_isClosed {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] {K : Submodule ℂ V} (hK : IsClosed (K : Set V)) :
    K.HasOrthogonalProjection := by
  have : CompleteSpace K := hK.completeSpace_coe
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace K

lemma rep_mul {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (g h : Γ) (v : V) : π (g * h) v = π g (π h v) := by
  rw [map_mul]; rfl

lemma rep_one {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (v : V) : π 1 v = v := by
  rw [map_one]; rfl

lemma rep_inv_mul {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (g : Γ) (v : V) : π g⁻¹ (π g v) = v := by
  rw [← rep_mul, inv_mul_cancel, rep_one]

lemma rep_mul_inv {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (g : Γ) (v : V) : π g (π g⁻¹ v) = v := by
  rw [← rep_mul, mul_inv_cancel, rep_one]

lemma rep_inner_inv {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (g : Γ) (u v : V) : ⟪u, π g v⟫_ℂ = ⟪π g⁻¹ u, v⟫_ℂ := by
  have := (π g⁻¹).inner_map_map u (π g v)
  rw [rep_inv_mul] at this
  exact this.symm

/-- The closed subspace of vectors fixed by a subgroup `H` under a unitary representation `π`. -/
def invSubspace {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (H : Subgroup Γ) : Submodule ℂ V where
  carrier := {v : V | ∀ g ∈ H, π g v = v}
  add_mem' {u v} hu hv g hg := by rw [map_add, hu g hg, hv g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c {v} hv g hg := by rw [map_smul, hv g hg]

lemma mem_invSubspace {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {π : Γ →* V ≃ₗᵢ[ℂ] V} {H : Subgroup Γ} {v : V} :
    v ∈ invSubspace π H ↔ ∀ g ∈ H, π g v = v := Iff.rfl

lemma isClosed_invSubspace {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (H : Subgroup Γ) : IsClosed (invSubspace π H : Set V) := by
  have h : (invSubspace π H : Set V) = ⋂ g ∈ H, {v : V | π g v = v} := by
    ext v; simp [invSubspace]
  rw [h]
  exact isClosed_biInter fun g _ => isClosed_eq (π g).continuous continuous_id

instance instHasOrthogonalProjection_invSubspace {Γ V : Type*} [Group Γ]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (H : Subgroup Γ) :
    (invSubspace π H).HasOrthogonalProjection :=
  hasOrthProj_of_isClosed (isClosed_invSubspace π H)

lemma invSubspace_anti {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {H K : Subgroup Γ} (hHK : H ≤ K) :
    invSubspace π K ≤ invSubspace π H :=
  fun _ hv g hg => hv g (hHK hg)

lemma invSubspace_closure {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (S : Set Γ) {v : V} :
    v ∈ invSubspace π (Subgroup.closure S) ↔ ∀ s ∈ S, π s v = v := by
  refine ⟨fun h s hs => h s (Subgroup.subset_closure hs), fun h g hg => ?_⟩
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h x hx
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact (congrArg (π x) hy).trans hx
  | inv x _ hx =>
    have := congrArg (π x⁻¹) hx
    rw [← LinearIsometryEquiv.trans_apply, ← LinearIsometryEquiv.mul_def, ← map_mul,
      inv_mul_cancel, map_one] at this
    exact this.symm

lemma invSubspace_sup {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (H K : Subgroup Γ) :
    invSubspace π (H ⊔ K) = invSubspace π H ⊓ invSubspace π K := by
  ext v
  rw [Subgroup.sup_eq_closure, invSubspace_closure]
  simp only [Set.mem_union, SetLike.mem_coe, Submodule.mem_inf, mem_invSubspace]
  exact ⟨fun h => ⟨fun g hg => h g (Or.inl hg), fun g hg => h g (Or.inr hg)⟩,
    fun ⟨hH, hK⟩ g hg => hg.elim (hH g) (hK g)⟩

lemma invSubspace_mem_of_norm {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {H : Subgroup Γ} {g : Γ} (hg : ∀ h ∈ H, g⁻¹ * h * g ∈ H)
    {v : V} (hv : v ∈ invSubspace π H) : π g v ∈ invSubspace π H := by
  intro h hh
  have h1 : h * g = g * (g⁻¹ * h * g) := by group
  calc π h (π g v) = π (h * g) v := by rw [map_mul]; rfl
    _ = π (g * (g⁻¹ * h * g)) v := by rw [h1]
    _ = π g (π (g⁻¹ * h * g) v) := by rw [map_mul]; rfl
    _ = π g v := by rw [hv _ (hg h hh)]

lemma invSubspace_orth_mem_of_norm {Γ V : Type*} [Group Γ] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (π : Γ →* V ≃ₗᵢ[ℂ] V) {H : Subgroup Γ} {g : Γ}
    (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H) {v : V} (hv : v ∈ (invSubspace π H)ᗮ) :
    π g v ∈ (invSubspace π H)ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  have hu' : π g⁻¹ u ∈ invSubspace π H :=
    invSubspace_mem_of_norm π (fun h hh => by simpa using hg h hh) hu
  have h1 : ⟪u, π g v⟫_ℂ = ⟪π g⁻¹ u, v⟫_ℂ := rep_inner_inv π g u v
  rw [h1, hv _ hu']

lemma starProjection_invSubspace_comm {Γ V : Type*} [Group Γ] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Γ →* V ≃ₗᵢ[ℂ] V) {H : Subgroup Γ} {g : Γ}
    (hg1 : ∀ h ∈ H, g⁻¹ * h * g ∈ H) (hg2 : ∀ h ∈ H, g * h * g⁻¹ ∈ H) (v : V) :
    (invSubspace π H).starProjection (π g v) = π g ((invSubspace π H).starProjection v) := by
  set K := invSubspace π H
  refine K.eq_starProjection_of_mem_orthogonal
    (invSubspace_mem_of_norm π hg1 (Submodule.coe_mem _)) ?_
  rw [← map_sub]
  exact invSubspace_orth_mem_of_norm π hg2 (K.sub_starProjection_mem_orthogonal v)

/-- If a closed subspace `K` is invariant under a unitary `U` and its inverse `U.symm`,
then its orthogonal projection commutes with `U`. -/
lemma starProjection_comm_of_invariant {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (U : V ≃ₗᵢ[ℂ] V) (K : Submodule ℂ V) [K.HasOrthogonalProjection]
    (hK : ∀ v ∈ K, U v ∈ K) (hKinv : ∀ v ∈ K, U.symm v ∈ K) (v : V) :
    K.starProjection (U v) = U (K.starProjection v) := by
  refine K.eq_starProjection_of_mem_orthogonal (hK _ (Submodule.coe_mem _)) ?_
  rw [← map_sub, Submodule.mem_orthogonal]
  intro u hu
  have h1 := U.symm.inner_map_map u (U (v - K.starProjection v))
  rw [U.symm_apply_apply] at h1
  rw [← h1]
  exact (Submodule.mem_orthogonal K _).mp (K.sub_starProjection_mem_orthogonal v) (U.symm u) (hKinv u hu)

/-- Fixed subspace of a single unitary operator `U : V ≃ₗᵢ[ℂ] V`. -/
def fixedSubspace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : V ≃ₗᵢ[ℂ] V) : Submodule ℂ V where
  carrier := {v : V | U v = v}
  add_mem' {u v} hu hv := by change U (u + v) = u + v; rw [map_add, hu, hv]
  zero_mem' := map_zero U
  smul_mem' c {v} hv := by change U (c • v) = c • v; rw [map_smul, hv]

lemma isClosed_fixedSubspace {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : V ≃ₗᵢ[ℂ] V) : IsClosed (fixedSubspace U : Set V) :=
  isClosed_eq U.continuous continuous_id

instance instHasOrthogonalProjection_fixedSubspace {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (U : V ≃ₗᵢ[ℂ] V) :
    (fixedSubspace U).HasOrthogonalProjection :=
  hasOrthProj_of_isClosed (isClosed_fixedSubspace U)

/-- Von Neumann Mean Ergodic Theorem for a single unitary operator `U : V ≃ₗᵢ[ℂ] V`. -/
lemma mean_ergodic_theorem {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (U : V ≃ₗᵢ[ℂ] V) (v : V) :
    Tendsto (fun N : ℕ => ((N : ℂ)⁻¹) • ∑ k ∈ Finset.range N, (U ^ k) v)
      atTop (𝓝 ((fixedSubspace U).starProjection v)) := by
  let A : ℕ → V → V := fun N w => ((N : ℂ)⁻¹) • ∑ k ∈ Finset.range N, (U ^ k) w
  have hA_norm : ∀ (N : ℕ) (w : V), ‖A N w‖ ≤ ‖w‖ := by
    intro N w
    dsimp only [A]
    by_cases hN : N = 0
    · subst hN; simp
    · have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      rw [norm_smul, norm_inv, Complex.norm_natCast]
      have hsum : ‖∑ k ∈ Finset.range N, (U ^ k) w‖ ≤ (N : ℝ) * ‖w‖ := by
        calc ‖∑ k ∈ Finset.range N, (U ^ k) w‖
            ≤ ∑ k ∈ Finset.range N, ‖(U ^ k) w‖ := norm_sum_le _ _
          _ = ∑ _k ∈ Finset.range N, ‖w‖ := Finset.sum_congr rfl fun k _ => (U ^ k).norm_map w
          _ = (N : ℝ) * ‖w‖ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc (N : ℝ)⁻¹ * ‖∑ k ∈ Finset.range N, (U ^ k) w‖
          ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ‖w‖) := mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = ‖w‖ := by field_simp [ne_of_gt hNpos]
  have hA_add : ∀ (N : ℕ) (w₁ w₂ : V), A N (w₁ + w₂) = A N w₁ + A N w₂ := fun N w₁ w₂ => by
    dsimp only [A]
    simp_rw [map_add, Finset.sum_add_distrib, smul_add]
  have hA_fix : ∀ (N : ℕ), 1 ≤ N → ∀ w ∈ fixedSubspace U, A N w = w := by
    intro N hN w hw
    have hpow : ∀ k : ℕ, (U ^ k) w = w := fun k => by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ']
        change U ((U ^ k) w) = w
        rw [ih]; exact hw
    dsimp only [A]
    have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp_rw [hpow, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ hN0, one_smul]
  have hA_cob : ∀ (N : ℕ) (u : V), 1 ≤ N → ‖A N (U u - u)‖ ≤ 2 * ‖u‖ / (N : ℝ) := by
    intro N u hN
    have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
    have htele : ∑ k ∈ Finset.range N, (U ^ k) (U u - u) = (U ^ N) u - u := by
      have hterm : ∀ k : ℕ, (U ^ k) (U u - u) = (U ^ (k + 1)) u - (U ^ k) u := fun k => by
        rw [map_sub, pow_succ]; rfl
      simp_rw [hterm]
      rw [Finset.sum_range_sub (fun k => (U ^ k) u) N]
      rfl
    dsimp only [A]
    rw [htele, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hNpos)
    calc ‖(U ^ N) u - u‖ ≤ ‖(U ^ N) u‖ + ‖u‖ := norm_sub_le _ _
      _ = 2 * ‖u‖ := by rw [(U ^ N).norm_map]; ring
  let R : Submodule ℂ V := LinearMap.range (U.toLinearMap - LinearMap.id)
  have hR_orth : Rᗮ = fixedSubspace U := by
    ext w
    rw [Submodule.mem_orthogonal]
    constructor
    · intro hw
      have h0 : ⟪U w - w, w⟫_ℂ = 0 := hw (U w - w) ⟨w, rfl⟩
      have hsq : ‖U w - w‖ ^ 2 = 0 := by
        have h1 : ‖U w - w‖ ^ 2 = ‖U w‖ ^ 2 - 2 * RCLike.re ⟪U w, w⟫_ℂ + ‖w‖ ^ 2 := norm_sub_sq (𝕜 := ℂ) _ _
        have h2 : RCLike.re ⟪U w, w⟫_ℂ = ‖w‖ ^ 2 := by
          have : ⟪U w, w⟫_ℂ - ⟪w, w⟫_ℂ = 0 := by rwa [← inner_sub_left]
          have heq : ⟪U w, w⟫_ℂ = ⟪w, w⟫_ℂ := sub_eq_zero.mp this
          rw [heq, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
        rw [h1, U.norm_map, h2]; ring
      exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
    · intro hw z hz
      obtain ⟨u, rfl⟩ := hz
      change ⟪U u - u, w⟫_ℂ = 0
      rw [inner_sub_left]
      have h1 : ⟪U u, w⟫_ℂ = ⟪u, w⟫_ℂ := by
        conv_lhs => rw [← (hw : U w = w)]
        exact U.inner_map_map u w
      rw [h1, sub_self]
  have hK_orth_eq : (fixedSubspace U)ᗮ = R.topologicalClosure := by
    have : R.topologicalClosure.HasOrthogonalProjection :=
      hasOrthProj_of_isClosed R.isClosed_topologicalClosure
    have h1 : R.topologicalClosureᗮ = fixedSubspace U := by
      rw [← hR_orth]
      apply le_antisymm
      · exact Submodule.orthogonal_le (Submodule.le_topologicalClosure R)
      · intro w hw
        rw [Submodule.mem_orthogonal] at hw ⊢
        intro z hz
        have hcl : IsClosed {t : V | ⟪t, w⟫_ℂ = 0} :=
          isClosed_eq (continuous_id.inner continuous_const) continuous_const
        exact (hcl.closure_subset_iff.mpr fun t ht => hw t ht) hz
    rw [← h1, Submodule.orthogonal_orthogonal]
  set p := (fixedSubspace U).starProjection v
  set v₂ := v - p
  have hv_split : v = p + v₂ := by dsimp only [v₂]; abel
  have hv₂_cl : v₂ ∈ R.topologicalClosure := by
    rw [← hK_orth_eq]; exact (fixedSubspace U).sub_starProjection_mem_orthogonal v
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨z, hzR, hz_ball⟩ := Metric.mem_closure_iff.mp hv₂_cl (ε / 2) (half_pos hε)
  obtain ⟨u, rfl⟩ := hzR
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (4 * ‖u‖ / ε)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₀ : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (by omega)
  have hdist : dist (A N v) p = ‖A N v₂‖ := by
    rw [dist_eq_norm, hv_split, hA_add, hA_fix N hN1 p (Submodule.coe_mem _), add_sub_cancel_left]
  rw [hdist]
  have hsplit2 : v₂ = (v₂ - (U u - u)) + (U u - u) := by abel
  have hle1 : ‖A N (v₂ - (U u - u))‖ < ε / 2 := by
    calc ‖A N (v₂ - (U u - u))‖ ≤ ‖v₂ - (U u - u)‖ := hA_norm N _
      _ = dist v₂ (U u - u) := (dist_eq_norm _ _).symm
      _ < ε / 2 := hz_ball
  have hle2 : ‖A N (U u - u)‖ < ε / 2 := by
    have h1 := hA_cob N u hN1
    have h2 : 4 * ‖u‖ / ε < (N : ℝ) := lt_of_lt_of_le hN₀ (by exact_mod_cast hNN₀)
    have h3 : 2 * ‖u‖ / (N : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hNpos]
      have h4 : 4 * ‖u‖ < (N : ℝ) * ε := (div_lt_iff₀ hε).mp h2
      linarith
    exact lt_of_le_of_lt h1 h3
  calc ‖A N v₂‖ = ‖A N (v₂ - (U u - u)) + A N (U u - u)‖ := by rw [← hA_add, ← hsplit2]
    _ ≤ ‖A N (v₂ - (U u - u))‖ + ‖A N (U u - u)‖ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add hle1 hle2
    _ = ε := add_halves ε


end AbstractGap
/- ### 5. Relative Property (T) for `(F₂ ⋉ ℤ², ℤ²)` and spectral gaps for `C`, `H`, and `Q` -/

section RelPropTF2Z2

open MeasureTheory

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

abbrev T2 : Type := UnitAddTorus (Fin 2)

/-- Clamp a real number to `[0, 1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min 1 t)

lemma continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

lemma clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

lemma clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_left _ _)

lemma clamp01_eq_zero {t : ℝ} (ht : t ≤ 0) : clamp01 t = 0 := by
  dsimp only [clamp01]; rw [min_eq_right (by linarith), max_eq_left ht]

lemma clamp01_eq_one {t : ℝ} (ht : 1 ≤ t) : clamp01 t = 1 := by
  dsimp only [clamp01]; rw [min_eq_left ht, max_eq_right zero_le_one]

/-- Distance to `0` on `ℝ / ℤ`, lifted continuously from `|·|` on `[-1/2, 1/2)`. -/
def torusAbs : UnitAddCircle → ℝ := AddCircle.liftIco (1 : ℝ) (-1 / 2) abs

lemma continuous_torusAbs : Continuous torusAbs :=
  AddCircle.liftIco_continuous (by norm_num) continuous_abs.continuousOn

lemma torusAbs_coe {x : ℝ} (hx : x ∈ Set.Ico (-1 / 2 : ℝ) (1 / 2)) :
    torusAbs (x : UnitAddCircle) = |x| := by
  have hx' : x ∈ Set.Ico (-1 / 2 : ℝ) (-1 / 2 + 1) := by
    rcases hx with ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  exact AddCircle.liftIco_coe_apply hx'

lemma exists_rep_Ico (t : UnitAddCircle) :
    ∃ x : ℝ, x ∈ Set.Ico (-1 / 2 : ℝ) (1 / 2) ∧ (x : UnitAddCircle) = t ∧ torusAbs t = |x| := by
  let y := AddCircle.equivIco (1 : ℝ) (-1 / 2) t
  have hy : y.1 ∈ Set.Ico (-1 / 2 : ℝ) (1 / 2) := by
    have h := y.2; exact ⟨h.1, by linarith [h.2]⟩
  have hcoe : (y.1 : UnitAddCircle) = t := AddCircle.coe_equivIco (p := (1 : ℝ)) (a := -1 / 2)
  refine ⟨y.1, hy, hcoe, ?_⟩
  rw [← hcoe, torusAbs_coe hy]

lemma torusAbs_nonneg (t : UnitAddCircle) : 0 ≤ torusAbs t := by
  obtain ⟨x, _, _, h⟩ := exists_rep_Ico t; rw [h]; exact abs_nonneg x

def torusN (p : T2) : ℝ := max (torusAbs (p 0)) (torusAbs (p 1))

lemma continuous_torusN : Continuous torusN :=
  (continuous_torusAbs.comp (continuous_apply 0)).max (continuous_torusAbs.comp (continuous_apply 1))

def coneH (u : ℝ) : ℝ := clamp01 (3 * u - 1)

lemma continuous_coneH : Continuous coneH :=
  continuous_clamp01.comp ((continuous_const.mul continuous_id).sub continuous_const)

lemma coneH_add_symm {u : ℝ} (_h0 : 0 ≤ u) (_h1 : u ≤ 1) : coneH u + coneH (1 - u) = 1 := by
  dsimp only [coneH, clamp01]
  by_cases ha : u ≤ 1 / 3
  · rw [min_eq_right (by linarith), max_eq_left (by linarith),
      min_eq_left (by linarith), max_eq_right (by norm_num)]; ring
  · by_cases hb : u ≤ 2 / 3
    · rw [min_eq_right (by linarith), max_eq_right (by linarith),
        min_eq_right (by linarith), max_eq_right (by linarith)]; ring
    · rw [min_eq_left (by linarith), max_eq_right (by norm_num),
        min_eq_right (by linarith), max_eq_left (by linarith)]; ring

def bumpInner (r : ℝ) (p : T2) : ℝ := clamp01 (torusN p / r - 1)
def bumpOuter (p : T2) : ℝ := clamp01 (2 - 50 * torusN p)
def bumpSmall (r : ℝ) (p : T2) : ℝ := clamp01 (2 - torusN p / (10 * r))

def psiX (r : ℝ) (p : T2) : ℝ :=
  bumpInner r p * bumpOuter p *
    coneH (torusAbs (p 0) / max (torusAbs (p 0) + torusAbs (p 1)) r)

def psiY (r : ℝ) (p : T2) : ℝ :=
  bumpInner r p * bumpOuter p *
    coneH (torusAbs (p 1) / max (torusAbs (p 0) + torusAbs (p 1)) r)

def torusE (p : T2) : ℝ :=
  ‖UnitAddTorus.mFourier (d := Fin 2) (Pi.single 0 1) p - 1‖ ^ 2 +
  ‖UnitAddTorus.mFourier (d := Fin 2) (Pi.single 1 1) p - 1‖ ^ 2

def fejer2D (M : ℕ) (p : T2) : ℝ :=
  ‖((M : ℂ)⁻¹) * ∑ m ∈ Finset.range M, fourier (T := (1 : ℝ)) (m : ℤ) (p 0)‖ ^ 2 *
  ‖((M : ℂ)⁻¹) * ∑ n ∈ Finset.range M, fourier (T := (1 : ℝ)) (n : ℤ) (p 1)‖ ^ 2

def phiA (k : ℤ) : C(T2, T2) where
  toFun p i := if i = 0 then p 0 else p 1 - k • p 0
  continuous_toFun := continuous_pi fun i => by
    fin_cases i
    · exact continuous_apply 0
    · exact (continuous_apply 1).sub ((continuous_zsmul k).comp (continuous_apply 0))

def phiB (k : ℤ) : C(T2, T2) where
  toFun p i := if i = 0 then p 0 - k • p 1 else p 1
  continuous_toFun := continuous_pi fun i => by
    fin_cases i
    · exact (continuous_apply 0).sub ((continuous_zsmul k).comp (continuous_apply 1))
    · exact continuous_apply 1

lemma continuous_bumpSmall (r : ℝ) : Continuous (bumpSmall r) :=
  continuous_clamp01.comp (continuous_const.sub (continuous_torusN.div_const _))

lemma continuous_psiX {r : ℝ} (hr : 0 < r) : Continuous (psiX r) := by
  have h1 : Continuous (bumpInner r) :=
    continuous_clamp01.comp ((continuous_torusN.div_const r).sub continuous_const)
  have h2 : Continuous bumpOuter :=
    continuous_clamp01.comp (continuous_const.sub (continuous_const.mul continuous_torusN))
  have ha0 : Continuous (fun p : T2 => torusAbs (p 0)) := continuous_torusAbs.comp (continuous_apply (0 : Fin 2))
  have ha1 : Continuous (fun p : T2 => torusAbs (p 1)) := continuous_torusAbs.comp (continuous_apply (1 : Fin 2))
  have hden : Continuous (fun p : T2 => max (torusAbs (p 0) + torusAbs (p 1)) r) :=
    (ha0.add ha1).max continuous_const
  have hne : ∀ p : T2, max (torusAbs (p 0) + torusAbs (p 1)) r ≠ 0 :=
    fun _ => ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  exact (h1.mul h2).mul (continuous_coneH.comp (ha0.div hden hne))

lemma continuous_psiY {r : ℝ} (hr : 0 < r) : Continuous (psiY r) := by
  have h1 : Continuous (bumpInner r) :=
    continuous_clamp01.comp ((continuous_torusN.div_const r).sub continuous_const)
  have h2 : Continuous bumpOuter :=
    continuous_clamp01.comp (continuous_const.sub (continuous_const.mul continuous_torusN))
  have ha0 : Continuous (fun p : T2 => torusAbs (p 0)) := continuous_torusAbs.comp (continuous_apply (0 : Fin 2))
  have ha1 : Continuous (fun p : T2 => torusAbs (p 1)) := continuous_torusAbs.comp (continuous_apply (1 : Fin 2))
  have hden : Continuous (fun p : T2 => max (torusAbs (p 0) + torusAbs (p 1)) r) :=
    (ha0.add ha1).max continuous_const
  have hne : ∀ p : T2, max (torusAbs (p 0) + torusAbs (p 1)) r ≠ 0 :=
    fun _ => ne_of_gt (lt_of_lt_of_le hr (le_max_right _ _))
  exact (h1.mul h2).mul (continuous_coneH.comp (ha1.div hden hne))

lemma continuous_torusE : Continuous torusE := by
  have h0 : Continuous (fun p : T2 => ‖UnitAddTorus.mFourier (d := Fin 2) (Pi.single 0 1) p - 1‖ ^ 2) :=
    (((UnitAddTorus.mFourier (d := Fin 2) (Pi.single 0 1)).continuous.sub continuous_const).norm).pow 2
  have h1 : Continuous (fun p : T2 => ‖UnitAddTorus.mFourier (d := Fin 2) (Pi.single 1 1) p - 1‖ ^ 2) :=
    (((UnitAddTorus.mFourier (d := Fin 2) (Pi.single 1 1)).continuous.sub continuous_const).norm).pow 2
  exact h0.add h1

lemma continuous_fejer2D (M : ℕ) : Continuous (fejer2D M) := by
  have hm0 : ∀ m : ℕ, Continuous (fun p : T2 => fourier (T := (1 : ℝ)) (m : ℤ) (p 0)) := fun m =>
    (fourier (T := (1 : ℝ)) (m : ℤ)).continuous.comp (continuous_apply (0 : Fin 2))
  have hm1 : ∀ n : ℕ, Continuous (fun p : T2 => fourier (T := (1 : ℝ)) (n : ℤ) (p 1)) := fun n =>
    (fourier (T := (1 : ℝ)) (n : ℤ)).continuous.comp (continuous_apply (1 : Fin 2))
  have hs0 : Continuous (fun p : T2 => ∑ m ∈ Finset.range M, fourier (T := (1 : ℝ)) (m : ℤ) (p 0)) :=
    continuous_finsetSum (Finset.range M) fun m _ => hm0 m
  have hs1 : Continuous (fun p : T2 => ∑ n ∈ Finset.range M, fourier (T := (1 : ℝ)) (n : ℤ) (p 1)) :=
    continuous_finsetSum (Finset.range M) fun n _ => hm1 n
  exact (((continuous_const.mul hs0).norm).pow 2).mul (((continuous_const.mul hs1).norm).pow 2)

lemma psiX_nonneg (r : ℝ) (p : T2) : 0 ≤ psiX r p :=
  mul_nonneg (mul_nonneg (clamp01_nonneg _) (clamp01_nonneg _)) (clamp01_nonneg _)

lemma psiX_le_one (r : ℝ) (p : T2) : psiX r p ≤ 1 := by
  have h1 := clamp01_le_one (torusN p / r - 1)
  have h2 := clamp01_le_one (2 - 50 * torusN p)
  have h3 := clamp01_le_one (3 * (torusAbs (p 0) / max (torusAbs (p 0) + torusAbs (p 1)) r) - 1)
  have n2 := clamp01_nonneg (2 - 50 * torusN p)
  have n3 := clamp01_nonneg (3 * (torusAbs (p 0) / max (torusAbs (p 0) + torusAbs (p 1)) r) - 1)
  dsimp only [psiX, bumpInner, bumpOuter, coneH]
  calc _ ≤ (1 * 1) * 1 := mul_le_mul (mul_le_mul h1 h2 n2 zero_le_one) h3 n3 (by norm_num)
    _ = 1 := by norm_num

lemma psiY_nonneg (r : ℝ) (p : T2) : 0 ≤ psiY r p :=
  mul_nonneg (mul_nonneg (clamp01_nonneg _) (clamp01_nonneg _)) (clamp01_nonneg _)

lemma psiY_le_one (r : ℝ) (p : T2) : psiY r p ≤ 1 := by
  have h1 := clamp01_le_one (torusN p / r - 1)
  have h2 := clamp01_le_one (2 - 50 * torusN p)
  have h3 := clamp01_le_one (3 * (torusAbs (p 1) / max (torusAbs (p 0) + torusAbs (p 1)) r) - 1)
  have n2 := clamp01_nonneg (2 - 50 * torusN p)
  have n3 := clamp01_nonneg (3 * (torusAbs (p 1) / max (torusAbs (p 0) + torusAbs (p 1)) r) - 1)
  dsimp only [psiY, bumpInner, bumpOuter, coneH]
  calc _ ≤ (1 * 1) * 1 := mul_le_mul (mul_le_mul h1 h2 n2 zero_le_one) h3 n3 (by norm_num)
    _ = 1 := by norm_num

lemma fourier_one_sub_one_sq_ge (t : UnitAddCircle) :
    16 * torusAbs t ^ 2 ≤ ‖fourier (T := (1 : ℝ)) 1 t - 1‖ ^ 2 := by
  obtain ⟨x, hx, rfl, habs⟩ := exists_rep_Ico t
  rw [habs, fourier_coe_apply]
  have harg : (2 * Real.pi * Complex.I * (1 : ℤ) * (x : ℂ) / (1 : ℝ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_mul_I]
  have hre : (Complex.cos ((2 * Real.pi * x : ℝ) : ℂ) + Complex.sin ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I - 1).re =
      Real.cos (2 * Real.pi * x) - 1 := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.one_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
  have him : (Complex.cos ((2 * Real.pi * x : ℝ) : ℂ) + Complex.sin ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I - 1).im =
      Real.sin (2 * Real.pi * x) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.one_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero, sub_zero]
  have hnorm_sq : ‖Complex.cos ((2 * Real.pi * x : ℝ) : ℂ) + Complex.sin ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I - 1‖ ^ 2 =
      4 * Real.sin (Real.pi * |x|) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
    have hcos : Real.cos (2 * Real.pi * x) = 1 - 2 * Real.sin (Real.pi * x) ^ 2 := by
      have h := Real.cos_two_mul (Real.pi * x)
      have hs := Real.sin_sq_add_cos_sq (Real.pi * x)
      rw [show 2 * (Real.pi * x) = 2 * Real.pi * x by ring] at h; linarith
    have hsin2 : Real.sin (2 * Real.pi * x) ^ 2 + Real.cos (2 * Real.pi * x) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    have hsin_abs : Real.sin (Real.pi * |x|) ^ 2 = Real.sin (Real.pi * x) ^ 2 := by
      rcases le_or_gt 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, mul_neg, Real.sin_neg, neg_sq]
    rw [hsin_abs]; nlinarith
  rw [hnorm_sq]
  have hx_le : |x| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hx.1], le_of_lt hx.2⟩
  have hsin_ge := Real.mul_le_sin (mul_nonneg (le_of_lt Real.pi_pos) (abs_nonneg x))
    (by nlinarith [Real.pi_pos])
  have h2x : 2 * |x| ≤ Real.sin (Real.pi * |x|) := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have heq : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by field_simp [hpi]
    rwa [heq] at hsin_ge
  nlinarith [abs_nonneg x]

lemma torusE_ge_of_torusN_ge {p : T2} (hp : 1 / 100 ≤ torusN p) :
    (1 / 625 : ℝ) ≤ torusE p := by
  dsimp only [torusE]
  rw [UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single]
  have h0 := fourier_one_sub_one_sq_ge (p 0)
  have h1 := fourier_one_sub_one_sq_ge (p 1)
  have hmax : (1 / 100 : ℝ) ≤ torusAbs (p 0) ∨ (1 / 100 : ℝ) ≤ torusAbs (p 1) := le_max_iff.mp hp
  rcases hmax with h | h
  · nlinarith [torusAbs_nonneg (p 0), sq_nonneg ‖fourier (T := (1 : ℝ)) 1 (p 1) - 1‖]
  · nlinarith [torusAbs_nonneg (p 1), sq_nonneg ‖fourier (T := (1 : ℝ)) 1 (p 0) - 1‖]

lemma bumpSmall_le_fejer2D {M : ℕ} (hM : 1 ≤ M) (p : T2) :
    bumpSmall (1 / (200 * (M : ℝ))) p ≤ 16 * fejer2D M p := by
  set r : ℝ := 1 / (200 * (M : ℝ))
  have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
  have hrpos : 0 < r := by positivity
  by_cases hbig : 20 * r ≤ torusN p
  · have h0 : bumpSmall r p = 0 := by
      dsimp only [bumpSmall]; apply clamp01_eq_zero
      have : 2 ≤ torusN p / (10 * r) := by rw [le_div_iff₀ (by positivity)]; linarith
      linarith
    rw [h0]
    have : 0 ≤ fejer2D M p := mul_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  · push Not at hbig
    have h1D : ∀ t : UnitAddCircle, torusAbs t < 1 / (10 * (M : ℝ)) →
        (1 / 4 : ℝ) ≤ ‖((M : ℂ)⁻¹) * ∑ m ∈ Finset.range M, fourier (T := (1 : ℝ)) (m : ℤ) t‖ ^ 2 := by
      intro t ht
      obtain ⟨x, _, rfl, habs⟩ := exists_rep_Ico t
      rw [habs] at ht
      have hre : (1 / 2 : ℝ) ≤ (((M : ℂ)⁻¹) * ∑ m ∈ Finset.range M, fourier (T := (1 : ℝ)) (m : ℤ) (x : UnitAddCircle)).re := by
        have hinv : ((M : ℂ)⁻¹) = (((M : ℝ)⁻¹ : ℝ) : ℂ) := by rw [Complex.ofReal_inv, Complex.ofReal_natCast]
        rw [hinv, Complex.re_ofReal_mul, Complex.re_sum]
        have hterm : ∀ m ∈ Finset.range M, (1 / 2 : ℝ) ≤ (fourier (T := (1 : ℝ)) (m : ℤ) (x : UnitAddCircle)).re := by
          intro m hm
          rw [Finset.mem_range] at hm
          rw [fourier_coe_apply]
          have harg : (2 * Real.pi * Complex.I * ((m : ℤ) : ℂ) * (x : ℂ) / (1 : ℝ)) =
              ((2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
          rw [harg, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
          simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
          have hcos_abs : Real.cos (2 * Real.pi * (m : ℝ) * x) = Real.cos (2 * Real.pi * (m : ℝ) * |x|) := by
            rcases le_or_gt 0 x with h | h
            · rw [abs_of_nonneg h]
            · rw [abs_of_neg h, mul_neg, Real.cos_neg]
          rw [hcos_abs, ← Real.cos_pi_div_three]
          refine Real.cos_le_cos_of_nonneg_of_le_pi (by positivity) (by linarith [Real.pi_pos]) ?_
          have hmle : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast le_of_lt hm
          have hprod : (m : ℝ) * |x| ≤ 1 / 10 := by
            calc (m : ℝ) * |x| ≤ (M : ℝ) * (1 / (10 * (M : ℝ))) :=
                  mul_le_mul hmle (le_of_lt ht) (abs_nonneg x) (le_of_lt hMpos)
              _ = 1 / 10 := by field_simp [ne_of_gt hMpos]
          nlinarith [Real.pi_pos]
        have hsum : (M : ℝ) * (1 / 2) ≤ ∑ m ∈ Finset.range M, (fourier (T := (1 : ℝ)) (m : ℤ) (x : UnitAddCircle)).re := by
          calc (M : ℝ) * (1 / 2) = ∑ _m ∈ Finset.range M, (1 / 2 : ℝ) := by simp
            _ ≤ _ := Finset.sum_le_sum hterm
        calc (1 / 2 : ℝ) = (M : ℝ)⁻¹ * ((M : ℝ) * (1 / 2)) := by field_simp [ne_of_gt hMpos]
          _ ≤ (M : ℝ)⁻¹ * _ := mul_le_mul_of_nonneg_left hsum (by positivity)
      have hnorm : (1 / 2 : ℝ) ≤ ‖((M : ℂ)⁻¹) * ∑ m ∈ Finset.range M, fourier (T := (1 : ℝ)) (m : ℤ) (x : UnitAddCircle)‖ :=
        hre.trans (Complex.re_le_norm _)
      nlinarith
    have hr20 : 20 * r = 1 / (10 * (M : ℝ)) := by dsimp only [r]; field_simp [ne_of_gt hMpos]; ring
    rw [hr20] at hbig
    have h0 := h1D (p 0) (lt_of_le_of_lt (le_max_left _ _) hbig)
    have h1 := h1D (p 1) (lt_of_le_of_lt (le_max_right _ _) hbig)
    have hfejer : (1 / 16 : ℝ) ≤ fejer2D M p := by dsimp only [fejer2D]; nlinarith
    have hb1 : bumpSmall r p ≤ 1 := clamp01_le_one _
    linarith

lemma pingpong_A {r : ℝ} (hr : 0 < r) (hr_hi : r ≤ 1 / 1000) (p : T2) :
    psiX r (phiA 4 p) + psiX r (phiA (-4) p) ≤
      psiY r p + 2 * bumpSmall r p + 1300 * torusE p := by
  have hE_nn : 0 ≤ torusE p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb_nn : 0 ≤ bumpSmall r p := clamp01_nonneg _
  have hy_nn : 0 ≤ psiY r p := psiY_nonneg r p
  by_cases hsmall : torusN p ≤ 10 * r
  · have hb1 : bumpSmall r p = 1 := by
      dsimp only [bumpSmall]; apply clamp01_eq_one
      have : torusN p / (10 * r) ≤ 1 := (div_le_one (by positivity)).mpr hsmall
      linarith
    rw [hb1]; linarith [psiX_le_one r (phiA 4 p), psiX_le_one r (phiA (-4) p)]
  · push Not at hsmall
    by_cases hbig : 1 / 100 ≤ torusN p
    · have hE := torusE_ge_of_torusN_ge hbig
      linarith [psiX_le_one r (phiA 4 p), psiX_le_one r (phiA (-4) p)]
    · push Not at hbig
      obtain ⟨x, hx, hpx, hax⟩ := exists_rep_Ico (p 0)
      obtain ⟨y, hy, hpy, hay⟩ := exists_rep_Ico (p 1)
      have hx_lt : |x| < 1 / 100 := by
        rw [← hax]; exact lt_of_le_of_lt (le_max_left _ _) hbig
      have hy_lt : |y| < 1 / 100 := by
        rw [← hay]; exact lt_of_le_of_lt (le_max_right _ _) hbig
      have hbi : bumpInner r p = 1 := by
        dsimp only [bumpInner]; apply clamp01_eq_one
        have : 2 ≤ torusN p / r := by rw [le_div_iff₀ hr]; linarith
        linarith
      have hbo : bumpOuter p = 1 := by
        dsimp only [bumpOuter]; apply clamp01_eq_one; linarith
      have hsum_ge : r ≤ |x| + |y| := by
        have : torusN p ≤ |x| + |y| := by
          dsimp only [torusN]; rw [hax, hay]; exact max_le (by linarith [abs_nonneg y]) (by linarith [abs_nonneg x])
        linarith
      have hpsiY_eq : psiY r p = coneH (|y| / (|x| + |y|)) := by
        dsimp only [psiY]; rw [hbi, hbo, one_mul, one_mul, hax, hay, max_eq_left hsum_ge]
      have hphi_abs : ∀ k : ℤ, |k| ≤ 4 →
          torusAbs (phiA k p 0) = |x| ∧ torusAbs (phiA k p 1) = |y - (k : ℝ) * x| := by
        intro k hk
        refine ⟨by change torusAbs (p 0) = |x|; exact hax, ?_⟩
        change torusAbs (p 1 - k • p 0) = |y - (k : ℝ) * x|
        have hcoe : ((y - (k : ℝ) * x : ℝ) : UnitAddCircle) = p 1 - k • p 0 := by
          rw [← hpx, ← hpy]; simp
        rw [← hcoe]; apply torusAbs_coe
        have hkR : |(k : ℝ)| ≤ 4 := by exact_mod_cast hk
        have hbd : |y - (k : ℝ) * x| < 1 / 2 := by
          calc |y - (k : ℝ) * x| ≤ |y| + |(k : ℝ) * x| := abs_sub _ _
            _ = |y| + |(k : ℝ)| * |x| := by rw [abs_mul]
            _ ≤ |y| + 4 * |x| := by nlinarith [abs_nonneg x]
            _ < 1 / 2 := by linarith
        exact ⟨by linarith [(abs_lt.mp hbd).1], (abs_lt.mp hbd).2⟩
      have hpos_imp : ∀ k : ℤ, |k| ≤ 4 → 0 < psiX r (phiA k p) → |y - (k : ℝ) * x| < 2 * |x| := by
        intro k hk hpos
        have ha := hphi_abs k hk
        have hbi_pos : 0 < bumpInner r (phiA k p) := by
          by_contra hle; push Not at hle
          have h0 : bumpInner r (phiA k p) = 0 := le_antisymm hle (clamp01_nonneg _)
          dsimp only [psiX] at hpos; rw [h0, zero_mul, zero_mul] at hpos; linarith
        have hN_gt : r < torusN (phiA k p) := by
          by_contra hle; push Not at hle
          have h0 : bumpInner r (phiA k p) = 0 := by
            dsimp only [bumpInner]; apply clamp01_eq_zero
            have : torusN (phiA k p) / r ≤ 1 := (div_le_one hr).mpr hle; linarith
          linarith
        have hsum_k : r ≤ |x| + |y - (k : ℝ) * x| := by
          have : torusN (phiA k p) ≤ |x| + |y - (k : ℝ) * x| := by
            dsimp only [torusN]; rw [ha.1, ha.2]
            exact max_le (by linarith [abs_nonneg (y - (k : ℝ) * x)]) (by linarith [abs_nonneg x])
          linarith
        have hcone_pos : 0 < coneH (|x| / (|x| + |y - (k : ℝ) * x|)) := by
          by_contra hle; push Not at hle
          have h0 : coneH (|x| / (|x| + |y - (k : ℝ) * x|)) = 0 := le_antisymm hle (clamp01_nonneg _)
          dsimp only [psiX] at hpos; rw [ha.1, ha.2, max_eq_left hsum_k, h0, mul_zero] at hpos; linarith
        have h3u : 1 < 3 * (|x| / (|x| + |y - (k : ℝ) * x|)) := by
          by_contra hle; push Not at hle
          have h0 : coneH (|x| / (|x| + |y - (k : ℝ) * x|)) = 0 :=
            clamp01_eq_zero (by linarith)
          linarith
        have hden_pos : 0 < |x| + |y - (k : ℝ) * x| := by linarith
        rw [mul_div_assoc', one_lt_div hden_pos] at h3u; linarith
      have hcore : psiX r (phiA 4 p) + psiX r (phiA (-4) p) ≤ psiY r p := by
        by_cases h1 : 0 < psiX r (phiA 4 p)
        · have hlt := hpos_imp 4 (by norm_num) h1
          have hxpos : 0 < |x| := by linarith [abs_nonneg (y - ((4 : ℤ) : ℝ) * x)]
          have hy_gt : 2 * |x| < |y| := by
            have htri : |4 * x| - |y| ≤ |4 * x - y| := abs_sub_abs_le_abs_sub (4 * x) y
            rw [abs_sub_comm, abs_mul, show |(4 : ℝ)| = 4 by norm_num] at htri
            norm_cast at hlt; linarith
          have h2_zero : psiX r (phiA (-4) p) = 0 := by
            by_contra hne
            have h2pos : 0 < psiX r (phiA (-4) p) := lt_of_le_of_ne (psiX_nonneg _ _) (Ne.symm hne)
            have hlt2 := hpos_imp (-4) (by norm_num) h2pos
            have h8 : |8 * x| ≤ |y - (4 : ℝ) * x| + |y - ((-4 : ℤ) : ℝ) * x| := by
              have hs : 8 * x = (y - ((-4 : ℤ) : ℝ) * x) - (y - (4 : ℝ) * x) := by push_cast; ring
              rw [hs]; linarith [abs_sub (y - ((-4 : ℤ) : ℝ) * x) (y - (4 : ℝ) * x)]
            rw [abs_mul, show |(8 : ℝ)| = 8 by norm_num] at h8
            norm_cast at hlt; linarith
          have hpsiY1 : psiY r p = 1 := by
            rw [hpsiY_eq]; dsimp only [coneH]; apply clamp01_eq_one
            have hden : 0 < |x| + |y| := by linarith
            have : 2 / 3 ≤ |y| / (|x| + |y|) := by rw [div_le_div_iff₀ (by norm_num) hden]; linarith
            linarith
          rw [h2_zero, add_zero, hpsiY1]; exact psiX_le_one _ _
        · have h1_zero : psiX r (phiA 4 p) = 0 := le_antisymm (not_lt.mp h1) (psiX_nonneg _ _)
          rw [h1_zero, zero_add]
          by_cases h2 : 0 < psiX r (phiA (-4) p)
          · have hlt2 := hpos_imp (-4) (by norm_num) h2
            have hy_gt : 2 * |x| < |y| := by
              have htri : |4 * x| - |y| ≤ |4 * x + y| := by
                have h := abs_sub_abs_le_abs_sub (4 * x) (-y)
                rwa [abs_neg, sub_neg_eq_add] at h
              rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num] at htri
              have heq : y - ((-4 : ℤ) : ℝ) * x = 4 * x + y := by push_cast; ring
              rw [heq] at hlt2; linarith
            have hpsiY1 : psiY r p = 1 := by
              rw [hpsiY_eq]; dsimp only [coneH]; apply clamp01_eq_one
              have hden : 0 < |x| + |y| := by linarith
              have : 2 / 3 ≤ |y| / (|x| + |y|) := by rw [div_le_div_iff₀ (by norm_num) hden]; linarith
              linarith
            rw [hpsiY1]; exact psiX_le_one _ _
          · have h2_zero : psiX r (phiA (-4) p) = 0 := le_antisymm (not_lt.mp h2) (psiX_nonneg _ _)
            rw [h2_zero]; exact hy_nn
      linarith

lemma pingpong_B {r : ℝ} (hr : 0 < r) (hr_hi : r ≤ 1 / 1000) (p : T2) :
    psiY r (phiB 4 p) + psiY r (phiB (-4) p) ≤
      psiX r p + 2 * bumpSmall r p + 1300 * torusE p := by
  let sw : T2 := fun i => p (1 - i)
  have h0 := pingpong_A hr hr_hi sw
  have hN : torusN sw = torusN p := by dsimp only [torusN, sw]; rw [max_comm]; rfl
  have hb : bumpSmall r sw = bumpSmall r p := by dsimp only [bumpSmall]; rw [hN]
  have hE : torusE sw = torusE p := by
    dsimp only [torusE]
    rw [UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single,
      UnitAddTorus.mFourier_single, UnitAddTorus.mFourier_single]
    change ‖fourier 1 (p 1) - 1‖ ^ 2 + ‖fourier 1 (p 0) - 1‖ ^ 2 =
      ‖fourier 1 (p 0) - 1‖ ^ 2 + ‖fourier 1 (p 1) - 1‖ ^ 2
    ring
  have hX : psiY r sw = psiX r p := by
    dsimp only [psiY, psiX, bumpInner, bumpOuter]; rw [hN]
    change _ * _ * coneH (torusAbs (p 0) / max (torusAbs (p 1) + torusAbs (p 0)) r) = _
    rw [add_comm (torusAbs (p 1))]
  have hphi : ∀ k : ℤ, psiX r (phiA k sw) = psiY r (phiB k p) := fun k => by
    have hNk : torusN (phiA k sw) = torusN (phiB k p) := by
      dsimp only [torusN, phiA, phiB, sw]; rw [max_comm]; rfl
    dsimp only [psiX, psiY, bumpInner, bumpOuter]; rw [hNk]
    change _ * _ * coneH (torusAbs (p 1) / max (torusAbs (p 1) + torusAbs (p 0 - k • p 1)) r) =
      _ * _ * coneH (torusAbs (p 1) / max (torusAbs (p 0 - k • p 1) + torusAbs (p 1)) r)
    rw [add_comm (torusAbs (p 1))]
  rwa [hphi 4, hphi (-4), hX, hb, hE] at h0

lemma torus_cover {r : ℝ} (hr : 0 < r) (hr_hi : r ≤ 1 / 1000) (p : T2) :
    1 ≤ psiX r p + psiY r p + bumpSmall r p + 650 * torusE p := by
  have hE_nn : 0 ≤ torusE p := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hb_nn : 0 ≤ bumpSmall r p := clamp01_nonneg _
  have hx_nn : 0 ≤ psiX r p := psiX_nonneg r p
  have hy_nn : 0 ≤ psiY r p := psiY_nonneg r p
  by_cases hsmall : torusN p ≤ 10 * r
  · have hb1 : bumpSmall r p = 1 := by
      dsimp only [bumpSmall]; apply clamp01_eq_one
      have : torusN p / (10 * r) ≤ 1 := (div_le_one (by positivity)).mpr hsmall; linarith
    linarith
  · push Not at hsmall
    by_cases hbig : 1 / 100 ≤ torusN p
    · have hE := torusE_ge_of_torusN_ge hbig; linarith
    · push Not at hbig
      have hbi : bumpInner r p = 1 := by
        dsimp only [bumpInner]; apply clamp01_eq_one
        have : 2 ≤ torusN p / r := by rw [le_div_iff₀ hr]; linarith
        linarith
      have hbo : bumpOuter p = 1 := by
        dsimp only [bumpOuter]; apply clamp01_eq_one; linarith
      have hsum_ge : r ≤ torusAbs (p 0) + torusAbs (p 1) := by
        have : torusN p ≤ torusAbs (p 0) + torusAbs (p 1) :=
          max_le (by linarith [torusAbs_nonneg (p 1)]) (by linarith [torusAbs_nonneg (p 0)])
        linarith
      have hden_pos : 0 < torusAbs (p 0) + torusAbs (p 1) := by linarith
      set u := torusAbs (p 0) / (torusAbs (p 0) + torusAbs (p 1))
      have hu0 : 0 ≤ u := div_nonneg (torusAbs_nonneg _) (le_of_lt hden_pos)
      have hu1 : u ≤ 1 := (div_le_one hden_pos).mpr (by linarith [torusAbs_nonneg (p 1)])
      have h1u : 1 - u = torusAbs (p 1) / (torusAbs (p 0) + torusAbs (p 1)) := by
        dsimp only [u]; field_simp [ne_of_gt hden_pos]; ring
      have hsum1 : psiX r p + psiY r p = 1 := by
        dsimp only [psiX, psiY]
        simp only [hbi, hbo, one_mul, max_eq_left hsum_ge, ← h1u]
        exact coneH_add_symm hu0 hu1
      linarith

/-- Orthogonality of `mFourier n` against `1` on `T2`. -/
lemma integral_mFourier_T2 (n : Fin 2 → ℤ) :
    ∫ θ : T2, UnitAddTorus.mFourier (d := Fin 2) n θ = if n = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := Fin 2))) 0 n
  rw [ContinuousMap.inner_toLp] at h
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, mul_one] at h
  by_cases hn : n = 0
  · subst hn; simpa using h
  · have h0n : (0 : Fin 2 → ℤ) ≠ n := Ne.symm hn
    simpa [hn, h0n] using h

lemma mFourier_comp_phiA (k : ℤ) (n : Fin 2 → ℤ) :
    (UnitAddTorus.mFourier (d := Fin 2) n).comp (phiA k) =
      UnitAddTorus.mFourier (d := Fin 2) ![n 0 - k * n 1, n 1] := by
  ext p
  change ∏ i : Fin 2, fourier (T := (1 : ℝ)) (n i) (phiA k p i) =
    ∏ i : Fin 2, fourier (T := (1 : ℝ)) (![n 0 - k * n 1, n 1] i) (p i)
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  change fourier (n 0) (p 0) * fourier (n 1) (p 1 - k • p 0) =
    fourier (n 0 - k * n 1) (p 0) * fourier (n 1) (p 1)
  have hsplit : fourier (T := (1 : ℝ)) (n 1) (p 1 - k • p 0) =
      fourier (T := (1 : ℝ)) (n 1) (p 1) * fourier (T := (1 : ℝ)) (-(k * n 1)) (p 0) := by
    rw [fourier_apply, fourier_apply, fourier_apply, smul_sub, sub_eq_add_neg,
      AddCircle.toCircle_add, Circle.coe_mul]
    congr 1; exact congrArg (fun z : UnitAddCircle => (AddCircle.toCircle z : ℂ))
      (by rw [neg_smul, mul_comm k (n 1), mul_smul])
  rw [hsplit, ← mul_assoc, mul_comm (fourier (n 0) (p 0)) (fourier (n 1) (p 1)),
    mul_assoc, ← fourier_add, mul_comm, sub_eq_add_neg]

lemma mFourier_comp_phiB (k : ℤ) (n : Fin 2 → ℤ) :
    (UnitAddTorus.mFourier (d := Fin 2) n).comp (phiB k) =
      UnitAddTorus.mFourier (d := Fin 2) ![n 0, n 1 - k * n 0] := by
  ext p
  change ∏ i : Fin 2, fourier (T := (1 : ℝ)) (n i) (phiB k p i) =
    ∏ i : Fin 2, fourier (T := (1 : ℝ)) (![n 0, n 1 - k * n 0] i) (p i)
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  change fourier (n 0) (p 0 - k • p 1) * fourier (n 1) (p 1) =
    fourier (n 0) (p 0) * fourier (n 1 - k * n 0) (p 1)
  have hsplit : fourier (T := (1 : ℝ)) (n 0) (p 0 - k • p 1) =
      fourier (T := (1 : ℝ)) (n 0) (p 0) * fourier (T := (1 : ℝ)) (-(k * n 0)) (p 1) := by
    rw [fourier_apply, fourier_apply, fourier_apply, smul_sub, sub_eq_add_neg,
      AddCircle.toCircle_add, Circle.coe_mul]
    congr 1; exact congrArg (fun z : UnitAddCircle => (AddCircle.toCircle z : ℂ))
      (by rw [neg_smul, mul_comm k (n 0), mul_smul])
  rw [hsplit, mul_assoc, ← fourier_add, add_comm (-(k * n 0)), ← sub_eq_add_neg]

/-- Fejér-kernel spectral sum `S_N θ w` on `T2` for commuting unitaries `π e₁, π e₂`. -/
def fejerSum {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (e₁ e₂ : Γ) (N : ℕ) (θ : T2) (w : V) : V :=
  ((N : ℂ)⁻¹) • ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
    UnitAddTorus.mFourier (d := Fin 2) ![-(m : ℤ), -(n : ℤ)] θ • π (e₁ ^ m * e₂ ^ n) w

/-- Approximate positive linear functional `L_N f w = ∫_{T²} f(θ) ‖S_N(θ, w)‖² dθ`. -/
def fejerFunc {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (e₁ e₂ : Γ) (N : ℕ) (f : C(T2, ℂ)) (w : V) : ℂ :=
  ∫ θ : T2, f θ * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ)

lemma continuous_fejerSum {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (e₁ e₂ : Γ) (N : ℕ) (w : V) :
    Continuous (fun θ : T2 => fejerSum π e₁ e₂ N θ w) :=
  continuous_const.smul (continuous_finsetSum _ fun m _ =>
    continuous_finsetSum _ fun n _ =>
      (UnitAddTorus.mFourier (d := Fin 2) ![-(m : ℤ), -(n : ℤ)]).continuous.smul continuous_const)

lemma integrable_fejer_integrand {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (e₁ e₂ : Γ) (N : ℕ) (f : C(T2, ℂ)) (w : V) :
    Integrable (fun θ : T2 => f θ * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ)) :=
  (f.continuous.mul (Complex.continuous_ofReal.comp
    (((continuous_fejerSum π e₁ e₂ N w).norm).pow 2))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma card_sub_eq_int (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) :
    (((Finset.range N ×ˢ Finset.range N).filter fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = k).card : ℕ) =
      N - k.natAbs := by
  by_cases hkn : 0 ≤ k
  · lift k to ℕ using hkn
    simp only [Int.natAbs_natCast] at hk ⊢
    have heq : (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = (k : ℤ)) =
        (Finset.range (N - k)).image (fun m => (m, m + k)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨a, by omega, rfl, by omega⟩
      · rintro ⟨m, hm, rfl, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by push_cast; ring⟩
    rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1), Finset.card_range]
  · push Not at hkn
    set d : ℕ := k.natAbs
    have hkd : k = -(d : ℤ) := by
      have : (d : ℤ) = -k := Int.ofNat_natAbs_of_nonpos (le_of_lt hkn)
      omega
    have heq : (Finset.range N ×ˢ Finset.range N).filter (fun p : ℕ × ℕ => (p.2 : ℤ) - (p.1 : ℤ) = k) =
        (Finset.range (N - d)).image (fun m => (m + d, m)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨b, by omega, by omega, rfl⟩
      · rintro ⟨m, hm, rfl, rfl⟩
        exact ⟨⟨by omega, by omega⟩, by rw [hkd]; push_cast; ring⟩
    rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2), Finset.card_range]

lemma fejerFunc_mFourier {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    (k : Fin 2 → ℤ) (N : ℕ) (hN0 : 1 ≤ N) (hN1 : (k 0).natAbs ≤ N) (hN2 : (k 1).natAbs ≤ N) (w : V) :
    fejerFunc π e₁ e₂ N (UnitAddTorus.mFourier (d := Fin 2) k) w =
      (((N - (k 0).natAbs : ℕ) : ℂ) / (N : ℂ)) * (((N - (k 1).natAbs : ℕ) : ℂ) / (N : ℂ)) *
        ⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ := by
  dsimp only [fejerFunc]
  have hexpand : ∀ θ : T2,
      UnitAddTorus.mFourier (d := Fin 2) k θ * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) =
      (((N : ℂ)⁻¹) ^ 2) *
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N) ×ˢ (Finset.range N ×ˢ Finset.range N),
          UnitAddTorus.mFourier (d := Fin 2)
            (k + ![(p.1.1 : ℤ) - (p.2.1 : ℤ), (p.1.2 : ℤ) - (p.2.2 : ℤ)]) θ *
            ⟪w, π (e₁ ^ ((p.2.1 : ℤ) - (p.1.1 : ℤ)) * e₂ ^ ((p.2.2 : ℤ) - (p.1.2 : ℤ))) w⟫_ℂ := by
    intro θ
    rw [show ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) = ⟪fejerSum π e₁ e₂ N θ w, fejerSum π e₁ e₂ N θ w⟫_ℂ by
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl]
    dsimp only [fejerSum]
    rw [inner_smul_left, inner_smul_right]
    have hstar : (starRingEnd ℂ) ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by rw [map_inv₀, map_natCast]
    rw [hstar, ← mul_assoc, ← mul_assoc, show UnitAddTorus.mFourier (d := Fin 2) k θ * (N : ℂ)⁻¹ * (N : ℂ)⁻¹ =
      (((N : ℂ)⁻¹) ^ 2) * UnitAddTorus.mFourier (d := Fin 2) k θ by ring, mul_assoc]
    congr 1
    rw [sum_inner, Finset.mul_sum]
    simp_rw [sum_inner, inner_sum, Finset.mul_sum, ← Finset.sum_product']
    refine Finset.sum_bij (fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩
    · intro p₁ _ p₂ _ h
      rcases p₁ with ⟨a1, b1, c1, d1⟩; rcases p₂ with ⟨a2, b2, c2, d2⟩
      simp only [Prod.mk.injEq] at h; rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩; rfl
    · intro q hq
      refine ⟨(q.1.1, q.1.2, q.2.1, q.2.2), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range] at hq ⊢
      exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
    · intro p _
      rw [inner_smul_left, inner_smul_right]
      have hmf : UnitAddTorus.mFourier (d := Fin 2) k θ *
          (starRingEnd ℂ) (UnitAddTorus.mFourier (d := Fin 2) ![-(p.1 : ℤ), -(p.2.1 : ℤ)] θ) *
          UnitAddTorus.mFourier (d := Fin 2) ![-(p.2.2.1 : ℤ), -(p.2.2.2 : ℤ)] θ =
          UnitAddTorus.mFourier (d := Fin 2)
            (k + ![(p.1 : ℤ) - (p.2.2.1 : ℤ), (p.2.1 : ℤ) - (p.2.2.2 : ℤ)]) θ := by
        rw [mul_assoc, ← UnitAddTorus.mFourier_neg, ← UnitAddTorus.mFourier_add, ← UnitAddTorus.mFourier_add]
        refine congrArg (fun m => UnitAddTorus.mFourier (d := Fin 2) m θ) ?_
        ext i; fin_cases i <;> simp [sub_eq_add_neg]
      have hgrp : (e₁ ^ p.1 * e₂ ^ p.2.1)⁻¹ * (e₁ ^ p.2.2.1 * e₂ ^ p.2.2.2) =
          e₁ ^ ((p.2.2.1 : ℤ) - (p.1 : ℤ)) * e₂ ^ ((p.2.2.2 : ℤ) - (p.2.1 : ℤ)) := by
        rw [_root_.mul_inv_rev, ← zpow_natCast e₁, ← zpow_natCast e₂, ← zpow_natCast e₁, ← zpow_natCast e₂,
          ← _root_.zpow_neg, ← _root_.zpow_neg]
        have hc1 : Commute (e₂ ^ (-(p.2.1 : ℤ))) (e₁ ^ (-(p.1 : ℤ))) := (he₁₂.symm.zpow_left _).zpow_right _
        have hc2 : Commute (e₂ ^ (-(p.2.1 : ℤ))) (e₁ ^ (p.2.2.1 : ℤ)) := (he₁₂.symm.zpow_left _).zpow_right _
        calc e₂ ^ (-(p.2.1 : ℤ)) * e₁ ^ (-(p.1 : ℤ)) * (e₁ ^ (p.2.2.1 : ℤ) * e₂ ^ (p.2.2.2 : ℤ))
            = (e₁ ^ (-(p.1 : ℤ)) * e₂ ^ (-(p.2.1 : ℤ))) * (e₁ ^ (p.2.2.1 : ℤ) * e₂ ^ (p.2.2.2 : ℤ)) := by rw [hc1.eq]
          _ = e₁ ^ (-(p.1 : ℤ)) * (e₂ ^ (-(p.2.1 : ℤ)) * e₁ ^ (p.2.2.1 : ℤ)) * e₂ ^ (p.2.2.2 : ℤ) := by group
          _ = e₁ ^ (-(p.1 : ℤ)) * (e₁ ^ (p.2.2.1 : ℤ) * e₂ ^ (-(p.2.1 : ℤ))) * e₂ ^ (p.2.2.2 : ℤ) := by rw [hc2.eq]
          _ = (e₁ ^ (-(p.1 : ℤ)) * e₁ ^ (p.2.2.1 : ℤ)) * (e₂ ^ (-(p.2.1 : ℤ)) * e₂ ^ (p.2.2.2 : ℤ)) := by group
          _ = e₁ ^ ((p.2.2.1 : ℤ) - (p.1 : ℤ)) * e₂ ^ ((p.2.2.2 : ℤ) - (p.2.1 : ℤ)) := by
              rw [← _root_.zpow_add, ← _root_.zpow_add]; congr 2 <;> ring
      have hinner : ⟪π (e₁ ^ p.1 * e₂ ^ p.2.1) w, π (e₁ ^ p.2.2.1 * e₂ ^ p.2.2.2) w⟫_ℂ =
          ⟪w, π (e₁ ^ ((p.2.2.1 : ℤ) - (p.1 : ℤ)) * e₂ ^ ((p.2.2.2 : ℤ) - (p.2.1 : ℤ))) w⟫_ℂ := by
        rw [← (π (e₁ ^ p.1 * e₂ ^ p.2.1)⁻¹).inner_map_map, rep_inv_mul, ← rep_mul, hgrp]
      rw [hinner, ← mul_assoc, ← mul_assoc, hmf]
  simp_rw [hexpand]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_mul_const, integral_mFourier_T2]
    have hcond : ∀ p : (ℕ × ℕ) × (ℕ × ℕ),
        (k + ![(p.1.1 : ℤ) - (p.2.1 : ℤ), (p.1.2 : ℤ) - (p.2.2 : ℤ)] = 0) ↔
          ((p.2.1 : ℤ) - (p.1.1 : ℤ) = k 0 ∧ (p.2.2 : ℤ) - (p.1.2 : ℤ) = k 1) := by
      intro p
      rw [funext_iff, Fin.forall_fin_two]
      simp only [Pi.add_apply, Pi.zero_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      constructor <;> intro ⟨h1, h2⟩ <;> exact ⟨by omega, by omega⟩
    have hsum_filt :
        ∑ p ∈ (Finset.range N ×ˢ Finset.range N) ×ˢ (Finset.range N ×ˢ Finset.range N),
          (if k + ![(p.1.1 : ℤ) - (p.2.1 : ℤ), (p.1.2 : ℤ) - (p.2.2 : ℤ)] = 0 then (1 : ℂ) else 0) *
            ⟪w, π (e₁ ^ ((p.2.1 : ℤ) - (p.1.1 : ℤ)) * e₂ ^ ((p.2.2 : ℤ) - (p.1.2 : ℤ))) w⟫_ℂ =
        ∑ p ∈ ((Finset.range N ×ˢ Finset.range N) ×ˢ (Finset.range N ×ˢ Finset.range N)).filter
            (fun p => (p.2.1 : ℤ) - (p.1.1 : ℤ) = k 0 ∧ (p.2.2 : ℤ) - (p.1.2 : ℤ) = k 1),
          ⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun p _ => ?_
      by_cases hp : (p.2.1 : ℤ) - (p.1.1 : ℤ) = k 0 ∧ (p.2.2 : ℤ) - (p.1.2 : ℤ) = k 1
      · rw [if_pos ((hcond p).mpr hp), if_pos hp, one_mul, hp.1, hp.2]
      · rw [if_neg (fun h => hp ((hcond p).mp h)), if_neg hp, zero_mul]
    rw [hsum_filt, Finset.sum_const, nsmul_eq_mul]
    let eSwap : (ℕ × ℕ) × (ℕ × ℕ) ≃ (ℕ × ℕ) × (ℕ × ℕ) :=
      { toFun := fun p => ((p.1.1, p.2.1), (p.1.2, p.2.2))
        invFun := fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))
        left_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl
        right_inv := fun ⟨⟨_, _⟩, ⟨_, _⟩⟩ => rfl }
    have hcard : (((Finset.range N ×ˢ Finset.range N) ×ˢ (Finset.range N ×ˢ Finset.range N)).filter
        (fun p => (p.2.1 : ℤ) - (p.1.1 : ℤ) = k 0 ∧ (p.2.2 : ℤ) - (p.1.2 : ℤ) = k 1)).card =
        (N - (k 0).natAbs) * (N - (k 1).natAbs) := by
      rw [← card_sub_eq_int N (k 0) hN1, ← card_sub_eq_int N (k 1) hN2, ← Finset.card_product]
      refine Finset.card_bij (fun p _ => eSwap p) ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, eSwap, Equiv.coe_fn_mk] at hp ⊢
        exact ⟨⟨⟨hp.1.1.1, hp.1.2.1⟩, hp.2.1⟩, ⟨⟨hp.1.1.2, hp.1.2.2⟩, hp.2.2⟩⟩
      · intro _ _ _ _ h; exact eSwap.injective h
      · intro q hq
        refine ⟨eSwap.symm q, ?_, eSwap.apply_symm_apply q⟩
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, eSwap, Equiv.coe_fn_symm_mk] at hq ⊢
        exact ⟨⟨⟨hq.1.1.1, hq.2.1.1⟩, ⟨hq.1.1.2, hq.2.1.2⟩⟩, hq.1.2, hq.2.2⟩
    rw [hcard, Nat.cast_mul]
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp [hNne]
  · intro p _
    exact ((UnitAddTorus.mFourier (d := Fin 2) _).continuous.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

lemma integral_fejerSum_norm_sq {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    {N : ℕ} (hN : 1 ≤ N) (w : V) :
    ∫ θ : T2, ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 = ‖w‖ ^ 2 := by
  have h := fejerFunc_mFourier π he₁₂ 0 N hN (by simp) (by simp) w
  simp only [UnitAddTorus.mFourier_zero, Pi.zero_apply, Int.natAbs_zero, Nat.sub_zero,
    zpow_zero, mul_one, rep_one] at h
  have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [div_self hNne, one_mul, one_mul, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow] at h
  have hre := congrArg Complex.re h
  dsimp only [fejerFunc] at hre
  simp only [ContinuousMap.one_apply, one_mul] at hre
  have hof : ∫ θ : T2, ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) =
      ((∫ θ : T2, ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
  rw [hof, Complex.ofReal_re] at hre
  exact hre.trans (Complex.ofReal_re _)

lemma norm_fejerFunc_le {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    {N : ℕ} (hN : 1 ≤ N) (f : C(T2, ℂ)) (w : V) :
    ‖fejerFunc π e₁ e₂ N f w‖ ≤ ‖f‖ * ‖w‖ ^ 2 := by
  dsimp only [fejerFunc]
  have hint_sq : Integrable (fun θ : T2 => ‖fejerSum π e₁ e₂ N θ w‖ ^ 2) :=
    (((continuous_fejerSum π e₁ e₂ N w).norm).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc ‖∫ θ : T2, f θ * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ)‖
      ≤ ∫ θ : T2, ‖f θ * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ : T2, ‖f‖ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
          (hint_sq.const_mul _) (Filter.Eventually.of_forall fun θ => ?_)
        dsimp only
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm θ) (sq_nonneg _)
    _ = ‖f‖ * ‖w‖ ^ 2 := by rw [integral_const_mul, integral_fejerSum_norm_sq π he₁₂ hN w]

lemma norm_fejerFunc_sub_w_le {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    {N : ℕ} (hN : 1 ≤ N) (f : C(T2, ℂ)) {w₁ w₂ : V} (hnorm : ‖w₁‖ = ‖w₂‖) :
    ‖fejerFunc π e₁ e₂ N f w₁ - fejerFunc π e₁ e₂ N f w₂‖ ≤ 2 * ‖f‖ * ‖w₁‖ * ‖w₁ - w₂‖ := by
  have hsub : fejerFunc π e₁ e₂ N f w₁ - fejerFunc π e₁ e₂ N f w₂ =
      ∫ θ : T2, f θ * (((‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2 - ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2 : ℝ) : ℂ)) := by
    dsimp only [fejerFunc]
    rw [← integral_sub (integrable_fejer_integrand π e₁ e₂ N f w₁) (integrable_fejer_integrand π e₁ e₂ N f w₂)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only; rw [Complex.ofReal_sub, mul_sub]
  rw [hsub]
  have hS_sub : ∀ θ : T2, fejerSum π e₁ e₂ N θ (w₁ - w₂) = fejerSum π e₁ e₂ N θ w₁ - fejerSum π e₁ e₂ N θ w₂ := fun θ => by
    dsimp only [fejerSum]; simp_rw [map_sub, smul_sub, Finset.sum_sub_distrib, smul_sub]
  by_cases h0 : ‖w₁‖ = 0
  · have hw1 : w₁ = 0 := norm_eq_zero.mp h0
    have hw2 : w₂ = 0 := norm_eq_zero.mp (hnorm ▸ h0)
    subst hw1; subst hw2; simp [fejerSum]
  · by_cases hd0 : ‖w₁ - w₂‖ = 0
    · have heq : w₁ = w₂ := sub_eq_zero.mp (norm_eq_zero.mp hd0)
      subst heq; simp
    · have hw1_pos : 0 < ‖w₁‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hd_pos : 0 < ‖w₁ - w₂‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
      set t : ℝ := ‖w₁ - w₂‖ / (2 * ‖w₁‖)
      have ht_pos : 0 < t := by positivity
      have hint1 : Integrable (fun θ : T2 => ‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2) :=
        (((continuous_fejerSum π e₁ e₂ N w₁).norm).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hint2 : Integrable (fun θ : T2 => ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2) :=
        (((continuous_fejerSum π e₁ e₂ N w₂).norm).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hintd : Integrable (fun θ : T2 => ‖fejerSum π e₁ e₂ N θ (w₁ - w₂)‖ ^ 2) :=
        (((continuous_fejerSum π e₁ e₂ N (w₁ - w₂)).norm).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      have hint12 : Integrable (fun θ : T2 => t * (‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2 + ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2)) :=
        (hint1.add hint2).const_mul t
      have hintd' : Integrable (fun θ : T2 => (2 * t)⁻¹ * ‖fejerSum π e₁ e₂ N θ (w₁ - w₂)‖ ^ 2) :=
        hintd.const_mul (2 * t)⁻¹
      have hdom : Integrable (fun θ : T2 =>
          ‖f‖ * (t * (‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2 + ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2) +
            (2 * t)⁻¹ * ‖fejerSum π e₁ e₂ N θ (w₁ - w₂)‖ ^ 2)) :=
        (hint12.add hintd').const_mul ‖f‖
      calc ‖∫ θ : T2, f θ * (((‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2 - ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2 : ℝ) : ℂ))‖
          ≤ ∫ θ : T2, ‖f θ * (((‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2 - ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2 : ℝ) : ℂ))‖ :=
            norm_integral_le_integral_norm _
        _ ≤ ∫ θ : T2, ‖f‖ * (t * (‖fejerSum π e₁ e₂ N θ w₁‖ ^ 2 + ‖fejerSum π e₁ e₂ N θ w₂‖ ^ 2) +
              (2 * t)⁻¹ * ‖fejerSum π e₁ e₂ N θ (w₁ - w₂)‖ ^ 2) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hdom
              (Filter.Eventually.of_forall fun θ => ?_)
            dsimp only
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            set a := ‖fejerSum π e₁ e₂ N θ w₁‖
            set b := ‖fejerSum π e₁ e₂ N θ w₂‖
            set c := ‖fejerSum π e₁ e₂ N θ (w₁ - w₂)‖
            have hcab : |a - b| ≤ c := by
              dsimp only [a, b, c]; rw [hS_sub θ]; exact abs_norm_sub_norm_le _ _
            have hdiff : |a ^ 2 - b ^ 2| ≤ (a + b) * c := by
              rw [show a ^ 2 - b ^ 2 = (a + b) * (a - b) by ring, abs_mul,
                abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
              exact mul_le_mul_of_nonneg_left hcab (add_nonneg (norm_nonneg _) (norm_nonneg _))
            have hamgm : (a + b) * c ≤ t * (a ^ 2 + b ^ 2) + (2 * t)⁻¹ * c ^ 2 := by
              have hsq1 : (2 * t) * ((a + b) * c) ≤ (2 * t) * (t * (a ^ 2 + b ^ 2) + (2 * t)⁻¹ * c ^ 2) := by
                have heq : (2 * t) * (t * (a ^ 2 + b ^ 2) + (2 * t)⁻¹ * c ^ 2) =
                    2 * t ^ 2 * (a ^ 2 + b ^ 2) + c ^ 2 := by field_simp [ne_of_gt ht_pos]
                rw [heq]
                have h2ab : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by nlinarith [sq_nonneg (a - b)]
                have hsq2 : 0 ≤ (t * (a + b) - c) ^ 2 := sq_nonneg _
                nlinarith [sq_nonneg t]
              exact le_of_mul_le_mul_left hsq1 (by positivity)
            exact mul_le_mul (f.norm_coe_le_norm θ) (hdiff.trans hamgm) (abs_nonneg _) (norm_nonneg f)
        _ = ‖f‖ * (t * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) + (2 * t)⁻¹ * ‖w₁ - w₂‖ ^ 2) := by
            rw [integral_const_mul, integral_add hint12 hintd', integral_const_mul, integral_add hint1 hint2,
              integral_const_mul, integral_fejerSum_norm_sq π he₁₂ hN w₁,
              integral_fejerSum_norm_sq π he₁₂ hN w₂, integral_fejerSum_norm_sq π he₁₂ hN (w₁ - w₂)]
        _ = 2 * ‖f‖ * ‖w₁‖ * ‖w₁ - w₂‖ := by
            rw [← hnorm]; dsimp only [t]; field_simp [ne_of_gt hw1_pos, ne_of_gt hd_pos]; ring

/-- Existence of the limiting spectral functional `specL` for every `f : C(T2, ℂ)`. -/
lemma fejerFunc_cauchy {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f : C(T2, ℂ)) (w : V) :
    ∃ L : ℂ, Tendsto (fun N => fejerFunc π e₁ e₂ N f w) atTop (𝓝 L) := by
  have hspan : ∀ p ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin 2))),
      ∃ L : ℂ, Tendsto (fun N => fejerFunc π e₁ e₂ N p w) atTop (𝓝 L) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, rfl⟩ := hg
      refine ⟨⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ, ?_⟩
      have ht : ∀ a : ℕ, Tendsto (fun N : ℕ => (((N - a : ℕ) : ℂ) / (N : ℂ))) atTop (𝓝 (1 : ℂ)) := fun a => by
        have h1 : Tendsto (fun N : ℕ => (1 : ℂ) - ((a : ℂ) / (N : ℂ))) atTop (𝓝 (1 : ℂ)) := by
          have hinv : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
            have := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
            simpa [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast] using
              (Complex.continuous_ofReal.tendsto 0).comp this
          have hmul : Tendsto (fun N : ℕ => (a : ℂ) * (N : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
            simpa using hinv.const_mul (a : ℂ)
          simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hmul
        refine h1.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop (max a 1)] with N hN
        have hNa : a ≤ N := le_trans (le_max_left _ _) hN
        have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
        have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        rw [Nat.cast_sub hNa]; field_simp [hNne]
      have hprod := ((ht (k 0).natAbs).mul (ht (k 1).natAbs)).mul_const ⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ
      simp only [one_mul] at hprod
      refine hprod.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (max 1 (max (k 0).natAbs (k 1).natAbs))] with N hN
      exact (fejerFunc_mFourier π he₁₂ k N (le_trans (le_max_left _ _) hN)
        (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)) w).symm
    | zero =>
      refine ⟨0, tendsto_const_nhds.congr fun N => by simp [fejerFunc]⟩
    | add x y _ _ hx hy =>
      obtain ⟨Lx, hLx⟩ := hx; obtain ⟨Ly, hLy⟩ := hy
      refine ⟨Lx + Ly, (hLx.add hLy).congr fun N => ?_⟩
      dsimp only [fejerFunc]
      rw [← integral_add (integrable_fejer_integrand π e₁ e₂ N x w) (integrable_fejer_integrand π e₁ e₂ N y w)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_); simp [add_mul]
    | smul c x _ hx =>
      obtain ⟨Lx, hLx⟩ := hx
      refine ⟨c * Lx, (hLx.const_mul c).congr fun N => ?_⟩
      dsimp only [fejerFunc]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_); simp [mul_assoc]
  refine cauchySeq_tendsto_of_complete ?_
  rw [Metric.cauchySeq_iff]
  intro ε hε
  by_cases hw0 : ‖w‖ = 0
  · refine ⟨1, fun m hm n hn => ?_⟩
    have hm0 := norm_fejerFunc_le π he₁₂ hm f w
    have hn0 := norm_fejerFunc_le π he₁₂ hn f w
    rw [hw0, zero_pow two_ne_zero, mul_zero, norm_le_zero_iff] at hm0 hn0
    rw [hm0, hn0, dist_self]; exact hε
  · have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)) 2
    have hmem : f ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin 2)))).topologicalClosure := by
      rw [UnitAddTorus.span_mFourier_closure_eq_top]; trivial
    obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hmem (ε / (3 * ‖w‖ ^ 2)) (by positivity)
    obtain ⟨Lp, hLp⟩ := hspan p hp
    have hcauchy_p := Metric.cauchySeq_iff.mp hLp.cauchySeq (ε / 3) (by positivity)
    obtain ⟨N0, hN0⟩ := hcauchy_p
    refine ⟨max N0 1, fun m hm n hn => ?_⟩
    have hm1 : 1 ≤ m := le_trans (le_max_right _ _) hm
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
    have hsub_eq : ∀ k, fejerFunc π e₁ e₂ k f w - fejerFunc π e₁ e₂ k p w = fejerFunc π e₁ e₂ k (f - p) w := fun k => by
      dsimp only [fejerFunc]
      rw [← integral_sub (integrable_fejer_integrand π e₁ e₂ k f w) (integrable_fejer_integrand π e₁ e₂ k p w)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_); simp [sub_mul]
    have hfp : ‖f - p‖ < ε / (3 * ‖w‖ ^ 2) := by rwa [dist_eq_norm] at hdist
    have hm_err : dist (fejerFunc π e₁ e₂ m f w) (fejerFunc π e₁ e₂ m p w) < ε / 3 := by
      rw [dist_eq_norm, hsub_eq m]
      calc ‖fejerFunc π e₁ e₂ m (f - p) w‖ ≤ ‖f - p‖ * ‖w‖ ^ 2 := norm_fejerFunc_le π he₁₂ hm1 (f - p) w
        _ < (ε / (3 * ‖w‖ ^ 2)) * ‖w‖ ^ 2 := mul_lt_mul_of_pos_right hfp hwpos
        _ = ε / 3 := by field_simp [ne_of_gt hwpos]
    have hn_err : dist (fejerFunc π e₁ e₂ n p w) (fejerFunc π e₁ e₂ n f w) < ε / 3 := by
      rw [dist_comm, dist_eq_norm, hsub_eq n]
      calc ‖fejerFunc π e₁ e₂ n (f - p) w‖ ≤ ‖f - p‖ * ‖w‖ ^ 2 := norm_fejerFunc_le π he₁₂ hn1 (f - p) w
        _ < (ε / (3 * ‖w‖ ^ 2)) * ‖w‖ ^ 2 := mul_lt_mul_of_pos_right hfp hwpos
        _ = ε / 3 := by field_simp [ne_of_gt hwpos]
    have hmn_p := hN0 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
    calc dist (fejerFunc π e₁ e₂ m f w) (fejerFunc π e₁ e₂ n f w)
        ≤ dist (fejerFunc π e₁ e₂ m f w) (fejerFunc π e₁ e₂ m p w) +
          dist (fejerFunc π e₁ e₂ m p w) (fejerFunc π e₁ e₂ n p w) +
          dist (fejerFunc π e₁ e₂ n p w) (fejerFunc π e₁ e₂ n f w) := by
            linarith [dist_triangle (fejerFunc π e₁ e₂ m f w) (fejerFunc π e₁ e₂ m p w) (fejerFunc π e₁ e₂ n f w),
              dist_triangle (fejerFunc π e₁ e₂ m p w) (fejerFunc π e₁ e₂ n p w) (fejerFunc π e₁ e₂ n f w)]
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith
      _ = ε := by ring

def specL {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f : C(T2, ℂ)) (w : V) : ℂ :=
  Classical.choose (fejerFunc_cauchy π he₁₂ f w)

lemma specL_tendsto {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f : C(T2, ℂ)) (w : V) :
    Tendsto (fun N => fejerFunc π e₁ e₂ N f w) atTop (𝓝 (specL π he₁₂ f w)) :=
  Classical.choose_spec (fejerFunc_cauchy π he₁₂ f w)

lemma specL_mFourier {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (k : Fin 2 → ℤ) (w : V) :
    specL π he₁₂ (UnitAddTorus.mFourier (d := Fin 2) k) w = ⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ := by
  have ht : ∀ a : ℕ, Tendsto (fun N : ℕ => (((N - a : ℕ) : ℂ) / (N : ℂ))) atTop (𝓝 (1 : ℂ)) := fun a => by
    have h1 : Tendsto (fun N : ℕ => (1 : ℂ) - ((a : ℂ) / (N : ℂ))) atTop (𝓝 (1 : ℂ)) := by
      have hinv : Tendsto (fun N : ℕ => (N : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
        have := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
        simpa [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast] using
          (Complex.continuous_ofReal.tendsto 0).comp this
      have hmul : Tendsto (fun N : ℕ => (a : ℂ) * (N : ℂ)⁻¹) atTop (𝓝 (0 : ℂ)) := by
        simpa using hinv.const_mul (a : ℂ)
      simpa [div_eq_mul_inv] using tendsto_const_nhds.sub hmul
    refine h1.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (max a 1)] with N hN
    have hNa : a ≤ N := le_trans (le_max_left _ _) hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [Nat.cast_sub hNa]; field_simp [hNne]
  have hprod := ((ht (k 0).natAbs).mul (ht (k 1).natAbs)).mul_const ⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ
  simp only [one_mul] at hprod
  have hlim : Tendsto (fun N => fejerFunc π e₁ e₂ N (UnitAddTorus.mFourier (d := Fin 2) k) w)
      atTop (𝓝 ⟪w, π (e₁ ^ (k 0) * e₂ ^ (k 1)) w⟫_ℂ) := by
    refine hprod.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (max 1 (max (k 0).natAbs (k 1).natAbs))] with N hN
    exact (fejerFunc_mFourier π he₁₂ k N (le_trans (le_max_left _ _) hN)
      (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hN))
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)) w).symm
  exact tendsto_nhds_unique (specL_tendsto π he₁₂ _ w) hlim

lemma specL_add {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f g : C(T2, ℂ)) (w : V) :
    specL π he₁₂ (f + g) w = specL π he₁₂ f w + specL π he₁₂ g w := by
  have hsum : Tendsto (fun N => fejerFunc π e₁ e₂ N (f + g) w) atTop
      (𝓝 (specL π he₁₂ f w + specL π he₁₂ g w)) := by
    refine ((specL_tendsto π he₁₂ f w).add (specL_tendsto π he₁₂ g w)).congr fun N => ?_
    dsimp only [fejerFunc]
    rw [← integral_add (integrable_fejer_integrand π e₁ e₂ N f w) (integrable_fejer_integrand π e₁ e₂ N g w)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_); simp [add_mul]
  exact tendsto_nhds_unique (specL_tendsto π he₁₂ (f + g) w) hsum

lemma specL_smul {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (c : ℂ) (f : C(T2, ℂ)) (w : V) :
    specL π he₁₂ (c • f) w = c * specL π he₁₂ f w := by
  have hsm : Tendsto (fun N => fejerFunc π e₁ e₂ N (c • f) w) atTop (𝓝 (c * specL π he₁₂ f w)) := by
    refine ((specL_tendsto π he₁₂ f w).const_mul c).congr fun N => ?_
    dsimp only [fejerFunc]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_); simp [mul_assoc]
  exact tendsto_nhds_unique (specL_tendsto π he₁₂ (c • f) w) hsm

lemma specL_zero {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (w : V) :
    specL π he₁₂ 0 w = 0 := by
  have h := specL_smul π he₁₂ (0 : ℂ) (0 : C(T2, ℂ)) w
  rw [zero_smul ℂ (0 : C(T2, ℂ)), zero_mul] at h; exact h

lemma specL_sub {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f g : C(T2, ℂ)) (w : V) :
    specL π he₁₂ (f - g) w = specL π he₁₂ f w - specL π he₁₂ g w := by
  rw [sub_eq_add_neg, specL_add, show -g = (-1 : ℂ) • g by ext; simp, specL_smul]; ring

lemma specL_norm_le {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f : C(T2, ℂ)) (w : V) :
    ‖specL π he₁₂ f w‖ ≤ ‖f‖ * ‖w‖ ^ 2 :=
  le_of_tendsto ((specL_tendsto π he₁₂ f w).norm)
    (Filter.eventually_atTop.mpr ⟨1, fun _ hN => norm_fejerFunc_le π he₁₂ hN f w⟩)

lemma specL_sub_w_le {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (f : C(T2, ℂ))
    {w₁ w₂ : V} (hnorm : ‖w₁‖ = ‖w₂‖) :
    ‖specL π he₁₂ f w₁ - specL π he₁₂ f w₂‖ ≤ 2 * ‖f‖ * ‖w₁‖ * ‖w₁ - w₂‖ :=
  le_of_tendsto (((specL_tendsto π he₁₂ f w₁).sub (specL_tendsto π he₁₂ f w₂)).norm)
    (Filter.eventually_atTop.mpr ⟨1, fun _ hN => norm_fejerFunc_sub_w_le π he₁₂ hN f hnorm⟩)

def ofRealC (f : C(T2, ℝ)) : C(T2, ℂ) :=
  ⟨fun θ => (f θ : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

lemma specL_ofReal_mono {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    {f g : C(T2, ℝ)} (hfg : ∀ θ, f θ ≤ g θ) (w : V) :
    (specL π he₁₂ (ofRealC f) w).re ≤ (specL π he₁₂ (ofRealC g) w).re := by
  refine le_of_tendsto_of_tendsto ((Complex.continuous_re.tendsto _).comp (specL_tendsto π he₁₂ (ofRealC f) w))
    ((Complex.continuous_re.tendsto _).comp (specL_tendsto π he₁₂ (ofRealC g) w))
    (Filter.Eventually.of_forall fun N => ?_)
  dsimp only [Function.comp_apply, fejerFunc, ofRealC, ContinuousMap.coe_mk]
  have hf_re : (∫ θ : T2, (f θ : ℂ) * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ)).re =
      ∫ θ : T2, f θ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 := by
    simp_rw [← Complex.ofReal_mul]
    have hof : ∫ θ : T2, ((f θ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) =
        ((∫ θ : T2, f θ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
    rw [hof, Complex.ofReal_re]
  have hg_re : (∫ θ : T2, (g θ : ℂ) * ((‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ)).re =
      ∫ θ : T2, g θ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 := by
    simp_rw [← Complex.ofReal_mul]
    have hof : ∫ θ : T2, ((g θ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) =
        ((∫ θ : T2, g θ * ‖fejerSum π e₁ e₂ N θ w‖ ^ 2 : ℝ) : ℂ) := integral_ofReal
    rw [hof, Complex.ofReal_re]
  rw [hf_re, hg_re]
  refine integral_mono
    ((f.continuous.mul (((continuous_fejerSum π e₁ e₂ N w).norm).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    ((g.continuous.mul (((continuous_fejerSum π e₁ e₂ N w).norm).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun θ => mul_le_mul_of_nonneg_right (hfg θ) (sq_nonneg _))

lemma specL_comp_phiA {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ a : Γ} (he₁₂ : Commute e₁ e₂)
    (ha1 : a * e₁ * a⁻¹ = e₁) (ha2 : a * e₂ * a⁻¹ = e₁ * e₂)
    (k : ℤ) (f : C(T2, ℂ)) (w : V) :
    specL π he₁₂ (f.comp (phiA k)) w = specL π he₁₂ f (π (a ^ k) w) := by
  have hconj1 : ∀ m : ℤ, a ^ (-m) * e₁ * a ^ m = e₁ := fun m => by
    have h1 : a⁻¹ * e₁ * a = e₁ := by
      have := congrArg (fun z => a⁻¹ * z * a) ha1; simpa [mul_assoc] using this.symm
    have hnat : ∀ n : ℕ, a⁻¹ ^ n * e₁ * a ^ n = e₁ := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', pow_succ, show a⁻¹ * a⁻¹ ^ n * e₁ * (a ^ n * a) = a⁻¹ * (a⁻¹ ^ n * e₁ * a ^ n) * a by group,
          ih, h1]
    cases m with
    | ofNat n =>
      rw [_root_.zpow_neg]
      change (a ^ (n : ℤ))⁻¹ * e₁ * a ^ (n : ℤ) = e₁
      rw [zpow_natCast, ← inv_pow]; exact hnat n
    | negSucc n =>
      have hpos : ∀ r : ℕ, a ^ r * e₁ * a⁻¹ ^ r = e₁ := fun r => by
        induction r with
        | zero => simp
        | succ r ih =>
          rw [pow_succ', pow_succ, show a * a ^ r * e₁ * (a⁻¹ ^ r * a⁻¹) = a * (a ^ r * e₁ * a⁻¹ ^ r) * a⁻¹ by group,
            ih, ha1]
      rw [Int.negSucc_eq, neg_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        _root_.zpow_neg, zpow_natCast, ← inv_pow]
      exact hpos (n + 1)
  have hconj2 : ∀ m : ℤ, a ^ (-m) * e₂ * a ^ m = e₁ ^ (-m) * e₂ := fun m => by
    have h1 : a⁻¹ * e₂ * a = e₁⁻¹ * e₂ := by
      have := congrArg (fun z => a⁻¹ * z * a) ha2
      have h1a : a⁻¹ * (e₁ * e₂) * a = (a⁻¹ * e₁ * a) * (a⁻¹ * e₂ * a) := by group
      have h1b : a⁻¹ * e₁ * a = e₁ := by simpa using hconj1 1
      rw [h1a, h1b] at this
      have h2 := congrArg (e₁⁻¹ * ·) this.symm; simpa [mul_assoc] using h2
    have he1_inv : ∀ r : ℕ, a⁻¹ * e₁⁻¹ ^ r * a = e₁⁻¹ ^ r := fun r => by
      have h1b : a⁻¹ * e₁ * a = e₁ := by simpa using hconj1 1
      have hinv : a⁻¹ * e₁⁻¹ * a = e₁⁻¹ := by
        have := congrArg (·⁻¹) h1b; simpa [mul_assoc] using this
      induction r with
      | zero => simp
      | succ r ih' =>
        rw [pow_succ, show a⁻¹ * (e₁⁻¹ ^ r * e₁⁻¹) * a = (a⁻¹ * e₁⁻¹ ^ r * a) * (a⁻¹ * e₁⁻¹ * a) by group,
          ih', hinv]
    have hnat : ∀ n : ℕ, a⁻¹ ^ n * e₂ * a ^ n = e₁⁻¹ ^ n * e₂ := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', pow_succ, show a⁻¹ * a⁻¹ ^ n * e₂ * (a ^ n * a) = a⁻¹ * (a⁻¹ ^ n * e₂ * a ^ n) * a by group,
          ih, show a⁻¹ * (e₁⁻¹ ^ n * e₂) * a = (a⁻¹ * e₁⁻¹ ^ n * a) * (a⁻¹ * e₂ * a) by group,
          he1_inv n, h1, ← mul_assoc, ← pow_succ]
    have he1_p : ∀ r : ℕ, a * e₁ ^ r * a⁻¹ = e₁ ^ r := fun r => by
      induction r with
      | zero => simp
      | succ r ih' =>
        rw [pow_succ, show a * (e₁ ^ r * e₁) * a⁻¹ = (a * e₁ ^ r * a⁻¹) * (a * e₁ * a⁻¹) by group,
          ih', ha1]
    have hpos : ∀ r : ℕ, a ^ r * e₂ * a⁻¹ ^ r = e₁ ^ r * e₂ := fun r => by
      induction r with
      | zero => simp
      | succ r ih =>
        rw [pow_succ', pow_succ, show a * a ^ r * e₂ * (a⁻¹ ^ r * a⁻¹) = a * (a ^ r * e₂ * a⁻¹ ^ r) * a⁻¹ by group,
          ih, show a * (e₁ ^ r * e₂) * a⁻¹ = (a * e₁ ^ r * a⁻¹) * (a * e₂ * a⁻¹) by group,
          he1_p r, ha2, ← mul_assoc, ← pow_succ]
    cases m with
    | ofNat n =>
      rw [_root_.zpow_neg, _root_.zpow_neg]
      change (a ^ (n : ℤ))⁻¹ * e₂ * a ^ (n : ℤ) = (e₁ ^ (n : ℤ))⁻¹ * e₂
      rw [zpow_natCast, zpow_natCast, ← inv_pow, ← inv_pow]
      exact hnat n
    | negSucc n =>
      rw [Int.negSucc_eq, neg_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        _root_.zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow]
      exact hpos (n + 1)
  have hconj_pow : ∀ n : Fin 2 → ℤ,
      (a ^ k)⁻¹ * (e₁ ^ (n 0) * e₂ ^ (n 1)) * (a ^ k) = e₁ ^ (n 0 - k * n 1) * e₂ ^ (n 1) := by
    intro n
    let φ : Γ →* Γ := MulAut.conj (a ^ (-k))
    have hφ1 : φ e₁ = e₁ := by change a ^ (-k) * e₁ * (a ^ (-k))⁻¹ = e₁; rw [_root_.zpow_neg, inv_inv, ← _root_.zpow_neg]; exact hconj1 k
    have hφ2 : φ e₂ = e₁ ^ (-k) * e₂ := by change a ^ (-k) * e₂ * (a ^ (-k))⁻¹ = _; rw [_root_.zpow_neg, inv_inv, ← _root_.zpow_neg]; exact hconj2 k
    have hφ_eq : (a ^ k)⁻¹ * (e₁ ^ (n 0) * e₂ ^ (n 1)) * (a ^ k) = φ (e₁ ^ (n 0) * e₂ ^ (n 1)) := by
      change _ = a ^ (-k) * (e₁ ^ (n 0) * e₂ ^ (n 1)) * (a ^ (-k))⁻¹; rw [_root_.zpow_neg, inv_inv]
    rw [hφ_eq, map_mul, map_zpow, map_zpow, hφ1, hφ2,
      (he₁₂.zpow_left (-k)).mul_zpow, ← mul_assoc, ← _root_.zpow_mul, ← _root_.zpow_add]
    congr 2; ring
  have hspan : ∀ p ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin 2))),
      specL π he₁₂ (p.comp (phiA k)) w = specL π he₁₂ p (π (a ^ k) w) := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨n, rfl⟩ := hg
      rw [mFourier_comp_phiA, specL_mFourier, specL_mFourier]
      have hstep : ⟪π (a ^ k) w, π (e₁ ^ (n 0) * e₂ ^ (n 1)) (π (a ^ k) w)⟫_ℂ =
          ⟪w, π ((a ^ k)⁻¹ * (e₁ ^ (n 0) * e₂ ^ (n 1)) * a ^ k) w⟫_ℂ := by
        rw [← (π (a ^ k)⁻¹).inner_map_map, rep_inv_mul, ← rep_mul, ← rep_mul]
      rw [hstep, hconj_pow n]; rfl
    | zero =>
      have h0 : (0 : C(T2, ℂ)).comp (phiA k) = 0 := by ext; rfl
      rw [h0, specL_zero, specL_zero]
    | add x y _ _ hx hy =>
      have hadd : (x + y).comp (phiA k) = x.comp (phiA k) + y.comp (phiA k) := by ext; rfl
      rw [hadd, specL_add, specL_add, hx, hy]
    | smul c x _ hx =>
      have hsm : (c • x).comp (phiA k) = c • (x.comp (phiA k)) := by ext; rfl
      rw [hsm, specL_smul, specL_smul, hx]
  by_contra hne
  have hpos : 0 < ‖specL π he₁₂ (f.comp (phiA k)) w - specL π he₁₂ f (π (a ^ k) w)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  by_cases hw0 : ‖w‖ = 0
  · have h1 := specL_norm_le π he₁₂ (f.comp (phiA k)) w
    have h2 := specL_norm_le π he₁₂ f (π (a ^ k) w)
    rw [(π (a ^ k)).norm_map, hw0, zero_pow two_ne_zero, mul_zero, norm_le_zero_iff] at h2
    rw [hw0, zero_pow two_ne_zero, mul_zero, norm_le_zero_iff] at h1
    exact hne (by rw [h1, h2])
  · have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)) 2
    set ε := ‖specL π he₁₂ (f.comp (phiA k)) w - specL π he₁₂ f (π (a ^ k) w)‖
    have hmem : f ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin 2)))).topologicalClosure := by
      rw [UnitAddTorus.span_mFourier_closure_eq_top]; trivial
    obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.mp hmem (ε / (3 * ‖w‖ ^ 2)) (by positivity)
    have hfp : ‖f - p‖ < ε / (3 * ‖w‖ ^ 2) := by rwa [dist_eq_norm] at hdist
    have hcomp_le : ‖(f - p).comp (phiA k)‖ ≤ ‖f - p‖ :=
      (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun θ => (f - p).norm_coe_le_norm (phiA k θ)
    have h1 : ‖specL π he₁₂ (f.comp (phiA k)) w - specL π he₁₂ (p.comp (phiA k)) w‖ < ε / 3 := by
      rw [← specL_sub, show f.comp (phiA k) - p.comp (phiA k) = (f - p).comp (phiA k) by ext; rfl]
      calc ‖specL π he₁₂ ((f - p).comp (phiA k)) w‖ ≤ ‖(f - p).comp (phiA k)‖ * ‖w‖ ^ 2 := specL_norm_le π he₁₂ _ w
        _ ≤ ‖f - p‖ * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right hcomp_le (le_of_lt hwpos)
        _ < (ε / (3 * ‖w‖ ^ 2)) * ‖w‖ ^ 2 := mul_lt_mul_of_pos_right hfp hwpos
        _ = ε / 3 := by field_simp [ne_of_gt hwpos]
    have h2 : ‖specL π he₁₂ p (π (a ^ k) w) - specL π he₁₂ f (π (a ^ k) w)‖ < ε / 3 := by
      rw [norm_sub_rev, ← specL_sub]
      calc ‖specL π he₁₂ (f - p) (π (a ^ k) w)‖ ≤ ‖f - p‖ * ‖π (a ^ k) w‖ ^ 2 := specL_norm_le π he₁₂ _ _
        _ = ‖f - p‖ * ‖w‖ ^ 2 := by rw [(π (a ^ k)).norm_map]
        _ < (ε / (3 * ‖w‖ ^ 2)) * ‖w‖ ^ 2 := mul_lt_mul_of_pos_right hfp hwpos
        _ = ε / 3 := by field_simp [ne_of_gt hwpos]
    have htri : ε ≤ ‖specL π he₁₂ (f.comp (phiA k)) w - specL π he₁₂ (p.comp (phiA k)) w‖ +
        ‖specL π he₁₂ p (π (a ^ k) w) - specL π he₁₂ f (π (a ^ k) w)‖ := by
      dsimp only [ε]; rw [← hspan p hp]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith

lemma specL_comp_phiB {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ b : Γ} (he₁₂ : Commute e₁ e₂)
    (hb1 : b * e₁ * b⁻¹ = e₁ * e₂) (hb2 : b * e₂ * b⁻¹ = e₂)
    (k : ℤ) (f : C(T2, ℂ)) (w : V) :
    specL π he₁₂ (f.comp (phiB k)) w = specL π he₁₂ f (π (b ^ k) w) := by
  let sw : C(T2, T2) := ⟨fun p i => p (1 - i), continuous_pi fun i => by fin_cases i <;> exact continuous_apply _⟩
  have hsw_inv : ∀ p, sw (sw p) = p := fun p => by ext i; fin_cases i <;> rfl
  have hfejer_sw : ∀ (N : ℕ) (g : C(T2, ℂ)) (u : V),
      fejerFunc π e₁ e₂ N g u = fejerFunc π e₂ e₁ N (g.comp sw) u := fun N g u => by
    dsimp only [fejerFunc]
    have hS : ∀ θ : T2, fejerSum π e₂ e₁ N (sw θ) u = fejerSum π e₁ e₂ N θ u := fun θ => by
      dsimp only [fejerSum]; congr 1; rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      have hmf : UnitAddTorus.mFourier (d := Fin 2) ![-(n : ℤ), -(m : ℤ)] (sw θ) =
          UnitAddTorus.mFourier (d := Fin 2) ![-(m : ℤ), -(n : ℤ)] θ := by
        change ∏ i : Fin 2, fourier (T := (1 : ℝ)) _ _ = ∏ i : Fin 2, fourier (T := (1 : ℝ)) _ _
        rw [Fin.prod_univ_two, Fin.prod_univ_two]
        change fourier (T := (1 : ℝ)) (-(n : ℤ)) (θ 1) * fourier (T := (1 : ℝ)) (-(m : ℤ)) (θ 0) =
          fourier (T := (1 : ℝ)) (-(m : ℤ)) (θ 0) * fourier (T := (1 : ℝ)) (-(n : ℤ)) (θ 1)
        ring
      rw [hmf, (he₁₂.pow_left m).pow_right n |>.eq]
    let swE : T2 ≃ᵐ T2 :=
      MeasurableEquiv.piCongrLeft (fun _ : Fin 2 => UnitAddCircle) (Equiv.subLeft (1 : Fin 2))
    have hswE : ∀ θ : T2, swE θ = sw θ := fun θ => by
      ext i; fin_cases i <;> rfl
    have hmp : MeasurePreserving swE volume volume :=
      MeasureTheory.measurePreserving_piCongrLeft (fun _ => volume) (Equiv.subLeft (1 : Fin 2))
    rw [← hmp.integral_comp' (g := fun θ => (g.comp sw) θ * ((‖fejerSum π e₂ e₁ N θ u‖ ^ 2 : ℝ) : ℂ))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    dsimp only [Function.comp_apply]
    rw [hswE θ, ContinuousMap.comp_apply, hsw_inv, hS]
  have hspec_sw : ∀ (g : C(T2, ℂ)) (u : V),
      specL π he₁₂ g u = specL π he₁₂.symm (g.comp sw) u := fun g u =>
    tendsto_nhds_unique (specL_tendsto π he₁₂ g u)
      ((specL_tendsto π he₁₂.symm (g.comp sw) u).congr fun N => (hfejer_sw N g u).symm)
  rw [hspec_sw (f.comp (phiB k)) w, hspec_sw f (π (b ^ k) w)]
  have hcomm : (f.comp (phiB k)).comp sw = (f.comp sw).comp (phiA k) := by
    ext p; change f (phiB k (sw p)) = f (sw (phiA k p))
    congr 1; ext i; fin_cases i <;> rfl
  rw [hcomm]
  exact specL_comp_phiA π he₁₂.symm hb2 (by rw [hb1, he₁₂.eq]) k (f.comp sw) w

lemma specL_torusE {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂) (w : V) :
    (specL π he₁₂ (ofRealC ⟨torusE, continuous_torusE⟩) w).re =
      ‖π e₁ w - w‖ ^ 2 + ‖π e₂ w - w‖ ^ 2 := by
  have h1D : ∀ (i : Fin 2) (θ : T2),
      ((‖UnitAddTorus.mFourier (d := Fin 2) (Pi.single i 1) θ - 1‖ ^ 2 : ℝ) : ℂ) =
        (2 : ℂ) * UnitAddTorus.mFourier (d := Fin 2) 0 θ -
        UnitAddTorus.mFourier (d := Fin 2) (Pi.single i 1) θ -
        UnitAddTorus.mFourier (d := Fin 2) (-Pi.single i 1) θ := by
    intro i θ
    set z := UnitAddTorus.mFourier (d := Fin 2) (Pi.single i 1) θ
    have hz1 : ‖z‖ = 1 := by
      dsimp only [z]; rw [UnitAddTorus.mFourier_single, fourier_apply]; exact Circle.norm_coe _
    have hconj : (starRingEnd ℂ) z = UnitAddTorus.mFourier (d := Fin 2) (-Pi.single i 1) θ :=
      (UnitAddTorus.mFourier_neg (n := Pi.single i 1) (x := θ)).symm
    have hmul : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]; norm_num
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj,
      map_sub, map_one, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one, ← hconj]
    linear_combination hmul
  let m0 := UnitAddTorus.mFourier (d := Fin 2) 0
  let m1 := UnitAddTorus.mFourier (d := Fin 2) (Pi.single 0 1)
  let m1' := UnitAddTorus.mFourier (d := Fin 2) (-Pi.single 0 1)
  let m2 := UnitAddTorus.mFourier (d := Fin 2) (Pi.single 1 1)
  let m2' := UnitAddTorus.mFourier (d := Fin 2) (-Pi.single 1 1)
  have heq : ofRealC ⟨torusE, continuous_torusE⟩ =
      ((2 : ℂ) • m0 - m1 - m1') + ((2 : ℂ) • m0 - m2 - m2') := by
    ext θ; simp only [ofRealC, torusE, ContinuousMap.coe_mk, Complex.ofReal_add,
      ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
    rw [h1D 0 θ, h1D 1 θ]
  rw [heq, specL_add, specL_sub, specL_sub, specL_sub, specL_sub, specL_smul]
  simp only [m0, m1, m1', m2, m2', specL_mFourier]
  have hsingle0 : e₁ ^ ((Pi.single 0 (1 : ℤ) : Fin 2 → ℤ) 0) * e₂ ^ ((Pi.single 0 (1 : ℤ) : Fin 2 → ℤ) 1) = e₁ := by simp
  have hsingle0' : e₁ ^ ((-Pi.single 0 (1 : ℤ) : Fin 2 → ℤ) 0) * e₂ ^ ((-Pi.single 0 (1 : ℤ) : Fin 2 → ℤ) 1) = e₁⁻¹ := by simp
  have hsingle1 : e₁ ^ ((Pi.single 1 (1 : ℤ) : Fin 2 → ℤ) 0) * e₂ ^ ((Pi.single 1 (1 : ℤ) : Fin 2 → ℤ) 1) = e₂ := by simp
  have hsingle1' : e₁ ^ ((-Pi.single 1 (1 : ℤ) : Fin 2 → ℤ) 0) * e₂ ^ ((-Pi.single 1 (1 : ℤ) : Fin 2 → ℤ) 1) = e₂⁻¹ := by simp
  simp only [Pi.zero_apply, zpow_zero, mul_one, rep_one, hsingle0, hsingle0', hsingle1, hsingle1']
  have hnorm_g : ∀ g : Γ, ‖π g w - w‖ ^ 2 = (2 * ⟪w, w⟫_ℂ - ⟪w, π g w⟫_ℂ - ⟪w, π g⁻¹ w⟫_ℂ).re := fun g => by
    have h1 := norm_sub_sq (𝕜 := ℂ) (π g w) w
    rw [(π g).norm_map] at h1
    have h2 : ⟪w, π g⁻¹ w⟫_ℂ = ⟪π g w, w⟫_ℂ := by
      rw [← (π g).inner_map_map w (π g⁻¹ w), rep_mul_inv]
    have h3 : (⟪w, π g w⟫_ℂ).re = (⟪π g w, w⟫_ℂ).re := by
      rw [← inner_conj_symm]; exact Complex.conj_re _
    have h4 : (⟪w, w⟫_ℂ).re = ‖w‖ ^ 2 := by
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; exact Complex.ofReal_re _
    rw [h2, Complex.sub_re, Complex.sub_re, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
      Complex.re_ofReal_mul, h4, h3]
    change _ = 2 * ‖w‖ ^ 2 - RCLike.re ⟪π g w, w⟫_ℂ - RCLike.re ⟪π g w, w⟫_ℂ
    linarith
  rw [Complex.add_re, hnorm_g e₁, hnorm_g e₂]

lemma specL_fejer2D {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    {M : ℕ} (_hM : 1 ≤ M) (w : V) :
    (specL π he₁₂ (ofRealC ⟨fejer2D M, continuous_fejer2D M⟩) w).re =
      ‖(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w‖ ^ 2 := by
  let S4 := (Finset.range M ×ˢ Finset.range M) ×ˢ (Finset.range M ×ˢ Finset.range M)
  have heq : ofRealC ⟨fejer2D M, continuous_fejer2D M⟩ =
      ((((M : ℂ) ^ 2)⁻¹) ^ 2) • ∑ p ∈ S4,
        UnitAddTorus.mFourier (d := Fin 2) ![(p.2.1 : ℤ) - (p.1.1 : ℤ), (p.2.2 : ℤ) - (p.1.2 : ℤ)] := by
    ext θ
    simp only [ofRealC, fejer2D, ContinuousMap.coe_mk, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, smul_eq_mul, Complex.ofReal_mul]
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
      ← Complex.mul_conj, ← Complex.mul_conj]
    simp only [map_mul, map_inv₀, map_natCast, map_sum, ← fourier_neg]
    have hcoeff : ((M : ℂ)⁻¹ * ∑ m ∈ Finset.range M, fourier (m : ℤ) (θ 0)) *
        ((M : ℂ)⁻¹ * ∑ m' ∈ Finset.range M, fourier (-(m' : ℤ)) (θ 0)) *
        (((M : ℂ)⁻¹ * ∑ n ∈ Finset.range M, fourier (n : ℤ) (θ 1)) *
        ((M : ℂ)⁻¹ * ∑ n' ∈ Finset.range M, fourier (-(n' : ℤ)) (θ 1))) =
        ((((M : ℂ) ^ 2)⁻¹) ^ 2) *
          ((∑ m' ∈ Finset.range M, fourier (-(m' : ℤ)) (θ 0)) * (∑ m ∈ Finset.range M, fourier (m : ℤ) (θ 0)) *
          ((∑ n' ∈ Finset.range M, fourier (-(n' : ℤ)) (θ 1)) * (∑ n ∈ Finset.range M, fourier (n : ℤ) (θ 1)))) := by
      ring
    rw [hcoeff]; congr 1
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_product', ← Finset.sum_product',
      Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_bij (fun (p : (ℕ × ℕ) × (ℕ × ℕ)) _ => ((p.1.1, p.2.1), (p.1.2, p.2.2))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [S4, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨⟨hp.1.1, hp.2.1⟩, ⟨hp.1.2, hp.2.2⟩⟩
    · intro p₁ _ p₂ _ h
      rcases p₁ with ⟨⟨a1, b1⟩, ⟨c1, d1⟩⟩; rcases p₂ with ⟨⟨a2, b2⟩, ⟨c2, d2⟩⟩
      simp only [Prod.mk.injEq] at h; rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩; rfl
    · intro q hq
      refine ⟨((q.1.1, q.2.1), (q.1.2, q.2.2)), ?_, rfl⟩
      simp only [S4, Finset.mem_product, Finset.mem_range] at hq ⊢
      exact ⟨⟨hq.1.1, hq.2.1⟩, ⟨hq.1.2, hq.2.2⟩⟩
    · intro p _
      change (fourier (T := (1 : ℝ)) (-(p.1.1 : ℤ)) (θ 0) * fourier (T := (1 : ℝ)) (p.1.2 : ℤ) (θ 0)) *
          (fourier (T := (1 : ℝ)) (-(p.2.1 : ℤ)) (θ 1) * fourier (T := (1 : ℝ)) (p.2.2 : ℤ) (θ 1)) =
        ∏ i : Fin 2, fourier (T := (1 : ℝ)) (![(p.1.2 : ℤ) - (p.1.1 : ℤ), (p.2.2 : ℤ) - (p.2.1 : ℤ)] i) (θ i)
      rw [Fin.prod_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_eq_add_neg, fourier_add,
        add_comm (p.1.2 : ℤ), add_comm (p.2.2 : ℤ)]
  have hspec_sum : ∀ (s : Finset ((ℕ × ℕ) × (ℕ × ℕ))) (F : ((ℕ × ℕ) × (ℕ × ℕ)) → C(T2, ℂ)),
      specL π he₁₂ (∑ p ∈ s, F p) w = ∑ p ∈ s, specL π he₁₂ (F p) w := by
    intro s F
    classical
    induction s using Finset.induction with
    | empty => simp [specL_zero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, specL_add, ih]
  rw [heq, specL_smul, hspec_sum]
  simp_rw [specL_mFourier]
  have hrhs : (((‖(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w‖ ^ 2 : ℝ) : ℂ)) =
      ((((M : ℂ) ^ 2)⁻¹) ^ 2) * ∑ p ∈ S4,
        ⟪w, π (e₁ ^ ((p.2.1 : ℤ) - (p.1.1 : ℤ)) * e₂ ^ ((p.2.2 : ℤ) - (p.1.2 : ℤ))) w⟫_ℂ := by
    rw [show ((‖(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w‖ ^ 2 : ℝ) : ℂ) =
      ⟪(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w,
        (((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w⟫_ℂ by
      rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl]
    rw [inner_smul_left, inner_smul_right,
      show (starRingEnd ℂ) (((M : ℂ) ^ 2)⁻¹) = ((M : ℂ) ^ 2)⁻¹ by rw [map_inv₀, map_pow, map_natCast],
      ← mul_assoc, ← sq]
    congr 1
    rw [sum_inner]
    simp_rw [sum_inner, inner_sum, ← Finset.sum_product']
    refine Finset.sum_bij (fun p _ => ((p.1, p.2.1), (p.2.2.1, p.2.2.2))) ?_ ?_ ?_ ?_
    · intro p hp
      simp only [S4, Finset.mem_product, Finset.mem_range] at hp ⊢
      exact ⟨⟨hp.1, hp.2.1⟩, ⟨hp.2.2.1, hp.2.2.2⟩⟩
    · intro p₁ _ p₂ _ h
      rcases p₁ with ⟨a1, b1, c1, d1⟩; rcases p₂ with ⟨a2, b2, c2, d2⟩
      simp only [Prod.mk.injEq] at h; rcases h with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩; rfl
    · intro q hq
      refine ⟨(q.1.1, q.1.2, q.2.1, q.2.2), ?_, rfl⟩
      simp only [S4, Finset.mem_product, Finset.mem_range] at hq ⊢
      exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
    · intro p _
      rw [← (π (e₁ ^ p.1 * e₂ ^ p.2.1)⁻¹).inner_map_map, rep_inv_mul, ← rep_mul]
      refine congrArg (fun g => ⟪w, π g w⟫_ℂ) ?_
      rw [_root_.mul_inv_rev, ← zpow_natCast e₁, ← zpow_natCast e₂, ← zpow_natCast e₁, ← zpow_natCast e₂,
        ← _root_.zpow_neg, ← _root_.zpow_neg]
      have hc1 : Commute (e₂ ^ (-(p.2.1 : ℤ))) (e₁ ^ (-(p.1 : ℤ))) := (he₁₂.symm.zpow_left _).zpow_right _
      have hc2 : Commute (e₂ ^ (-(p.2.1 : ℤ))) (e₁ ^ (p.2.2.1 : ℤ)) := (he₁₂.symm.zpow_left _).zpow_right _
      calc e₂ ^ (-(p.2.1 : ℤ)) * e₁ ^ (-(p.1 : ℤ)) * (e₁ ^ (p.2.2.1 : ℤ) * e₂ ^ (p.2.2.2 : ℤ))
          = (e₁ ^ (-(p.1 : ℤ)) * e₂ ^ (-(p.2.1 : ℤ))) * (e₁ ^ (p.2.2.1 : ℤ) * e₂ ^ (p.2.2.2 : ℤ)) := by rw [hc1.eq]
        _ = e₁ ^ (-(p.1 : ℤ)) * (e₂ ^ (-(p.2.1 : ℤ)) * e₁ ^ (p.2.2.1 : ℤ)) * e₂ ^ (p.2.2.2 : ℤ) := by group
        _ = e₁ ^ (-(p.1 : ℤ)) * (e₁ ^ (p.2.2.1 : ℤ) * e₂ ^ (-(p.2.1 : ℤ))) * e₂ ^ (p.2.2.2 : ℤ) := by rw [hc2.eq]
        _ = (e₁ ^ (-(p.1 : ℤ)) * e₁ ^ (p.2.2.1 : ℤ)) * (e₂ ^ (-(p.2.1 : ℤ)) * e₂ ^ (p.2.2.2 : ℤ)) := by group
        _ = e₁ ^ ((p.2.2.1 : ℤ) - (p.1 : ℤ)) * e₂ ^ ((p.2.2.2 : ℤ) - (p.2.1 : ℤ)) := by
            rw [← _root_.zpow_add, ← _root_.zpow_add]; congr 2 <;> ring
  have hcongr : ∑ p ∈ S4, ⟪w, π (e₁ ^ ((![(p.2.1 : ℤ) - (p.1.1 : ℤ), (p.2.2 : ℤ) - (p.1.2 : ℤ)] : Fin 2 → ℤ) 0) *
      e₂ ^ ((![(p.2.1 : ℤ) - (p.1.1 : ℤ), (p.2.2 : ℤ) - (p.1.2 : ℤ)] : Fin 2 → ℤ) 1)) w⟫_ℂ =
      ∑ p ∈ S4, ⟪w, π (e₁ ^ ((p.2.1 : ℤ) - (p.1.1 : ℤ)) * e₂ ^ ((p.2.2 : ℤ) - (p.1.2 : ℤ))) w⟫_ℂ := rfl
  rw [hcongr, ← hrhs, Complex.ofReal_re]

lemma tendsto_double_avg_zero {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (π : Γ →* V ≃ₗᵢ[ℂ] V) {e₁ e₂ : Γ} (he₁₂ : Commute e₁ e₂)
    {w : V} (hw : w ∈ (invSubspace π (Subgroup.closure ({e₁, e₂} : Set Γ)))ᗮ) :
    Tendsto (fun M : ℕ =>
        ‖(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w‖ ^ 2)
      atTop (𝓝 (0 : ℝ)) := by
  let A₁ : ℕ → V → V := fun M u => ((M : ℂ)⁻¹) • ∑ m ∈ Finset.range M, (π e₁ ^ m) u
  let A₂ : ℕ → V → V := fun M u => ((M : ℂ)⁻¹) • ∑ n ∈ Finset.range M, (π e₂ ^ n) u
  have hcomp : ∀ M : ℕ, (((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w =
      A₁ M (A₂ M w) := fun M => by
    dsimp only [A₁, A₂]
    simp_rw [map_smul, map_sum, ← Finset.smul_sum, smul_smul, ← mul_inv, ← sq]
    congr 1; refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    rw [rep_mul, map_pow, map_pow]
  set p₂ : V := (fixedSubspace (π e₂)).starProjection w
  set p₁ : V := (fixedSubspace (π e₁)).starProjection p₂
  have hp₁_mem : p₁ ∈ invSubspace π (Subgroup.closure ({e₁, e₂} : Set Γ)) := by
    rw [invSubspace_closure]
    intro g hg
    rcases hg with hg | hg
    · rw [hg]; exact Submodule.coe_mem ((fixedSubspace (π e₁)).orthogonalProjectionOnto p₂)
    · rw [hg]
      have hcomm : ∀ u ∈ fixedSubspace (π e₁), π e₂ u ∈ fixedSubspace (π e₁) := by
        intro u hu; change π e₁ (π e₂ u) = π e₂ u
        rw [← rep_mul, he₁₂.eq, rep_mul, hu]
      have hcomm' : ∀ u ∈ fixedSubspace (π e₁), (π e₂).symm u ∈ fixedSubspace (π e₁) := by
        intro u hu
        have hinv : (π e₂).symm u = π e₂⁻¹ u := by apply (π e₂).injective; rw [(π e₂).apply_symm_apply, rep_mul_inv]
        rw [hinv]; change π e₁ (π e₂⁻¹ u) = π e₂⁻¹ u
        rw [← rep_mul, he₁₂.inv_right.eq, rep_mul, hu]
      have hpc := starProjection_comm_of_invariant (π e₂) (fixedSubspace (π e₁)) hcomm hcomm' p₂
      dsimp only [p₁]; rw [← hpc]
      exact congrArg _ (Submodule.coe_mem ((fixedSubspace (π e₂)).orthogonalProjectionOnto w))
  have hp₁_zero : p₁ = 0 := by
    have horth1 : ⟪p₁, p₂ - p₁⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal (fixedSubspace (π e₁)) _).mp ((fixedSubspace (π e₁)).sub_starProjection_mem_orthogonal p₂)
        p₁ (Submodule.coe_mem _)
    have horth2 : ⟪p₁, w - p₂⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal (fixedSubspace (π e₂)) _).mp ((fixedSubspace (π e₂)).sub_starProjection_mem_orthogonal w)
        p₁ (hp₁_mem e₂ (Subgroup.subset_closure (by simp)))
    have horthw : ⟪p₁, w⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ w).mp hw p₁ hp₁_mem
    have hself : ⟪p₁, p₁⟫_ℂ = 0 := by
      rw [inner_sub_right, sub_eq_zero] at horth1 horth2
      rw [← horth1, ← horth2, horthw]
    exact inner_self_eq_zero.mp hself
  have hA₁_le : ∀ (M : ℕ) (u : V), 1 ≤ M → ‖A₁ M u‖ ≤ ‖u‖ := fun M u hM => by
    dsimp only [A₁]
    rw [norm_smul, norm_inv, Complex.norm_natCast]
    calc (M : ℝ)⁻¹ * ‖∑ m ∈ Finset.range M, (π e₁ ^ m) u‖
        ≤ (M : ℝ)⁻¹ * ∑ m ∈ Finset.range M, ‖(π e₁ ^ m) u‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = (M : ℝ)⁻¹ * ((M : ℝ) * ‖u‖) := by
          congr 1; simp_rw [(π e₁ ^ _).norm_map, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ‖u‖ := by field_simp [show (M : ℝ) ≠ 0 by exact Nat.cast_ne_zero.mpr (by omega)]
  have hnorm_zero : Tendsto (fun M => ‖A₁ M (A₂ M w)‖) atTop (𝓝 (0 : ℝ)) := by
    refine squeeze_zero' (g := fun M => ‖A₂ M w - p₂‖ + ‖A₁ M p₂‖)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
    · filter_upwards [Filter.eventually_ge_atTop 1] with M hM
      have hsplit : A₁ M (A₂ M w) = A₁ M (A₂ M w - p₂) + A₁ M p₂ := by
        dsimp only [A₁]; simp_rw [map_sub, Finset.sum_sub_distrib, smul_sub]; abel
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add (hA₁_le M _ hM) le_rfl)
    · have h2 : Tendsto (fun M => ‖A₂ M w - p₂‖) atTop (𝓝 (0 : ℝ)) := by
        simpa [A₂, p₂, sub_self] using
          ((mean_ergodic_theorem (π e₂) w).sub (tendsto_const_nhds (x := p₂))).norm
      have h1 : Tendsto (fun M => ‖A₁ M p₂‖) atTop (𝓝 (0 : ℝ)) := by
        simpa [A₁, p₁, hp₁_zero] using (mean_ergodic_theorem (π e₁) p₂).norm
      simpa using h2.add h1
  simp_rw [hcomp]
  simpa [zero_pow two_ne_zero] using hnorm_zero.pow 2

/-- Relative Property (T) for `(F₂ ⋉ ℤ², ℤ²)` with explicit constant `1/6500`, proved elementarily
via the Fejér-kernel functional `specL` and continuous ping-pong on `T2`. -/
lemma rel_propT_F2_Z2 {Γ V : Type} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [CompleteSpace V] (π : Γ →* V ≃ₗᵢ[ℂ] V) (e₁ e₂ a b : Γ)
    (he₁₂ : Commute e₁ e₂)
    (ha1 : a * e₁ * a⁻¹ = e₁) (ha2 : a * e₂ * a⁻¹ = e₁ * e₂)
    (hb1 : b * e₁ * b⁻¹ = e₁ * e₂) (hb2 : b * e₂ * b⁻¹ = e₂) (v : V) :
    ‖(invSubspace π (Subgroup.closure ({e₁, e₂} : Set Γ)))ᗮ.starProjection v‖ ^ 2 ≤
      6500 * (‖π e₁ v - v‖ ^ 2 + ‖π e₂ v - v‖ ^ 2 + ‖π a v - v‖ ^ 2 + ‖π b v - v‖ ^ 2) := by
  set Z := Subgroup.closure ({e₁, e₂} : Set Γ)
  set w : V := (invSubspace π Z)ᗮ.starProjection v
  have hw_orth : w ∈ (invSubspace π Z)ᗮ := Submodule.coe_mem _
  -- Step 1: Bound `‖w‖^2` in terms of `‖π g w - w‖` via `specL` and ping-pong
  have hmain_w : ‖w‖ ^ 2 ≤
      6500 * (‖π e₁ w - w‖ ^ 2 + ‖π e₂ w - w‖ ^ 2 + ‖π a w - w‖ ^ 2 + ‖π b w - w‖ ^ 2) := by
    set η : ℝ := ‖π e₁ w - w‖ ^ 2 + ‖π e₂ w - w‖ ^ 2
    set δa : ℝ := ‖π a w - w‖
    set δb : ℝ := ‖π b w - w‖
    have hpow4 : ∀ g : Γ, ‖π (g ^ (4 : ℤ)) w - w‖ ≤ 4 * ‖π g w - w‖ ∧
        ‖π (g ^ (-4 : ℤ)) w - w‖ ≤ 4 * ‖π g w - w‖ := fun g => by
      have hpos : ∀ n : ℕ, ‖π (g ^ n) w - w‖ ≤ (n : ℝ) * ‖π g w - w‖ := fun n => by
        induction n with
        | zero => simp
        | succ n ih =>
          have hs : π (g ^ (n + 1)) w - w = π g (π (g ^ n) w - w) + (π g w - w) := by
            rw [pow_succ', rep_mul, map_sub]; abel
          rw [hs]
          calc ‖π g (π (g ^ n) w - w) + (π g w - w)‖
              ≤ ‖π g (π (g ^ n) w - w)‖ + ‖π g w - w‖ := norm_add_le _ _
            _ = ‖π (g ^ n) w - w‖ + ‖π g w - w‖ := by rw [(π g).norm_map]
            _ ≤ (n : ℝ) * ‖π g w - w‖ + ‖π g w - w‖ := add_le_add ih le_rfl
            _ = ((n + 1 : ℕ) : ℝ) * ‖π g w - w‖ := by push_cast; ring
      have h4 : ‖π (g ^ (4 : ℤ)) w - w‖ ≤ 4 * ‖π g w - w‖ := by simpa using hpos 4
      have hm4 : ‖π (g ^ (-4 : ℤ)) w - w‖ ≤ 4 * ‖π g w - w‖ := by
        have heq : ‖π (g ^ (-4 : ℤ)) w - w‖ = ‖π (g ^ (4 : ℤ)) w - w‖ := by
          rw [← (π (g ^ (4 : ℤ))).norm_map (π (g ^ (-4 : ℤ)) w - w), map_sub, ← rep_mul,
            ← _root_.zpow_add, add_neg_cancel, zpow_zero, rep_one, norm_sub_rev]
        rw [heq]; exact h4
      exact ⟨h4, hm4⟩
    have hstep_M : ∀ M : ℕ, 5 ≤ M →
        ‖w‖ ^ 2 ≤ 16 * ‖w‖ * (δa + δb) +
          80 * ‖(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w‖ ^ 2 +
          3250 * η := by
      intro M hM
      set r : ℝ := 1 / (200 * (M : ℝ))
      have hMpos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr (by omega)
      have hr : 0 < r := by positivity
      have hr_hi : r ≤ 1 / 1000 := by
        dsimp only [r]; rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (5 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        linarith
      let fX : C(T2, ℝ) := ⟨psiX r, continuous_psiX hr⟩
      let fY : C(T2, ℝ) := ⟨psiY r, continuous_psiY hr⟩
      let fB : C(T2, ℝ) := ⟨bumpSmall r, continuous_bumpSmall r⟩
      let fE : C(T2, ℝ) := ⟨torusE, continuous_torusE⟩
      let fF : C(T2, ℝ) := ⟨fejer2D M, continuous_fejer2D M⟩
      set α : ℝ := (specL π he₁₂ (ofRealC fX) w).re
      set β : ℝ := (specL π he₁₂ (ofRealC fY) w).re
      set γ : ℝ := (specL π he₁₂ (ofRealC fB) w).re
      have hE_val : (specL π he₁₂ (ofRealC fE) w).re = η := specL_torusE π he₁₂ w
      have h1_val : (specL π he₁₂ (ofRealC (1 : C(T2, ℝ))) w).re = ‖w‖ ^ 2 := by
        have h1eq : ofRealC (1 : C(T2, ℝ)) = UnitAddTorus.mFourier (d := Fin 2) 0 := by
          ext; simp [ofRealC, UnitAddTorus.mFourier_zero]
        rw [h1eq, specL_mFourier]
        simp only [Pi.zero_apply, zpow_zero, mul_one, rep_one, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
        exact Complex.ofReal_re _
      have hfX_norm : ‖ofRealC fX‖ ≤ 1 :=
        (ContinuousMap.norm_le _ zero_le_one).mpr fun θ => by
          change ‖(psiX r θ : ℂ)‖ ≤ 1; rw [Complex.norm_real, Real.norm_of_nonneg (psiX_nonneg r θ)]; exact psiX_le_one r θ
      have hfY_norm : ‖ofRealC fY‖ ≤ 1 :=
        (ContinuousMap.norm_le _ zero_le_one).mpr fun θ => by
          change ‖(psiY r θ : ℂ)‖ ≤ 1; rw [Complex.norm_real, Real.norm_of_nonneg (psiY_nonneg r θ)]; exact psiY_le_one r θ
      have hdiff_A : ∀ k : ℤ, (k = 4 ∨ k = -4) →
          α - 8 * ‖w‖ * δa ≤ (specL π he₁₂ (ofRealC (fX.comp (phiA k))) w).re := by
        intro k hk
        have hcomp : ofRealC (fX.comp (phiA k)) = (ofRealC fX).comp (phiA k) := rfl
        rw [hcomp, specL_comp_phiA π he₁₂ ha1 ha2 k (ofRealC fX) w]
        have hle := specL_sub_w_le π he₁₂ (ofRealC fX) (w₁ := w) (w₂ := π (a ^ k) w) ((π (a ^ k)).norm_map w).symm
        have hre : α - (specL π he₁₂ (ofRealC fX) (π (a ^ k) w)).re ≤ 2 * ‖ofRealC fX‖ * ‖w‖ * ‖w - π (a ^ k) w‖ :=
          (Complex.re_le_norm _).trans hle
        rw [norm_sub_rev] at hre
        have h4k : ‖π (a ^ k) w - w‖ ≤ 4 * δa := by rcases hk with rfl | rfl; exact (hpow4 a).1; exact (hpow4 a).2
        have h8 : 2 * ‖ofRealC fX‖ * ‖w‖ * ‖π (a ^ k) w - w‖ ≤ 8 * ‖w‖ * δa := by
          have := mul_le_mul (mul_le_mul_of_nonneg_left hfX_norm zero_le_two) (mul_le_mul_of_nonneg_left h4k (norm_nonneg w))
            (by positivity) (by norm_num)
          linarith
        linarith
      have hdiff_B : ∀ k : ℤ, (k = 4 ∨ k = -4) →
          β - 8 * ‖w‖ * δb ≤ (specL π he₁₂ (ofRealC (fY.comp (phiB k))) w).re := by
        intro k hk
        have hcomp : ofRealC (fY.comp (phiB k)) = (ofRealC fY).comp (phiB k) := rfl
        rw [hcomp, specL_comp_phiB π he₁₂ hb1 hb2 k (ofRealC fY) w]
        have hle := specL_sub_w_le π he₁₂ (ofRealC fY) (w₁ := w) (w₂ := π (b ^ k) w) ((π (b ^ k)).norm_map w).symm
        have hre : β - (specL π he₁₂ (ofRealC fY) (π (b ^ k) w)).re ≤ 2 * ‖ofRealC fY‖ * ‖w‖ * ‖w - π (b ^ k) w‖ :=
          (Complex.re_le_norm _).trans hle
        rw [norm_sub_rev] at hre
        have h4k : ‖π (b ^ k) w - w‖ ≤ 4 * δb := by rcases hk with rfl | rfl; exact (hpow4 b).1; exact (hpow4 b).2
        have h8 : 2 * ‖ofRealC fY‖ * ‖w‖ * ‖π (b ^ k) w - w‖ ≤ 8 * ‖w‖ * δb := by
          have := mul_le_mul (mul_le_mul_of_nonneg_left hfY_norm zero_le_two) (mul_le_mul_of_nonneg_left h4k (norm_nonneg w))
            (by positivity) (by norm_num)
          linarith
        linarith
      have hlin_add : ∀ g₁ g₂ : C(T2, ℝ),
          (specL π he₁₂ (ofRealC (g₁ + g₂)) w).re = (specL π he₁₂ (ofRealC g₁) w).re + (specL π he₁₂ (ofRealC g₂) w).re := fun g₁ g₂ => by
        rw [show ofRealC (g₁ + g₂) = ofRealC g₁ + ofRealC g₂ by ext; simp [ofRealC], specL_add, Complex.add_re]
      have hlin_smul : ∀ (c : ℝ) (g : C(T2, ℝ)),
          (specL π he₁₂ (ofRealC (c • g)) w).re = c * (specL π he₁₂ (ofRealC g) w).re := fun c g => by
        rw [show ofRealC (c • g) = (c : ℂ) • ofRealC g by ext; simp [ofRealC], specL_smul, Complex.re_ofReal_mul]
      have hppA := specL_ofReal_mono π he₁₂ (f := fX.comp (phiA 4) + fX.comp (phiA (-4)))
        (g := fY + (2 : ℝ) • fB + (1300 : ℝ) • fE) (fun p => pingpong_A hr hr_hi p) w
      rw [hlin_add, hlin_add, hlin_add, hlin_smul, hlin_smul, hE_val] at hppA
      have hppB := specL_ofReal_mono π he₁₂ (f := fY.comp (phiB 4) + fY.comp (phiB (-4)))
        (g := fX + (2 : ℝ) • fB + (1300 : ℝ) • fE) (fun p => pingpong_B hr hr_hi p) w
      rw [hlin_add, hlin_add, hlin_add, hlin_smul, hlin_smul, hE_val] at hppB
      have hcov := specL_ofReal_mono π he₁₂ (f := (1 : C(T2, ℝ)))
        (g := fX + fY + fB + (650 : ℝ) • fE) (fun p => torus_cover hr hr_hi p) w
      rw [h1_val, hlin_add, hlin_add, hlin_add, hlin_smul, hE_val] at hcov
      have hB_le := specL_ofReal_mono π he₁₂ (f := fB) (g := (16 : ℝ) • fF)
        (fun p => bumpSmall_le_fejer2D (by omega : 1 ≤ M) p) w
      rw [hlin_smul, specL_fejer2D π he₁₂ (by omega : 1 ≤ M) w] at hB_le
      have hA4 := hdiff_A 4 (Or.inl rfl)
      have hAm4 := hdiff_A (-4) (Or.inr rfl)
      have hB4 := hdiff_B 4 (Or.inl rfl)
      have hBm4 := hdiff_B (-4) (Or.inr rfl)
      linarith
    have hlim : ‖w‖ ^ 2 ≤ 16 * ‖w‖ * (δa + δb) + 3250 * η := by
      have htend : Tendsto (fun M : ℕ =>
          16 * ‖w‖ * (δa + δb) +
            80 * ‖(((M : ℂ) ^ 2)⁻¹) • ∑ m ∈ Finset.range M, ∑ n ∈ Finset.range M, π (e₁ ^ m * e₂ ^ n) w‖ ^ 2 +
            3250 * η) atTop (𝓝 (16 * ‖w‖ * (δa + δb) + 3250 * η)) := by
        have h0 := (tendsto_double_avg_zero π he₁₂ hw_orth).const_mul 80
        simpa using (tendsto_const_nhds.add h0).add tendsto_const_nhds
      exact ge_of_tendsto htend (Filter.eventually_atTop.mpr ⟨5, hstep_M⟩)
    have hamgm : 16 * ‖w‖ * (δa + δb) ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 + 256 * (δa ^ 2 + δb ^ 2) := by
      nlinarith [sq_nonneg (‖w‖ - 16 * (δa + δb)), sq_nonneg (δa - δb)]
    dsimp only [η, δa, δb] at hlim hamgm
    linarith [sq_nonneg ‖π a w - w‖, sq_nonneg ‖π b w - w‖]
  -- Step 2: `Z` is normalized by `e₁, e₂, a, b`, so `‖π g w - w‖ ≤ ‖π g v - v‖` for `g ∈ {e₁, e₂, a, b}`
  have hnorm_Z : ∀ g : Γ, g = e₁ ∨ g = e₂ ∨ g = a ∨ g = b →
      (∀ h ∈ Z, g⁻¹ * h * g ∈ Z) ∧ (∀ h ∈ Z, g * h * g⁻¹ ∈ Z) := by
    have hZ_conj : ∀ g : Γ, (g * e₁ * g⁻¹ ∈ Z ∧ g * e₂ * g⁻¹ ∈ Z) → ∀ h ∈ Z, g * h * g⁻¹ ∈ Z := by
      intro g ⟨h1, h2⟩ h hh
      induction hh using Subgroup.closure_induction with
      | mem u hu => rcases hu with rfl | rfl; exact h1; exact h2
      | one => simp
      | mul x y _ _ hx hy =>
        rw [show g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) by group]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        rw [show g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ by group]
        exact Subgroup.inv_mem _ hx
    have he1Z : e₁ ∈ Z := Subgroup.subset_closure (by simp)
    have he2Z : e₂ ∈ Z := Subgroup.subset_closure (by simp)
    have ha1_inv : a⁻¹ * e₁ * a = e₁ := by
      have := congrArg (fun z => a⁻¹ * z * a) ha1; simpa [mul_assoc] using this.symm
    have ha2_inv : a⁻¹ * e₂ * a = e₁⁻¹ * e₂ := by
      have := congrArg (fun z => a⁻¹ * z * a) ha2
      have hsplit : a⁻¹ * (e₁ * e₂) * a = (a⁻¹ * e₁ * a) * (a⁻¹ * e₂ * a) := by group
      rw [hsplit, ha1_inv] at this
      have h2 := congrArg (e₁⁻¹ * ·) this.symm; simpa [mul_assoc] using h2
    have hb2_inv : b⁻¹ * e₂ * b = e₂ := by
      have := congrArg (fun z => b⁻¹ * z * b) hb2; simpa [mul_assoc] using this.symm
    have hb1_inv : b⁻¹ * e₁ * b = e₁ * e₂⁻¹ := by
      have := congrArg (fun z => b⁻¹ * z * b) hb1
      have hsplit : b⁻¹ * (e₁ * e₂) * b = (b⁻¹ * e₁ * b) * (b⁻¹ * e₂ * b) := by group
      rw [hsplit, hb2_inv] at this
      have h2 := congrArg (· * e₂⁻¹) this.symm; simpa [mul_assoc] using h2
    intro g hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      exact ⟨fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ he1Z) hh) he1Z,
        fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ he1Z hh) (Subgroup.inv_mem _ he1Z)⟩
    · rw [hg]
      exact ⟨fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ he2Z) hh) he2Z,
        fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ he2Z hh) (Subgroup.inv_mem _ he2Z)⟩
    · rw [hg]
      refine ⟨fun h hh => by simpa [inv_inv] using hZ_conj a⁻¹ ⟨by simpa [inv_inv] using ha1_inv.symm ▸ he1Z,
          by simpa [inv_inv] using ha2_inv.symm ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ he1Z) he2Z⟩ h hh,
        hZ_conj a ⟨ha1.symm ▸ he1Z, ha2.symm ▸ Subgroup.mul_mem _ he1Z he2Z⟩⟩
    · rw [hg]
      refine ⟨fun h hh => by simpa [inv_inv] using hZ_conj b⁻¹ ⟨by simpa [inv_inv] using hb1_inv.symm ▸ Subgroup.mul_mem _ he1Z (Subgroup.inv_mem _ he2Z),
          by simpa [inv_inv] using hb2_inv.symm ▸ he2Z⟩ h hh,
        hZ_conj b ⟨hb1.symm ▸ Subgroup.mul_mem _ he1Z he2Z, hb2.symm ▸ he2Z⟩⟩
  have hdisp : ∀ g : Γ, g = e₁ ∨ g = e₂ ∨ g = a ∨ g = b → ‖π g w - w‖ ^ 2 ≤ ‖π g v - v‖ ^ 2 := by
    intro g hg
    have hn := hnorm_Z g hg
    have hcomm : (invSubspace π Z)ᗮ.starProjection (π g v) = π g ((invSubspace π Z)ᗮ.starProjection v) := by
      rw [(invSubspace π Z).starProjection_orthogonal_val, (invSubspace π Z).starProjection_orthogonal_val,
        map_sub, starProjection_invSubspace_comm π hn.1 hn.2 v]
    have hsub : π g w - w = (invSubspace π Z)ᗮ.starProjection (π g v - v) := by
      dsimp only [w]; rw [map_sub, hcomm]
    rw [hsub]
    have hpyth := (invSubspace π Z)ᗮ.norm_sq_eq_add_norm_sq_projection (π g v - v)
    have h1 : ‖(invSubspace π Z)ᗮ.orthogonalProjectionOnto (π g v - v)‖ =
        ‖(invSubspace π Z)ᗮ.starProjection (π g v - v)‖ := rfl
    rw [h1] at hpyth; linarith [sq_nonneg ‖(invSubspace π Z)ᗮᗮ.orthogonalProjectionOnto (π g v - v)‖]
  have hd1 := hdisp e₁ (Or.inl rfl)
  have hd2 := hdisp e₂ (Or.inr (Or.inl rfl))
  have hd3 := hdisp a (Or.inr (Or.inr (Or.inl rfl)))
  have hd4 := hdisp b (Or.inr (Or.inr (Or.inr rfl)))
  linarith

end RelPropTF2Z2

end
end OMA.Green100H2

/- Applying @zzzfu411's quantitative shear bound (Green100, part ii) to the
standard integral two-dimensional affine group. -/

open OMA.Green100H2

theorem green100_shear_gap
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ →* MulAut (Multiplicative (Fin 2 → ℤ)))
    (hα : ∀ g x, Multiplicative.toAdd (α g x) =
      (g : Matrix (Fin 2) (Fin 2) ℤ).mulVec (Multiplicative.toAdd x)) :
    ∃ e₁ e₂ a b : Multiplicative (Fin 2 → ℤ) ⋊[α] Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
        (π : (Multiplicative (Fin 2 → ℤ) ⋊[α] Matrix.SpecialLinearGroup (Fin 2) ℤ) →* V ≃ₗᵢ[ℂ] V)
        (v : V) (x : Multiplicative (Fin 2 → ℤ)),
        ‖π (SemidirectProduct.inl x) v - v‖ ^ 2 ≤ 26000 *
          (‖π e₁ v-v‖^2 + ‖π e₂ v-v‖^2 + ‖π a v-v‖^2 + ‖π b v-v‖^2) := by
  classical
  let G := Multiplicative (Fin 2 → ℤ) ⋊[α] Matrix.SpecialLinearGroup (Fin 2) ℤ
  let U (i : Fin 2) := Multiplicative.ofAdd (Pi.single i (1 : ℤ) : Fin 2 → ℤ)
  let e (i : Fin 2) : G := SemidirectProduct.inl (U i)
  let t (i j : Fin 2) (h : i ≠ j) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    Matrix.SpecialLinearGroup.transvection h (1 : ℤ)
  let s (i j : Fin 2) (h : i ≠ j) : G := SemidirectProduct.inr (t i j h)
  have conj (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (y : Multiplicative (Fin 2 → ℤ)) :
      (SemidirectProduct.inr g * SemidirectProduct.inl y * (SemidirectProduct.inr g)⁻¹ : G)
        = SemidirectProduct.inl (α g y) := by
    rw [← map_inv, ← SemidirectProduct.inl_aut]
  have fst (i j : Fin 2) (h : i ≠ j) : s i j h * e i * (s i j h)⁻¹ = e i := by
    dsimp only [s, e]
    rw [conj]
    apply congrArg SemidirectProduct.inl
    apply Multiplicative.toAdd.injective
    rw [hα]
    exact Matrix.SpecialLinearGroup.transvection_smul_single_fst h (1 : ℤ)
  have snd (i j : Fin 2) (h : i ≠ j) : s i j h * e j * (s i j h)⁻¹ = e j * e i := by
    dsimp only [s, e]
    rw [conj, ← map_mul]
    apply congrArg SemidirectProduct.inl
    apply Multiplicative.toAdd.injective
    rw [hα]
    change (Matrix.SpecialLinearGroup.transvection h (1 : ℤ)) • (Pi.single j 1 : Fin 2 → ℤ) =
      (Pi.single j (1 : ℤ) : Fin 2 → ℤ) + Pi.single i 1
    simpa only [one_smul] using Matrix.SpecialLinearGroup.transvection_smul_single_snd h (1 : ℤ)
  have he : Commute (e 0) (e 1) := (Commute.all (U 0) (U 1)).map SemidirectProduct.inl
  let Z := Subgroup.closure ({e 0, e 1} : Set G)
  have hmem (x : Multiplicative (Fin 2 → ℤ)) : (SemidirectProduct.inl x : G) ∈ Z := by
    have hi (i : Fin 2) : e i ∈ Z := by
      apply Subgroup.subset_closure
      fin_cases i <;> simp
    have hx : x = U 0 ^ x.toAdd 0 * U 1 ^ x.toAdd 1 := by
      apply Multiplicative.toAdd.injective
      change x.toAdd = x.toAdd 0 • Pi.single 0 (1 : ℤ) + x.toAdd 1 • Pi.single 1 (1 : ℤ)
      ext i
      fin_cases i <;> simp
    rw [hx, map_mul, map_zpow, map_zpow]
    exact Z.mul_mem (Z.zpow_mem (hi 0) _) (Z.zpow_mem (hi 1) _)
  refine ⟨e 0, e 1, s 0 1 (by decide), s 1 0 (by decide), ?_⟩
  intro V _ _ _ π v x
  have h := rel_propT_F2_Z2 π (e 0) (e 1) (s 0 1 (by decide)) (s 1 0 (by decide)) he
    (fst 0 1 (by decide)) ((snd 0 1 (by decide)).trans he.eq.symm) (snd 1 0 (by decide))
    (fst 1 0 (by decide)) v
  let K := invSubspace π Z
  let w := K.starProjection v
  have hw : π (SemidirectProduct.inl x) w = w :=
    (show w ∈ K from Submodule.coe_mem _) _ (hmem x)
  have hdisp : ‖π (SemidirectProduct.inl x) v - v‖ ≤ 2 * ‖Kᗮ.starProjection v‖ := by
    rw [K.starProjection_orthogonal_val]
    change _ ≤ 2 * ‖v-w‖
    have heq : π (SemidirectProduct.inl x) v - v = π (SemidirectProduct.inl x) (v-w) - (v-w) := by
      rw [map_sub, hw]
      abel
    rw [heq]
    simpa only [LinearIsometryEquiv.norm_map, two_mul] using
      norm_sub_le (π (SemidirectProduct.inl x) (v-w)) (v-w)
  change ‖Kᗮ.starProjection v‖ ^ 2 ≤ _ at h
  nlinarith [sq_le_sq' (show -(2*‖Kᗮ.starProjection v‖) ≤ ‖π (SemidirectProduct.inl x) v - v‖ by linarith [norm_nonneg (Kᗮ.starProjection v), norm_nonneg (π (SemidirectProduct.inl x) v-v)]) hdisp]

/- Positive semidefiniteness of the Gaussian distance kernel on a complex Hilbert space. -/
open Filter Matrix
open scoped Matrix InnerProductSpace ComplexOrder Topology BigOperators

namespace Green100Gaussian

private theorem finite_kernel {I E : Type} [Fintype I] [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : I → E) (t : ℝ) (ht : 0 ≤ t) :
    (Matrix.of fun i j => (Real.exp (-t * ‖v i - v j‖^2) : ℂ)).PosSemidef := by
  classical
  let G := Matrix.gram ℂ v
  let A := t • (G + G.transpose)
  have hG := Matrix.posSemidef_gram ℂ v
  have hA : A.PosSemidef := (hG.add hG.transpose).smul ht
  let P (n : ℕ) : Matrix I I ℂ := Matrix.of fun i j => (A i j)^n
  have hP (n : ℕ) : (P n).PosSemidef := by
    induction n with
    | zero =>
      have hp := Matrix.posSemidef_vecMulVec_self_star (fun _ : I => (1 : ℂ))
      simpa [P, Matrix.vecMulVec, Pi.star_def] using hp
    | succ n ih =>
      simpa only [P, pow_succ, Matrix.hadamard, Matrix.of_apply] using ih.hadamard hA
  let T (n : ℕ) : Matrix I I ℂ := ∑ m ∈ Finset.range n, (m.factorial : ℝ)⁻¹ • P m
  have hT (n : ℕ) : (T n).PosSemidef :=
    Matrix.posSemidef_sum _ fun m _ => (hP m).smul (by positivity : 0 ≤ (m.factorial : ℝ)⁻¹)
  have hlim (i j : I) : Tendsto (fun n => T n i j) atTop (𝓝 (Complex.exp (A i j))) := by
    simpa [T, Matrix.sum_apply, P, Matrix.smul_apply, Complex.real_smul,
      div_eq_inv_mul, Complex.ofReal_inv, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (A i j)).tendsto_sum_nat
  let X : Matrix I I ℂ := Matrix.of fun i j => Complex.exp (A i j)
  have hX : X.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · ext i j
      change star (Complex.exp (A j i)) = Complex.exp (A i j)
      change (starRingEnd ℂ) (Complex.exp (A j i)) = _
      rw [← Complex.exp_conj]
      exact congrArg Complex.exp (hA.isHermitian.apply i j)
    · intro w
      suffices H : Tendsto (fun n : ℕ => star w ⬝ᵥ (T n *ᵥ w)) atTop (𝓝 (star w ⬝ᵥ (X *ᵥ w))) from
        ge_of_tendsto' H (fun n => (hT n).dotProduct_mulVec_nonneg w)
      unfold dotProduct Matrix.mulVec
      exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul_const _)
  let d : I → ℂ := fun i => Real.exp (-t * ‖v i‖^2)
  have hDX := (Matrix.posSemidef_vecMulVec_self_star d).hadamard hX
  suffices eqn : (Matrix.of fun i j => (Real.exp (-t * ‖v i - v j‖^2) : ℂ)) =
      (Matrix.vecMulVec d (star d)).hadamard X by rwa [eqn]
  apply Matrix.ext
  intro i j
  change (Real.exp (-t * ‖v i-v j‖^2) : ℂ) =
    (d i * star (d j)) * Complex.exp (A i j)
  have entry : A i j = (t * (2 * (inner ℂ (v i) (v j)).re) : ℝ) := by
    simp only [A,G,Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,Matrix.gram_apply,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    rw [← inner_conj_symm (v j) (v i)]
    rw [Complex.add_conj]
    push_cast
    ring
  rw [entry, ← Complex.ofReal_exp]
  simp only [d, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2
  rw [@norm_sub_sq ℂ _ _ _ _ (v i) (v j)]
  change -t * (‖v i‖ ^ 2 - 2 * (inner ℂ (v i) (v j)).re + ‖v j‖ ^ 2) = _
  ring

/-- Every finite quadratic form associated to this kernel is nonnegative. -/
theorem gaussian_posSemidef {I E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (v : I → E) (t : ℝ) (ht : 0 ≤ t) :
    (Matrix.of fun i j => (Real.exp (-t * ‖v i - v j‖^2) : ℂ)).PosSemidef := by
  classical
  refine ⟨?_, fun x => ?_⟩
  · ext i j
    change (starRingEnd ℂ) (↑(Real.exp (-t * ‖v j - v i‖^2)) : ℂ) = ↑(Real.exp (-t * ‖v i - v j‖^2))
    rw [Complex.conj_ofReal, norm_sub_rev (v j) (v i)]
  have hh := finite_kernel (I := x.support) (fun i => v i.val) t ht
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using hh.2 (x.subtypeDomain (· ∈ x.support))

end Green100Gaussian

/- The cyclic representation associated to a translation-invariant positive kernel. -/

open scoped ComplexOrder InnerProductSpace
open UniformSpace

private theorem green100_preinner {G : Type} (K : Matrix G G ℂ) (hp : K.PosSemidef) :
    ∃ cd : PreInnerProductSpace.Core ℂ (G →₀ ℂ), ∀ x y,
      cd.inner x y = x.sum fun i a => y.sum fun j b => star a * K i j * b := by
  classical
  refine ⟨{
    inner := fun x y => x.sum fun i a => y.sum fun j b => star a * K i j * b
    conj_inner_symm := ?_
    re_inner_nonneg := fun x => (hp.2 x).1
    add_left := ?_
    smul_left := ?_ }, fun _ _ => rfl⟩
  · intro x y
    rw [Finsupp.sum_comm]
    simp only [map_finsuppSum, map_mul, ← Complex.star_def, star_star]
    congr! 6
    rw [hp.isHermitian.apply]
    ring
  · intro x y z
    rw [Finsupp.sum_add_index'] <;> simp [← Finsupp.sum_add, add_mul]
  · intro x y r
    rw [Finsupp.sum_smul_index] <;> simp [Finsupp.mul_sum, ← mul_assoc]

private theorem green100_kernel_representation {G : Type} [Group G]
    (K : Matrix G G ℂ) (hp : K.PosSemidef) (hd : ∀ g, K g g = 1)
    (hinv : ∀ t g h, K (t*g) (t*h) = K g h) :
    ∃ (F : Type) (_ : NormedAddCommGroup F) (_ : InnerProductSpace ℂ F) (_ : CompleteSpace F)
      (π : G →* F ≃ₗᵢ[ℂ] F) (ξ : F),
      ‖ξ‖ = 1 ∧ ∀ g, ‖π g ξ - ξ‖^2 = 2 - 2*(K 1 g).re := by
  classical
  obtain ⟨cd, hcd⟩ := green100_preinner K hp
  let : SeminormedAddCommGroup (G →₀ ℂ) :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (c := cd)
  let : InnerProductSpace ℂ (G →₀ ℂ) := .ofCore cd
  let T (g : G) : (G →₀ ℂ) ≃ₗ[ℂ] (G →₀ ℂ) := Finsupp.domLCongr (Equiv.mulLeft g)
  have hT (g : G) (x : G →₀ ℂ) : ‖T g x‖ = ‖x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]
    change (cd.inner (T g x) (T g x)).re = (cd.inner x x).re
    simp only [hcd, T, Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.sum_equivMapDomain,
      show ∀ a, Equiv.mulLeft g a = g*a from fun _ => rfl, hinv]
  have hOne (x : G →₀ ℂ) : T 1 x = x := by
    ext i
    change x (1⁻¹ * i) = x i
    simp
  have hMul (g h : G) (x : G →₀ ℂ) : T (g*h) x = T g (T h x) := by
    ext i
    change x ((g*h)⁻¹*i) = x (h⁻¹*(g⁻¹*i))
    simp [mul_assoc]
  let S (g : G) : (G →₀ ℂ) →L[ℂ] (G →₀ ℂ) :=
    (T g).toLinearMap.mkContinuous 1 fun x => by simp [hT]
  let C := Completion (G →₀ ℂ)
  let U (g : G) : C →L[ℂ] C := (S g).completion
  have hU (g : G) (x : G →₀ ℂ) : U g (x : C) = (T g x : C) :=
    ContinuousLinearMap.completion_apply_coe _ _
  have hUid (x : C) : U 1 x = x := by
    refine Completion.induction_on x (isClosed_eq (U 1).continuous continuous_id) ?_
    intro y
    simp only [hU, hOne]
  have hUprod (g h : G) (x : C) : U (g*h) x = U g (U h x) := by
    refine Completion.induction_on x (isClosed_eq (U _).continuous ((U g).continuous.comp (U h).continuous)) ?_
    intro y
    simp only [hU, hMul]
  have hUnorm (g : G) (x : C) : ‖U g x‖ = ‖x‖ := by
    refine Completion.induction_on x (isClosed_eq (U g).continuous.norm continuous_norm) ?_
    intro y
    rw [hU, Completion.norm_coe, Completion.norm_coe, hT]
  let L (g : G) : C ≃ₗᵢ[ℂ] C := {
    toFun := U g
    invFun := U g⁻¹
    left_inv := fun x => by rw [← hUprod, inv_mul_cancel, hUid]
    right_inv := fun x => by rw [← hUprod, mul_inv_cancel, hUid]
    map_add' := (U g).map_add
    map_smul' := (U g).map_smul
    norm_map' := hUnorm g }
  let π : G →* C ≃ₗᵢ[ℂ] C := {
    toFun := L
    map_one' := LinearIsometryEquiv.ext hUid
    map_mul' := fun g h => LinearIsometryEquiv.ext (hUprod g h) }
  let e (i : G) : G →₀ ℂ := Finsupp.single i 1
  have he (i j : G) : inner ℂ (e i : C) (e j : C) = K i j := by
    rw [Completion.inner_coe]
    change cd.inner _ _ = _
    simp [hcd, e]
  have hn (i : G) : ‖(e i : C)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), he, hd]
    norm_num
  refine ⟨C, inferInstance, inferInstance, inferInstance, π, (e 1 : C), hn _, ?_⟩
  intro g
  change ‖U g (e 1 : C) - (e 1 : C)‖^2 = _
  have hact : T g (e 1) = e g := by simp [T, e]
  rw [hU, hact, norm_sub_rev, norm_sub_sq (𝕜 := ℂ), hn, hn, he]
  change 1^2 - 2*(K 1 g).re + 1^2 = _
  ring

open Filter Topology

/-- Compare the right derivatives at zero of the two sides of the Gaussian displacement bound. -/
private lemma green100_gaussian_bound (x a b c d K : ℝ)
    (h : ∀ t : ℝ, 0 < t →
      2 - 2 * Real.exp (-t * x) ≤ K *
        ((2 - 2 * Real.exp (-t * a)) + (2 - 2 * Real.exp (-t * b)) +
         (2 - 2 * Real.exp (-t * c)) + (2 - 2 * Real.exp (-t * d)))) :
    x ≤ K * (a + b + c + d) := by
  let F (u t : ℝ) := 2 - 2 * Real.exp (-t * u)
  have hF (u : ℝ) : Tendsto (fun t : ℝ => t⁻¹ * F u t) (𝓝[>] 0) (𝓝 (2 * u)) := by
    have hd : HasDerivAt (F u) (2 * u) 0 := by
      simpa [F, Pi.sub_def, id_def] using (hasDerivAt_const (0 : ℝ) (2 : ℝ)).sub
        ((((hasDerivAt_id (0 : ℝ)).neg.mul_const u).exp).const_mul (2 : ℝ))
    simpa [F, smul_eq_mul] using hd.tendsto_slope_zero_right
  have hright := tendsto_const_nhds (x := K) |>.mul
    ((((hF a).add (hF b)).add (hF c)).add (hF d))
  have hderiv := le_of_tendsto_of_tendsto (hF x) hright (by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h₀ : 0 < t := ht
    have h₁ := mul_le_mul_of_nonneg_left (h t h₀) (inv_nonneg.mpr h₀.le)
    dsimp [F]
    linarith only [h₁])
  linarith only [hderiv]

/-- A single bound for all displacements when the four generator norms are fixed. -/
private lemma green100_gaussian_uniform {α E : Type*} [NormedAddCommGroup E]
    (f : α → E) (a b c d K : ℝ)
    (h : ∀ t : ℝ, 0 < t → ∀ z : α,
      2 - 2 * Real.exp (-t * ‖f z‖ ^ 2) ≤ K *
        ((2 - 2 * Real.exp (-t * a)) + (2 - 2 * Real.exp (-t * b)) +
         (2 - 2 * Real.exp (-t * c)) + (2 - 2 * Real.exp (-t * d)))) :
    ∃ M : ℝ, ∀ z, ‖f z‖ ≤ M := by
  refine ⟨Real.sqrt (K * (a + b + c + d)), fun z => ?_⟩
  exact Real.le_sqrt_of_sq_le (green100_gaussian_bound _ _ _ _ _ _ (fun t ht => h t ht z))

/-- Relative boundedness for the translation subgroup, via Gaussian unitary representations. -/
theorem OMA.solution : OMA.R_Green100_green_100_variants_operator_norm_R1_H1_R1_H1_R1.H2 := by
  intro α hα E _ _ _ ρ c hc
  let G := Multiplicative (Fin 2 → ℤ) ⋊[α] Matrix.SpecialLinearGroup (Fin 2) ℤ
  obtain ⟨e₁, e₂, a, b, hgap⟩ := green100_shear_gap α hα
  have hc1 : c 1 = 0 := by
    have h := hc 1 1
    rw [mul_one, map_one] at h
    change c 1 = c 1 + c 1 at h
    simpa using sub_eq_zero.mpr h.symm
  apply green100_gaussian_uniform (fun x => c (SemidirectProduct.inl x))
    (‖c e₁‖ ^ 2) (‖c e₂‖ ^ 2) (‖c a‖ ^ 2) (‖c b‖ ^ 2) 26000
  intro t ht
  let K : Matrix G G ℂ := Matrix.of (fun i j => (Real.exp (-t * ‖c i - c j‖^2) : ℂ))
  have hdiag (g : G) : K g g = 1 := by simp [K]
  have hinv (w g h : G) : K (w * g) (w * h) = K g h := by
    simp only [K, Matrix.of_apply, hc, add_sub_add_left_eq_sub, ← map_sub,
      LinearIsometryEquiv.norm_map]
  obtain ⟨V, hV, hI, hC, π, ξ, _, hdist⟩ := green100_kernel_representation K
    (Green100Gaussian.gaussian_posSemidef c t ht.le) hdiag hinv
  have hdist' (g : G) : ‖π g ξ - ξ‖ ^ 2 = 2 - 2 * Real.exp (-t * ‖c g‖ ^ 2) := by
    simpa only [K, Matrix.of_apply, hc1, zero_sub, norm_neg, Complex.ofReal_re] using hdist g
  intro x
  simpa only [hdist'] using hgap V π ξ x
