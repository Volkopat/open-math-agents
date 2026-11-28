import OMAReductions.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1
import Mathlib

/-!
# Proof of Green100.green_100.parts.ii.R1.H2.R1.H2.R1.H2.R1.H2

Property (T) input (Ershov–Jaikin-Zapirain for the finite-field relations (3.1)–(3.5),
Steinberg/A₂ + Burger–Shalom relative property (T) for the shears, and extension),
transferred to every tracial matrix ultraproduct.

Credit: @zzzfu411
-/

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

/-- Restrict a unitary representation `π` to a `π`-invariant closed subspace `W`. -/
def restrictRep {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (W : Submodule ℂ V) (hW : ∀ g v, v ∈ W → π g v ∈ W) :
    Γ →* W ≃ₗᵢ[ℂ] W where
  toFun g :=
    { toLinearEquiv :=
        { toFun := fun v => ⟨π g v.1, hW g v.1 v.2⟩
          invFun := fun v => ⟨π g⁻¹ v.1, hW g⁻¹ v.1 v.2⟩
          map_add' := fun u v => Subtype.ext (map_add (π g) u.1 v.1)
          map_smul' := fun c v => Subtype.ext (map_smul (π g) c v.1)
          left_inv := fun v => Subtype.ext (by
            change (π g⁻¹ * π g) v.1 = v.1
            rw [← map_mul, inv_mul_cancel, map_one]; rfl)
          right_inv := fun v => Subtype.ext (by
            change (π g * π g⁻¹) v.1 = v.1
            rw [← map_mul, mul_inv_cancel, map_one]; rfl) }
      norm_map' := fun v => (π g).norm_map v.1 }
  map_one' := by ext ⟨v, _⟩; simp
  map_mul' g₁ g₂ := by ext ⟨v, _⟩; simp

/-- L² spectral gap for a unitary representation of `Γ` relative to a finite subset `S`. -/
def HasSpectralGap {Γ : Type} [Group Γ] (S : Finset Γ) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (v : V), v ∈ (invSubspace π ⊤)ᗮ →
    κ * ‖v‖ ^ 2 ≤ ∑ g ∈ S, ‖π g v - v‖ ^ 2

lemma hasSpectralGap_of_max_bound {Γ : Type} [Group Γ] (S : Finset Γ) {c : ℝ} (hc : 0 < c)
    (h : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : Γ →* V ≃ₗᵢ[ℂ] V) (v : V), v ∈ (invSubspace π ⊤)ᗮ →
      ∃ g ∈ S, c * ‖v‖ ≤ ‖π g v - v‖) :
    HasSpectralGap S (c ^ 2) := by
  refine ⟨sq_pos_of_pos hc, fun V _ _ _ π v hv => ?_⟩
  obtain ⟨g, hg, hle⟩ := h V π v hv
  calc c ^ 2 * ‖v‖ ^ 2 = (c * ‖v‖) ^ 2 := by ring
    _ ≤ ‖π g v - v‖ ^ 2 := pow_le_pow_left₀ (by positivity) hle 2
    _ ≤ ∑ s ∈ S, ‖π s v - v‖ ^ 2 :=
      Finset.single_le_sum (f := fun s => ‖π s v - v‖ ^ 2) (fun _ _ => sq_nonneg _) hg

lemma hasSpectralGap_mono {Γ : Type} [Group Γ] {S₁ S₂ : Finset Γ} {κ₁ κ₂ : ℝ}
    (hS : S₁ ⊆ S₂) (hκ : κ₂ ≤ κ₁) (hκ₂ : 0 < κ₂) (h : HasSpectralGap S₁ κ₁) :
    HasSpectralGap S₂ κ₂ := by
  refine ⟨hκ₂, fun V _ _ _ π v hv => ?_⟩
  calc κ₂ * ‖v‖ ^ 2 ≤ κ₁ * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hκ (sq_nonneg _)
    _ ≤ ∑ g ∈ S₁, ‖π g v - v‖ ^ 2 := h.2 V π v hv
    _ ≤ ∑ g ∈ S₂, ‖π g v - v‖ ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)

/-- Quotient permanence of spectral gap along a surjective homomorphism. -/
lemma hasSpectralGap_of_surjective {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] [DecidableEq Γ₂]
    (f : Γ₁ →* Γ₂) (hf : Function.Surjective f) {S : Finset Γ₁} {κ : ℝ}
    (h : HasSpectralGap S κ) :
    HasSpectralGap (S.image f) (κ / (S.card.max 1 : ℝ)) := by
  have hpos : (0 : ℝ) < (S.card.max 1 : ℝ) := by positivity
  refine ⟨div_pos h.1 hpos, fun V _ _ _ π v hv => ?_⟩
  let π₁ : Γ₁ →* V ≃ₗᵢ[ℂ] V := π.comp f
  have hv₁ : v ∈ (invSubspace π₁ ⊤)ᗮ := by
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    apply hv u
    intro g₂ _
    obtain ⟨g₁, rfl⟩ := hf g₂
    exact hu g₁ trivial
  have hgap := h.2 V π₁ v hv₁
  have hsum : ∑ g ∈ S, ‖π (f g) v - v‖ ^ 2 ≤ (S.card.max 1 : ℝ) * ∑ y ∈ S.image f, ‖π y v - v‖ ^ 2 := by
    calc ∑ g ∈ S, ‖π (f g) v - v‖ ^ 2
        ≤ ∑ _g ∈ S, ∑ y ∈ S.image f, ‖π y v - v‖ ^ 2 :=
          Finset.sum_le_sum fun g hg =>
            Finset.single_le_sum (f := fun y => ‖π y v - v‖ ^ 2) (fun _ _ => sq_nonneg _)
              (Finset.mem_image_of_mem f hg)
      _ = (S.card : ℝ) * ∑ y ∈ S.image f, ‖π y v - v‖ ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (S.card.max 1 : ℝ) * ∑ y ∈ S.image f, ‖π y v - v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left S.card 1)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hgap' : κ * ‖v‖ ^ 2 ≤ ∑ g ∈ S, ‖π (f g) v - v‖ ^ 2 := hgap
  rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
  linarith

/-- Triangle inequality for unitary action along a word in generators and their inverses. -/
lemma norm_rep_word_sub_le {Γ V : Type*} [Group Γ] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) (S : Set Γ) (v : V) (M : ℝ) (hM : ∀ s ∈ S, ‖π s v - v‖ ≤ M) :
    ∀ g ∈ Subgroup.closure S, ∃ L : ℕ, ‖π g v - v‖ ≤ (L : ℝ) * M := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨1, by simpa using hM x hx⟩
  | one => exact ⟨0, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L₁, hL₁⟩ := hx
    obtain ⟨L₂, hL₂⟩ := hy
    refine ⟨L₁ + L₂, ?_⟩
    have hsplit : π (x * y) v - v = π x (π y v - v) + (π x v - v) := by
      rw [rep_mul, map_sub]; abel
    rw [hsplit, Nat.cast_add, add_mul]
    calc ‖π x (π y v - v) + (π x v - v)‖
        ≤ ‖π x (π y v - v)‖ + ‖π x v - v‖ := norm_add_le _ _
      _ = ‖π y v - v‖ + ‖π x v - v‖ := by rw [(π x).norm_map]
      _ ≤ (L₂ : ℝ) * M + (L₁ : ℝ) * M := add_le_add hL₂ hL₁
      _ = (L₁ : ℝ) * M + (L₂ : ℝ) * M := add_comm _ _
  | inv x _ hx =>
    obtain ⟨L, hL⟩ := hx
    refine ⟨L, ?_⟩
    have heq : ‖π x⁻¹ v - v‖ = ‖π x v - v‖ := by
      have h1 : π x (π x⁻¹ v - v) = -(π x v - v) := by
        rw [map_sub, rep_mul_inv]; abel
      rw [← (π x).norm_map, h1, norm_neg]
    rwa [heq]

/-- Word-length bound independent of the representation `π`: every `g ∈ Subgroup.closure S`
is a product of `L` elements of `S ∪ S⁻¹`. -/
lemma exists_word_bound {Γ : Type*} [Group Γ] (S : Finset Γ) {g : Γ}
    (hg : g ∈ Subgroup.closure (S : Set Γ)) :
    ∃ L : ℕ, ∀ (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (π : Γ →* V ≃ₗᵢ[ℂ] V) (v : V),
      ‖π g v - v‖ ^ 2 ≤ (L : ℝ) ^ 2 * ∑ s ∈ S, ‖π s v - v‖ ^ 2 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    refine ⟨1, fun V _ _ π v => ?_⟩
    rw [Nat.cast_one, one_pow, one_mul]
    exact Finset.single_le_sum (f := fun s => ‖π s v - v‖ ^ 2) (fun _ _ => sq_nonneg _) hx
  | one =>
    exact ⟨0, fun V _ _ π v => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨L₁, hL₁⟩ := hx
    obtain ⟨L₂, hL₂⟩ := hy
    refine ⟨L₁ + L₂, fun V _ _ π v => ?_⟩
    set B := ∑ s ∈ S, ‖π s v - v‖ ^ 2
    have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h1 : ‖π x v - v‖ ≤ (L₁ : ℝ) * Real.sqrt B := by
      have hsq := Real.sqrt_le_sqrt (hL₁ V π v)
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (Nat.cast_nonneg _)] at hsq
    have h2 : ‖π y v - v‖ ≤ (L₂ : ℝ) * Real.sqrt B := by
      have hsq := Real.sqrt_le_sqrt (hL₂ V π v)
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq (Nat.cast_nonneg _)] at hsq
    have htri : ‖π (x * y) v - v‖ ≤ ((L₁ + L₂ : ℕ) : ℝ) * Real.sqrt B := by
      have hsplit : π (x * y) v - v = π x (π y v - v) + (π x v - v) := by
        rw [rep_mul, map_sub]; abel
      rw [hsplit]
      calc ‖π x (π y v - v) + (π x v - v)‖
          ≤ ‖π x (π y v - v)‖ + ‖π x v - v‖ := norm_add_le _ _
        _ = ‖π y v - v‖ + ‖π x v - v‖ := by rw [(π x).norm_map]
        _ ≤ (L₂ : ℝ) * Real.sqrt B + (L₁ : ℝ) * Real.sqrt B := add_le_add h2 h1
        _ = ((L₁ + L₂ : ℕ) : ℝ) * Real.sqrt B := by push_cast; ring
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    rwa [mul_pow, Real.sq_sqrt hB] at hsq
  | inv x _ hx =>
    obtain ⟨L, hL⟩ := hx
    refine ⟨L, fun V _ _ π v => ?_⟩
    have heq : ‖π x⁻¹ v - v‖ = ‖π x v - v‖ := by
      have h1 : π x (π x⁻¹ v - v) = -(π x v - v) := by
        rw [map_sub, rep_mul_inv]; abel
      rw [← (π x).norm_map, h1, norm_neg]
    rw [heq]; exact hL V π v

/-- Changing generating set preserves spectral gap (with an explicit positive constant). -/
lemma hasSpectralGap_change_gen {Γ : Type} [Group Γ] {S₁ S₂ : Finset Γ} {κ : ℝ}
    (h : HasSpectralGap S₁ κ) (hsub : ∀ g ∈ S₁, g ∈ Subgroup.closure (S₂ : Set Γ)) :
    ∃ κ' : ℝ, HasSpectralGap S₂ κ' := by
  classical
  have hL : ∀ g : S₁, ∃ L : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (π : Γ →* V ≃ₗᵢ[ℂ] V) (v : V),
      ‖π g.1 v - v‖ ^ 2 ≤ (L : ℝ) ^ 2 * ∑ s ∈ S₂, ‖π s v - v‖ ^ 2 :=
    fun g => exists_word_bound S₂ (hsub g.1 g.2)
  choose L hL using hL
  let C : ℝ := 1 + ∑ g : S₁, (L g : ℝ) ^ 2
  have hC : 0 < C := by
    have : 0 ≤ ∑ g : S₁, (L g : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    linarith
  refine ⟨κ / C, div_pos h.1 hC, fun V _ _ _ π v hv => ?_⟩
  have hgap := h.2 V π v hv
  have hsum : ∑ g ∈ S₁, ‖π g v - v‖ ^ 2 ≤ C * ∑ s ∈ S₂, ‖π s v - v‖ ^ 2 := by
    calc ∑ g ∈ S₁, ‖π g v - v‖ ^ 2
        = ∑ g : S₁, ‖π g.1 v - v‖ ^ 2 := (Finset.sum_coe_sort S₁ _).symm
      _ ≤ ∑ g : S₁, ((L g : ℝ) ^ 2 * ∑ s ∈ S₂, ‖π s v - v‖ ^ 2) :=
          Finset.sum_le_sum fun g _ => hL g V π v
      _ = (∑ g : S₁, (L g : ℝ) ^ 2) * ∑ s ∈ S₂, ‖π s v - v‖ ^ 2 := (Finset.sum_mul _ _ _).symm
      _ ≤ C * ∑ s ∈ S₂, ‖π s v - v‖ ^ 2 := by
          have hnn : 0 ≤ ∑ s ∈ S₂, ‖π s v - v‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
          nlinarith [show (∑ g : S₁, (L g : ℝ) ^ 2) ≤ C by dsimp only [C]; linarith]
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  linarith

/-- Extension permanence of spectral gap (BHV Prop. 1.7.6). -/
lemma hasSpectralGap_extension {Γ : Type} [Group Γ] [DecidableEq Γ]
    (N : Subgroup Γ) [N.Normal] [DecidableEq (Γ ⧸ N)] (S_N : Finset N) (S_Q : Finset Γ) {κ_N κ_Q : ℝ}
    (hN : HasSpectralGap S_N κ_N)
    (hQ : HasSpectralGap (S_Q.image (QuotientGroup.mk' N)) κ_Q) :
    ∃ κ : ℝ, HasSpectralGap (S_N.image N.subtype ∪ S_Q) κ := by
  let M : ℝ := 2 + 8 * (S_Q.card : ℝ) / κ_N
  have hM : 0 < M := by have := hN.1; positivity
  let κ : ℝ := min κ_N κ_Q / (M + 1)
  have hκ : 0 < κ := div_pos (lt_min hN.1 hQ.1) (by linarith)
  refine ⟨κ, hκ, fun V _ _ _ π v hv => ?_⟩
  set K := invSubspace π N
  set v₁ : V := K.starProjection v
  set v₂ : V := v - v₁
  have hv₁K : v₁ ∈ K := Submodule.coe_mem _
  have hv₂K : v₂ ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have hpyth : ‖v‖ ^ 2 = ‖v₁‖ ^ 2 + ‖v₂‖ ^ 2 := by
    have := K.norm_sq_eq_add_norm_sq_projection v
    have h1 : ‖K.orthogonalProjectionOnto v‖ = ‖v₁‖ := rfl
    have h2 : ‖Kᗮ.orthogonalProjectionOnto v‖ = ‖v₂‖ := by
      change ‖Kᗮ.starProjection v‖ = ‖v - v₁‖
      rw [K.starProjection_orthogonal_val]
    rw [h1, h2] at this; exact this
  -- N-gap on v₂
  let πN : N →* V ≃ₗᵢ[ℂ] V := π.comp N.subtype
  have hv₂_orthN : v₂ ∈ (invSubspace πN ⊤)ᗮ := by
    rw [Submodule.mem_orthogonal] at hv₂K ⊢
    intro u hu
    apply hv₂K u
    intro g hg
    exact hu ⟨g, hg⟩ trivial
  have hgapN : κ_N * ‖v₂‖ ^ 2 ≤ ∑ s ∈ S_N, ‖π s.1 v - v‖ ^ 2 := by
    have h1 := hN.2 V πN v₂ hv₂_orthN
    refine h1.trans_eq (Finset.sum_congr rfl fun s _ => ?_)
    have hfix : π s.1 v₁ = v₁ := hv₁K s.1 s.2
    have hsub : πN s v₂ - v₂ = π s.1 v - v := by
      change π s.1 (v - v₁) - (v - v₁) = π s.1 v - v
      rw [map_sub, hfix]; abel
    rw [hsub]
  -- Q/N-gap on v₁ ∈ K
  have hK_inv : ∀ g : Γ, ∀ u : V, u ∈ K → π g u ∈ K := fun g u hu =>
    invSubspace_mem_of_norm π (fun h hh => Subgroup.Normal.conj_mem' ‹_› h hh g) hu
  let πK : Γ →* K ≃ₗᵢ[ℂ] K := restrictRep π K hK_inv
  have hN_ker : N ≤ πK.ker := by
    intro g hg
    ext ⟨u, hu⟩
    exact hu g hg
  let πQ : (Γ ⧸ N) →* K ≃ₗᵢ[ℂ] K := QuotientGroup.lift N πK hN_ker
  have : CompleteSpace K := (isClosed_invSubspace π N).completeSpace_coe
  have hv₁_orthQ : (⟨v₁, hv₁K⟩ : K) ∈ (invSubspace πQ ⊤)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro ⟨u, huK⟩ huQ
    have huG : u ∈ invSubspace π ⊤ := by
      intro g _
      have := congrArg Subtype.val (huQ (QuotientGroup.mk' N g) trivial)
      simpa [πQ, πK, restrictRep] using this
    have h1 : ⟪(⟨u, huK⟩ : K), (⟨v₁, hv₁K⟩ : K)⟫_ℂ = ⟪u, v₁⟫_ℂ := rfl
    rw [h1]
    have h2 : ⟪u, v₂⟫_ℂ = 0 := (Submodule.mem_orthogonal K v₂).mp hv₂K u huK
    have h3 : ⟪u, v⟫_ℂ = 0 := (Submodule.mem_orthogonal (invSubspace π ⊤) v).mp hv u huG
    have h4 : v₁ = v - v₂ := by dsimp only [v₂]; abel
    rw [h4, inner_sub_right, h3, h2, sub_zero]
  have hgapQ := hQ.2 K πQ ⟨v₁, hv₁K⟩ hv₁_orthQ
  have hQ_bound : ∑ q ∈ S_Q.image (QuotientGroup.mk' N), ‖πQ q ⟨v₁, hv₁K⟩ - ⟨v₁, hv₁K⟩‖ ^ 2 ≤
      2 * ∑ s ∈ S_Q, ‖π s v - v‖ ^ 2 + 8 * (S_Q.card : ℝ) * ‖v₂‖ ^ 2 := by
    have hstep : ∀ s ∈ S_Q, ‖πQ (QuotientGroup.mk' N s) ⟨v₁, hv₁K⟩ - ⟨v₁, hv₁K⟩‖ ^ 2 ≤
        2 * ‖π s v - v‖ ^ 2 + 8 * ‖v₂‖ ^ 2 := by
      intro s _
      change ‖π s v₁ - v₁‖ ^ 2 ≤ _
      have hsplit : π s v₁ - v₁ = (π s v - v) - (π s v₂ - v₂) := by
        have : v₁ = v - v₂ := by dsimp only [v₂]; abel
        rw [this, map_sub]; abel
      have htri : ‖π s v₁ - v₁‖ ≤ ‖π s v - v‖ + 2 * ‖v₂‖ := by
        rw [hsplit]
        have h2v : ‖π s v₂ - v₂‖ ≤ 2 * ‖v₂‖ := by
          calc ‖π s v₂ - v₂‖ ≤ ‖π s v₂‖ + ‖v₂‖ := norm_sub_le _ _
            _ = 2 * ‖v₂‖ := by rw [(π s).norm_map]; ring
        linarith [norm_sub_le (π s v - v) (π s v₂ - v₂)]
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖π s v - v‖ - 2 * ‖v₂‖), norm_nonneg (π s v - v), norm_nonneg v₂]
    calc ∑ q ∈ S_Q.image (QuotientGroup.mk' N), ‖πQ q ⟨v₁, hv₁K⟩ - ⟨v₁, hv₁K⟩‖ ^ 2
        ≤ ∑ s ∈ S_Q, ‖πQ (QuotientGroup.mk' N s) ⟨v₁, hv₁K⟩ - ⟨v₁, hv₁K⟩‖ ^ 2 :=
          Finset.sum_image_le_of_nonneg fun _ _ => sq_nonneg _
      _ ≤ ∑ s ∈ S_Q, (2 * ‖π s v - v‖ ^ 2 + 8 * ‖v₂‖ ^ 2) := Finset.sum_le_sum hstep
      _ = 2 * ∑ s ∈ S_Q, ‖π s v - v‖ ^ 2 + 8 * (S_Q.card : ℝ) * ‖v₂‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]; ring
  have hS_N_le : ∑ s ∈ S_N, ‖π s.1 v - v‖ ^ 2 ≤ ∑ g ∈ S_N.image N.subtype ∪ S_Q, ‖π g v - v‖ ^ 2 := by
    have h1 : ∑ s ∈ S_N, ‖π s.1 v - v‖ ^ 2 = ∑ g ∈ S_N.image N.subtype, ‖π g v - v‖ ^ 2 :=
      (Finset.sum_image (f := fun g => ‖π g v - v‖ ^ 2) fun _ _ _ _ h => Subtype.ext h).symm
    rw [h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => sq_nonneg _
  have hS_Q_le : ∑ s ∈ S_Q, ‖π s v - v‖ ^ 2 ≤ ∑ g ∈ S_N.image N.subtype ∪ S_Q, ‖π g v - v‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun _ _ _ => sq_nonneg _
  set T := ∑ g ∈ S_N.image N.subtype ∪ S_Q, ‖π g v - v‖ ^ 2
  have hT_nn : 0 ≤ T := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv₂_le : ‖v₂‖ ^ 2 ≤ T / κ_N := by
    rw [le_div_iff₀ hN.1]; linarith
  have hv₁_norm : ‖(⟨v₁, hv₁K⟩ : K)‖ ^ 2 = ‖v₁‖ ^ 2 := rfl
  rw [hv₁_norm] at hgapQ
  have hQ_T : κ_Q * ‖v₁‖ ^ 2 ≤ M * T := by
    have h1 : κ_Q * ‖v₁‖ ^ 2 ≤ 2 * T + 8 * (S_Q.card : ℝ) * (T / κ_N) := by
      have := mul_le_mul_of_nonneg_left hv₂_le (show 0 ≤ 8 * (S_Q.card : ℝ) by positivity)
      linarith
    have h2 : 2 * T + 8 * (S_Q.card : ℝ) * (T / κ_N) = M * T := by dsimp only [M]; ring
    linarith
  have hm1 : min κ_N κ_Q * ‖v₁‖ ^ 2 ≤ M * T :=
    (mul_le_mul_of_nonneg_right (min_le_right κ_N κ_Q) (sq_nonneg _)).trans hQ_T
  have hm2 : min κ_N κ_Q * ‖v₂‖ ^ 2 ≤ T :=
    (mul_le_mul_of_nonneg_right (min_le_left κ_N κ_Q) (sq_nonneg _)).trans (by linarith)
  have hcomb : min κ_N κ_Q * ‖v‖ ^ 2 ≤ (M + 1) * T := by
    rw [hpyth, mul_add]; linarith
  dsimp only [κ]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < M + 1)]
  linarith

end AbstractGap

/- ### 2. Subspace ε-orthogonality and Ershov–Jaikin-Zapirain's 3-subgroup criterion -/

section SubspaceGeom

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Two subspaces `X, Y` are `ε`-orthogonal if `‖⟪x, y⟫‖ ≤ ε ‖x‖ ‖y‖` for all `x ∈ X, y ∈ Y`. -/
def EpsOrth (X Y : Submodule ℂ V) (ε : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖

lemma epsOrth_symm {X Y : Submodule ℂ V} {ε : ℝ} (h : EpsOrth X Y ε) : EpsOrth Y X ε := by
  intro y hy x hx
  rw [← inner_conj_symm, RCLike.norm_conj]
  calc ‖⟪x, y⟫_ℂ‖ ≤ ε * ‖x‖ * ‖y‖ := h x hx y hy
    _ = ε * ‖y‖ * ‖x‖ := by ring

lemma epsOrth_mono {X Y : Submodule ℂ V} {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂) (h : EpsOrth X Y ε₁) :
    EpsOrth X Y ε₂ := fun x hx y hy =>
  (h x hx y hy).trans (by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε (norm_nonneg x)) (norm_nonneg y)
    linarith)

lemma epsOrth_mono_subspace {X₁ X₂ Y₁ Y₂ : Submodule ℂ V} {ε : ℝ}
    (hX : X₁ ≤ X₂) (hY : Y₁ ≤ Y₂) (h : EpsOrth X₂ Y₂ ε) : EpsOrth X₁ Y₁ ε :=
  fun x hx y hy => h x (hX hx) y (hY hy)

lemma epsOrth_closure {X Y : Submodule ℂ V} {ε : ℝ} (h : EpsOrth X Y ε) :
    EpsOrth X.topologicalClosure Y.topologicalClosure ε := by
  have h1 : EpsOrth X Y.topologicalClosure ε := by
    intro x hx y hy
    have hcl : IsClosed {z : V | ‖⟪x, z⟫_ℂ‖ ≤ ε * ‖x‖ * ‖z‖} :=
      isClosed_le (continuous_norm.comp (continuous_const.inner continuous_id))
        (continuous_const.mul continuous_norm)
    exact (hcl.closure_subset_iff.mpr fun z hz => h x hx z hz) hy
  intro x hx y hy
  have hcl : IsClosed {z : V | ‖⟪z, y⟫_ℂ‖ ≤ ε * ‖z‖ * ‖y‖} :=
    isClosed_le (continuous_norm.comp (continuous_id.inner continuous_const))
      ((continuous_const.mul continuous_norm).mul continuous_const)
  exact (hcl.closure_subset_iff.mpr fun z hz => h1 z hz y hy) hx

lemma epsOrth_iff_proj_le [CompleteSpace V] {X Y : Submodule ℂ V} [Y.HasOrthogonalProjection]
    {ε : ℝ} (hε : 0 ≤ ε) :
    EpsOrth X Y ε ↔ ∀ x ∈ X, ‖Y.starProjection x‖ ≤ ε * ‖x‖ := by
  constructor
  · intro h x hx
    set p := Y.starProjection x
    have hpY : p ∈ Y := Submodule.coe_mem _
    have horth : ⟪x - p, p⟫_ℂ = 0 := Y.starProjection_inner_eq_zero x p hpY
    have hinner : ⟪x, p⟫_ℂ = ⟪p, p⟫_ℂ := by
      have : ⟪x, p⟫_ℂ - ⟪p, p⟫_ℂ = 0 := by rwa [← inner_sub_left]
      exact sub_eq_zero.mp this
    have hnorm_sq : ‖p‖ ^ 2 = ‖⟪x, p⟫_ℂ‖ := by
      rw [hinner, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    have hle := h x hx p hpY
    rw [← hnorm_sq] at hle
    by_cases hp0 : ‖p‖ = 0
    · rw [hp0]; positivity
    · have hp_pos : 0 < ‖p‖ := lt_of_le_of_ne (norm_nonneg p) (Ne.symm hp0)
      nlinarith
  · intro h x hx y hy
    have h1 : ⟪x, y⟫_ℂ = ⟪Y.starProjection x, y⟫_ℂ := by
      have horth : ⟪x - Y.starProjection x, y⟫_ℂ = 0 := Y.starProjection_inner_eq_zero x y hy
      rw [inner_sub_left, sub_eq_zero] at horth
      exact horth
    rw [h1]
    calc ‖⟪Y.starProjection x, y⟫_ℂ‖ ≤ ‖Y.starProjection x‖ * ‖y‖ := norm_inner_le_norm _ _
      _ ≤ (ε * ‖x‖) * ‖y‖ := mul_le_mul_of_nonneg_right (h x hx) (norm_nonneg y)

/-- EJZ Lemma 2.1: If `X, Y` are closed, `ε`-orthogonal, and `closure(X + Y) = ⊤`,
then `Xᗮ` and `Yᗮ` are `ε`-orthogonal. -/
lemma epsOrth_orth_of_closure_sup_eq_top [CompleteSpace V] {X Y : Submodule ℂ V}
    [X.HasOrthogonalProjection] [Y.HasOrthogonalProjection]
    {ε : ℝ} (hε : 0 ≤ ε) (hXY : EpsOrth X Y ε)
    (hdense : (X ⊔ Y).topologicalClosure = ⊤) :
    EpsOrth Xᗮ Yᗮ ε := by
  apply epsOrth_symm
  rw [epsOrth_iff_proj_le hε]
  set P := Yᗮ.starProjection
  -- Step 1: bound on `P '' X`
  have hPX : ∀ x ∈ X, ‖Xᗮ.starProjection (P x)‖ ≤ ε * ‖P x‖ := by
    intro x hx
    set y := P x
    have hyY' : y ∈ Yᗮ := Submodule.coe_mem _
    have hxyY : x - y ∈ Y := by
      have : x - y = Y.starProjection x := by
        dsimp only [y, P]; rw [Y.starProjection_orthogonal_val]; abel
      rw [this]; exact Submodule.coe_mem _
    have hxy_norm : ‖x - y‖ ≤ ε * ‖x‖ := by
      have : x - y = Y.starProjection x := by
        dsimp only [y, P]; rw [Y.starProjection_orthogonal_val]; abel
      rw [this]; exact (epsOrth_iff_proj_le hε).mp hXY x hx
    have hpyth : ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖x - y‖ ^ 2 := by
      have h1 := Y.norm_sq_eq_add_norm_sq_projection x
      have h2 : ‖Y.orthogonalProjectionOnto x‖ = ‖x - y‖ := by
        change ‖Y.starProjection x‖ = ‖x - y‖
        congr 1; dsimp only [y, P]; rw [Y.starProjection_orthogonal_val]; abel
      have h3 : ‖Yᗮ.orthogonalProjectionOnto x‖ = ‖y‖ := rfl
      rw [h2, h3] at h1; linarith
    by_cases hx0 : x = 0
    · subst hx0; simp [y]
    have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    let c : ℝ := ‖y‖ ^ 2 / ‖x‖ ^ 2
    have hmin : ‖Xᗮ.starProjection y‖ ≤ ‖y - (c : ℂ) • x‖ := by
      rw [X.starProjection_orthogonal_val, X.starProjection_minimal]
      have hmem : (c : ℂ) • x ∈ X := X.smul_mem _ hx
      exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨(c : ℂ) • x, hmem⟩ : X)
    have hyx_inner : ⟪y, x⟫_ℂ = ((‖y‖ ^ 2 : ℝ) : ℂ) := by
      have horth : ⟪y, x - y⟫_ℂ = 0 := (Submodule.mem_orthogonal' Y y).mp hyY' (x - y) hxyY
      rw [inner_sub_right, sub_eq_zero] at horth
      rw [horth, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
    have hv_sq : ‖y - (c : ℂ) • x‖ ^ 2 ≤ (ε * ‖y‖) ^ 2 := by
      have h1 : ‖y - (c : ℂ) • x‖ ^ 2 =
          ‖y‖ ^ 2 - 2 * RCLike.re ⟪y, (c : ℂ) • x⟫_ℂ + ‖(c : ℂ) • x‖ ^ 2 :=
        norm_sub_sq y ((c : ℂ) • x)
      have h2 : RCLike.re ⟪y, (c : ℂ) • x⟫_ℂ = c * ‖y‖ ^ 2 := by
        rw [inner_smul_right, hyx_inner, ← Complex.ofReal_mul]
        exact Complex.ofReal_re _
      have h3 : ‖(c : ℂ) • x‖ ^ 2 = c ^ 2 * ‖x‖ ^ 2 := by
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by dsimp only [c]; positivity), mul_pow]
      rw [h1, h2, h3]
      have h4 : ‖y‖ ^ 2 - 2 * (c * ‖y‖ ^ 2) + c ^ 2 * ‖x‖ ^ 2 =
          (‖y‖ ^ 2 / ‖x‖ ^ 2) * (‖x‖ ^ 2 - ‖y‖ ^ 2) := by
        dsimp only [c]; field_simp [ne_of_gt hx_pos]; ring
      rw [h4, show ‖x‖ ^ 2 - ‖y‖ ^ 2 = ‖x - y‖ ^ 2 by linarith]
      have hsq_xy : ‖x - y‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hxy_norm 2
      have h5 : (‖y‖ ^ 2 / ‖x‖ ^ 2) * ‖x - y‖ ^ 2 ≤ (‖y‖ ^ 2 / ‖x‖ ^ 2) * (ε * ‖x‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq_xy (by positivity)
      have h6 : (‖y‖ ^ 2 / ‖x‖ ^ 2) * (ε * ‖x‖) ^ 2 = (ε * ‖y‖) ^ 2 := by
        field_simp [ne_of_gt hx_pos]
      linarith
    have hrt := Real.sqrt_le_sqrt hv_sq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hε (norm_nonneg _))] at hrt
    exact hmin.trans hrt
  -- Step 2: `closure(P '' X) = Yᗮ`
  let M : Submodule ℂ V := (X.map P.toLinearMap).topologicalClosure
  have hM_le : M ≤ Yᗮ :=
    Submodule.topologicalClosure_minimal _ (by rintro _ ⟨x, _, rfl⟩; exact Submodule.coe_mem _) Y.isClosed_orthogonal
  have hM_eq : M = Yᗮ := by
    apply le_antisymm hM_le
    intro w hw
    have : M.HasOrthogonalProjection := hasOrthProj_of_isClosed (X.map P.toLinearMap).isClosed_topologicalClosure
    set u := w - M.starProjection w
    have huM : u ∈ Mᗮ := M.sub_starProjection_mem_orthogonal w
    have huY' : u ∈ Yᗮ := Yᗮ.sub_mem hw (hM_le (Submodule.coe_mem _))
    have hu_orth_XY : u ∈ (X ⊔ Y)ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      rw [Submodule.mem_sup] at hz
      obtain ⟨x, hx, y, hy, rfl⟩ := hz
      rw [inner_add_right]
      have hy0 : ⟪u, y⟫_ℂ = 0 := (Submodule.mem_orthogonal' Y u).mp huY' y hy
      have hx_split : x = P x + Y.starProjection x := by
        dsimp only [P]; rw [Y.starProjection_orthogonal_val]; abel
      have hPx0 : ⟪u, P x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal' M u).mp huM (P x)
          (Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩)
      have hYx0 : ⟪u, Y.starProjection x⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal' Y u).mp huY' _ (Submodule.coe_mem _)
      rw [hx_split, inner_add_right, hPx0, hYx0, hy0, add_zero, add_zero]
    have hu_orth_top : u ∈ (⊤ : Submodule ℂ V)ᗮ := by
      rw [← hdense]
      rw [Submodule.mem_orthogonal'] at hu_orth_XY ⊢
      intro z hz
      have hcl : IsClosed {t : V | ⟪u, t⟫_ℂ = 0} :=
        isClosed_eq (continuous_const.inner continuous_id) continuous_const
      exact (hcl.closure_subset_iff.mpr fun t ht => hu_orth_XY t ht) hz
    have hu0 : u = 0 := by
      have := (Submodule.mem_orthogonal' (⊤ : Submodule ℂ V) u).mp hu_orth_top u trivial
      exact inner_self_eq_zero.mp this
    have hw_eq : w = M.starProjection w := sub_eq_zero.mp hu0
    rw [hw_eq]; exact Submodule.coe_mem _
  -- Step 3: extend bound by continuity from `P '' X` to `M = Yᗮ`
  intro w hw
  rw [← hM_eq] at hw
  have hcl : IsClosed {z : V | ‖Xᗮ.starProjection z‖ ≤ ε * ‖z‖} :=
    isClosed_le (continuous_norm.comp Xᗮ.starProjection.continuous)
      (continuous_const.mul continuous_norm)
  refine (hcl.closure_subset_iff.mpr ?_) hw
  rintro _ ⟨x, hx, rfl⟩
  exact hPX x hx

/-- EJZ Lemma 2.2: If `X ⊥_{ε₃} Y`, `X ⊥_{ε₂} Z`, `Y ⊥_{ε₁} Z` with `ε₃ < 1`,
then `closure(X + Y) ⊥_{ε₀} Z` for `ε₀ = √2 * max ε₁ ε₂ / √(1 - ε₃)`. -/
lemma epsOrth_sup_left [CompleteSpace V] {X Y Z : Submodule ℂ V} [Z.HasOrthogonalProjection]
    {ε₁ ε₂ ε₃ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₃ : 0 ≤ ε₃) (hε₃_lt : ε₃ < 1)
    (hXY : EpsOrth X Y ε₃) (hXZ : EpsOrth X Z ε₂) (hYZ : EpsOrth Y Z ε₁) :
    EpsOrth (X ⊔ Y).topologicalClosure Z (Real.sqrt 2 * max ε₁ ε₂ / Real.sqrt (1 - ε₃)) := by
  have h1m : 0 < 1 - ε₃ := by linarith
  have hε0_nn : 0 ≤ Real.sqrt 2 * max ε₁ ε₂ / Real.sqrt (1 - ε₃) := by positivity
  have hsup : EpsOrth (X ⊔ Y) Z (Real.sqrt 2 * max ε₁ ε₂ / Real.sqrt (1 - ε₃)) := by
    rw [epsOrth_iff_proj_le hε0_nn]
    intro v hv
    rw [Submodule.mem_sup] at hv
    obtain ⟨x, hx, y, hy, rfl⟩ := hv
    set ε := max ε₁ ε₂
    have hxZ : ‖Z.starProjection x‖ ≤ ε * ‖x‖ :=
      ((epsOrth_iff_proj_le hε₂).mp hXZ x hx).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
    have hyZ : ‖Z.starProjection y‖ ≤ ε * ‖y‖ :=
      ((epsOrth_iff_proj_le hε₁).mp hYZ y hy).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    have hnum : ‖Z.starProjection (x + y)‖ ^ 2 ≤ 2 * ε ^ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
      rw [map_add]
      have htri : ‖Z.starProjection x + Z.starProjection y‖ ≤ ‖Z.starProjection x‖ + ‖Z.starProjection y‖ :=
        norm_add_le _ _
      have hsq1 : ‖Z.starProjection x + Z.starProjection y‖ ^ 2 ≤
          2 * (‖Z.starProjection x‖ ^ 2 + ‖Z.starProjection y‖ ^ 2) := by
        have := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖Z.starProjection x‖ - ‖Z.starProjection y‖)]
      have hsqx : ‖Z.starProjection x‖ ^ 2 ≤ ε ^ 2 * ‖x‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hxZ 2; rwa [mul_pow] at this
      have hsqy : ‖Z.starProjection y‖ ^ 2 ≤ ε ^ 2 * ‖y‖ ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hyZ 2; rwa [mul_pow] at this
      linarith
    have hden : (1 - ε₃) * (‖x‖ ^ 2 + ‖y‖ ^ 2) ≤ ‖x + y‖ ^ 2 := by
      have h1 : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * RCLike.re ⟪x, y⟫_ℂ + ‖y‖ ^ 2 := norm_add_sq x y
      have h2 : |RCLike.re ⟪x, y⟫_ℂ| ≤ ε₃ * ‖x‖ * ‖y‖ :=
        (RCLike.abs_re_le_norm ⟪x, y⟫_ℂ).trans (hXY x hx y hy)
      have h3 : -RCLike.re ⟪x, y⟫_ℂ ≤ ε₃ * ‖x‖ * ‖y‖ := (neg_le_abs _).trans h2
      have h4 : 2 * (‖x‖ * ‖y‖) ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - ‖y‖)]
      nlinarith
    have hsq_goal : ‖Z.starProjection (x + y)‖ ^ 2 ≤
        (Real.sqrt 2 * ε / Real.sqrt (1 - ε₃) * ‖x + y‖) ^ 2 := by
      rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt zero_le_two, Real.sq_sqrt (le_of_lt h1m)]
      rw [div_mul_eq_mul_div, le_div_iff₀ h1m]
      have h1 := mul_le_mul_of_nonneg_left hden (show 0 ≤ 2 * ε ^ 2 by positivity)
      have h2 := mul_le_mul_of_nonneg_right hnum (le_of_lt h1m)
      linarith
    have hrt := Real.sqrt_le_sqrt hsq_goal
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hε0_nn (norm_nonneg _))] at hrt
  have hcl := epsOrth_closure hsup
  exact epsOrth_mono_subspace le_rfl (Submodule.le_topologicalClosure Z) hcl

/-- EJZ Lemma 3.4: If `H` is normalized by `K` and `H ⊔ K = ⊤`, then `V^H ⊥ V^K` when `V^⊤ = ⊥`. -/
lemma orth_normal_subgroups {Γ : Type*} [Group Γ] [CompleteSpace V]
    (π : Γ →* V ≃ₗᵢ[ℂ] V) {H K : Subgroup Γ} (hHK : H ⊔ K = ⊤)
    (hnorm : ∀ k ∈ K, ∀ h ∈ H, k⁻¹ * h * k ∈ H ∧ k * h * k⁻¹ ∈ H)
    (htriv : invSubspace π ⊤ = ⊥) :
    EpsOrth (invSubspace π H) (invSubspace π K) 0 := by
  apply epsOrth_symm
  rw [epsOrth_iff_proj_le le_rfl]
  intro v hv
  have hwK : (invSubspace π H).starProjection v ∈ invSubspace π K := by
    intro k hk
    rw [← starProjection_invSubspace_comm π (fun h hh => (hnorm k hk h hh).1)
      (fun h hh => (hnorm k hk h hh).2) v, hv k hk]
  have hwH : (invSubspace π H).starProjection v ∈ invSubspace π H := Submodule.coe_mem _
  have hw_top : (invSubspace π H).starProjection v ∈ invSubspace π ⊤ := by
    rw [← hHK, invSubspace_sup]
    exact ⟨hwH, hwK⟩
  rw [htriv, Submodule.mem_bot] at hw_top
  simp [hw_top]

/-- Subgroup `ε`-orthogonality: for every unitary representation of `H₁ ⊔ H₂` without nonzero
invariant vectors, the `H₁`-fixed and `H₂`-fixed subspaces are `ε`-orthogonal. -/
def SubgroupEpsOrth {Γ : Type} [Group Γ] (H₁ H₂ : Subgroup Γ) (ε : ℝ) : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (σ : ↥(H₁ ⊔ H₂) →* W ≃ₗᵢ[ℂ] W),
    invSubspace σ ⊤ = ⊥ →
    EpsOrth (invSubspace σ (H₁.comap (H₁ ⊔ H₂).subtype))
            (invSubspace σ (H₂.comap (H₁ ⊔ H₂).subtype)) ε

lemma subgroupEpsOrth_symm {Γ : Type} [Group Γ] {H₁ H₂ : Subgroup Γ} {ε : ℝ}
    (h : SubgroupEpsOrth H₁ H₂ ε) : SubgroupEpsOrth H₂ H₁ ε := by
  intro W _ _ _ σ htriv
  let e : ↥(H₁ ⊔ H₂) ≃* ↥(H₂ ⊔ H₁) := MulEquiv.subgroupCongr (sup_comm H₁ H₂)
  let σ' : ↥(H₁ ⊔ H₂) →* W ≃ₗᵢ[ℂ] W := σ.comp e.toMonoidHom
  have htriv' : invSubspace σ' ⊤ = ⊥ := by
    ext v; simp only [Submodule.mem_bot]
    constructor
    · intro hv
      have : v ∈ invSubspace σ ⊤ := fun g _ => by
        have := hv (e.symm g) trivial
        simpa [σ'] using this
      rwa [htriv, Submodule.mem_bot] at this
    · rintro rfl g _; simp
  have h0 := epsOrth_symm (h W σ' htriv')
  refine epsOrth_mono_subspace ?_ ?_ h0
  · intro v hv ⟨g, hg⟩ hg2
    exact hv ⟨g, (sup_comm H₁ H₂) ▸ hg⟩ hg2
  · intro v hv ⟨g, hg⟩ hg1
    exact hv ⟨g, (sup_comm H₁ H₂) ▸ hg⟩ hg1

/-- Applying `SubgroupEpsOrth` to the orthogonal complement of `V^{H₁ ⊔ H₂}` in any `Γ`-rep. -/
lemma subgroupEpsOrth_on_orth {Γ V : Type} [Group Γ] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Γ →* V ≃ₗᵢ[ℂ] V)
    {H₁ H₂ : Subgroup Γ} {ε : ℝ} (h : SubgroupEpsOrth H₁ H₂ ε) :
    EpsOrth (invSubspace π H₁ ⊓ (invSubspace π (H₁ ⊔ H₂))ᗮ)
            (invSubspace π H₂ ⊓ (invSubspace π (H₁ ⊔ H₂))ᗮ) ε := by
  set W : Submodule ℂ V := (invSubspace π (H₁ ⊔ H₂))ᗮ
  have : CompleteSpace W := (invSubspace π (H₁ ⊔ H₂)).isClosed_orthogonal.completeSpace_coe
  have hW_inv : ∀ g : ↥(H₁ ⊔ H₂), ∀ v ∈ W, π g.1 v ∈ W := by
    intro g v hv
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu
    rw [rep_inner_inv, hu g.1⁻¹ (Subgroup.inv_mem _ g.2), hv u hu]
  let σ : ↥(H₁ ⊔ H₂) →* W ≃ₗᵢ[ℂ] W := restrictRep (π.comp (H₁ ⊔ H₂).subtype) W hW_inv
  have htriv : invSubspace σ ⊤ = ⊥ := by
    ext ⟨u, huW⟩
    simp only [Submodule.mem_bot]
    constructor
    · intro hu
      have huK : u ∈ invSubspace π (H₁ ⊔ H₂) := fun g hg =>
        congrArg Subtype.val (hu ⟨g, hg⟩ trivial)
      have := (Submodule.mem_orthogonal (invSubspace π (H₁ ⊔ H₂)) u).mp huW u huK
      exact Subtype.ext (inner_self_eq_zero.mp this)
    · intro h0 g _
      rw [h0]; simp
  have h0 := h W σ htriv
  intro x ⟨hx1, hxW⟩ y ⟨hy2, hyW⟩
  have hx' : (⟨x, hxW⟩ : W) ∈ invSubspace σ (H₁.comap (H₁ ⊔ H₂).subtype) :=
    fun g hg => Subtype.ext (hx1 g.1 hg)
  have hy' : (⟨y, hyW⟩ : W) ∈ invSubspace σ (H₂.comap (H₁ ⊔ H₂).subtype) :=
    fun g hg => Subtype.ext (hy2 g.1 hg)
  exact h0 ⟨x, hxW⟩ hx' ⟨y, hyW⟩ hy'

/-- EJZ Proposition 3.2: Pairwise `ε_i`-orthogonality of three generating subgroups implies
`ε₀`-orthogonality of `H₁ ⊔ H₃` and `H₁ ⊔ H₂`. -/
lemma three_subgroups_epsOrth {Γ : Type} [Group Γ] (H₁ H₂ H₃ : Subgroup Γ)
    (hgen : H₁ ⊔ H₂ ⊔ H₃ = ⊤)
    {ε₁ ε₂ ε₃ : ℝ} (hε₁ : 0 ≤ ε₁) (hε₂ : 0 ≤ ε₂) (hε₃ : 0 ≤ ε₃)
    (hε₃_lt : ε₃ < 1)
    (h12 : SubgroupEpsOrth H₁ H₂ ε₃)
    (h13 : SubgroupEpsOrth H₁ H₃ ε₂)
    (h23 : SubgroupEpsOrth H₂ H₃ ε₁) :
    SubgroupEpsOrth (H₁ ⊔ H₃) (H₁ ⊔ H₂) (Real.sqrt 2 * max ε₁ ε₂ / Real.sqrt (1 - ε₃)) := by
  have htop : (H₁ ⊔ H₃) ⊔ (H₁ ⊔ H₂) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_right))
      (le_sup_of_le_left le_sup_right)
  intro V _ _ _ σ htrivσ
  -- Lift `σ` to `Γ` via `htop`
  let eTop : Γ ≃* ↥((H₁ ⊔ H₃) ⊔ (H₁ ⊔ H₂)) :=
    (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr htop.symm)
  let π : Γ →* V ≃ₗᵢ[ℂ] V := σ.comp eTop.toMonoidHom
  have htriv : invSubspace π ⊤ = ⊥ := by
    ext v; simp only [Submodule.mem_bot]
    constructor
    · intro hv
      have : v ∈ invSubspace σ ⊤ := fun g _ => by
        have h1 := hv g.1 trivial
        have h2 : eTop g.1 = g := Subtype.ext rfl
        simpa [π, h2] using h1
      rwa [htrivσ, Submodule.mem_bot] at this
    · rintro rfl g _; simp
  suffices hmain : EpsOrth (invSubspace π (H₁ ⊔ H₃)) (invSubspace π (H₁ ⊔ H₂))
      (Real.sqrt 2 * max ε₁ ε₂ / Real.sqrt (1 - ε₃)) by
    refine epsOrth_mono_subspace ?_ ?_ hmain
    · intro v hv g hg; exact hv ⟨g, htop ▸ Subgroup.mem_top g⟩ hg
    · intro v hv g hg; exact hv ⟨g, htop ▸ Subgroup.mem_top g⟩ hg
  set V₁ := invSubspace π (H₂ ⊔ H₃)
  set V₂ := invSubspace π (H₁ ⊔ H₃)
  set V₃ := invSubspace π (H₁ ⊔ H₂)
  set V₀ := (V₁ ⊔ V₂ ⊔ V₃).topologicalClosure
  have : CompleteSpace V₀ := (V₁ ⊔ V₂ ⊔ V₃).isClosed_topologicalClosure.completeSpace_coe
  let W₁ : Submodule ℂ V₀ := V₁.comap V₀.subtype
  let W₂ : Submodule ℂ V₀ := V₂.comap V₀.subtype
  let W₃ : Submodule ℂ V₀ := V₃.comap V₀.subtype
  have hW₁_cl : IsClosed (W₁ : Set V₀) := (isClosed_invSubspace π _).preimage continuous_subtype_val
  have hW₂_cl : IsClosed (W₂ : Set V₀) := (isClosed_invSubspace π _).preimage continuous_subtype_val
  have hW₃_cl : IsClosed (W₃ : Set V₀) := (isClosed_invSubspace π _).preimage continuous_subtype_val
  have : W₁.HasOrthogonalProjection := hasOrthProj_of_isClosed hW₁_cl
  have : W₂.HasOrthogonalProjection := hasOrthProj_of_isClosed hW₂_cl
  have : W₃.HasOrthogonalProjection := hasOrthProj_of_isClosed hW₃_cl
  have hW_dense : (W₁ ⊔ W₂ ⊔ W₃).topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro ⟨u, hu⟩ _
    change (⟨u, hu⟩ : V₀) ∈ closure ((W₁ ⊔ W₂ ⊔ W₃ : Submodule ℂ V₀) : Set V₀)
    rw [mem_closure_iff]
    intro U hU huU
    rw [isOpen_induced_iff] at hU
    obtain ⟨U', hU', rfl⟩ := hU
    obtain ⟨z, hzU', hzS⟩ := mem_closure_iff.mp hu U' hU' huU
    have hzV₀ : z ∈ V₀ := Submodule.le_topologicalClosure _ hzS
    refine ⟨⟨z, hzV₀⟩, hzU', ?_⟩
    change z ∈ V₁ ⊔ V₂ ⊔ V₃ at hzS
    rw [Submodule.mem_sup] at hzS
    obtain ⟨z12, hz12, z3, hz3, rfl⟩ := hzS
    rw [Submodule.mem_sup] at hz12
    obtain ⟨z1, hz1, z2, hz2, rfl⟩ := hz12
    have h1 : z1 ∈ V₀ := Submodule.le_topologicalClosure _ (Submodule.mem_sup_left (Submodule.mem_sup_left hz1))
    have h2 : z2 ∈ V₀ := Submodule.le_topologicalClosure _ (Submodule.mem_sup_left (Submodule.mem_sup_right hz2))
    have h3 : z3 ∈ V₀ := Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hz3)
    have hsum : (⟨z1 + z2 + z3, hzV₀⟩ : V₀) = ⟨z1, h1⟩ + ⟨z2, h2⟩ + ⟨z3, h3⟩ := rfl
    rw [hsum]
    exact Submodule.add_mem_sup (Submodule.add_mem_sup (show (⟨z1, h1⟩ : V₀) ∈ W₁ from hz1)
      (show (⟨z2, h2⟩ : V₀) ∈ W₂ from hz2)) (show (⟨z3, h3⟩ : V₀) ∈ W₃ from hz3)
  -- Helper: from `SubgroupEpsOrth Ha Hb ε`, get `(Wcᗮ ⊓ Wbᗮ) ⊥_ε (Wcᗮ ⊓ Waᗮ)` inside `V₀`
  have hpair : ∀ (Ha Hb Hc : Subgroup Γ) (ε : ℝ), 0 ≤ ε → SubgroupEpsOrth Ha Hb ε →
      ∀ (Wa Wb Wc : Submodule ℂ V₀) [Wa.HasOrthogonalProjection] [Wb.HasOrthogonalProjection]
        [Wc.HasOrthogonalProjection],
      invSubspace π (Ha ⊔ Hb) ≤ V₀ →
      Wa = (invSubspace π (Hb ⊔ Hc)).comap V₀.subtype →
      Wb = (invSubspace π (Ha ⊔ Hc)).comap V₀.subtype →
      Wc = (invSubspace π (Ha ⊔ Hb)).comap V₀.subtype →
      (Wa ⊔ Wb ⊔ Wc).topologicalClosure = ⊤ →
      EpsOrth (Wcᗮ ⊓ Wbᗮ) (Wcᗮ ⊓ Waᗮ) ε ∧
        EpsOrth ((Wc ⊔ Wb).topologicalClosure ⊓ Wcᗮ) ((Wc ⊔ Wa).topologicalClosure ⊓ Wcᗮ) ε := by
    intro Ha Hb Hc ε hε hHab Wa Wb Wc _ _ _ hVc_le hWa hWb hWc hWtop
    set A : Submodule ℂ V₀ := (Wc ⊔ Wb).topologicalClosure ⊓ Wcᗮ
    set B : Submodule ℂ V₀ := (Wc ⊔ Wa).topologicalClosure ⊓ Wcᗮ
    have hA_Ha : ∀ x ∈ A, x.1 ∈ invSubspace π Ha := by
      intro x ⟨hxcl, _⟩
      have hsub : Wc ⊔ Wb ≤ (invSubspace π Ha).comap V₀.subtype := by
        rw [sup_le_iff, hWc, hWb]
        exact ⟨fun z hz => invSubspace_anti π le_sup_left hz,
          fun z hz => invSubspace_anti π le_sup_left hz⟩
      have hcl : IsClosed ((invSubspace π Ha).comap V₀.subtype : Set V₀) :=
        (isClosed_invSubspace π Ha).preimage continuous_subtype_val
      exact (hcl.closure_subset_iff.mpr hsub) hxcl
    have hB_Hb : ∀ y ∈ B, y.1 ∈ invSubspace π Hb := by
      intro y ⟨hycl, _⟩
      have hsub : Wc ⊔ Wa ≤ (invSubspace π Hb).comap V₀.subtype := by
        rw [sup_le_iff, hWc, hWa]
        exact ⟨fun z hz => invSubspace_anti π le_sup_right hz,
          fun z hz => invSubspace_anti π le_sup_left hz⟩
      have hcl : IsClosed ((invSubspace π Hb).comap V₀.subtype : Set V₀) :=
        (isClosed_invSubspace π Hb).preimage continuous_subtype_val
      exact (hcl.closure_subset_iff.mpr hsub) hycl
    have hWc_orth_V : ∀ z ∈ Wcᗮ, z.1 ∈ (invSubspace π (Ha ⊔ Hb))ᗮ := by
      intro z hz
      rw [Submodule.mem_orthogonal]
      intro u hu
      exact (Submodule.mem_orthogonal Wc z).mp hz ⟨u, hVc_le hu⟩ (by rw [hWc]; exact hu)
    have hAB : EpsOrth A B ε := by
      have h0 := subgroupEpsOrth_on_orth π hHab
      intro x hx y hy
      exact h0 x.1 ⟨hA_Ha x hx, hWc_orth_V x hx.2⟩ y.1 ⟨hB_Hb y hy, hWc_orth_V y hy.2⟩
    refine ⟨?_, hAB⟩
    -- Apply `epsOrth_orth_of_closure_sup_eq_top` inside the Hilbert space `Wcᗮ`!
    have : CompleteSpace Wcᗮ := Wc.isClosed_orthogonal.completeSpace_coe
    let A' : Submodule ℂ Wcᗮ := A.comap Wcᗮ.subtype
    let B' : Submodule ℂ Wcᗮ := B.comap Wcᗮ.subtype
    have hA'_cl : IsClosed (A' : Set Wcᗮ) :=
      ((Wc ⊔ Wb).isClosed_topologicalClosure.inter Wc.isClosed_orthogonal).preimage continuous_subtype_val
    have hB'_cl : IsClosed (B' : Set Wcᗮ) :=
      ((Wc ⊔ Wa).isClosed_topologicalClosure.inter Wc.isClosed_orthogonal).preimage continuous_subtype_val
    have : A'.HasOrthogonalProjection := hasOrthProj_of_isClosed hA'_cl
    have : B'.HasOrthogonalProjection := hasOrthProj_of_isClosed hB'_cl
    have hA'B' : EpsOrth A' B' ε := fun x hx y hy => hAB x.1 hx y.1 hy
    have hA'B'_dense : (A' ⊔ B').topologicalClosure = ⊤ := by
      rw [eq_top_iff]
      intro u _
      have : (A' ⊔ B').topologicalClosure.HasOrthogonalProjection :=
        hasOrthProj_of_isClosed (A' ⊔ B').isClosed_topologicalClosure
      set z := u - (A' ⊔ B').topologicalClosure.starProjection u
      have hz_orth : z ∈ (A' ⊔ B').topologicalClosureᗮ :=
        (A' ⊔ B').topologicalClosure.sub_starProjection_mem_orthogonal u
      have hz0 : z = 0 := by
        -- Show `z.1 ∈ (Wa ⊔ Wb ⊔ Wc)ᗮ = ⊥` in `V₀`
        have hz_Wa : z.1 ∈ Waᗮ := by
          rw [Submodule.mem_orthogonal']
          intro w hw
          have hpw : Wcᗮ.starProjection w ∈ B := by
            refine ⟨Submodule.le_topologicalClosure _ ?_, Submodule.coe_mem _⟩
            rw [Wc.starProjection_orthogonal_val]
            exact Submodule.sub_mem _ (Submodule.mem_sup_right hw) (Submodule.mem_sup_left (Submodule.coe_mem _))
          have h1 : ⟪z.1, Wcᗮ.starProjection w⟫_ℂ = 0 :=
            (Submodule.mem_orthogonal' _ z).mp hz_orth ⟨Wcᗮ.starProjection w, hpw.2⟩
              (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hpw))
          have h2 : w = Wcᗮ.starProjection w + Wc.starProjection w := by
            rw [Wc.starProjection_orthogonal_val]; abel
          have h3 : ⟪z.1, Wc.starProjection w⟫_ℂ = 0 :=
            (Submodule.mem_orthogonal' Wc z.1).mp z.2 _ (Submodule.coe_mem _)
          rw [h2, inner_add_right, h1, h3, add_zero]
        have hz_Wb : z.1 ∈ Wbᗮ := by
          rw [Submodule.mem_orthogonal']
          intro w hw
          have hpw : Wcᗮ.starProjection w ∈ A := by
            refine ⟨Submodule.le_topologicalClosure _ ?_, Submodule.coe_mem _⟩
            rw [Wc.starProjection_orthogonal_val]
            exact Submodule.sub_mem _ (Submodule.mem_sup_right hw) (Submodule.mem_sup_left (Submodule.coe_mem _))
          have h1 : ⟪z.1, Wcᗮ.starProjection w⟫_ℂ = 0 :=
            (Submodule.mem_orthogonal' _ z).mp hz_orth ⟨Wcᗮ.starProjection w, hpw.2⟩
              (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hpw))
          have h2 : w = Wcᗮ.starProjection w + Wc.starProjection w := by
            rw [Wc.starProjection_orthogonal_val]; abel
          have h3 : ⟪z.1, Wc.starProjection w⟫_ℂ = 0 :=
            (Submodule.mem_orthogonal' Wc z.1).mp z.2 _ (Submodule.coe_mem _)
          rw [h2, inner_add_right, h1, h3, add_zero]
        have hz_all : ∀ w ∈ Wa ⊔ Wb ⊔ Wc, ⟪z.1, w⟫_ℂ = 0 := by
          intro w hw
          rw [Submodule.mem_sup] at hw
          obtain ⟨w12, hw12, wc, hwc, rfl⟩ := hw
          rw [Submodule.mem_sup] at hw12
          obtain ⟨wa, hwa, wb, hwb, rfl⟩ := hw12
          rw [inner_add_right, inner_add_right,
            (Submodule.mem_orthogonal' Wa z.1).mp hz_Wa wa hwa,
            (Submodule.mem_orthogonal' Wb z.1).mp hz_Wb wb hwb,
            (Submodule.mem_orthogonal' Wc z.1).mp z.2 wc hwc, add_zero, add_zero]
        have hz_top : ∀ w : V₀, ⟪z.1, w⟫_ℂ = 0 := by
          intro w
          have hw : w ∈ (Wa ⊔ Wb ⊔ Wc).topologicalClosure := by rw [hWtop]; trivial
          have hcl : IsClosed {t : V₀ | ⟪z.1, t⟫_ℂ = 0} :=
            isClosed_eq (continuous_const.inner continuous_id) continuous_const
          exact (hcl.closure_subset_iff.mpr hz_all) hw
        exact Subtype.ext (inner_self_eq_zero.mp (hz_top z.1))
      have hu_eq : u = (A' ⊔ B').topologicalClosure.starProjection u := sub_eq_zero.mp hz0
      rw [hu_eq]; exact Submodule.coe_mem _
    have horth := epsOrth_orth_of_closure_sup_eq_top hε hA'B' hA'B'_dense
    intro x ⟨hxC, hxB⟩ y ⟨hyC, hyA⟩
    have hx' : (⟨x, hxC⟩ : Wcᗮ) ∈ A'ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro a ha
      have hsub : ∀ w ∈ Wc ⊔ Wb, ⟪x, w⟫_ℂ = 0 := by
        intro w hw
        rw [Submodule.mem_sup] at hw
        obtain ⟨wc, hwc, wb, hwb, rfl⟩ := hw
        rw [inner_add_right, (Submodule.mem_orthogonal' Wc x).mp hxC wc hwc,
          (Submodule.mem_orthogonal' Wb x).mp hxB wb hwb, add_zero]
      have hcl : IsClosed {t : V₀ | ⟪x, t⟫_ℂ = 0} :=
        isClosed_eq (continuous_const.inner continuous_id) continuous_const
      exact (hcl.closure_subset_iff.mpr hsub) ha.1
    have hy' : (⟨y, hyC⟩ : Wcᗮ) ∈ B'ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro b hb
      have hsub : ∀ w ∈ Wc ⊔ Wa, ⟪y, w⟫_ℂ = 0 := by
        intro w hw
        rw [Submodule.mem_sup] at hw
        obtain ⟨wc, hwc, wa, hwa, rfl⟩ := hw
        rw [inner_add_right, (Submodule.mem_orthogonal' Wc y).mp hyC wc hwc,
          (Submodule.mem_orthogonal' Wa y).mp hyA wa hwa, add_zero]
      have hcl : IsClosed {t : V₀ | ⟪y, t⟫_ℂ = 0} :=
        isClosed_eq (continuous_const.inner continuous_id) continuous_const
      exact (hcl.closure_subset_iff.mpr hsub) hb.1
    exact horth ⟨x, hxC⟩ hx' ⟨y, hyC⟩ hy'
  -- Apply `hpair` to all three cyclic permutations
  have hV₁_le : V₁ ≤ V₀ := fun z hz => Submodule.le_topologicalClosure _ (Submodule.mem_sup_left (Submodule.mem_sup_left hz))
  have hV₂_le : V₂ ≤ V₀ := fun z hz => Submodule.le_topologicalClosure _ (Submodule.mem_sup_left (Submodule.mem_sup_right hz))
  have hV₃_le : V₃ ≤ V₀ := fun z hz => Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hz)
  have h3 := hpair H₁ H₂ H₃ ε₃ hε₃ h12 W₁ W₂ W₃ hV₃_le rfl rfl rfl hW_dense
  have hW_dense2 : (W₁ ⊔ W₃ ⊔ W₂).topologicalClosure = ⊤ := by
    have : W₁ ⊔ W₃ ⊔ W₂ = W₁ ⊔ W₂ ⊔ W₃ := by ac_rfl
    rw [this]; exact hW_dense
  have h2 := hpair H₁ H₃ H₂ ε₂ hε₂ h13 W₁ W₃ W₂ hV₂_le (by rw [sup_comm H₃ H₂]) rfl rfl hW_dense2
  have hW_dense1 : (W₂ ⊔ W₃ ⊔ W₁).topologicalClosure = ⊤ := by
    have : W₂ ⊔ W₃ ⊔ W₁ = W₁ ⊔ W₂ ⊔ W₃ := by ac_rfl
    rw [this]; exact hW_dense
  have h1 := hpair H₂ H₃ H₁ ε₁ hε₁ h23 W₂ W₃ W₁ hV₁_le (by rw [sup_comm H₃ H₁]) (by rw [sup_comm H₂ H₁]) rfl hW_dense1
  -- Apply `epsOrth_sup_left` to `X' = W₃ᗮ ⊓ W₂ᗮ`, `Y' = W₃ᗮ ⊓ W₁ᗮ`, `Z' = W₁ᗮ ⊓ W₂ᗮ`
  set X' : Submodule ℂ V₀ := W₃ᗮ ⊓ W₂ᗮ
  set Y' : Submodule ℂ V₀ := W₃ᗮ ⊓ W₁ᗮ
  set Z' : Submodule ℂ V₀ := W₁ᗮ ⊓ W₂ᗮ
  have hZ'_cl : IsClosed (Z' : Set V₀) := W₁.isClosed_orthogonal.inter W₂.isClosed_orthogonal
  have : Z'.HasOrthogonalProjection := hasOrthProj_of_isClosed hZ'_cl
  have hX'Z' : EpsOrth X' Z' ε₂ := by
    refine epsOrth_mono_subspace (by rw [inf_comm]) (by rw [inf_comm]) h2.1
  have hY'Z' : EpsOrth Y' Z' ε₁ := by
    refine epsOrth_mono_subspace (by rw [inf_comm]) le_rfl h1.1
  have hXY_Z' := epsOrth_sup_left hε₁ hε₂ hε₃ hε₃_lt h3.1 hX'Z' hY'Z'
  -- Show `(X' ⊔ Y').topologicalClosure = W₃ᗮ`
  have hXY_eq : (X' ⊔ Y').topologicalClosure = W₃ᗮ := by
    apply le_antisymm
    · exact (X' ⊔ Y').topologicalClosure_minimal (sup_le inf_le_left inf_le_left) W₃.isClosed_orthogonal
    · intro u hu
      have : (X' ⊔ Y').topologicalClosure.HasOrthogonalProjection :=
        hasOrthProj_of_isClosed (X' ⊔ Y').isClosed_topologicalClosure
      set z := u - (X' ⊔ Y').topologicalClosure.starProjection u
      have hz_orth : z ∈ (X' ⊔ Y').topologicalClosureᗮ :=
        (X' ⊔ Y').topologicalClosure.sub_starProjection_mem_orthogonal u
      have hzW₃' : z ∈ W₃ᗮ := W₃ᗮ.sub_mem hu
        ((X' ⊔ Y').topologicalClosure_minimal (sup_le inf_le_left inf_le_left) W₃.isClosed_orthogonal
          (Submodule.coe_mem _))
      have hz_cl2 : z ∈ (W₃ ⊔ W₂).topologicalClosure := by
        have : (W₃ ⊔ W₂).topologicalClosure.HasOrthogonalProjection :=
          hasOrthProj_of_isClosed (W₃ ⊔ W₂).isClosed_topologicalClosure
        rw [← Submodule.orthogonal_orthogonal (W₃ ⊔ W₂).topologicalClosure]
        rw [Submodule.mem_orthogonal]
        intro w hw
        have hwX' : w ∈ X' := by
          refine ⟨?_, ?_⟩
          · change w ∈ W₃ᗮ; rw [Submodule.mem_orthogonal]; intro a ha
            exact (Submodule.mem_orthogonal _ w).mp hw a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left ha))
          · change w ∈ W₂ᗮ; rw [Submodule.mem_orthogonal]; intro a ha
            exact (Submodule.mem_orthogonal _ w).mp hw a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right ha))
        exact (Submodule.mem_orthogonal _ z).mp hz_orth w (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hwX'))
      have hz_cl1 : z ∈ (W₃ ⊔ W₁).topologicalClosure := by
        have : (W₃ ⊔ W₁).topologicalClosure.HasOrthogonalProjection :=
          hasOrthProj_of_isClosed (W₃ ⊔ W₁).isClosed_topologicalClosure
        rw [← Submodule.orthogonal_orthogonal (W₃ ⊔ W₁).topologicalClosure]
        rw [Submodule.mem_orthogonal]
        intro w hw
        have hwY' : w ∈ Y' := by
          refine ⟨?_, ?_⟩
          · change w ∈ W₃ᗮ; rw [Submodule.mem_orthogonal]; intro a ha
            exact (Submodule.mem_orthogonal _ w).mp hw a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left ha))
          · change w ∈ W₁ᗮ; rw [Submodule.mem_orthogonal]; intro a ha
            exact (Submodule.mem_orthogonal _ w).mp hw a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right ha))
        exact (Submodule.mem_orthogonal _ z).mp hz_orth w (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hwY'))
      have hz0 : z = 0 := by
        have hle := h3.2 z ⟨hz_cl2, hzW₃'⟩ z ⟨hz_cl1, hzW₃'⟩
        rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)] at hle
        have : ‖z‖ ^ 2 ≤ ε₃ * ‖z‖ ^ 2 := by linarith
        have : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖]
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
      rw [sub_eq_zero.mp hz0]; exact Submodule.coe_mem _
  rw [hXY_eq] at hXY_Z'
  -- Show `(W₃ᗮ ⊔ Z').topologicalClosure = ⊤` in `V₀`
  have hW₃Z'_dense : (W₃ᗮ ⊔ Z').topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have : (W₃ᗮ ⊔ Z').topologicalClosure.HasOrthogonalProjection :=
      hasOrthProj_of_isClosed (W₃ᗮ ⊔ Z').isClosed_topologicalClosure
    set z := u - (W₃ᗮ ⊔ Z').topologicalClosure.starProjection u
    have hz_orth : z ∈ (W₃ᗮ ⊔ Z').topologicalClosureᗮ :=
      (W₃ᗮ ⊔ Z').topologicalClosure.sub_starProjection_mem_orthogonal u
    have hzW₃ : z ∈ W₃ := by
      rw [← Submodule.orthogonal_orthogonal W₃]
      rw [Submodule.mem_orthogonal]
      intro w hw
      exact (Submodule.mem_orthogonal _ z).mp hz_orth w (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hw))
    have hz_cl12 : z ∈ (W₁ ⊔ W₂).topologicalClosure := by
      have : (W₁ ⊔ W₂).topologicalClosure.HasOrthogonalProjection :=
        hasOrthProj_of_isClosed (W₁ ⊔ W₂).isClosed_topologicalClosure
      rw [← Submodule.orthogonal_orthogonal (W₁ ⊔ W₂).topologicalClosure]
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hwZ' : w ∈ Z' := by
        refine ⟨?_, ?_⟩
        · change w ∈ W₁ᗮ; rw [Submodule.mem_orthogonal]; intro a ha
          exact (Submodule.mem_orthogonal _ w).mp hw a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left ha))
        · change w ∈ W₂ᗮ; rw [Submodule.mem_orthogonal]; intro a ha
          exact (Submodule.mem_orthogonal _ w).mp hw a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right ha))
      exact (Submodule.mem_orthogonal _ z).mp hz_orth w (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hwZ'))
    have hzH₃ : z.1 ∈ invSubspace π H₃ := by
      have hsub : W₁ ⊔ W₂ ≤ (invSubspace π H₃).comap V₀.subtype := by
        rw [sup_le_iff]
        exact ⟨fun a ha => invSubspace_anti π le_sup_right ha,
          fun a ha => invSubspace_anti π le_sup_right ha⟩
      have hcl : IsClosed ((invSubspace π H₃).comap V₀.subtype : Set V₀) :=
        (isClosed_invSubspace π H₃).preimage continuous_subtype_val
      exact (hcl.closure_subset_iff.mpr hsub) hz_cl12
    have hz_top : z.1 ∈ invSubspace π ⊤ := by
      rw [← hgen, invSubspace_sup]
      exact ⟨hzW₃, hzH₃⟩
    rw [htriv, Submodule.mem_bot] at hz_top
    have hz0 : z = 0 := Subtype.ext hz_top
    rw [sub_eq_zero.mp hz0]; exact Submodule.coe_mem _
  -- Apply Lemma 2.1 one final time: `W₃ᗮᗮ ⊥_{ε₀} Z'ᗮ`
  have hε0_nn : 0 ≤ Real.sqrt 2 * max ε₁ ε₂ / Real.sqrt (1 - ε₃) := by
    have : 0 < 1 - ε₃ := by linarith
    positivity
  have hfin := epsOrth_orth_of_closure_sup_eq_top hε0_nn hXY_Z' hW₃Z'_dense
  -- Translate back to `V₂` and `V₃` inside `V`
  intro x hx y hy
  have hx' : (⟨x, hV₂_le hx⟩ : V₀) ∈ Z'ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w ⟨_, hw2⟩
    exact (Submodule.mem_orthogonal' W₂ w).mp hw2 ⟨x, hV₂_le hx⟩ hx
  have hy' : (⟨y, hV₃_le hy⟩ : V₀) ∈ W₃ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal]; exact hy
  exact epsOrth_symm hfin ⟨x, hV₂_le hx⟩ hx' ⟨y, hV₃_le hy⟩ hy'

/-- EJZ Lemma 2.5 + Lemma 3.1 for two subgroups: if `H, K` generate `Γ` and are `ε`-orthogonal
with `ε < 1`, then for any `v ⊥ V^Γ`, the sum of squared orthogonal projections onto `(V^H)ᗮ`
and `(V^K)ᗮ` is at least `(1 - ε) * ‖v‖^2`. -/
lemma two_subgroups_proj_sum_ge {Γ V : Type} [Group Γ] [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V] (π : Γ →* V ≃ₗᵢ[ℂ] V)
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤) {ε : ℝ} (hε : 0 ≤ ε)
    (hHK : SubgroupEpsOrth H K ε) {v : V} (hv : v ∈ (invSubspace π ⊤)ᗮ) :
    (1 - ε) * ‖v‖ ^ 2 ≤
      ‖(invSubspace π H)ᗮ.starProjection v‖ ^ 2 + ‖(invSubspace π K)ᗮ.starProjection v‖ ^ 2 := by
  set aH := (invSubspace π H).starProjection v
  set aK := (invSubspace π K).starProjection v
  set bH := (invSubspace π H)ᗮ.starProjection v
  set bK := (invSubspace π K)ᗮ.starProjection v
  have haH_orth : aH ∈ (invSubspace π (H ⊔ K))ᗮ := by
    rw [hgen, Submodule.mem_orthogonal]
    intro u hu
    have huH : u ∈ invSubspace π H := invSubspace_anti π le_top hu
    have h1 : ⟪u, v - aH⟫_ℂ = 0 := by
      have := (invSubspace π H).starProjection_inner_eq_zero v u huH
      rw [← inner_conj_symm, this, map_zero]
    have h2 : ⟪u, v⟫_ℂ = 0 := (Submodule.mem_orthogonal (invSubspace π ⊤) v).mp hv u hu
    rw [inner_sub_right, h2, zero_sub, neg_eq_zero] at h1
    exact h1
  have haK_orth : aK ∈ (invSubspace π (H ⊔ K))ᗮ := by
    rw [hgen, Submodule.mem_orthogonal]
    intro u hu
    have huK : u ∈ invSubspace π K := invSubspace_anti π le_top hu
    have h1 : ⟪u, v - aK⟫_ℂ = 0 := by
      have := (invSubspace π K).starProjection_inner_eq_zero v u huK
      rw [← inner_conj_symm, this, map_zero]
    have h2 : ⟪u, v⟫_ℂ = 0 := (Submodule.mem_orthogonal (invSubspace π ⊤) v).mp hv u hu
    rw [inner_sub_right, h2, zero_sub, neg_eq_zero] at h1
    exact h1
  have horth_ab := subgroupEpsOrth_on_orth π hHK aH ⟨Submodule.coe_mem _, haH_orth⟩
    aK ⟨Submodule.coe_mem _, haK_orth⟩
  have hpythH : ‖v‖ ^ 2 = ‖aH‖ ^ 2 + ‖bH‖ ^ 2 := (invSubspace π H).norm_sq_eq_add_norm_sq_projection v
  have hpythK : ‖v‖ ^ 2 = ‖aK‖ ^ 2 + ‖bK‖ ^ 2 := (invSubspace π K).norm_sq_eq_add_norm_sq_projection v
  -- `‖aH + aK‖^2 ≤ (1 + ε) (‖aH‖^2 + ‖aK‖^2)` and `⟪aH + aK, v⟫ = ‖aH‖^2 + ‖aK‖^2`
  have hsum_sq : ‖aH + aK‖ ^ 2 ≤ (1 + ε) * (‖aH‖ ^ 2 + ‖aK‖ ^ 2) := by
    have h1 : ‖aH + aK‖ ^ 2 = ‖aH‖ ^ 2 + 2 * RCLike.re ⟪aH, aK⟫_ℂ + ‖aK‖ ^ 2 := norm_add_sq aH aK
    have h2 : RCLike.re ⟪aH, aK⟫_ℂ ≤ ε * ‖aH‖ * ‖aK‖ :=
      (RCLike.re_le_norm _).trans horth_ab
    have h3 : 2 * (‖aH‖ * ‖aK‖) ≤ ‖aH‖ ^ 2 + ‖aK‖ ^ 2 := by nlinarith [sq_nonneg (‖aH‖ - ‖aK‖)]
    nlinarith
  have hinner_v : ⟪aH + aK, v⟫_ℂ = ((‖aH‖ ^ 2 + ‖aK‖ ^ 2 : ℝ) : ℂ) := by
    have hH : ⟪aH, v⟫_ℂ = ((‖aH‖ ^ 2 : ℝ) : ℂ) := by
      have : ⟪aH, v - aH⟫_ℂ = 0 := by
        have := (invSubspace π H).starProjection_inner_eq_zero v aH (Submodule.coe_mem _)
        rw [← inner_conj_symm, this, map_zero]
      rw [inner_sub_right, sub_eq_zero] at this
      rw [this, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
    have hK : ⟪aK, v⟫_ℂ = ((‖aK‖ ^ 2 : ℝ) : ℂ) := by
      have : ⟪aK, v - aK⟫_ℂ = 0 := by
        have := (invSubspace π K).starProjection_inner_eq_zero v aK (Submodule.coe_mem _)
        rw [← inner_conj_symm, this, map_zero]
      rw [inner_sub_right, sub_eq_zero] at this
      rw [this, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
    rw [inner_add_left, hH, hK, Complex.ofReal_add]
  have hcs : (‖aH‖ ^ 2 + ‖aK‖ ^ 2) ^ 2 ≤ ‖aH + aK‖ ^ 2 * ‖v‖ ^ 2 := by
    have h1 : ‖⟪aH + aK, v⟫_ℂ‖ ≤ ‖aH + aK‖ * ‖v‖ := norm_inner_le_norm _ _
    rw [hinner_v, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h1
    have h2 := pow_le_pow_left₀ (by positivity) h1 2
    rwa [mul_pow] at h2
  have ha_sum_le : ‖aH‖ ^ 2 + ‖aK‖ ^ 2 ≤ (1 + ε) * ‖v‖ ^ 2 := by
    have h1 : (‖aH‖ ^ 2 + ‖aK‖ ^ 2) ^ 2 ≤ (1 + ε) * (‖aH‖ ^ 2 + ‖aK‖ ^ 2) * ‖v‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hsum_sq (sq_nonneg ‖v‖)
      linarith
    by_cases h0 : ‖aH‖ ^ 2 + ‖aK‖ ^ 2 = 0
    · rw [h0]; positivity
    · have hpos : 0 < ‖aH‖ ^ 2 + ‖aK‖ ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h0)
      nlinarith
  linarith

/-- Spectral gap for `H ⊔ K` from `SubgroupEpsOrth H K ε` and spectral gaps on `H` and `K`. -/
lemma two_subgroups_spectralGap {Γ : Type} [Group Γ] [DecidableEq Γ]
    (H K : Subgroup Γ) (hgen : H ⊔ K = ⊤) {ε : ℝ} (hε : 0 ≤ ε) (hε_lt : ε < 1)
    (hHK : SubgroupEpsOrth H K ε)
    {SH : Finset H} {SK : Finset K} {κH κK : ℝ}
    (hH : HasSpectralGap SH κH) (hK : HasSpectralGap SK κK) :
    HasSpectralGap (SH.image H.subtype ∪ SK.image K.subtype)
      ((1 - ε) * min κH κK / 2) := by
  have hκ_pos : 0 < (1 - ε) * min κH κK / 2 := by
    have := lt_min hH.1 hK.1; linarith [mul_pos (show 0 < 1 - ε by linarith) this]
  refine ⟨hκ_pos, fun V _ _ _ π v hv => ?_⟩
  have hproj := two_subgroups_proj_sum_ge π H K hgen hε hHK hv
  set bH := (invSubspace π H)ᗮ.starProjection v
  set bK := (invSubspace π K)ᗮ.starProjection v
  let πH : H →* V ≃ₗᵢ[ℂ] V := π.comp H.subtype
  let πK : K →* V ≃ₗᵢ[ℂ] V := π.comp K.subtype
  have hbH_orth : bH ∈ (invSubspace πH ⊤)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have huH : u ∈ invSubspace π H := fun g hg => hu ⟨g, hg⟩ trivial
    exact (Submodule.mem_orthogonal (invSubspace π H) bH).mp (Submodule.coe_mem _) u huH
  have hbK_orth : bK ∈ (invSubspace πK ⊤)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have huK : u ∈ invSubspace π K := fun g hg => hu ⟨g, hg⟩ trivial
    exact (Submodule.mem_orthogonal (invSubspace π K) bK).mp (Submodule.coe_mem _) u huK
  have hgapH : κH * ‖bH‖ ^ 2 ≤ ∑ g ∈ SH.image H.subtype, ‖π g v - v‖ ^ 2 := by
    have h1 := hH.2 V πH bH hbH_orth
    rw [Finset.sum_image (f := fun g => ‖π g v - v‖ ^ 2) (g := H.subtype) fun _ _ _ _ h => Subtype.ext h]
    refine h1.trans_eq (Finset.sum_congr rfl fun s _ => ?_)
    have ha_mem : (invSubspace π H).starProjection v ∈ invSubspace π H := Submodule.coe_mem _
    have ha : π s.1 ((invSubspace π H).starProjection v) = (invSubspace π H).starProjection v :=
      ha_mem s.1 s.2
    have hsub : πH s bH - bH = π s.1 v - v := by
      change π s.1 ((invSubspace π H)ᗮ.starProjection v) - (invSubspace π H)ᗮ.starProjection v = _
      rw [(invSubspace π H).starProjection_orthogonal_val, map_sub, ha]; abel
    rw [hsub]; rfl
  have hgapK : κK * ‖bK‖ ^ 2 ≤ ∑ g ∈ SK.image K.subtype, ‖π g v - v‖ ^ 2 := by
    have h1 := hK.2 V πK bK hbK_orth
    rw [Finset.sum_image (f := fun g => ‖π g v - v‖ ^ 2) (g := K.subtype) fun _ _ _ _ h => Subtype.ext h]
    refine h1.trans_eq (Finset.sum_congr rfl fun s _ => ?_)
    have ha_mem : (invSubspace π K).starProjection v ∈ invSubspace π K := Submodule.coe_mem _
    have ha : π s.1 ((invSubspace π K).starProjection v) = (invSubspace π K).starProjection v :=
      ha_mem s.1 s.2
    have hsub : πK s bK - bK = π s.1 v - v := by
      change π s.1 ((invSubspace π K)ᗮ.starProjection v) - (invSubspace π K)ᗮ.starProjection v = _
      rw [(invSubspace π K).starProjection_orthogonal_val, map_sub, ha]; abel
    rw [hsub]; rfl
  set T := ∑ g ∈ SH.image H.subtype ∪ SK.image K.subtype, ‖π g v - v‖ ^ 2
  have hT_H : ∑ g ∈ SH.image H.subtype, ‖π g v - v‖ ^ 2 ≤ T :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left fun _ _ _ => sq_nonneg _
  have hT_K : ∑ g ∈ SK.image K.subtype, ‖π g v - v‖ ^ 2 ≤ T :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right fun _ _ _ => sq_nonneg _
  have hmin : min κH κK * (‖bH‖ ^ 2 + ‖bK‖ ^ 2) ≤ 2 * T := by
    have hmH := mul_le_mul_of_nonneg_right (min_le_left κH κK) (sq_nonneg ‖bH‖)
    have hmK := mul_le_mul_of_nonneg_right (min_le_right κH κK) (sq_nonneg ‖bK‖)
    linarith
  have h1 := mul_le_mul_of_nonneg_right hproj (le_of_lt (lt_min hH.1 hK.1))
  linarith

/-- EJZ Corollary 3.3: Three generating subgroups with pairwise `ε`-orthogonality
(`√2 * ε / √(1 - ε) < 1`) and individual spectral gaps yield a spectral gap for `Γ`. -/
lemma three_subgroups_spectralGap {Γ : Type} [Group Γ] [DecidableEq Γ]
    (H₁ H₂ H₃ : Subgroup Γ) (hgen : H₁ ⊔ H₂ ⊔ H₃ = ⊤)
    {ε : ℝ} (hε : 0 ≤ ε) (hε_lt : ε < 1) (hε0_lt : Real.sqrt 2 * ε / Real.sqrt (1 - ε) < 1)
    (h12 : SubgroupEpsOrth H₁ H₂ ε)
    (h13 : SubgroupEpsOrth H₁ H₃ ε)
    (h23 : SubgroupEpsOrth H₂ H₃ ε)
    {S₁ : Finset H₁} {S₂ : Finset H₂} {S₃ : Finset H₃} {κ : ℝ}
    (hH₁ : HasSpectralGap S₁ κ) (hH₂ : HasSpectralGap S₂ κ) (hH₃ : HasSpectralGap S₃ κ) :
    ∃ κ' : ℝ, HasSpectralGap (S₁.image H₁.subtype ∪ S₂.image H₂.subtype ∪ S₃.image H₃.subtype) κ' := by
  -- Helper: spectral gap on `Ha ⊔ Hb` from `SubgroupEpsOrth Ha Hb ε`
  have hpair_gap : ∀ (Ha Hb : Subgroup Γ) (Sa : Finset Ha) (Sb : Finset Hb),
      SubgroupEpsOrth Ha Hb ε → HasSpectralGap Sa κ → HasSpectralGap Sb κ →
      ∃ κab : ℝ, HasSpectralGap
        (Sa.image (Subgroup.inclusion (le_sup_left : Ha ≤ Ha ⊔ Hb)) ∪
          Sb.image (Subgroup.inclusion (le_sup_right : Hb ≤ Ha ⊔ Hb))) κab := by
    intro Ha Hb Sa Sb hHab hHa hHb
    let Ha' : Subgroup ↥(Ha ⊔ Hb) := Ha.comap (Ha ⊔ Hb).subtype
    let Hb' : Subgroup ↥(Ha ⊔ Hb) := Hb.comap (Ha ⊔ Hb).subtype
    have hgen' : Ha' ⊔ Hb' = ⊤ := by
      rw [eq_top_iff]; rintro ⟨g, hg⟩ _
      have hsub : ∀ x (hx : x ∈ Ha ⊔ Hb), (⟨x, hx⟩ : ↥(Ha ⊔ Hb)) ∈ Ha' ⊔ Hb' := by
        intro x hx
        have hx' : x ∈ Subgroup.closure ((Ha : Set Γ) ∪ (Hb : Set Γ)) := by
          rwa [← Subgroup.sup_eq_closure]
        induction hx' using Subgroup.closure_induction with
        | mem u hu =>
          rcases hu with hu | hu
          · exact Subgroup.mem_sup_left hu
          · exact Subgroup.mem_sup_right hu
        | one => exact Subgroup.one_mem _
        | mul u v hu hv ihu ihv =>
          have hu' : u ∈ Ha ⊔ Hb := by rwa [Subgroup.sup_eq_closure]
          have hv' : v ∈ Ha ⊔ Hb := by rwa [Subgroup.sup_eq_closure]
          exact Subgroup.mul_mem _ (ihu hu') (ihv hv')
        | inv u hu ihu =>
          have hu' : u ∈ Ha ⊔ Hb := by rwa [Subgroup.sup_eq_closure]
          exact Subgroup.inv_mem _ (ihu hu')
      exact hsub g hg
    have hHab' : SubgroupEpsOrth Ha' Hb' ε := by
      intro W _ _ _ σ htriv
      let e : ↥(Ha ⊔ Hb) ≃* ↥(Ha' ⊔ Hb') :=
        (Subgroup.topEquiv.symm).trans (MulEquiv.subgroupCongr hgen'.symm)
      let σ' := σ.comp e.toMonoidHom
      have htriv' : invSubspace σ' ⊤ = ⊥ := by
        ext v; simp only [Submodule.mem_bot]
        constructor
        · intro hv
          have : v ∈ invSubspace σ ⊤ := fun g _ => by
            have h1 := hv g.1 trivial
            have h2 : e g.1 = g := Subtype.ext rfl
            simpa [σ', h2] using h1
          rwa [htriv, Submodule.mem_bot] at this
        · rintro rfl g _; simp
      have h0 := hHab W σ' htriv'
      refine epsOrth_mono_subspace ?_ ?_ h0
      · intro v hv g hg; exact hv ⟨g, hgen' ▸ Subgroup.mem_top g⟩ hg
      · intro v hv g hg; exact hv ⟨g, hgen' ▸ Subgroup.mem_top g⟩ hg
    let ea : Ha ≃* Ha' :=
      { toFun := fun x => ⟨⟨x.1, (le_sup_left : Ha ≤ Ha ⊔ Hb) x.2⟩, x.2⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    let eb : Hb ≃* Hb' :=
      { toFun := fun x => ⟨⟨x.1, (le_sup_right : Hb ≤ Ha ⊔ Hb) x.2⟩, x.2⟩
        invFun := fun x => ⟨x.1.1, x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_mul' := fun _ _ => rfl }
    have hHa' := hasSpectralGap_of_surjective ea.toMonoidHom ea.surjective hHa
    have hHb' := hasSpectralGap_of_surjective eb.toMonoidHom eb.surjective hHb
    have hgap := two_subgroups_spectralGap Ha' Hb' hgen' hε hε_lt hHab' hHa' hHb'
    have hset : (Sa.image ea.toMonoidHom).image Ha'.subtype ∪ (Sb.image eb.toMonoidHom).image Hb'.subtype =
        Sa.image (Subgroup.inclusion (le_sup_left : Ha ≤ Ha ⊔ Hb)) ∪
          Sb.image (Subgroup.inclusion (le_sup_right : Hb ≤ Ha ⊔ Hb)) := by
      ext ⟨x, hx⟩
      simp only [Finset.mem_union, Finset.mem_image]
      constructor
      · rintro (⟨a, ⟨a', ha', rfl⟩, h⟩ | ⟨b, ⟨b', hb', rfl⟩, h⟩)
        · exact Or.inl ⟨a', ha', h⟩
        · exact Or.inr ⟨b', hb', h⟩
      · rintro (⟨a', ha', h⟩ | ⟨b', hb', h⟩)
        · exact Or.inl ⟨ea a', ⟨a', ha', rfl⟩, h⟩
        · exact Or.inr ⟨eb b', ⟨b', hb', rfl⟩, h⟩
    exact ⟨_, hset ▸ hgap⟩
  obtain ⟨κ12, hgap12⟩ := hpair_gap H₁ H₂ S₁ S₂ h12 hH₁ hH₂
  obtain ⟨κ13, hgap13⟩ := hpair_gap H₁ H₃ S₁ S₃ h13 hH₁ hH₃
  have h13_12 := three_subgroups_epsOrth H₁ H₂ H₃ hgen hε hε hε hε_lt h12 h13 h23
  rw [max_self] at h13_12
  have htop : (H₁ ⊔ H₃) ⊔ (H₁ ⊔ H₂) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_right))
      (le_sup_of_le_left le_sup_right)
  have hε0_nn : 0 ≤ Real.sqrt 2 * ε / Real.sqrt (1 - ε) := by
    have : 0 < 1 - ε := by linarith
    positivity
  have hfinal := two_subgroups_spectralGap (H₁ ⊔ H₃) (H₁ ⊔ H₂) htop hε0_nn hε0_lt h13_12 hgap13 hgap12
  refine ⟨_, hasSpectralGap_mono ?_ le_rfl hfinal.1 hfinal⟩
  intro g hg
  simp only [Finset.mem_union, Finset.mem_image, Subgroup.coe_subtype, Subtype.exists] at hg ⊢
  rcases hg with (⟨a, ha, (⟨x, hx, hxs, hxeq⟩ | ⟨x, hx, hxs, hxeq⟩), rfl⟩ |
                  ⟨a, ha, (⟨x, hx, hxs, hxeq⟩ | ⟨x, hx, hxs, hxeq⟩), rfl⟩)
  · left; left; exact ⟨x, hx, hxs, congrArg Subtype.val hxeq⟩
  · right; exact ⟨x, hx, hxs, congrArg Subtype.val hxeq⟩
  · left; left; exact ⟨x, hx, hxs, congrArg Subtype.val hxeq⟩
  · left; right; exact ⟨x, hx, hxs, congrArg Subtype.val hxeq⟩

end SubspaceGeom

/- ### 3. Property (T) for the finite-field covers `Δ_d` (via finite 5-group averaging) -/

section DeltaPropT

/-- Ordered product of a `Fin k`-indexed family in a possibly noncommutative monoid. -/
def finProd {M : Type*} [Monoid M] {k : ℕ} (a : Fin k → M) : M :=
  ((List.finRange k).map a).prod

lemma list_prod_mul_of_comm {M : Type*} [Monoid M] {α : Type*} (l : List α) (a b : α → M)
    (hcomm : ∀ x ∈ l, ∀ y ∈ l, Commute (a x) (b y)) :
    (l.map a).prod * (l.map b).prod = (l.map fun x => a x * b x).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons]
    have hcomm_xs : ∀ u ∈ xs, ∀ v ∈ xs, Commute (a u) (b v) :=
      fun u hu v hv => hcomm u (List.mem_cons_of_mem x hu) v (List.mem_cons_of_mem x hv)
    have hc : Commute (xs.map a).prod (b x) := by
      have : ∀ z ∈ xs.map a, Commute z (b x) := by
        intro z hz
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hz
        exact hcomm u (List.mem_cons_of_mem x hu) x (List.mem_cons_self)
      exact Commute.list_prod_left _ _ this
    calc (a x * (xs.map a).prod) * (b x * (xs.map b).prod)
        = a x * ((xs.map a).prod * b x) * (xs.map b).prod := by simp [mul_assoc]
      _ = a x * (b x * (xs.map a).prod) * (xs.map b).prod := by rw [hc.eq]
      _ = (a x * b x) * ((xs.map a).prod * (xs.map b).prod) := by simp [mul_assoc]
      _ = (a x * b x) * (xs.map fun y => a y * b y).prod := by rw [ih hcomm_xs]

lemma finProd_mul {M : Type*} [Monoid M] {k : ℕ} (a b : Fin k → M)
    (hcomm : ∀ i j, Commute (a i) (b j)) :
    finProd a * finProd b = finProd (fun i => a i * b i) :=
  list_prod_mul_of_comm (List.finRange k) a b fun i _ j _ => hcomm i j

lemma finProd_one {M : Type*} [Monoid M] {k : ℕ} :
    finProd (fun _ : Fin k => (1 : M)) = 1 := by
  simp [finProd]

lemma finProd_congr {M : Type*} [Monoid M] {k : ℕ} {a b : Fin k → M} (h : ∀ i, a i = b i) :
    finProd a = finProd b := by
  dsimp only [finProd]; congr 1; exact List.map_congr_left fun i _ => h i

lemma finProd_single {M : Type*} [Monoid M] {k : ℕ} (a : Fin k → M) (j : Fin k)
    (h : ∀ i, i ≠ j → a i = 1) : finProd a = a j := by
  have hlist : ∀ (l : List (Fin k)), l.Nodup →
      (l.map a).prod = if j ∈ l then a j else 1 := by
    intro l hl
    induction l with
    | nil => simp
    | cons x xs ih =>
      rw [List.nodup_cons] at hl
      simp only [List.map_cons, List.prod_cons, List.mem_cons]
      rw [ih hl.2]
      by_cases hxj : x = j
      · subst hxj; rw [if_neg hl.1, if_pos (Or.inl rfl), mul_one]
      · rw [h x hxj, one_mul]
        by_cases h1 : j ∈ xs
        · rw [if_pos h1, if_pos (Or.inr h1)]
        · rw [if_neg h1, if_neg (by rintro (rfl | hj); exact hxj rfl; exact h1 hj)]
  have := hlist (List.finRange k) (List.nodup_finRange k)
  simpa [finProd] using this

lemma finProd_mem_subgroup {G : Type*} [Group G] {k : ℕ} (H : Subgroup G) (a : Fin k → G)
    (ha : ∀ i, a i ∈ H) : finProd a ∈ H :=
  H.list_prod_mem fun _ hx => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ha i

lemma commute_finProd_left {M : Type*} [Monoid M] {k : ℕ} (a : Fin k → M) (x : M)
    (h : ∀ i, Commute (a i) x) : Commute (finProd a) x :=
  Commute.list_prod_left _ _ fun _ hy => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hy
    exact h i

lemma finProd_pow {M : Type*} [Monoid M] {k : ℕ} (a : Fin k → M)
    (hcomm : ∀ i j, Commute (a i) (a j)) (n : ℕ) :
    finProd a ^ n = finProd (fun i => a i ^ n) := by
  induction n with
  | zero => simp [finProd_one]
  | succ n ih =>
    rw [pow_succ, ih, finProd_mul _ _ fun i j => (hcomm i j).pow_left n]
    exact finProd_congr fun i => (pow_succ (a i) n).symm

/-- Reindexing a `finProd` along an equivalence when factors pairwise commute. -/
lemma finProd_equiv {M : Type*} [Monoid M] {k₁ k₂ : ℕ} (e : Fin k₁ ≃ Fin k₂)
    (a : Fin k₂ → M) (hcomm : ∀ i j, Commute (a i) (a j)) :
    finProd (fun i => a (e i)) = finProd a := by
  -- Both lists are permutations of each other and their elements pairwise commute!
  have hperm : ((List.finRange k₁).map (fun i => a (e i))).Perm ((List.finRange k₂).map a) := by
    have h1 : ((List.finRange k₁).map e).Perm (List.finRange k₂) := by
      rw [List.perm_ext_iff_of_nodup ((List.nodup_finRange k₁).map e.injective) (List.nodup_finRange k₂)]
      intro j; simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
      exact ⟨e.symm j, e.apply_symm_apply j⟩
    have h2 := h1.map a
    rw [List.map_map] at h2
    exact h2
  have hprod_perm : ∀ {l₁ l₂ : List M}, l₁.Perm l₂ → (∀ x ∈ l₂, ∀ y ∈ l₂, Commute x y) →
      l₁.prod = l₂.prod := by
    intro l₁ l₂ hp hc
    induction hp with
    | nil => rfl
    | cons x hp ih =>
      simp only [List.prod_cons]
      rw [ih fun u hu v hv => hc u (List.mem_cons_of_mem x hu) v (List.mem_cons_of_mem x hv)]
    | swap x y l =>
      simp only [List.prod_cons, ← mul_assoc]
      congr 1
      exact (hc y (List.mem_cons_of_mem x List.mem_cons_self) x List.mem_cons_self).eq
    | trans hp₁ hp₂ ih₁ ih₂ =>
      have hc' : ∀ u ∈ _, ∀ v ∈ _, Commute u v := fun u hu v hv =>
        hc u (hp₂.subset hu) v (hp₂.subset hv)
      exact (ih₁ hc').trans (ih₂ hc)
  exact hprod_perm hperm fun _ hx _ hy => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
    exact hcomm i j

/-- A homomorphism from `(Fin k → ZMod 5)` (additive) to `Γ` generated by commuting elements
of order dividing 5. -/
def zmod5Hom {Γ : Type*} [Group Γ] {k : ℕ} (g : Fin k → Γ)
    (hcomm : ∀ i j, Commute (g i) (g j)) (h5 : ∀ i, g i ^ 5 = 1) :
    Multiplicative (Fin k → ZMod 5) →* Γ where
  toFun f := finProd fun i : Fin k => g i ^ ((Multiplicative.toAdd f i).val)
  map_one' := by
    change finProd (fun i : Fin k => g i ^ ((0 : ZMod 5).val)) = 1
    simp [finProd_one]
  map_mul' f₁ f₂ := by
    change finProd (fun i : Fin k => g i ^ (((Multiplicative.toAdd f₁ i + Multiplicative.toAdd f₂ i : ZMod 5)).val)) =
      finProd (fun i : Fin k => g i ^ (Multiplicative.toAdd f₁ i).val) *
      finProd (fun i : Fin k => g i ^ (Multiplicative.toAdd f₂ i).val)
    rw [finProd_mul _ _ fun i j => ((hcomm i j).pow_left _).pow_right _]
    refine finProd_congr fun i => ?_
    rw [← pow_add, ZMod.val_add]
    have hdiv := Nat.div_add_mod ((Multiplicative.toAdd f₁ i).val + (Multiplicative.toAdd f₂ i).val) 5
    set a := (Multiplicative.toAdd f₁ i).val + (Multiplicative.toAdd f₂ i).val
    calc g i ^ (a % 5) = (g i ^ 5) ^ (a / 5) * g i ^ (a % 5) := by rw [h5 i, one_pow, one_mul]
      _ = g i ^ (5 * (a / 5) + a % 5) := by rw [← pow_mul, ← pow_add]
      _ = g i ^ a := by rw [hdiv]

lemma zmod5Hom_single {Γ : Type*} [Group Γ] {k : ℕ} (g : Fin k → Γ)
    (hcomm : ∀ i j, Commute (g i) (g j)) (h5 : ∀ i, g i ^ 5 = 1) (j : Fin k) :
    zmod5Hom g hcomm h5 (Multiplicative.ofAdd (Pi.single j (1 : ZMod 5))) = g j := by
  classical
  change finProd (fun i : Fin k => g i ^ ((Pi.single j (1 : ZMod 5) : Fin k → ZMod 5) i).val) = g j
  rw [finProd_single _ j fun i hij => by simp [Pi.single_eq_of_ne hij]]
  rw [Pi.single_eq_same, show (1 : ZMod 5).val = 1 from rfl, pow_one]

lemma zmod5Hom_range {Γ : Type*} [Group Γ] {k : ℕ} (g : Fin k → Γ)
    (hcomm : ∀ i j, Commute (g i) (g j)) (h5 : ∀ i, g i ^ 5 = 1) :
    (zmod5Hom g hcomm h5).range = Subgroup.closure (Set.range g) := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact finProd_mem_subgroup _ _ fun i =>
      Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range.mpr ⟨i, rfl⟩)) _
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨Multiplicative.ofAdd (Pi.single j 1), zmod5Hom_single g hcomm h5 j⟩

/-- Spectral gap for a finite abelian 5-group generated by `k` elements. -/
lemma finite_abelian_five_group_gap {Γ : Type} [Group Γ] [DecidableEq Γ] {k : ℕ} (g : Fin k → Γ)
    (hcomm : ∀ i j, Commute (g i) (g j)) (h5 : ∀ i, g i ^ 5 = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤) :
    HasSpectralGap (Finset.univ.image g) (1 / (8 * ((k.max 1 : ℕ) : ℝ) ^ 2)) := by
  let φ := zmod5Hom g hcomm h5
  have hsurj : Function.Surjective φ := by
    intro x
    have : x ∈ φ.range := by rw [zmod5Hom_range, hgen]; trivial
    exact this
  let A := Fin k → ZMod 5
  have hcard : Fintype.card A = 5 ^ k := by
    dsimp only [A]; simp [ZMod.card]
  have hcard_pos : (0 : ℝ) < (Fintype.card A : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hκ_pos : (0 : ℝ) < 1 / (8 * ((k.max 1 : ℕ) : ℝ) ^ 2) := by positivity
  refine ⟨hκ_pos, fun V _ _ _ π v hv => ?_⟩
  let avg : V := ((Fintype.card A : ℂ)⁻¹) • ∑ f : A, π (φ (Multiplicative.ofAdd f)) v
  have havg_inv : avg ∈ invSubspace π ⊤ := by
    intro γ _
    obtain ⟨f₀, rfl⟩ := hsurj γ
    dsimp only [avg]
    rw [map_smul, map_sum]
    congr 1
    have heq : ∑ f : A, π (φ f₀) (π (φ (Multiplicative.ofAdd f)) v) =
        ∑ f : A, π (φ (Multiplicative.ofAdd (Multiplicative.toAdd f₀ + f))) v :=
      Finset.sum_congr rfl fun f _ => by rw [← rep_mul, ← map_mul]; rfl
    rw [heq]
    exact Fintype.sum_equiv (Equiv.addLeft (Multiplicative.toAdd f₀)) _ _ fun _ => rfl
  have hinner_avg : ⟪avg, v⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal (invSubspace π ⊤) v).mp hv avg havg_inv
  have hsum_inner : ∑ f : A, ⟪π (φ (Multiplicative.ofAdd f)) v, v⟫_ℂ = 0 := by
    dsimp only [avg] at hinner_avg
    rw [inner_smul_left, sum_inner] at hinner_avg
    have hinv0 : (starRingEnd ℂ) ((Fintype.card A : ℂ)⁻¹) ≠ 0 := by
      simp [Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)]
    exact (mul_eq_zero.mp hinner_avg).resolve_left hinv0
  have hsum_sq : ∑ f : A, ‖π (φ (Multiplicative.ofAdd f)) v - v‖ ^ 2 =
      2 * (Fintype.card A : ℝ) * ‖v‖ ^ 2 := by
    have hterm : ∀ f : A, ‖π (φ (Multiplicative.ofAdd f)) v - v‖ ^ 2 =
        2 * ‖v‖ ^ 2 - 2 * RCLike.re ⟪π (φ (Multiplicative.ofAdd f)) v, v⟫_ℂ := by
      intro f
      rw [norm_sub_sq (𝕜 := ℂ), (π (φ (Multiplicative.ofAdd f))).norm_map]; ring
    simp_rw [hterm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    have hre : ∑ f : A, RCLike.re ⟪π (φ (Multiplicative.ofAdd f)) v, v⟫_ℂ = 0 := by
      change ∑ f : A, (⟪π (φ (Multiplicative.ofAdd f)) v, v⟫_ℂ).re = 0
      rw [← Complex.re_sum, hsum_inner, Complex.zero_re]
    rw [hre]; ring
  have hbound : ∀ f : A, ‖π (φ (Multiplicative.ofAdd f)) v - v‖ ^ 2 ≤
      16 * ((k.max 1 : ℕ) : ℝ) ^ 2 * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 := by
    intro f
    have hlist_le : ∀ (l : List (Fin k)) (e : Fin k → ℕ),
        ‖π (l.map fun i => g i ^ e i).prod v - v‖ ≤ (l.map fun i => (e i : ℝ) * ‖π (g i) v - v‖).sum := by
      intro l e
      induction l with
      | nil => simp
      | cons a xs ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        have hsplit : π (g a ^ e a * (xs.map fun i => g i ^ e i).prod) v - v =
            π (g a ^ e a) (π (xs.map fun i => g i ^ e i).prod v - v) + (π (g a ^ e a) v - v) := by
          rw [rep_mul, map_sub]; abel
        have hpow : ∀ m : ℕ, ‖π (g a ^ m) v - v‖ ≤ (m : ℝ) * ‖π (g a) v - v‖ := by
          intro m
          induction m with
          | zero => simp
          | succ m ihm =>
            rw [pow_succ']
            have hs : π (g a * g a ^ m) v - v = π (g a) (π (g a ^ m) v - v) + (π (g a) v - v) := by
              rw [rep_mul, map_sub]; abel
            rw [hs, Nat.cast_succ, add_mul, one_mul]
            calc ‖π (g a) (π (g a ^ m) v - v) + (π (g a) v - v)‖
                ≤ ‖π (g a) (π (g a ^ m) v - v)‖ + ‖π (g a) v - v‖ := norm_add_le _ _
              _ = ‖π (g a ^ m) v - v‖ + ‖π (g a) v - v‖ := by rw [(π (g a)).norm_map]
              _ ≤ _ := by linarith
        rw [hsplit]
        calc ‖π (g a ^ e a) (π (xs.map fun i => g i ^ e i).prod v - v) + (π (g a ^ e a) v - v)‖
            ≤ ‖π (g a ^ e a) (π (xs.map fun i => g i ^ e i).prod v - v)‖ + ‖π (g a ^ e a) v - v‖ := norm_add_le _ _
          _ = ‖π (xs.map fun i => g i ^ e i).prod v - v‖ + ‖π (g a ^ e a) v - v‖ := by rw [(π _).norm_map]
          _ ≤ _ := by linarith [hpow (e a)]
    have h1 : ‖π (φ (Multiplicative.ofAdd f)) v - v‖ ≤
        ∑ i : Fin k, ((f i).val : ℝ) * ‖π (g i) v - v‖ := by
      have h0 := hlist_le (List.finRange k) (fun i => (f i).val)
      have hsum_eq : ((List.finRange k).map fun i => ((f i).val : ℝ) * ‖π (g i) v - v‖).sum =
          ∑ i : Fin k, ((f i).val : ℝ) * ‖π (g i) v - v‖ := by
        rw [Fin.sum_univ_def]
      exact h0.trans_eq hsum_eq
    have h2 : ∑ i : Fin k, ((f i).val : ℝ) * ‖π (g i) v - v‖ ≤
        4 * ∑ i : Fin k, ‖π (g i) v - v‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have hlt : (f i).val ≤ 4 := Nat.lt_succ_iff.mp (ZMod.val_lt _)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlt) (norm_nonneg _)
    have h3 : (∑ i : Fin k, ‖π (g i) v - v‖) ^ 2 ≤
        (k : ℝ) * ∑ i : Fin k, ‖π (g i) v - v‖ ^ 2 := by
      have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin k)))
        (f := fun i => ‖π (g i) v - v‖)
      simpa using hcs
    have h4 : ∑ i : Fin k, ‖π (g i) v - v‖ ^ 2 ≤
        ((k.max 1 : ℕ) : ℝ) * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 := by
      calc ∑ i : Fin k, ‖π (g i) v - v‖ ^ 2
          ≤ ∑ _i : Fin k, ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 :=
            Finset.sum_le_sum fun i _ =>
              Finset.single_le_sum (f := fun s => ‖π s v - v‖ ^ 2) (fun _ _ => sq_nonneg _)
                (Finset.mem_image_of_mem g (Finset.mem_univ i))
        _ = (k : ℝ) * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ((k.max 1 : ℕ) : ℝ) * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast le_max_left k 1)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have htr := h1.trans h2
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htr 2
    rw [mul_pow] at hsq
    have hk_le : (k : ℝ) ≤ ((k.max 1 : ℕ) : ℝ) := by exact_mod_cast le_max_left k 1
    have hS_nn : 0 ≤ ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h5 : (k : ℝ) * ∑ i : Fin k, ‖π (g i) v - v‖ ^ 2 ≤
        ((k.max 1 : ℕ) : ℝ) ^ 2 * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 := by
      have h4' := mul_le_mul_of_nonneg_left h4 (Nat.cast_nonneg k)
      have h5' : (k : ℝ) * ((k.max 1 : ℕ) : ℝ) ≤ ((k.max 1 : ℕ) : ℝ) ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_right h5' hS_nn
      linarith
    linarith
  have hsum_le : ∑ f : A, ‖π (φ (Multiplicative.ofAdd f)) v - v‖ ^ 2 ≤
      (Fintype.card A : ℝ) * (16 * ((k.max 1 : ℕ) : ℝ) ^ 2 * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2) := by
    calc ∑ f : A, ‖π (φ (Multiplicative.ofAdd f)) v - v‖ ^ 2
        ≤ ∑ _f : A, (16 * ((k.max 1 : ℕ) : ℝ) ^ 2 * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2) :=
          Finset.sum_le_sum fun f _ => hbound f
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum_sq] at hsum_le
  have hcancel : 2 * ‖v‖ ^ 2 ≤ 16 * ((k.max 1 : ℕ) : ℝ) ^ 2 * ∑ s ∈ Finset.univ.image g, ‖π s v - v‖ ^ 2 := by
    nlinarith
  rw [one_div, inv_mul_eq_div, div_le_iff₀ (by positivity : (0 : ℝ) < 8 * ((k.max 1 : ℕ) : ℝ) ^ 2)]
  linarith

/-- Bilinearity of commutators when commutators are central. -/
lemma commutator_mul_left_of_central {G : Type*} [Group G] {x y z : G}
    (hc : Commute ⁅y, z⁆ x) : ⁅x * y, z⁆ = ⁅y, z⁆ * ⁅x, z⁆ := by
  simp only [commutatorElement_def] at hc ⊢
  calc x * y * z * (x * y)⁻¹ * z⁻¹
      = x * (y * z * y⁻¹ * z⁻¹) * (z * x⁻¹ * z⁻¹) := by group
    _ = ((y * z * y⁻¹ * z⁻¹) * x) * (z * x⁻¹ * z⁻¹) := by rw [hc.eq]
    _ = (y * z * y⁻¹ * z⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group

lemma commutator_mul_right_of_central {G : Type*} [Group G] {x y z : G}
    (hc : Commute ⁅x, z⁆ y) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  simp only [commutatorElement_def] at hc ⊢
  calc x * (y * z) * x⁻¹ * (y * z)⁻¹
      = (x * y * x⁻¹ * y⁻¹) * (y * (x * z * x⁻¹ * z⁻¹) * y⁻¹) := by group
    _ = (x * y * x⁻¹ * y⁻¹) * ((x * z * x⁻¹ * z⁻¹) * y * y⁻¹) := by rw [hc.eq]
    _ = (x * y * x⁻¹ * y⁻¹) * (x * z * x⁻¹ * z⁻¹) := by group

lemma commutator_pow_left_of_central {G : Type*} [Group G] {x z : G}
    (hc : Commute ⁅x, z⁆ x) (n : ℕ) : ⁅x ^ n, z⁆ = ⁅x, z⁆ ^ n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ n ih =>
    rw [pow_succ', pow_succ']
    have hc' : Commute ⁅x ^ n, z⁆ x := by rw [ih]; exact hc.pow_left n
    rw [commutator_mul_left_of_central hc', ih, ← pow_succ, ← pow_succ']

lemma commutator_pow_right_of_central {G : Type*} [Group G] {x z : G}
    (hc : Commute ⁅x, z⁆ z) (n : ℕ) : ⁅x, z ^ n⁆ = ⁅x, z⁆ ^ n := by
  induction n with
  | zero => simp [commutatorElement_def]
  | succ n ih =>
    rw [pow_succ', pow_succ']
    have hc' : Commute ⁅x, z ^ n⁆ z := by rw [ih]; exact hc.pow_left n
    rw [commutator_mul_right_of_central hc', ih]

/-- Character on `(Fin m → ZMod 5)` for Fourier decomposition of finite elementary abelian 5-groups. -/
def zmod5Char {m : ℕ} (ξ c : Fin m → ZMod 5) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((∑ p : Fin m, (ξ p * c p).val : ℕ) : ℂ) / 5)

lemma zmod5Char_zero {m : ℕ} (ξ : Fin m → ZMod 5) : zmod5Char ξ 0 = 1 := by
  simp [zmod5Char]

lemma zmod5Char_add {m : ℕ} (ξ c₁ c₂ : Fin m → ZMod 5) :
    zmod5Char ξ (c₁ + c₂) = zmod5Char ξ c₁ * zmod5Char ξ c₂ := by
  dsimp only [zmod5Char]
  rw [← Complex.exp_add]
  have hmod : (∑ p : Fin m, (ξ p * (c₁ p + c₂ p)).val) % 5 =
      ((∑ p : Fin m, (ξ p * c₁ p).val) + (∑ p : Fin m, (ξ p * c₂ p).val)) % 5 := by
    have h1 : (((∑ p : Fin m, (ξ p * (c₁ p + c₂ p)).val) : ℕ) : ZMod 5) =
        (((∑ p : Fin m, (ξ p * c₁ p).val) + (∑ p : Fin m, (ξ p * c₂ p).val) : ℕ) : ZMod 5) := by
      push_cast
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [mul_add]
    have h2 := congrArg ZMod.val h1
    rw [ZMod.val_natCast, ZMod.val_natCast] at h2
    exact h2
  set A := ∑ p : Fin m, (ξ p * (c₁ p + c₂ p)).val
  set B := (∑ p : Fin m, (ξ p * c₁ p).val) + (∑ p : Fin m, (ξ p * c₂ p).val)
  have hdiff : ((A : ℂ) - (B : ℂ)) / 5 = ((A / 5 : ℤ) - (B / 5 : ℤ) : ℤ) := by
    have hA : (A : ℤ) = 5 * (A / 5 : ℤ) + (A % 5 : ℤ) := by omega
    have hB : (B : ℤ) = 5 * (B / 5 : ℤ) + (B % 5 : ℤ) := by omega
    have hAB : (A : ℤ) - (B : ℤ) = 5 * ((A / 5 : ℤ) - (B / 5 : ℤ)) := by omega
    have hABc : (A : ℂ) - (B : ℂ) = 5 * (((A / 5 : ℤ) - (B / 5 : ℤ) : ℤ) : ℂ) := by
      exact_mod_cast hAB
    rw [hABc]; ring
  have hexp : 2 * ↑Real.pi * Complex.I * (A : ℂ) / 5 =
      (2 * ↑Real.pi * Complex.I * (∑ p : Fin m, (ξ p * c₁ p).val : ℕ) / 5 +
        2 * ↑Real.pi * Complex.I * (∑ p : Fin m, (ξ p * c₂ p).val : ℕ) / 5) +
      (((A / 5 : ℤ) - (B / 5 : ℤ) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    have hBc : (B : ℂ) = (∑ p : Fin m, (ξ p * c₁ p).val : ℕ) + (∑ p : Fin m, (ξ p * c₂ p).val : ℕ) := by
      dsimp only [B]; push_cast; rfl
    have h1 : (A : ℂ) = (B : ℂ) + 5 * (((A / 5 : ℤ) - (B / 5 : ℤ) : ℤ) : ℂ) := by
      linear_combination 5 * hdiff
    rw [h1, hBc]; ring
  change Complex.exp (2 * ↑Real.pi * Complex.I * (A : ℂ) / 5) = _
  rw [hexp, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma zmod5Char_neg {m : ℕ} (ξ c : Fin m → ZMod 5) :
    zmod5Char ξ (-c) = star (zmod5Char ξ c) := by
  have h1 : zmod5Char ξ c * zmod5Char ξ (-c) = 1 := by
    rw [← zmod5Char_add, add_neg_cancel, zmod5Char_zero]
  have hnorm : ‖zmod5Char ξ c‖ = 1 := by
    dsimp only [zmod5Char]
    have harg : 2 * ↑Real.pi * Complex.I * ((∑ p : Fin m, (ξ p * c p).val : ℕ) : ℂ) / 5 =
        ((2 * Real.pi * ((∑ p : Fin m, (ξ p * c p).val : ℕ) : ℝ) / 5 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.norm_exp_ofReal_mul_I]
  have hstar : star (zmod5Char ξ c) * zmod5Char ξ c = 1 := by
    rw [Complex.star_def, Complex.conj_mul', hnorm, Complex.ofReal_one, one_pow]
  calc zmod5Char ξ (-c) = (star (zmod5Char ξ c) * zmod5Char ξ c) * zmod5Char ξ (-c) := by rw [hstar, one_mul]
    _ = star (zmod5Char ξ c) * (zmod5Char ξ c * zmod5Char ξ (-c)) := by ring
    _ = star (zmod5Char ξ c) := by rw [h1, mul_one]

lemma zmod5Char_sum_eq {m : ℕ} (c : Fin m → ZMod 5) :
    ∑ ξ : Fin m → ZMod 5, zmod5Char ξ c = if c = 0 then ((5 ^ m : ℕ) : ℂ) else 0 := by
  split_ifs with hc
  · subst hc; simp [zmod5Char_zero, ZMod.card]
  · obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Fin m, c p₀ ≠ 0 := by
      by_contra h; push Not at h; exact hc (funext h)
    let δ : Fin m → ZMod 5 := Pi.single p₀ (1 : ZMod 5)
    have hchar_ne : zmod5Char δ c ≠ 1 := by
      dsimp only [zmod5Char, δ]
      have hsum : ∑ p : Fin m, ((Pi.single p₀ (1 : ZMod 5) : Fin m → ZMod 5) p * c p).val = (c p₀).val := by
        rw [Finset.sum_eq_single p₀]
        · simp
        · intro p _ hp; simp [Pi.single_eq_of_ne hp]
        · intro h; exact absurd (Finset.mem_univ p₀) h
      rw [hsum]
      intro heq
      rw [Complex.exp_eq_one_iff] at heq
      obtain ⟨n, hn⟩ := heq
      have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hval : ((c p₀).val : ℂ) / 5 = (n : ℂ) := by
        apply mul_left_cancel₀ hpi
        have h1 : 2 * ↑Real.pi * Complex.I * (((c p₀).val : ℂ) / 5) =
            2 * ↑Real.pi * Complex.I * ((c p₀).val : ℂ) / 5 := by ring
        rw [h1, hn]; ring
      have hval_int : ((c p₀).val : ℤ) = 5 * n := by
        have h1 : ((c p₀).val : ℂ) = 5 * (n : ℂ) := by linear_combination 5 * hval
        exact_mod_cast h1
      have hlt : (c p₀).val < 5 := ZMod.val_lt (c p₀)
      have hpos : 0 < (c p₀).val := Nat.pos_of_ne_zero (fun h0 => hp₀ ((ZMod.val_eq_zero _).mp h0))
      omega
    have hshift : ∑ ξ : Fin m → ZMod 5, zmod5Char ξ c =
        zmod5Char δ c * ∑ ξ : Fin m → ZMod 5, zmod5Char ξ c := by
      rw [Finset.mul_sum]
      have hterm : ∀ ξ : Fin m → ZMod 5, zmod5Char δ c * zmod5Char ξ c = zmod5Char (δ + ξ) c := by
        intro ξ
        have hsym : ∀ a b : Fin m → ZMod 5, zmod5Char a b = zmod5Char b a := fun a b => by
          dsimp only [zmod5Char]
          have hs : ∑ p : Fin m, (a p * b p).val = ∑ p : Fin m, (b p * a p).val :=
            Finset.sum_congr rfl fun p _ => by rw [mul_comm]
          rw [hs]
        rw [hsym δ c, hsym ξ c, ← zmod5Char_add, hsym]
      simp_rw [hterm]
      exact (Fintype.sum_equiv (Equiv.addLeft δ) _ _ fun _ => rfl).symm
    have hmul0 : (1 - zmod5Char δ c) * ∑ ξ : Fin m → ZMod 5, zmod5Char ξ c = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hchar_ne.symm)

/-- Finite 5-group nilpotency-class-2 orthogonality: if `X` and `Y` are elementary abelian 5-groups
generated by `k`-tuples `a` and `b` whose mutual commutators `⁅a i, b j⁆` commute with all of
`X ⊔ Y`, then `X` and `Y` are `1 / √5`-orthogonal. -/
lemma nilp2_five_group_epsOrth {Γ : Type} [Group Γ] {k : ℕ}
    (a b : Fin k → Γ)
    (ha_comm : ∀ i j, Commute (a i) (a j)) (ha5 : ∀ i, a i ^ 5 = 1)
    (hb_comm : ∀ i j, Commute (b i) (b j)) (hb5 : ∀ i, b i ^ 5 = 1)
    (hcent_a : ∀ i j l, Commute ⁅a i, b j⁆ (a l))
    (hcent_b : ∀ i j l, Commute ⁅a i, b j⁆ (b l)) :
    SubgroupEpsOrth (Subgroup.closure (Set.range a)) (Subgroup.closure (Set.range b))
      (1 / Real.sqrt 5) := by
  classical
  set X := Subgroup.closure (Set.range a)
  set Y := Subgroup.closure (Set.range b)
  set J := X ⊔ Y
  let aJ : Fin k → J := fun i => ⟨a i, (le_sup_left : X ≤ X ⊔ Y) (Subgroup.subset_closure ⟨i, rfl⟩)⟩
  let bJ : Fin k → J := fun j => ⟨b j, (le_sup_right : Y ≤ X ⊔ Y) (Subgroup.subset_closure ⟨j, rfl⟩)⟩
  have haJ_comm : ∀ i j, Commute (aJ i) (aJ j) := fun i j => Subtype.ext (ha_comm i j)
  have haJ5 : ∀ i, aJ i ^ 5 = 1 := fun i => Subtype.ext (ha5 i)
  have hbJ_comm : ∀ i j, Commute (bJ i) (bJ j) := fun i j => Subtype.ext (hb_comm i j)
  have hbJ5 : ∀ i, bJ i ^ 5 = 1 := fun i => Subtype.ext (hb5 i)
  have hcentJ : ∀ i j (g : J), Commute ⁅aJ i, bJ j⁆ g := by
    intro i j ⟨g, hg⟩
    have hg' : g ∈ Subgroup.closure (Set.range a ∪ Set.range b) := by
      rwa [Subgroup.closure_union]
    apply Subtype.ext
    change Commute ⁅a i, b j⁆ g
    clear hg
    induction hg' using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact hcent_a i j l
      · exact hcent_b i j l
    | one => exact Commute.one_right _
    | mul x y _ _ hx hy => exact hx.mul_right hy
    | inv x _ hx => exact hx.inv_right
  -- Pairwise commuting order-dividing-5 commutators `z : Fin (k * k) → J`
  let eProd : Fin k × Fin k ≃ Fin (k * k) := finProdFinEquiv
  let zJ : Fin (k * k) → J := fun p => ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆
  have hzJ_cent : ∀ p (g : J), Commute (zJ p) g := fun p g => hcentJ _ _ g
  have hzJ_comm : ∀ p q, Commute (zJ p) (zJ q) := fun p q => hzJ_cent p (zJ q)
  have hzJ5 : ∀ p, zJ p ^ 5 = 1 := by
    intro p
    dsimp only [zJ]
    rw [← commutator_pow_left_of_central (hcentJ _ _ _), haJ5, commutatorElement_one_left]
  let φX : Multiplicative (Fin k → ZMod 5) →* J := zmod5Hom aJ haJ_comm haJ5
  let φY : Multiplicative (Fin k → ZMod 5) →* J := zmod5Hom bJ hbJ_comm hbJ5
  let φZ : Multiplicative (Fin (k * k) → ZMod 5) →* J := zmod5Hom zJ hzJ_comm hzJ5
  have hφZ_cent : ∀ c (g : J), Commute (φZ c) g := fun c g =>
    commute_finProd_left _ g fun p => (hzJ_cent p g).pow_left _
  -- Explicit formula: `⁅φX f, φY g⁆ = φZ (fun p => f (eProd.symm p).1 * g (eProd.symm p).2)`
  have hcomm_list_right : ∀ (x : J) (l : List (Fin k)) (e : Fin k → ℕ),
      (∀ j ∈ l, ∀ h : J, Commute ⁅x, bJ j⁆ h) →
      ⁅x, (l.map fun j => bJ j ^ e j).prod⁆ = (l.map fun j => ⁅x, bJ j⁆ ^ e j).prod := by
    intro x l e hc
    induction l with
    | nil => simp [commutatorElement_def]
    | cons j ls ih =>
      simp only [List.map_cons, List.prod_cons]
      have hcs : ∀ l ∈ ls, ∀ h : J, Commute ⁅x, bJ l⁆ h :=
        fun l hl h => hc l (List.mem_cons_of_mem j hl) h
      have ih' := ih hcs
      have hc_rest : Commute ⁅x, (ls.map fun l => bJ l ^ e l).prod⁆ (bJ j ^ e j) := by
        rw [ih']
        exact Commute.list_prod_left _ _ fun _ hy => by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
          exact (hcs l hl _).pow_left _
      rw [commutator_mul_right_of_central hc_rest, ih',
        commutator_pow_right_of_central (hc j List.mem_cons_self _)]
  have hcomm_list_left : ∀ (l : List (Fin k)) (e : Fin k → ℕ) (y : J),
      (∀ i ∈ l, ∀ h : J, Commute ⁅aJ i, y⁆ h) →
      ⁅(l.map fun i => aJ i ^ e i).prod, y⁆ = (l.map fun i => ⁅aJ i, y⁆ ^ e i).prod := by
    intro l e y hc
    induction l with
    | nil => simp [commutatorElement_def]
    | cons i ls ih =>
      simp only [List.map_cons, List.prod_cons]
      have hcs : ∀ l ∈ ls, ∀ h : J, Commute ⁅aJ l, y⁆ h :=
        fun l hl h => hc l (List.mem_cons_of_mem i hl) h
      have ih' := ih hcs
      have hc_rest : Commute ⁅(ls.map fun l => aJ l ^ e l).prod, y⁆ (aJ i ^ e i) := by
        rw [ih']
        exact Commute.list_prod_left _ _ fun _ hy => by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
          exact (hcs l hl _).pow_left _
      rw [commutator_mul_left_of_central hc_rest, ih',
        commutator_pow_left_of_central (hc i List.mem_cons_self _)]
      have hc_swap : Commute (ls.map fun l => ⁅aJ l, y⁆ ^ e l).prod (⁅aJ i, y⁆ ^ e i) :=
        Commute.list_prod_left _ _ fun _ hy => by
          obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hy
          exact (hcs l hl _).pow_left _
      exact hc_swap.eq
  have hcomm_formula : ∀ (f g : Fin k → ZMod 5),
      ⁅φX (Multiplicative.ofAdd f), φY (Multiplicative.ofAdd g)⁆ =
        φZ (Multiplicative.ofAdd (fun p => f (eProd.symm p).1 * g (eProd.symm p).2)) := by
    intro f g
    change ⁅finProd (fun i : Fin k => aJ i ^ (f i).val), finProd (fun j : Fin k => bJ j ^ (g j).val)⁆ =
      finProd (fun p : Fin (k * k) => zJ p ^ (f (eProd.symm p).1 * g (eProd.symm p).2).val)
    have hc_a : ∀ i ∈ List.finRange k, ∀ h : J,
        Commute ⁅aJ i, finProd (fun j : Fin k => bJ j ^ (g j).val)⁆ h := by
      intro i _ h
      rw [finProd, hcomm_list_right (aJ i) (List.finRange k) (fun j => (g j).val) (fun j _ h' => hcentJ i j h')]
      exact Commute.list_prod_left _ _ fun _ hy => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hy
        exact (hcentJ i j h).pow_left _
    rw [finProd, hcomm_list_left (List.finRange k) (fun i => (f i).val) _ hc_a]
    have hstep : ∀ i : Fin k, ⁅aJ i, finProd (fun j : Fin k => bJ j ^ (g j).val)⁆ ^ (f i).val =
        finProd (fun j : Fin k => ⁅aJ i, bJ j⁆ ^ ((f i).val * (g j).val)) := by
      intro i
      rw [finProd, hcomm_list_right (aJ i) (List.finRange k) (fun j => (g j).val) (fun j _ h' => hcentJ i j h')]
      change finProd (fun j : Fin k => ⁅aJ i, bJ j⁆ ^ (g j).val) ^ (f i).val = _
      rw [finProd_pow _ (fun j₁ j₂ => ((hcentJ i j₁ _).pow_left _))]
      exact finProd_congr fun j => by rw [← pow_mul, mul_comm]
    -- Flatten `finProd_i (finProd_j ...)` into `finProd_p` via `finProd_equiv`!
    have hflat : ((List.finRange k).map fun i => ⁅aJ i, finProd (fun j : Fin k => bJ j ^ (g j).val)⁆ ^ (f i).val).prod =
        finProd (fun p : Fin (k * k) => ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ ((f (eProd.symm p).1).val * (g (eProd.symm p).2).val)) := by
      -- Prove via induction on `Fin k` or direct `List.prod` permutation!
      have hprod_flatMap : ∀ (l : List (Fin k)) (G : Fin k → List J),
          (l.flatMap G).prod = (l.map fun i => (G i).prod).prod := by
        intro l G; induction l with
        | nil => simp
        | cons x xs ih => simp [List.flatMap_cons, List.prod_append, ih]
      have h1 : ((List.finRange k).map fun i => ⁅aJ i, finProd (fun j : Fin k => bJ j ^ (g j).val)⁆ ^ (f i).val).prod =
          ((List.finRange k).flatMap fun i => (List.finRange k).map fun j =>
            ⁅aJ i, bJ j⁆ ^ ((f i).val * (g j).val)).prod := by
        rw [hprod_flatMap]
        congr 1
        exact List.map_congr_left fun i _ => hstep i
      rw [h1]
      have hperm : ((List.finRange k).flatMap fun i => (List.finRange k).map fun j =>
          ⁅aJ i, bJ j⁆ ^ ((f i).val * (g j).val)).Perm
          ((List.finRange (k * k)).map fun p =>
            ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ ((f (eProd.symm p).1).val * (g (eProd.symm p).2).val)) := by
        let F : Fin k × Fin k → J := fun q => ⁅aJ q.1, bJ q.2⁆ ^ ((f q.1).val * (g q.2).val)
        have hlhs : ((List.finRange k).flatMap fun i => (List.finRange k).map fun j => F (i, j)) =
            ((List.finRange k).product (List.finRange k)).map F := by
          simp [List.product, List.map_flatMap, Function.comp_def]
        have hrhs : ((List.finRange (k * k)).map fun p => F (eProd.symm p)) =
            ((List.finRange (k * k)).map eProd.symm).map F := by
          simp [List.map_map, Function.comp_def]
        rw [hlhs, hrhs]
        apply List.Perm.map
        change (List.finRange k ×ˢ List.finRange k).Perm _
        rw [List.perm_ext_iff_of_nodup
          ((List.nodup_finRange k).product (List.nodup_finRange k))
          ((List.nodup_finRange (k * k)).map eProd.symm.injective)]
        intro q
        simp only [List.mem_map, List.mem_finRange, true_and]
        exact ⟨fun _ => ⟨eProd q, eProd.symm_apply_apply q⟩,
          fun _ => List.mem_product.mpr ⟨List.mem_finRange _, List.mem_finRange _⟩⟩
      have hprod_perm : ∀ {l₁ l₂ : List J}, l₁.Perm l₂ → (∀ x ∈ l₂, ∀ y ∈ l₂, Commute x y) →
          l₁.prod = l₂.prod := by
        intro l₁ l₂ hp hc
        induction hp with
        | nil => rfl
        | cons x hp ih =>
          simp only [List.prod_cons]
          rw [ih fun u hu v hv => hc u (List.mem_cons_of_mem x hu) v (List.mem_cons_of_mem x hv)]
        | swap x y l =>
          simp only [List.prod_cons, ← mul_assoc]
          congr 1
          exact (hc y (List.mem_cons_of_mem x List.mem_cons_self) x List.mem_cons_self).eq
        | trans hp₁ hp₂ ih₁ ih₂ =>
          exact (ih₁ fun u hu v hv => hc u (hp₂.subset hu) v (hp₂.subset hv)).trans (ih₂ hc)
      exact hprod_perm hperm fun _ hx _ hy => by
        obtain ⟨p, _, rfl⟩ := List.mem_map.mp hx
        exact (hcentJ _ _ _).pow_left _
    rw [hflat]
    refine finProd_congr fun p => ?_
    dsimp only [zJ]
    rw [ZMod.val_mul]
    set a := (f (eProd.symm p).1).val * (g (eProd.symm p).2).val
    have hdiv := Nat.div_add_mod a 5
    have h5ij : ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ 5 = 1 := by
      rw [← commutator_pow_left_of_central (hcentJ _ _ _), haJ5, commutatorElement_one_left]
    calc ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ a
        = ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ (5 * (a / 5) + a % 5) := by rw [hdiv]
      _ = (⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ 5) ^ (a / 5) *
          ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ (a % 5) := by rw [pow_add, pow_mul]
      _ = ⁅aJ (eProd.symm p).1, bJ (eProd.symm p).2⁆ ^ (a % 5) := by rw [h5ij, one_pow, one_mul]
  intro W _ _ _ σ htriv
  set X' := X.comap J.subtype
  set Y' := Y.comap J.subtype
  have hφX_range : φX.range = X' := by
    rw [zmod5Hom_range]
    apply le_antisymm
    · rw [Subgroup.closure_le]; rintro _ ⟨i, rfl⟩; exact Subgroup.subset_closure ⟨i, rfl⟩
    · have hsub : ∀ x, x ∈ X → ∀ hxJ : x ∈ J, (⟨x, hxJ⟩ : J) ∈ Subgroup.closure (Set.range aJ) := by
        intro x hxX
        induction hxX using Subgroup.closure_induction with
        | mem u hu =>
          intro hxJ; obtain ⟨i, rfl⟩ := hu
          exact Subgroup.subset_closure ⟨i, rfl⟩
        | one => intro _; exact Subgroup.one_mem _
        | mul u v hu hv ihu ihv =>
          intro _; exact Subgroup.mul_mem _ (ihu ((le_sup_left : X ≤ J) hu)) (ihv ((le_sup_left : X ≤ J) hv))
        | inv u hu ihu =>
          intro _; exact Subgroup.inv_mem _ (ihu ((le_sup_left : X ≤ J) hu))
      rintro ⟨x, hxJ⟩ hxX; exact hsub x hxX hxJ
  have hφY_range : φY.range = Y' := by
    rw [zmod5Hom_range]
    apply le_antisymm
    · rw [Subgroup.closure_le]; rintro _ ⟨j, rfl⟩; exact Subgroup.subset_closure ⟨j, rfl⟩
    · have hsub : ∀ y, y ∈ Y → ∀ hyJ : y ∈ J, (⟨y, hyJ⟩ : J) ∈ Subgroup.closure (Set.range bJ) := by
        intro y hyY
        induction hyY using Subgroup.closure_induction with
        | mem u hu =>
          intro hyJ; obtain ⟨j, rfl⟩ := hu
          exact Subgroup.subset_closure ⟨j, rfl⟩
        | one => intro _; exact Subgroup.one_mem _
        | mul u v hu hv ihu ihv =>
          intro _; exact Subgroup.mul_mem _ (ihu ((le_sup_right : Y ≤ J) hu)) (ihv ((le_sup_right : Y ≤ J) hv))
        | inv u hu ihu =>
          intro _; exact Subgroup.inv_mem _ (ihu ((le_sup_right : Y ≤ J) hu))
      rintro ⟨y, hyJ⟩ hyY; exact hsub y hyY hyJ
  -- Apply `epsOrth_symm` + `epsOrth_iff_proj_le`: show `∀ u ∈ W^{Y'}, ‖(W^{X'}).starProjection u‖ ≤ (1 / √5) * ‖u‖`
  apply epsOrth_symm
  rw [epsOrth_iff_proj_le (by positivity)]
  intro u huY
  -- Explicit formula for `PX w := (5^k)⁻¹ • ∑ f, σ (φX f) w`
  let A := Fin k → ZMod 5
  let B := Fin (k * k) → ZMod 5
  let PX : W → W := fun w => ((5 ^ k : ℕ) : ℂ)⁻¹ • ∑ f : A, σ (φX (Multiplicative.ofAdd f)) w
  have h5k0 : ((5 ^ k : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  have hPX_eq : ∀ w : W, (invSubspace σ X').starProjection w = PX w := by
    intro w
    refine (invSubspace σ X').eq_starProjection_of_mem_orthogonal ?_ ?_
    · intro x hx
      rw [← hφX_range] at hx
      obtain ⟨f₀, rfl⟩ := hx
      dsimp only [PX]
      rw [map_smul, map_sum]
      congr 1
      have hterm : ∀ f : A, σ (φX f₀) (σ (φX (Multiplicative.ofAdd f)) w) =
          σ (φX (Multiplicative.ofAdd (Multiplicative.toAdd f₀ + f))) w := fun f => by
        rw [← rep_mul, ← map_mul]; rfl
      simp_rw [hterm]
      exact Fintype.sum_equiv (Equiv.addLeft (Multiplicative.toAdd f₀)) _ _ fun _ => rfl
    · rw [Submodule.mem_orthogonal']
      intro x hx
      rw [inner_sub_left, sub_eq_zero]
      dsimp only [PX]
      rw [inner_smul_left, sum_inner]
      have hterm : ∀ f : A, ⟪σ (φX (Multiplicative.ofAdd f)) w, x⟫_ℂ = ⟪w, x⟫_ℂ := fun f => by
        have hx' : σ (φX (Multiplicative.ofAdd (-f))) x = x :=
          hx _ (hφX_range ▸ ⟨Multiplicative.ofAdd (-f), rfl⟩)
        have h1 := (σ (φX (Multiplicative.ofAdd (-f)))).inner_map_map (σ (φX (Multiplicative.ofAdd f)) w) x
        rw [hx', ← rep_mul, ← map_mul] at h1
        have h0 : Multiplicative.ofAdd (-f) * Multiplicative.ofAdd f = 1 := by
          change Multiplicative.ofAdd (-f + f) = Multiplicative.ofAdd 0
          rw [neg_add_cancel]
        rw [h0, map_one, rep_one] at h1
        exact h1.symm
      simp_rw [hterm, Finset.sum_const, Finset.card_univ]
      have hcardA : Fintype.card A = 5 ^ k := by dsimp only [A]; simp [ZMod.card]
      rw [hcardA, nsmul_eq_mul]
      have hstar : (starRingEnd ℂ) (((5 ^ k : ℕ) : ℂ)⁻¹) = ((5 ^ k : ℕ) : ℂ)⁻¹ := by
        rw [map_inv₀, map_natCast]
      rw [hstar, ← mul_assoc, inv_mul_cancel₀ h5k0, one_mul]
  -- Fourier projections `P ξ w := (5^(k*k))⁻¹ • ∑ c : B, star (zmod5Char ξ c) • σ (φZ c) w`
  let P : B → W → W := fun ξ w =>
    ((5 ^ (k * k) : ℕ) : ℂ)⁻¹ • ∑ c : B, star (zmod5Char ξ c) • σ (φZ (Multiplicative.ofAdd c)) w
  have h5kk0 : ((5 ^ (k * k) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by positivity)
  have hP_sum : ∀ w : W, ∑ ξ : B, P ξ w = w := by
    intro w
    dsimp only [P]
    rw [← Finset.smul_sum, Finset.sum_comm]
    have hterm : ∀ c : B, ∑ ξ : B, star (zmod5Char ξ c) • σ (φZ (Multiplicative.ofAdd c)) w =
        (if c = 0 then ((5 ^ (k * k) : ℕ) : ℂ) else 0) • σ (φZ (Multiplicative.ofAdd c)) w := by
      intro c
      rw [← Finset.sum_smul]
      congr 1
      simp_rw [← zmod5Char_neg]
      rw [zmod5Char_sum_eq (-c)]
      simp only [neg_eq_zero]
    simp_rw [hterm]
    rw [Finset.sum_eq_single (0 : B)]
    · simp [smul_smul]
    · intro c _ hc0; simp [hc0]
    · intro h; exact absurd (Finset.mem_univ (0 : B)) h
  have hP_eig : ∀ (ξ c : B) (w : W), σ (φZ (Multiplicative.ofAdd c)) (P ξ w) = zmod5Char ξ c • P ξ w := by
    intro ξ c w
    dsimp only [P]
    rw [map_smul, map_sum, smul_comm]
    congr 1
    rw [Finset.smul_sum]
    have hterm : ∀ c' : B, σ (φZ (Multiplicative.ofAdd c)) (star (zmod5Char ξ c') • σ (φZ (Multiplicative.ofAdd c')) w) =
        star (zmod5Char ξ c') • σ (φZ (Multiplicative.ofAdd (c + c'))) w := fun c' => by
      rw [map_smul, ← rep_mul, ← map_mul]; rfl
    simp_rw [hterm]
    rw [Fintype.sum_equiv (Equiv.addLeft c) _
      (fun c' => star (zmod5Char ξ (-c + c')) • σ (φZ (Multiplicative.ofAdd c')) w)
      (fun c' => by
        have hcc : -c + (c + c') = c' := by dsimp only [B]; abel
        simp [hcc])]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [smul_smul]
    congr 1
    rw [← zmod5Char_neg, neg_add, neg_neg, zmod5Char_add, zmod5Char_neg]
  have hP_comm : ∀ (ξ : B) (g : J) (w : W), σ g (P ξ w) = P ξ (σ g w) := by
    intro ξ g w
    dsimp only [P]
    rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, ← rep_mul, ← (hφZ_cent _ g).eq, rep_mul]
  have hP_smul : ∀ (ξ : B) (α : ℂ) (w : W), P ξ (α • w) = α • P ξ w := fun ξ α w => by
    dsimp only [P]
    simp_rw [map_smul, smul_comm _ α, ← Finset.smul_sum, smul_comm _ α]
  have hP_sum_lin : ∀ {ι : Type} (ξ : B) (s : Finset ι) (f : ι → W),
      P ξ (∑ i ∈ s, f i) = ∑ i ∈ s, P ξ (f i) := fun ξ s f => by
    dsimp only [P]
    simp_rw [map_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
  have hP_PX : ∀ (ξ : B) (w : W), PX (P ξ w) = P ξ (PX w) := fun ξ w => by
    dsimp only [PX]
    rw [hP_smul, hP_sum_lin]
    congr 1
    exact Finset.sum_congr rfl fun f _ => hP_comm ξ _ w
  have hP_orth : ∀ (ξ η : B) (w₁ w₂ : W), ξ ≠ η → ⟪P ξ w₁, P η w₂⟫_ℂ = 0 := by
    intro ξ η w₁ w₂ hne
    -- Since `zmod5Char ξ` and `zmod5Char η` differ at some `c₀ : B`, `⟪P ξ w₁, P η w₂⟫ = 0`
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Fin (k * k), ξ p₀ ≠ η p₀ := by
      by_contra h; push Not at h; exact hne (funext h)
    let c₀ : B := Pi.single p₀ (1 : ZMod 5)
    have hchi_ne : zmod5Char ξ c₀ ≠ zmod5Char η c₀ := by
      intro heq
      have hdiv : zmod5Char (ξ - η) c₀ = 1 := by
        have h1 : zmod5Char (ξ - η) c₀ = zmod5Char ξ c₀ * star (zmod5Char η c₀) := by
          have hsym : ∀ x y : B, zmod5Char x y = zmod5Char y x := fun x y => by
            dsimp only [zmod5Char]
            have hs : ∑ p : Fin (k * k), (x p * y p).val = ∑ p : Fin (k * k), (y p * x p).val :=
              Finset.sum_congr rfl fun p _ => by rw [mul_comm]
            rw [hs]
          rw [hsym, sub_eq_add_neg, zmod5Char_add, zmod5Char_neg, hsym, hsym c₀ η]
        rw [h1, heq]
        have hnorm : ‖zmod5Char η c₀‖ = 1 := by
          dsimp only [zmod5Char]
          have harg : 2 * ↑Real.pi * Complex.I * ((∑ p : Fin (k * k), (η p * c₀ p).val : ℕ) : ℂ) / 5 =
              ((2 * Real.pi * ((∑ p : Fin (k * k), (η p * c₀ p).val : ℕ) : ℝ) / 5 : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [harg, Complex.norm_exp_ofReal_mul_I]
        rw [mul_comm, Complex.star_def, Complex.conj_mul', hnorm, Complex.ofReal_one, one_pow]
      dsimp only [zmod5Char, c₀] at hdiv
      have hsum : ∑ p : Fin (k * k), ((ξ - η) p * (Pi.single p₀ (1 : ZMod 5) : B) p).val = (ξ p₀ - η p₀).val := by
        rw [Finset.sum_eq_single p₀]
        · simp; rfl
        · intro p _ hp; simp [Pi.single_eq_of_ne hp]
        · intro h; exact absurd (Finset.mem_univ p₀) h
      rw [hsum, Complex.exp_eq_one_iff] at hdiv
      obtain ⟨n, hn⟩ := hdiv
      have hpi : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hval : ((ξ p₀ - η p₀).val : ℂ) / 5 = (n : ℂ) := by
        apply mul_left_cancel₀ hpi
        have h1 : 2 * ↑Real.pi * Complex.I * (((ξ p₀ - η p₀).val : ℂ) / 5) =
            2 * ↑Real.pi * Complex.I * ((ξ p₀ - η p₀).val : ℂ) / 5 := by ring
        rw [h1, hn]; ring
      have hval_int : ((ξ p₀ - η p₀).val : ℤ) = 5 * n := by
        have h1 : ((ξ p₀ - η p₀).val : ℂ) = 5 * (n : ℂ) := by linear_combination 5 * hval
        exact_mod_cast h1
      have hlt : (ξ p₀ - η p₀).val < 5 := ZMod.val_lt _
      have hpos : 0 < (ξ p₀ - η p₀).val :=
        Nat.pos_of_ne_zero (fun h0 => sub_ne_zero.mpr hp₀ ((ZMod.val_eq_zero _).mp h0))
      omega
    have h1 := (σ (φZ (Multiplicative.ofAdd c₀))).inner_map_map (P ξ w₁) (P η w₂)
    rw [hP_eig, hP_eig, inner_smul_left, inner_smul_right] at h1
    have hnorm : ‖zmod5Char ξ c₀‖ = 1 := by
      dsimp only [zmod5Char]
      have harg : 2 * ↑Real.pi * Complex.I * ((∑ p : Fin (k * k), (ξ p * c₀ p).val : ℕ) : ℂ) / 5 =
          ((2 * Real.pi * ((∑ p : Fin (k * k), (ξ p * c₀ p).val : ℕ) : ℝ) / 5 : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    have hmul_ne : star (zmod5Char ξ c₀) * zmod5Char η c₀ ≠ 1 := by
      intro hprod
      have hst : zmod5Char ξ c₀ * star (zmod5Char ξ c₀) = 1 := by
        rw [mul_comm, Complex.star_def, Complex.conj_mul', hnorm, Complex.ofReal_one, one_pow]
      have : zmod5Char η c₀ = zmod5Char ξ c₀ := by
        calc zmod5Char η c₀ = (zmod5Char ξ c₀ * star (zmod5Char ξ c₀)) * zmod5Char η c₀ := by rw [hst, one_mul]
          _ = zmod5Char ξ c₀ * (star (zmod5Char ξ c₀) * zmod5Char η c₀) := by ring
          _ = zmod5Char ξ c₀ := by rw [hprod, mul_one]
      exact hchi_ne this.symm
    have h2 : (1 - star (zmod5Char ξ c₀) * zmod5Char η c₀) * ⟪P ξ w₁, P η w₂⟫_ℂ = 0 := by
      have : star (zmod5Char ξ c₀) * zmod5Char η c₀ * ⟪P ξ w₁, P η w₂⟫_ℂ = ⟪P ξ w₁, P η w₂⟫_ℂ := by
        simpa [Complex.star_def, mul_assoc] using h1
      linear_combination -this
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hmul_ne.symm)
  have hnorm_decomp : ∀ w : W, ‖w‖ ^ 2 = ∑ ξ : B, ‖P ξ w‖ ^ 2 := by
    intro w
    have h1 : ((‖w‖ ^ 2 : ℝ) : ℂ) = ⟪∑ ξ : B, P ξ w, ∑ η : B, P η w⟫_ℂ := by
      rw [hP_sum, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
    rw [sum_inner] at h1
    have hterm : ∀ ξ : B, ⟪P ξ w, ∑ η : B, P η w⟫_ℂ = ((‖P ξ w‖ ^ 2 : ℝ) : ℂ) := by
      intro ξ
      rw [inner_sum, Finset.sum_eq_single ξ]
      · rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
      · intro η _ hηξ; exact hP_orth ξ η w w hηξ.symm
      · intro h; exact absurd (Finset.mem_univ ξ) h
    simp_rw [hterm] at h1
    rw [← Complex.ofReal_sum] at h1
    exact Complex.ofReal_injective h1
  -- Main componentwise bound: `‖PX (P ξ u)‖^2 ≤ (1/5) * ‖P ξ u‖^2` for every `ξ : B`!
  have hcomp : ∀ ξ : B, ‖PX (P ξ u)‖ ^ 2 ≤ (1 / 5 : ℝ) * ‖P ξ u‖ ^ 2 := by
    intro ξ
    set uξ := P ξ u
    have huξ_Y : uξ ∈ invSubspace σ Y' := fun y hy => by
      dsimp only [uξ]; rw [hP_comm, huY y hy]
    by_cases htriv_xi : ∀ f g : A, zmod5Char ξ (fun p => f (eProd.symm p).1 * g (eProd.symm p).2) = 1
    · -- Case 1: `[X', Y']` acts trivially on `uξ`, so `PX uξ ∈ W^{X'} ⊓ W^{Y'} = W^⊤ = ⊥`
      have hPX_X : PX uξ ∈ invSubspace σ X' := by
        rw [← hPX_eq]; exact Submodule.coe_mem _
      have hPX_Y : PX uξ ∈ invSubspace σ Y' := by
        intro y hy
        rw [← hφY_range] at hy
        obtain ⟨g, rfl⟩ := hy
        set g' := Multiplicative.toAdd g
        have hg_eq : g = Multiplicative.ofAdd g' := rfl
        rw [hg_eq]
        dsimp only [PX]
        rw [map_smul, map_sum]
        congr 1
        refine Finset.sum_congr rfl fun f _ => ?_
        have hrel : φY (Multiplicative.ofAdd g') * φX (Multiplicative.ofAdd f) =
            ⁅φX (Multiplicative.ofAdd f), φY (Multiplicative.ofAdd g')⁆⁻¹ *
              (φX (Multiplicative.ofAdd f) * φY (Multiplicative.ofAdd g')) := by
          simp only [commutatorElement_def]; group
        rw [← rep_mul, hrel, rep_mul, rep_mul]
        have hfixY : σ (φY (Multiplicative.ofAdd g')) uξ = uξ :=
          huξ_Y _ (hφY_range ▸ ⟨Multiplicative.ofAdd g', rfl⟩)
        rw [hfixY, hcomm_formula f g']
        have hinv : (φZ (Multiplicative.ofAdd (fun p => f (eProd.symm p).1 * g' (eProd.symm p).2)))⁻¹ =
            φZ (Multiplicative.ofAdd (-(fun p => f (eProd.symm p).1 * g' (eProd.symm p).2))) := by
          rw [← map_inv]; rfl
        rw [hinv]
        dsimp only [uξ]
        rw [hP_comm, hP_eig, zmod5Char_neg, htriv_xi f g', star_one, one_smul, ← hP_comm]
      have hPX_top : PX uξ ∈ invSubspace σ ⊤ := by
        have htop_XY : X' ⊔ Y' = ⊤ := by
          have hsub : ∀ x, x ∈ Subgroup.closure ((X : Set Γ) ∪ (Y : Set Γ)) →
              ∀ hxJ : x ∈ J, (⟨x, hxJ⟩ : J) ∈ X' ⊔ Y' := by
            intro x hx
            induction hx using Subgroup.closure_induction with
            | mem y hy =>
              intro hyJ
              rcases hy with hy | hy
              · exact Subgroup.mem_sup_left hy
              · exact Subgroup.mem_sup_right hy
            | one => intro _; exact Subgroup.one_mem _
            | mul x y hx hy ihx ihy =>
              intro _
              have hxJ : x ∈ J := by dsimp only [J]; rwa [Subgroup.sup_eq_closure]
              have hyJ : y ∈ J := by dsimp only [J]; rwa [Subgroup.sup_eq_closure]
              exact Subgroup.mul_mem _ (ihx hxJ) (ihy hyJ)
            | inv x hx ihx =>
              intro _
              have hxJ : x ∈ J := by dsimp only [J]; rwa [Subgroup.sup_eq_closure]
              exact Subgroup.inv_mem _ (ihx hxJ)
          rw [eq_top_iff]; rintro ⟨g, hg⟩ _
          exact hsub g (by dsimp only [J] at hg; rwa [Subgroup.sup_eq_closure] at hg) hg
        rw [← htop_XY, invSubspace_sup]
        exact ⟨hPX_X, hPX_Y⟩
      rw [htriv, Submodule.mem_bot] at hPX_top
      rw [hPX_top]; simp
    · -- Case 2: `K := {f : A | ∀ g : A, zmod5Char ξ (f ⊗ g) = 1}` is a proper subgroup of `A`
      push Not at htriv_xi
      obtain ⟨f₀, g₀, hne₀⟩ := htriv_xi
      let K : AddSubgroup A :=
        { carrier := {f : A | ∀ g : A, zmod5Char ξ (fun p => f (eProd.symm p).1 * g (eProd.symm p).2) = 1}
          zero_mem' := fun g => by
            have : (fun p => (0 : A) (eProd.symm p).1 * g (eProd.symm p).2) = 0 := by
              ext p; change (0 : ZMod 5) * g (eProd.symm p).2 = 0; ring
            rw [this, zmod5Char_zero]
          add_mem' := fun {f₁ f₂} hf₁ hf₂ g => by
            have : (fun p => (f₁ + f₂) (eProd.symm p).1 * g (eProd.symm p).2) =
                (fun p => f₁ (eProd.symm p).1 * g (eProd.symm p).2) +
                (fun p => f₂ (eProd.symm p).1 * g (eProd.symm p).2) := by
              ext p
              change (f₁ (eProd.symm p).1 + f₂ (eProd.symm p).1) * g (eProd.symm p).2 =
                f₁ (eProd.symm p).1 * g (eProd.symm p).2 + f₂ (eProd.symm p).1 * g (eProd.symm p).2
              ring
            rw [this, zmod5Char_add, hf₁ g, hf₂ g, mul_one]
          neg_mem' := fun {f} hf g => by
            have : (fun p => (-f) (eProd.symm p).1 * g (eProd.symm p).2) =
                -(fun p => f (eProd.symm p).1 * g (eProd.symm p).2) := by
              ext p
              change (-f (eProd.symm p).1) * g (eProd.symm p).2 = -(f (eProd.symm p).1 * g (eProd.symm p).2)
              ring
            rw [this, zmod5Char_neg, hf g, star_one] }
      have hK_lt : Fintype.card K < 5 ^ k := by
        have hcardA : Fintype.card A = 5 ^ k := by dsimp only [A]; simp [ZMod.card]
        rw [← hcardA]
        have hle : Fintype.card K ≤ Fintype.card A := Fintype.card_subtype_le _
        refine lt_of_le_of_ne hle fun heq => ?_
        have hall : ∀ f : A, f ∈ K := fun f => by
          have hset : (Finset.univ.filter (· ∈ K)) = Finset.univ := by
            apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
            rw [Finset.card_univ, ← heq, Fintype.card_subtype]
          have : f ∈ Finset.univ.filter (· ∈ K) := by rw [hset]; exact Finset.mem_univ f
          exact (Finset.mem_filter.mp this).2
        exact hne₀ (hall f₀ g₀)
      have hK_dvd : Fintype.card K ∣ 5 ^ k := by
        have hcardA : Fintype.card A = 5 ^ k := by dsimp only [A]; simp [ZMod.card]
        rw [← hcardA, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact Subgroup.card_subgroup_dvd_card K.toSubgroup
      have h5K : 5 * Fintype.card K ≤ 5 ^ k := by
        obtain ⟨i, hik, hi⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hK_dvd
        rw [hi] at hK_lt ⊢
        have hilt : i < k := by
          by_contra hge
          have : i = k := by omega
          subst this; exact lt_irrefl _ hK_lt
        calc 5 * 5 ^ i = 5 ^ (i + 1) := by rw [pow_succ']
          _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hilt
      -- Orthogonality: for `f ∉ K`, `⟪σ (φX f) uξ, uξ⟫ = 0`!
      have hterm_zero : ∀ f : A, f ∉ K → ⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ = 0 := by
        intro f hfK
        have : ¬ ∀ g : A, zmod5Char ξ (fun p => f (eProd.symm p).1 * g (eProd.symm p).2) = 1 := hfK
        push Not at this
        obtain ⟨g, hg⟩ := this
        have hfixY : σ (φY (Multiplicative.ofAdd g)) uξ = uξ :=
          huξ_Y _ (hφY_range ▸ ⟨Multiplicative.ofAdd g, rfl⟩)
        have h1 := (σ (φY (Multiplicative.ofAdd g))).inner_map_map (σ (φX (Multiplicative.ofAdd f)) uξ) uξ
        rw [hfixY] at h1
        have hrel : φY (Multiplicative.ofAdd g) * φX (Multiplicative.ofAdd f) =
            ⁅φX (Multiplicative.ofAdd f), φY (Multiplicative.ofAdd g)⁆⁻¹ *
              (φX (Multiplicative.ofAdd f) * φY (Multiplicative.ofAdd g)) := by
          simp only [commutatorElement_def]; group
        have h2 : σ (φY (Multiplicative.ofAdd g)) (σ (φX (Multiplicative.ofAdd f)) uξ) =
            star (zmod5Char ξ (fun p => f (eProd.symm p).1 * g (eProd.symm p).2)) •
              σ (φX (Multiplicative.ofAdd f)) uξ := by
          rw [← rep_mul, hrel, rep_mul, rep_mul, hfixY, hcomm_formula f g]
          have hinv : (φZ (Multiplicative.ofAdd (fun p => f (eProd.symm p).1 * g (eProd.symm p).2)))⁻¹ =
              φZ (Multiplicative.ofAdd (-(fun p => f (eProd.symm p).1 * g (eProd.symm p).2))) := by
            rw [← map_inv]; rfl
          rw [hinv]
          dsimp only [uξ]
          rw [hP_comm, hP_eig, zmod5Char_neg, ← hP_comm]
        rw [h2, inner_smul_left, starRingEnd_apply, star_star] at h1
        have hmul0 : (1 - zmod5Char ξ (fun p => f (eProd.symm p).1 * g (eProd.symm p).2)) *
            ⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ = 0 := by
          linear_combination -h1
        exact (mul_eq_zero.mp hmul0).resolve_left (sub_ne_zero.mpr hg.symm)
      -- Now compute `‖PX uξ‖^2 = Re ⟪PX uξ, uξ⟫`
      have hPX_sq : ‖PX uξ‖ ^ 2 = RCLike.re ⟪PX uξ, uξ⟫_ℂ := by
        rw [← hPX_eq]
        set p := (invSubspace σ X').starProjection uξ
        have horth : ⟪p, uξ - p⟫_ℂ = 0 := by
          have := (invSubspace σ X').starProjection_inner_eq_zero uξ p (Submodule.coe_mem _)
          rw [← inner_conj_symm, this, map_zero]
        rw [inner_sub_right, sub_eq_zero] at horth
        rw [horth, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]
      rw [hPX_sq]
      dsimp only [PX]
      rw [inner_smul_left, sum_inner]
      have hstar : (starRingEnd ℂ) (((5 ^ k : ℕ) : ℂ)⁻¹) = ((((5 ^ k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
        rw [map_inv₀, map_natCast, Complex.ofReal_inv, Complex.ofReal_natCast]
      rw [hstar]
      change (((((5 ^ k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ f : A, ⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re ≤ _
      rw [Complex.re_ofReal_mul, Complex.re_sum]
      have hsum_K : ∑ f : A, (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re ≤
          (Fintype.card K : ℝ) * ‖uξ‖ ^ 2 := by
        have hsplit : ∑ f : A, (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re =
            ∑ f ∈ Finset.univ.filter (· ∈ K), (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ K)]
          have h0 : ∑ f ∈ Finset.univ.filter (fun f => ¬ f ∈ K),
              (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re = 0 :=
            Finset.sum_eq_zero fun f hf => by
              rw [hterm_zero f (Finset.mem_filter.mp hf).2, Complex.zero_re]
          rw [h0, add_zero]
        rw [hsplit]
        calc ∑ f ∈ Finset.univ.filter (· ∈ K), (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re
            ≤ ∑ _f ∈ Finset.univ.filter (· ∈ K), ‖uξ‖ ^ 2 := by
              refine Finset.sum_le_sum fun f _ => ?_
              calc (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re
                  ≤ ‖⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ‖ := Complex.re_le_norm _
                _ ≤ ‖σ (φX (Multiplicative.ofAdd f)) uξ‖ * ‖uξ‖ := norm_inner_le_norm _ _
                _ = ‖uξ‖ ^ 2 := by rw [(σ _).norm_map]; ring
          _ = (Fintype.card K : ℝ) * ‖uξ‖ ^ 2 := by
              rw [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
      have h5k_pos : (0 : ℝ) < ((5 ^ k : ℕ) : ℝ) := by positivity
      calc ((5 ^ k : ℕ) : ℝ)⁻¹ * ∑ f : A, (⟪σ (φX (Multiplicative.ofAdd f)) uξ, uξ⟫_ℂ).re
          ≤ ((5 ^ k : ℕ) : ℝ)⁻¹ * ((Fintype.card K : ℝ) * ‖uξ‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_K (by positivity)
        _ = ((Fintype.card K : ℝ) / ((5 ^ k : ℕ) : ℝ)) * ‖uξ‖ ^ 2 := by ring
        _ ≤ (1 / 5 : ℝ) * ‖uξ‖ ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            rw [div_le_div_iff₀ h5k_pos (by norm_num : (0 : ℝ) < 5)]
            have h5K' : 5 * (Fintype.card K : ℝ) ≤ ((5 ^ k : ℕ) : ℝ) := by exact_mod_cast h5K
            linarith
  -- Sum over all `ξ : B`!
  have hsq : ‖(invSubspace σ X').starProjection u‖ ^ 2 ≤ ((1 / Real.sqrt 5) * ‖u‖) ^ 2 := by
    rw [hPX_eq, hnorm_decomp (PX u), mul_pow, hnorm_decomp u, one_div, inv_pow,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ _ => ?_
    rw [← hP_PX]
    simpa [one_div] using hcomp ξ
  have hrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt

/-- Property (T) (explicit spectral gap) for the subgroup generated by `{x i j m | i ≠ j, m < k}`
under the finite-field relations (3.1)–(3.5) of Ershov–Jaikin-Zapirain (`k = 4` or `k = 7`). -/
lemma delta_spectralGap {G : Type} [Group G] [DecidableEq G]
    (x : Fin 3 → Fin 3 → Fin 7 → G)
    (hx_diag : ∀ i m, x i i m = 1)
    (hx5 : ∀ i j m, x i j m ^ 5 = 1)
    (hx_comm : ∀ i j k l m n, i ≠ l → j ≠ k → ⁅x i j m, x k l n⁆ = 1)
    (hx_stein : ∀ i j k m, i ≠ j → j ≠ k → i ≠ k → ⁅x i j m, x j k 0⁆ = x i k m)
    (hx_triple : ∀ i j k a b m n l, i ≠ j → j ≠ k → i ≠ k → i ≠ b → k ≠ a →
      ⁅⁅x i j m, x j k n⁆, x a b l⁆ = 1)
    {k : ℕ} (hk0 : 0 < k) (hk7 : k ≤ 7) :
    let S : Finset G :=
      (Finset.univ.filter fun p : Fin 3 × Fin 3 × Fin k => p.1 ≠ p.2.1).image
        (fun p => x p.1 p.2.1 ⟨p.2.2.val, lt_of_lt_of_le p.2.2.isLt hk7⟩)
    let Γ := Subgroup.closure (S : Set G)
    ∃ κ : ℝ, HasSpectralGap (S.attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : Γ)) κ := by
  intro S Γ
  let lift : Fin 3 → Fin 3 → Fin k → Γ := fun i j m =>
    if h : i ≠ j then
      ⟨x i j ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩,
        Subgroup.subset_closure (Finset.mem_image.mpr ⟨(i, j, m),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩)⟩
    else 1
  have hlift_val : ∀ i j m, (lift i j m).1 = x i j ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩ := by
    intro i j m; dsimp only [lift]
    split_ifs with h
    · rfl
    · push Not at h; subst h; exact (hx_diag i _).symm
  have hlift5 : ∀ i j m, lift i j m ^ 5 = 1 := fun i j m => by
    apply Subtype.ext; rw [Subgroup.coe_pow, Subgroup.coe_one, hlift_val]; exact hx5 _ _ _
  have hlift_comm : ∀ i j a b m n, i ≠ b → j ≠ a → Commute (lift i j m) (lift a b n) := by
    intro i j a b m n hib hja
    rw [commute_iff_eq]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hlift_val, hlift_val]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hx_comm i j a b _ _ hib hja)
  have hlift_cent : ∀ i j l a b m n r, i ≠ j → j ≠ l → i ≠ l → i ≠ b → l ≠ a →
      Commute ⁅lift i j m, lift j l n⁆ (lift a b r) := by
    intro i j l a b m n r hij hjl hil hib hla
    rw [commute_iff_eq]
    apply Subtype.ext
    have h1 : ((⁅lift i j m, lift j l n⁆ : Γ) : G) = ⁅x i j ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩,
        x j l ⟨n.val, lt_of_lt_of_le n.isLt hk7⟩⁆ := by
      simp [commutatorElement_def, hlift_val]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, h1, hlift_val]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hx_triple i j l a b _ _ _ hij hjl hil hib hla)
  let g1 : Fin k → Γ := fun m => lift 0 1 m
  let g2 : Fin k → Γ := fun m => lift 1 2 m
  let g3 : Fin k → Γ := fun m => lift 2 0 m
  let H₁ : Subgroup Γ := Subgroup.closure (Set.range g1)
  let H₂ : Subgroup Γ := Subgroup.closure (Set.range g2)
  let H₃ : Subgroup Γ := Subgroup.closure (Set.range g3)
  have hgen : H₁ ⊔ H₂ ⊔ H₃ = ⊤ := by
    have hmem : ∀ s (hs : s ∈ S), (⟨s, Subgroup.subset_closure hs⟩ : Γ) ∈ H₁ ⊔ H₂ ⊔ H₃ := by
      intro s hs
      obtain ⟨⟨i, j, m⟩, hflt, rfl⟩ := Finset.mem_image.mp hs
      have hij : i ≠ j := (Finset.mem_filter.mp hflt).2
      have heq : (⟨x i j ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩, Subgroup.subset_closure hs⟩ : Γ) = lift i j m := by
        apply Subtype.ext; exact (hlift_val i j m).symm
      rw [heq]
      let m0 : Fin k := ⟨0, hk0⟩
      fin_cases i <;> fin_cases j <;> dsimp only
      · exact absurd rfl hij
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨m, rfl⟩))
      · have hcomm_eq : lift 0 2 m = ⁅g1 m, g2 m0⁆ := by
          apply Subtype.ext
          simp only [commutatorElement_def, g1, g2, m0, Subgroup.coe_mul, Subgroup.coe_inv, hlift_val]
          exact (hx_stein 0 1 2 _ (by decide) (by decide) (by decide)).symm
        change lift 0 2 m ∈ _
        rw [hcomm_eq, commutatorElement_def]
        have h1 : g1 m ∈ H₁ ⊔ H₂ ⊔ H₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨m, rfl⟩))
        have h2 : g2 m0 ∈ H₁ ⊔ H₂ ⊔ H₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m0, rfl⟩))
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
      · have hcomm_eq : lift 1 0 m = ⁅g2 m, g3 m0⁆ := by
          apply Subtype.ext
          simp only [commutatorElement_def, g2, g3, m0, Subgroup.coe_mul, Subgroup.coe_inv, hlift_val]
          exact (hx_stein 1 2 0 _ (by decide) (by decide) (by decide)).symm
        change lift 1 0 m ∈ _
        rw [hcomm_eq, commutatorElement_def]
        have h1 : g2 m ∈ H₁ ⊔ H₂ ⊔ H₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m, rfl⟩))
        have h2 : g3 m0 ∈ H₁ ⊔ H₂ ⊔ H₃ := Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m0, rfl⟩)
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
      · exact absurd rfl hij
      · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m, rfl⟩))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m, rfl⟩)
      · have hcomm_eq : lift 2 1 m = ⁅g3 m, g1 m0⁆ := by
          apply Subtype.ext
          simp only [commutatorElement_def, g3, g1, m0, Subgroup.coe_mul, Subgroup.coe_inv, hlift_val]
          exact (hx_stein 2 0 1 _ (by decide) (by decide) (by decide)).symm
        change lift 2 1 m ∈ _
        rw [hcomm_eq, commutatorElement_def]
        have h1 : g3 m ∈ H₁ ⊔ H₂ ⊔ H₃ := Subgroup.mem_sup_right (Subgroup.subset_closure ⟨m, rfl⟩)
        have h2 : g1 m0 ∈ H₁ ⊔ H₂ ⊔ H₃ := Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨m0, rfl⟩))
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)
      · exact absurd rfl hij
    have hsub : ∀ z (hz : z ∈ Γ), (⟨z, hz⟩ : Γ) ∈ H₁ ⊔ H₂ ⊔ H₃ := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem y hy => exact hmem y hy
      | one => exact Subgroup.one_mem _
      | mul a b ha hb iha ihb => exact Subgroup.mul_mem _ iha ihb
      | inv a ha iha => exact Subgroup.inv_mem _ iha
    rw [eq_top_iff]; rintro ⟨z, hz⟩ _; exact hsub z hz
  have h12 : SubgroupEpsOrth H₁ H₂ (1 / Real.sqrt 5) :=
    nilp2_five_group_epsOrth g1 g2
      (fun m n => hlift_comm 0 1 0 1 m n (by decide) (by decide)) (fun m => hlift5 0 1 m)
      (fun m n => hlift_comm 1 2 1 2 m n (by decide) (by decide)) (fun m => hlift5 1 2 m)
      (fun m n l => hlift_cent 0 1 2 0 1 m n l (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun m n l => hlift_cent 0 1 2 1 2 m n l (by decide) (by decide) (by decide) (by decide) (by decide))
  have h23 : SubgroupEpsOrth H₂ H₃ (1 / Real.sqrt 5) :=
    nilp2_five_group_epsOrth g2 g3
      (fun m n => hlift_comm 1 2 1 2 m n (by decide) (by decide)) (fun m => hlift5 1 2 m)
      (fun m n => hlift_comm 2 0 2 0 m n (by decide) (by decide)) (fun m => hlift5 2 0 m)
      (fun m n l => hlift_cent 1 2 0 1 2 m n l (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun m n l => hlift_cent 1 2 0 2 0 m n l (by decide) (by decide) (by decide) (by decide) (by decide))
  have h31 : SubgroupEpsOrth H₃ H₁ (1 / Real.sqrt 5) :=
    nilp2_five_group_epsOrth g3 g1
      (fun m n => hlift_comm 2 0 2 0 m n (by decide) (by decide)) (fun m => hlift5 2 0 m)
      (fun m n => hlift_comm 0 1 0 1 m n (by decide) (by decide)) (fun m => hlift5 0 1 m)
      (fun m n l => hlift_cent 2 0 1 2 0 m n l (by decide) (by decide) (by decide) (by decide) (by decide))
      (fun m n l => hlift_cent 2 0 1 0 1 m n l (by decide) (by decide) (by decide) (by decide) (by decide))
  have h13 : SubgroupEpsOrth H₁ H₃ (1 / Real.sqrt 5) := subgroupEpsOrth_symm h31
  -- Individual spectral gaps on `H₁, H₂, H₃`
  let g1' : Fin k → H₁ := fun m => ⟨g1 m, Subgroup.subset_closure ⟨m, rfl⟩⟩
  let g2' : Fin k → H₂ := fun m => ⟨g2 m, Subgroup.subset_closure ⟨m, rfl⟩⟩
  let g3' : Fin k → H₃ := fun m => ⟨g3 m, Subgroup.subset_closure ⟨m, rfl⟩⟩
  have hgen_sub : ∀ (g : Fin k → Γ) (H : Subgroup Γ) (hH : H = Subgroup.closure (Set.range g)),
      Subgroup.closure (Set.range fun m => (⟨g m, hH ▸ Subgroup.subset_closure ⟨m, rfl⟩⟩ : H)) = ⊤ := by
    intro g H hH
    subst hH
    have hsub : ∀ z (hz : z ∈ Subgroup.closure (Set.range g)),
        (⟨z, hz⟩ : Subgroup.closure (Set.range g)) ∈
          Subgroup.closure (Set.range fun m => (⟨g m, Subgroup.subset_closure ⟨m, rfl⟩⟩ : Subgroup.closure (Set.range g))) := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨m, rfl⟩ := hy
        exact Subgroup.subset_closure ⟨m, rfl⟩
      | one => exact Subgroup.one_mem _
      | mul a b ha hb iha ihb => exact Subgroup.mul_mem _ iha ihb
      | inv a ha iha => exact Subgroup.inv_mem _ iha
    rw [eq_top_iff]; rintro ⟨z, hz⟩ _; exact hsub z hz
  have hH₁ := finite_abelian_five_group_gap g1'
    (fun m n => Subtype.ext (hlift_comm 0 1 0 1 m n (by decide) (by decide)))
    (fun m => Subtype.ext (hlift5 0 1 m)) (hgen_sub g1 H₁ rfl)
  have hH₂ := finite_abelian_five_group_gap g2'
    (fun m n => Subtype.ext (hlift_comm 1 2 1 2 m n (by decide) (by decide)))
    (fun m => Subtype.ext (hlift5 1 2 m)) (hgen_sub g2 H₂ rfl)
  have hH₃ := finite_abelian_five_group_gap g3'
    (fun m n => Subtype.ext (hlift_comm 2 0 2 0 m n (by decide) (by decide)))
    (fun m => Subtype.ext (hlift5 2 0 m)) (hgen_sub g3 H₃ rfl)
  have hε_lt : (1 : ℝ) / Real.sqrt 5 < 1 := by
    rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
    have : (1 : ℝ) < 5 := by norm_num
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ < Real.sqrt 5 := Real.sqrt_lt_sqrt zero_le_one this
  have hε0_lt : Real.sqrt 2 * (1 / Real.sqrt 5) / Real.sqrt (1 - 1 / Real.sqrt 5) < 1 := by
    have hrt5 : 2 < Real.sqrt 5 := by
      have : Real.sqrt 4 < Real.sqrt 5 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h4 : Real.sqrt 4 = 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
      linarith
    have h1m : 0 < 1 - 1 / Real.sqrt 5 := by linarith
    rw [div_lt_one (Real.sqrt_pos.mpr h1m)]
    have hsq : (Real.sqrt 2 * (1 / Real.sqrt 5)) ^ 2 < 1 - 1 / Real.sqrt 5 := by
      rw [mul_pow, one_div, inv_pow, Real.sq_sqrt zero_le_two, Real.sq_sqrt (by norm_num)]
      have hlt : (Real.sqrt 5)⁻¹ < (2 : ℝ)⁻¹ := by
        rw [inv_lt_inv₀ (by linarith) zero_lt_two]; exact hrt5
      linarith
    have hlt := Real.sqrt_lt_sqrt (sq_nonneg _) hsq
    rwa [Real.sqrt_sq (by positivity)] at hlt
  obtain ⟨κ', hgap⟩ := three_subgroups_spectralGap H₁ H₂ H₃ hgen (by positivity) hε_lt hε0_lt
    h12 h13 h23 hH₁ hH₂ hH₃
  refine ⟨κ', hasSpectralGap_mono ?_ le_rfl hgap.1 hgap⟩
  intro y hy
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hy
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
  rcases hy with (⟨a, ⟨m, rfl⟩, rfl⟩ | ⟨a, ⟨m, rfl⟩, rfl⟩) | ⟨a, ⟨m, rfl⟩, rfl⟩
  · refine ⟨x 0 1 ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩,
      Finset.mem_image.mpr ⟨(0, 1, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (0 : Fin 3) ≠ 1 by decide⟩, rfl⟩, ?_⟩
    apply Subtype.ext; exact (hlift_val 0 1 m).symm
  · refine ⟨x 1 2 ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩,
      Finset.mem_image.mpr ⟨(1, 2, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (1 : Fin 3) ≠ 2 by decide⟩, rfl⟩, ?_⟩
    apply Subtype.ext; exact (hlift_val 1 2 m).symm
  · refine ⟨x 2 0 ⟨m.val, lt_of_lt_of_le m.isLt hk7⟩,
      Finset.mem_image.mpr ⟨(2, 0, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, show (2 : Fin 3) ≠ 0 by decide⟩, rfl⟩, ?_⟩
    apply Subtype.ext; exact (hlift_val 2 0 m).symm

end DeltaPropT

/- ### 4. Mean Ergodic Theorem, Heisenberg 1/√2-orthogonality, and EJZ Magic Graph -/

section HeisenbergAndMagicGraph

lemma starProjection_congr {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {K₁ K₂ : Submodule ℂ V} [K₁.HasOrthogonalProjection] [K₂.HasOrthogonalProjection]
    (h : K₁ = K₂) (v : V) : K₁.starProjection v = K₂.starProjection v := by
  subst h; rfl

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

/-- Elementary `1 / √2`-orthogonality for any Heisenberg-type group `⟨x, y⟩` with `⁅x, y⁆` central. -/
lemma heisenberg_epsOrth {Γ : Type} [Group Γ] (x y : Γ)
    (hx : Commute ⁅x, y⁆ x) (hy : Commute ⁅x, y⁆ y) :
    SubgroupEpsOrth (Subgroup.closure {x}) (Subgroup.closure {y}) (1 / Real.sqrt 2) := by
  set X := Subgroup.closure ({x} : Set Γ)
  set Y := Subgroup.closure ({y} : Set Γ)
  set J := X ⊔ Y
  let xJ : J := ⟨x, (le_sup_left : X ≤ J) (Subgroup.subset_closure rfl)⟩
  let yJ : J := ⟨y, (le_sup_right : Y ≤ J) (Subgroup.subset_closure rfl)⟩
  let zJ : J := ⁅xJ, yJ⁆
  have hcentJ : ∀ g : J, Commute zJ g := by
    rintro ⟨g, hg⟩
    have hg' : g ∈ Subgroup.closure (({x} : Set Γ) ∪ ({y} : Set Γ)) := by
      rwa [Subgroup.closure_union]
    apply Subtype.ext
    change Commute ⁅x, y⁆ g
    clear hg
    induction hg' using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact hx
      · exact hy
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hyx_pow : ∀ m n : ℕ, yJ ^ m * xJ ^ n = (zJ⁻¹) ^ (m * n) * xJ ^ n * yJ ^ m := by
    have h1 : yJ * xJ = zJ⁻¹ * xJ * yJ := by
      dsimp only [zJ]; simp only [commutatorElement_def]; group
    have h1n : ∀ n : ℕ, yJ * xJ ^ n = (zJ⁻¹) ^ n * xJ ^ n * yJ := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, ← mul_assoc, ih, mul_assoc ((zJ⁻¹) ^ n * xJ ^ n), h1]
        have hc1 : Commute zJ⁻¹ (xJ ^ n) := (hcentJ (xJ ^ n)).inv_left
        calc (zJ⁻¹) ^ n * xJ ^ n * (zJ⁻¹ * xJ * yJ)
            = (zJ⁻¹) ^ n * (xJ ^ n * zJ⁻¹) * xJ * yJ := by group
          _ = (zJ⁻¹) ^ n * (zJ⁻¹ * xJ ^ n) * xJ * yJ := by rw [← hc1.eq]
          _ = (zJ⁻¹) ^ (n + 1) * (xJ ^ n * xJ) * yJ := by rw [pow_succ]; group
    intro m n
    induction m with
    | zero => simp
    | succ m ih =>
      conv_lhs => rw [pow_succ', mul_assoc, ih]
      have hc1 : Commute ((zJ⁻¹) ^ (m * n)) yJ := ((hcentJ yJ).inv_left).pow_left _
      have hc2 : Commute ((zJ⁻¹) ^ n) (xJ ^ n) := ((hcentJ (xJ ^ n)).inv_left).pow_left _
      calc yJ * ((zJ⁻¹) ^ (m * n) * xJ ^ n * yJ ^ m)
          = (yJ * (zJ⁻¹) ^ (m * n)) * xJ ^ n * yJ ^ m := by group
        _ = ((zJ⁻¹) ^ (m * n) * yJ) * xJ ^ n * yJ ^ m := by rw [← hc1.eq]
        _ = (zJ⁻¹) ^ (m * n) * (yJ * xJ ^ n) * yJ ^ m := by group
        _ = (zJ⁻¹) ^ (m * n) * ((zJ⁻¹) ^ n * xJ ^ n * yJ) * yJ ^ m := by rw [h1n n]
        _ = ((zJ⁻¹) ^ (m * n) * (zJ⁻¹) ^ n) * xJ ^ n * (yJ * yJ ^ m) := by group
        _ = (zJ⁻¹) ^ ((m + 1) * n) * xJ ^ n * yJ ^ (m + 1) := by
            rw [← pow_add, show m * n + n = (m + 1) * n by ring, pow_succ' yJ m]
  intro W _ _ _ σ htriv
  set X' := X.comap J.subtype
  set Y' := Y.comap J.subtype
  have hX'_inv : invSubspace σ X' = fixedSubspace (σ xJ) := by
    ext w; constructor
    · intro hw; exact hw xJ (Subgroup.subset_closure rfl)
    · intro hw ⟨g, hgJ⟩ hgX
      have hsub : ∀ u, u ∈ X → ∀ huJ : u ∈ J, σ ⟨u, huJ⟩ w = w := by
        intro u hu
        induction hu using Subgroup.closure_induction with
        | mem a ha =>
          rcases ha with rfl; intro _; exact hw
        | one => intro _; exact rep_one σ w
        | mul a b ha hb iha ihb =>
          intro _
          have haJ : a ∈ J := (le_sup_left : X ≤ J) ha
          have hbJ : b ∈ J := (le_sup_left : X ≤ J) hb
          change σ (⟨a, haJ⟩ * ⟨b, hbJ⟩) w = w
          rw [rep_mul, ihb hbJ, iha haJ]
        | inv a ha iha =>
          intro _
          have haJ : a ∈ J := (le_sup_left : X ≤ J) ha
          change σ (⟨a, haJ⟩⁻¹) w = w
          have h1 := congrArg (σ (⟨a, haJ⟩⁻¹)) (iha haJ)
          rw [rep_inv_mul] at h1; exact h1.symm
      exact hsub g hgX hgJ
  have hY'_inv : invSubspace σ Y' = fixedSubspace (σ yJ) := by
    ext w; constructor
    · intro hw; exact hw yJ (Subgroup.subset_closure rfl)
    · intro hw ⟨g, hgJ⟩ hgY
      have hsub : ∀ u, u ∈ Y → ∀ huJ : u ∈ J, σ ⟨u, huJ⟩ w = w := by
        intro u hu
        induction hu using Subgroup.closure_induction with
        | mem a ha =>
          rcases ha with rfl; intro _; exact hw
        | one => intro _; exact rep_one σ w
        | mul a b ha hb iha ihb =>
          intro _
          have haJ : a ∈ J := (le_sup_right : Y ≤ J) ha
          have hbJ : b ∈ J := (le_sup_right : Y ≤ J) hb
          change σ (⟨a, haJ⟩ * ⟨b, hbJ⟩) w = w
          rw [rep_mul, ihb hbJ, iha haJ]
        | inv a ha iha =>
          intro _
          have haJ : a ∈ J := (le_sup_right : Y ≤ J) ha
          change σ (⟨a, haJ⟩⁻¹) w = w
          have h1 := congrArg (σ (⟨a, haJ⟩⁻¹)) (iha haJ)
          rw [rep_inv_mul] at h1; exact h1.symm
      exact hsub g hgY hgJ
  have hXY_top : X' ⊔ Y' = ⊤ := by
    have hsub : ∀ u, u ∈ Subgroup.closure ((X : Set Γ) ∪ (Y : Set Γ)) →
        ∀ huJ : u ∈ J, (⟨u, huJ⟩ : J) ∈ X' ⊔ Y' := by
      intro u hu
      induction hu using Subgroup.closure_induction with
      | mem a ha =>
        intro _; rcases ha with ha | ha
        · exact Subgroup.mem_sup_left ha
        · exact Subgroup.mem_sup_right ha
      | one => intro _; exact Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
        intro _
        exact Subgroup.mul_mem _ (iha (by dsimp only [J]; rwa [Subgroup.sup_eq_closure]))
          (ihb (by dsimp only [J]; rwa [Subgroup.sup_eq_closure]))
      | inv a ha iha =>
        intro _
        exact Subgroup.inv_mem _ (iha (by dsimp only [J]; rwa [Subgroup.sup_eq_closure]))
    rw [eq_top_iff]; rintro ⟨g, hg⟩ _
    exact hsub g (by dsimp only [J] at hg; rwa [Subgroup.sup_eq_closure] at hg) hg
  -- Define `Vd d := fixedSubspace (σ zJ ^ d)`, `Fd d`, `Ed d`, `Wfin`
  let Vd : ℕ → Submodule ℂ W := fun d => fixedSubspace (σ zJ ^ d)
  have hVd_inv : ∀ (d : ℕ) (g : J) (w : W), w ∈ Vd d → σ g w ∈ Vd d := by
    intro d g w hw
    change (σ zJ ^ d) (σ g w) = σ g w
    rw [← map_pow, ← rep_mul, ((hcentJ g).pow_left d).eq, rep_mul, map_pow]
    exact congrArg (σ g) hw
  have hVd_proj_comm : ∀ (d : ℕ) (g : J) (w : W),
      (Vd d).starProjection (σ g w) = σ g ((Vd d).starProjection w) := fun d g w =>
    starProjection_comm_of_invariant (σ g) (Vd d) (hVd_inv d g)
      (fun u hu => by
        have hinv : (σ g).symm u = σ g⁻¹ u := by
          apply (σ g).injective; rw [(σ g).apply_symm_apply, rep_mul_inv]
        rw [hinv]; exact hVd_inv d g⁻¹ u hu) w
  let Fd : ℕ → Submodule ℂ W := fun d => (⨆ r ∈ Finset.Ico 1 d, Vd r).topologicalClosure
  let Ed : ℕ → Submodule ℂ W := fun d => Vd d ⊓ (Fd d)ᗮ
  have hFd_cl : ∀ d, IsClosed (Fd d : Set W) := fun d => Submodule.isClosed_topologicalClosure _
  have hEd_cl : ∀ d, IsClosed (Ed d : Set W) := fun d =>
    (isClosed_fixedSubspace _).inter (Fd d).isClosed_orthogonal
  have hFd_orth_proj : ∀ d, (Fd d).HasOrthogonalProjection := fun d => hasOrthProj_of_isClosed (hFd_cl d)
  have hEd_orth_proj : ∀ d, (Ed d).HasOrthogonalProjection := fun d => hasOrthProj_of_isClosed (hEd_cl d)
  have hFd_inv : ∀ (d : ℕ) (g : J) (w : W), w ∈ Fd d → σ g w ∈ Fd d := by
    intro d g w hw
    have hsub : (⨆ r ∈ Finset.Ico 1 d, Vd r) ≤ (Fd d).comap (σ g).toLinearMap := by
      refine iSup₂_le fun r hr u hu => ?_
      change σ g u ∈ Fd d
      exact Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem r (Submodule.mem_iSup_of_mem hr (hVd_inv r g u hu)))
    have hcl : IsClosed (((Fd d).comap (σ g).toLinearMap : Submodule ℂ W) : Set W) :=
      (hFd_cl d).preimage (σ g).continuous
    exact (hcl.closure_subset_iff.mpr hsub) hw
  have hEd_inv : ∀ (d : ℕ) (g : J) (w : W), w ∈ Ed d → σ g w ∈ Ed d := by
    intro d g w ⟨hw1, hw2⟩
    refine ⟨hVd_inv d g w hw1, ?_⟩
    change w ∈ (Fd d)ᗮ at hw2
    change σ g w ∈ (Fd d)ᗮ
    rw [Submodule.mem_orthogonal] at hw2 ⊢
    intro u hu
    rw [rep_inner_inv]
    exact hw2 (σ g⁻¹ u) (hFd_inv d g⁻¹ u hu)
  have hEd_proj_comm : ∀ (d : ℕ) (g : J) (w : W),
      (Ed d).starProjection (σ g w) = σ g ((Ed d).starProjection w) := fun d g w =>
    @starProjection_comm_of_invariant W _ _ _ (σ g) (Ed d) (hEd_orth_proj d) (hEd_inv d g)
      (fun u hu => by
        have hinv : (σ g).symm u = σ g⁻¹ u := by
          apply (σ g).injective; rw [(σ g).apply_symm_apply, rep_mul_inv]
        rw [hinv]; exact hEd_inv d g⁻¹ u hu) w
  let Wfin : Submodule ℂ W := (⨆ d ∈ Set.Ici (1 : ℕ), Vd d).topologicalClosure
  have hWfin_cl : IsClosed (Wfin : Set W) := Submodule.isClosed_topologicalClosure _
  have : Wfin.HasOrthogonalProjection := hasOrthProj_of_isClosed hWfin_cl
  have hWfin_inv : ∀ (g : J) (w : W), w ∈ Wfin → σ g w ∈ Wfin := by
    intro g w hw
    have hsub : (⨆ d ∈ Set.Ici (1 : ℕ), Vd d) ≤ Wfin.comap (σ g).toLinearMap := by
      refine iSup₂_le fun d hd u hu => ?_
      change σ g u ∈ Wfin
      exact Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd (hVd_inv d g u hu)))
    have hcl : IsClosed ((Wfin.comap (σ g).toLinearMap : Submodule ℂ W) : Set W) :=
      hWfin_cl.preimage (σ g).continuous
    exact (hcl.closure_subset_iff.mpr hsub) hw
  have hWfin_proj_comm : ∀ (g : J) (w : W), Wfin.starProjection (σ g w) = σ g (Wfin.starProjection w) :=
    fun g w => starProjection_comm_of_invariant (σ g) Wfin (hWfin_inv g)
      (fun u hu => by
        have hinv : (σ g).symm u = σ g⁻¹ u := by
          apply (σ g).injective; rw [(σ g).apply_symm_apply, rep_mul_inv]
        rw [hinv]; exact hWfin_inv g⁻¹ u hu) w
  -- Key inner product identity: for `w ∈ W^{Y'}` and `n ≥ 1`, `⟪(σ xJ ^ n) w, w⟫ = ⟪(σ xJ ^ n) (P_{Vd n} w), P_{Vd n} w⟫`
  have hinner_Vd : ∀ (w : W), w ∈ invSubspace σ Y' → ∀ n : ℕ, 1 ≤ n →
      ⟪(σ xJ ^ n) w, w⟫_ℂ = ⟪(σ xJ ^ n) ((Vd n).starProjection w), (Vd n).starProjection w⟫_ℂ := by
    intro w hwY n _
    have hfixY : ∀ m : ℕ, (σ yJ ^ m) w = w := fun m => by
      have hw1 : σ yJ w = w := by rwa [hY'_inv] at hwY
      induction m with
      | zero => rfl
      | succ m ih => rw [pow_succ']; change σ yJ ((σ yJ ^ m) w) = w; rw [ih, hw1]
    have hstep : ∀ m : ℕ, ⟪(σ xJ ^ n) w, w⟫_ℂ = ⟪((σ zJ⁻¹ ^ n) ^ m) ((σ xJ ^ n) w), w⟫_ℂ := by
      intro m
      have h1 := (σ yJ ^ m).inner_map_map ((σ xJ ^ n) w) w
      rw [hfixY m] at h1
      rw [← h1]
      congr 1
      rw [← map_pow, ← map_pow, ← rep_mul, hyx_pow m n, rep_mul, rep_mul,
        map_pow σ yJ m, hfixY m, map_pow, mul_comm m n, pow_mul]
    have havg : ∀ M : ℕ, 1 ≤ M →
        ⟪((M : ℂ)⁻¹) • ∑ m ∈ Finset.range M, ((σ zJ⁻¹ ^ n) ^ m) ((σ xJ ^ n) w), w⟫_ℂ =
          ⟪(σ xJ ^ n) w, w⟫_ℂ := by
      intro M hM
      rw [inner_smul_left, sum_inner]
      have hterm : ∀ m ∈ Finset.range M, ⟪((σ zJ⁻¹ ^ n) ^ m) ((σ xJ ^ n) w), w⟫_ℂ = ⟪(σ xJ ^ n) w, w⟫_ℂ :=
        fun m _ => (hstep m).symm
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hM0 : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hstar : (starRingEnd ℂ) ((M : ℂ)⁻¹) = (M : ℂ)⁻¹ := by rw [map_inv₀, map_natCast]
      rw [hstar, ← mul_assoc, inv_mul_cancel₀ hM0, one_mul]
    have htend1 : Tendsto (fun M : ℕ =>
        ⟪((M : ℂ)⁻¹) • ∑ m ∈ Finset.range M, ((σ zJ⁻¹ ^ n) ^ m) ((σ xJ ^ n) w), w⟫_ℂ)
        atTop (𝓝 ⟪(fixedSubspace (σ zJ⁻¹ ^ n)).starProjection ((σ xJ ^ n) w), w⟫_ℂ) :=
      ((continuous_id.inner continuous_const).tendsto _).comp (mean_ergodic_theorem (σ zJ⁻¹ ^ n) _)
    have htend2 : Tendsto (fun M : ℕ =>
        ⟪((M : ℂ)⁻¹) • ∑ m ∈ Finset.range M, ((σ zJ⁻¹ ^ n) ^ m) ((σ xJ ^ n) w), w⟫_ℂ)
        atTop (𝓝 ⟪(σ xJ ^ n) w, w⟫_ℂ) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with M hM
      exact (havg M hM).symm
    have heq_sub : fixedSubspace (σ zJ⁻¹ ^ n) = Vd n := by
      ext u
      change (σ zJ⁻¹ ^ n) u = u ↔ (σ zJ ^ n) u = u
      rw [← map_pow, ← map_pow]
      constructor
      · intro h
        have h1 := congrArg (σ (zJ ^ n)) h
        rw [← rep_mul, inv_pow, mul_inv_cancel, rep_one] at h1
        exact h1.symm
      · intro h
        have h1 := congrArg (σ (zJ⁻¹ ^ n)) h
        rw [← rep_mul, show zJ⁻¹ ^ n * zJ ^ n = 1 by rw [inv_pow, inv_mul_cancel], rep_one] at h1
        exact h1.symm
    have heq : ⟪(σ xJ ^ n) w, w⟫_ℂ = ⟪(Vd n).starProjection ((σ xJ ^ n) w), w⟫_ℂ := by
      have h0 := tendsto_nhds_unique htend2 htend1
      rwa [starProjection_congr heq_sub] at h0
    rw [heq]
    have hcomm : (Vd n).starProjection ((σ xJ ^ n) w) = (σ xJ ^ n) ((Vd n).starProjection w) := by
      have hpow : σ xJ ^ n = σ (xJ ^ n) := (map_pow σ xJ n).symm
      rw [hpow]; exact hVd_proj_comm n (xJ ^ n) w
    rw [hcomm]
    have horth : ⟪(σ xJ ^ n) ((Vd n).starProjection w), w - (Vd n).starProjection w⟫_ℂ = 0 := by
      have hmem : (σ xJ ^ n) ((Vd n).starProjection w) ∈ Vd n := by
        rw [← map_pow]; exact hVd_inv n (xJ ^ n) _ (Submodule.coe_mem _)
      exact (Submodule.mem_orthogonal (Vd n) _).mp ((Vd n).sub_starProjection_mem_orthogonal w) _ hmem
    rw [inner_sub_right, sub_eq_zero] at horth
    exact horth
  -- Bound on `Wfinᗮ`: `P_{X'} w = 0` for `w ∈ W^{Y'} ∩ Wfinᗮ`
  have hPX_orth_Wfin : ∀ w : W, w ∈ invSubspace σ Y' → w ∈ Wfinᗮ →
      (invSubspace σ X').starProjection w = 0 := by
    intro w hwY hw_orth
    have hterm0 : ∀ n : ℕ, 1 ≤ n → ⟪(σ xJ ^ n) w, w⟫_ℂ = 0 := by
      intro n hn
      rw [hinner_Vd w hwY n hn]
      have hVd_le : Vd n ≤ Wfin := fun u hu =>
        Submodule.le_topologicalClosure _ (Submodule.mem_iSup_of_mem n (Submodule.mem_iSup_of_mem hn hu))
      have hp0 : (Vd n).starProjection w = 0 := by
        refine (Vd n).eq_starProjection_of_mem_orthogonal (Vd n).zero_mem ?_
        rw [sub_zero, Submodule.mem_orthogonal]
        intro u hu; exact (Submodule.mem_orthogonal Wfin w).mp hw_orth u (hVd_le hu)
      rw [hp0, map_zero, inner_zero_left]
    have hlim1 : Tendsto (fun N : ℕ =>
        ⟪((N : ℂ)⁻¹) • ∑ k ∈ Finset.range N, (σ xJ ^ k) w, w⟫_ℂ)
        atTop (𝓝 ⟪(fixedSubspace (σ xJ)).starProjection w, w⟫_ℂ) :=
      ((continuous_id.inner continuous_const).tendsto _).comp (mean_ergodic_theorem (σ xJ) w)
    have hlim2 : Tendsto (fun N : ℕ =>
        ⟪((N : ℂ)⁻¹) • ∑ k ∈ Finset.range N, (σ xJ ^ k) w, w⟫_ℂ)
        atTop (𝓝 (0 : ℂ)) := by
      have h0 : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹) * ⟪w, w⟫_ℂ) atTop (𝓝 (0 : ℂ)) := by
        have hinv : Tendsto (fun N : ℕ => ((N : ℂ)⁻¹)) atTop (𝓝 (0 : ℂ)) := by
          have := tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))
          simpa [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_natCast] using
            (Complex.continuous_ofReal.tendsto 0).comp this
        simpa using hinv.mul_const ⟪w, w⟫_ℂ
      refine h0.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop 1] with N hN
      rw [inner_smul_left, sum_inner]
      have hstar : (starRingEnd ℂ) ((N : ℂ)⁻¹) = (N : ℂ)⁻¹ := by rw [map_inv₀, map_natCast]
      rw [hstar]
      congr 1
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk0; exact hterm0 k (Nat.pos_of_ne_zero hk0)
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have hinner0 : ⟪(invSubspace σ X').starProjection w, w⟫_ℂ = 0 := by
      rw [starProjection_congr hX'_inv]; exact tendsto_nhds_unique hlim1 hlim2
    set p := (invSubspace σ X').starProjection w
    have horth : ⟪p, w - p⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal _ _).mp ((invSubspace σ X').sub_starProjection_mem_orthogonal w) p (Submodule.coe_mem _)
    rw [inner_sub_right, hinner0, zero_sub, neg_eq_zero, inner_self_eq_zero] at horth
    exact horth
  -- Bound on each `Ed d` (`d ≥ 1`): `‖P_{X'} w‖² ≤ (1/2) * ‖w‖²`
  have hPX_Ed : ∀ (d : ℕ), 1 ≤ d → ∀ w : W, w ∈ invSubspace σ Y' → w ∈ Ed d →
      ‖(invSubspace σ X').starProjection w‖ ^ 2 ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
    intro d hd w hwY hwEd
    by_cases hd1 : d = 1
    · subst hd1
      -- On `Ed 1 ≤ Vd 1`, `σ zJ w = w`, so `P_{X'} w ∈ W^{X'} ⊓ W^{Y'} = ⊥`
      have hz1 : σ zJ w = w := by simpa [Vd, fixedSubspace] using hwEd.1
      have hfixY_pow : ∀ k : ℕ, (σ xJ ^ k) w ∈ invSubspace σ Y' := by
        intro k
        rw [hY'_inv]; change σ yJ ((σ xJ ^ k) w) = (σ xJ ^ k) w
        have hyw : σ yJ w = w := by rwa [hY'_inv] at hwY
        have hzk : (σ zJ⁻¹ ^ k) w = w := by
          have hzinv : σ zJ⁻¹ w = w := by
            have h1 := congrArg (σ zJ⁻¹) hz1
            rw [rep_inv_mul] at h1; exact h1.symm
          induction k with
          | zero => rfl
          | succ k ih => rw [pow_succ']; change σ zJ⁻¹ ((σ zJ⁻¹ ^ k) w) = w; rw [ih, hzinv]
        have hrel := hyx_pow 1 k
        simp only [pow_one, one_mul] at hrel
        rw [← map_pow, ← rep_mul, hrel, rep_mul, rep_mul, hyw,
          ← rep_mul, ((hcentJ (xJ ^ k)).inv_left.pow_left k).eq, rep_mul, map_pow, map_pow, hzk]
      have hmemY : (invSubspace σ X').starProjection w ∈ invSubspace σ Y' := by
        rw [starProjection_congr hX'_inv]
        refine (isClosed_invSubspace σ Y').mem_of_tendsto (mean_ergodic_theorem (σ xJ) w) ?_
        filter_upwards with N
        exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => hfixY_pow k)
      have htop : (invSubspace σ X').starProjection w ∈ invSubspace σ ⊤ := by
        rw [← hXY_top, invSubspace_sup]
        exact ⟨Submodule.coe_mem _, hmemY⟩
      rw [htriv, Submodule.mem_bot] at htop
      rw [htop]; simp
    · have hd2 : 2 ≤ d := by omega
      have hzero_ndvd : ∀ n : ℕ, 1 ≤ n → ¬ d ∣ n → ⟪(σ xJ ^ n) w, w⟫_ℂ = 0 := by
        intro n hn hndvd
        rw [hinner_Vd w hwY n hn]
        set u := (Vd n).starProjection w
        have hu_Vd : u ∈ Vd d := by
          have h1 : (σ zJ ^ d) u = (Vd n).starProjection ((σ zJ ^ d) w) := by
            have hpow : σ zJ ^ d = σ (zJ ^ d) := (map_pow σ zJ d).symm
            rw [hpow]; exact (hVd_proj_comm n (zJ ^ d) w).symm
          have h2 : (σ zJ ^ d) w = w := hwEd.1
          change (σ zJ ^ d) u = u; rw [h1, h2]
        have hu_Vn : u ∈ Vd n := Submodule.coe_mem _
        have hu_Vr : u ∈ Vd (n % d) := by
          have hdiv := Nat.div_add_mod n d
          change (σ zJ ^ (n % d)) u = u
          have hqd : (σ zJ ^ (d * (n / d))) u = u := by
            rw [pow_mul]
            induction (n / d) with
            | zero => rfl
            | succ q ih =>
              rw [pow_succ']
              change (σ zJ ^ d) (((σ zJ ^ d) ^ q) u) = u
              rw [ih]; exact hu_Vd
          have hsum : (σ zJ ^ (d * (n / d))) ((σ zJ ^ (n % d)) u) = u := by
            rw [← map_pow, ← map_pow, ← rep_mul, ← pow_add, hdiv, map_pow]
            exact hu_Vn
          have hcomm : (σ zJ ^ (d * (n / d))) ((σ zJ ^ (n % d)) u) =
              (σ zJ ^ (n % d)) ((σ zJ ^ (d * (n / d))) u) := by
            rw [← map_pow, ← map_pow, ← rep_mul, ← pow_add, add_comm, pow_add, rep_mul, map_pow, map_pow]
          rw [hcomm, hqd] at hsum; exact hsum
        have hr_mem : n % d ∈ Finset.Ico 1 d := Finset.mem_Ico.mpr
          ⟨Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0), Nat.mod_lt n (by omega)⟩
        have hu_Fd : u ∈ Fd d := Submodule.le_topologicalClosure _
          (Submodule.mem_iSup_of_mem (n % d) (Submodule.mem_iSup_of_mem hr_mem hu_Vr))
        have hu_orth : u ∈ (Fd d)ᗮ := by
          rw [Submodule.mem_orthogonal]
          intro a ha
          have ha' : (Vd n).starProjection a ∈ Fd d := by
            -- `P_{Vd n}` preserves `Fd d` via `mean_ergodic_theorem`!
            refine (hFd_cl d).mem_of_tendsto (mean_ergodic_theorem (σ zJ ^ n) a) ?_
            filter_upwards with N
            refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => ?_)
            rw [← map_pow, ← map_pow]; exact hFd_inv d ((zJ ^ n) ^ k) a ha
          have hself : ⟪a, u⟫_ℂ = ⟪(Vd n).starProjection a, w⟫_ℂ := by
            have h1 : ⟪a - (Vd n).starProjection a, u⟫_ℂ = 0 :=
              (Vd n).starProjection_inner_eq_zero a u (Submodule.coe_mem _)
            have h2 : ⟪(Vd n).starProjection a, w - u⟫_ℂ = 0 :=
              (Submodule.mem_orthogonal (Vd n) _).mp ((Vd n).sub_starProjection_mem_orthogonal w) _ (Submodule.coe_mem _)
            rw [inner_sub_left, sub_eq_zero] at h1
            rw [inner_sub_right, sub_eq_zero] at h2
            rw [h1, h2]
          rw [hself]
          exact (Submodule.mem_orthogonal (Fd d) w).mp hwEd.2 _ ha'
        have hu0 : u = 0 := inner_self_eq_zero.mp ((Submodule.mem_orthogonal (Fd d) u).mp hu_orth u hu_Fd)
        rw [hu0, map_zero, inner_zero_left]
      -- Subsequence `N = m * d` in `mean_ergodic_theorem`
      have hsub_le : ∀ m : ℕ, 1 ≤ m →
          (⟪(((m * d : ℕ) : ℂ)⁻¹) • ∑ n ∈ Finset.range (m * d), (σ xJ ^ n) w, w⟫_ℂ).re ≤
            (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
        intro m hm
        rw [inner_smul_left, sum_inner]
        have hstar : (starRingEnd ℂ) ((((m * d : ℕ) : ℂ)⁻¹)) = ((((m * d : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) := by
          rw [map_inv₀, map_natCast, Complex.ofReal_inv, Complex.ofReal_natCast]
        rw [hstar, Complex.re_ofReal_mul, Complex.re_sum]
        have hfilt : ∑ n ∈ Finset.range (m * d), (⟪(σ xJ ^ n) w, w⟫_ℂ).re =
            ∑ n ∈ (Finset.range (m * d)).filter (d ∣ ·), (⟪(σ xJ ^ n) w, w⟫_ℂ).re := by
          rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (m * d)) (d ∣ ·)]
          have h0 : ∑ n ∈ (Finset.range (m * d)).filter (fun n => ¬ d ∣ n), (⟪(σ xJ ^ n) w, w⟫_ℂ).re = 0 :=
            Finset.sum_eq_zero fun n hn => by
              have hnd : ¬ d ∣ n := (Finset.mem_filter.mp hn).2
              have hn1 : 1 ≤ n := Nat.pos_of_ne_zero fun h0 => hnd (h0 ▸ dvd_zero d)
              rw [hzero_ndvd n hn1 hnd, Complex.zero_re]
          rw [h0, add_zero]
        have hcard_le : ((Finset.range (m * d)).filter (d ∣ ·)).card ≤ m := by
          have hsub : (Finset.range (m * d)).filter (d ∣ ·) ⊆ (Finset.range m).image (· * d) := by
            intro n hn
            obtain ⟨hnr, q, rfl⟩ := Finset.mem_filter.mp hn
            rw [Finset.mem_range] at hnr
            refine Finset.mem_image.mpr ⟨q, Finset.mem_range.mpr ?_, mul_comm q d⟩
            nlinarith
          exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
        have hsum_le : ∑ n ∈ (Finset.range (m * d)).filter (d ∣ ·), (⟪(σ xJ ^ n) w, w⟫_ℂ).re ≤
            (m : ℝ) * ‖w‖ ^ 2 := by
          calc ∑ n ∈ (Finset.range (m * d)).filter (d ∣ ·), (⟪(σ xJ ^ n) w, w⟫_ℂ).re
              ≤ ∑ _n ∈ (Finset.range (m * d)).filter (d ∣ ·), ‖w‖ ^ 2 :=
                Finset.sum_le_sum fun n _ => by
                  calc (⟪(σ xJ ^ n) w, w⟫_ℂ).re ≤ ‖⟪(σ xJ ^ n) w, w⟫_ℂ‖ := Complex.re_le_norm _
                    _ ≤ ‖(σ xJ ^ n) w‖ * ‖w‖ := norm_inner_le_norm _ _
                    _ = ‖w‖ ^ 2 := by rw [(σ xJ ^ n).norm_map]; ring
            _ = (((Finset.range (m * d)).filter (d ∣ ·)).card : ℝ) * ‖w‖ ^ 2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
            _ ≤ (m : ℝ) * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard_le) (sq_nonneg _)
        rw [hfilt]
        have hmd_pos : (0 : ℝ) < ((m * d : ℕ) : ℝ) := Nat.cast_pos.mpr (by nlinarith)
        calc (((m * d : ℕ) : ℝ)⁻¹) * ∑ n ∈ (Finset.range (m * d)).filter (d ∣ ·), (⟪(σ xJ ^ n) w, w⟫_ℂ).re
            ≤ (((m * d : ℕ) : ℝ)⁻¹) * ((m : ℝ) * ‖w‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hsum_le (by positivity)
          _ = ((m : ℝ) / ((m : ℝ) * (d : ℝ))) * ‖w‖ ^ 2 := by push_cast; ring
          _ ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
              refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
              have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (by omega)
              have hd_ge : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
              rw [div_le_div_iff₀ (by positivity) zero_lt_two]; nlinarith
      have htend_sub : Tendsto (fun m : ℕ =>
          (⟪(((m * d : ℕ) : ℂ)⁻¹) • ∑ n ∈ Finset.range (m * d), (σ xJ ^ n) w, w⟫_ℂ).re)
          atTop (𝓝 (⟪(fixedSubspace (σ xJ)).starProjection w, w⟫_ℂ).re) := by
        have hcont : Continuous (fun u : W => (⟪u, w⟫_ℂ).re) :=
          Complex.continuous_re.comp (continuous_id.inner continuous_const)
        have h1 := (hcont.tendsto _).comp (mean_ergodic_theorem (σ xJ) w)
        have hmul : Tendsto (fun m : ℕ => m * d) atTop atTop :=
          Filter.tendsto_atTop.mpr fun b => Filter.eventually_atTop.mpr ⟨b, fun m hm => by nlinarith⟩
        exact h1.comp hmul
      have hre_le : (⟪(invSubspace σ X').starProjection w, w⟫_ℂ).re ≤ (1 / 2 : ℝ) * ‖w‖ ^ 2 := by
        rw [starProjection_congr hX'_inv]
        exact le_of_tendsto htend_sub (Filter.eventually_atTop.mpr ⟨1, hsub_le⟩)
      have hnorm_eq : ‖(invSubspace σ X').starProjection w‖ ^ 2 =
          (⟪(invSubspace σ X').starProjection w, w⟫_ℂ).re := by
        set p := (invSubspace σ X').starProjection w
        have horth : ⟪p, w - p⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal _ _).mp ((invSubspace σ X').sub_starProjection_mem_orthogonal w) p (Submodule.coe_mem _)
        rw [inner_sub_right, sub_eq_zero] at horth
        rw [horth, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
        exact (Complex.ofReal_re _).symm
      rw [hnorm_eq]; exact hre_le
  -- Pairwise orthogonality of `Ed d` and finite orthogonal sums `Md D := ⨆ d ∈ Finset.Icc 1 D, Ed d`
  have hEd_orth : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → d₁ < d₂ → ∀ u ∈ Ed d₁, ∀ v ∈ Ed d₂, ⟪u, v⟫_ℂ = 0 := by
    intro d₁ d₂ hd₁ hlt u hu v hv
    have hu_Fd : u ∈ Fd d₂ := Submodule.le_topologicalClosure _
      (Submodule.mem_iSup_of_mem d₁ (Submodule.mem_iSup_of_mem (Finset.mem_Ico.mpr ⟨hd₁, hlt⟩) hu.1))
    exact (Submodule.mem_orthogonal (Fd d₂) v).mp hv.2 u hu_Fd
  have hEd_orth_ne : ∀ d₁ d₂ : ℕ, 1 ≤ d₁ → 1 ≤ d₂ → d₁ ≠ d₂ → ∀ u ∈ Ed d₁, ∀ v ∈ Ed d₂, ⟪u, v⟫_ℂ = 0 := by
    intro d₁ d₂ hd₁ hd₂ hne u hu v hv
    rcases lt_or_gt_of_ne hne with h | h
    · exact hEd_orth d₁ d₂ hd₁ h u hu v hv
    · rw [← inner_conj_symm, hEd_orth d₂ d₁ hd₂ h v hv u hu, map_zero]
  let S : ℕ → W → W := fun D w => ∑ d ∈ Finset.Icc 1 D, (@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) w
  let Md : ℕ → Submodule ℂ W := fun D => ⨆ d ∈ Finset.Icc 1 D, Ed d
  have hS_mem : ∀ D w, S D w ∈ Md D := fun D w =>
    Submodule.sum_mem _ fun d hd =>
      Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd (Submodule.coe_mem _))
  have hS_orth : ∀ D w, w - S D w ∈ (Md D)ᗮ := by
    intro D w
    rw [Submodule.mem_orthogonal]
    intro z hz
    have hmem : ∀ d ∈ Finset.Icc 1 D, ∀ u ∈ Ed d, ⟪u, w - S D w⟫_ℂ = 0 := by
      intro d hd u hu
      rw [inner_sub_right]
      dsimp only [S]
      rw [inner_sum, Finset.sum_eq_single d]
      · have h1 : ⟪u, w - (@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) w⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal (Ed d) _).mp
            ((@Submodule.sub_starProjection_mem_orthogonal ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) w) u hu
        rw [inner_sub_right] at h1; exact h1
      · intro r hr hrd
        exact hEd_orth_ne d r (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hr).1 hrd.symm u hu _ (Submodule.coe_mem _)
      · intro h; exact absurd hd h
    have hle : Md D ≤ (Submodule.span ℂ {w - S D w})ᗮ := by
      refine iSup₂_le fun d hd u hu => ?_
      rw [Submodule.mem_orthogonal']
      intro t ht
      rw [Submodule.mem_span_singleton] at ht
      obtain ⟨c, rfl⟩ := ht
      rw [inner_smul_right, hmem d hd u hu, mul_zero]
    exact (Submodule.mem_orthogonal' _ z).mp (hle hz) (w - S D w) (Submodule.subset_span rfl)
  have hMd_cl : ∀ D, IsClosed (Md D : Set W) := by
    intro D
    have hS_cont : Continuous (S D) := continuous_finsetSum _ fun d _ =>
      (@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)).continuous
    have heq : (Md D : Set W) = {w : W | S D w = w} := by
      ext w; constructor
      · intro hw
        have h0 : ⟪w - S D w, w - S D w⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal (Md D) _).mp (hS_orth D w) (w - S D w) (Submodule.sub_mem _ hw (hS_mem D w))
        exact (sub_eq_zero.mp (inner_self_eq_zero.mp h0)).symm
      · intro hw; rw [← hw]; exact hS_mem D w
    rw [heq]
    exact isClosed_eq hS_cont continuous_id
  have hVd_le_Md : ∀ D d, 1 ≤ d → d ≤ D → Vd d ≤ Md D := by
    intro D
    induction D with
    | zero => intro d hd1 hd0; omega
    | succ D ih =>
      intro d hd1 hdD
      by_cases hlt : d ≤ D
      · exact (ih d hd1 hlt).trans (iSup₂_le fun r hr =>
          le_iSup₂_of_le r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩) le_rfl)
      · have hdeq : d = D + 1 := by omega
        subst hdeq
        intro v hv
        have hFd_le : Fd (D + 1) ≤ Md D :=
          Submodule.topologicalClosure_minimal _ (iSup₂_le fun r hr =>
            ih r (Finset.mem_Ico.mp hr).1 (by have := (Finset.mem_Ico.mp hr).2; omega)) (hMd_cl D)
        have hMd_le : Md D ≤ Md (D + 1) :=
          iSup₂_le fun r hr =>
            le_iSup₂_of_le r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1, by have := (Finset.mem_Icc.mp hr).2; omega⟩) le_rfl
        have hv1 : S D v ∈ Md (D + 1) := hMd_le (hS_mem D v)
        have hv2_orth : v - S D v ∈ (Fd (D + 1))ᗮ :=
          Submodule.orthogonal_le hFd_le (hS_orth D v)
        have hv2_Vd : v - S D v ∈ Vd (D + 1) := by
          have hS_Vd : S D v ∈ Vd (D + 1) := by
            change (σ zJ ^ (D + 1)) (S D v) = S D v
            dsimp only [S]
            rw [map_sum]
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [← map_pow, ← hEd_proj_comm r (zJ ^ (D + 1)) v, map_pow]
            exact congrArg _ hv
          exact (Vd (D + 1)).sub_mem hv hS_Vd
        have hv2 : v - S D v ∈ Md (D + 1) :=
          Submodule.mem_iSup_of_mem (D + 1) (Submodule.mem_iSup_of_mem (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
            ⟨hv2_Vd, hv2_orth⟩)
        have hsplit : v = S D v + (v - S D v) := by abel
        rw [hsplit]; exact (Md (D + 1)).add_mem hv1 hv2
  -- Final `epsOrth` argument
  apply epsOrth_symm
  rw [epsOrth_iff_proj_le (by positivity)]
  intro u huY
  set u_fin := Wfin.starProjection u
  set u_inf := Wfinᗮ.starProjection u
  have hu_split : u = u_fin + u_inf := by
    dsimp only [u_inf]; rw [Wfin.starProjection_orthogonal_val]; abel
  have hu_fin_Y : u_fin ∈ invSubspace σ Y' := by
    rw [hY'_inv]; change σ yJ (Wfin.starProjection u) = Wfin.starProjection u
    rw [← hWfin_proj_comm, show σ yJ u = u by rwa [hY'_inv] at huY]
  have hu_inf_Y : u_inf ∈ invSubspace σ Y' := by
    have : u_inf = u - u_fin := by rw [hu_split]; abel
    rw [this]; exact (invSubspace σ Y').sub_mem huY hu_fin_Y
  have hP_inf : (invSubspace σ X').starProjection u_inf = 0 :=
    hPX_orth_Wfin u_inf hu_inf_Y (Submodule.coe_mem _)
  have hPu_eq : (invSubspace σ X').starProjection u = (invSubspace σ X').starProjection u_fin := by
    rw [hu_split, map_add, hP_inf, add_zero]
  rw [hPu_eq]
  have hufin_le : ‖u_fin‖ ≤ ‖u‖ := by
    have hpyth := Wfin.norm_sq_eq_add_norm_sq_projection u
    have hsq : ‖u_fin‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      have : 0 ≤ ‖Wfinᗮ.orthogonalProjectionOnto u‖ ^ 2 := sq_nonneg _
      have h1 : ‖Wfin.orthogonalProjectionOnto u‖ = ‖u_fin‖ := rfl
      rw [h1] at hpyth; linarith
    have hrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hrt
  suffices hfin_bound : ∀ ε > 0, ‖(invSubspace σ X').starProjection u_fin‖ ≤ (1 / Real.sqrt 2) * ‖u_fin‖ + ε by
    have hle : ‖(invSubspace σ X').starProjection u_fin‖ ≤ (1 / Real.sqrt 2) * ‖u_fin‖ := by
      by_contra hgt
      push Not at hgt
      have h1 := hfin_bound ((‖(invSubspace σ X').starProjection u_fin‖ - (1 / Real.sqrt 2) * ‖u_fin‖) / 2) (by linarith)
      linarith
    exact hle.trans (mul_le_mul_of_nonneg_left hufin_le (by positivity))
  intro ε hε
  -- Approximate `u_fin ∈ Wfin` by some `z ∈ ⨆ d ≥ 1, Vd d`, hence `z ∈ Md D` for some `D`
  obtain ⟨z, hz_sup, hz_ball⟩ := Metric.mem_closure_iff.mp (Submodule.coe_mem (Wfin.orthogonalProjectionOnto u)) ε hε
  have hz_Md : ∃ D : ℕ, z ∈ Md D := by
    have hMd_mono : ∀ {D₁ D₂ : ℕ}, D₁ ≤ D₂ → Md D₁ ≤ Md D₂ := fun hD =>
      iSup₂_le fun r hr => le_iSup₂_of_le r (Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hr).1,
        le_trans (Finset.mem_Icc.mp hr).2 hD⟩) le_rfl
    let Usub : Submodule ℂ W :=
      { carrier := {w : W | ∃ D : ℕ, w ∈ Md D}
        zero_mem' := ⟨0, Submodule.zero_mem _⟩
        add_mem' := fun {a b} ⟨D₁, ha⟩ ⟨D₂, hb⟩ =>
          ⟨max D₁ D₂, Submodule.add_mem _ (hMd_mono (le_max_left _ _) ha) (hMd_mono (le_max_right _ _) hb)⟩
        smul_mem' := fun c {a} ⟨D, ha⟩ => ⟨D, Submodule.smul_mem _ c ha⟩ }
    have hle : (⨆ d ∈ Set.Ici (1 : ℕ), Vd d) ≤ Usub :=
      iSup₂_le fun d hd v hv => ⟨d, hVd_le_Md d d hd le_rfl hv⟩
    exact hle hz_sup
  obtain ⟨D, hzD⟩ := hz_Md
  have hdist_S : ‖u_fin - S D u_fin‖ ≤ ε := by
    have horth : ⟪S D u_fin - z, u_fin - S D u_fin⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal (Md D) _).mp (hS_orth D u_fin) _ (Submodule.sub_mem _ (hS_mem D u_fin) hzD)
    have hpyth : ‖u_fin - z‖ ^ 2 = ‖u_fin - S D u_fin‖ ^ 2 + ‖S D u_fin - z‖ ^ 2 := by
      have hsplit : u_fin - z = (u_fin - S D u_fin) + (S D u_fin - z) := by abel
      rw [hsplit, norm_add_sq (𝕜 := ℂ)]
      have h0 : ⟪u_fin - S D u_fin, S D u_fin - z⟫_ℂ = 0 := by
        rw [← inner_conj_symm, horth, map_zero]
      rw [h0]; simp
    have hsq : ‖u_fin - S D u_fin‖ ^ 2 ≤ ‖u_fin - z‖ ^ 2 := by linarith [sq_nonneg ‖S D u_fin - z‖]
    have hle : ‖u_fin - S D u_fin‖ ≤ ‖u_fin - z‖ := by
      have hrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hrt
    exact hle.trans (le_of_lt (by simpa [dist_eq_norm] using hz_ball))
  have hSD_bound : ‖(invSubspace σ X').starProjection (S D u_fin)‖ ≤ (1 / Real.sqrt 2) * ‖u_fin‖ := by
    have hsq_S : ‖S D u_fin‖ ^ 2 = ∑ d ∈ Finset.Icc 1 D, ‖(@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin‖ ^ 2 := by
      have h1 : ((‖S D u_fin‖ ^ 2 : ℝ) : ℂ) = ⟪S D u_fin, S D u_fin⟫_ℂ := by
        rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
      dsimp only [S] at h1
      rw [sum_inner] at h1
      have hterm : ∀ d ∈ Finset.Icc 1 D,
          ⟪(@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin,
            ∑ r ∈ Finset.Icc 1 D, (@Submodule.starProjection ℂ W _ _ _ (Ed r) (hEd_orth_proj r)) u_fin⟫_ℂ =
          ((‖(@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin‖ ^ 2 : ℝ) : ℂ) := by
        intro d hd
        rw [inner_sum, Finset.sum_eq_single d]
        · rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
        · intro r hr hrd
          exact hEd_orth_ne d r (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hr).1 hrd.symm _
            (Submodule.coe_mem _) _ (Submodule.coe_mem _)
        · intro h; exact absurd hd h
      rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum] at h1
      exact Complex.ofReal_injective h1
    have hsq_PS : ‖(invSubspace σ X').starProjection (S D u_fin)‖ ^ 2 =
        ∑ d ∈ Finset.Icc 1 D,
          ‖(invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin)‖ ^ 2 := by
      have hmap : (invSubspace σ X').starProjection (S D u_fin) =
          ∑ d ∈ Finset.Icc 1 D,
            (invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin) :=
        map_sum _ _ _
      have hPX_Ed_mem : ∀ d, 1 ≤ d →
          (invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin) ∈ Ed d := by
        intro d _
        rw [starProjection_congr hX'_inv]
        refine (hEd_cl d).mem_of_tendsto (mean_ergodic_theorem (σ xJ) _) ?_
        filter_upwards with N
        refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ => ?_)
        rw [← map_pow]; exact hEd_inv d (xJ ^ k) _ (Submodule.coe_mem _)
      have h1 : ((‖(invSubspace σ X').starProjection (S D u_fin)‖ ^ 2 : ℝ) : ℂ) =
          ⟪∑ d ∈ Finset.Icc 1 D,
              (invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin),
            ∑ r ∈ Finset.Icc 1 D,
              (invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed r) (hEd_orth_proj r)) u_fin)⟫_ℂ := by
        rw [← hmap, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
      rw [sum_inner] at h1
      have hterm : ∀ d ∈ Finset.Icc 1 D,
          ⟪(invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin),
            ∑ r ∈ Finset.Icc 1 D,
              (invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed r) (hEd_orth_proj r)) u_fin)⟫_ℂ =
          ((‖(invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin)‖ ^ 2 : ℝ) : ℂ) := by
        intro d hd
        rw [inner_sum, Finset.sum_eq_single d]
        · rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
        · intro r hr hrd
          exact hEd_orth_ne d r (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hr).1 hrd.symm _
            (hPX_Ed_mem d (Finset.mem_Icc.mp hd).1) _ (hPX_Ed_mem r (Finset.mem_Icc.mp hr).1)
        · intro h; exact absurd hd h
      rw [Finset.sum_congr rfl hterm, ← Complex.ofReal_sum] at h1
      exact Complex.ofReal_injective h1
    have hS_le_ufin : ‖S D u_fin‖ ^ 2 ≤ ‖u_fin‖ ^ 2 := by
      have horth : ⟪S D u_fin, u_fin - S D u_fin⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal (Md D) _).mp (hS_orth D u_fin) (S D u_fin) (hS_mem D u_fin)
      have hsplit : u_fin = S D u_fin + (u_fin - S D u_fin) := by abel
      have hpyth : ‖u_fin‖ ^ 2 = ‖S D u_fin‖ ^ 2 + ‖u_fin - S D u_fin‖ ^ 2 := by
        conv_lhs => rw [hsplit]
        rw [norm_add_sq (𝕜 := ℂ), horth]; simp
      linarith [sq_nonneg ‖u_fin - S D u_fin‖]
    have hsq : ‖(invSubspace σ X').starProjection (S D u_fin)‖ ^ 2 ≤ ((1 / Real.sqrt 2) * ‖u_fin‖) ^ 2 := by
      rw [hsq_PS, mul_pow, one_div, inv_pow, Real.sq_sqrt zero_le_two]
      calc ∑ d ∈ Finset.Icc 1 D,
            ‖(invSubspace σ X').starProjection ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin)‖ ^ 2
          ≤ ∑ d ∈ Finset.Icc 1 D, (1 / 2 : ℝ) *
              ‖(@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin‖ ^ 2 := by
            refine Finset.sum_le_sum fun d hd => hPX_Ed d (Finset.mem_Icc.mp hd).1 _ ?_ (Submodule.coe_mem _)
            rw [hY'_inv]
            change σ yJ ((@Submodule.starProjection ℂ W _ _ _ (Ed d) (hEd_orth_proj d)) u_fin) = _
            rw [← hEd_proj_comm d yJ u_fin, show σ yJ u_fin = u_fin by rwa [hY'_inv] at hu_fin_Y]
        _ = (1 / 2 : ℝ) * ‖S D u_fin‖ ^ 2 := by rw [← Finset.mul_sum, hsq_S]
        _ ≤ 2⁻¹ * ‖u_fin‖ ^ 2 := by rw [one_div]; exact mul_le_mul_of_nonneg_left hS_le_ufin (by positivity)
    have hrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt
  have hP_rem : ‖(invSubspace σ X').starProjection (u_fin - S D u_fin)‖ ≤ ‖u_fin - S D u_fin‖ := by
    have hpyth := (invSubspace σ X').norm_sq_eq_add_norm_sq_projection (u_fin - S D u_fin)
    have hsq : ‖(invSubspace σ X').starProjection (u_fin - S D u_fin)‖ ^ 2 ≤ ‖u_fin - S D u_fin‖ ^ 2 := by
      have : 0 ≤ ‖(invSubspace σ X')ᗮ.orthogonalProjectionOnto (u_fin - S D u_fin)‖ ^ 2 := sq_nonneg _
      have h1 : ‖(invSubspace σ X').orthogonalProjectionOnto (u_fin - S D u_fin)‖ =
          ‖(invSubspace σ X').starProjection (u_fin - S D u_fin)‖ := rfl
      rw [h1] at hpyth; linarith
    have hrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hrt
  have hsplit_u : u_fin = S D u_fin + (u_fin - S D u_fin) := by abel
  calc ‖(invSubspace σ X').starProjection u_fin‖
      = ‖(invSubspace σ X').starProjection (S D u_fin) + (invSubspace σ X').starProjection (u_fin - S D u_fin)‖ := by
          conv_lhs => rw [hsplit_u, map_add]
    _ ≤ ‖(invSubspace σ X').starProjection (S D u_fin)‖ + ‖(invSubspace σ X').starProjection (u_fin - S D u_fin)‖ :=
          norm_add_le _ _
    _ ≤ (1 / Real.sqrt 2) * ‖u_fin‖ + ε := add_le_add hSD_bound (hP_rem.trans hdist_S)

/-- The 6 vertices of the EJZ magic graph: ordered pairs `(i, j)` of distinct elements of `Fin 3`. -/
abbrev MagicVtx : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- The unique third index in `Fin 3` distinct from `i` and `j` (for `i ≠ j`). -/
def thirdIdx (i j : Fin 3) : Fin 3 := -(i + j)

lemma thirdIdx_ne_left {i j : Fin 3} (h : i ≠ j) : thirdIdx i j ≠ i := by
  revert i j h; decide

lemma thirdIdx_ne_right {i j : Fin 3} (h : i ≠ j) : thirdIdx i j ≠ j := by
  revert i j h; decide

lemma thirdIdx_comm (i j : Fin 3) : thirdIdx i j = thirdIdx j i := by
  dsimp only [thirdIdx]; rw [add_comm]

lemma thirdIdx_self_right {i j : Fin 3} (h : i ≠ j) : thirdIdx i (thirdIdx i j) = j := by
  revert i j h; decide

lemma thirdIdx_self_left {i j : Fin 3} (h : i ≠ j) : thirdIdx (thirdIdx i j) j = i := by
  revert i j h; decide

lemma thirdIdx_right_self {i j : Fin 3} (h : i ≠ j) : thirdIdx j (thirdIdx i j) = i := by
  revert i j h; decide

lemma thirdIdx_left_self {i j : Fin 3} (h : i ≠ j) : thirdIdx (thirdIdx i j) i = j := by
  revert i j h; decide

/-- Antipodal vertex `(j, i)` of `(i, j)` in the magic graph. -/
def magicSwap (y : MagicVtx) : MagicVtx := ⟨(y.1.2, y.1.1), y.2.symm⟩

/-- The 4 neighbors of `y` in the octahedron graph `K_{2,2,2}`: all vertices except `y` and `magicSwap y`. -/
def magicNbrs (y : MagicVtx) : Finset MagicVtx :=
  Finset.univ.filter fun y' => y' ≠ y ∧ y' ≠ magicSwap y

lemma magicNbrs_card (y : MagicVtx) : (magicNbrs y).card = 4 := by
  revert y; decide

lemma magicNbrs_symm {y y' : MagicVtx} : y' ∈ magicNbrs y ↔ y ∈ magicNbrs y' := by
  revert y y'; decide

lemma mem_magicNbrs_iff {y y' : MagicVtx} : y' ∈ magicNbrs y ↔ y' ≠ y ∧ y' ≠ magicSwap y := by
  simp [magicNbrs]

lemma magicNbrs_eq_four (i j : Fin 3) (hij : i ≠ j) :
    magicNbrs ⟨(i, j), hij⟩ =
      {⟨(i, thirdIdx i j), (thirdIdx_ne_left hij).symm⟩,
       ⟨(thirdIdx i j, j), thirdIdx_ne_right hij⟩,
       ⟨(j, thirdIdx i j), (thirdIdx_ne_right hij).symm⟩,
       ⟨(thirdIdx i j, i), thirdIdx_ne_left hij⟩} := by
  revert i j hij; decide

lemma sum_magicNbrs_eq_ite {α : Type*} [AddCommMonoid α] (y : MagicVtx) (F : MagicVtx → α) :
    ∑ y' ∈ magicNbrs y, F y' = ∑ y' : MagicVtx, if y' ∈ magicNbrs y then F y' else 0 := by
  rw [← Finset.sum_filter]
  congr 1; ext z; simp


/-- An `A₂`-system of 6 shear generators `cL i j` (`i ≠ j`) generating a group `C`. -/
structure A2Sys (C : Type) [Group C] where
  cL : Fin 3 → Fin 3 → C
  diag : ∀ i, cL i i = 1
  comm : ∀ i j k l, i ≠ l → j ≠ k → Commute (cL i j) (cL k l)
  stein : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ⁅cL i j, cL j k⁆ = cL i k
  gen : Subgroup.closure {g : C | ∃ i j : Fin 3, i ≠ j ∧ cL i j = g} = ⊤

namespace A2Sys

def Xsub {C : Type} [Group C] (A : A2Sys C) (i j : Fin 3) : Subgroup C :=
  Subgroup.closure {A.cL i j}

def Gsub {C : Type} [Group C] (A : A2Sys C) (y : MagicVtx) : Subgroup C :=
  A.Xsub y.1.1 (thirdIdx y.1.1 y.1.2) ⊔ A.Xsub (thirdIdx y.1.1 y.1.2) y.1.2

def midSubspace {C W₀ : Type} [Group C] [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) (y : MagicVtx) : Submodule ℂ W₀ :=
  invSubspace π₀ (A.Xsub y.1.1 y.1.2) ⊓ (invSubspace π₀ (A.Gsub y))ᗮ

instance instHasOrthProj_midSubspace {C W₀ : Type} [Group C] [NormedAddCommGroup W₀]
    [InnerProductSpace ℂ W₀] [CompleteSpace W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) (y : MagicVtx) :
    (A.midSubspace π₀ y).HasOrthogonalProjection :=
  hasOrthProj_of_isClosed ((isClosed_invSubspace π₀ _).inter (invSubspace π₀ _).isClosed_orthogonal)

lemma X_le_G {C : Type} [Group C] (A : A2Sys C) (y : MagicVtx) :
    A.Xsub y.1.1 y.1.2 ≤ A.Gsub y := by
  rcases y with ⟨⟨i, j⟩, hij⟩
  rw [Xsub, Subgroup.closure_le, Set.singleton_subset_iff]
  set k := thirdIdx i j
  have hik : i ≠ k := (thirdIdx_ne_left hij).symm
  have hkj : k ≠ j := thirdIdx_ne_right hij
  rw [← A.stein i k j hik hkj hij, commutatorElement_def]
  have h1 : A.cL i k ∈ A.Gsub ⟨(i, j), hij⟩ := Subgroup.mem_sup_left (Subgroup.subset_closure rfl)
  have h2 : A.cL k j ∈ A.Gsub ⟨(i, j), hij⟩ := Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) (Subgroup.inv_mem _ h1)) (Subgroup.inv_mem _ h2)

lemma X_norm_G {C : Type} [Group C] (A : A2Sys C) (i j : Fin 3) (hij : i ≠ j)
    {g : C} (hg : g ∈ A.Gsub ⟨(i, j), hij⟩) {h : C} (hh : h ∈ A.Xsub i j) :
    g * h * g⁻¹ ∈ A.Xsub i j := by
  set k := thirdIdx i j
  have hcomm_g : Commute (A.cL i j) g := by
    have hg' : g ∈ Subgroup.closure (({A.cL i k} : Set C) ∪ ({A.cL k j} : Set C)) := by
      dsimp only [Gsub, Xsub] at hg; rwa [Subgroup.closure_union]
    clear hg
    induction hg' using Subgroup.closure_induction with
    | mem u hu =>
      rcases hu with rfl | rfl
      · exact A.comm i j i k (thirdIdx_ne_left hij).symm hij.symm
      · exact A.comm i j k j hij (thirdIdx_ne_right hij).symm
    | one => exact Commute.one_right _
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  have hcomm_h : Commute h g := by
    induction hh using Subgroup.closure_induction with
    | mem u hu => rcases hu with rfl; exact hcomm_g
    | one => exact Commute.one_left _
    | mul a b _ _ ha hb => exact ha.mul_left hb
    | inv a _ ha => exact ha.inv_left
  rw [← hcomm_h.eq, mul_assoc, mul_inv_cancel, mul_one]; exact hh

lemma H1_norm_G {C : Type} [Group C] (A : A2Sys C) (i j : Fin 3) (hij : i ≠ j)
    {g : C} (hg : g ∈ A.Gsub ⟨(i, j), hij⟩) :
    (∀ h ∈ A.Xsub i (thirdIdx i j) ⊔ A.Xsub i j, g * h * g⁻¹ ∈ A.Xsub i (thirdIdx i j) ⊔ A.Xsub i j) ∧
    (∀ h ∈ A.Xsub i (thirdIdx i j) ⊔ A.Xsub i j, g⁻¹ * h * g ∈ A.Xsub i (thirdIdx i j) ⊔ A.Xsub i j) := by
  set k := thirdIdx i j
  have hg' : g ∈ Subgroup.closure (({A.cL i k} : Set C) ∪ ({A.cL k j} : Set C)) := by
    dsimp only [Gsub, Xsub] at hg; rwa [Subgroup.closure_union]
  clear hg
  have hik : i ≠ k := (thirdIdx_ne_left hij).symm
  have hkj : k ≠ j := thirdIdx_ne_right hij
  have hstep_conj : ∀ (e : C),
      (e * A.cL i k * e⁻¹ ∈ A.Xsub i k ⊔ A.Xsub i j) → (e * A.cL i j * e⁻¹ ∈ A.Xsub i k ⊔ A.Xsub i j) →
      ∀ h ∈ A.Xsub i k ⊔ A.Xsub i j, e * h * e⁻¹ ∈ A.Xsub i k ⊔ A.Xsub i j := by
    intro e he1 he2 h hh
    have hh' : h ∈ Subgroup.closure (({A.cL i k} : Set C) ∪ ({A.cL i j} : Set C)) := by
      dsimp only [Xsub] at hh; rwa [Subgroup.closure_union]
    clear hh
    induction hh' using Subgroup.closure_induction with
    | mem a ha => rcases ha with rfl | rfl; exact he1; exact he2
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show e * a⁻¹ * e⁻¹ = (e * a * e⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  induction hg' using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    · constructor
      · intro h hh
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure rfl)) hh)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure rfl)))
      · intro h hh
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))) hh)
          (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
    · have hc_kj_ij : Commute (A.cL k j) (A.cL i j) := A.comm k j i j hkj hij.symm
      constructor
      · refine hstep_conj (A.cL k j) ?_ ?_
        · have hrel : A.cL k j * A.cL i k * (A.cL k j)⁻¹ = (A.cL i j)⁻¹ * A.cL i k := by
            rw [← A.stein i k j hik hkj hij, commutatorElement_def]; group
          rw [hrel]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure rfl)))
            (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
        · rw [hc_kj_ij.eq, mul_assoc, mul_inv_cancel, mul_one]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
      · have hstep_inv := hstep_conj (A.cL k j)⁻¹
        rw [inv_inv] at hstep_inv
        refine hstep_inv ?_ ?_
        · have hrel : (A.cL k j)⁻¹ * A.cL i k * A.cL k j = A.cL i j * A.cL i k := by
            have h1 : A.cL i k * A.cL k j = A.cL i j * A.cL k j * A.cL i k := by
              rw [← A.stein i k j hik hkj hij, commutatorElement_def]; group
            calc (A.cL k j)⁻¹ * A.cL i k * A.cL k j = (A.cL k j)⁻¹ * (A.cL i k * A.cL k j) := by group
              _ = (A.cL k j)⁻¹ * (A.cL i j * A.cL k j * A.cL i k) := by rw [h1]
              _ = ((A.cL k j)⁻¹ * A.cL i j) * A.cL k j * A.cL i k := by group
              _ = (A.cL i j * (A.cL k j)⁻¹) * A.cL k j * A.cL i k := by rw [hc_kj_ij.inv_left.eq]
              _ = A.cL i j * A.cL i k := by group
          rw [hrel]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))
            (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
        · rw [hc_kj_ij.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
  | one => exact ⟨fun h hh => by simpa using hh, fun h hh => by simpa using hh⟩
  | mul a b _ _ ha hb =>
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · rw [show a * b * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ by group]; exact ha.1 _ (hb.1 h hh)
    · rw [show (a * b)⁻¹ * h * (a * b) = b⁻¹ * (a⁻¹ * h * a) * b by group]; exact hb.2 _ (ha.2 h hh)
  | inv a _ ha => exact ⟨fun h hh => by simpa using ha.2 h hh, fun h hh => by simpa using ha.1 h hh⟩

lemma H2_norm_G {C : Type} [Group C] (A : A2Sys C) (i j : Fin 3) (hij : i ≠ j)
    {g : C} (hg : g ∈ A.Gsub ⟨(i, j), hij⟩) :
    (∀ h ∈ A.Xsub (thirdIdx i j) j ⊔ A.Xsub i j, g * h * g⁻¹ ∈ A.Xsub (thirdIdx i j) j ⊔ A.Xsub i j) ∧
    (∀ h ∈ A.Xsub (thirdIdx i j) j ⊔ A.Xsub i j, g⁻¹ * h * g ∈ A.Xsub (thirdIdx i j) j ⊔ A.Xsub i j) := by
  set k := thirdIdx i j
  have hg' : g ∈ Subgroup.closure (({A.cL i k} : Set C) ∪ ({A.cL k j} : Set C)) := by
    dsimp only [Gsub, Xsub] at hg; rwa [Subgroup.closure_union]
  clear hg
  have hik : i ≠ k := (thirdIdx_ne_left hij).symm
  have hkj : k ≠ j := thirdIdx_ne_right hij
  have hstep_conj : ∀ (e : C),
      (e * A.cL k j * e⁻¹ ∈ A.Xsub k j ⊔ A.Xsub i j) → (e * A.cL i j * e⁻¹ ∈ A.Xsub k j ⊔ A.Xsub i j) →
      ∀ h ∈ A.Xsub k j ⊔ A.Xsub i j, e * h * e⁻¹ ∈ A.Xsub k j ⊔ A.Xsub i j := by
    intro e he1 he2 h hh
    have hh' : h ∈ Subgroup.closure (({A.cL k j} : Set C) ∪ ({A.cL i j} : Set C)) := by
      dsimp only [Xsub] at hh; rwa [Subgroup.closure_union]
    clear hh
    induction hh' using Subgroup.closure_induction with
    | mem a ha => rcases ha with rfl | rfl; exact he1; exact he2
    | one => simp
    | mul a b _ _ ha hb =>
      rw [show e * (a * b) * e⁻¹ = (e * a * e⁻¹) * (e * b * e⁻¹) by group]
      exact Subgroup.mul_mem _ ha hb
    | inv a _ ha =>
      rw [show e * a⁻¹ * e⁻¹ = (e * a * e⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ ha
  induction hg' using Subgroup.closure_induction with
  | mem u hu =>
    rcases hu with rfl | rfl
    · have hc_ik_ij : Commute (A.cL i k) (A.cL i j) := A.comm i k i j hij hik.symm
      constructor
      · refine hstep_conj (A.cL i k) ?_ ?_
        · have hrel : A.cL i k * A.cL k j * (A.cL i k)⁻¹ = A.cL i j * A.cL k j := by
            rw [← A.stein i k j hik hkj hij, commutatorElement_def]; group
          rw [hrel]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure rfl))
            (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
        · rw [hc_ik_ij.eq, mul_assoc, mul_inv_cancel, mul_one]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
      · have hstep_inv := hstep_conj (A.cL i k)⁻¹
        rw [inv_inv] at hstep_inv
        refine hstep_inv ?_ ?_
        · have hrel : (A.cL i k)⁻¹ * A.cL k j * A.cL i k = (A.cL i j)⁻¹ * A.cL k j := by
            have h1 : A.cL k j * A.cL i k = (A.cL i j)⁻¹ * A.cL i k * A.cL k j := by
              rw [← A.stein i k j hik hkj hij, commutatorElement_def]; group
            calc (A.cL i k)⁻¹ * A.cL k j * A.cL i k = (A.cL i k)⁻¹ * (A.cL k j * A.cL i k) := by group
              _ = (A.cL i k)⁻¹ * ((A.cL i j)⁻¹ * A.cL i k * A.cL k j) := by rw [h1]
              _ = ((A.cL i k)⁻¹ * (A.cL i j)⁻¹) * A.cL i k * A.cL k j := by group
              _ = ((A.cL i j)⁻¹ * (A.cL i k)⁻¹) * A.cL i k * A.cL k j := by rw [hc_ik_ij.inv_left.inv_right.eq]
              _ = (A.cL i j)⁻¹ * A.cL k j := by group
          rw [hrel]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.subset_closure rfl)))
            (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
        · rw [hc_ik_ij.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
          exact Subgroup.mem_sup_right (Subgroup.subset_closure rfl)
    · constructor
      · intro h hh
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure rfl)) hh)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure rfl)))
      · intro h hh
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))) hh)
          (Subgroup.mem_sup_left (Subgroup.subset_closure rfl))
  | one => exact ⟨fun h hh => by simpa using hh, fun h hh => by simpa using hh⟩
  | mul a b _ _ ha hb =>
    refine ⟨fun h hh => ?_, fun h hh => ?_⟩
    · rw [show a * b * h * (a * b)⁻¹ = a * (b * h * b⁻¹) * a⁻¹ by group]; exact ha.1 _ (hb.1 h hh)
    · rw [show (a * b)⁻¹ * h * (a * b) = b⁻¹ * (a⁻¹ * h * a) * b by group]; exact hb.2 _ (ha.2 h hh)
  | inv a _ ha => exact ⟨fun h hh => by simpa using ha.2 h hh, fun h hh => by simpa using ha.1 h hh⟩

lemma H12_orth {C W₀ : Type} [Group C] [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    [CompleteSpace W₀] (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀)
    (y : MagicVtx) {u₁ u₂ : W₀}
    (hu₁ : u₁ ∈ invSubspace π₀ (A.Xsub y.1.1 (thirdIdx y.1.1 y.1.2) ⊔ A.Xsub y.1.1 y.1.2))
    (hu₂ : u₂ ∈ invSubspace π₀ (A.Xsub (thirdIdx y.1.1 y.1.2) y.1.2 ⊔ A.Xsub y.1.1 y.1.2))
    (ho₁ : u₁ ∈ (invSubspace π₀ (A.Gsub y))ᗮ) (ho₂ : u₂ ∈ (invSubspace π₀ (A.Gsub y))ᗮ) :
    ⟪u₁, u₂⟫_ℂ = 0 := by
  rcases y with ⟨⟨i, j⟩, hij⟩
  set k := thirdIdx i j
  set H₁ := A.Xsub i k ⊔ A.Xsub i j
  set H₂ := A.Xsub k j ⊔ A.Xsub i j
  have hsup : H₁ ⊔ H₂ = A.Gsub ⟨(i, j), hij⟩ := by
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left (A.X_le_G ⟨(i, j), hij⟩))
        (sup_le le_sup_right (A.X_le_G ⟨(i, j), hij⟩))
    · exact sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_right le_sup_left)
  let K := (invSubspace π₀ (A.Gsub ⟨(i, j), hij⟩))ᗮ
  have hK_inv : ∀ (g : A.Gsub ⟨(i, j), hij⟩) (w : W₀), w ∈ K → π₀ g.1 w ∈ K := fun g w hw =>
    invSubspace_orth_mem_of_norm π₀ (fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2 hh) (Subgroup.inv_mem _ g.2)) hw
  let σG : A.Gsub ⟨(i, j), hij⟩ →* K ≃ₗᵢ[ℂ] K := restrictRep (π₀.comp (A.Gsub ⟨(i, j), hij⟩).subtype) K hK_inv
  let H₁' : Subgroup (A.Gsub ⟨(i, j), hij⟩) := H₁.comap (A.Gsub ⟨(i, j), hij⟩).subtype
  let H₂' : Subgroup (A.Gsub ⟨(i, j), hij⟩) := H₂.comap (A.Gsub ⟨(i, j), hij⟩).subtype
  have : H₁'.Normal := ⟨fun n hn g => (A.H1_norm_G i j hij g.2).1 n hn⟩
  have : H₂'.Normal := ⟨fun n hn g => (A.H2_norm_G i j hij g.2).1 n hn⟩
  have hgen' : H₁' ⊔ H₂' = ⊤ := by
    have hsub : ∀ z (hz : z ∈ Subgroup.closure ((H₁ : Set C) ∪ (H₂ : Set C)))
        (hzG : z ∈ A.Gsub ⟨(i, j), hij⟩), (⟨z, hzG⟩ : A.Gsub ⟨(i, j), hij⟩) ∈ H₁' ⊔ H₂' := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem a ha =>
        intro _; rcases ha with ha | ha
        · exact Subgroup.mem_sup_left ha
        · exact Subgroup.mem_sup_right ha
      | one => intro _; exact Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
        intro _
        exact Subgroup.mul_mem _ (iha (hsup ▸ Subgroup.sup_eq_closure H₁ H₂ ▸ ha))
          (ihb (hsup ▸ Subgroup.sup_eq_closure H₁ H₂ ▸ hb))
      | inv a ha iha =>
        intro _
        exact Subgroup.inv_mem _ (iha (hsup ▸ Subgroup.sup_eq_closure H₁ H₂ ▸ ha))
    rw [eq_top_iff]; rintro ⟨z, hz⟩ _
    exact hsub z (by rw [← Subgroup.sup_eq_closure, hsup]; exact hz) hz
  have htrivG : invSubspace σG ⊤ = ⊥ := by
    ext u; simp only [Submodule.mem_bot]
    constructor
    · intro h; apply Subtype.ext
      have hwG : u.1 ∈ invSubspace π₀ (A.Gsub ⟨(i, j), hij⟩) := fun g hg => congrArg Subtype.val (h ⟨g, hg⟩ trivial)
      exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal _ u.1).mp u.2 u.1 hwG)
    · rintro rfl g _; exact map_zero _
  have hnorm' : ∀ k ∈ H₂', ∀ h ∈ H₁', k⁻¹ * h * k ∈ H₁' ∧ k * h * k⁻¹ ∈ H₁' :=
    fun k _ h hh => ⟨(A.H1_norm_G i j hij k.2).2 h hh, (A.H1_norm_G i j hij k.2).1 h hh⟩
  have h0 := orth_normal_subgroups σG hgen' hnorm' htrivG
  have hu₁' : (⟨u₁, ho₁⟩ : K) ∈ invSubspace σG H₁' := fun g hg => Subtype.ext (hu₁ g.1 hg)
  have hu₂' : (⟨u₂, ho₂⟩ : K) ∈ invSubspace σG H₂' := fun g hg => Subtype.ext (hu₂ g.1 hg)
  have hzero := h0 ⟨u₁, ho₁⟩ hu₁' ⟨u₂, ho₂⟩ hu₂'
  simp only [zero_mul, norm_le_zero_iff] at hzero
  exact hzero

/-- EJZ Claim 5.7 (`rho`): local edge-sum bounds at each vertex `y : MagicVtx`. -/
lemma claim_rho {C W₀ : Type} [Group C] [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    [CompleteSpace W₀] (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀)
    (y : MagicVtx) (f : MagicVtx → W₀)
    (hf : ∀ y' ∈ magicNbrs y, f y' ∈ invSubspace π₀ (A.Gsub y ⊓ A.Gsub y')) :
    ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection (∑ y' ∈ magicNbrs y, f y')‖ ^ 2 ≤
      (1 + 1 / Real.sqrt 2) * ∑ y' ∈ magicNbrs y, ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection (f y')‖ ^ 2 ∧
    ‖(A.midSubspace π₀ y).starProjection (∑ y' ∈ magicNbrs y, f y')‖ ^ 2 ≤
      2 * ∑ y' ∈ magicNbrs y, ‖(A.midSubspace π₀ y).starProjection (f y')‖ ^ 2 := by
  rcases y with ⟨⟨i, j⟩, hij⟩
  set y : MagicVtx := ⟨(i, j), hij⟩
  set k := thirdIdx i j
  have hik : i ≠ k := (thirdIdx_ne_left hij).symm
  have hkj : k ≠ j := thirdIdx_ne_right hij
  let y1 : MagicVtx := ⟨(i, k), hik⟩
  let y2 : MagicVtx := ⟨(k, j), hkj⟩
  let y3 : MagicVtx := ⟨(j, k), hkj.symm⟩
  let y4 : MagicVtx := ⟨(k, i), hik.symm⟩
  have hnbrs_eq : magicNbrs y = {y1, y2, y3, y4} := magicNbrs_eq_four i j hij
  have hne12 : y1 ≠ y2 := fun h => hik (congrArg (fun t => t.1.1) h)
  have hne13 : y1 ≠ y3 := fun h => hij (congrArg (fun t => t.1.1) h)
  have hne14 : y1 ≠ y4 := fun h => hik (congrArg (fun t => t.1.1) h)
  have hne23 : y2 ≠ y3 := fun h => hkj (congrArg (fun t => t.1.1) h)
  have hne24 : y2 ≠ y4 := fun h => hij.symm (congrArg (fun t => t.1.2) h)
  have hne34 : y3 ≠ y4 := fun h => hkj.symm (congrArg (fun t => t.1.1) h)
  have hsum4 : ∀ (F : MagicVtx → W₀), ∑ y' ∈ magicNbrs y, F y' = F y1 + F y2 + F y3 + F y4 := fun F => by
    rw [hnbrs_eq, Finset.sum_insert (by simp [hne12, hne13, hne14]),
      Finset.sum_insert (by simp [hne23, hne24]),
      Finset.sum_insert (by simp [hne34]), Finset.sum_singleton]; abel
  have hsum4_real : ∀ (F : MagicVtx → ℝ), ∑ y' ∈ magicNbrs y, F y' = F y1 + F y2 + F y3 + F y4 := fun F => by
    rw [hnbrs_eq, Finset.sum_insert (by simp [hne12, hne13, hne14]),
      Finset.sum_insert (by simp [hne23, hne24]),
      Finset.sum_insert (by simp [hne34]), Finset.sum_singleton]; ring
  have hH1_le : A.Xsub i k ⊔ A.Xsub i j ≤ A.Gsub y ⊓ A.Gsub y1 := by
    refine le_inf (sup_le le_sup_left (A.X_le_G y)) (sup_le (A.X_le_G y1) ?_)
    have htk : thirdIdx i k = j := thirdIdx_self_right hij
    change A.Xsub i j ≤ A.Xsub i (thirdIdx i k) ⊔ A.Xsub (thirdIdx i k) k
    rw [htk]; exact le_sup_left
  have hH2_le : A.Xsub k j ⊔ A.Xsub i j ≤ A.Gsub y ⊓ A.Gsub y2 := by
    refine le_inf (sup_le le_sup_right (A.X_le_G y)) (sup_le (A.X_le_G y2) ?_)
    have htk : thirdIdx k j = i := thirdIdx_self_left hij
    change A.Xsub i j ≤ A.Xsub k (thirdIdx k j) ⊔ A.Xsub (thirdIdx k j) j
    rw [htk]; exact le_sup_right
  have hH3_le : A.Xsub i k ≤ A.Gsub y ⊓ A.Gsub y3 := by
    refine le_inf le_sup_left ?_
    have htk : thirdIdx j k = i := thirdIdx_right_self hij
    change A.Xsub i k ≤ A.Xsub j (thirdIdx j k) ⊔ A.Xsub (thirdIdx j k) k
    rw [htk]; exact le_sup_right
  have hH4_le : A.Xsub k j ≤ A.Gsub y ⊓ A.Gsub y4 := by
    refine le_inf le_sup_right ?_
    have htk : thirdIdx k i = j := thirdIdx_left_self hij
    change A.Xsub k j ≤ A.Xsub k (thirdIdx k i) ⊔ A.Xsub (thirdIdx k i) i
    rw [htk]; exact le_sup_left
  have hf1 : f y1 ∈ invSubspace π₀ (A.Xsub i k ⊔ A.Xsub i j) :=
    invSubspace_anti π₀ hH1_le (hf y1 (by rw [hnbrs_eq]; simp))
  have hf2 : f y2 ∈ invSubspace π₀ (A.Xsub k j ⊔ A.Xsub i j) :=
    invSubspace_anti π₀ hH2_le (hf y2 (by rw [hnbrs_eq]; simp))
  have hf3 : f y3 ∈ invSubspace π₀ (A.Xsub i k) :=
    invSubspace_anti π₀ hH3_le (hf y3 (by rw [hnbrs_eq]; simp))
  have hf4 : f y4 ∈ invSubspace π₀ (A.Xsub k j) :=
    invSubspace_anti π₀ hH4_le (hf y4 (by rw [hnbrs_eq]; simp))
  have hPX_comm : ∀ g ∈ A.Gsub y, ∀ w : W₀,
      (invSubspace π₀ (A.Xsub i j)).starProjection (π₀ g w) = π₀ g ((invSubspace π₀ (A.Xsub i j)).starProjection w) :=
    fun g hg w => starProjection_invSubspace_comm π₀
      (fun h hh => by simpa using A.X_norm_G i j hij (Subgroup.inv_mem _ hg) hh)
      (fun h hh => A.X_norm_G i j hij hg hh) w
  have hPX'_comm : ∀ g ∈ A.Gsub y, ∀ w : W₀,
      (invSubspace π₀ (A.Xsub i j))ᗮ.starProjection (π₀ g w) = π₀ g ((invSubspace π₀ (A.Xsub i j))ᗮ.starProjection w) := by
    intro g hg w
    rw [(invSubspace π₀ (A.Xsub i j)).starProjection_orthogonal_val,
      (invSubspace π₀ (A.Xsub i j)).starProjection_orthogonal_val, map_sub, hPX_comm g hg w]
  have hPG_comm : ∀ g ∈ A.Gsub y, ∀ w : W₀,
      (invSubspace π₀ (A.Gsub y)).starProjection (π₀ g w) = π₀ g ((invSubspace π₀ (A.Gsub y)).starProjection w) :=
    fun g hg w => starProjection_invSubspace_comm π₀
      (fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hh) hg)
      (fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hh) (Subgroup.inv_mem _ hg)) w
  have hPG'_comm : ∀ g ∈ A.Gsub y, ∀ w : W₀,
      (invSubspace π₀ (A.Gsub y))ᗮ.starProjection (π₀ g w) = π₀ g ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w) := by
    intro g hg w
    rw [(invSubspace π₀ (A.Gsub y)).starProjection_orthogonal_val,
      (invSubspace π₀ (A.Gsub y)).starProjection_orthogonal_val, map_sub, hPG_comm g hg w]
  have hPM_eq : ∀ w : W₀,
      (A.midSubspace π₀ y).starProjection w =
        (invSubspace π₀ (A.Xsub i j)).starProjection ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w) := by
    intro w
    refine (A.midSubspace π₀ y).eq_starProjection_of_mem_orthogonal ?_ ?_
    · refine ⟨Submodule.coe_mem _, ?_⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]; intro u hu
      have huX : u ∈ invSubspace π₀ (A.Xsub i j) := invSubspace_anti π₀ (A.X_le_G y) hu
      have h1 : ⟪u, (invSubspace π₀ (A.Gsub y))ᗮ.starProjection w -
          (invSubspace π₀ (A.Xsub i j)).starProjection ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w)⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp ((invSubspace π₀ (A.Xsub i j)).sub_starProjection_mem_orthogonal _) u huX
      have h2 : ⟪u, (invSubspace π₀ (A.Gsub y))ᗮ.starProjection w⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp (Submodule.coe_mem _) u hu
      rw [inner_sub_right, h2, zero_sub, neg_eq_zero] at h1; exact h1
    · rw [Submodule.mem_orthogonal]; intro u ⟨huX, huG'⟩
      have h1 : ⟪u, w - (invSubspace π₀ (A.Gsub y))ᗮ.starProjection w⟫_ℂ = 0 := by
        rw [(invSubspace π₀ (A.Gsub y)).starProjection_orthogonal_val, sub_sub_cancel]
        have : ⟪(invSubspace π₀ (A.Gsub y)).starProjection w, u⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal _ _).mp huG' _ (Submodule.coe_mem _)
        rw [← inner_conj_symm, this, map_zero]
      have h2 : ⟪u, (invSubspace π₀ (A.Gsub y))ᗮ.starProjection w -
          (invSubspace π₀ (A.Xsub i j)).starProjection ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w)⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp ((invSubspace π₀ (A.Xsub i j)).sub_starProjection_mem_orthogonal _) u huX
      have hsplit : w - (invSubspace π₀ (A.Xsub i j)).starProjection ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w) =
          (w - (invSubspace π₀ (A.Gsub y))ᗮ.starProjection w) +
          ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w -
            (invSubspace π₀ (A.Xsub i j)).starProjection ((invSubspace π₀ (A.Gsub y))ᗮ.starProjection w)) := by abel
      rw [hsplit, inner_add_right, h1, h2, add_zero]
  constructor
  · set P1 := (invSubspace π₀ (A.Xsub i j))ᗮ.starProjection
    rw [map_sum, hsum4, hsum4_real]
    have hp1 : P1 (f y1) = 0 := by
      refine (invSubspace π₀ (A.Xsub i j))ᗮ.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
      rw [sub_zero, Submodule.orthogonal_orthogonal]; exact invSubspace_anti π₀ le_sup_right hf1
    have hp2 : P1 (f y2) = 0 := by
      refine (invSubspace π₀ (A.Xsub i j))ᗮ.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
      rw [sub_zero, Submodule.orthogonal_orthogonal]; exact invSubspace_anti π₀ le_sup_right hf2
    rw [hp1, hp2, zero_add, zero_add]
    have hX_norm_le : ∀ w : W₀, ∀ H : Subgroup C, H ≤ A.Gsub y → w ∈ invSubspace π₀ H → P1 w ∈ invSubspace π₀ H :=
      fun w H hHG hw g hg => by rw [← hPX'_comm g (hHG hg) w, hw g hg]
    have hc_mem : P1 (f y3) ∈ invSubspace π₀ (A.Xsub i k) ⊓ (invSubspace π₀ (A.Gsub y))ᗮ :=
      ⟨hX_norm_le (f y3) (A.Xsub i k) le_sup_left hf3,
        Submodule.orthogonal_le (invSubspace_anti π₀ (A.X_le_G y)) (Submodule.coe_mem _)⟩
    have hd_mem : P1 (f y4) ∈ invSubspace π₀ (A.Xsub k j) ⊓ (invSubspace π₀ (A.Gsub y))ᗮ :=
      ⟨hX_norm_le (f y4) (A.Xsub k j) le_sup_right hf4,
        Submodule.orthogonal_le (invSubspace_anti π₀ (A.X_le_G y)) (Submodule.coe_mem _)⟩
    have hheis : SubgroupEpsOrth (A.Xsub i k) (A.Xsub k j) (1 / Real.sqrt 2) :=
      heisenberg_epsOrth (A.cL i k) (A.cL k j)
        (by rw [A.stein i k j hik hkj hij]; exact A.comm i j i k hik hij.symm)
        (by rw [A.stein i k j hik hkj hij]; exact A.comm i j k j hij hkj.symm)
    have horth_cd : ‖⟪P1 (f y3), P1 (f y4)⟫_ℂ‖ ≤ (1 / Real.sqrt 2) * ‖P1 (f y3)‖ * ‖P1 (f y4)‖ :=
      subgroupEpsOrth_on_orth π₀ hheis _ hc_mem _ hd_mem
    have hadd : ‖P1 (f y3) + P1 (f y4)‖ ^ 2 ≤ (1 + 1 / Real.sqrt 2) * (‖P1 (f y3)‖ ^ 2 + ‖P1 (f y4)‖ ^ 2) := by
      have h1 : ‖P1 (f y3) + P1 (f y4)‖ ^ 2 =
          ‖P1 (f y3)‖ ^ 2 + 2 * RCLike.re ⟪P1 (f y3), P1 (f y4)⟫_ℂ + ‖P1 (f y4)‖ ^ 2 := norm_add_sq (𝕜 := ℂ) _ _
      have h2 : RCLike.re ⟪P1 (f y3), P1 (f y4)⟫_ℂ ≤ (1 / Real.sqrt 2) * ‖P1 (f y3)‖ * ‖P1 (f y4)‖ :=
        (RCLike.re_le_norm _).trans horth_cd
      have h3 : 2 * (‖P1 (f y3)‖ * ‖P1 (f y4)‖) ≤ ‖P1 (f y3)‖ ^ 2 + ‖P1 (f y4)‖ ^ 2 := by
        nlinarith [sq_nonneg (‖P1 (f y3)‖ - ‖P1 (f y4)‖)]
      have hpos : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
      nlinarith
    nlinarith [sq_nonneg ‖(0 : W₀)‖, show (0 : ℝ) ≤ 1 + 1 / Real.sqrt 2 by positivity]
  · set P2 := (A.midSubspace π₀ y).starProjection
    rw [map_sum, hsum4, hsum4_real]
    have hP2_mem : ∀ w : W₀, ∀ H : Subgroup C, H ≤ A.Gsub y → w ∈ invSubspace π₀ H →
        P2 w ∈ invSubspace π₀ (H ⊔ A.Xsub i j) ∧ P2 w ∈ (invSubspace π₀ (A.Gsub y))ᗮ := by
      intro w H hHG hw
      have hmem_M : P2 w ∈ A.midSubspace π₀ y := Submodule.coe_mem _
      refine ⟨?_, hmem_M.2⟩
      rw [invSubspace_sup]
      refine ⟨fun g hg => ?_, hmem_M.1⟩
      rw [hPM_eq w, ← hPX_comm g (hHG hg), ← hPG'_comm g (hHG hg), hw g hg]
    have ha_m := hP2_mem (f y1) (A.Xsub i k ⊔ A.Xsub i j) (sup_le le_sup_left (A.X_le_G y)) hf1
    have hb_m := hP2_mem (f y2) (A.Xsub k j ⊔ A.Xsub i j) (sup_le le_sup_right (A.X_le_G y)) hf2
    have hc_m := hP2_mem (f y3) (A.Xsub i k) le_sup_left hf3
    have hd_m := hP2_mem (f y4) (A.Xsub k j) le_sup_right hf4
    have horth : ⟪P2 (f y1) + P2 (f y3), P2 (f y2) + P2 (f y4)⟫_ℂ = 0 :=
      A.H12_orth π₀ y
        (Submodule.add_mem _ (invSubspace_anti π₀ le_sup_left ha_m.1) hc_m.1)
        (Submodule.add_mem _ (invSubspace_anti π₀ le_sup_left hb_m.1) hd_m.1)
        (Submodule.add_mem _ ha_m.2 hc_m.2) (Submodule.add_mem _ hb_m.2 hd_m.2)
    have hsplit : P2 (f y1) + P2 (f y2) + P2 (f y3) + P2 (f y4) =
        (P2 (f y1) + P2 (f y3)) + (P2 (f y2) + P2 (f y4)) := by abel
    rw [hsplit, norm_add_sq (𝕜 := ℂ), horth, map_zero, mul_zero, add_zero]
    have hle1 : ‖P2 (f y1) + P2 (f y3)‖ ^ 2 ≤ 2 * (‖P2 (f y1)‖ ^ 2 + ‖P2 (f y3)‖ ^ 2) := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (P2 (f y1)) (P2 (f y3))) 2
      nlinarith [sq_nonneg (‖P2 (f y1)‖ - ‖P2 (f y3)‖)]
    have hle2 : ‖P2 (f y2) + P2 (f y4)‖ ^ 2 ≤ 2 * (‖P2 (f y2)‖ ^ 2 + ‖P2 (f y4)‖ ^ 2) := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (P2 (f y2)) (P2 (f y4))) 2
      nlinarith [sq_nonneg (‖P2 (f y2)‖ - ‖P2 (f y4)‖)]
    linarith

/-- EJZ Claim 5.8(a) (`bounds (a)`): `D ≤ 3 d₁ + 5 d₃` for any `g : MagicVtx → W₀`
satisfying the edge-invariance condition `g y - g y' ∈ V^{G_y ⊓ G_{y'}}`. -/
lemma claim_a {C W₀ : Type} [Group C] [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    [CompleteSpace W₀] (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) (g : MagicVtx → W₀)
    (hg : ∀ y : MagicVtx, ∀ y' ∈ magicNbrs y, g y - g y' ∈ invSubspace π₀ (A.Gsub y ⊓ A.Gsub y')) :
    (1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖g y - g y'‖ ^ 2 ≤
      3 * ((1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y,
        ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection (g y - g y')‖ ^ 2) +
      5 * ((1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y,
        ‖(invSubspace π₀ (A.Gsub y)).starProjection (g y - g y')‖ ^ 2) := by
  let P1 : MagicVtx → W₀ →L[ℂ] W₀ := fun y => (invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection
  let P3 : MagicVtx → W₀ →L[ℂ] W₀ := fun y => (invSubspace π₀ (A.Gsub y)).starProjection
  have htriple : ∀ (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      let vik : MagicVtx := ⟨(i, k), hik⟩
      let vjk : MagicVtx := ⟨(j, k), hjk⟩
      let vij : MagicVtx := ⟨(i, j), hij⟩
      ‖g vik - g vjk‖ ^ 2 + ‖g vik - g vij‖ ^ 2 + 2 * ‖g vij - g vjk‖ ^ 2 ≤
        5 * (‖P3 vik (g vik - g vjk)‖ ^ 2 + ‖P3 vik (g vik - g vij)‖ ^ 2) +
        3 * (‖P1 vij (g vij - g vjk)‖ ^ 2 + ‖P1 vjk (g vjk - g vij)‖ ^ 2) := by
    intro i j k hij hjk hik vik vjk vij
    have hthird_ik : thirdIdx i k = j := by revert i j k hij hjk hik; decide
    have hthird_jk : thirdIdx j k = i := by revert i j k hij hjk hik; decide
    have hthird_ij : thirdIdx i j = k := by revert i j k hij hjk hik; decide
    have hGik_eq : A.Gsub vik = A.Xsub i j ⊔ A.Xsub j k := by
      change A.Xsub i (thirdIdx i k) ⊔ A.Xsub (thirdIdx i k) k = _; rw [hthird_ik]
    have hz1_mem : g vik - g vjk ∈ invSubspace π₀ (A.Xsub i k ⊔ A.Xsub j k) := by
      have hvjk_nbr : vjk ∈ magicNbrs vik := by
        rw [mem_magicNbrs_iff]
        exact ⟨fun h => hij.symm (congrArg (fun t => t.1.1) h), fun h => hik.symm (congrArg (fun t => t.1.2) h)⟩
      have hsub : A.Xsub i k ⊔ A.Xsub j k ≤ A.Gsub vik ⊓ A.Gsub vjk := by
        refine le_inf (sup_le (A.X_le_G vik) (hGik_eq ▸ le_sup_right)) (sup_le ?_ (A.X_le_G vjk))
        change A.Xsub i k ≤ A.Xsub j (thirdIdx j k) ⊔ A.Xsub (thirdIdx j k) k
        rw [hthird_jk]; exact le_sup_right
      exact invSubspace_anti π₀ hsub (hg vik vjk hvjk_nbr)
    have hz2_mem : g vik - g vij ∈ invSubspace π₀ (A.Xsub i k ⊔ A.Xsub i j) := by
      have hvij_nbr : vij ∈ magicNbrs vik := by
        rw [mem_magicNbrs_iff]
        exact ⟨fun h => hjk (congrArg (fun t => t.1.2) h), fun h => hik (congrArg (fun t => t.1.1) h)⟩
      have hsub : A.Xsub i k ⊔ A.Xsub i j ≤ A.Gsub vik ⊓ A.Gsub vij := by
        refine le_inf (sup_le (A.X_le_G vik) (hGik_eq ▸ le_sup_left)) (sup_le ?_ (A.X_le_G vij))
        change A.Xsub i k ≤ A.Xsub i (thirdIdx i j) ⊔ A.Xsub (thirdIdx i j) j
        rw [hthird_ij]; exact le_sup_left
      exact invSubspace_anti π₀ hsub (hg vik vij hvij_nbr)
    have hP_z1 : (invSubspace π₀ (A.Xsub i j)).starProjection (g vik - g vjk) = P3 vik (g vik - g vjk) := by
      set z := g vik - g vjk
      have hp_mem_ik : (invSubspace π₀ (A.Xsub i j)).starProjection z ∈ invSubspace π₀ (A.Xsub i j ⊔ A.Xsub i k) := by
        rw [invSubspace_sup]
        refine ⟨Submodule.coe_mem _, fun a ha => ?_⟩
        have hcomm_a : ∀ b ∈ A.Xsub i j, Commute a b := fun b hb => by
          induction ha using Subgroup.closure_induction with
          | mem u hu =>
            rcases hu with rfl
            induction hb using Subgroup.closure_induction with
            | mem w hw => rcases hw with rfl; exact A.comm i k i j hij hik.symm
            | one => exact Commute.one_right _
            | mul x y _ _ hx hy => exact hx.mul_right hy
            | inv x _ hx => exact hx.inv_right
          | one => exact Commute.one_left _
          | mul x y _ _ hx hy => exact hx.mul_left hy
          | inv x _ hx => exact hx.inv_left
        have hcomm_proj := starProjection_invSubspace_comm π₀
          (fun b hb => by rw [(hcomm_a b hb).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]; exact hb)
          (fun b hb => by rw [(hcomm_a b hb).eq, mul_assoc, mul_inv_cancel, mul_one]; exact hb) z
        rw [← hcomm_proj, (invSubspace_anti π₀ le_sup_left hz1_mem) a ha]
      have hp_eq_ij_ik : (invSubspace π₀ (A.Xsub i j)).starProjection z =
          (invSubspace π₀ (A.Xsub i j ⊔ A.Xsub i k)).starProjection z := by
        symm; refine (invSubspace π₀ (A.Xsub i j ⊔ A.Xsub i k)).eq_starProjection_of_mem_orthogonal hp_mem_ik ?_
        exact Submodule.orthogonal_le (invSubspace_anti π₀ le_sup_left)
          ((invSubspace π₀ (A.Xsub i j)).sub_starProjection_mem_orthogonal z)
      have hp_mem_G : (invSubspace π₀ (A.Xsub i j ⊔ A.Xsub i k)).starProjection z ∈ invSubspace π₀ (A.Gsub vik) := by
        rw [hGik_eq, invSubspace_sup]
        refine ⟨invSubspace_anti π₀ le_sup_left (Submodule.coe_mem _), fun a ha => ?_⟩
        have haG : a ∈ A.Gsub vik := hGik_eq ▸ Subgroup.mem_sup_right ha
        have hnorm := A.H1_norm_G i k hik haG
        rw [hthird_ik] at hnorm
        have hcomm_proj := starProjection_invSubspace_comm π₀ hnorm.2 hnorm.1 z
        rw [← hcomm_proj, (invSubspace_anti π₀ le_sup_right hz1_mem) a ha]
      rw [hp_eq_ij_ik]
      symm; refine (invSubspace π₀ (A.Gsub vik)).eq_starProjection_of_mem_orthogonal hp_mem_G ?_
      exact Submodule.orthogonal_le (invSubspace_anti π₀ (sup_le (hGik_eq ▸ le_sup_left) (A.X_le_G vik)))
        ((invSubspace π₀ (A.Xsub i j ⊔ A.Xsub i k)).sub_starProjection_mem_orthogonal z)
    have hP_z2 : (invSubspace π₀ (A.Xsub j k)).starProjection (g vik - g vij) = P3 vik (g vik - g vij) := by
      set z := g vik - g vij
      have hp_mem_ik : (invSubspace π₀ (A.Xsub j k)).starProjection z ∈ invSubspace π₀ (A.Xsub j k ⊔ A.Xsub i k) := by
        rw [invSubspace_sup]
        refine ⟨Submodule.coe_mem _, fun a ha => ?_⟩
        have hcomm_a : ∀ b ∈ A.Xsub j k, Commute a b := fun b hb => by
          induction ha using Subgroup.closure_induction with
          | mem u hu =>
            rcases hu with rfl
            induction hb using Subgroup.closure_induction with
            | mem w hw => rcases hw with rfl; exact A.comm i k j k hik hjk.symm
            | one => exact Commute.one_right _
            | mul x y _ _ hx hy => exact hx.mul_right hy
            | inv x _ hx => exact hx.inv_right
          | one => exact Commute.one_left _
          | mul x y _ _ hx hy => exact hx.mul_left hy
          | inv x _ hx => exact hx.inv_left
        have hcomm_proj := starProjection_invSubspace_comm π₀
          (fun b hb => by rw [(hcomm_a b hb).inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]; exact hb)
          (fun b hb => by rw [(hcomm_a b hb).eq, mul_assoc, mul_inv_cancel, mul_one]; exact hb) z
        rw [← hcomm_proj, (invSubspace_anti π₀ le_sup_left hz2_mem) a ha]
      have hp_eq_jk_ik : (invSubspace π₀ (A.Xsub j k)).starProjection z =
          (invSubspace π₀ (A.Xsub j k ⊔ A.Xsub i k)).starProjection z := by
        symm; refine (invSubspace π₀ (A.Xsub j k ⊔ A.Xsub i k)).eq_starProjection_of_mem_orthogonal hp_mem_ik ?_
        exact Submodule.orthogonal_le (invSubspace_anti π₀ le_sup_left)
          ((invSubspace π₀ (A.Xsub j k)).sub_starProjection_mem_orthogonal z)
      have hp_mem_G : (invSubspace π₀ (A.Xsub j k ⊔ A.Xsub i k)).starProjection z ∈ invSubspace π₀ (A.Gsub vik) := by
        rw [hGik_eq, invSubspace_sup]
        refine ⟨fun a ha => ?_, invSubspace_anti π₀ le_sup_left (Submodule.coe_mem _)⟩
        have haG : a ∈ A.Gsub vik := hGik_eq ▸ Subgroup.mem_sup_left ha
        have hnorm := A.H2_norm_G i k hik haG
        rw [hthird_ik] at hnorm
        have hcomm_proj := starProjection_invSubspace_comm π₀ hnorm.2 hnorm.1 z
        rw [← hcomm_proj, (invSubspace_anti π₀ le_sup_right hz2_mem) a ha]
      rw [hp_eq_jk_ik]
      symm; refine (invSubspace π₀ (A.Gsub vik)).eq_starProjection_of_mem_orthogonal hp_mem_G ?_
      exact Submodule.orthogonal_le (invSubspace_anti π₀ (sup_le (hGik_eq ▸ le_sup_right) (A.X_le_G vik)))
        ((invSubspace π₀ (A.Xsub j k ⊔ A.Xsub i k)).sub_starProjection_mem_orthogonal z)
    have hest1 : ‖g vik - g vjk‖ ^ 2 = ‖P3 vik (g vik - g vjk)‖ ^ 2 + ‖P1 vij (g vij - g vjk)‖ ^ 2 := by
      have h1 := (invSubspace π₀ (A.Xsub i j)).norm_sq_eq_add_norm_sq_projection (g vik - g vjk)
      have h2 : P1 vij (g vik - g vjk) = P1 vij (g vij - g vjk) := by
        have hs : g vik - g vjk = (g vik - g vij) + (g vij - g vjk) := by abel
        rw [hs, map_add]
        have h0 : P1 vij (g vik - g vij) = 0 := by
          refine (invSubspace π₀ (A.Xsub i j))ᗮ.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
          rw [sub_zero, Submodule.orthogonal_orthogonal]; exact invSubspace_anti π₀ le_sup_right hz2_mem
        rw [h0, zero_add]
      have h3 : ‖(invSubspace π₀ (A.Xsub i j)).orthogonalProjectionOnto (g vik - g vjk)‖ = ‖P3 vik (g vik - g vjk)‖ := by
        change ‖(invSubspace π₀ (A.Xsub i j)).starProjection (g vik - g vjk)‖ = _; rw [hP_z1]
      have h4 : ‖(invSubspace π₀ (A.Xsub i j))ᗮ.orthogonalProjectionOnto (g vik - g vjk)‖ = ‖P1 vij (g vij - g vjk)‖ := by
        change ‖P1 vij (g vik - g vjk)‖ = _; rw [h2]
      rw [h3, h4] at h1; exact h1
    have hest2 : ‖g vik - g vij‖ ^ 2 = ‖P3 vik (g vik - g vij)‖ ^ 2 + ‖P1 vjk (g vjk - g vij)‖ ^ 2 := by
      have h1 := (invSubspace π₀ (A.Xsub j k)).norm_sq_eq_add_norm_sq_projection (g vik - g vij)
      have h2 : P1 vjk (g vik - g vij) = P1 vjk (g vjk - g vij) := by
        have hs : g vik - g vij = (g vik - g vjk) + (g vjk - g vij) := by abel
        rw [hs, map_add]
        have h0 : P1 vjk (g vik - g vjk) = 0 := by
          refine (invSubspace π₀ (A.Xsub j k))ᗮ.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
          rw [sub_zero, Submodule.orthogonal_orthogonal]; exact invSubspace_anti π₀ le_sup_right hz1_mem
        rw [h0, zero_add]
      have h3 : ‖(invSubspace π₀ (A.Xsub j k)).orthogonalProjectionOnto (g vik - g vij)‖ = ‖P3 vik (g vik - g vij)‖ := by
        change ‖(invSubspace π₀ (A.Xsub j k)).starProjection (g vik - g vij)‖ = _; rw [hP_z2]
      have h4 : ‖(invSubspace π₀ (A.Xsub j k))ᗮ.orthogonalProjectionOnto (g vik - g vij)‖ = ‖P1 vjk (g vjk - g vij)‖ := by
        change ‖P1 vjk (g vik - g vij)‖ = _; rw [h2]
      rw [h3, h4] at h1; exact h1
    have hest3 : ‖g vij - g vjk‖ ^ 2 ≤
        2 * (‖P3 vik (g vik - g vij)‖ ^ 2 + ‖P3 vik (g vik - g vjk)‖ ^ 2) +
        ‖P1 vij (g vij - g vjk)‖ ^ 2 + ‖P1 vjk (g vjk - g vij)‖ ^ 2 := by
      set PG' := (invSubspace π₀ (A.Gsub vik))ᗮ.starProjection
      have hpyth_ij_jk := (invSubspace π₀ (A.Gsub vik)).norm_sq_eq_add_norm_sq_projection (g vij - g vjk)
      have hs : g vij - g vjk = -(g vik - g vij) + (g vik - g vjk) := by abel
      have hPG'_comm_vik : ∀ a ∈ A.Gsub vik, ∀ w : W₀, PG' (π₀ a w) = π₀ a (PG' w) := by
        intro a ha w
        dsimp only [PG']
        rw [(invSubspace π₀ (A.Gsub vik)).starProjection_orthogonal_val,
          (invSubspace π₀ (A.Gsub vik)).starProjection_orthogonal_val, map_sub]
        congr 1
        exact starProjection_invSubspace_comm π₀
          (fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ ha) hh) ha)
          (fun h hh => Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hh) (Subgroup.inv_mem _ ha)) w
      have hu1 : PG' (-(g vik - g vij)) ∈ invSubspace π₀ (A.Xsub i (thirdIdx i k) ⊔ A.Xsub i k) := by
        rw [hthird_ik]; intro a ha
        have haG : a ∈ A.Gsub vik := (sup_le (hGik_eq ▸ le_sup_left) (A.X_le_G vik)) ha
        rw [← hPG'_comm_vik a haG, map_neg, (invSubspace_anti π₀ (by rw [sup_comm]) hz2_mem) a ha]
      have hu2 : PG' (g vik - g vjk) ∈ invSubspace π₀ (A.Xsub (thirdIdx i k) k ⊔ A.Xsub i k) := by
        rw [hthird_ik]; intro a ha
        have haG : a ∈ A.Gsub vik := (sup_le (hGik_eq ▸ le_sup_right) (A.X_le_G vik)) ha
        rw [← hPG'_comm_vik a haG, (invSubspace_anti π₀ (by rw [sup_comm]) hz1_mem) a ha]
      have horth := A.H12_orth π₀ vik hu1 hu2 (Submodule.coe_mem _) (Submodule.coe_mem _)
      have hPG'_split : ‖PG' (g vij - g vjk)‖ ^ 2 = ‖PG' (g vik - g vij)‖ ^ 2 + ‖PG' (g vik - g vjk)‖ ^ 2 := by
        rw [hs, map_add, norm_add_sq (𝕜 := ℂ), horth, map_zero, mul_zero, add_zero, map_neg, norm_neg]
      have hP3_split : ‖P3 vik (g vij - g vjk)‖ ^ 2 ≤
          2 * (‖P3 vik (g vik - g vij)‖ ^ 2 + ‖P3 vik (g vik - g vjk)‖ ^ 2) := by
        rw [hs, map_add, map_neg]
        have htri := norm_add_le (-P3 vik (g vik - g vij)) (P3 vik (g vik - g vjk))
        rw [norm_neg] at htri
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖P3 vik (g vik - g vij)‖ - ‖P3 vik (g vik - g vjk)‖)]
      have hpyth1 := (invSubspace π₀ (A.Gsub vik)).norm_sq_eq_add_norm_sq_projection (g vik - g vjk)
      have hpyth2 := (invSubspace π₀ (A.Gsub vik)).norm_sq_eq_add_norm_sq_projection (g vik - g vij)
      have h3a : ‖(invSubspace π₀ (A.Gsub vik)).orthogonalProjectionOnto (g vij - g vjk)‖ = ‖P3 vik (g vij - g vjk)‖ := rfl
      have h3b : ‖(invSubspace π₀ (A.Gsub vik))ᗮ.orthogonalProjectionOnto (g vij - g vjk)‖ = ‖PG' (g vij - g vjk)‖ := rfl
      have h1a : ‖(invSubspace π₀ (A.Gsub vik)).orthogonalProjectionOnto (g vik - g vjk)‖ = ‖P3 vik (g vik - g vjk)‖ := rfl
      have h1b : ‖(invSubspace π₀ (A.Gsub vik))ᗮ.orthogonalProjectionOnto (g vik - g vjk)‖ = ‖PG' (g vik - g vjk)‖ := rfl
      have h2a : ‖(invSubspace π₀ (A.Gsub vik)).orthogonalProjectionOnto (g vik - g vij)‖ = ‖P3 vik (g vik - g vij)‖ := rfl
      have h2b : ‖(invSubspace π₀ (A.Gsub vik))ᗮ.orthogonalProjectionOnto (g vik - g vij)‖ = ‖PG' (g vik - g vij)‖ := rfl
      rw [h3a, h3b] at hpyth_ij_jk; rw [h1a, h1b] at hpyth1; rw [h2a, h2b] at hpyth2
      linarith
    linarith
  have hsum_6 : ∑ y : MagicVtx,
      (‖g y - g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩‖ ^ 2 +
       ‖g y - g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩‖ ^ 2 +
       2 * ‖g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩ -
            g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩‖ ^ 2) ≤
    ∑ y : MagicVtx,
      (5 * (‖P3 y (g y - g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩)‖ ^ 2 +
            ‖P3 y (g y - g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩)‖ ^ 2) +
       3 * (‖P1 ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩
              (g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩ -
               g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩)‖ ^ 2 +
            ‖P1 ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩
              (g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩ -
               g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩)‖ ^ 2)) :=
    Finset.sum_le_sum fun ⟨⟨i, k⟩, hik⟩ _ =>
      htriple i (thirdIdx i k) k (thirdIdx_ne_left hik).symm (thirdIdx_ne_right hik) hik
  let v01 : MagicVtx := ⟨(0, 1), by decide⟩
  let v10 : MagicVtx := ⟨(1, 0), by decide⟩
  let v02 : MagicVtx := ⟨(0, 2), by decide⟩
  let v20 : MagicVtx := ⟨(2, 0), by decide⟩
  let v12 : MagicVtx := ⟨(1, 2), by decide⟩
  let v21 : MagicVtx := ⟨(2, 1), by decide⟩
  have huniv6 : (Finset.univ : Finset MagicVtx) = {v01, v10, v02, v20, v12, v21} := by decide
  have hsum6_expand : ∀ F : MagicVtx → ℝ,
      ∑ y : MagicVtx, F y = F v01 + F v10 + F v02 + F v20 + F v12 + F v21 := fun F => by
    rw [huniv6]
    simp only [Finset.sum_insert (by decide : v01 ∉ ({v10, v02, v20, v12, v21} : Finset MagicVtx)),
      Finset.sum_insert (by decide : v10 ∉ ({v02, v20, v12, v21} : Finset MagicVtx)),
      Finset.sum_insert (by decide : v02 ∉ ({v20, v12, v21} : Finset MagicVtx)),
      Finset.sum_insert (by decide : v20 ∉ ({v12, v21} : Finset MagicVtx)),
      Finset.sum_insert (by decide : v12 ∉ ({v21} : Finset MagicVtx)),
      Finset.sum_singleton]; ring
  have hnbrs_v01 : magicNbrs v01 = {v02, v21, v12, v20} := by decide
  have hnbrs_v10 : magicNbrs v10 = {v12, v20, v02, v21} := by decide
  have hnbrs_v02 : magicNbrs v02 = {v01, v12, v21, v10} := by decide
  have hnbrs_v20 : magicNbrs v20 = {v21, v10, v01, v12} := by decide
  have hnbrs_v12 : magicNbrs v12 = {v10, v02, v20, v01} := by decide
  have hnbrs_v21 : magicNbrs v21 = {v20, v01, v10, v02} := by decide
  have hsum4_set : ∀ (a b c d : MagicVtx), a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∀ F : MagicVtx → ℝ, ∑ x ∈ ({a, b, c, d} : Finset MagicVtx), F x = F a + F b + F c + F d :=
    fun a b c d hab hac had hbc hbd hcd F => by
      rw [Finset.sum_insert (by simp [hab, hac, had]),
        Finset.sum_insert (by simp [hbc, hbd]),
        Finset.sum_insert (by simp [hcd]), Finset.sum_singleton]; ring
  have hsum_v01 : ∀ F : MagicVtx → ℝ, ∑ x ∈ magicNbrs v01, F x = F v02 + F v21 + F v12 + F v20 := fun F => by
    rw [hnbrs_v01]; exact hsum4_set _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) F
  have hsum_v10 : ∀ F : MagicVtx → ℝ, ∑ x ∈ magicNbrs v10, F x = F v12 + F v20 + F v02 + F v21 := fun F => by
    rw [hnbrs_v10]; exact hsum4_set _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) F
  have hsum_v02 : ∀ F : MagicVtx → ℝ, ∑ x ∈ magicNbrs v02, F x = F v01 + F v12 + F v21 + F v10 := fun F => by
    rw [hnbrs_v02]; exact hsum4_set _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) F
  have hsum_v20 : ∀ F : MagicVtx → ℝ, ∑ x ∈ magicNbrs v20, F x = F v21 + F v10 + F v01 + F v12 := fun F => by
    rw [hnbrs_v20]; exact hsum4_set _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) F
  have hsum_v12 : ∀ F : MagicVtx → ℝ, ∑ x ∈ magicNbrs v12, F x = F v10 + F v02 + F v20 + F v01 := fun F => by
    rw [hnbrs_v12]; exact hsum4_set _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) F
  have hsum_v21 : ∀ F : MagicVtx → ℝ, ∑ x ∈ magicNbrs v21, F x = F v20 + F v01 + F v10 + F v02 := fun F => by
    rw [hnbrs_v21]; exact hsum4_set _ _ _ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) F
  have hlhs_eq : ∑ y : MagicVtx,
      (‖g y - g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩‖ ^ 2 +
       ‖g y - g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩‖ ^ 2 +
       2 * ‖g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩ -
            g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩‖ ^ 2) =
      ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖g y - g y'‖ ^ 2 := by
    rw [hsum6_expand, hsum6_expand]
    rw [hsum_v01, hsum_v10, hsum_v02, hsum_v20, hsum_v12, hsum_v21]
    simp only [v01, v10, v02, v20, v12, v21, thirdIdx]
    simp only [show (-(0 + 1) : Fin 3) = 2 by decide, show (-(1 + 0) : Fin 3) = 2 by decide,
      show (-(0 + 2) : Fin 3) = 1 by decide, show (-(2 + 0) : Fin 3) = 1 by decide,
      show (-(1 + 2) : Fin 3) = 0 by decide, show (-(2 + 1) : Fin 3) = 0 by decide]
    have s1 : ‖g ⟨(2, 1), by decide⟩ - g ⟨(0, 1), by decide⟩‖ ^ 2 = ‖g ⟨(0, 1), by decide⟩ - g ⟨(2, 1), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s2 : ‖g ⟨(0, 2), by decide⟩ - g ⟨(0, 1), by decide⟩‖ ^ 2 = ‖g ⟨(0, 1), by decide⟩ - g ⟨(0, 2), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s3 : ‖g ⟨(1, 2), by decide⟩ - g ⟨(0, 1), by decide⟩‖ ^ 2 = ‖g ⟨(0, 1), by decide⟩ - g ⟨(1, 2), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s4 : ‖g ⟨(2, 0), by decide⟩ - g ⟨(0, 1), by decide⟩‖ ^ 2 = ‖g ⟨(0, 1), by decide⟩ - g ⟨(2, 0), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s5 : ‖g ⟨(2, 0), by decide⟩ - g ⟨(1, 0), by decide⟩‖ ^ 2 = ‖g ⟨(1, 0), by decide⟩ - g ⟨(2, 0), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s6 : ‖g ⟨(1, 2), by decide⟩ - g ⟨(1, 0), by decide⟩‖ ^ 2 = ‖g ⟨(1, 0), by decide⟩ - g ⟨(1, 2), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s7 : ‖g ⟨(0, 2), by decide⟩ - g ⟨(1, 0), by decide⟩‖ ^ 2 = ‖g ⟨(1, 0), by decide⟩ - g ⟨(0, 2), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s8 : ‖g ⟨(2, 1), by decide⟩ - g ⟨(1, 0), by decide⟩‖ ^ 2 = ‖g ⟨(1, 0), by decide⟩ - g ⟨(2, 1), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s9 : ‖g ⟨(1, 2), by decide⟩ - g ⟨(0, 2), by decide⟩‖ ^ 2 = ‖g ⟨(0, 2), by decide⟩ - g ⟨(1, 2), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s10 : ‖g ⟨(2, 1), by decide⟩ - g ⟨(0, 2), by decide⟩‖ ^ 2 = ‖g ⟨(0, 2), by decide⟩ - g ⟨(2, 1), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s11 : ‖g ⟨(2, 1), by decide⟩ - g ⟨(2, 0), by decide⟩‖ ^ 2 = ‖g ⟨(2, 0), by decide⟩ - g ⟨(2, 1), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    have s12 : ‖g ⟨(1, 2), by decide⟩ - g ⟨(2, 0), by decide⟩‖ ^ 2 = ‖g ⟨(2, 0), by decide⟩ - g ⟨(1, 2), by decide⟩‖ ^ 2 := by rw [norm_sub_rev]
    simp only [s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12]
    ring
  have hrhs_le : ∑ y : MagicVtx,
      (5 * (‖P3 y (g y - g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩)‖ ^ 2 +
            ‖P3 y (g y - g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩)‖ ^ 2) +
       3 * (‖P1 ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩
              (g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩ -
               g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩)‖ ^ 2 +
            ‖P1 ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩
              (g ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩ -
               g ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩)‖ ^ 2)) ≤
      5 * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖P3 y (g y - g y')‖ ^ 2 +
      3 * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖P1 y (g y - g y')‖ ^ 2 := by
    rw [hsum6_expand, hsum6_expand, hsum6_expand]
    rw [hsum_v01, hsum_v10, hsum_v02, hsum_v20, hsum_v12, hsum_v21]
    rw [hsum_v01, hsum_v10, hsum_v02, hsum_v20, hsum_v12, hsum_v21]
    simp only [v01, v10, v02, v20, v12, v21, thirdIdx]
    simp only [show (-(0 + 1) : Fin 3) = 2 by decide, show (-(1 + 0) : Fin 3) = 2 by decide,
      show (-(0 + 2) : Fin 3) = 1 by decide, show (-(2 + 0) : Fin 3) = 1 by decide,
      show (-(1 + 2) : Fin 3) = 0 by decide, show (-(2 + 1) : Fin 3) = 0 by decide]
    linarith [
      sq_nonneg ‖P3 ⟨(0, 1), by decide⟩ (g ⟨(0, 1), by decide⟩ - g ⟨(1, 2), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(0, 1), by decide⟩ (g ⟨(0, 1), by decide⟩ - g ⟨(2, 0), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(1, 0), by decide⟩ (g ⟨(1, 0), by decide⟩ - g ⟨(0, 2), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(1, 0), by decide⟩ (g ⟨(1, 0), by decide⟩ - g ⟨(2, 1), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(0, 2), by decide⟩ (g ⟨(0, 2), by decide⟩ - g ⟨(2, 1), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(0, 2), by decide⟩ (g ⟨(0, 2), by decide⟩ - g ⟨(1, 0), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(2, 0), by decide⟩ (g ⟨(2, 0), by decide⟩ - g ⟨(0, 1), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(2, 0), by decide⟩ (g ⟨(2, 0), by decide⟩ - g ⟨(1, 2), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(1, 2), by decide⟩ (g ⟨(1, 2), by decide⟩ - g ⟨(2, 0), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(1, 2), by decide⟩ (g ⟨(1, 2), by decide⟩ - g ⟨(0, 1), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(2, 1), by decide⟩ (g ⟨(2, 1), by decide⟩ - g ⟨(1, 0), by decide⟩)‖,
      sq_nonneg ‖P3 ⟨(2, 1), by decide⟩ (g ⟨(2, 1), by decide⟩ - g ⟨(0, 2), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(0, 1), by decide⟩ (g ⟨(0, 1), by decide⟩ - g ⟨(0, 2), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(0, 1), by decide⟩ (g ⟨(0, 1), by decide⟩ - g ⟨(2, 1), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(1, 0), by decide⟩ (g ⟨(1, 0), by decide⟩ - g ⟨(1, 2), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(1, 0), by decide⟩ (g ⟨(1, 0), by decide⟩ - g ⟨(2, 0), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(0, 2), by decide⟩ (g ⟨(0, 2), by decide⟩ - g ⟨(0, 1), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(0, 2), by decide⟩ (g ⟨(0, 2), by decide⟩ - g ⟨(1, 2), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(2, 0), by decide⟩ (g ⟨(2, 0), by decide⟩ - g ⟨(2, 1), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(2, 0), by decide⟩ (g ⟨(2, 0), by decide⟩ - g ⟨(1, 0), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(1, 2), by decide⟩ (g ⟨(1, 2), by decide⟩ - g ⟨(1, 0), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(1, 2), by decide⟩ (g ⟨(1, 2), by decide⟩ - g ⟨(0, 2), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(2, 1), by decide⟩ (g ⟨(2, 1), by decide⟩ - g ⟨(2, 0), by decide⟩)‖,
      sq_nonneg ‖P1 ⟨(2, 1), by decide⟩ (g ⟨(2, 1), by decide⟩ - g ⟨(0, 1), by decide⟩)‖]
  linarith

end A2Sys

section MagicLaplacian

/-- Constant functions on `MagicVtx` valued in a Hilbert space `W₀`. -/
def magicU (W₀ : Type*) [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀] :
    Submodule ℂ (PiLp 2 (fun _ : MagicVtx => W₀)) where
  carrier := {f | ∀ y₁ y₂ : MagicVtx, f y₁ = f y₂}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb y₁ y₂ => by simp [ha y₁ y₂, hb y₁ y₂]
  smul_mem' := fun c {a} ha y₁ y₂ => by simp [ha y₁ y₂]

lemma isClosed_magicU (W₀ : Type*) [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀] :
    IsClosed (magicU W₀ : Set (PiLp 2 (fun _ : MagicVtx => W₀))) := by
  have heq : (magicU W₀ : Set (PiLp 2 (fun _ : MagicVtx => W₀))) =
      ⋂ y₁ : MagicVtx, ⋂ y₂ : MagicVtx, {f | f y₁ = f y₂} := by
    ext f; simp [magicU]
  rw [heq]
  exact isClosed_iInter fun y₁ => isClosed_iInter fun y₂ =>
    isClosed_eq (PiLp.continuous_apply 2 _ y₁) (PiLp.continuous_apply 2 _ y₂)

instance instHasOrthProj_magicU (W₀ : Type*) [NormedAddCommGroup W₀]
    [InnerProductSpace ℂ W₀] [CompleteSpace W₀] :
    (magicU W₀).HasOrthogonalProjection :=
  hasOrthProj_of_isClosed (isClosed_magicU W₀)

lemma mem_magicU_orth_iff {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (f : PiLp 2 (fun _ : MagicVtx => W₀)) :
    f ∈ (magicU W₀)ᗮ ↔ ∑ y : MagicVtx, f y = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hf
    let c : PiLp 2 (fun _ : MagicVtx => W₀) := WithLp.toLp 2 (fun _ : MagicVtx => ∑ y : MagicVtx, f y)
    have h0 : ⟪c, f⟫_ℂ = 0 := hf c (fun _ _ => rfl)
    rw [PiLp.inner_apply] at h0
    have h1 : ∑ y : MagicVtx, ⟪c y, f y⟫_ℂ = ⟪∑ y : MagicVtx, f y, ∑ y : MagicVtx, f y⟫_ℂ := by
      rw [inner_sum]
    rw [h1, inner_self_eq_zero] at h0; exact h0
  · intro hsum u hu
    obtain ⟨y₀⟩ : Nonempty MagicVtx := ⟨⟨(0, 1), by decide⟩⟩
    rw [PiLp.inner_apply]
    have heq : ∑ y : MagicVtx, ⟪u y, f y⟫_ℂ = ⟪u y₀, ∑ y : MagicVtx, f y⟫_ℂ := by
      rw [inner_sum]; exact Finset.sum_congr rfl fun y _ => by rw [hu y y₀]
    rw [heq, hsum, inner_zero_right]

/-- The graph Laplacian of the 6-vertex octahedron graph `K_{2,2,2}` acting on `MagicVtx → W₀`. -/
def magicΔ (W₀ : Type*) [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀] :
    PiLp 2 (fun _ : MagicVtx => W₀) →L[ℂ] PiLp 2 (fun _ : MagicVtx => W₀) :=
  LinearMap.mkContinuous
    { toFun := fun f => WithLp.toLp 2 (fun y : MagicVtx => (4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y')
      map_add' := fun f₁ f₂ => by
        ext y; change (4 : ℂ) • (f₁ y + f₂ y) - ∑ y' ∈ magicNbrs y, (f₁ y' + f₂ y') =
          ((4 : ℂ) • f₁ y - ∑ y' ∈ magicNbrs y, f₁ y') + ((4 : ℂ) • f₂ y - ∑ y' ∈ magicNbrs y, f₂ y')
        rw [smul_add, Finset.sum_add_distrib]; abel
      map_smul' := fun c f => by
        ext y; change (4 : ℂ) • (c • f y) - ∑ y' ∈ magicNbrs y, (c • f y') =
          c • ((4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y')
        rw [← Finset.smul_sum, smul_sub, smul_comm] }
    8
    (fun f => by
      have hsq : ‖WithLp.toLp 2 (fun y : MagicVtx => (4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y')‖ ^ 2 ≤ (8 * ‖f‖) ^ 2 := by
        rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
        calc ∑ y : MagicVtx, ‖(4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y'‖ ^ 2
            ≤ ∑ y : MagicVtx, (32 * ‖f y‖ ^ 2 + 8 * ∑ y' ∈ magicNbrs y, ‖f y'‖ ^ 2) := by
              refine Finset.sum_le_sum fun y _ => ?_
              have htri : ‖(4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y'‖ ≤ 4 * ‖f y‖ + ∑ y' ∈ magicNbrs y, ‖f y'‖ := by
                calc ‖(4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y'‖
                    ≤ ‖(4 : ℂ) • f y‖ + ‖∑ y' ∈ magicNbrs y, f y'‖ := norm_sub_le _ _
                  _ ≤ 4 * ‖f y‖ + ∑ y' ∈ magicNbrs y, ‖f y'‖ := by
                      rw [norm_smul, show ‖(4 : ℂ)‖ = 4 by norm_num]
                      exact add_le_add le_rfl (norm_sum_le _ _)
              have hcs : (∑ y' ∈ magicNbrs y, ‖f y'‖) ^ 2 ≤ 4 * ∑ y' ∈ magicNbrs y, ‖f y'‖ ^ 2 := by
                have h0 := sq_sum_le_card_mul_sum_sq (s := magicNbrs y) (f := fun y' => ‖f y'‖)
                rw [magicNbrs_card y] at h0; simpa using h0
              have hsq1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
              nlinarith [sq_nonneg (4 * ‖f y‖ - ∑ y' ∈ magicNbrs y, ‖f y'‖)]
          _ = 32 * ∑ y : MagicVtx, ‖f y‖ ^ 2 + 8 * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖f y'‖ ^ 2 := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ = 64 * ∑ y : MagicVtx, ‖f y‖ ^ 2 := by
              have hswap : ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖f y'‖ ^ 2 = 4 * ∑ y' : MagicVtx, ‖f y'‖ ^ 2 := by
                calc ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖f y'‖ ^ 2
                    = ∑ y : MagicVtx, ∑ y' : MagicVtx, if y' ∈ magicNbrs y then ‖f y'‖ ^ 2 else 0 :=
                      Finset.sum_congr rfl fun y _ => sum_magicNbrs_eq_ite y _
                  _ = ∑ y' : MagicVtx, ∑ y : MagicVtx, if y ∈ magicNbrs y' then ‖f y'‖ ^ 2 else 0 := by
                      rw [Finset.sum_comm]
                      refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y _ => by simp only [magicNbrs_symm]
                  _ = ∑ y' : MagicVtx, ∑ _y ∈ magicNbrs y', ‖f y'‖ ^ 2 :=
                      Finset.sum_congr rfl fun y' _ => (sum_magicNbrs_eq_ite y' _).symm
                  _ = 4 * ∑ y' : MagicVtx, ‖f y'‖ ^ 2 := by
                      simp_rw [Finset.sum_const, magicNbrs_card, nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_ofNat]
              rw [hswap]; ring
          _ = 8 ^ 2 * ∑ y : MagicVtx, ‖f y‖ ^ 2 := by ring
      have hrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt)

lemma magicΔ_apply {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (f : PiLp 2 (fun _ : MagicVtx => W₀)) (y : MagicVtx) :
    magicΔ W₀ f y = ∑ y' ∈ magicNbrs y, (f y - f y') := by
  change (4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y' = _
  rw [Finset.sum_sub_distrib, Finset.sum_const, magicNbrs_card y, ← Nat.cast_smul_eq_nsmul ℂ]; norm_num

lemma magicΔ_orth_U {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (f : PiLp 2 (fun _ : MagicVtx => W₀)) : magicΔ W₀ f ∈ (magicU W₀)ᗮ := by
  rw [mem_magicU_orth_iff]
  simp_rw [magicΔ_apply]
  have h1 : ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (f y - f y') =
      ∑ y : MagicVtx, ∑ y' : MagicVtx, if y' ∈ magicNbrs y then (f y - f y') else 0 :=
    Finset.sum_congr rfl fun y _ => sum_magicNbrs_eq_ite y _
  rw [h1]
  have hneg : ∑ y : MagicVtx, ∑ y' : MagicVtx, (if y' ∈ magicNbrs y then (f y - f y') else 0) =
      -(∑ y : MagicVtx, ∑ y' : MagicVtx, (if y' ∈ magicNbrs y then (f y - f y') else 0)) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y' _ => by simp only [magicNbrs_symm]; split_ifs <;> simp
  have h2 : (2 : ℂ) • ∑ y : MagicVtx, ∑ y' : MagicVtx, (if y' ∈ magicNbrs y then (f y - f y') else 0) = 0 := by
    rw [show (2 : ℂ) = 1 + 1 by norm_num, add_smul, one_smul]
    conv_rhs => rw [← add_neg_cancel (∑ y : MagicVtx, ∑ y' : MagicVtx, if y' ∈ magicNbrs y then f y - f y' else 0)]
    congr 1
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

lemma magicΔ_energy {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (f : PiLp 2 (fun _ : MagicVtx => W₀)) :
    RCLike.re ⟪magicΔ W₀ f, f⟫_ℂ = (1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖f y - f y'‖ ^ 2 := by
  have h1 : (RCLike.re ⟪magicΔ W₀ f, f⟫_ℂ) = ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (⟪f y - f y', f y⟫_ℂ).re := by
    change (⟪magicΔ W₀ f, f⟫_ℂ).re = _
    rw [PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [magicΔ_apply, sum_inner, Complex.re_sum]
  have h2 : ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (⟪f y - f y', f y⟫_ℂ).re =
      ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (⟪f y' - f y, f y'⟫_ℂ).re := by
    calc ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (⟪f y - f y', f y⟫_ℂ).re
        = ∑ y : MagicVtx, ∑ y' : MagicVtx, if y' ∈ magicNbrs y then (⟪f y - f y', f y⟫_ℂ).re else 0 :=
          Finset.sum_congr rfl fun y _ => sum_magicNbrs_eq_ite y _
      _ = ∑ y' : MagicVtx, ∑ y : MagicVtx, if y ∈ magicNbrs y' then (⟪f y - f y', f y⟫_ℂ).re else 0 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun y' _ => Finset.sum_congr rfl fun y _ => by simp only [magicNbrs_symm]
      _ = ∑ y' : MagicVtx, ∑ y ∈ magicNbrs y', (⟪f y - f y', f y⟫_ℂ).re :=
          Finset.sum_congr rfl fun y' _ => (sum_magicNbrs_eq_ite y' _).symm
  have hsum : 2 * RCLike.re ⟪magicΔ W₀ f, f⟫_ℂ = ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖f y - f y'‖ ^ 2 := by
    calc 2 * RCLike.re ⟪magicΔ W₀ f, f⟫_ℂ
        = ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (⟪f y - f y', f y⟫_ℂ).re +
          ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, (⟪f y' - f y, f y'⟫_ℂ).re := by rw [h1, ← h2]; ring
      _ = ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ((⟪f y - f y', f y⟫_ℂ).re + (⟪f y' - f y, f y'⟫_ℂ).re) := by
          simp_rw [← Finset.sum_add_distrib]
      _ = ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖f y - f y'‖ ^ 2 := by
          refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => ?_
          have h3 : (⟪f y - f y', f y⟫_ℂ).re + (⟪f y' - f y, f y'⟫_ℂ).re =
              (⟪f y - f y', f y - f y'⟫_ℂ).re := by
            rw [inner_sub_right, Complex.sub_re, show f y' - f y = -(f y - f y') by abel,
              inner_neg_left, Complex.neg_re]; ring
          rw [h3, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; exact Complex.ofReal_re _
  linarith

lemma magicΔ_on_Uorth {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    {f : PiLp 2 (fun _ : MagicVtx => W₀)} (hf : f ∈ (magicU W₀)ᗮ) (y : MagicVtx) :
    magicΔ W₀ f y = (5 : ℂ) • f y + f (magicSwap y) := by
  have hsum0 : ∑ z : MagicVtx, f z = 0 := (mem_magicU_orth_iff f).mp hf
  have hsplit : ∑ z : MagicVtx, f z = f y + f (magicSwap y) + ∑ y' ∈ magicNbrs y, f y' := by
    have hunion : (Finset.univ : Finset MagicVtx) = insert y (insert (magicSwap y) (magicNbrs y)) := by
      ext z; simp [magicNbrs]; tauto
    have hne_swap : y ≠ magicSwap y := fun h => y.2 (congrArg (fun t => t.1.1) h)
    rw [hunion, Finset.sum_insert (by simp [magicNbrs, hne_swap]), Finset.sum_insert (by simp [magicNbrs])]; abel
  have hnbr_sum : ∑ y' ∈ magicNbrs y, f y' = -(f y + f (magicSwap y)) := by
    rw [hsplit] at hsum0; exact eq_neg_of_add_eq_zero_right hsum0
  change (4 : ℂ) • f y - ∑ y' ∈ magicNbrs y, f y' = _
  rw [hnbr_sum, sub_neg_eq_add, show (5 : ℂ) = 4 + 1 by norm_num, add_smul, one_smul]; abel

lemma magicΔ_coercive {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    {f : PiLp 2 (fun _ : MagicVtx => W₀)} (hf : f ∈ (magicU W₀)ᗮ) :
    4 * ‖f‖ ^ 2 ≤ RCLike.re ⟪magicΔ W₀ f, f⟫_ℂ := by
  have h1 : RCLike.re ⟪magicΔ W₀ f, f⟫_ℂ = ∑ y : MagicVtx, (5 * ‖f y‖ ^ 2 + (⟪f (magicSwap y), f y⟫_ℂ).re) := by
    change (⟪magicΔ W₀ f, f⟫_ℂ).re = _
    rw [PiLp.inner_apply, Complex.re_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [magicΔ_on_Uorth hf y, inner_add_left, inner_smul_left, Complex.add_re]
    rw [show (starRingEnd ℂ) (5 : ℂ) = ((5 : ℝ) : ℂ) by rw [map_ofNat]; norm_num, inner_self_eq_norm_sq_to_K,
      ← RCLike.ofReal_pow]
    change (((5 : ℝ) : ℂ) * ((‖f y‖ ^ 2 : ℝ) : ℂ)).re + _ = _
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
  have hswap_sum : ∑ y : MagicVtx, ‖f (magicSwap y)‖ ^ 2 = ∑ y : MagicVtx, ‖f y‖ ^ 2 := by
    let eSwap : MagicVtx ≃ MagicVtx :=
      { toFun := magicSwap, invFun := magicSwap,
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl, right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
    exact Fintype.sum_equiv eSwap _ _ fun _ => rfl
  have hcs : ∀ y : MagicVtx, -(‖f y‖ ^ 2 + ‖f (magicSwap y)‖ ^ 2) / 2 ≤ (⟪f (magicSwap y), f y⟫_ℂ).re := by
    intro y
    have h0 : |(⟪f (magicSwap y), f y⟫_ℂ).re| ≤ ‖f (magicSwap y)‖ * ‖f y‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have hge := (abs_le.mp h0).1
    nlinarith [sq_nonneg (‖f y‖ - ‖f (magicSwap y)‖)]
  rw [h1, PiLp.norm_sq_eq_of_L2]
  have hsum_ge : ∑ y : MagicVtx, (-(‖f y‖ ^ 2 + ‖f (magicSwap y)‖ ^ 2) / 2) ≤
      ∑ y : MagicVtx, (⟪f (magicSwap y), f y⟫_ℂ).re := Finset.sum_le_sum fun y _ => hcs y
  have hsum_eval : ∑ y : MagicVtx, (-(‖f y‖ ^ 2 + ‖f (magicSwap y)‖ ^ 2) / 2) = -∑ y : MagicVtx, ‖f y‖ ^ 2 := by
    simp_rw [neg_div, Finset.sum_neg_distrib, ← Finset.sum_div, Finset.sum_add_distrib, hswap_sum]; ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]; linarith

/-- Solve `V'.starProjection (magicΔ W₀ g) = x` in `U₁ := (magicU W₀)ᗮ ⊓ V'` via Neumann series. -/
lemma magicΔ_solve {W₀ : Type*} [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀] [CompleteSpace W₀]
    (V' : Submodule ℂ (PiLp 2 (fun _ : MagicVtx => W₀)))
    (hV'_cl : IsClosed (V' : Set (PiLp 2 (fun _ : MagicVtx => W₀))))
    (hUV' : magicU W₀ ≤ V') [V'.HasOrthogonalProjection]
    {x : PiLp 2 (fun _ : MagicVtx => W₀)} (hx : x ∈ (magicU W₀)ᗮ ⊓ V') :
    ∃ g : PiLp 2 (fun _ : MagicVtx => W₀), g ∈ (magicU W₀)ᗮ ⊓ V' ∧ V'.starProjection (magicΔ W₀ g) = x := by
  let Ω0 := PiLp 2 (fun _ : MagicVtx => W₀)
  let U₁ : Submodule ℂ Ω0 := (magicU W₀)ᗮ ⊓ V'
  have hU₁_cl : IsClosed (U₁ : Set Ω0) := (magicU W₀).isClosed_orthogonal.inter hV'_cl
  have : CompleteSpace U₁ := hU₁_cl.completeSpace_coe
  have : U₁.HasOrthogonalProjection := hasOrthProj_of_isClosed hU₁_cl
  let P_U₁ : Ω0 →L[ℂ] U₁ := U₁.orthogonalProjectionOnto
  let T : U₁ →L[ℂ] U₁ :=
    P_U₁.comp ((ContinuousLinearMap.id ℂ Ω0 - ((6 : ℂ)⁻¹) • magicΔ W₀).comp U₁.subtypeL)
  have hT_le : ∀ u : U₁, ‖T u‖ ≤ (1 / 3 : ℝ) * ‖u‖ := by
    intro u
    have hP_le : ‖P_U₁ (u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1)‖ ≤ ‖u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1‖ := by
      have hpyth := U₁.norm_sq_eq_add_norm_sq_projection (u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1)
      have hsq : ‖P_U₁ (u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1)‖ ^ 2 ≤ ‖u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1‖ ^ 2 := by
        linarith [sq_nonneg ‖U₁ᗮ.orthogonalProjectionOnto (u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1)‖]
      have hrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hrt
    refine hP_le.trans ?_
    have hsq : ‖u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1‖ ^ 2 ≤ ((1 / 3 : ℝ) * ‖u.1‖) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
      have hterm : ∀ y : MagicVtx, (u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1) y =
          ((6 : ℂ)⁻¹) • (u.1 y - u.1 (magicSwap y)) := by
        intro y
        change u.1 y - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1 y = _
        rw [magicΔ_on_Uorth u.2.1 y, smul_add, smul_smul]
        have h56 : (6 : ℂ)⁻¹ * 5 = 1 - (6 : ℂ)⁻¹ := by norm_num
        rw [h56, sub_smul, one_smul, smul_sub]; abel
      have hswap_sum : ∑ y : MagicVtx, ‖u.1 (magicSwap y)‖ ^ 2 = ∑ y : MagicVtx, ‖u.1 y‖ ^ 2 := by
        let eSwap : MagicVtx ≃ MagicVtx :=
          { toFun := magicSwap, invFun := magicSwap,
            left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl, right_inv := fun ⟨⟨_, _⟩, _⟩ => rfl }
        exact Fintype.sum_equiv eSwap _ _ fun _ => rfl
      calc ∑ y : MagicVtx, ‖(u.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ u.1) y‖ ^ 2
          = ∑ y : MagicVtx, (1 / 36 : ℝ) * ‖u.1 y - u.1 (magicSwap y)‖ ^ 2 := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [hterm y, norm_smul, norm_inv, show ‖(6 : ℂ)‖ = 6 by norm_num, mul_pow]; norm_num
        _ ≤ ∑ y : MagicVtx, (1 / 36 : ℝ) * (2 * ‖u.1 y‖ ^ 2 + 2 * ‖u.1 (magicSwap y)‖ ^ 2) := by
            refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (by positivity)
            have hsq1 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (u.1 y) (u.1 (magicSwap y))) 2
            nlinarith [sq_nonneg (‖u.1 y‖ - ‖u.1 (magicSwap y)‖)]
        _ = (1 / 36 : ℝ) * (2 * ∑ y : MagicVtx, ‖u.1 y‖ ^ 2 + 2 * ∑ y : MagicVtx, ‖u.1 (magicSwap y)‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ = (1 / 3 : ℝ) ^ 2 * ∑ y : MagicVtx, ‖u.1 y‖ ^ 2 := by rw [hswap_sum]; ring
    have hrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt
  have hT_pow : ∀ k : ℕ, ‖(T ^ k) ⟨x, hx⟩‖ ≤ (1 / 3 : ℝ) ^ k * ‖(⟨x, hx⟩ : U₁)‖ := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ']
      calc ‖T ((T ^ k) ⟨x, hx⟩)‖ ≤ (1 / 3 : ℝ) * ‖(T ^ k) ⟨x, hx⟩‖ := hT_le _
        _ ≤ (1 / 3 : ℝ) * ((1 / 3 : ℝ) ^ k * ‖(⟨x, hx⟩ : U₁)‖) := mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (1 / 3 : ℝ) ^ (k + 1) * ‖(⟨x, hx⟩ : U₁)‖ := by rw [pow_succ']; ring
  have hsumm : Summable (fun k : ℕ => (T ^ k) ⟨x, hx⟩) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity) (by norm_num)).mul_right _) hT_pow
  let g₀ : U₁ := ∑' k : ℕ, (T ^ k) ⟨x, hx⟩
  have hTg₀ : T g₀ = g₀ - ⟨x, hx⟩ := by
    dsimp only [g₀]
    rw [T.map_tsum hsumm]
    have hsplit := hsumm.tsum_eq_zero_add
    have hshift : (∑' k : ℕ, T ((T ^ k) ⟨x, hx⟩)) = ∑' k : ℕ, (T ^ (k + 1)) ⟨x, hx⟩ :=
      tsum_congr fun k => by rw [pow_succ']; rfl
    rw [hshift]
    have h0 : (T ^ 0) ⟨x, hx⟩ = ⟨x, hx⟩ := rfl
    rw [h0] at hsplit; rw [hsplit]; abel
  let g : Ω0 := ((6 : ℂ)⁻¹) • g₀.1
  refine ⟨g, U₁.smul_mem _ g₀.2, ?_⟩
  have hPU₁_eq : U₁.starProjection (magicΔ W₀ g) = x := by
    have h1 : g₀ - T g₀ = ⟨x, hx⟩ := by rw [hTg₀]; abel
    have h2 : (g₀ - T g₀).1 = ((6 : ℂ)⁻¹) • U₁.starProjection (magicΔ W₀ g₀.1) := by
      change g₀.1 - U₁.starProjection (g₀.1 - ((6 : ℂ)⁻¹) • magicΔ W₀ g₀.1) = _
      rw [map_sub, map_smul, U₁.starProjection_eq_self_iff.mpr g₀.2]; abel
    have h3 : ((6 : ℂ)⁻¹) • U₁.starProjection (magicΔ W₀ g₀.1) = x := by rw [← h2, h1]
    dsimp only [g]; rw [map_smul, map_smul, h3]
  have hV'_eq_U₁ : V'.starProjection (magicΔ W₀ g) = U₁.starProjection (magicΔ W₀ g) := by
    refine V'.eq_starProjection_of_mem_orthogonal (Submodule.coe_mem (U₁.orthogonalProjectionOnto (magicΔ W₀ g))).2 ?_
    rw [Submodule.mem_orthogonal]; intro w hw
    have hsplit : w = (magicU W₀).starProjection w + (magicU W₀)ᗮ.starProjection w := by
      rw [(magicU W₀).starProjection_orthogonal_val]; abel
    have hw1 : (magicU W₀)ᗮ.starProjection w ∈ U₁ := by
      refine ⟨Submodule.coe_mem _, ?_⟩
      rw [(magicU W₀).starProjection_orthogonal_val]
      exact V'.sub_mem hw (hUV' (Submodule.coe_mem _))
    have h_u : ⟪(magicU W₀).starProjection w, magicΔ W₀ g - U₁.starProjection (magicΔ W₀ g)⟫_ℂ = 0 := by
      have hmem_U' : magicΔ W₀ g - U₁.starProjection (magicΔ W₀ g) ∈ (magicU W₀)ᗮ :=
        (magicU W₀)ᗮ.sub_mem (magicΔ_orth_U g) (Submodule.coe_mem (U₁.orthogonalProjectionOnto (magicΔ W₀ g))).1
      exact (Submodule.mem_orthogonal (magicU W₀) _).mp hmem_U' _ (Submodule.coe_mem _)
    have h_u1 : ⟪(magicU W₀)ᗮ.starProjection w, magicΔ W₀ g - U₁.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal U₁ _).mp (U₁.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) _ hw1
    rw [hsplit, inner_add_left, h_u, h_u1, add_zero]
  rw [hV'_eq_U₁, hPU₁_eq]

end MagicLaplacian

/-- Helper subspace `magicW A π₀` of vertex-wise `G_y`-invariant functions on `MagicVtx`. -/
def A2Sys.magicW {C W₀ : Type} [Group C] [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) : Submodule ℂ (PiLp 2 (fun _ : MagicVtx => W₀)) where
  carrier := {f | ∀ y : MagicVtx, f y ∈ invSubspace π₀ (A.Gsub y)}
  zero_mem' := fun y => (invSubspace π₀ (A.Gsub y)).zero_mem
  add_mem' := fun {_ _} ha hb y => (invSubspace π₀ (A.Gsub y)).add_mem (ha y) (hb y)
  smul_mem' := fun c {_} ha y => (invSubspace π₀ (A.Gsub y)).smul_mem c (ha y)

lemma A2Sys.isClosed_magicW {C W₀ : Type} [Group C] [NormedAddCommGroup W₀] [InnerProductSpace ℂ W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) :
    IsClosed (A.magicW π₀ : Set (PiLp 2 (fun _ : MagicVtx => W₀))) := by
  have heq : (A.magicW π₀ : Set (PiLp 2 (fun _ : MagicVtx => W₀))) =
      ⋂ y : MagicVtx, {f : PiLp 2 (fun _ : MagicVtx => W₀) | f y ∈ invSubspace π₀ (A.Gsub y)} := by
    ext f; simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_ofPred_eq]; rfl
  rw [heq]
  exact isClosed_iInter fun y => (isClosed_invSubspace π₀ (A.Gsub y)).preimage (PiLp.continuous_apply 2 _ y)

instance A2Sys.instHasOrthProj_magicW {C W₀ : Type} [Group C] [NormedAddCommGroup W₀]
    [InnerProductSpace ℂ W₀] [CompleteSpace W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) :
    (A.magicW π₀).HasOrthogonalProjection :=
  hasOrthProj_of_isClosed (A.isClosed_magicW π₀)

/-- Step 1 of EJZ Theorem 5.6: `‖W₁.starProjection x‖^2 ≤ (14/15) * ‖x‖^2` for `x ∈ Uᗮ ⊓ V'`. -/
lemma A2Sys.magic_UW_step1 {C W₀ : Type} [Group C] [NormedAddCommGroup W₀]
    [InnerProductSpace ℂ W₀] [CompleteSpace W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀)
    (V' : Submodule ℂ (PiLp 2 (fun _ : MagicVtx => W₀)))
    (hV'_eq : V' = (magicU W₀ ⊔ A.magicW π₀).topologicalClosure)
    (W₁ : Submodule ℂ (PiLp 2 (fun _ : MagicVtx => W₀)))
    (hW₁_eq : W₁ = (A.magicW π₀)ᗮ ⊓ V') [W₁.HasOrthogonalProjection]
    {x : PiLp 2 (fun _ : MagicVtx => W₀)} (hx : x ∈ (magicU W₀)ᗮ ⊓ V') :
    ‖W₁.starProjection x‖ ^ 2 ≤ (14 / 15 : ℝ) * ‖x‖ ^ 2 := by
  subst hV'_eq; subst hW₁_eq
  let Ω0 := PiLp 2 (fun _ : MagicVtx => W₀)
  let U := magicU W₀
  let W := A.magicW π₀
  let V' : Submodule ℂ Ω0 := (U ⊔ W).topologicalClosure
  let W₁ : Submodule ℂ Ω0 := Wᗮ ⊓ V'
  have hV'_cl : IsClosed (V' : Set Ω0) := (U ⊔ W).isClosed_topologicalClosure
  have : V'.HasOrthogonalProjection := hasOrthProj_of_isClosed hV'_cl
  have hPW_apply : ∀ (f : Ω0) (y : MagicVtx), W.starProjection f y = (invSubspace π₀ (A.Gsub y)).starProjection (f y) := by
    intro f y
    let g : Ω0 := WithLp.toLp 2 (fun z : MagicVtx => (invSubspace π₀ (A.Gsub z)).starProjection (f z))
    have hg : W.starProjection f = g := by
      refine W.eq_starProjection_of_mem_orthogonal (fun z => Submodule.coe_mem _) ?_
      rw [Submodule.mem_orthogonal]; intro u hu; rw [PiLp.inner_apply]
      exact Finset.sum_eq_zero fun z _ =>
        (Submodule.mem_orthogonal _ _).mp ((invSubspace π₀ (A.Gsub z)).sub_starProjection_mem_orthogonal (f z)) (u z) (hu z)
    rw [hg]
  have hPW'_apply : ∀ (f : Ω0) (y : MagicVtx), Wᗮ.starProjection f y = (invSubspace π₀ (A.Gsub y))ᗮ.starProjection (f y) := by
    intro f y
    rw [W.starProjection_orthogonal_val, (invSubspace π₀ (A.Gsub y)).starProjection_orthogonal_val]
    change f y - W.starProjection f y = _; rw [hPW_apply]
  have hVprime_diff : ∀ g : Ω0, g ∈ V' → ∀ y : MagicVtx, ∀ y' ∈ magicNbrs y,
      g y - g y' ∈ invSubspace π₀ (A.Gsub y ⊓ A.Gsub y') := by
    intro g hg y y' _
    have hcl : IsClosed {f : Ω0 | f y - f y' ∈ invSubspace π₀ (A.Gsub y ⊓ A.Gsub y')} :=
      (isClosed_invSubspace π₀ _).preimage ((PiLp.continuous_apply 2 _ y).sub (PiLp.continuous_apply 2 _ y'))
    refine (hcl.closure_subset_iff.mpr ?_) hg
    intro f hf
    change f ∈ U ⊔ W at hf
    rw [Submodule.mem_sup] at hf
    obtain ⟨u, hu, w, hw, rfl⟩ := hf
    change (u y + w y) - (u y' + w y') ∈ invSubspace π₀ (A.Gsub y ⊓ A.Gsub y')
    rw [hu y y', add_sub_add_left_eq_sub]
    exact (invSubspace π₀ _).sub_mem (invSubspace_anti π₀ inf_le_left (hw y)) (invSubspace_anti π₀ inf_le_right (hw y'))
  obtain ⟨g, hgU₁, hΔg⟩ := magicΔ_solve V' hV'_cl (fun u hu => Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hu)) hx
  have hgV' : g ∈ V' := hgU₁.2
  let P1 : MagicVtx → W₀ →L[ℂ] W₀ := fun y => (invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection
  let P2 : MagicVtx → W₀ →L[ℂ] W₀ := fun y => (A.midSubspace π₀ y).starProjection
  let P3 : MagicVtx → W₀ →L[ℂ] W₀ := fun y => (invSubspace π₀ (A.Gsub y)).starProjection
  have hdecomp3 : ∀ (y : MagicVtx) (w : W₀), ‖w‖ ^ 2 = ‖P1 y w‖ ^ 2 + ‖P2 y w‖ ^ 2 + ‖P3 y w‖ ^ 2 := by
    intro y w
    have h1 := (invSubspace π₀ (A.Xsub y.1.1 y.1.2)).norm_sq_eq_add_norm_sq_projection w
    set u := (invSubspace π₀ (A.Xsub y.1.1 y.1.2)).starProjection w
    have h2 := (invSubspace π₀ (A.Gsub y)).norm_sq_eq_add_norm_sq_projection u
    have hP3_u : P3 y u = P3 y w := by
      symm; refine (invSubspace π₀ (A.Gsub y)).eq_starProjection_of_mem_orthogonal (Submodule.coe_mem _) ?_
      rw [Submodule.mem_orthogonal]; intro a ha
      have hwu : ⟪a, w - u⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp ((invSubspace π₀ (A.Xsub y.1.1 y.1.2)).sub_starProjection_mem_orthogonal w) a
          (invSubspace_anti π₀ (A.X_le_G y) ha)
      have huP : ⟪a, u - P3 y u⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).mp ((invSubspace π₀ (A.Gsub y)).sub_starProjection_mem_orthogonal u) a ha
      have hs : w - P3 y u = (w - u) + (u - P3 y u) := by abel
      rw [hs, inner_add_right, hwu, huP, add_zero]
    have hP2_u : (invSubspace π₀ (A.Gsub y))ᗮ.starProjection u = P2 y w := by
      symm; refine (A.midSubspace π₀ y).eq_starProjection_of_mem_orthogonal ?_ ?_
      · refine ⟨?_, Submodule.coe_mem _⟩
        rw [(invSubspace π₀ (A.Gsub y)).starProjection_orthogonal_val]
        exact (invSubspace π₀ (A.Xsub y.1.1 y.1.2)).sub_mem (Submodule.coe_mem _)
          (invSubspace_anti π₀ (A.X_le_G y) (Submodule.coe_mem _))
      · rw [Submodule.mem_orthogonal]; intro a ⟨haX, haG'⟩
        have hwu : ⟪a, w - u⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal _ _).mp ((invSubspace π₀ (A.Xsub y.1.1 y.1.2)).sub_starProjection_mem_orthogonal w) a haX
        have hP30 : ⟪a, P3 y u⟫_ℂ = 0 := by
          have : ⟪P3 y u, a⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).mp haG' _ (Submodule.coe_mem _)
          rw [← inner_conj_symm, this, map_zero]
        have hs : w - (invSubspace π₀ (A.Gsub y))ᗮ.starProjection u = (w - u) + P3 y u := by
          rw [(invSubspace π₀ (A.Gsub y)).starProjection_orthogonal_val]; abel
        rw [hs, inner_add_right, hwu, hP30, add_zero]
    have ha1 : ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2)).orthogonalProjectionOnto w‖ = ‖u‖ := rfl
    have ha2 : ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.orthogonalProjectionOnto w‖ = ‖P1 y w‖ := rfl
    have hb1 : ‖(invSubspace π₀ (A.Gsub y)).orthogonalProjectionOnto u‖ = ‖P3 y w‖ := by
      change ‖P3 y u‖ = _; rw [hP3_u]
    have hb2 : ‖(invSubspace π₀ (A.Gsub y))ᗮ.orthogonalProjectionOnto u‖ = ‖P2 y w‖ := by
      change ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection u‖ = _; rw [hP2_u]
    rw [ha1, ha2] at h1; rw [hb1, hb2] at h2; linarith
  have hdecomp2_G' : ∀ (y : MagicVtx) (w : W₀),
      ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w‖ ^ 2 = ‖P1 y w‖ ^ 2 + ‖P2 y w‖ ^ 2 := by
    intro y w
    have h1 := (invSubspace π₀ (A.Gsub y)).norm_sq_eq_add_norm_sq_projection w
    have h2 := hdecomp3 y w
    have h3 : ‖(invSubspace π₀ (A.Gsub y)).orthogonalProjectionOnto w‖ = ‖P3 y w‖ := rfl
    have h4 : ‖(invSubspace π₀ (A.Gsub y))ᗮ.orthogonalProjectionOnto w‖ = ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w‖ := rfl
    rw [h3, h4] at h1; linarith
  set D : ℝ := (1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖g y - g y'‖ ^ 2
  set d1 : ℝ := (1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖P1 y (g y - g y')‖ ^ 2
  set d2 : ℝ := (1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖P2 y (g y - g y')‖ ^ 2
  set d3 : ℝ := (1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖P3 y (g y - g y')‖ ^ 2
  have hD_sum : D = d1 + d2 + d3 := by
    dsimp only [D, d1, d2, d3]
    have hcongr : ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖g y - g y'‖ ^ 2 =
        ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y,
          (‖P1 y (g y - g y')‖ ^ 2 + ‖P2 y (g y - g y')‖ ^ 2 + ‖P3 y (g y - g y')‖ ^ 2) :=
      Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ => hdecomp3 y (g y - g y')
    rw [hcongr]
    simp_rw [Finset.sum_add_distrib]
    ring
  have hD_le : D ≤ (1 / 4 : ℝ) * ‖x‖ ^ 2 := by
    have h1 : D = RCLike.re ⟪magicΔ W₀ g, g⟫_ℂ := (magicΔ_energy g).symm
    have h2 : ⟪magicΔ W₀ g, g⟫_ℂ = ⟪x, g⟫_ℂ := by
      have horth : ⟪magicΔ W₀ g - V'.starProjection (magicΔ W₀ g), g⟫_ℂ = 0 :=
        V'.starProjection_inner_eq_zero (magicΔ W₀ g) g hgV'
      rw [hΔg, inner_sub_left, sub_eq_zero] at horth; exact horth
    have h3 : 4 * ‖g‖ ^ 2 ≤ RCLike.re ⟪x, g⟫_ℂ := by rw [← h2]; exact magicΔ_coercive hgU₁.1
    have h4 : RCLike.re ⟪x, g⟫_ℂ ≤ ‖x‖ * ‖g‖ := (RCLike.re_le_norm _).trans (norm_inner_le_norm x g)
    have hg_le : 4 * ‖g‖ ≤ ‖x‖ := by
      by_cases hg0 : ‖g‖ = 0
      · rw [hg0, mul_zero]; exact norm_nonneg x
      · have hgpos : 0 < ‖g‖ := lt_of_le_of_ne (norm_nonneg g) (Ne.symm hg0); nlinarith
    rw [h1, h2]; nlinarith [norm_nonneg x, norm_nonneg g]
  have hpyth_W : ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖W₁.starProjection x‖ ^ 2 := by
    have h1 := W.norm_sq_eq_add_norm_sq_projection x
    have hW'_eq : Wᗮ.starProjection x = W₁.starProjection x := by
      symm; refine W₁.eq_starProjection_of_mem_orthogonal ?_ ?_
      · refine ⟨Submodule.coe_mem _, ?_⟩
        rw [W.starProjection_orthogonal_val]
        exact V'.sub_mem hx.2 (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right (Submodule.coe_mem _)))
      · rw [Submodule.mem_orthogonal]; intro u hu
        rw [W.starProjection_orthogonal_val, sub_sub_cancel]
        have : ⟪W.starProjection x, u⟫_ℂ = 0 := (Submodule.mem_orthogonal W u).mp hu.1 _ (Submodule.coe_mem _)
        rw [← inner_conj_symm, this, map_zero]
    have h2 : ‖W.orthogonalProjectionOnto x‖ = ‖W.starProjection x‖ := rfl
    have h3 : ‖Wᗮ.orthogonalProjectionOnto x‖ = ‖W₁.starProjection x‖ := by
      change ‖Wᗮ.starProjection x‖ = _; rw [hW'_eq]
    rw [h2, h3] at h1; exact h1
  have hd3_ge : (1 / 8 : ℝ) * (‖x‖ ^ 2 - ‖W₁.starProjection x‖ ^ 2) ≤ d3 := by
    have hPW_x : W.starProjection x = W.starProjection (magicΔ W₀ g) := by
      rw [← hΔg]; refine W.eq_starProjection_of_mem_orthogonal (Submodule.coe_mem _) ?_
      rw [Submodule.mem_orthogonal]; intro u hu
      have h1 : ⟪u, magicΔ W₀ g - V'.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal V' _).mp (V'.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) u
          (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hu))
      have h2 : ⟪u, magicΔ W₀ g - W.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal W _).mp (W.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) u hu
      have hs : V'.starProjection (magicΔ W₀ g) - W.starProjection (magicΔ W₀ g) =
          (magicΔ W₀ g - W.starProjection (magicΔ W₀ g)) - (magicΔ W₀ g - V'.starProjection (magicΔ W₀ g)) := by abel
      rw [hs, inner_sub_right, h2, h1, sub_zero]
    have hbound : ‖W.starProjection x‖ ^ 2 ≤ 8 * d3 := by
      rw [hPW_x, PiLp.norm_sq_eq_of_L2]; dsimp only [d3]
      calc ∑ y : MagicVtx, ‖W.starProjection (magicΔ W₀ g) y‖ ^ 2
          = ∑ y : MagicVtx, ‖∑ y' ∈ magicNbrs y, P3 y (g y - g y')‖ ^ 2 :=
            Finset.sum_congr rfl fun y _ => by rw [hPW_apply, magicΔ_apply, map_sum]
        _ ≤ ∑ y : MagicVtx, 4 * ∑ y' ∈ magicNbrs y, ‖P3 y (g y - g y')‖ ^ 2 := by
            refine Finset.sum_le_sum fun y _ => ?_
            have hsq := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le (magicNbrs y) fun y' => P3 y (g y - g y')) 2
            have hcs := sq_sum_le_card_mul_sum_sq (s := magicNbrs y) (f := fun y' => ‖P3 y (g y - g y')‖)
            rw [magicNbrs_card y] at hcs; exact hsq.trans (by simpa using hcs)
        _ = 8 * ((1 / 2 : ℝ) * ∑ y : MagicVtx, ∑ y' ∈ magicNbrs y, ‖P3 y (g y - g y')‖ ^ 2) := by
            rw [← Finset.mul_sum]; ring
    linarith
  have hW1_upper : ‖W₁.starProjection x‖ ^ 2 ≤ (2 + Real.sqrt 2) * d1 + 4 * d2 := by
    have h1 : ‖W₁.starProjection x‖ ^ 2 ≤ ‖Wᗮ.starProjection (magicΔ W₀ g)‖ ^ 2 := by
      have hW1_eq : W₁.starProjection x = W₁.starProjection (magicΔ W₀ g) := by
        rw [← hΔg]; refine W₁.eq_starProjection_of_mem_orthogonal (Submodule.coe_mem _) ?_
        rw [Submodule.mem_orthogonal]; intro u hu
        have h2 : ⟪u, magicΔ W₀ g - V'.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal V' _).mp (V'.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) u hu.2
        have h3 : ⟪u, magicΔ W₀ g - W₁.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal W₁ _).mp (W₁.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) u hu
        have hs : V'.starProjection (magicΔ W₀ g) - W₁.starProjection (magicΔ W₀ g) =
            (magicΔ W₀ g - W₁.starProjection (magicΔ W₀ g)) - (magicΔ W₀ g - V'.starProjection (magicΔ W₀ g)) := by abel
        rw [hs, inner_sub_right, h3, h2, sub_zero]
      rw [hW1_eq]
      have horth : ⟪W₁.starProjection (magicΔ W₀ g), Wᗮ.starProjection (magicΔ W₀ g) - W₁.starProjection (magicΔ W₀ g)⟫_ℂ = 0 := by
        have h2 : ⟪W₁.starProjection (magicΔ W₀ g), magicΔ W₀ g - Wᗮ.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal Wᗮ _).mp (Wᗮ.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) _
            (Submodule.coe_mem (W₁.orthogonalProjectionOnto (magicΔ W₀ g))).1
        have h3 : ⟪W₁.starProjection (magicΔ W₀ g), magicΔ W₀ g - W₁.starProjection (magicΔ W₀ g)⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal W₁ _).mp (W₁.sub_starProjection_mem_orthogonal (magicΔ W₀ g)) _ (Submodule.coe_mem _)
        have hs : Wᗮ.starProjection (magicΔ W₀ g) - W₁.starProjection (magicΔ W₀ g) =
            (magicΔ W₀ g - W₁.starProjection (magicΔ W₀ g)) - (magicΔ W₀ g - Wᗮ.starProjection (magicΔ W₀ g)) := by abel
        rw [hs, inner_sub_right, h3, h2, sub_zero]
      have hsplit : Wᗮ.starProjection (magicΔ W₀ g) =
          W₁.starProjection (magicΔ W₀ g) + (Wᗮ.starProjection (magicΔ W₀ g) - W₁.starProjection (magicΔ W₀ g)) := by abel
      have hpyth : ‖Wᗮ.starProjection (magicΔ W₀ g)‖ ^ 2 =
          ‖W₁.starProjection (magicΔ W₀ g)‖ ^ 2 + ‖Wᗮ.starProjection (magicΔ W₀ g) - W₁.starProjection (magicΔ W₀ g)‖ ^ 2 := by
        conv_lhs => rw [hsplit]
        rw [norm_add_sq (𝕜 := ℂ), horth]; simp
      linarith [sq_nonneg ‖Wᗮ.starProjection (magicΔ W₀ g) - W₁.starProjection (magicΔ W₀ g)‖]
    refine h1.trans ?_
    rw [PiLp.norm_sq_eq_of_L2]
    calc ∑ y : MagicVtx, ‖Wᗮ.starProjection (magicΔ W₀ g) y‖ ^ 2
        = ∑ y : MagicVtx, (‖P1 y (∑ y' ∈ magicNbrs y, (g y - g y'))‖ ^ 2 +
            ‖P2 y (∑ y' ∈ magicNbrs y, (g y - g y'))‖ ^ 2) :=
          Finset.sum_congr rfl fun y _ => by rw [hPW'_apply, magicΔ_apply, hdecomp2_G']
      _ ≤ ∑ y : MagicVtx, ((1 + 1 / Real.sqrt 2) * ∑ y' ∈ magicNbrs y, ‖P1 y (g y - g y')‖ ^ 2 +
            2 * ∑ y' ∈ magicNbrs y, ‖P2 y (g y - g y')‖ ^ 2) := by
          refine Finset.sum_le_sum fun y _ => ?_
          have hrho := A.claim_rho π₀ y (fun y' => g y - g y') (fun y' hy' => hVprime_diff g hgV' y y' hy')
          exact add_le_add hrho.1 hrho.2
      _ = (2 + Real.sqrt 2) * d1 + 4 * d2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          dsimp only [d1, d2]
          have hrt2 : (1 + 1 / Real.sqrt 2) = (2 + Real.sqrt 2) * (1 / 2) := by
            have hne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr zero_lt_two)
            field_simp [hne]; nlinarith [Real.sq_sqrt zero_le_two]
          rw [hrt2]; ring
  have hD_claim_a : D ≤ 3 * d1 + 5 * d3 := A.claim_a π₀ (fun y => g y) (hVprime_diff g hgV')
  have hrt2_lo : (1.4 : ℝ) < Real.sqrt 2 := by
    have h1 : Real.sqrt (1.4 ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hrt2_hi : Real.sqrt 2 < (1.42 : ℝ) := by
    have h1 : Real.sqrt 2 < Real.sqrt (1.42 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have hstep1 : ‖W₁.starProjection x‖ ^ 2 ≤
      ((10 + Real.sqrt 2) / 3) * D - ((2 + 5 * Real.sqrt 2) / 3) * d3 := by
    have hmul : (2 - Real.sqrt 2) * (D - 5 * d3) ≤ (2 - Real.sqrt 2) * (3 * d1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hstep2 : ‖W₁.starProjection x‖ ^ 2 ≤
      ((10 + Real.sqrt 2) / 12) * ‖x‖ ^ 2 - ((2 + 5 * Real.sqrt 2) / 24) * (‖x‖ ^ 2 - ‖W₁.starProjection x‖ ^ 2) := by
    have hm1 : ((10 + Real.sqrt 2) / 3) * D ≤ ((10 + Real.sqrt 2) / 3) * ((1 / 4 : ℝ) * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hD_le (by linarith)
    have hm2 : ((2 + 5 * Real.sqrt 2) / 3) * ((1 / 8 : ℝ) * (‖x‖ ^ 2 - ‖W₁.starProjection x‖ ^ 2)) ≤
        ((2 + 5 * Real.sqrt 2) / 3) * d3 :=
      mul_le_mul_of_nonneg_left hd3_ge (by linarith)
    linarith
  have hstep3 : (22 - 5 * Real.sqrt 2) * ‖W₁.starProjection x‖ ^ 2 ≤ (18 - 3 * Real.sqrt 2) * ‖x‖ ^ 2 := by linarith
  have hcoeff : 15 * (18 - 3 * Real.sqrt 2) ≤ 14 * (22 - 5 * Real.sqrt 2) := by linarith
  have hpos_c : 0 < 22 - 5 * Real.sqrt 2 := by linarith
  nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖W₁.starProjection x‖]

/-- Main spectral-codistance estimate of EJZ Theorem 5.6: `EpsOrth (magicU W₀) (A.magicW π₀) (√(14/15))`. -/
lemma A2Sys.magic_UW_epsOrth {C W₀ : Type} [Group C] [NormedAddCommGroup W₀]
    [InnerProductSpace ℂ W₀] [CompleteSpace W₀]
    (A : A2Sys C) (π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀) (htriv : invSubspace π₀ ⊤ = ⊥) :
    EpsOrth (magicU W₀) (A.magicW π₀) (Real.sqrt (14 / 15)) := by
  let Ω0 := PiLp 2 (fun _ : MagicVtx => W₀)
  let U := magicU W₀
  let W := A.magicW π₀
  have hW_cl : IsClosed (W : Set Ω0) := A.isClosed_magicW π₀
  let V' : Submodule ℂ Ω0 := (U ⊔ W).topologicalClosure
  have hV'_cl : IsClosed (V' : Set Ω0) := (U ⊔ W).isClosed_topologicalClosure
  let U₁ : Submodule ℂ Ω0 := Uᗮ ⊓ V'
  let W₁ : Submodule ℂ Ω0 := Wᗮ ⊓ V'
  have hW₁_cl : IsClosed (W₁ : Set Ω0) := W.isClosed_orthogonal.inter hV'_cl
  have : W₁.HasOrthogonalProjection := hasOrthProj_of_isClosed hW₁_cl
  have hmain_U₁ : ∀ x : Ω0, x ∈ U₁ → ‖W₁.starProjection x‖ ^ 2 ≤ (14 / 15 : ℝ) * ‖x‖ ^ 2 :=
    fun _ hx => A.magic_UW_step1 π₀ V' rfl W₁ rfl hx
  -- Step 2: Translate `EpsOrth U₁ W₁ (√(14/15))` to `EpsOrth U W (√(14/15))` via EJZ Lemma 2.1 in `V'`
  have : CompleteSpace V' := hV'_cl.completeSpace_coe
  let U' : Submodule ℂ V' := U.comap V'.subtype
  let W' : Submodule ℂ V' := W.comap V'.subtype
  have : U'.HasOrthogonalProjection := hasOrthProj_of_isClosed ((isClosed_magicU W₀).preimage continuous_subtype_val)
  have : W'.HasOrthogonalProjection := hasOrthProj_of_isClosed (hW_cl.preimage continuous_subtype_val)
  have hU'W'_orth_dense : (U'ᗮ ⊔ W'ᗮ).topologicalClosure = ⊤ := by
    have : (U'ᗮ ⊔ W'ᗮ).topologicalClosure.HasOrthogonalProjection :=
      hasOrthProj_of_isClosed (U'ᗮ ⊔ W'ᗮ).isClosed_topologicalClosure
    rw [← Submodule.orthogonal_orthogonal (U'ᗮ ⊔ W'ᗮ).topologicalClosure]
    rw [eq_top_iff]; intro u _
    rw [Submodule.mem_orthogonal]; intro z hz
    have hzU' : z ∈ U' := by
      rw [← Submodule.orthogonal_orthogonal U', Submodule.mem_orthogonal]
      intro a ha; exact (Submodule.mem_orthogonal _ z).mp hz a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_left ha))
    have hzW' : z ∈ W' := by
      rw [← Submodule.orthogonal_orthogonal W', Submodule.mem_orthogonal]
      intro a ha; exact (Submodule.mem_orthogonal _ z).mp hz a (Submodule.le_topologicalClosure _ (Submodule.mem_sup_right ha))
    have hz0 : z = 0 := by
      have hzu : ∀ y₁ y₂ : MagicVtx, z.1 y₁ = z.1 y₂ := hzU'
      have hzw : ∀ y : MagicVtx, z.1 y ∈ invSubspace π₀ (A.Gsub y) := hzW'
      obtain ⟨y₀⟩ : Nonempty MagicVtx := ⟨⟨(0, 1), by decide⟩⟩
      have hw0_inv : z.1 y₀ ∈ invSubspace π₀ ⊤ := by
        have htop_C : Subgroup.closure (⋃ y : MagicVtx, (A.Gsub y : Set C)) = ⊤ := by
          rw [eq_top_iff, ← A.gen, Subgroup.closure_le]
          rintro _ ⟨i, j, hij, rfl⟩
          exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨⟨(i, j), hij⟩, A.X_le_G ⟨(i, j), hij⟩ (Subgroup.subset_closure rfl)⟩)
        rw [← htop_C, invSubspace_closure]
        intro g hg
        obtain ⟨y, hy⟩ := Set.mem_iUnion.mp hg
        rw [hzu y₀ y]; exact hzw y g hy
      rw [htriv, Submodule.mem_bot] at hw0_inv
      apply Subtype.ext; ext y; rw [hzu y y₀]; exact hw0_inv
    rw [hz0, inner_zero_left]
  have hU'W'_orth : EpsOrth U'ᗮ W'ᗮ (Real.sqrt (14 / 15)) := by
    rw [epsOrth_iff_proj_le (Real.sqrt_nonneg _)]
    intro ⟨x, hxV'⟩ hxU'
    have hxU₁ : x ∈ U₁ := by
      refine ⟨?_, hxV'⟩
      rw [SetLike.mem_coe, Submodule.mem_orthogonal]; intro u hu
      exact (Submodule.mem_orthogonal U' ⟨x, hxV'⟩).mp hxU' ⟨u, Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hu)⟩ hu
    have hproj_eq : (W'ᗮ.starProjection ⟨x, hxV'⟩).1 = W₁.starProjection x := by
      symm; refine W₁.eq_starProjection_of_mem_orthogonal ?_ ?_
      · refine ⟨?_, (W'ᗮ.starProjection ⟨x, hxV'⟩).2⟩
        rw [SetLike.mem_coe, Submodule.mem_orthogonal]; intro w hw
        exact (Submodule.mem_orthogonal W' _).mp (Submodule.coe_mem (W'ᗮ.orthogonalProjectionOnto ⟨x, hxV'⟩))
          ⟨w, Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hw)⟩ hw
      · rw [Submodule.mem_orthogonal]; intro u hu
        have huW' : (⟨u, hu.2⟩ : V') ∈ W'ᗮ := by
          rw [Submodule.mem_orthogonal]; intro w hw; exact (Submodule.mem_orthogonal W u).mp hu.1 w.1 hw
        exact (Submodule.mem_orthogonal W'ᗮ _).mp (W'ᗮ.sub_starProjection_mem_orthogonal ⟨x, hxV'⟩) ⟨u, hu.2⟩ huW'
    have hsq : ‖W'ᗮ.starProjection ⟨x, hxV'⟩‖ ^ 2 ≤ (Real.sqrt (14 / 15) * ‖(⟨x, hxV'⟩ : V')‖) ^ 2 := by
      change ‖(W'ᗮ.starProjection ⟨x, hxV'⟩).1‖ ^ 2 ≤ (Real.sqrt (14 / 15) * ‖x‖) ^ 2
      rw [hproj_eq, mul_pow, Real.sq_sqrt (by positivity)]
      exact hmain_U₁ x hxU₁
    have hrt := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt
  have hfin := epsOrth_orth_of_closure_sup_eq_top (Real.sqrt_nonneg _) hU'W'_orth hU'W'_orth_dense
  intro u hu w hw
  have hu' : (⟨u, Submodule.le_topologicalClosure _ (Submodule.mem_sup_left hu)⟩ : V') ∈ U'ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal]; exact hu
  have hw' : (⟨w, Submodule.le_topologicalClosure _ (Submodule.mem_sup_right hw)⟩ : V') ∈ W'ᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal]; exact hw
  exact hfin _ hu' _ hw'

/-- Ershov–Jaikin-Zapirain Theorem 5.6 (Magic graph on 6 vertices):
For any `A₂`-system generated by 6 shears `c i j` (`i ≠ j`), in any unitary representation,
`‖v‖^2 ≤ 30 * ∑ i ≠ j, ‖(V^{X_{ij}})ᗮ.starProjection v‖^2` for `v ⊥ V^C`. -/
lemma magic_graph_proj_bound {G : Type} [Group G]
    (c : Fin 3 → Fin 3 → G)
    (hc_diag : ∀ i, c i i = 1)
    (hc_comm : ∀ i j k l, i ≠ l → j ≠ k → ⁅c i j, c k l⁆ = 1)
    (hc_stein : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ⁅c i j, c j k⁆ = c i k) :
    let C := Subgroup.closure {g : G | ∃ i j : Fin 3, i ≠ j ∧ c i j = g}
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
      (π : C →* V ≃ₗᵢ[ℂ] V) (v : V), v ∈ (invSubspace π ⊤)ᗮ →
      ‖v‖ ^ 2 ≤ 30 * ∑ y : MagicVtx,
        ‖(invSubspace π (Subgroup.closure {⟨c y.1.1 y.1.2, Subgroup.subset_closure ⟨y.1.1, y.1.2, y.2, rfl⟩⟩}))ᗮ.starProjection v‖ ^ 2 := by
  intro C V _ _ _ π v hv
  have hW₀_inv : ∀ (g : C) (u : V), u ∈ (invSubspace π ⊤)ᗮ → π g u ∈ (invSubspace π ⊤)ᗮ := fun g u hu =>
    invSubspace_orth_mem_of_norm π (fun _ _ => Subgroup.mem_top _) hu
  let W₀ := (invSubspace π ⊤)ᗮ
  have : CompleteSpace W₀ := (invSubspace π ⊤).isClosed_orthogonal.completeSpace_coe
  let π₀ : C →* W₀ ≃ₗᵢ[ℂ] W₀ := restrictRep π W₀ hW₀_inv
  have htriv : invSubspace π₀ ⊤ = ⊥ := by
    ext u; simp only [Submodule.mem_bot]
    constructor
    · intro h; apply Subtype.ext
      have huG : u.1 ∈ invSubspace π ⊤ := fun g _ => congrArg Subtype.val (h g trivial)
      exact inner_self_eq_zero.mp ((Submodule.mem_orthogonal (invSubspace π ⊤) u.1).mp u.2 u.1 huG)
    · rintro rfl g _; exact map_zero _
  let cL : Fin 3 → Fin 3 → C := fun i j =>
    if h : i ≠ j then ⟨c i j, Subgroup.subset_closure ⟨i, j, h, rfl⟩⟩ else 1
  have hcL_val : ∀ i j, (cL i j).1 = c i j := fun i j => by
    dsimp only [cL]; split_ifs with h
    · rfl
    · push Not at h; subst h; exact (hc_diag i).symm
  let A : A2Sys C :=
    { cL := cL
      diag := fun i => Subtype.ext (by rw [hcL_val, Subgroup.coe_one, hc_diag])
      comm := fun i j k l hil hjk => by
        rw [commute_iff_eq]; apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hcL_val, hcL_val]
        exact commutatorElement_eq_one_iff_mul_comm.mp (hc_comm i j k l hil hjk)
      stein := fun i j k hij hjk hik => by
        apply Subtype.ext
        simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, hcL_val]
        exact hc_stein i j k hij hjk hik
      gen := by
        have hsub : ∀ z (hz : z ∈ C), (⟨z, hz⟩ : C) ∈ Subgroup.closure {g : C | ∃ i j : Fin 3, i ≠ j ∧ cL i j = g} := by
          intro z hz
          induction hz using Subgroup.closure_induction with
          | mem u hu =>
            obtain ⟨i, j, hij, rfl⟩ := hu
            exact Subgroup.subset_closure ⟨i, j, hij, Subtype.ext (hcL_val i j)⟩
          | one => exact Subgroup.one_mem _
          | mul a b _ _ iha ihb => exact Subgroup.mul_mem _ iha ihb
          | inv a _ iha => exact Subgroup.inv_mem _ iha
        rw [eq_top_iff]; rintro ⟨z, hz⟩ _; exact hsub z hz }
  have hUW_orth := A.magic_UW_epsOrth π₀ htriv
  let Ω0 := PiLp 2 (fun _ : MagicVtx => W₀)
  let w₀ : W₀ := ⟨v, hv⟩
  let u₀ : Ω0 := WithLp.toLp 2 (fun _ : MagicVtx => w₀)
  let f₀ : Ω0 := WithLp.toLp 2 (fun y : MagicVtx => (invSubspace π₀ (A.Gsub y)).starProjection w₀)
  have hu₀_norm : ‖u₀‖ ^ 2 = 6 * ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    have hcard : Fintype.card MagicVtx = 6 := by decide
    simp [u₀, w₀, hcard]
  have hf₀_inner : ⟪u₀, f₀⟫_ℂ = ((‖f₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [PiLp.inner_apply, PiLp.norm_sq_eq_of_L2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    change ⟪w₀, (invSubspace π₀ (A.Gsub y)).starProjection w₀⟫_ℂ = _
    have horth : ⟪w₀ - (invSubspace π₀ (A.Gsub y)).starProjection w₀, (invSubspace π₀ (A.Gsub y)).starProjection w₀⟫_ℂ = 0 :=
      (invSubspace π₀ (A.Gsub y)).starProjection_inner_eq_zero w₀ _ (Submodule.coe_mem _)
    rw [inner_sub_left, sub_eq_zero] at horth
    rw [horth, inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]; rfl
  have hf₀_le : ‖f₀‖ ^ 2 ≤ (14 / 15 : ℝ) * (6 * ‖v‖ ^ 2) := by
    have h1 := hUW_orth u₀ (fun _ _ => rfl) f₀ (fun y => Submodule.coe_mem _)
    rw [hf₀_inner, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h1
    by_cases hf0 : ‖f₀‖ = 0
    · rw [hf0, zero_pow two_ne_zero]; positivity
    · have hfpos : 0 < ‖f₀‖ := lt_of_le_of_ne (norm_nonneg f₀) (Ne.symm hf0)
      have h2 : ‖f₀‖ ≤ Real.sqrt (14 / 15) * ‖u₀‖ := by nlinarith
      have hsq := pow_le_pow_left₀ (norm_nonneg _) h2 2
      rw [mul_pow, Real.sq_sqrt (by positivity), hu₀_norm] at hsq; exact hsq
  have hG_sum : (2 / 5 : ℝ) * ‖v‖ ^ 2 ≤ ∑ y : MagicVtx, ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w₀‖ ^ 2 := by
    have hpyth_sum : ∑ y : MagicVtx, (‖(invSubspace π₀ (A.Gsub y)).starProjection w₀‖ ^ 2 +
        ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w₀‖ ^ 2) = 6 * ‖v‖ ^ 2 := by
      have hterm : ∀ y : MagicVtx, ‖(invSubspace π₀ (A.Gsub y)).starProjection w₀‖ ^ 2 +
          ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w₀‖ ^ 2 = ‖v‖ ^ 2 := fun y =>
        ((invSubspace π₀ (A.Gsub y)).norm_sq_eq_add_norm_sq_projection w₀).symm
      simp_rw [hterm, Finset.sum_const, Finset.card_univ, show Fintype.card MagicVtx = 6 by decide, nsmul_eq_mul, Nat.cast_ofNat]
    rw [Finset.sum_add_distrib] at hpyth_sum
    have hf₀_eq : ‖f₀‖ ^ 2 = ∑ y : MagicVtx, ‖(invSubspace π₀ (A.Gsub y)).starProjection w₀‖ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
    linarith
  have hstep_X : ∀ y : MagicVtx,
      (1 - 1 / Real.sqrt 2) * ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w₀‖ ^ 2 ≤
        ‖(invSubspace π₀ (A.Xsub y.1.1 (thirdIdx y.1.1 y.1.2)))ᗮ.starProjection w₀‖ ^ 2 +
        ‖(invSubspace π₀ (A.Xsub (thirdIdx y.1.1 y.1.2) y.1.2))ᗮ.starProjection w₀‖ ^ 2 := by
    rintro ⟨⟨i, j⟩, hij⟩
    set k := thirdIdx i j
    have hik : i ≠ k := (thirdIdx_ne_left hij).symm
    have hkj : k ≠ j := thirdIdx_ne_right hij
    set Gy := A.Gsub ⟨(i, j), hij⟩
    let Ha : Subgroup Gy := (A.Xsub i k).comap Gy.subtype
    let Hb : Subgroup Gy := (A.Xsub k j).comap Gy.subtype
    have hgen_Gy : Ha ⊔ Hb = ⊤ := by
      have hsub : ∀ z (hz : z ∈ Subgroup.closure ((A.Xsub i k : Set C) ∪ (A.Xsub k j : Set C)))
          (hzG : z ∈ Gy), (⟨z, hzG⟩ : Gy) ∈ Ha ⊔ Hb := by
        intro z hz
        induction hz using Subgroup.closure_induction with
        | mem a ha =>
          intro _; rcases ha with ha | ha
          · exact Subgroup.mem_sup_left ha
          · exact Subgroup.mem_sup_right ha
        | one => intro _; exact Subgroup.one_mem _
        | mul a b ha hb iha ihb =>
          intro _
          exact Subgroup.mul_mem _ (iha (by dsimp only [Gy, A2Sys.Gsub]; rwa [Subgroup.sup_eq_closure]))
            (ihb (by dsimp only [Gy, A2Sys.Gsub]; rwa [Subgroup.sup_eq_closure]))
        | inv a ha iha =>
          intro _
          exact Subgroup.inv_mem _ (iha (by dsimp only [Gy, A2Sys.Gsub]; rwa [Subgroup.sup_eq_closure]))
      rw [eq_top_iff]; rintro ⟨z, hz⟩ _
      exact hsub z (by dsimp only [Gy, A2Sys.Gsub] at hz; rwa [Subgroup.sup_eq_closure] at hz) hz
    have hheis_Gy : SubgroupEpsOrth Ha Hb (1 / Real.sqrt 2) := by
      let c1 : Gy := ⟨A.cL i k, Subgroup.mem_sup_left (Subgroup.subset_closure rfl)⟩
      let c2 : Gy := ⟨A.cL k j, Subgroup.mem_sup_right (Subgroup.subset_closure rfl)⟩
      have hHa_eq : Ha = Subgroup.closure {c1} := by
        apply le_antisymm
        · have hsub : ∀ z (hz : z ∈ A.Xsub i k) (hzG : z ∈ Gy), (⟨z, hzG⟩ : Gy) ∈ Subgroup.closure {c1} := by
            intro z hz
            induction hz using Subgroup.closure_induction with
            | mem a ha => rcases ha with rfl; intro _; exact Subgroup.subset_closure rfl
            | one => intro _; exact Subgroup.one_mem _
            | mul a b ha hb iha ihb => intro _; exact Subgroup.mul_mem _ (iha (Subgroup.mem_sup_left ha)) (ihb (Subgroup.mem_sup_left hb))
            | inv a ha iha => intro _; exact Subgroup.inv_mem _ (iha (Subgroup.mem_sup_left ha))
          rintro ⟨z, hzG⟩ hz; exact hsub z hz hzG
        · rw [Subgroup.closure_le, Set.singleton_subset_iff]; exact Subgroup.subset_closure rfl
      have hHb_eq : Hb = Subgroup.closure {c2} := by
        apply le_antisymm
        · have hsub : ∀ z (hz : z ∈ A.Xsub k j) (hzG : z ∈ Gy), (⟨z, hzG⟩ : Gy) ∈ Subgroup.closure {c2} := by
            intro z hz
            induction hz using Subgroup.closure_induction with
            | mem a ha => rcases ha with rfl; intro _; exact Subgroup.subset_closure rfl
            | one => intro _; exact Subgroup.one_mem _
            | mul a b ha hb iha ihb => intro _; exact Subgroup.mul_mem _ (iha (Subgroup.mem_sup_right ha)) (ihb (Subgroup.mem_sup_right hb))
            | inv a ha iha => intro _; exact Subgroup.inv_mem _ (iha (Subgroup.mem_sup_right ha))
          rintro ⟨z, hzG⟩ hz; exact hsub z hz hzG
        · rw [Subgroup.closure_le, Set.singleton_subset_iff]; exact Subgroup.subset_closure rfl
      rw [hHa_eq, hHb_eq]
      refine heisenberg_epsOrth c1 c2 ?_ ?_
      · apply Subtype.ext; change Commute ⁅A.cL i k, A.cL k j⁆ (A.cL i k)
        rw [A.stein i k j hik hkj hij]; exact A.comm i j i k hik hij.symm
      · apply Subtype.ext; change Commute ⁅A.cL i k, A.cL k j⁆ (A.cL k j)
        rw [A.stein i k j hik hkj hij]; exact A.comm i j k j hij hkj.symm
    let πGy : Gy →* W₀ ≃ₗᵢ[ℂ] W₀ := π₀.comp Gy.subtype
    set bG := (invSubspace π₀ Gy)ᗮ.starProjection w₀
    have hbG_orth : bG ∈ (invSubspace πGy ⊤)ᗮ := by
      rw [Submodule.mem_orthogonal]; intro u hu
      exact (Submodule.mem_orthogonal (invSubspace π₀ Gy) bG).mp (Submodule.coe_mem _) u (fun g hg => hu ⟨g, hg⟩ trivial)
    have hproj := two_subgroups_proj_sum_ge πGy Ha Hb hgen_Gy (by positivity) hheis_Gy hbG_orth
    have hinv_Ha : invSubspace πGy Ha = invSubspace π₀ (A.Xsub i k) := by
      ext u; constructor
      · intro hu g hg; exact hu ⟨g, Subgroup.mem_sup_left hg⟩ hg
      · intro hu ⟨g, _⟩ hg; exact hu g hg
    have hinv_Hb : invSubspace πGy Hb = invSubspace π₀ (A.Xsub k j) := by
      ext u; constructor
      · intro hu g hg; exact hu ⟨g, Subgroup.mem_sup_right hg⟩ hg
      · intro hu ⟨g, _⟩ hg; exact hu g hg
    have hproj_a : (invSubspace πGy Ha)ᗮ.starProjection bG = (invSubspace π₀ (A.Xsub i k))ᗮ.starProjection w₀ := by
      rw [starProjection_congr (congrArg Submodule.orthogonal hinv_Ha)]
      dsimp only [bG]; rw [(invSubspace π₀ Gy).starProjection_orthogonal_val, map_sub]
      have h0 : (invSubspace π₀ (A.Xsub i k))ᗮ.starProjection ((invSubspace π₀ Gy).starProjection w₀) = 0 := by
        refine (invSubspace π₀ (A.Xsub i k))ᗮ.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
        rw [sub_zero, Submodule.orthogonal_orthogonal]; exact invSubspace_anti π₀ le_sup_left (Submodule.coe_mem _)
      rw [h0, sub_zero]
    have hproj_b : (invSubspace πGy Hb)ᗮ.starProjection bG = (invSubspace π₀ (A.Xsub k j))ᗮ.starProjection w₀ := by
      rw [starProjection_congr (congrArg Submodule.orthogonal hinv_Hb)]
      dsimp only [bG]; rw [(invSubspace π₀ Gy).starProjection_orthogonal_val, map_sub]
      have h0 : (invSubspace π₀ (A.Xsub k j))ᗮ.starProjection ((invSubspace π₀ Gy).starProjection w₀) = 0 := by
        refine (invSubspace π₀ (A.Xsub k j))ᗮ.eq_starProjection_of_mem_orthogonal (Submodule.zero_mem _) ?_
        rw [sub_zero, Submodule.orthogonal_orthogonal]; exact invSubspace_anti π₀ le_sup_right (Submodule.coe_mem _)
      rw [h0, sub_zero]
    rwa [hproj_a, hproj_b] at hproj
  have hsum_X : (1 - 1 / Real.sqrt 2) * (2 / 5 : ℝ) * ‖v‖ ^ 2 ≤
      2 * ∑ y : MagicVtx, ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection w₀‖ ^ 2 := by
    have h1 : (1 - 1 / Real.sqrt 2) * ((2 / 5 : ℝ) * ‖v‖ ^ 2) ≤
        ∑ y : MagicVtx, (1 - 1 / Real.sqrt 2) * ‖(invSubspace π₀ (A.Gsub y))ᗮ.starProjection w₀‖ ^ 2 := by
      rw [← Finset.mul_sum]
      have hrt2 : (1 : ℝ) < Real.sqrt 2 := by
        have := Real.sqrt_lt_sqrt zero_le_one (by norm_num : (1 : ℝ) < 2); simpa using this
      have hpos : 0 ≤ 1 - 1 / Real.sqrt 2 := by
        have : 1 / Real.sqrt 2 < 1 := (div_lt_one (by linarith)).mpr hrt2; linarith
      exact mul_le_mul_of_nonneg_left hG_sum hpos
    have h2 := Finset.sum_le_sum (s := (Finset.univ : Finset MagicVtx)) fun y _ => hstep_X y
    have h3 : ∑ y : MagicVtx, (‖(invSubspace π₀ (A.Xsub y.1.1 (thirdIdx y.1.1 y.1.2)))ᗮ.starProjection w₀‖ ^ 2 +
          ‖(invSubspace π₀ (A.Xsub (thirdIdx y.1.1 y.1.2) y.1.2))ᗮ.starProjection w₀‖ ^ 2) =
        2 * ∑ y : MagicVtx, ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection w₀‖ ^ 2 := by
      rw [Finset.sum_add_distrib]
      let e1 : MagicVtx ≃ MagicVtx :=
        { toFun := fun y => ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩
          invFun := fun y => ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩
          left_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext rfl (by revert i j hij; decide))
          right_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext rfl (by revert i j hij; decide)) }
      let e2 : MagicVtx ≃ MagicVtx :=
        { toFun := fun y => ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩
          invFun := fun y => ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩
          left_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext (by revert i j hij; decide) rfl)
          right_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext (by revert i j hij; decide) rfl) }
      have hs1 := Fintype.sum_equiv e1
        (fun y => ‖(invSubspace π₀ (A.Xsub y.1.1 (thirdIdx y.1.1 y.1.2)))ᗮ.starProjection w₀‖ ^ 2)
        (fun y => ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection w₀‖ ^ 2) (fun _ => rfl)
      have hs2 := Fintype.sum_equiv e2
        (fun y => ‖(invSubspace π₀ (A.Xsub (thirdIdx y.1.1 y.1.2) y.1.2))ᗮ.starProjection w₀‖ ^ 2)
        (fun y => ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection w₀‖ ^ 2) (fun _ => rfl)
      rw [hs1, hs2]; ring
    linarith
  have hnorm_W₀_V : ∀ y : MagicVtx,
      ‖(invSubspace π₀ (A.Xsub y.1.1 y.1.2))ᗮ.starProjection w₀‖ =
        ‖(invSubspace π (Subgroup.closure {⟨c y.1.1 y.1.2, Subgroup.subset_closure ⟨y.1.1, y.1.2, y.2, rfl⟩⟩}))ᗮ.starProjection v‖ := by
    intro y
    have hX_eq : A.Xsub y.1.1 y.1.2 = Subgroup.closure {⟨c y.1.1 y.1.2, Subgroup.subset_closure ⟨y.1.1, y.1.2, y.2, rfl⟩⟩} := by
      change Subgroup.closure {cL y.1.1 y.1.2} = _; dsimp only [cL]; rw [dif_pos y.2]
    set H := Subgroup.closure ({⟨c y.1.1 y.1.2, Subgroup.subset_closure ⟨y.1.1, y.1.2, y.2, rfl⟩⟩} : Set C)
    rw [starProjection_congr (congrArg Submodule.orthogonal (congrArg (invSubspace π₀) hX_eq))]
    have hproj_eq : ((invSubspace π₀ H)ᗮ.starProjection w₀).1 = (invSubspace π H)ᗮ.starProjection v := by
      symm; refine (invSubspace π H)ᗮ.eq_starProjection_of_mem_orthogonal ?_ ?_
      · rw [Submodule.mem_orthogonal]; intro u hu
        have hsplit : u = (invSubspace π ⊤).starProjection u + W₀.starProjection u := by
          dsimp only [W₀]; rw [(invSubspace π ⊤).starProjection_orthogonal_val]; abel
        have hu1 : ⟪(invSubspace π ⊤).starProjection u, ((invSubspace π₀ H)ᗮ.starProjection w₀).1⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal (invSubspace π ⊤) _).mp ((invSubspace π₀ H)ᗮ.starProjection w₀).2 _ (Submodule.coe_mem _)
        have hu2_mem : (⟨W₀.starProjection u, Submodule.coe_mem _⟩ : W₀) ∈ invSubspace π₀ H := by
          intro g hg; apply Subtype.ext
          have h1 : W₀.starProjection u = u - (invSubspace π ⊤).starProjection u := by
            dsimp only [W₀]; rw [(invSubspace π ⊤).starProjection_orthogonal_val]
          have htop_fix : π g ((invSubspace π ⊤).starProjection u) = (invSubspace π ⊤).starProjection u :=
            (Submodule.coe_mem ((invSubspace π ⊤).orthogonalProjectionOnto u)) g trivial
          change π g (W₀.starProjection u) = W₀.starProjection u
          rw [h1, map_sub, hu g hg, htop_fix]
        have hu2 : ⟪W₀.starProjection u, ((invSubspace π₀ H)ᗮ.starProjection w₀).1⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal (invSubspace π₀ H) _).mp (Submodule.coe_mem _) _ hu2_mem
        rw [hsplit, inner_add_left, hu1, hu2, add_zero]
      · rw [Submodule.mem_orthogonal]; intro u hu
        have huW₀ : u ∈ W₀ := Submodule.orthogonal_le (invSubspace_anti π le_top) hu
        have huH' : (⟨u, huW₀⟩ : W₀) ∈ (invSubspace π₀ H)ᗮ := by
          rw [Submodule.mem_orthogonal]; intro a ha
          exact (Submodule.mem_orthogonal (invSubspace π H) u).mp hu a.1 (fun g hg => congrArg Subtype.val (ha g hg))
        exact (Submodule.mem_orthogonal (invSubspace π₀ H)ᗮ _).mp ((invSubspace π₀ H)ᗮ.sub_starProjection_mem_orthogonal w₀) ⟨u, huW₀⟩ huH'
    change ‖((invSubspace π₀ H)ᗮ.starProjection w₀).1‖ = _
    rw [hproj_eq]
  simp_rw [hnorm_W₀_V] at hsum_X
  have hrt2_lo : (1.4 : ℝ) < Real.sqrt 2 := by
    have h1 : Real.sqrt (1.4 ^ 2) < Real.sqrt 2 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [Real.sqrt_sq (by norm_num)] at h1
  have h1m : (1 / 4 : ℝ) ≤ 1 - 1 / Real.sqrt 2 := by
    have : 1 / Real.sqrt 2 < 3 / 4 := by
      rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
    linarith
  have hnn : 0 ≤ ∑ y : MagicVtx,
      ‖(invSubspace π (Subgroup.closure {⟨c y.1.1 y.1.2, Subgroup.subset_closure ⟨y.1.1, y.1.2, y.2, rfl⟩⟩}))ᗮ.starProjection v‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [sq_nonneg ‖v‖]

end HeisenbergAndMagicGraph

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

section ShearsAndFullPropT

/-- Single-vertex projection bound inside `shears_spectralGap`. -/
lemma shears_vertex_bound {G V : Type} [Group G] [DecidableEq G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (c : Fin 3 → Fin 3 → G)
    (hc_comm : ∀ i j k l, i ≠ l → j ≠ k → ⁅c i j, c k l⁆ = 1)
    (hc_stein : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ⁅c i j, c j k⁆ = c i k)
    (C : Subgroup G) (cV : MagicVtx → C) (hcV : ∀ y : MagicVtx, (cV y).1 = c y.1.1 y.1.2)
    (C' : Subgroup G) (eC : C ≃* C') (heC : ∀ g : C, (eC g).1 = g.1)
    (π : C →* V ≃ₗᵢ[ℂ] V) (v : V) (y : MagicVtx) (hy_mem : c y.1.1 y.1.2 ∈ C') :
    let π' : C' →* V ≃ₗᵢ[ℂ] V := π.comp eC.symm.toMonoidHom
    ‖(invSubspace π' (Subgroup.closure {⟨c y.1.1 y.1.2, hy_mem⟩}))ᗮ.starProjection v‖ ^ 2 ≤
      6500 * (‖π (cV y) v - v‖ ^ 2 +
        ‖π (cV ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩) v - v‖ ^ 2 +
        ‖π (cV ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩) v - v‖ ^ 2 +
        ‖π (cV ⟨(thirdIdx y.1.1 y.1.2, y.1.1), thirdIdx_ne_left y.2⟩) v - v‖ ^ 2) := by
  intro π'
  rcases y with ⟨⟨a, b⟩, hab⟩
  set d := thirdIdx a b
  have had : a ≠ d := (thirdIdx_ne_left hab).symm
  have hdb : d ≠ b := thirdIdx_ne_right hab
  let e₁ : C := cV ⟨(a, b), hab⟩
  let e₂ : C := cV ⟨(d, b), hdb⟩
  let α : C := cV ⟨(a, d), had⟩
  let β : C := cV ⟨(d, a), had.symm⟩
  have he₁_val : e₁.1 = c a b := hcV ⟨(a, b), hab⟩
  have he₂_val : e₂.1 = c d b := hcV ⟨(d, b), hdb⟩
  have hα_val : α.1 = c a d := hcV ⟨(a, d), had⟩
  have hβ_val : β.1 = c d a := hcV ⟨(d, a), had.symm⟩
  have he₁₂ : Commute e₁ e₂ := by
    rw [commute_iff_eq]; apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, he₁_val, he₂_val]
    exact commutatorElement_eq_one_iff_mul_comm.mp (hc_comm a b d b hab hdb.symm)
  have ha1 : α * e₁ * α⁻¹ = e₁ := by
    have hc : Commute α e₁ := by
      rw [commute_iff_eq]; apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hα_val, he₁_val]
      exact commutatorElement_eq_one_iff_mul_comm.mp (hc_comm a d a b hab had.symm)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have ha2 : α * e₂ * α⁻¹ = e₁ * e₂ := by
    apply Subtype.ext
    have hs := hc_stein a d b had hdb hab
    simp only [commutatorElement_def] at hs
    have h1 := congrArg (· * c d b) hs
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hα_val, he₁_val, he₂_val]
    simpa [mul_assoc] using h1
  have hb1 : β * e₁ * β⁻¹ = e₁ * e₂ := by
    apply Subtype.ext
    have hs := hc_stein d a b had.symm hab hdb
    simp only [commutatorElement_def] at hs
    have h1 := congrArg (· * c a b) hs
    have hc := commutatorElement_eq_one_iff_mul_comm.mp (hc_comm a b d b hab hdb.symm)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hβ_val, he₁_val, he₂_val]
    simpa [mul_assoc, hc] using h1
  have hb2 : β * e₂ * β⁻¹ = e₂ := by
    have hc : Commute β e₂ := by
      rw [commute_iff_eq]; apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hβ_val, he₂_val]
      exact commutatorElement_eq_one_iff_mul_comm.mp (hc_comm d a d b hdb had)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hrel := rel_propT_F2_Z2 π e₁ e₂ α β he₁₂ ha1 ha2 hb1 hb2 v
  have hsub_le : (invSubspace π' (Subgroup.closure {⟨c a b, hy_mem⟩}))ᗮ ≤
      (invSubspace π (Subgroup.closure ({e₁, e₂} : Set C)))ᗮ := by
    refine Submodule.orthogonal_le ?_
    intro u hu g hg
    have hmem : eC.symm g ∈ Subgroup.closure ({e₁, e₂} : Set C) := by
      induction hg using Subgroup.closure_induction with
      | mem z hz =>
        rcases hz with rfl
        have hze : eC.symm ⟨c a b, hy_mem⟩ = e₁ := by
          apply eC.injective; rw [eC.apply_symm_apply]; apply Subtype.ext; rw [heC, he₁_val]
        rw [hze]; exact Subgroup.subset_closure (Or.inl rfl)
      | one => simp
      | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
      | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
    exact hu (eC.symm g) hmem
  have hproj_le :
      ‖(invSubspace π' (Subgroup.closure {⟨c a b, hy_mem⟩}))ᗮ.starProjection v‖ ^ 2 ≤
      ‖(invSubspace π (Subgroup.closure ({e₁, e₂} : Set C)))ᗮ.starProjection v‖ ^ 2 := by
    set K₁ := (invSubspace π' (Subgroup.closure {⟨c a b, hy_mem⟩}))ᗮ
    set K₂ := (invSubspace π (Subgroup.closure ({e₁, e₂} : Set C)))ᗮ
    have h1 := K₁.norm_sq_eq_add_norm_sq_projection v
    have h2 := K₂.norm_sq_eq_add_norm_sq_projection v
    have hK₂_orth : K₂ᗮ ≤ K₁ᗮ := Submodule.orthogonal_le hsub_le
    have hrem_le : ‖K₂ᗮ.starProjection v‖ ^ 2 ≤ ‖K₁ᗮ.starProjection v‖ ^ 2 := by
      have horth : ⟪K₂ᗮ.starProjection v, K₁ᗮ.starProjection v - K₂ᗮ.starProjection v⟫_ℂ = 0 := by
        have ha : ⟪K₂ᗮ.starProjection v, v - K₁ᗮ.starProjection v⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal K₁ᗮ _).mp (K₁ᗮ.sub_starProjection_mem_orthogonal v) _ (hK₂_orth (Submodule.coe_mem _))
        have hb : ⟪K₂ᗮ.starProjection v, v - K₂ᗮ.starProjection v⟫_ℂ = 0 :=
          (Submodule.mem_orthogonal K₂ᗮ _).mp (K₂ᗮ.sub_starProjection_mem_orthogonal v) _ (Submodule.coe_mem _)
        have hs : K₁ᗮ.starProjection v - K₂ᗮ.starProjection v = (v - K₂ᗮ.starProjection v) - (v - K₁ᗮ.starProjection v) := by abel
        rw [hs, inner_sub_right, hb, ha, sub_zero]
      have hsplit : K₁ᗮ.starProjection v = K₂ᗮ.starProjection v + (K₁ᗮ.starProjection v - K₂ᗮ.starProjection v) := by abel
      have hpyth : ‖K₁ᗮ.starProjection v‖ ^ 2 = ‖K₂ᗮ.starProjection v‖ ^ 2 + ‖K₁ᗮ.starProjection v - K₂ᗮ.starProjection v‖ ^ 2 := by
        conv_lhs => rw [hsplit]
        rw [norm_add_sq (𝕜 := ℂ), horth]; simp
      linarith [sq_nonneg ‖K₁ᗮ.starProjection v - K₂ᗮ.starProjection v‖]
    have ha1 : ‖K₁.orthogonalProjectionOnto v‖ = ‖K₁.starProjection v‖ := rfl
    have ha2 : ‖K₁ᗮ.orthogonalProjectionOnto v‖ = ‖K₁ᗮ.starProjection v‖ := rfl
    have hb1 : ‖K₂.orthogonalProjectionOnto v‖ = ‖K₂.starProjection v‖ := rfl
    have hb2 : ‖K₂ᗮ.orthogonalProjectionOnto v‖ = ‖K₂ᗮ.starProjection v‖ := rfl
    rw [ha1, ha2] at h1; rw [hb1, hb2] at h2; linarith
  exact hproj_le.trans hrel

lemma sum_magic_four (f : MagicVtx → ℝ) :
    ∑ y : MagicVtx,
      (f y +
       f ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩ +
       f ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩ +
       f ⟨(thirdIdx y.1.1 y.1.2, y.1.1), thirdIdx_ne_left y.2⟩) =
      4 * ∑ y : MagicVtx, f y := by
  simp_rw [Finset.sum_add_distrib]
  let e2 : MagicVtx ≃ MagicVtx :=
    { toFun := fun y => ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩
      invFun := fun y => ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩
      left_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext (thirdIdx_self_left hij) rfl)
      right_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext (thirdIdx_self_left hij) rfl) }
  let e3 : MagicVtx ≃ MagicVtx :=
    { toFun := fun y => ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩
      invFun := fun y => ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩
      left_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext rfl (thirdIdx_self_right hij))
      right_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext rfl (thirdIdx_self_right hij)) }
  let e4 : MagicVtx ≃ MagicVtx :=
    { toFun := fun y => ⟨(thirdIdx y.1.1 y.1.2, y.1.1), thirdIdx_ne_left y.2⟩
      invFun := fun y => ⟨(y.1.2, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_right y.2).symm⟩
      left_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext rfl (thirdIdx_left_self hij))
      right_inv := fun ⟨⟨i, j⟩, hij⟩ => Subtype.ext (Prod.ext (by revert i j hij; decide) rfl) }
  have h2' : ∑ y : MagicVtx, f ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩ = ∑ y : MagicVtx, f y :=
    Fintype.sum_equiv e2 (fun y => f (e2 y)) f (fun _ => rfl)
  have h3' : ∑ y : MagicVtx, f ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩ = ∑ y : MagicVtx, f y :=
    Fintype.sum_equiv e3 (fun y => f (e3 y)) f (fun _ => rfl)
  have h4' : ∑ y : MagicVtx, f ⟨(thirdIdx y.1.1 y.1.2, y.1.1), thirdIdx_ne_left y.2⟩ = ∑ y : MagicVtx, f y :=
    Fintype.sum_equiv e4 (fun y => f (e4 y)) f (fun _ => rfl)
  rw [h2', h3', h4']; ring

lemma sum_magic_le_six_mul {α : Type} [DecidableEq α] (T : Finset α)
    (f : MagicVtx → α) (hf : ∀ y, f y ∈ T) (g : α → ℝ) (hg : ∀ x ∈ T, 0 ≤ g x) :
    ∑ y : MagicVtx, g (f y) ≤ 6 * ∑ x ∈ T, g x := by
  calc ∑ y : MagicVtx, g (f y)
      ≤ ∑ _y : MagicVtx, ∑ x ∈ T, g x :=
        Finset.sum_le_sum fun y _ => Finset.single_le_sum hg (hf y)
    _ = 6 * ∑ x ∈ T, g x := by
        rw [Finset.sum_const, Finset.card_univ, show Fintype.card MagicVtx = 6 by decide, nsmul_eq_mul, Nat.cast_ofNat]

/-- Spectral gap for the shear subgroup `C = ⟨c i j | i ≠ j⟩` by combining the magic graph bound
(EJZ Theorem 5.6) with relative Property (T) for `(F₂ ⋉ ℤ², ℤ²)`. -/
lemma shears_spectralGap {G : Type} [Group G] [DecidableEq G]
    (c : Fin 3 → Fin 3 → G)
    (hc_diag : ∀ i, c i i = 1)
    (hc_comm : ∀ i j k l, i ≠ l → j ≠ k → ⁅c i j, c k l⁆ = 1)
    (hc_stein : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ⁅c i j, c j k⁆ = c i k) :
    let S : Finset G := (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 ≠ p.2).image (fun p => c p.1 p.2)
    let C := Subgroup.closure (S : Set G)
    HasSpectralGap (S.attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : C)) (1 / 4680000) := by
  intro S C
  have hS_set : (S : Set G) = {g : G | ∃ i j : Fin 3, i ≠ j ∧ c i j = g} := by
    ext g; simp [S]
  have hC_eq : C = Subgroup.closure {g : G | ∃ i j : Fin 3, i ≠ j ∧ c i j = g} := by
    dsimp only [C]; rw [hS_set]
  let S_C : Finset C := S.attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : C)
  refine ⟨by norm_num, fun V _ _ _ π v hv => ?_⟩
  let C' := Subgroup.closure {g : G | ∃ i j : Fin 3, i ≠ j ∧ c i j = g}
  let eC : C ≃* C' := MulEquiv.subgroupCongr hC_eq
  let π' : C' →* V ≃ₗᵢ[ℂ] V := π.comp eC.symm.toMonoidHom
  have hv' : v ∈ (invSubspace π' ⊤)ᗮ := by
    rw [Submodule.mem_orthogonal] at hv ⊢
    intro u hu; exact hv u (fun g _ => hu (eC g) trivial)
  have hmagic := magic_graph_proj_bound c hc_diag hc_comm hc_stein V π' v hv'
  let cV : MagicVtx → C := fun y =>
    ⟨c y.1.1 y.1.2, Subgroup.subset_closure (Finset.mem_image.mpr ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩)⟩
  have hrel_y : ∀ y : MagicVtx,
      ‖(invSubspace π' (Subgroup.closure {⟨c y.1.1 y.1.2, Subgroup.subset_closure ⟨y.1.1, y.1.2, y.2, rfl⟩⟩}))ᗮ.starProjection v‖ ^ 2 ≤
        6500 * (‖π (cV y) v - v‖ ^ 2 +
          ‖π (cV ⟨(thirdIdx y.1.1 y.1.2, y.1.2), thirdIdx_ne_right y.2⟩) v - v‖ ^ 2 +
          ‖π (cV ⟨(y.1.1, thirdIdx y.1.1 y.1.2), (thirdIdx_ne_left y.2).symm⟩) v - v‖ ^ 2 +
          ‖π (cV ⟨(thirdIdx y.1.1 y.1.2, y.1.1), thirdIdx_ne_left y.2⟩) v - v‖ ^ 2) :=
    fun y => shears_vertex_bound c hc_comm hc_stein C cV (fun _ => rfl) C' eC (fun _ => rfl) π v y _
  have hsum_vtx := sum_magic_four (fun y => ‖π (cV y) v - v‖ ^ 2)
  have hcV_mem : ∀ y : MagicVtx, cV y ∈ S_C := fun y =>
    Finset.mem_image.mpr
      ⟨⟨c y.1.1 y.1.2, Finset.mem_image.mpr ⟨y.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, y.2⟩, rfl⟩⟩,
        Finset.mem_attach _ _, Subtype.ext rfl⟩
  have hsum_SC : ∑ y : MagicVtx, ‖π (cV y) v - v‖ ^ 2 ≤ 6 * ∑ s ∈ S_C, ‖π s v - v‖ ^ 2 :=
    sum_magic_le_six_mul S_C cV hcV_mem (fun s => ‖π s v - v‖ ^ 2) (fun _ _ => sq_nonneg _)
  have hsum_all := Finset.sum_le_sum (s := (Finset.univ : Finset MagicVtx)) fun y _ => hrel_y y
  rw [← Finset.mul_sum, hsum_vtx] at hsum_all
  nlinarith

/-- Combined spectral gap for both `H = ⟨x i j m | i ≠ j, m < 4⟩` and `Q = ⟨H, C⟩`. -/
lemma full_group_spectralGap {G : Type} [Group G] [DecidableEq G]
    (x : Fin 3 → Fin 3 → Fin 7 → G) (c : Fin 3 → Fin 3 → G)
    (hdiag : ∀ i m, x i i m = 1 ∧ c i i = 1)
    (hx5 : ∀ i j m, x i j m ^ 5 = 1)
    (hcomm : ∀ i j k l m n, i ≠ l → j ≠ k → ⁅x i j m, x k l n⁆ = 1 ∧ ⁅c i j, c k l⁆ = 1)
    (hstein : ∀ i j k m, i ≠ j → j ≠ k → i ≠ k →
      ⁅x i j m, x j k 0⁆ = x i k m ∧ ⁅x i j 0, x j k m⁆ = x i k m ∧ ⁅c i j, c j k⁆ = c i k)
    (htriple : ∀ i j k a b m n l, i ≠ j → j ≠ k → i ≠ k → i ≠ b → k ≠ a →
      ⁅⁅x i j m, x j k n⁆, x a b l⁆ = 1)
    (hnorm_gen : ∀ a b i j m,
      c a b * x i j m * (c a b)⁻¹ ∈ Subgroup.closure (Set.range ↿x) ∧
      (c a b)⁻¹ * x i j m * c a b ∈ Subgroup.closure (Set.range ↿x) ∧
      x i j m ∈ Subgroup.closure ({g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g} ∪ Set.range ↿c)) :
    let S_H : Finset G :=
      (Finset.univ.filter fun p : Fin 3 × Fin 3 × Fin 4 => p.1 ≠ p.2.1).image
        (fun p => x p.1 p.2.1 ⟨p.2.2.val, by omega⟩)
    let S_C : Finset G :=
      (Finset.univ.filter fun p : Fin 3 × Fin 3 => p.1 ≠ p.2).image (fun p => c p.1 p.2)
    let H := Subgroup.closure (S_H : Set G)
    let Q := Subgroup.closure ((S_H ∪ S_C : Finset G) : Set G)
    ∃ κ : ℝ, 0 < κ ∧
      HasSpectralGap (S_H.attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : H)) κ ∧
      HasSpectralGap ((S_H ∪ S_C).attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : Q)) κ := by
  classical
  intro S_H S_C H Q
  -- 1. Spectral gap for `H` (`k = 4`)
  obtain ⟨κ_H, hgap_H⟩ := delta_spectralGap x (fun i m => (hdiag i m).1) hx5
    (fun i j k l m n hil hjk => (hcomm i j k l m n hil hjk).1)
    (fun i j k m hij hjk hik => (hstein i j k m hij hjk hik).1)
    htriple (k := 4) (by norm_num) (by norm_num)
  -- 2. Spectral gap for `N = ⟨x i j m | i ≠ j⟩` (`k = 7`) and `C = ⟨c i j | i ≠ j⟩`
  let S_N : Finset G :=
    (Finset.univ.filter fun p : Fin 3 × Fin 3 × Fin 7 => p.1 ≠ p.2.1).image
      (fun p => x p.1 p.2.1 ⟨p.2.2.val, lt_of_lt_of_le p.2.2.isLt le_rfl⟩)
  let N := Subgroup.closure (S_N : Set G)
  let C := Subgroup.closure (S_C : Set G)
  obtain ⟨κ_N, hgap_N⟩ := delta_spectralGap x (fun i m => (hdiag i m).1) hx5
    (fun i j k l m n hil hjk => (hcomm i j k l m n hil hjk).1)
    (fun i j k m hij hjk hik => (hstein i j k m hij hjk hik).1)
    htriple (k := 7) (by norm_num) le_rfl
  have hgap_C := shears_spectralGap c (fun i => (hdiag i 0).2)
    (fun i j k l hil hjk => (hcomm i j k l 0 0 hil hjk).2)
    (fun i j k hij hjk hik => (hstein i j k 0 hij hjk hik).2.2)
  -- Identify `Subgroup.closure (Set.range ↿x) = N` and `Subgroup.closure (E ∪ Set.range ↿c) = Q`
  have hN_eq : Subgroup.closure (Set.range ↿x) = N := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨⟨i, j, m⟩, rfl⟩
      by_cases hij : i = j
      · subst hij; change x i i m ∈ N; rw [(hdiag i m).1]; exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Finset.mem_image.mpr ⟨(i, j, m), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
    · rw [Subgroup.closure_le]
      rintro _ hg
      obtain ⟨⟨i, j, m⟩, _, rfl⟩ := Finset.mem_image.mp hg
      exact Subgroup.subset_closure ⟨(i, j, m), rfl⟩
  have hQ_eq : Subgroup.closure ({g | ∃ i j m, i ≠ j ∧ m.val < 4 ∧ x i j m = g} ∪ Set.range ↿c) = Q := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro g (⟨i, j, m, hij, hm, rfl⟩ | ⟨⟨i, j⟩, rfl⟩)
      · exact Subgroup.subset_closure (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨(i, j, ⟨m.val, hm⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))
      · by_cases hij : i = j
        · subst hij; change c i i ∈ Q; rw [(hdiag i 0).2]; exact Subgroup.one_mem _
        · exact Subgroup.subset_closure (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))
    · rw [Subgroup.closure_le]
      rintro g hg
      rcases Finset.mem_union.mp hg with hgH | hgC
      · obtain ⟨⟨i, j, m⟩, hflt, rfl⟩ := Finset.mem_image.mp hgH
        have hij : i ≠ j := (Finset.mem_filter.mp hflt).2
        exact Subgroup.subset_closure (Or.inl ⟨i, j, ⟨m.val, by omega⟩, hij, m.isLt, rfl⟩)
      · obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hgC
        exact Subgroup.subset_closure (Or.inr ⟨(i, j), rfl⟩)
  have hNQ : N ≤ Q := by
    rw [← hN_eq, Subgroup.closure_le]
    rintro _ ⟨⟨i, j, m⟩, rfl⟩
    rw [← hQ_eq]; exact (hnorm_gen 0 0 i j m).2.2
  have hCQ : C ≤ Q := Subgroup.closure_mono (by intro g hg; exact Finset.mem_union_right _ hg)
  -- Normality of `N' := N.comap Q.subtype` in `Q`
  have hN_norm_Q : ∀ q ∈ Q, ∀ u ∈ N, q * u * q⁻¹ ∈ N ∧ q⁻¹ * u * q ∈ N := by
    have hc_norm_N : ∀ a b : Fin 3, ∀ u ∈ N, c a b * u * (c a b)⁻¹ ∈ N ∧ (c a b)⁻¹ * u * c a b ∈ N := by
      intro a b u hu
      rw [← hN_eq] at hu ⊢
      induction hu using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨⟨i, j, m⟩, rfl⟩ := hz
        exact ⟨(hnorm_gen a b i j m).1, (hnorm_gen a b i j m).2.1⟩
      | one => simp
      | mul x₁ x₂ _ _ hx₁ hx₂ =>
        refine ⟨?_, ?_⟩
        · rw [show c a b * (x₁ * x₂) * (c a b)⁻¹ = (c a b * x₁ * (c a b)⁻¹) * (c a b * x₂ * (c a b)⁻¹) by group]
          exact Subgroup.mul_mem _ hx₁.1 hx₂.1
        · rw [show (c a b)⁻¹ * (x₁ * x₂) * c a b = ((c a b)⁻¹ * x₁ * c a b) * ((c a b)⁻¹ * x₂ * c a b) by group]
          exact Subgroup.mul_mem _ hx₁.2 hx₂.2
      | inv x₁ _ hx₁ =>
        refine ⟨?_, ?_⟩
        · rw [show c a b * x₁⁻¹ * (c a b)⁻¹ = (c a b * x₁ * (c a b)⁻¹)⁻¹ by group]
          exact Subgroup.inv_mem _ hx₁.1
        · rw [show (c a b)⁻¹ * x₁⁻¹ * c a b = ((c a b)⁻¹ * x₁ * c a b)⁻¹ by group]
          exact Subgroup.inv_mem _ hx₁.2
    intro q hq
    induction hq using Subgroup.closure_induction with
    | mem g hg =>
      rcases Finset.mem_union.mp hg with hgH | hgC
      · have hgN : g ∈ N := by
          obtain ⟨⟨i, j, m⟩, hflt, rfl⟩ := Finset.mem_image.mp hgH
          exact Subgroup.subset_closure (Finset.mem_image.mpr
            ⟨(i, j, ⟨m.val, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hflt).2⟩, rfl⟩)
        intro u hu
        exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hgN hu) (Subgroup.inv_mem _ hgN),
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgN) hu) hgN⟩
      · obtain ⟨⟨a, b⟩, _, rfl⟩ := Finset.mem_image.mp hgC
        exact hc_norm_N a b
    | one => intro u hu; simpa using hu
    | mul q₁ q₂ _ _ hq₁ hq₂ =>
      intro u hu
      refine ⟨?_, ?_⟩
      · rw [show q₁ * q₂ * u * (q₁ * q₂)⁻¹ = q₁ * (q₂ * u * q₂⁻¹) * q₁⁻¹ by group]
        exact (hq₁ _ (hq₂ u hu).1).1
      · rw [show (q₁ * q₂)⁻¹ * u * (q₁ * q₂) = q₂⁻¹ * (q₁⁻¹ * u * q₁) * q₂ by group]
        exact (hq₂ _ (hq₁ u hu).2).2
    | inv q₁ _ hq₁ =>
      intro u hu; exact ⟨by simpa using (hq₁ u hu).2, by simpa using (hq₁ u hu).1⟩
  let N' : Subgroup Q := N.comap Q.subtype
  have : N'.Normal := ⟨fun n hn q => (hN_norm_Q q.1 q.2 n.1 hn).1⟩
  -- Transfer `hgap_N` to `N'`
  let eN : N ≃* N' :=
    { toFun := fun u => ⟨⟨u.1, hNQ u.2⟩, u.2⟩
      invFun := fun u => ⟨u.1.1, u.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hgap_N' := hasSpectralGap_of_surjective eN.toMonoidHom eN.surjective hgap_N
  -- Transfer `hgap_C` to `Q ⧸ N'`
  let fC : C →* Q ⧸ N' := (QuotientGroup.mk' N').comp (Subgroup.inclusion hCQ)
  have hfC_surj : Function.Surjective fC := by
    intro qbar
    obtain ⟨⟨g, hgQ⟩, rfl⟩ := QuotientGroup.mk'_surjective N' qbar
    have hsub : ∀ z (hz : z ∈ Q), ∃ c₀ : C, fC c₀ = QuotientGroup.mk' N' ⟨z, hz⟩ := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem g hg =>
        rcases Finset.mem_union.mp hg with hgH | hgC
        · refine ⟨1, ?_⟩
          have hgN : g ∈ N := by
            obtain ⟨⟨i, j, m⟩, hflt, rfl⟩ := Finset.mem_image.mp hgH
            exact Subgroup.subset_closure (Finset.mem_image.mpr
              ⟨(i, j, ⟨m.val, by omega⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hflt).2⟩, rfl⟩)
          rw [map_one]; symm
          exact (QuotientGroup.eq_one_iff _).mpr hgN
        · exact ⟨⟨g, Subgroup.subset_closure hgC⟩, rfl⟩
      | one => exact ⟨1, by rw [map_one]; exact (map_one _).symm⟩
      | mul a b ha hb iha ihb =>
        obtain ⟨ca, hca⟩ := iha; obtain ⟨cb, hcb⟩ := ihb
        exact ⟨ca * cb, by rw [map_mul, hca, hcb, ← map_mul]; rfl⟩
      | inv a ha iha =>
        obtain ⟨ca, hca⟩ := iha
        exact ⟨ca⁻¹, by rw [map_inv, hca, ← map_inv]; rfl⟩
    exact hsub g hgQ
  have hgap_Qquot := hasSpectralGap_of_surjective fC hfC_surj hgap_C
  -- Express generating set of `Q ⧸ N'` as `S_C_Q.image (QuotientGroup.mk' N')`
  let S_C_Q : Finset Q := S_C.attach.image fun s => (⟨s.1, Subgroup.subset_closure (Finset.mem_union_right _ s.2)⟩ : Q)
  have himg_C : (S_C.attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : C)).image fC =
      S_C_Q.image (QuotientGroup.mk' N') := by
    ext qbar
    simp only [Finset.mem_image, Finset.mem_attach, true_and, S_C_Q, fC, MonoidHom.comp_apply]
    constructor
    · rintro ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩; exact ⟨⟨a, Subgroup.subset_closure (Finset.mem_union_right _ ha)⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨a, ha⟩, rfl⟩, rfl⟩; exact ⟨⟨a, Subgroup.subset_closure ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [himg_C] at hgap_Qquot
  -- Apply `hasSpectralGap_extension` to `N'` and `Q ⧸ N'`
  obtain ⟨κ_Q1, hgap_Q1⟩ := hasSpectralGap_extension N' _ S_C_Q hgap_N' hgap_Qquot
  -- Change generating set to `(S_H ∪ S_C).attach.image ...`
  let S_Q : Finset Q := (S_H ∪ S_C).attach.image fun s => (⟨s.1, Subgroup.subset_closure s.2⟩ : Q)
  have hgen_Q : Subgroup.closure (S_Q : Set Q) = ⊤ := by
    have hsub : ∀ z (hz : z ∈ Q), (⟨z, hz⟩ : Q) ∈ Subgroup.closure (S_Q : Set Q) := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem g hg =>
        exact Subgroup.subset_closure (Finset.mem_image.mpr ⟨⟨g, hg⟩, Finset.mem_attach _ _, rfl⟩)
      | one => exact Subgroup.one_mem _
      | mul a b _ _ iha ihb => exact Subgroup.mul_mem _ iha ihb
      | inv a _ iha => exact Subgroup.inv_mem _ iha
    rw [eq_top_iff]; rintro ⟨z, hz⟩ _; exact hsub z hz
  obtain ⟨κ_Q, hgap_Q⟩ := hasSpectralGap_change_gen hgap_Q1 (S₂ := S_Q) (fun g _ => by rw [hgen_Q]; trivial)
  refine ⟨min κ_H κ_Q, lt_min hgap_H.1 hgap_Q.1,
    hasSpectralGap_mono Finset.Subset.rfl (min_le_left _ _) (lt_min hgap_H.1 hgap_Q.1) hgap_H,
    hasSpectralGap_mono Finset.Subset.rfl (min_le_right _ _) (lt_min hgap_H.1 hgap_Q.1) hgap_Q⟩

end ShearsAndFullPropT

/- ### 6. Transfer to tracial matrix ultraproducts and conclusion of `H2` -/

section UltraproductTransfer

open Green100

/-- Normalized squared Frobenius norm of a `k × k` complex matrix. -/
def qMat {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) : ℝ :=
  (∑ a : Fin k, ∑ b : Fin k, ‖A a b‖ ^ 2) / (k : ℝ)

/-- Normalized Hilbert–Schmidt inner product `(1/k) Tr(A^* B)`. -/
def trInner {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) : ℂ :=
  Matrix.trace (star A * B) / (k : ℂ)

lemma trInner_self {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) :
    trInner A A = ((qMat A : ℝ) : ℂ) := by
  dsimp only [trInner, qMat]
  rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_sum]
  congr 1
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow]

lemma trInner_conj_symm {k : ℕ} (A B : Matrix (Fin k) (Fin k) ℂ) :
    (starRingEnd ℂ) (trInner B A) = trInner A B := by
  dsimp only [trInner]
  rw [map_div₀, map_natCast]
  congr 1
  change star (Matrix.trace (star B * A)) = Matrix.trace (star A * B)
  rw [← Matrix.trace_conjTranspose, ← Matrix.star_eq_conjTranspose, star_mul, star_star]

lemma trInner_add_left {k : ℕ} (A B C : Matrix (Fin k) (Fin k) ℂ) :
    trInner (A + B) C = trInner A C + trInner B C := by
  dsimp only [trInner]
  rw [star_add, add_mul, Matrix.trace_add, add_div]

lemma trInner_smul_left {k : ℕ} (c : ℂ) (A B : Matrix (Fin k) (Fin k) ℂ) :
    trInner (c • A) B = (starRingEnd ℂ) c * trInner A B := by
  dsimp only [trInner]
  rw [star_smul, smul_mul_assoc, Matrix.trace_smul, smul_eq_mul, mul_div_assoc]
  rfl

lemma trInner_conj_unitary {k : ℕ} (u : Matrix.unitaryGroup (Fin k) ℂ)
    (A B : Matrix (Fin k) (Fin k) ℂ) :
    trInner ((u : Matrix (Fin k) (Fin k) ℂ) * A * star (u : Matrix (Fin k) (Fin k) ℂ))
            ((u : Matrix (Fin k) (Fin k) ℂ) * B * star (u : Matrix (Fin k) (Fin k) ℂ)) =
      trInner A B := by
  dsimp only [trInner]
  congr 1
  have hu : star (u : Matrix (Fin k) (Fin k) ℂ) * (u : Matrix (Fin k) (Fin k) ℂ) = 1 :=
    Unitary.star_mul_self_of_mem u.2
  have h1 : star ((u : Matrix (Fin k) (Fin k) ℂ) * A * star (u : Matrix (Fin k) (Fin k) ℂ)) *
      ((u : Matrix (Fin k) (Fin k) ℂ) * B * star (u : Matrix (Fin k) (Fin k) ℂ)) =
      ((u : Matrix (Fin k) (Fin k) ℂ) * star A * B) * star (u : Matrix (Fin k) (Fin k) ℂ) := by
    rw [star_mul, star_mul, star_star]
    calc (u : Matrix _ _ ℂ) * (star A * star (u : Matrix _ _ ℂ)) * ((u : Matrix _ _ ℂ) * B * star (u : Matrix _ _ ℂ))
        = (u : Matrix _ _ ℂ) * star A * (star (u : Matrix _ _ ℂ) * (u : Matrix _ _ ℂ)) * B * star (u : Matrix _ _ ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = ((u : Matrix _ _ ℂ) * star A * B) * star (u : Matrix _ _ ℂ) := by
          rw [hu, Matrix.mul_one]
  rw [h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu, Matrix.one_mul]

lemma qMat_le_opNorm_sq {k : ℕ} (hk : 0 < k) (A : Matrix (Fin k) (Fin k) ℂ) :
    qMat A ≤ ‖Matrix.toEuclideanCLM (n := Fin k) (𝕜 := ℂ) A‖ ^ 2 := by
  dsimp only [qMat]
  have h1 := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.ss_mul_left_le A 1
  rw [Matrix.mul_one] at h1
  have h1sum : ∑ a : Fin k, ∑ b : Fin k, ‖(1 : Matrix (Fin k) (Fin k) ℂ) a b‖ ^ 2 = (k : ℝ) := by
    have hinner : ∀ a : Fin k, ∑ b : Fin k, ‖(1 : Matrix (Fin k) (Fin k) ℂ) a b‖ ^ 2 = 1 := fun a => by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hba; simp [hba.symm]
      · intro h; exact absurd (Finset.mem_univ a) h
    simp [hinner]
  rw [h1sum] at h1
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  rwa [div_le_iff₀ hkpos]

lemma norm_trInner_le {k : ℕ} (hk : 0 < k) (A B : Matrix (Fin k) (Fin k) ℂ) :
    ‖trInner A B‖ ≤ Real.sqrt (qMat A) * Real.sqrt (qMat B) := by
  dsimp only [trInner, qMat]
  have hkpos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  rw [norm_div, Complex.norm_natCast]
  have htr : ‖Matrix.trace (star A * B)‖ ≤ ∑ a : Fin k, ∑ b : Fin k, ‖A a b‖ * ‖B a b‖ := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.star_apply]
    rw [Finset.sum_comm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
    rw [norm_mul, norm_star]
  have hcs : ∑ a : Fin k, ∑ b : Fin k, ‖A a b‖ * ‖B a b‖ ≤
      Real.sqrt (∑ a : Fin k, ∑ b : Fin k, ‖A a b‖ ^ 2) *
      Real.sqrt (∑ a : Fin k, ∑ b : Fin k, ‖B a b‖ ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin k × Fin k))
      (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
    simpa [Fintype.sum_prod_type] using h
  have hsq : Real.sqrt ((∑ a : Fin k, ∑ b : Fin k, ‖A a b‖ ^ 2) / (k : ℝ)) *
      Real.sqrt ((∑ a : Fin k, ∑ b : Fin k, ‖B a b‖ ^ 2) / (k : ℝ)) =
      (Real.sqrt (∑ a : Fin k, ∑ b : Fin k, ‖A a b‖ ^ 2) *
       Real.sqrt (∑ a : Fin k, ∑ b : Fin k, ‖B a b‖ ^ 2)) / (k : ℝ) := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_div (by positivity), div_mul_div_comm,
      Real.mul_self_sqrt (le_of_lt hkpos)]
  rw [hsq]
  exact div_le_div_of_nonneg_right (htr.trans hcs) (le_of_lt hkpos)

/-- Operator-norm-bounded sequence of `d n × d n` complex matrices. -/
structure BSeqH (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) where
  val : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ
  bdd : ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (val n)‖ ≤ C

namespace BSeqH

variable {d : ℕ → ℕ} {hd : ∀ n, 0 < d n}

lemma ext {a b : BSeqH d hd} (h : a.val = b.val) : a = b := by
  cases a; cases b; congr

instance : Zero (BSeqH d hd) := ⟨⟨fun _ => 0, ⟨0, fun _ => by simp⟩⟩⟩

instance : Add (BSeqH d hd) :=
  ⟨fun a b => ⟨fun n => a.val n + b.val n, by
    obtain ⟨Ca, hCa⟩ := a.bdd; obtain ⟨Cb, hCb⟩ := b.bdd
    exact ⟨Ca + Cb, fun n => by rw [map_add]; exact (norm_add_le _ _).trans (add_le_add (hCa n) (hCb n))⟩⟩⟩

instance : Neg (BSeqH d hd) :=
  ⟨fun a => ⟨fun n => -a.val n, by
    obtain ⟨Ca, hCa⟩ := a.bdd
    exact ⟨Ca, fun n => by rw [map_neg, norm_neg]; exact hCa n⟩⟩⟩

instance : Sub (BSeqH d hd) :=
  ⟨fun a b => ⟨fun n => a.val n - b.val n, by
    obtain ⟨Ca, hCa⟩ := a.bdd; obtain ⟨Cb, hCb⟩ := b.bdd
    exact ⟨Ca + Cb, fun n => by rw [map_sub]; exact (norm_sub_le _ _).trans (add_le_add (hCa n) (hCb n))⟩⟩⟩

instance : SMul ℂ (BSeqH d hd) :=
  ⟨fun c a => ⟨fun n => c • a.val n, by
    obtain ⟨Ca, hCa⟩ := a.bdd
    exact ⟨‖c‖ * max Ca 0, fun n => by
      rw [map_smul, norm_smul]
      exact mul_le_mul_of_nonneg_left ((hCa n).trans (le_max_left _ _)) (norm_nonneg c)⟩⟩⟩

instance : AddCommGroup (BSeqH d hd) where
  add_assoc _ _ _ := ext (funext fun _ => add_assoc _ _ _)
  zero_add _ := ext (funext fun _ => zero_add _)
  add_zero _ := ext (funext fun _ => add_zero _)
  neg_add_cancel _ := ext (funext fun _ => neg_add_cancel _)
  add_comm _ _ := ext (funext fun _ => add_comm _ _)
  sub_eq_add_neg _ _ := ext (funext fun _ => sub_eq_add_neg _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : Module ℂ (BSeqH d hd) where
  one_smul _ := ext (funext fun _ => one_smul ℂ _)
  mul_smul c₁ c₂ _ := ext (funext fun _ => mul_smul c₁ c₂ _)
  smul_zero c := ext (funext fun _ => smul_zero c)
  smul_add c _ _ := ext (funext fun _ => smul_add c _ _)
  add_smul c₁ c₂ _ := ext (funext fun _ => add_smul c₁ c₂ _)
  zero_smul _ := ext (funext fun _ => zero_smul ℂ _)

lemma trInner_tendsto (a b : BSeqH d hd) :
    ∃ z : ℂ, Tendsto (fun n => trInner (a.val n) (b.val n)) (hyperfilter ℕ) (𝓝 z) := by
  obtain ⟨Ca, hCa⟩ := a.bdd
  obtain ⟨Cb, hCb⟩ := b.bdd
  set R : ℝ := max Ca 0 * max Cb 0
  have hmem : ∀ n, trInner (a.val n) (b.val n) ∈ Metric.closedBall (0 : ℂ) R := fun n => by
    rw [Metric.mem_closedBall, dist_zero_right]
    have ha : Real.sqrt (qMat (a.val n)) ≤ max Ca 0 := by
      have h1 := Real.sqrt_le_sqrt (qMat_le_opNorm_sq (hd n) (a.val n))
      rw [Real.sqrt_sq (norm_nonneg _)] at h1
      exact h1.trans ((hCa n).trans (le_max_left _ _))
    have hb : Real.sqrt (qMat (b.val n)) ≤ max Cb 0 := by
      have h1 := Real.sqrt_le_sqrt (qMat_le_opNorm_sq (hd n) (b.val n))
      rw [Real.sqrt_sq (norm_nonneg _)] at h1
      exact h1.trans ((hCb n).trans (le_max_left _ _))
    exact (norm_trInner_le (hd n) (a.val n) (b.val n)).trans
      (mul_le_mul ha hb (Real.sqrt_nonneg _) (le_max_right _ _))
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall _ _
  have hmap_mem : Metric.closedBall (0 : ℂ) R ∈ Ultrafilter.map (fun n => trInner (a.val n) (b.val n)) (hyperfilter ℕ) :=
    Filter.mem_map.mpr (Filter.Eventually.of_forall hmem)
  obtain ⟨z, _, hz⟩ := hcomp.ultrafilter_le_nhds' _ hmap_mem
  exact ⟨z, hz⟩

def uInner (a b : BSeqH d hd) : ℂ := Classical.choose (trInner_tendsto a b)

lemma uInner_tendsto (a b : BSeqH d hd) :
    Tendsto (fun n => trInner (a.val n) (b.val n)) (hyperfilter ℕ) (𝓝 (uInner a b)) :=
  Classical.choose_spec (trInner_tendsto a b)

scoped instance instPreCore (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : PreInnerProductSpace.Core ℂ (BSeqH d hd) where
  inner := uInner
  conj_inner_symm a b := by
    have h1 := (Complex.continuous_conj.tendsto _).comp (uInner_tendsto b a)
    have h2 : Tendsto (fun n => (starRingEnd ℂ) (trInner (b.val n) (a.val n))) (hyperfilter ℕ)
        (𝓝 (uInner a b)) := (uInner_tendsto a b).congr fun n => (trInner_conj_symm (a.val n) (b.val n)).symm
    exact tendsto_nhds_unique h1 h2
  re_inner_nonneg a := by
    have hre : Tendsto (fun n => (trInner (a.val n) (a.val n)).re) (hyperfilter ℕ) (𝓝 (uInner a a).re) :=
      (Complex.continuous_re.tendsto _).comp (uInner_tendsto a a)
    refine ge_of_tendsto hre (Filter.Eventually.of_forall fun n => ?_)
    rw [trInner_self, Complex.ofReal_re]
    dsimp only [qMat]; positivity
  add_left a b c := by
    have h1 := (uInner_tendsto a c).add (uInner_tendsto b c)
    have h2 : Tendsto (fun n => trInner (a.val n) (c.val n) + trInner (b.val n) (c.val n)) (hyperfilter ℕ)
        (𝓝 (uInner (a + b) c)) := (uInner_tendsto (a + b) c).congr fun n => trInner_add_left _ _ _
    exact tendsto_nhds_unique h2 h1
  smul_left a b c := by
    have h1 := (uInner_tendsto a b).const_mul ((starRingEnd ℂ) c)
    have h2 : Tendsto (fun n => (starRingEnd ℂ) c * trInner (a.val n) (b.val n)) (hyperfilter ℕ)
        (𝓝 (uInner (c • a) b)) := (uInner_tendsto (c • a) b).congr fun n => trInner_smul_left c _ _
    exact tendsto_nhds_unique h2 h1

scoped instance instSemi (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : SeminormedAddCommGroup (BSeqH d hd) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

scoped instance instIPS (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : InnerProductSpace ℂ (BSeqH d hd) :=
  InnerProductSpace.ofCore (instPreCore d hd)

/-- The tracial matrix ultraproduct Hilbert space `L²(∏_ω M_{d(n)}(ℂ))`. -/
def L2M (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : Type := UniformSpace.Completion (BSeqH d hd)

scoped instance instNormedL2M (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : NormedAddCommGroup (L2M d hd) :=
  inferInstanceAs (NormedAddCommGroup (UniformSpace.Completion (BSeqH d hd)))

scoped instance instIPSL2M (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : InnerProductSpace ℂ (L2M d hd) :=
  inferInstanceAs (InnerProductSpace ℂ (UniformSpace.Completion (BSeqH d hd)))

scoped instance instCompleteL2M (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) : CompleteSpace (L2M d hd) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (BSeqH d hd)))

def toL2 (a : BSeqH d hd) : L2M d hd := (a : UniformSpace.Completion (BSeqH d hd))

def mapL2 (f : BSeqH d hd → BSeqH d hd) : L2M d hd → L2M d hd :=
  UniformSpace.Completion.map f

lemma mapL2_continuous (f : BSeqH d hd → BSeqH d hd) : Continuous (mapL2 f) :=
  UniformSpace.Completion.continuous_map

lemma mapL2_toL2 {f : BSeqH d hd → BSeqH d hd} (hf : UniformContinuous f) (a : BSeqH d hd) :
    mapL2 f (toL2 a) = toL2 (f a) :=
  UniformSpace.Completion.map_coe hf a

lemma toL2_add (a b : BSeqH d hd) : toL2 (a + b) = toL2 a + toL2 b :=
  UniformSpace.Completion.coe_add a b

lemma toL2_sub (a b : BSeqH d hd) : toL2 (a - b) = toL2 a - toL2 b :=
  UniformSpace.Completion.coe_sub a b

lemma toL2_smul (c : ℂ) (a : BSeqH d hd) : toL2 (c • a) = c • toL2 a :=
  UniformSpace.Completion.coe_smul c a

lemma norm_toL2 (a : BSeqH d hd) : ‖toL2 a‖ = ‖a‖ :=
  UniformSpace.Completion.norm_coe a

lemma toL2_induction_on {p : L2M d hd → Prop} (x : L2M d hd)
    (hp : IsClosed {x : L2M d hd | p x}) (ih : ∀ a : BSeqH d hd, p (toL2 a)) : p x :=
  UniformSpace.Completion.induction_on x hp ih

lemma toL2_induction_on₂ {p : L2M d hd → L2M d hd → Prop} (x y : L2M d hd)
    (hp : IsClosed {q : L2M d hd × L2M d hd | p q.1 q.2}) (ih : ∀ a b : BSeqH d hd, p (toL2 a) (toL2 b)) :
    p x y :=
  UniformSpace.Completion.induction_on₂ x y hp ih

lemma qMat_tendsto_norm_sq (a : BSeqH d hd) :
    Tendsto (fun n => qMat (a.val n)) (hyperfilter ℕ) (𝓝 (‖toL2 a‖ ^ 2)) := by
  have h1 : Tendsto (fun n => (trInner (a.val n) (a.val n)).re) (hyperfilter ℕ) (𝓝 (uInner a a).re) :=
    (Complex.continuous_re.tendsto _).comp (uInner_tendsto a a)
  have hnorm : (uInner a a).re = ‖toL2 a‖ ^ 2 := by
    rw [norm_toL2]
    exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) a).symm
  rw [hnorm] at h1
  exact h1.congr fun n => by rw [trInner_self, Complex.ofReal_re]

/-- Unitary conjugation on `BSeqH d hd`. -/
def conjBSeq (u : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (a : BSeqH d hd) : BSeqH d hd where
  val n := (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
  bdd := by
    obtain ⟨C, hC⟩ := a.bdd
    refine ⟨C, fun n => ?_⟩
    have h := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.opnorm_conj_le
      (Unitary.star_mem (u n).2) (a.val n)
    rw [star_star] at h
    exact h.trans (hC n)

lemma conjBSeq_isometry (u : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) :
    Isometry (conjBSeq (hd := hd) u) := by
  rw [isometry_iff_dist_eq]
  intro a b
  rw [dist_eq_norm, dist_eq_norm]
  have hsq : ‖conjBSeq u a - conjBSeq u b‖ ^ 2 = ‖a - b‖ ^ 2 := by
    have hsub : conjBSeq u a - conjBSeq u b = conjBSeq u (a - b) := by
      apply BSeqH.ext; funext n
      change (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) -
        (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * b.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
        (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (a.val n - b.val n) * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
      rw [Matrix.mul_sub, Matrix.sub_mul]
    rw [hsub]
    have h1 := qMat_tendsto_norm_sq (conjBSeq u (a - b))
    have h2 := qMat_tendsto_norm_sq (a - b)
    have heq : ∀ n, qMat ((conjBSeq u (a - b)).val n) = qMat ((a - b).val n) := fun n => by
      have ht := trInner_conj_unitary (u n) ((a - b).val n) ((a - b).val n)
      rw [trInner_self, trInner_self] at ht
      exact Complex.ofReal_injective ht
    have hlim := tendsto_nhds_unique (h1.congr heq) h2
    simpa [norm_toL2] using hlim
  have hrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hrt

/-- Lifting unitary conjugation to a linear isometry equivalence on `L2M d hd`. -/
def conjL2 (u : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) : L2M d hd ≃ₗᵢ[ℂ] L2M d hd where
  toFun := mapL2 (conjBSeq (hd := hd) u)
  invFun := mapL2 (conjBSeq (hd := hd) u⁻¹)
  map_add' x y := by
    have hu := (conjBSeq_isometry (hd := hd) u).uniformContinuous
    refine toL2_induction_on₂
      (p := fun x y => mapL2 (conjBSeq (hd := hd) u) (x + y) =
        mapL2 (conjBSeq (hd := hd) u) x + mapL2 (conjBSeq (hd := hd) u) y) x y
      (isClosed_eq ((mapL2_continuous _).comp continuous_add)
        (((mapL2_continuous _).comp continuous_fst).add ((mapL2_continuous _).comp continuous_snd)))
      (fun a b => ?_)
    rw [← toL2_add, mapL2_toL2 hu, mapL2_toL2 hu, mapL2_toL2 hu, ← toL2_add]
    congr 1; apply BSeqH.ext; funext n
    change (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (a.val n + b.val n) * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
      (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) +
      (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * b.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by
    have hu := (conjBSeq_isometry (hd := hd) u).uniformContinuous
    refine toL2_induction_on
      (p := fun x => mapL2 (conjBSeq (hd := hd) u) (c • x) = c • mapL2 (conjBSeq (hd := hd) u) x) x
      (isClosed_eq ((mapL2_continuous _).comp (continuous_const_smul c))
        ((continuous_const_smul c).comp (mapL2_continuous _)))
      (fun a => ?_)
    rw [← toL2_smul, mapL2_toL2 hu, mapL2_toL2 hu, ← toL2_smul]
    congr 1; apply BSeqH.ext; funext n
    change (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (c • a.val n) * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
      c • ((u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
    rw [Matrix.mul_smul, Matrix.smul_mul]
  left_inv x := by
    have hu := (conjBSeq_isometry (hd := hd) u).uniformContinuous
    have hui := (conjBSeq_isometry (hd := hd) u⁻¹).uniformContinuous
    refine toL2_induction_on
      (p := fun x => mapL2 (conjBSeq (hd := hd) u⁻¹) (mapL2 (conjBSeq (hd := hd) u) x) = x) x
      (isClosed_eq ((mapL2_continuous _).comp (mapL2_continuous _)) continuous_id)
      (fun a => ?_)
    rw [mapL2_toL2 hu, mapL2_toL2 hui]
    congr 1; apply BSeqH.ext; funext n
    change star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
      ((u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) *
      star (star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) = a.val n
    rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.star_mul_self_of_mem (u n).2,
      Matrix.one_mul, Matrix.mul_assoc, Unitary.star_mul_self_of_mem (u n).2, Matrix.mul_one]
  right_inv x := by
    have hu := (conjBSeq_isometry (hd := hd) u).uniformContinuous
    have hui := (conjBSeq_isometry (hd := hd) u⁻¹).uniformContinuous
    refine toL2_induction_on
      (p := fun x => mapL2 (conjBSeq (hd := hd) u) (mapL2 (conjBSeq (hd := hd) u⁻¹) x) = x) x
      (isClosed_eq ((mapL2_continuous _).comp (mapL2_continuous _)) continuous_id)
      (fun a => ?_)
    rw [mapL2_toL2 hui, mapL2_toL2 hu]
    congr 1; apply BSeqH.ext; funext n
    change (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
      (star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ))) *
      star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) = a.val n
    rw [star_star, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Unitary.mul_star_self_of_mem (u n).2,
      Matrix.one_mul, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (u n).2, Matrix.mul_one]
  norm_map' x := by
    have hu := (conjBSeq_isometry (hd := hd) u).uniformContinuous
    refine toL2_induction_on
      (p := fun x => ‖mapL2 (conjBSeq (hd := hd) u) x‖ = ‖x‖) x
      (isClosed_eq (continuous_norm.comp (mapL2_continuous _)) continuous_norm)
      (fun a => ?_)
    rw [mapL2_toL2 hu, norm_toL2, norm_toL2]
    have h0 := (conjBSeq_isometry (hd := hd) u).dist_eq a 0
    have hz : conjBSeq (hd := hd) u 0 = 0 := by
      apply BSeqH.ext; funext n
      change (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * 0 * star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) = 0
      simp
    rw [hz, dist_zero_right, dist_zero_right] at h0
    exact h0

lemma conjL2_coe (u : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (a : BSeqH d hd) :
    conjL2 u (toL2 a) = toL2 (conjBSeq u a) :=
  mapL2_toL2 (conjBSeq_isometry (hd := hd) u).uniformContinuous a

def conjL2Hom (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) →* (L2M d hd ≃ₗᵢ[ℂ] L2M d hd) where
  toFun := conjL2 (hd := hd)
  map_one' := by
    ext x
    refine toL2_induction_on (p := fun x => conjL2 (hd := hd) 1 x = x) x
      (isClosed_eq (conjL2 (hd := hd) 1).continuous continuous_id) (fun a => ?_)
    rw [conjL2_coe]; congr 1; apply BSeqH.ext; funext n; simp [conjBSeq]
  map_mul' u v := by
    ext x
    refine toL2_induction_on (p := fun x => conjL2 (hd := hd) (u * v) x = conjL2 (hd := hd) u (conjL2 (hd := hd) v x)) x
      (isClosed_eq (conjL2 (hd := hd) (u * v)).continuous
        ((conjL2 (hd := hd) u).continuous.comp (conjL2 (hd := hd) v).continuous))
      (fun a => ?_)
    rw [conjL2_coe, conjL2_coe, conjL2_coe]
    congr 1; apply BSeqH.ext; funext n
    change ((u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) * a.val n *
      star ((u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) =
      (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ) *
        ((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n * star (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ)) *
        star (u n : Matrix (Fin (d n)) (Fin (d n)) ℂ)
    rw [star_mul]; simp only [Matrix.mul_assoc]

/-- `conjL2Hom` descends to the quotient `U ⧸ N_U` by asymptotically trivial unitaries. -/
def conjQuot (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) :
    (((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸
      Subgroup.normalClosure {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
        Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)}) →*
      (L2M d hd ≃ₗᵢ[ℂ] L2M d hd) :=
  QuotientGroup.lift _ (conjL2Hom d hd) fun v hv => by
    ext x
    refine toL2_induction_on (p := fun x => conjL2Hom d hd v x = x) x
      (isClosed_eq (conjL2Hom d hd v).continuous continuous_id) (fun a => ?_)
    change conjL2 v (toL2 a) = toL2 a
    rw [conjL2_coe, ← sub_eq_zero, ← norm_eq_zero]
    have hsq : ‖toL2 (conjBSeq v a - a)‖ ^ 2 = 0 := by
      have h1 := qMat_tendsto_norm_sq (conjBSeq v a - a)
      have h2 : Tendsto (fun n => qMat ((conjBSeq v a - a).val n)) (hyperfilter ℕ) (𝓝 0) := by
        obtain ⟨C, hC⟩ := a.bdd
        have hv0 := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.tendsto_of_mem_normalClosure hv
        have hl := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.tendsto_q_mul_right hC hv0
        have hr := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.tendsto_q_mul_left hC hv0
        have hsub := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.tendsto_q_sub hl hr
        refine hsub.congr fun n => ?_
        dsimp only [qMat]
        congr 1
        have heq1 : ((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) * a.val n -
            a.val n * ((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - 1) =
            (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n - a.val n * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) := by
          noncomm_ring
        have heq2 : ((v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n *
            star (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - a.val n) *
            (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
            (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * a.val n - a.val n * (v n : Matrix (Fin (d n)) (Fin (d n)) ℂ) := by
          rw [Matrix.sub_mul, Matrix.mul_assoc, Unitary.star_mul_self_of_mem (v n).2, Matrix.mul_one]
        rw [heq1, ← heq2, _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.ss_mul_unitary (v n).2]
        rfl
      exact tendsto_nhds_unique h1 h2
    rw [toL2_sub] at hsq
    exact sq_eq_zero_iff.mp hsq

lemma conjQuot_mk (u : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) (x : L2M d hd) :
    conjQuot d hd (QuotientGroup.mk u) x = conjL2 u x := rfl

/-- Closed operator-norm ball `K_C` inside `L2M d hd`. -/
def opBall (d : ℕ → ℕ) (hd : ∀ n, 0 < d n) (C : ℝ) : Set (L2M d hd) :=
  {ξ | ∃ a : BSeqH d hd, toL2 a = ξ ∧
    ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (a.val n)‖ ≤ C}

lemma opBall_convex (C : ℝ) : Convex ℝ (opBall d hd C) := by
  rintro _ ⟨a, rfl, ha⟩ _ ⟨b, rfl, hb⟩ t₁ t₂ ht₁ ht₂ hsum
  refine ⟨(t₁ : ℂ) • a + (t₂ : ℂ) • b, ?_, fun n => ?_⟩
  · rw [toL2_add, toL2_smul, toL2_smul]
    exact congrArg₂ (· + ·) (algebraMap_smul ℂ t₁ (toL2 a)) (algebraMap_smul ℂ t₂ (toL2 b))
  · change ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) ((t₁ : ℂ) • a.val n + (t₂ : ℂ) • b.val n)‖ ≤ C
    rw [map_add, map_smul, map_smul]
    calc ‖(t₁ : ℂ) • Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (a.val n) +
            (t₂ : ℂ) • Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (b.val n)‖
        ≤ ‖(t₁ : ℂ) • Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (a.val n)‖ +
            ‖(t₂ : ℂ) • Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (b.val n)‖ :=
          norm_add_le _ _
      _ = t₁ * ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (a.val n)‖ +
            t₂ * ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (b.val n)‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg ht₁, Real.norm_of_nonneg ht₂]
      _ ≤ t₁ * C + t₂ * C := add_le_add (mul_le_mul_of_nonneg_left (ha n) ht₁) (mul_le_mul_of_nonneg_left (hb n) ht₂)
      _ = C := by rw [← add_mul, hsum, one_mul]

lemma opBall_conj_inv (C : ℝ)
    (q : ((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸
      Subgroup.normalClosure {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
        Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)})
    {ξ : L2M d hd} (hξ : ξ ∈ opBall d hd C) :
    conjQuot d hd q ξ ∈ opBall d hd C := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨a, rfl, ha⟩ := hξ
  refine ⟨conjBSeq u a, ?_, fun n => ?_⟩
  · rw [conjQuot_mk]; exact (conjL2_coe u a).symm
  · have h := _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.opnorm_conj_le
      (Unitary.star_mem (u n).2) (a.val n)
    rw [star_star] at h
    exact h.trans (ha n)

/-- Closedness of the operator-norm ball `opBall d hd C` in `L2M d hd` via ultrafilter diagonalization. -/
lemma isClosed_opBall (C : ℝ) : IsClosed (opBall d hd C) := by
  rw [← closure_subset_iff_isClosed]
  intro ξ hξ
  have hex : ∀ k : ℕ, ∃ a : BSeqH d hd,
      (∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (a.val n)‖ ≤ C) ∧
      ‖toL2 a - ξ‖ < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨η, ⟨a, rfl, ha⟩, hdist⟩ := Metric.mem_closure_iff.mp hξ (1 / ((k : ℝ) + 1)) (by positivity)
    exact ⟨a, ha, by rwa [dist_comm, dist_eq_norm] at hdist⟩
  choose a ha_bdd ha_dist using hex
  have hdiff_lt : ∀ j k : ℕ, j < k →
      ∀ᶠ n in hyperfilter ℕ, qMat ((a j).val n - (a k).val n) < (2 / ((j : ℝ) + 1)) ^ 2 := by
    intro j k hjk
    have hnorm : ‖toL2 (a j - a k)‖ < 2 / ((j : ℝ) + 1) := by
      rw [toL2_sub]
      have htri : ‖toL2 (a j) - toL2 (a k)‖ ≤ ‖toL2 (a j) - ξ‖ + ‖toL2 (a k) - ξ‖ := by
        rw [← sub_sub_sub_cancel_right (toL2 (a j)) (toL2 (a k)) ξ]
        exact norm_sub_le _ _
      have hjkR : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) := by gcongr
      have h2 : (1 : ℝ) / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) = 2 / ((j : ℝ) + 1) := by ring
      linarith [ha_dist j, ha_dist k]
    have hsq : ‖toL2 (a j - a k)‖ ^ 2 < (2 / ((j : ℝ) + 1)) ^ 2 :=
      pow_lt_pow_left₀ hnorm (norm_nonneg _) two_ne_zero
    exact (qMat_tendsto_norm_sq (a j - a k)).eventually (gt_mem_nhds hsq)
  let A : ℕ → Set ℕ := fun k =>
    {n : ℕ | k ≤ n ∧ ∀ j < k, qMat ((a j).val n - (a k).val n) < (2 / ((j : ℝ) + 1)) ^ 2}
  have hA_mem : ∀ k : ℕ, A k ∈ hyperfilter ℕ := fun k => by
    have hge : {n : ℕ | k ≤ n} ∈ hyperfilter ℕ := by
      have hcof : {n : ℕ | k ≤ n} ∈ (Filter.cofinite : Filter ℕ) := by
        rw [Filter.mem_cofinite]
        exact (Set.finite_lt_nat k).subset fun n hn => by simpa using hn
      exact Filter.hyperfilter_le_cofinite hcof
    have hall : {n : ℕ | ∀ j < k, qMat ((a j).val n - (a k).val n) < (2 / ((j : ℝ) + 1)) ^ 2} ∈ hyperfilter ℕ := by
      have heq : {n : ℕ | ∀ j < k, qMat ((a j).val n - (a k).val n) < (2 / ((j : ℝ) + 1)) ^ 2} =
          ⋂ j ∈ Finset.range k, {n : ℕ | qMat ((a j).val n - (a k).val n) < (2 / ((j : ℝ) + 1)) ^ 2} := by
        ext n; simp [Finset.mem_range]
      rw [heq]
      exact (Filter.biInter_finset_mem (Finset.range k)).mpr fun j hj => hdiff_lt j k (Finset.mem_range.mp hj)
    exact Filter.inter_mem hge hall
  let Bset : ℕ → Set ℕ := fun k => ⋂ i ∈ Finset.range (k + 1), A i
  have hB_mem : ∀ k : ℕ, Bset k ∈ hyperfilter ℕ := fun k =>
    (Filter.biInter_finset_mem (Finset.range (k + 1))).mpr fun i _ => hA_mem i
  have hB0 : ∀ n : ℕ, n ∈ Bset 0 := fun n => by simp [Bset, A]
  classical
  let kOf : ℕ → ℕ := fun n =>
    ((Finset.range (n + 1)).filter (fun k => n ∈ Bset k)).max'
      ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.zero_lt_succ n), hB0 n⟩⟩
  have hkOf_mem : ∀ n : ℕ, n ∈ Bset (kOf n) := fun n =>
    (Finset.mem_filter.mp (Finset.max'_mem ((Finset.range (n + 1)).filter fun k => n ∈ Bset k) _)).2
  have hkOf_ge : ∀ n k : ℕ, k ≤ n → n ∈ Bset k → k ≤ kOf n := fun n k hkn hnk =>
    Finset.le_max' _ k (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hkn), hnk⟩)
  let b : BSeqH d hd :=
    { val := fun n => (a (kOf n)).val n
      bdd := ⟨C, fun n => ha_bdd (kOf n) n⟩ }
  refine ⟨b, ?_, fun n => ha_bdd (kOf n) n⟩
  have hdist_b : ∀ j : ℕ, ‖toL2 b - ξ‖ ≤ 3 / ((j : ℝ) + 1) := by
    intro j
    have hjb : ‖toL2 (a j - b)‖ ≤ 2 / ((j : ℝ) + 1) := by
      have hsq : ‖toL2 (a j - b)‖ ^ 2 ≤ (2 / ((j : ℝ) + 1)) ^ 2 := by
        refine le_of_tendsto (qMat_tendsto_norm_sq (a j - b)) ?_
        filter_upwards [hB_mem (j + 1)] with n hn
        have hjn : j + 1 ≤ n := ((Set.mem_iInter₂.mp hn (j + 1) (Finset.mem_range.mpr (Nat.lt_succ_self _)))).1
        have hjk : j + 1 ≤ kOf n := hkOf_ge n (j + 1) hjn hn
        have hAk : n ∈ A (kOf n) := Set.mem_iInter₂.mp (hkOf_mem n) (kOf n) (Finset.mem_range.mpr (Nat.lt_succ_self _))
        exact le_of_lt (hAk.2 j (by omega))
      have hrt := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at hrt
    rw [toL2_sub] at hjb
    have htri : ‖toL2 b - ξ‖ ≤ ‖toL2 (a j) - toL2 b‖ + ‖toL2 (a j) - ξ‖ := by
      have hs : toL2 b - ξ = (toL2 (a j) - ξ) - (toL2 (a j) - toL2 b) := by
        rw [sub_sub_sub_cancel_left]
      rw [hs]; linarith [norm_sub_le (toL2 (a j) - ξ) (toL2 (a j) - toL2 b)]
    have h3 : (2 : ℝ) / ((j : ℝ) + 1) + 1 / ((j : ℝ) + 1) = 3 / ((j : ℝ) + 1) := by ring
    linarith [ha_dist j]
  have hnorm0 : ‖toL2 b - ξ‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hpos; push Not at hpos
    obtain ⟨j, hj⟩ := exists_nat_gt (3 / ‖toL2 b - ξ‖)
    have h1 := hdist_b j
    have h2 : 3 / ((j : ℝ) + 1) < ‖toL2 b - ξ‖ := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hpos] at hj
      nlinarith
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

/-- The `Γ`-invariant orthogonal projection of any vector in a closed convex `Γ`-invariant set
stays in that set (Alaoglu–Birkhoff minimal-norm element). -/
lemma starProjection_mem_closed_convex_invariant {G V : Type} [Group G]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (π : G →* V ≃ₗᵢ[ℂ] V) (K : Set V) (hK_cl : IsClosed K) (hK_conv : Convex ℝ K)
    (hK_inv : ∀ g : G, ∀ ξ ∈ K, π g ξ ∈ K) {y : V} (hy : y ∈ K) :
    (invSubspace π ⊤).starProjection y ∈ K := by
  let orb : Set V := Set.range fun g : G => π g y
  let Sy : Set V := closure (convexHull ℝ orb)
  have hSy_ne : Sy.Nonempty := ⟨y, subset_closure (subset_convexHull ℝ orb ⟨1, rep_one π _⟩)⟩
  have hSy_cl : IsClosed Sy := isClosed_closure
  have hSy_comp : IsComplete Sy := hSy_cl.isComplete
  have hSy_conv : Convex ℝ Sy := (convex_convexHull ℝ orb).closure
  have hSy_sub : Sy ⊆ K := by
    refine hK_cl.closure_subset_iff.mpr (convexHull_min ?_ hK_conv)
    rintro _ ⟨g, rfl⟩
    exact hK_inv g y hy
  have hSy_inv : ∀ g : G, ∀ ξ ∈ Sy, π g ξ ∈ Sy := by
    intro g ξ hξ
    have hpre : Sy ⊆ (fun u => π g u) ⁻¹' Sy := by
      refine (hSy_cl.preimage (π g).continuous).closure_subset_iff.mpr ?_
      refine convexHull_min ?_ (hSy_conv.linear_preimage ((π g).toLinearMap.restrictScalars ℝ))
      rintro _ ⟨h, rfl⟩
      change π g (π h y) ∈ Sy
      rw [← rep_mul]
      exact subset_closure (subset_convexHull ℝ orb ⟨g * h, rfl⟩)
    exact hpre hξ
  let : InnerProductSpace ℝ V := InnerProductSpace.rclikeToReal ℂ V
  obtain ⟨e₀, he₀_Sy, he₀_min⟩ := exists_norm_eq_iInf_of_complete_convex hSy_ne hSy_comp hSy_conv (0 : V)
  have hmin_le : ∀ w ∈ Sy, ‖e₀‖ ≤ ‖w‖ := fun w hw => by
    have h1 : ‖(0 : V) - e₀‖ = ⨅ u : Sy, ‖(0 : V) - u‖ := he₀_min
    have hbdd : BddBelow (Set.range fun u : Sy => ‖(0 : V) - u‖) :=
      ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
    have h2 : ⨅ u : Sy, ‖(0 : V) - u‖ ≤ ‖(0 : V) - w‖ := ciInf_le hbdd ⟨w, hw⟩
    simpa using h1.le.trans h2
  have he₀_inv : e₀ ∈ invSubspace π ⊤ := by
    intro g _
    have hge : π g e₀ ∈ Sy := hSy_inv g e₀ he₀_Sy
    have hmid : (1 / 2 : ℝ) • e₀ + (1 / 2 : ℝ) • (π g e₀) ∈ Sy :=
      hSy_conv he₀_Sy hge (by norm_num) (by norm_num) (by norm_num)
    have hle := hmin_le _ hmid
    have hpar := parallelogram_law_with_norm ℝ e₀ (π g e₀)
    rw [(π g).norm_map] at hpar
    have h2m : ‖e₀ + π g e₀‖ = 2 * ‖(1 / 2 : ℝ) • e₀ + (1 / 2 : ℝ) • π g e₀‖ := by
      rw [← smul_add, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]; ring
    have hsq : ‖e₀ - π g e₀‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg e₀, norm_nonneg ((1 / 2 : ℝ) • e₀ + (1 / 2 : ℝ) • π g e₀)]
    have h0 : ‖e₀ - π g e₀‖ = 0 := by nlinarith [sq_nonneg ‖e₀ - π g e₀‖, norm_nonneg (e₀ - π g e₀)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp h0)).symm
  have he₀_proj : (invSubspace π ⊤).starProjection y = e₀ := by
    refine (invSubspace π ⊤).eq_starProjection_of_mem_orthogonal he₀_inv ?_
    rw [Submodule.mem_orthogonal]
    intro u hu
    let Hu : Set V := {ξ : V | ⟪u, ξ⟫_ℂ = ⟪u, y⟫_ℂ}
    have hHu_cl : IsClosed Hu := isClosed_eq (continuous_const.inner continuous_id) continuous_const
    have hHu_conv : Convex ℝ Hu := by
      intro ξ₁ h₁ ξ₂ h₂ t₁ t₂ _ _ hsum
      change ⟪u, t₁ • ξ₁ + t₂ • ξ₂⟫_ℂ = ⟪u, y⟫_ℂ
      rw [inner_add_right, ← algebraMap_smul ℂ t₁, ← algebraMap_smul ℂ t₂, inner_smul_right, inner_smul_right]
      rw [h₁, h₂, ← add_mul, ← map_add, hsum, map_one, one_mul]
    have hSy_Hu : Sy ⊆ Hu := by
      refine hHu_cl.closure_subset_iff.mpr (convexHull_min ?_ hHu_conv)
      rintro _ ⟨g, rfl⟩
      change ⟪u, π g y⟫_ℂ = ⟪u, y⟫_ℂ
      rw [← (π g⁻¹).inner_map_map u (π g y), rep_inv_mul, hu g⁻¹ trivial]
    have he₀_Hu : ⟪u, e₀⟫_ℂ = ⟪u, y⟫_ℂ := hSy_Hu he₀_Sy
    rw [inner_sub_right, he₀_Hu, sub_self]
  rw [he₀_proj]
  exact hSy_sub he₀_Sy

/-- The `Γ`-invariant projection of a bounded sequence `y` stays inside the same operator-norm ball. -/
lemma exists_bdd_inv_proj {G : Type} [Group G] (Γ : Subgroup G)
    (ρ : G →* (((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸
      Subgroup.normalClosure {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
        Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)}))
    (y : BSeqH d hd) :
    let πΓ : Γ →* (L2M d hd ≃ₗᵢ[ℂ] L2M d hd) := ((conjQuot d hd).comp ρ).comp Γ.subtype
    ∃ e : BSeqH d hd, toL2 e = (invSubspace πΓ ⊤).starProjection (toL2 y) := by
  intro πΓ
  obtain ⟨C, hC⟩ := y.bdd
  have hmem := starProjection_mem_closed_convex_invariant πΓ (opBall d hd C)
    (isClosed_opBall C) (opBall_convex C) (fun g _ hξ => opBall_conj_inv C (ρ g.1) hξ) ⟨y, rfl, hC⟩
  obtain ⟨e, he_eq, _⟩ := hmem
  exact ⟨e, he_eq⟩

/-- Transfer of a Hilbert-space spectral gap for `(Γ, S_Γ)` to tracial matrix ultraproducts. -/
lemma spectralGap_transfer {G : Type} [Group G] {κ : ℝ}
    (d : ℕ → ℕ) (hd : ∀ n, 0 < d n)
    (ρ : G →* (((n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ) ⧸
      Subgroup.normalClosure {v : (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ |
        Tendsto (fun n => hsDist (v n) 1) (hyperfilter ℕ) (𝓝 0)}))
    (gIdx : Fin 3 → Fin 3 → Fin 8 → G)
    (w : Fin 3 → Fin 3 → Fin 8 → (n : ℕ) → Matrix.unitaryGroup (Fin (d n)) ℂ)
    (hw : ∀ i j m, (QuotientGroup.mk (w i j m)) = ρ (gIdx i j m))
    (s : Fin 8 → Prop) [DecidablePred s]
    (y : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ)
    (hBy : ∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (y n)‖ ≤ C)
    (Γ : Subgroup G) (S_Γ : Finset Γ)
    (hgap : HasSpectralGap S_Γ κ)
    (hmem_Γ : ∀ i j m, i ≠ j → s m → gIdx i j m ∈ Γ)
    (hhit : ∀ g ∈ S_Γ, ∃ i j m, i ≠ j ∧ s m ∧ gIdx i j m = g.1) :
    ∃ e : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ,
      (∃ C : ℝ, ∀ n, ‖Matrix.toEuclideanCLM (n := Fin (d n)) (𝕜 := ℂ) (e n)‖ ≤ C) ∧
      (∀ i j m, i ≠ j → s m →
        Tendsto (fun n => qMat ((w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * e n -
            e n * (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))
          (hyperfilter ℕ) (𝓝 0)) ∧
      ∀ ε > 0, ∀ᶠ n in hyperfilter ℕ,
        κ * qMat (y n - e n) ≤
          ε + ∑ i, ∑ j, ∑ m, if i ≠ j ∧ s m then
            qMat ((w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
              y n * (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
          else 0 := by
  classical
  let yB : BSeqH d hd := ⟨y, hBy⟩
  let π : G →* (L2M d hd ≃ₗᵢ[ℂ] L2M d hd) := (conjQuot d hd).comp ρ
  let πΓ : Γ →* (L2M d hd ≃ₗᵢ[ℂ] L2M d hd) := π.comp Γ.subtype
  obtain ⟨eB, heB⟩ := exists_bdd_inv_proj Γ ρ yB
  have hconj_q : ∀ (i j : Fin 3) (m : Fin 8) (aB : BSeqH d hd),
      Tendsto (fun n => qMat ((w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * aB.val n -
          aB.val n * (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ)))
        (hyperfilter ℕ) (𝓝 (‖π (gIdx i j m) (toL2 aB) - toL2 aB‖ ^ 2)) := by
    intro i j m aB
    have hact : π (gIdx i j m) (toL2 aB) = toL2 (conjBSeq (w i j m) aB) := by
      change conjQuot d hd (ρ (gIdx i j m)) (toL2 aB) = _
      rw [← hw i j m, conjQuot_mk]
      exact conjL2_coe (w i j m) aB
    rw [hact, ← toL2_sub]
    refine (qMat_tendsto_norm_sq (conjBSeq (w i j m) aB - aB)).congr fun n => ?_
    dsimp only [qMat]
    congr 1
    have heq : ((w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * aB.val n *
        star (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) - aB.val n) *
        (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) =
        (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * aB.val n -
        aB.val n * (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, Unitary.star_mul_self_of_mem (w i j m n).2, Matrix.mul_one]
    rw [← heq, _root_.OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.ss_mul_unitary (w i j m n).2]
    rfl
  refine ⟨eB.val, eB.bdd, ?_, ?_⟩
  · intro i j m hij hsm
    have hfix : π (gIdx i j m) (toL2 eB) = toL2 eB := by
      rw [heB]
      exact (Submodule.coe_mem ((invSubspace πΓ ⊤).orthogonalProjectionOnto (toL2 yB))) ⟨gIdx i j m, hmem_Γ i j m hij hsm⟩ trivial
    simpa [hfix] using hconj_q i j m eB
  · intro ε hε
    set v : L2M d hd := toL2 yB - toL2 eB
    have hv_orth : v ∈ (invSubspace πΓ ⊤)ᗮ := by
      dsimp only [v]; rw [heB]; exact (invSubspace πΓ ⊤).sub_starProjection_mem_orthogonal _
    have hgap_v := hgap.2 (L2M d hd) πΓ v hv_orth
    have hdisp_eq : ∀ g ∈ S_Γ, ‖πΓ g v - v‖ ^ 2 = ‖π g.1 (toL2 yB) - toL2 yB‖ ^ 2 := by
      intro g _
      have hfix : πΓ g (toL2 eB) = toL2 eB := by
        rw [heB]
        exact (Submodule.coe_mem ((invSubspace πΓ ⊤).orthogonalProjectionOnto (toL2 yB))) g trivial
      have hs : πΓ g v - v = π g.1 (toL2 yB) - toL2 yB := by
        dsimp only [v]; rw [map_sub, hfix]
        exact sub_sub_sub_cancel_right (π g.1 (toL2 yB)) (toL2 yB) (toL2 eB)
      rw [hs]
    have hsum_le : ∑ g ∈ S_Γ, ‖πΓ g v - v‖ ^ 2 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 8,
          if i ≠ j ∧ s m then ‖π (gIdx i j m) (toL2 yB) - toL2 yB‖ ^ 2 else 0 := by
      have hex : ∀ g : S_Γ, ∃ t : Fin 3 × Fin 3 × Fin 8, t.1 ≠ t.2.1 ∧ s t.2.2 ∧ gIdx t.1 t.2.1 t.2.2 = g.1.1 :=
        fun g => by obtain ⟨i, j, m, h1, h2, h3⟩ := hhit g.1 g.2; exact ⟨(i, j, m), h1, h2, h3⟩
      choose pick hpick using hex
      have hinj : Function.Injective pick := fun g₁ g₂ h => by
        apply Subtype.ext; apply Subtype.ext
        rw [← (hpick g₁).2.2, ← (hpick g₂).2.2, h]
      have h1 : ∑ g ∈ S_Γ, ‖πΓ g v - v‖ ^ 2 =
          ∑ g : S_Γ, ‖π (gIdx (pick g).1 (pick g).2.1 (pick g).2.2) (toL2 yB) - toL2 yB‖ ^ 2 := by
        rw [← Finset.sum_attach S_Γ]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [hdisp_eq g.1 g.2, (hpick g).2.2]
      rw [h1]
      have h2 : ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 8,
          (if i ≠ j ∧ s m then ‖π (gIdx i j m) (toL2 yB) - toL2 yB‖ ^ 2 else 0) =
          ∑ t : Fin 3 × Fin 3 × Fin 8,
            if t.1 ≠ t.2.1 ∧ s t.2.2 then ‖π (gIdx t.1 t.2.1 t.2.2) (toL2 yB) - toL2 yB‖ ^ 2 else 0 := by
        simp [Fintype.sum_prod_type]
      rw [h2]
      calc ∑ g : S_Γ, ‖π (gIdx (pick g).1 (pick g).2.1 (pick g).2.2) (toL2 yB) - toL2 yB‖ ^ 2
          = ∑ t ∈ Finset.univ.image pick,
              if t.1 ≠ t.2.1 ∧ s t.2.2 then ‖π (gIdx t.1 t.2.1 t.2.2) (toL2 yB) - toL2 yB‖ ^ 2 else 0 := by
            rw [Finset.sum_image (fun a _ b _ h => hinj h)]
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [if_pos ⟨(hpick g).1, (hpick g).2.1⟩]
        _ ≤ ∑ t : Fin 3 × Fin 3 × Fin 8,
              if t.1 ≠ t.2.1 ∧ s t.2.2 then ‖π (gIdx t.1 t.2.1 t.2.2) (toL2 yB) - toL2 yB‖ ^ 2 else 0 :=
            Finset.sum_le_univ_sum_of_nonneg fun t => by split_ifs <;> positivity
    have hineq : κ * ‖v‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 8,
        if i ≠ j ∧ s m then ‖π (gIdx i j m) (toL2 yB) - toL2 yB‖ ^ 2 else 0 :=
      hgap_v.trans hsum_le
    have hlhs_lim : Tendsto (fun n => κ * qMat (y n - eB.val n)) (hyperfilter ℕ) (𝓝 (κ * ‖v‖ ^ 2)) := by
      have hv_eq : ‖v‖ ^ 2 = ‖toL2 (yB - eB)‖ ^ 2 := by rw [toL2_sub]
      rw [hv_eq]
      exact (qMat_tendsto_norm_sq (yB - eB)).const_mul κ
    have hrhs_lim : Tendsto (fun n => ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 8,
          if i ≠ j ∧ s m then
            qMat ((w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ) * y n -
              y n * (w i j m n : Matrix (Fin (d n)) (Fin (d n)) ℂ))
          else 0)
        (hyperfilter ℕ)
        (𝓝 (∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 8,
          if i ≠ j ∧ s m then ‖π (gIdx i j m) (toL2 yB) - toL2 yB‖ ^ 2 else 0)) := by
      refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => tendsto_finsetSum _ fun m _ => ?_
      by_cases hcond : i ≠ j ∧ s m
      · simp only [if_pos hcond]; exact hconj_q i j m yB
      · simp only [if_neg hcond]; exact tendsto_const_nhds
    have hdiff_lim := hlhs_lim.sub hrhs_lim
    have hlt : κ * ‖v‖ ^ 2 - (∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 8,
        if i ≠ j ∧ s m then ‖π (gIdx i j m) (toL2 yB) - toL2 yB‖ ^ 2 else 0) < ε := by
      linarith
    filter_upwards [hdiff_lim.eventually (gt_mem_nhds hlt)] with n hn
    linarith

end BSeqH

end UltraproductTransfer

end

end OMA.Green100H2

open OMA.Green100H2 OMA.Green100H2.BSeqH Filter in
open scoped OMA.Green100H2.BSeqH Topology in
/-- Final proof of `OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.H2`. -/
theorem OMA.solution : OMA.R_Green100_green_100_parts_ii_R1_H2_R1_H2_R1_H2_R1.H2 := by
  intro G _ x c hdiag hx5 hcomm hstein htriple _ hnorm_gen
  let : DecidableEq G := Classical.decEq G
  obtain ⟨κ, hκ_pos, hgap_H, hgap_Q⟩ :=
    full_group_spectralGap x c hdiag hx5 hcomm hstein htriple hnorm_gen
  refine ⟨κ, hκ_pos, fun d hd ρ w hw s _ hs y hBy => ?_⟩
  let gIdx : Fin 3 → Fin 3 → Fin 8 → G := fun i j m =>
    if hm : m.val < 7 then x i j ⟨m.val, hm⟩ else c i j
  rcases hs with hs | hs
  · refine spectralGap_transfer d hd ρ gIdx w hw s y hBy _ _ hgap_H ?_ ?_
    · intro i j m hij hm
      rw [hs] at hm
      have hm7 : m.val < 7 := by omega
      change (if hm' : m.val < 7 then x i j ⟨m.val, hm'⟩ else c i j) ∈ _
      rw [dif_pos hm7]
      exact Subgroup.subset_closure (Finset.mem_image.mpr
        ⟨(i, j, ⟨m.val, hm⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)
    · intro g hg
      obtain ⟨⟨a, ha⟩, _, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨⟨i, j, m⟩, hflt, rfl⟩ := Finset.mem_image.mp ha
      have hij : i ≠ j := (Finset.mem_filter.mp hflt).2
      refine ⟨i, j, ⟨m.val, by omega⟩, hij, ?_, ?_⟩
      · rw [hs]; exact m.isLt
      · change (if hm' : m.val < 7 then x i j ⟨m.val, hm'⟩ else c i j) = _
        rw [dif_pos (by omega)]
  · refine spectralGap_transfer d hd ρ gIdx w hw s y hBy _ _ hgap_Q ?_ ?_
    · intro i j m hij hm
      rw [hs] at hm
      rcases hm with hm4 | hm7
      · change (if hm' : m.val < 7 then x i j ⟨m.val, hm'⟩ else c i j) ∈ _
        rw [dif_pos (by omega)]
        exact Subgroup.subset_closure (Finset.mem_union_left _ (Finset.mem_image.mpr
          ⟨(i, j, ⟨m.val, hm4⟩), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))
      · change (if hm' : m.val < 7 then x i j ⟨m.val, hm'⟩ else c i j) ∈ _
        rw [dif_neg (by rw [hm7]; decide)]
        exact Subgroup.subset_closure (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩))
    · intro g hg
      obtain ⟨⟨a, ha⟩, _, rfl⟩ := Finset.mem_image.mp hg
      rcases Finset.mem_union.mp ha with haH | haC
      · obtain ⟨⟨i, j, m⟩, hflt, rfl⟩ := Finset.mem_image.mp haH
        have hij : i ≠ j := (Finset.mem_filter.mp hflt).2
        refine ⟨i, j, ⟨m.val, by omega⟩, hij, ?_, ?_⟩
        · rw [hs]; exact Or.inl m.isLt
        · change (if hm' : m.val < 7 then x i j ⟨m.val, hm'⟩ else c i j) = _
          rw [dif_pos (by omega)]
      · obtain ⟨⟨i, j⟩, hflt, rfl⟩ := Finset.mem_image.mp haC
        have hij : i ≠ j := (Finset.mem_filter.mp hflt).2
        refine ⟨i, j, 7, hij, ?_, ?_⟩
        · rw [hs]; exact Or.inr rfl
        · change (if hm' : (7 : Fin 8).val < 7 then x i j ⟨(7 : Fin 8).val, hm'⟩ else c i j) = _
          rw [dif_neg (by decide)]
