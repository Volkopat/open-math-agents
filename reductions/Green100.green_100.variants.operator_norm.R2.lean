import FormalConjectures.GreensOpenProblems.«100»
import Mathlib

/-! A different obstruction from the ordinary lamp construction: Sauers,
Non-MF groups exist, sections on one-sided compression and Clifford lamps.
The central Clifford sign is a nontrivial involution in a compression defect.
All norm models collapse this defect in normalized Hilbert–Schmidt norm.
Compression to the nontrivial spectral corner of a central involution upgrades
collapse in every such model to collapse in operator norm. -/
open Filter Finset Green100
open scoped Topology
namespace OMA.R_Green100_green_100_variants_operator_norm_R2

/-- The group-theoretic witness: a central involution in the subgroup
generated normally by compressor commutators of a Kazhdan subgroup. -/
def H1 : Prop := ∃ G : Type, ∃ _ : Group G, ∃ _ : Countable G,
  ∃ (L : Subgroup G) (z : G), z ≠ 1 ∧ z*z = 1 ∧ (∀ a : G, Commute z a) ∧
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : L →* E ≃ₗᵢ[ℂ] E) (b : L → E), (∀ g h, b (g*h) = b g + ρ g (b h)) →
    ∃ v : E, ∀ g, b g = ρ g v - v) ∧ z ∈ Subgroup.normalClosure {x : G | ∃ u c l : G, l ∈ L ∧
    (∀ a ∈ L, u*a*u⁻¹ ∈ L) ∧ (∀ a ∈ L, Commute c a) ∧
    x = (u*c*u⁻¹)*l*(u*c*u⁻¹)⁻¹*l⁻¹}

/-- One-sided Kazhdan transport collapses the compression defect in normalized
Hilbert–Schmidt norm. No centrality of the defect element is needed. -/
def H2 : Prop := ∀ (G : Type) [Group G] [Countable G] (L : Subgroup G),
  (∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ρ : L →* E ≃ₗᵢ[ℂ] E) (b : L → E), (∀ g h, b (g*h) = b g + ρ g (b h)) →
    ∃ v : E, ∀ g, b g = ρ g v - v) → ∀ z ∈ Subgroup.normalClosure {x : G | ∃ u c l : G, l ∈ L ∧
    (∀ a ∈ L, u*a*u⁻¹ ∈ L) ∧ (∀ a ∈ L, Commute c a) ∧
    x = (u*c*u⁻¹)*l*(u*c*u⁻¹)⁻¹*l⁻¹},
  ∀ (d : ℕ → ℕ) (φ : ∀ j, G → Matrix.unitaryGroup (Fin (d j)) ℂ),
    (∀ j, φ j 1 = 1) →
    (∀ a b, Tendsto (fun j ↦ opDist (φ j (a*b)) (φ j a*φ j b)) atTop (𝓝 0)) →
    Tendsto (fun j ↦ hsDist (φ j z) 1) atTop (𝓝 0)

/-- An elementary finite normal subgroup case of the normal Kazhdan theorem.
The universal quantifier over models is essential for compression to a corner. -/
def H3 : Prop := ∀ (G : Type) [Group G] [Countable G] (z : G),
  z*z = 1 → (∀ a : G, Commute z a) →
  (∀ (d : ℕ → ℕ) (φ : ∀ j, G → Matrix.unitaryGroup (Fin (d j)) ℂ),
    (∀ j, φ j 1 = 1) →
    (∀ a b, Tendsto (fun j ↦ opDist (φ j (a*b)) (φ j a*φ j b)) atTop (𝓝 0)) →
    Tendsto (fun j ↦ hsDist (φ j z) 1) atTop (𝓝 0)) →
  ∀ (d : ℕ → ℕ) (φ : ∀ j, G → Matrix.unitaryGroup (Fin (d j)) ℂ),
    (∀ j, φ j 1 = 1) →
    (∀ a b, Tendsto (fun j ↦ opDist (φ j (a*b)) (φ j a*φ j b)) atTop (𝓝 0)) →
    Tendsto (fun j ↦ opDist (φ j z) 1) atTop (𝓝 0)

theorem main : H1 → H2 → H3 → type_of% @Green100.green_100.variants.operator_norm := by
  classical
  intro exampleG transport amplify hall
  obtain ⟨G, instG, instCount, L, z, hz, order, central, fixedPt, defect⟩ := exampleG
  obtain ⟨e,he⟩ := exists_surjective_nat G
  let A (j : ℕ) := insert z (insert 1 ((Finset.range j).image e))
  have exhaust (a : G) : ∀ᶠ j in atTop, a ∈ A j := by
    obtain ⟨i,rfl⟩ := he a
    filter_upwards [eventually_gt_atTop i] with j hj
    exact mem_insert_of_mem (mem_insert_of_mem (mem_image.mpr ⟨i,mem_range.mpr hj,rfl⟩))
  choose d φ hone hmul hsep using fun j ↦ hall G (A j) (by simp [A]) (1/((j:ℝ)+1)) (by positivity)
  have approx (a b : G) : Tendsto (fun j ↦ opDist (φ j (a*b)) (φ j a*φ j b)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [exhaust a,exhaust b,exhaust (a*b)] with j ha hb hab
    exact (hmul j a ha b hb hab).le
  have collapse := amplify G z order central (transport G L fixedPt z defect) d φ hone approx
  have contra : (1:ℝ) ≤ 0 := ge_of_tendsto collapse (Eventually.of_forall
    fun j ↦ hsep j z (mem_insert_self _ _) hz)
  linarith

end OMA.R_Green100_green_100_variants_operator_norm_R2
