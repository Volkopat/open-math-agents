import OMAStatements.S_mo_316709
import Mathlib

/-!
# Reduction of MathOverflow 316709 (Sun's disjoint-coset conjecture)

Sun's conjecture: if `k > 1` left cosets `a₁G₁, …, a_kG_k` of finite-index subgroups are pairwise
disjoint, then `gcd([G : Gᵢ], [G : Gⱼ]) ≥ k` for some `i < j`.

* `H1` (the classical case `k = 2`, every group in `Type`): two disjoint left cosets of
  finite-index subgroups `H`, `K` have non-coprime indices. If the indices are coprime then
  `[G : H ∩ K] = [G : H][G : K]`, so `[H : H ∩ K] = [G : K]`, the embedding
  `H ⧸ (H ∩ K) ↪ G ⧸ K` is a bijection, `G = HK`, and any two cosets `aH`, `bK` meet.
* `H2` (the open core): the conjecture for `k ≥ 3` and finite groups in `Type`.

`main` reduces an arbitrary group (in any universe) to a finite group in `Type`: the normal core
`N` of `⋂ Gᵢ` has finite index, every `Gᵢ` contains `N`, and the cosets, their disjointness and
the indices pass to `G ⧸ N` (moved to `Type` with `Shrink`).

This is a classical partial case, not progress on the open conjecture.
-/

namespace OMA.R_mo_316709_R1

open scoped Pointwise

universe u

/-- The case `k = 2`: two disjoint left cosets of finite-index subgroups have indices with
greatest common divisor at least `2`. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] (H : Fin 2 → Subgroup G) (a : Fin 2 → G),
    (∀ i, (H i).index ≠ 0) →
    Pairwise (fun i j => Disjoint (a i • (H i : Set G)) (a j • (H j : Set G))) →
    ∃ i j : Fin 2, i < j ∧ 2 ≤ Nat.gcd (H i).index (H j).index

/-- The open core: Sun's conjecture for `k ≥ 3` cosets in a finite group. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (k : ℕ), 2 < k →
    ∀ (H : Fin k → Subgroup G) (a : Fin k → G),
    Pairwise (fun i j => Disjoint (a i • (H i : Set G)) (a j • (H j : Set G))) →
    ∃ i j : Fin k, i < j ∧ k ≤ Nat.gcd (H i).index (H j).index

/-- Move a family of finite-index cosets to a finite group in `Type`, keeping the indices and
the pairwise disjointness. -/
theorem transport {G : Type u} [Group G] {k : ℕ} (H : Fin k → Subgroup G) (a : Fin k → G)
    (hfin : ∀ i, (H i).index ≠ 0)
    (hdisj : Pairwise (fun i j => Disjoint (a i • (H i : Set G)) (a j • (H j : Set G)))) :
    ∃ (G₀ : Type) (_ : Group G₀) (_ : Finite G₀) (H₀ : Fin k → Subgroup G₀) (a₀ : Fin k → G₀),
      (∀ i, (H₀ i).index = (H i).index) ∧
      Pairwise (fun i j => Disjoint (a₀ i • (H₀ i : Set G₀)) (a₀ j • (H₀ j : Set G₀))) := by
  have hI : (⨅ i, H i).FiniteIndex := Subgroup.finiteIndex_iInf (fun i => ⟨hfin i⟩)
  set N : Subgroup G := (⨅ i, H i).normalCore with hN
  have hNle : ∀ i, N ≤ H i := fun i => (Subgroup.normalCore_le _).trans (iInf_le _ i)
  have hNfin : N.FiniteIndex := Subgroup.finiteIndex_normalCore _
  have hQ : Finite (G ⧸ N) := Subgroup.finite_quotient_of_finiteIndex
  let ψ : G →* Shrink.{0} (G ⧸ N) :=
    (Shrink.mulEquiv.{0} (α := G ⧸ N)).symm.toMonoidHom.comp (QuotientGroup.mk' N)
  have hsurj : Function.Surjective ψ :=
    (Shrink.mulEquiv.{0} (α := G ⧸ N)).symm.surjective.comp (QuotientGroup.mk'_surjective N)
  have hker : ∀ x, ψ x = 1 → x ∈ N := by
    intro x hx
    have h1 : (QuotientGroup.mk' N) x = 1 := by
      have := congrArg (Shrink.mulEquiv.{0} (α := G ⧸ N)) hx
      simpa [ψ] using this
    exact (QuotientGroup.eq_one_iff x).mp h1
  have key : ∀ i (g : G), g ∈ a i • (H i : Set G) ↔
      ψ g ∈ ψ (a i) • ((H i).map ψ : Set (Shrink.{0} (G ⧸ N))) := by
    intro i g
    rw [mem_leftCoset_iff, mem_leftCoset_iff]
    constructor
    · intro hg
      refine ⟨(a i)⁻¹ * g, hg, ?_⟩
      simp [map_mul, map_inv]
    · rintro ⟨h, hh, heq⟩
      have hm : h⁻¹ * ((a i)⁻¹ * g) ∈ N := by
        apply hker
        rw [map_mul, map_inv, map_mul, map_inv, heq]
        simp [map_mul, map_inv]
      have := (H i).mul_mem hh (hNle i hm)
      simpa using this
  refine ⟨Shrink.{0} (G ⧸ N), inferInstance, Finite.of_equiv _ (equivShrink.{0} (G ⧸ N)),
    fun i => (H i).map ψ, fun i => ψ (a i), ?_, ?_⟩
  · intro i
    exact Subgroup.index_map_eq (H i) hsurj (fun x hx => hNle i (hker x hx))
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    obtain ⟨g, rfl⟩ := hsurj x
    exact Set.disjoint_left.mp (hdisj hij) ((key i g).mpr hxi) ((key j g).mpr hxj)

theorem main : H1 → H2 → type_of% @OMA.S_mo_316709.main := by
  intro h1 h2 G _ k hk H a hfin hdisj
  obtain ⟨G₀, _, _, H₀, a₀, hidx, hdisj₀⟩ := transport H a hfin hdisj
  by_cases hk2 : k = 2
  · subst hk2
    obtain ⟨i, j, hij, hg⟩ := h1 G₀ H₀ a₀ (fun i => by rw [hidx]; exact hfin i) hdisj₀
    exact ⟨i, j, hij, by rwa [hidx, hidx] at hg⟩
  · obtain ⟨i, j, hij, hg⟩ := h2 G₀ k (by omega) H₀ a₀ hdisj₀
    exact ⟨i, j, hij, by rwa [hidx, hidx] at hg⟩

end OMA.R_mo_316709_R1
