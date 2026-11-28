import FormalConjectures.GreensOpenProblems.«82»
import Mathlib

/-! Bedert, arXiv:2407.16075v2, Theorem 1.3, applies to finite integer
coefficient alphabets. In the signed-frequency formulation, positive and
negative frequencies coalesce with multiplicity at most two. The value at
zero is exactly the cardinality of the original set. H2 is the normalized
specialization of Bedert's quantitative estimate to this alphabet. -/
namespace OMA.R_Green82_green_82_lower_bound_R1
open Filter Real Set Finset Asymptotics
open scoped Topology

/-- Convert the explicit quantitative bound into the near-unit exponent. -/
def H1 : Prop := ∀ c : ℝ, 0<c → ∃ o : ℕ → ℝ, o =o[atTop] (fun _ ↦ (1:ℝ)) ∧
  ∀ᶠ n : ℕ in atTop, (log (log n))^(1-|o n|) ≤ c*log (log n)/log (log (log n))

/-- Bounded-coefficient trigonometric estimate in one full normalized period. -/
def H2 : Prop := ∃ c : ℝ, 0<c ∧ ∀ᶠ n : ℕ in atTop, ∀ (S : Finset ℕ) (b : ℕ → ℕ),
  (∀ k ∈ S, b k≤2) → (∑ k ∈ S,b k)=n →
  ⌊c*log (log n)/log (log (log n))⌋₊ ≤
    ({θ : ℝ | θ ∈ Set.Ico 0 1 ∧ ∑ k ∈ S,(b k:ℝ)*cos (2*π*k*θ)=0} : Set ℝ).ncard

theorem main : H1 → H2 → type_of% @Green82.green_82_lower_bound := by
  classical
  intro h1 h2
  obtain ⟨c,hc,hB⟩ := h2
  obtain ⟨o,ho,hO⟩ := h1 c hc
  refine ⟨o,ho,?_⟩
  filter_upwards [hO,hB] with n hn hbed
  intro A hA
  let S := A.image Int.natAbs
  let b (k : ℕ) := (A.filter (fun i => i.natAbs=k)).card
  have small (k : ℕ) : b k ≤ 2 := by
    have sub : (A.filter (fun i => i.natAbs=k)) ⊆ {(k:ℤ),-(k:ℤ)} := by
      intro i hi
      have e := (mem_filter.mp hi).2
      have either : i=(k:ℤ) ∨ i= -(k:ℤ) := by omega
      simpa using either
    exact (Finset.card_le_card sub).trans (card_le_two)
  have covered : ∀ a ∈ A, Int.natAbs a ∈ S := fun _ h => mem_image_of_mem _ h
  have sumB : (∑ k ∈ S,b k)=n := (card_eq_sum_card_fiberwise covered).symm.trans hA
  have same (θ : ℝ) : ∑ a ∈ A,cos (2*π*a*θ) = ∑ k ∈ S,(b k:ℝ)*cos (2*π*k*θ) := by
    symm
    calc
      _ = ∑ k ∈ S,∑ a ∈ A.filter (fun i => i.natAbs=k),cos (2*π*a*θ) := by
        apply sum_congr rfl
        intro k _
        rw [show (b k:ℝ)*cos (2*π*k*θ) = ∑ _ ∈ A.filter (fun i => i.natAbs=k),cos (2*π*k*θ) by simp [b]]
        apply sum_congr rfl
        intro a ha
        have e := (mem_filter.mp ha).2
        rcases (show a=(k:ℤ) ∨ a= -(k:ℤ) by omega) with rfl|ha
        · simp
        · rw [ha]
          push_cast
          simp
      _ = _ := sum_fiberwise_of_maps_to covered _
  have d := (Nat.floor_mono hn).trans (hbed S b (fun k _ => small k) sumB)
  simp_rw [same]
  exact_mod_cast d

end OMA.R_Green82_green_82_lower_bound_R1
