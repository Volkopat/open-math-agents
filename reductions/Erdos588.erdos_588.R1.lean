import FormalConjectures.ErdosProblems.«588»
import Mathlib.Combinatorics.SimpleGraph.Triangle.Tripartite

/-!
# Bounded triangle ratios on rich lines, for every fixed line cap

This generalizes the four-point reduction of @ubuwaits, Left to Solve
Erdos101.erdos_101.R2. The number of points permitted on a line and the
number of allowed triangle-ratio values are distinct parameters.
-/

namespace OMA.R_Erdos588_erdos_588_R1

open EuclideanGeometry SimpleGraph.TripartiteFromTriangles Filter Asymptotics
open scoped Classical

/-- Extract many ordered triples from distinct k-rich lines with boundedly
many ratio values throughout their tripartite graph of pairs. -/
def H1 : Prop :=
  ∀ k : ℕ, 4 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ m : ℕ, ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
    ∀ S : Finset ℝ², N ≤ S.card → NonCollinearFor (k+1) (S : Set ℝ²) →
      δ * (S.card : ℝ)^2 ≤ (linesWithPointsFor k (S : Set ℝ²)).ncard →
    ∃ T : Finset (S × S × S), ExplicitDisjoint T ∧ η * (S.card : ℝ)^2 ≤ T.card ∧
      (T : Set (S × S × S)).InjOn (fun p => line[ℝ,(p.1 : ℝ²),(p.2.1 : ℝ²)]) ∧
      (∀ p ∈ T, p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧
        line[ℝ,(p.1 : ℝ²),(p.2.1 : ℝ²)] ∈ linesWithPointsFor k (S : Set ℝ²)) ∧
      ∃ (a b d : S → S → ℝˣ) (K : Finset ℝˣ), (∀ p ∈ T, (a p.1 p.2.2 : ℝ) + (b p.2.1 p.2.2 : ℝ) = 1 ∧
    (a p.1 p.2.2 : ℝ) • (p.1 : ℝ²) + (b p.2.1 p.2.2 : ℝ) • (p.2.1 : ℝ²) = (p.2.2 : ℝ²) ∧
    d p.1 p.2.1 = b p.2.1 p.2.2 / a p.1 p.2.2) ∧
        K.card ≤ m ∧ (∀ x y z, (∃ w, (x,y,w) ∈ T) → (∃ w, (x,w,z) ∈ T) → (∃ w, (w,y,z) ∈ T) →
    a x z * d x y / b y z ∈ K)

/-- A dense linear family of compatible triples cannot have boundedly many
triangle ratios in a configuration with fixed line cap. This assertion
applies to arbitrary records with the stated compatibility. -/
def H2 : Prop :=
  ∀ k m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ S : Finset ℝ²,
    N ≤ S.card → NonCollinearFor (k+1) (S : Set ℝ²) →
    ∀ T : Finset (S × S × S), ExplicitDisjoint T →
    ∀ (a b d : S → S → ℝˣ) (K : Finset ℝˣ), (∀ p ∈ T, (a p.1 p.2.2 : ℝ) + (b p.2.1 p.2.2 : ℝ) = 1 ∧
    (a p.1 p.2.2 : ℝ) • (p.1 : ℝ²) + (b p.2.1 p.2.2 : ℝ) • (p.2.1 : ℝ²) = (p.2.2 : ℝ²) ∧
    d p.1 p.2.1 = b p.2.1 p.2.2 / a p.1 p.2.2) →
      K.card ≤ m → (∀ x y z, (∃ w, (x,y,w) ∈ T) → (∃ w, (x,w,z) ∈ T) → (∃ w, (w,y,z) ∈ T) →
    a x z * d x y / b y z ∈ K) → (T.card : ℝ) < ε * (S.card : ℝ)^2

theorem main : H1 → H2 → type_of% @Erdos588.erdos_588 := by
  intro extract sparse k hk
  apply IsLittleO.of_bound
  intro δ hδ
  obtain ⟨m,η,hη,N,hN⟩ := extract k hk δ hδ
  obtain ⟨M,hM⟩ := sparse k m η hη
  filter_upwards [eventually_ge_atTop (max N M)] with n hn
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
  suffices Erdos588.numLinesWithPointsMax k n ≤ ⌊δ*(n : ℝ)^2⌋₊ from
    (Nat.cast_le.mpr this).trans (Nat.floor_le (mul_nonneg hδ.le (sq_nonneg _)))
  apply csSup_le'
  rintro _ ⟨U, hcard, hfin, hcap, rfl⟩
  let S := hfin.toFinset
  have hU : (S : Set ℝ²) = U := hfin.coe_toFinset
  have hs : S.card = n := (Set.ncard_eq_toFinset_card U hfin).symm.trans hcard
  apply Nat.le_floor
  by_contra! hdense
  obtain ⟨T,ht,hsize,_,_,a,b,d,K,hr,hm,hK⟩ :=
    hN S (hs ▸ (le_max_left ..).trans hn) (hU ▸ hcap) (by simpa only [hU,hs] using hdense.le)
  exact (not_lt_of_ge hsize) (hM S (hs ▸ (le_max_right ..).trans hn)
    (hU ▸ hcap) T ht a b d K hr hm hK)

end OMA.R_Erdos588_erdos_588_R1
