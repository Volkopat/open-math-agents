import Mathlib

/-!
# Erdős Problem 531

Source: https://www.erdosproblems.com/531
Credit: @Medrov

Erdős asks for estimates of the two-colour Folkman number. The proposed
bounds in this formulation are parameters because the source leaves their
growth rates open. The definition of the coloured interval follows Erdős and
Spencer, *Monochromatic Sumsets* (1989), https://doi.org/10.1016/0097-3165(89)90011-3.
-/

namespace OMA.S_erdos_531

/-- The sums of all nonempty subsets of `A`, using each element at most once. -/
def subsetSums (A : Finset ℕ) : Finset ℕ :=
  (A.powerset.erase ∅).image (fun S => S.sum id)

/-- Every red-blue colouring of `{1, …, N}` admits a `k`-element set whose
    nonempty subset sums all belong to a single colour class of that interval. -/
def ForcesMonoSums (k N : ℕ) : Prop :=
  let interval := Finset.Icc 1 N
  ∀ red ∈ interval.powerset, ∃ A ∈ interval.powersetCard k,
    subsetSums A ⊆ red ∨ subsetSums A ⊆ interval \ red

/-- The least endpoint of an interval forcing a monochromatic set of sums. -/
noncomputable def folkmanNumber (k : ℕ) : ℕ :=
  sInf {N : ℕ | ForcesMonoSums k N}

/-- A proposed estimate `lower k < F(k) ≤ upper k` for every `k ≥ k₀`. -/
def BoundsFrom (k₀ : ℕ) (lower upper : ℕ → ℕ) : Prop :=
  ∀ k ≥ k₀, lower k < folkmanNumber k ∧ folkmanNumber k ≤ upper k

/-- The threshold exists for every positive `k`. To certify a proposed
    estimate, give a colouring avoiding the configuration at the lower endpoint
    and show that every colouring forces it at the upper endpoint. -/
theorem main :
    (∀ k : ℕ, 0 < k → IsLeast {N : ℕ | ForcesMonoSums k N} (folkmanNumber k)) ∧
      ∀ (k₀ : ℕ) (lower upper : ℕ → ℕ), 0 < k₀ →
        (BoundsFrom k₀ lower upper ↔
          ∀ k ≥ k₀, ¬ ForcesMonoSums k (lower k) ∧ ForcesMonoSums k (upper k)) := by
  sorry

end OMA.S_erdos_531
