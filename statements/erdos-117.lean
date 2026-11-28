import Mathlib

/-!
# Erdős Problem 117

Source: https://www.erdosproblems.com/117
Credit: @ciphore (formalization prepared for the open-math-agents statement review)

The source asks: let `h(n)` be minimal such that every group `G` with the property that every
subset of more than `n` elements contains two distinct commuting elements can be covered by at
most `h(n)` abelian subgroups. Estimate `h(n)` as well as possible.

A pending proof claim by Guillaume Lecomte gives the sharp logarithmic asymptotic
`log₂ h(n) = n / 2 + O(√n (log (n + 2))³)`, hence `h(n)^(1/n) → √2`.

Formalization notes:

* The noncommutation hypothesis is represented by `NoncommutingBound G n`: every finite pairwise
  noncommuting subset of `G` has cardinality at most `n`. Over finite subsets this is the exact
  contrapositive form of the source's “every subset of more than `n` elements contains two distinct
  commuting elements”; infinite subsets add no further strength in the finite-clique-number reading.
* An abelian cover is a finite family of abelian subgroups whose union is `G`. Here abelianness of a
  subgroup `A` is `IsMulCommutative A`.
* `h n` is the least universal bound valid for every group satisfying the noncommutation bound. This
  is the meaning of “minimal such that any group ... can be covered” in the source. It is given the
  value `⊤` in `ℕ∞` if no finite universal bound exists, so finiteness is part of the theorem rather
  than a hidden junk value.
* Groups range over `Type u`; the theorem is universe-polymorphic rather than restricted to `Type 0`.
* The main theorem states the sharp logarithmic asymptotic and its consequence for the `n`th root.
  This is an estimate of `h`, as requested by the open-ended source problem.
-/

namespace OMA.S_erdos_117

open Filter Asymptotics
open scoped Topology

universe u

/-- Every finite pairwise noncommuting subset has at most `n` elements. -/
def NoncommutingBound (G : Type*) [Group G] (n : ℕ) : Prop :=
  ∀ s : Finset G, (s : Set G).Pairwise (fun x y => ¬ Commute x y) → s.card ≤ n

/-- An abelian cover indexed by a finite type. -/
def AbelianCover (G : Type*) [Group G] (ι : Type*) (A : ι → Subgroup G) : Prop :=
  (∀ i, IsMulCommutative (A i)) ∧ ∀ x : G, ∃ i, x ∈ A i

/-- Existence of a cover by at most `k` abelian subgroups. -/
def HasAbelianCover (G : Type*) [Group G] (k : ℕ) : Prop :=
  ∃ A : Fin k → Subgroup G, AbelianCover G (Fin k) A

/-- `k` is a universal abelian-cover bound for all groups whose finite pairwise-noncommuting
subsets have at most `n` elements. -/
def UniversalAbelianCoverBound (n k : ℕ) : Prop :=
  ∀ (G : Type u) [Group G], NoncommutingBound G n → HasAbelianCover G k

/-- The least universal cover bound, with value `⊤` if no finite bound exists. -/
noncomputable def h (n : ℕ) : ℕ∞ :=
  ⨅ k : {k : ℕ // UniversalAbelianCoverBound.{u} n k}, (k.1 : ℕ∞)

/-- Erdős Problem 117: `h` is finite and
`log₂ h(n) - n / 2 = O(√n (log (n + 2))³)`; in particular `h(n)^(1/n) → √2`. -/
theorem main :
    (∀ n : ℕ, h.{u} n < ⊤) ∧
    ((fun n : ℕ => Real.log (h.{u} n).toNat / Real.log 2 - (n : ℝ) / 2) =O[atTop]
      (fun n : ℕ => Real.sqrt n * (Real.log ((n : ℝ) + 2)) ^ 3)) ∧
    Tendsto (fun n : ℕ => ((h.{u} n).toNat : ℝ) ^ (1 / (n : ℝ))) atTop
      (𝓝 (Real.sqrt 2)) := by
  sorry

end OMA.S_erdos_117
