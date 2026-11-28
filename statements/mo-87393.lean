import Mathlib

/-!
# Counting triangulated integral homology three-spheres

Source https://mathoverflow.net/questions/87393/are-there-lots-of-integer-homology-three-spheres

Is the number of combinatorial types of integral homology 3-spheres
with N tetrahedra bounded by an exponential in N?
-/

namespace OMA.S_mo_87393

open AlgebraicTopology
open scoped BigOperators

abbrev Faces (v : ℕ) := Set (Finset (Fin v))

/-- The standard barycentric realization of a finite abstract complex. -/
abbrev Realization {v : ℕ} (K : Faces v) :=
  {x : Fin v → ℝ // (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 ∧
    ∃ s ∈ K, ∀ i, i ∉ s → x i = 0}

def vertexLink {v : ℕ} (K : Faces v) (i : Fin v) : Faces v :=
  {s | i ∉ s ∧ insert i s ∈ K}

abbrev Sphere (d : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (d + 1))) 1

def IsClosedThreeManifold {v : ℕ} (K : Faces v) : Prop :=
  ∅ ∈ K ∧
  (∀ s ∈ K, ∀ t ⊆ s, t ∈ K) ∧
  (∀ i : Fin v, {i} ∈ K) ∧
  (∀ s ∈ K, ∃ t ∈ K, s ⊆ t ∧ t.card = 4) ∧
  ∀ i : Fin v, Nonempty (Realization (vertexLink K i) ≃ₜ Sphere 2)

noncomputable def integralHomology (X : Type) [TopologicalSpace X] (k : ℕ) : ModuleCat ℤ :=
  (((singularHomologyFunctor (ModuleCat ℤ) k).obj (ModuleCat.of ℤ ℤ)).obj (TopCat.of X))

def IsIntegralHomologySphere {v : ℕ} (K : Faces v) : Prop :=
  IsClosedThreeManifold K ∧
  ∀ k : ℕ, Nonempty (integralHomology (Realization K) k ≃+ integralHomology (Sphere 3) k)

noncomputable def tetrahedronCount {v : ℕ} (K : Faces v) : ℕ :=
  Nat.card {s : Finset (Fin v) // s ∈ K ∧ s.card = 4}

abbrev ComplexesWithCounts (N v : ℕ) :=
  {K : Faces v // IsIntegralHomologySphere K ∧ tetrahedronCount K = N}

def IsCombinatoriallyIsomorphic {v : ℕ} (K L : Faces v) : Prop :=
  ∃ e : Equiv.Perm (Fin v), ∀ s, s ∈ K ↔ s.map e.toEmbedding ∈ L

noncomputable def count (N : ℕ) : ℕ :=
  ∑ v ∈ Finset.range (4 * N + 1),
    Nat.card (Quot (fun K L : ComplexesWithCounts N v =>
      IsCombinatoriallyIsomorphic K.val L.val))

theorem main :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (count N : ℝ) ≤ C ^ N := by
  sorry

end OMA.S_mo_87393
