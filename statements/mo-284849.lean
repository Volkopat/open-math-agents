import Mathlib

/-!
# Entry permutations respecting inversion at a given matrix

Source: jcdornano, https://mathoverflow.net/questions/284849 (CC BY-SA 3.0).
Contribution by @connoranderson.

Independent row and column permutations have the form `rowsCols`. An arbitrary
permutation of the matrix entries has the form `entries`. The last clause
gives a counterexample among adjacency matrices of simple undirected graphs.
-/
namespace OMA.S_mo_284849
open Matrix
abbrev Mat (K : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) K

def entries {K : Type*} {n : ℕ} (e : Equiv.Perm (Fin n × Fin n)) (A : Mat K n) : Mat K n :=
  Matrix.of (fun i j => A (e (i,j)).1 (e (i,j)).2)
def rowsCols {K : Type*} {n : ℕ} (A B : Mat K n) : Prop :=
  ∃ s t : Equiv.Perm (Fin n), ∀ i j, B i j = A (s i) (t j)
noncomputable def paired {K : Type*} [Field K] {n : ℕ} (A : Mat K n) (p : Fin n × Fin n) : K × K :=
  (A p.1 p.2,A⁻¹ p.1 p.2)

theorem main :
    (∀ (K : Type) [Field K] (n : ℕ) (A B : Mat K n),
      (∃ e : Equiv.Perm (Fin n × Fin n), entries e A=B ∧ entries e A⁻¹=B⁻¹) ↔
        ∀ v : K × K, Nat.card {p // paired A p=v} = Nat.card {p // paired B p=v}) ∧
    (∀ (K : Type) [Field K], ∃ (A : Mat K 3) (e : Equiv.Perm (Fin 3 × Fin 3)),
      IsUnit A.det ∧ IsUnit (entries e A).det ∧ entries e A⁻¹=(entries e A)⁻¹ ∧
      ¬rowsCols A (entries e A)) ∧
    (∃ (A B : Mat (ZMod 2) 12) (e : Equiv.Perm (Fin 12 × Fin 12)),
      A.IsSymm ∧ B.IsSymm ∧ (∀ i,A i i=0 ∧ B i i=0) ∧ A*A=1 ∧ B*B=1 ∧
      entries e A=B ∧ entries e A⁻¹=B⁻¹ ∧ ¬rowsCols A B) := by sorry
end OMA.S_mo_284849
