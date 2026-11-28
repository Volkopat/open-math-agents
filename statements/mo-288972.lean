import Mathlib

/-!
# Reconstructing a real orthogonal matrix from its entrywise squares

Source: Jiro, https://mathoverflow.net/questions/288972 (CC BY-SA).
Credit: @connoranderson.

The question asks for an efficient exact search without specifying an input
encoding or a model for real arithmetic. We give a bound on the number of row
sign assignments explored. Independent coordinate functionals on the space of
available rows determine a linear system with a unique solution. One nonzero
coordinate fixes the sign of the row. Column signs make the first row positive
or zero. For matrix size n+1 the resulting search has at most 2^(n choose 2)
leaves. This is an upper bound, with no assertion of computational optimality.
-/

namespace OMA.S_mo_288972
open Matrix Module Finset
open scoped Classical

abbrev Row (n : ℕ) := Fin n → ℝ
abbrev Space (n : ℕ) := Submodule ℝ (Row n)

structure Chart {n : ℕ} (V : Space n) where
  index : Fin (finrank ℝ V) ↪ Fin n
  solve : (Fin (finrank ℝ V) → ℝ) ≃ₗ[ℝ] V
  reads : ∀ x j, (solve x).val (index j)=x j

def unitRow {n : ℕ} (a v : Row n) : Prop := v ⬝ᵥ v=1 ∧ ∀ j, v j^2=a j
noncomputable def nextSpace {n : ℕ} (V : Space n) (v : Row n) : Space n :=
  V ⊓ LinearMap.ker (dotProductBilin ℝ ℝ v)

noncomputable def decode {n : ℕ} {V : Space n} (T : Chart V) (a : Row n)
    (j : Fin (finrank ℝ V)) (b : {i : Fin (finrank ℝ V) // i ≠ j} → Bool) : V :=
  T.solve (fun i => if e : i=j then Real.sqrt (a (T.index i))
    else if b ⟨i,e⟩ then Real.sqrt (a (T.index i)) else -Real.sqrt (a (T.index i)))

noncomputable def candidates {n : ℕ} {V : Space n} (T : Chart V) (a : Row n) :
    Finset (Row n) := by
  classical
  exact if h : ∃ j, 0 < a (T.index j) then
    (univ.image (fun b => (decode T a h.choose b).val)).filter (unitRow a) else ∅

noncomputable def search {n : ℕ} (T : ∀ V : Space n, Chart V) :
    (m : ℕ) → Space n → (Fin m → Row n) → Finset (Fin m → Row n)
  | 0, _, _ => {fun i => i.elim0}
  | m+1, V, A => (candidates (T V) (A 0)).biUnion fun v =>
      (search T m (nextSpace V v) (fun i => A i.succ)).image (Fin.cons v)

/-- Counts terminal outcomes in the search. Sign assignments that fail the row test
or duplicate an accepted row terminate at this level. When no orientation is
possible, the dead node counts once. -/
noncomputable def leaves {n : ℕ} (T : ∀ V : Space n, Chart V) :
    (m : ℕ) → Space n → (Fin m → Row n) → ℕ
  | 0, _, _ => 1
  | m+1, V, A =>
    let B := candidates (T V) (A 0)
    let slots := if ∃ j, 0 < A 0 ((T V).index j) then 2^(finrank ℝ V-1) else 1
    slots - B.card + ∑ v ∈ B, leaves T m (nextSpace V v) (fun i => A i.succ)

noncomputable def reconstruct {n : ℕ} (T : ∀ V : Space (n+1), Chart V)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : Finset (Fin (n+1) → Row (n+1)) := by
  classical
  let v : Row (n+1) := fun j => Real.sqrt (A 0 j)
  exact if unitRow (A 0) v then
    (search T n (nextSpace ⊤ v) (fun i => A i.succ)).image (Fin.cons v) else ∅

noncomputable def reconstructionLeaves {n : ℕ} (T : ∀ V : Space (n+1), Chart V)
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℕ := by
  classical
  let v : Row (n+1) := fun j => Real.sqrt (A 0 j)
  exact if unitRow (A 0) v then leaves T n (nextSpace ⊤ v) (fun i => A i.succ) else 1

def Witness {n : ℕ} (A O : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  O*O.transpose=1 ∧ ∀ i j, (O i j)^2=A i j

theorem main : ∀ n : ℕ, ∃ T : ∀ V : Space (n+1), Chart V,
    (∀ (V : Space (n+1)) (a : Row (n+1)),
      (candidates (T V) a).card ≤ 2^(finrank ℝ V-1)) ∧
    (∀ (m : ℕ) (V : Space (n+1)) (A : Fin m → Row (n+1)),
      leaves T m V A ≤ 2^((finrank ℝ V).choose 2)) ∧
    ∀ A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ,
      reconstructionLeaves T A ≤ 2^(n.choose 2) ∧
      (reconstruct T A).card ≤ 2^(n.choose 2) ∧
      (∀ O ∈ reconstruct T A, Witness A O) ∧
      ((reconstruct T A).Nonempty ↔ ∃ O, Witness A O) := by
  sorry

end OMA.S_mo_288972
