import Mathlib

/-!
# Average number of preserved circular neighbors, up to rotation (A326404)

A circular seating is represented by the permutation taking each person
to the next person clockwise. Relabeling the standard circle gives every
seating. A rotation of the seats has the same successor permutation.
Reflection is distinguished, as in the OEIS entry. An original adjacent
pair is maintained if it occurs in either order in the new seating.

The row average is the sum of k*T(n,k) divided by the row sum. The exact
formula is stated from n=3, when every person has two distinct neighbors.

Source: https://oeis.org/A326404
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a326404
open Filter Topology Finset

def relabel {n : ℕ} (σ c : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  σ.symm.trans (c.trans σ)

noncomputable def circles (n : ℕ) : Finset (Equiv.Perm (Fin n)) := by
  classical
  exact univ.image (fun σ => relabel σ (finRotate n))

def adjacent {n : ℕ} (c : Equiv.Perm (Fin n)) (x y : Fin n) : Prop :=
  c x = y ∨ c y = x

noncomputable def kept {n : ℕ} (c : Equiv.Perm (Fin n)) : ℕ := by
  classical
  exact (univ.filter (fun x => adjacent c x (finRotate n x))).card

noncomputable def entry (n k : ℕ) : ℕ := by
  classical
  exact ((circles n).filter (fun c => kept c = k)).card

noncomputable def mean (n : ℕ) : ℝ :=
  (∑ k ∈ range (n+1), (k:ℝ)*entry n k)/(∑ k ∈ range (n+1), (entry n k:ℝ))

theorem main :
    (∀ n : ℕ, 3 ≤ n → mean n = 2/((n:ℝ)-1)+2) ∧
    Tendsto mean atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a326404
