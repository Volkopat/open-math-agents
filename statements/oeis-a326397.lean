import Mathlib

/-!
# Preserved neighboring pairs up to reflection (OEIS A326397)

A seating is a permutation of the people. Its image together with its
reflection in the fixed seating order represents a single seating class.
Rotated seatings are distinguished. Adjacency in the original circle is
undirected. The problem brief gives the row mean and prints two separate
conjectures for T(n,n-3). Both formulas and their subscripts are retained.
The index n-3 in the unrestricted formula is defined in the triangle for
n ≥ 3. The second formula has the entry's explicit restriction n > 4.

Source: https://oeis.org/A326397
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a326397
open Filter Topology

def kept {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i => p (finRotate n i) = finRotate n (p i) ∨
    p i = finRotate n (p (finRotate n i)))).card

noncomputable def entry (n k : ℕ) : ℕ := by
  classical
  let seatings := Finset.univ.filter (fun p : Equiv.Perm (Fin n) => kept p = k)
  exact (seatings.image (fun p => ({p, Fin.revPerm.trans p} : Finset (Equiv.Perm (Fin n))))).card

noncomputable def mean (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n+1), (k:ℝ)*entry n k)/
    (∑ k ∈ Finset.range (n+1), (entry n k:ℝ))

theorem main :
    ((∀ n : ℕ, 3 ≤ n → mean n = 2/((n:ℝ)-1)+2) ∧ Tendsto mean atTop (𝓝 2)) ∧
    (∀ n : ℕ, 3 ≤ n → (entry n (n-3):ℚ) = 1/2*(n:ℚ)^3 + 3/4*(n:ℚ)^2 - 2) ∧
    (∀ n : ℕ, 4 < n → (entry n (n-3):ℚ) =
      2/3*(n:ℚ)^4 + 3*(n:ℚ)^3 + 1/3*(n:ℚ)^2 - 7*(n:ℚ) + 3) := by
  sorry

end OMA.S_oeis_a326397
