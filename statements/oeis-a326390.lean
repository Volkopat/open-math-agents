import Mathlib

/-!
# Preserved neighboring pairs around a labeled table (OEIS A326390)

A permutation assigns the people to the seats of the original circle.
An edge is preserved if its occupants were neighbors in either order.
Rotations and reflections are distinct seatings in this entry. For n ≥ 3
the original circle has n distinct undirected edges. The three conjectures
in the problem brief give the exact row average and its limit, and two
near-diagonal entries. The final polynomial is transcribed as printed.

Source: https://oeis.org/A326390
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a326390
open Filter Topology

def kept {n : ℕ} (p : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i => p (finRotate n i) = finRotate n (p i) ∨
    p i = finRotate n (p (finRotate n i)))).card

def entry (n k : ℕ) : ℕ :=
  (Finset.univ.filter (fun p : Equiv.Perm (Fin n) => kept p = k)).card

noncomputable def mean (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n+1), (k:ℝ)*entry n k)/(n.factorial:ℝ)

theorem main :
    ((∀ n : ℕ, 3 ≤ n → mean n = 2/((n:ℝ)-1)+2) ∧ Tendsto mean atTop (𝓝 2)) ∧
    (∀ n : ℕ, 3 < n → entry n (n-2) = n^2*(n-3)) ∧
    (∀ n : ℕ, 4 < n → (entry n (n-3):ℚ) =
      3/4*(n:ℚ)^4 + 6*(n:ℚ)^3 + 2/3*(n:ℚ)^2 - 14*(n:ℚ) + 6) := by
  sorry

end OMA.S_oeis_a326390
