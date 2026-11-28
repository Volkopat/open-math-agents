import Mathlib

/-!
# Sharp degree bound for the adjugate of a polynomial matrix

Source: Tadashi, https://mathoverflow.net/questions/243833 (CC BY-SA).
The sharp bound and the diagonal witness were proposed by user35593 in the comments.
Credit: @connoranderson.

For a matrix of size n+1, bound every adjugate entry by n*d. For each positive
number of variables the bound is attained by a matrix whose entries have
maximum total degree exactly d.
-/

namespace OMA.S_mo_243833

abbrev PolyMat (m n : ℕ) := Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial (Fin m) ℝ)

theorem main :
    (∀ (m n d : ℕ) (A : PolyMat m n), (∀ i j, (A i j).totalDegree ≤ d) →
      ∀ i j, (A.adjugate i j).totalDegree ≤ n*d) ∧
    ∀ m n d : ℕ, ∃ A : PolyMat (m+1) n,
      (∀ i j, (A i j).totalDegree ≤ d) ∧ (A 0 0).totalDegree = d ∧
      (A.adjugate 0 0).totalDegree = n*d := by
  sorry

end OMA.S_mo_243833
