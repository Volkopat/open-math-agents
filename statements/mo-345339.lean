import Mathlib

/-!
# Positive integral matrices below the proposed minimum entry sum

Source: loup blanc, https://mathoverflow.net/questions/345339 (CC BY-SA 4.0).
Credit: @connoranderson.

The proposed minimum n(n+2) fails in every dimension n=4r−1 for integer r≥2.
Add r to three entries of the identity plus the all-ones matrix, at positions
(0,1), (1,2), and (2,2). The entry sum is n²+n+3r, and the eigenvalues are
1, r, and n+2 with a nontrivial Jordan chain at 1. In dimension seven the
sum is 62, one below the proposed minimum.
-/
namespace OMA.S_mo_345339
open Matrix Polynomial Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℚ
def rationalDiagonalizable {n : ℕ} (A : Mat n) : Prop :=
  ∃ (P : (Mat n)ˣ) (v : Fin n → ℚ), A=(P:Mat n)*diagonal v*(P⁻¹: (Mat n)ˣ)

theorem main : ∀ m : ℕ,
    let n := 4*m+7
    let r := m+2
    ∃ A : Mat n,
      (∀ i j, ∃ k : ℕ, 0 < k ∧ A i j = k) ∧
      A.charpoly = (X-1)^(n-2)*(X-C (r:ℚ))*(X-C ((n:ℚ)+2)) ∧
      ¬ rationalDiagonalizable A ∧
      (∑ i, ∑ j, A i j) = (n:ℚ)^2+n+3*r ∧
      (∑ i, ∑ j, A i j) < (n:ℚ)*(n+2) := by
  sorry

end OMA.S_mo_345339
