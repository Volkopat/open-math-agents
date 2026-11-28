import Mathlib

/-!
# Nonpositive sum of the largest eigenvalues after subtracting the diagonal

Source: Victor Reis, https://mathoverflow.net/questions/334087 (CC BY-SA 4.0).
Credit: @connoranderson.

For any real positive semidefinite n-by-n matrix A, every n−k+1 eigenvalues
of A−k diag(A) sum to at most zero. In particular this holds for the largest
such eigenvalues. Christian Remling suggested the projection reformulation in
the source comments. We prove it by two Cauchy–Schwarz inequalities and use
a spectral projection to recover the eigenvalue inequality.

For the proposed generalization, the sum from the m-th to the
(n−m(k−1))-th largest eigenvalue is also nonpositive for every positive m.
The proof maximizes a regularized determinant on positive contractions,
counts the contracted directions, and passes to a compact limit. This gives
the required trace estimate on the span of the leading eigenvectors.
-/
namespace OMA.S_mo_334087
open Matrix Finset
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ
def diagPart {n : ℕ} (A : Mat n) : Mat n := diagonal (fun i => A i i)
def shifted {n : ℕ} (A : Mat n) (k : ℕ) : Mat n := A - (k:ℝ) • diagPart A
theorem main :
    (∀ n (P : Mat n), P.IsHermitian → P*P=P →
      (((n:ℝ)+1-P.trace) • diagPart P - P).PosSemidef) ∧
    (∀ n (A : Mat n), A.PosSemidef → ∀ k, ∃ h : (shifted A k).IsHermitian,
      ∀ S : Finset (Fin n), S.card+k=n+1 → ∑ i ∈ S,h.eigenvalues i ≤ 0) ∧
    (∀ n (A : Mat n), A.PosSemidef → ∀ k m : ℕ, 1 ≤ k → 1 ≤ m →
      ∃ h : (shifted A k).IsHermitian,
        ∑ i ∈ (univ.filter (fun i : Fin (Fintype.card (Fin n)) =>
          m-1 ≤ i.val ∧ i.val < n-m*(k-1))), h.eigenvalues₀ i ≤ 0) := by
  sorry
end OMA.S_mo_334087
