import Mathlib

/-!
# Even coefficients of the double Lambert series in OEIS A350583

Source: https://oeis.org/A350583
Credit: @etaubman

The conjecture was posed by Andrews, Dixit, Schultz and Yee. See also the
proofs by Qianwen Fang (arXiv:2604.06242) and Su-Ping Cui and Dazhao Tang
(arXiv:2604.08839). The even coefficients are finite sums.
-/

namespace OMA.S_oeis_a350583

abbrev Index := ℕ × ℕ × ℕ × ℕ

/-- The term with m,n ≥ 1 and the two geometric expansion indices k,l ≥ 0,
in exactly the order used in the defining double series. -/
def geometricDegree : Index → ℕ
  | (m,n,k,l) => 2*m*n + m + n*k + (2*m-1)*l

def geometricSign : Index → ℤ
  | (m,_,k,_) => if (m+k)%2=0 then 1 else -1

noncomputable def geometricCoefficient (N : ℕ) : ℤ := by
  classical
  exact ∑ r ∈ (Finset.Iic ((N,N,N,N) : Index)).filter
    (fun r => 0 < r.1 ∧ 0 < r.2.1 ∧ geometricDegree r = N), geometricSign r

theorem main : ∀ k : ℕ, geometricCoefficient (2*k) = 0 := by
  sorry

end OMA.S_oeis_a350583
