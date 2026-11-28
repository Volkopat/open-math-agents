import Mathlib

namespace OMA.S_arxiv_2201_00788

/-- Wilmshurst's conjecture (disproved by Lee–Lerario–Lundberg 2015 and further in
arXiv:2201.00788): for any complex polynomials `p` of degree `n` and `q` of degree `m`
with `1 ≤ m < n` such that the harmonic polynomial `z ↦ p(z) + conj(q(z))` has finitely
many zeros, the number of zeros is at most `m * (m - 1) + 3 * n - 2`. -/
theorem main :
    ∀ (n m : ℕ), 1 ≤ m → m < n →
    ∀ (p q : Polynomial ℂ), p.natDegree = n → q.natDegree = m →
    {z : ℂ | p.eval z + starRingEnd ℂ (q.eval z) = 0}.Finite →
    ∀ (S : Finset ℂ), (∀ z ∈ S, p.eval z + starRingEnd ℂ (q.eval z) = 0) →
      S.card ≤ m * (m - 1) + 3 * n - 2 := by
  sorry

end OMA.S_arxiv_2201_00788
