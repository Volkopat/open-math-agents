import Mathlib

namespace OMA.S_arxiv_2408_13346

/-- For a partition represented by its multiset of parts `s`, `pre2 s` is the multiset
of monomials (pairwise products of parts) appearing in the second elementary symmetric
polynomial `e_2(s)`. -/
def pre2 (s : Multiset ℕ) : Multiset ℕ :=
  (s.powersetCard 2).map Multiset.prod

/-- The image `pre_2(P(n))` of all integer partitions of `n` under `pre_2`. -/
noncomputable def pre2Image (n : ℕ) : Finset (Multiset ℕ) :=
  Finset.univ.image (fun lam : Nat.Partition n => pre2 lam.parts)

/-- Conjecture from arXiv:2408.13346 (Mercer–... / experimental approach to partitions and
elementary symmetric polynomials): for every `n : ℕ`, the number of odd partitions in
`pre_2(P(n))` is at least the number of distinct partitions in `pre_2(P(n))`. -/
theorem main :
    ∀ n : ℕ,
      ((pre2Image n).filter (fun m => m.Nodup)).card ≤
        ((pre2Image n).filter (fun m => ∀ x ∈ m, Odd x)).card := by
  sorry

end OMA.S_arxiv_2408_13346
