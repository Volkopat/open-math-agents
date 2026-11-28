import Mathlib

namespace OMA.S_arxiv_2001_06839

/-- Recursive probability generating function of the number of wrongly seated passengers among
the remaining `rem` passengers (indices `n - rem, ..., n - 1`) in an `n`-seat airplane with
`k` absent-minded passengers (`0, ..., k - 1`) when `occ` is the set of already-occupied seats.
Each absent-minded passenger (`i < k`) picks uniformly at random from the unoccupied seats;
each subsequent passenger (`i ≥ k`) takes seat `i` if unoccupied and otherwise picks uniformly
at random from the unoccupied seats. -/
noncomputable def ampStep (n k : ℕ) (t : ℝ) : ℕ → Finset (Fin n) → ℝ
  | 0, _ => 1
  | r + 1, occ =>
      let i := n - (r + 1)
      let free := Finset.univ \ occ
      if i < k then
        (1 / (free.card : ℝ)) *
          ∑ s ∈ free, (if s.val = i then (1 : ℝ) else t) * ampStep n k t r (insert s occ)
      else if h : i < n then
        if ⟨i, h⟩ ∉ occ then
          ampStep n k t r (insert ⟨i, h⟩ occ)
        else
          (1 / (free.card : ℝ)) *
            ∑ s ∈ free, t * ampStep n k t r (insert s occ)
      else 1

/-- Probability generating function `E[t^{X_{n,k}}]` of the total number `X_{n,k}` of
passengers occupying a wrong seat in an `n`-seat airplane with `k` absent-minded passengers
(Henze–Last AMM 2019; Ekhad–Zeilberger, arXiv:2001.06839). -/
noncomputable def ampPGF (n k : ℕ) (t : ℝ) : ℝ :=
  ampStep n k t n ∅

/-- Explicit closed-form probability generating function for the Absent-Minded Passengers
problem with `k` absent-minded passengers out of `n` (`k ≤ n`), answering the open problem
of Henze and Last (AMM 2019) resolved in Ekhad–Zeilberger (arXiv:2001.06839). -/
theorem main :
    ∀ (n k : ℕ) (t : ℝ), k ≤ n →
      ampPGF n k t =
        ((Nat.factorial k : ℝ) / (Nat.factorial n : ℝ)) *
          ∑ s ∈ Finset.range (k + 1),
            ((1 - t) ^ s * t ^ (k - s) / (Nat.factorial s : ℝ)) *
              ∏ j ∈ Finset.Icc 1 (n - k), ((j : ℝ) + ((k - s : ℕ) : ℝ) * t) := by
  sorry

end OMA.S_arxiv_2001_06839
