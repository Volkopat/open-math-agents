import Mathlib

/-!
# Projective primes for a fixed prime dimension

Source: https://arxiv.org/abs/2010.08023 (Gareth A. Jones, Alexander K. Zvonkin, Primes in
geometric series and finite permutation groups), Conjecture 6.5, the conjecture of the abstract:
for any fixed prime n ≥ 3 there are infinitely many prime values m = 1 + p + p² + ⋯ + p^(n-1),
where p ranges over all prime numbers. (m = (pⁿ − 1)/(p − 1) is the natural degree of Lₙ(p).)

This restricted form implies the paper's general Conjecture 1.3 (infinitely many projective
primes). Literature: open even for n = 3 (primes p with p² + p + 1 prime, a case of the
Bunyakovsky/Bateman–Horn conjectures); no resolution was found.
-/

namespace OMA.S_arxiv_2010_08023

theorem main : ∀ n : ℕ, n.Prime → 3 ≤ n →
    {p : ℕ | p.Prime ∧ (∑ i ∈ Finset.range n, p ^ i).Prime}.Infinite := by
  sorry

end OMA.S_arxiv_2010_08023
