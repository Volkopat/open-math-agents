import FormalConjectures.ErdosProblems.«1094»

-- Reduction Erdos1094.erdos_1094.R1 of Erdős Problem 1094
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: split the exceptional pairs (n, k) by the size of n relative to k^2.
-- * H1 (range n ≥ k^2): here max (n / k) k = n / k, and Ecklund (Pacific J. Math. 1969,
--   On prime divisors of the binomial coefficient) proved that for n ≥ k^2 the binomial
--   coefficient C(n, k) has a prime factor ≤ n / k, the only exception being C(62, 6).
--   So H1 is a known theorem that is not yet in Mathlib.
-- * H2 (range 2k ≤ n < k^2): the remaining open core of the conjecture of
--   Erdős, Lacampagne and Selfridge.
-- The exceptional set is contained in the union of the two sets, so it is finite.
-- No computer search was used.

namespace OMA.R_Erdos1094_erdos_1094_R1

/-- Ecklund's range `n ≥ k^2`: only finitely many exceptions. -/
def H1 : Prop :=
  {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ k * k ≤ n ∧
    (n.choose k).minFac > max (n / k) k}.Finite

/-- The open range `2k ≤ n < k^2`: only finitely many exceptions. -/
def H2 : Prop :=
  {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ n < k * k ∧
    (n.choose k).minFac > max (n / k) k}.Finite

theorem main : H1 → H2 → type_of% @Erdos1094.erdos_1094 := by
  intro h1 h2
  unfold H1 at h1
  unfold H2 at h2
  refine (h1.union h2).subset ?_
  rintro ⟨n, k⟩ ⟨hk, h2k, hm⟩
  by_cases h : k * k ≤ n
  · exact Or.inl ⟨hk, h2k, h, hm⟩
  · exact Or.inr ⟨hk, h2k, by omega, hm⟩

end OMA.R_Erdos1094_erdos_1094_R1
