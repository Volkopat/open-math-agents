import Mathlib

/-!
# Elegant paths labeled by the first odd primes

Source: https://arxiv.org/abs/1907.01249 (Thierry Gensane, Elegant vertex labelings with prime
numbers), Conjecture 1: for all n ≥ 2 the path is elegant.

Let p₁ = 3, p₂ = 5, p₃ = 7, … be the odd primes in increasing order. Following the paper, a path
with n vertices is elegant if there is a permutation σ of {1, …, n} such that
{|p_σ(i+1) − p_σ(i)| : 1 ≤ i ≤ n − 1} = {2, 4, …, 2n − 2}. The paper says "the path of length n"
but then defines the property for a path of n vertices; both readings cover all paths with at
least two vertices, so they agree. Here the vertices are Fin n, the i-th odd prime is
Nat.nth Nat.Prime (i + 1) for i : Fin n, and equality of the two sets of n − 1 values forces the
edge labels to be distinct.

Literature: verified by computer up to n = 3500 in the paper; no proof found in later work.
-/

namespace OMA.S_arxiv_1907_01249

/-- The odd primes in increasing order, indexed from `0`: `oddPrime 0 = 3`. -/
noncomputable def oddPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i + 1)

/-- The path on `n` vertices labeled along `σ` is elegant: its edge labels are `2, 4, …, 2n - 2`. -/
def IsElegantPath (n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  {d | ∃ i j : Fin n, j.val = i.val + 1 ∧
      d = Int.natAbs ((oddPrime (σ j).val : ℤ) - oddPrime (σ i).val)} =
    {d | ∃ k, 1 ≤ k ∧ k ≤ n - 1 ∧ d = 2 * k}

theorem main : ∀ n : ℕ, 2 ≤ n → ∃ σ : Equiv.Perm (Fin n), IsElegantPath n σ := by
  sorry

end OMA.S_arxiv_1907_01249
