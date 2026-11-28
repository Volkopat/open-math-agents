import Mathlib

/-!
# Erdős Problem 879

Source: https://www.erdosproblems.com/879
Credit: @mgv27

Call a set $S\subseteq \{1,\ldots,n\}$ admissible if $(a,b)=1$ for all $a\neq b\in S$. Let
$G(n) = \max_{S} \sum_{a\in S} a$ (over admissible $S$) and
$H(n)=\sum_{p<n}p+ n\pi(n^{1/2})$. Is it true that $G(n) > H(n)-n^{1+o(1)}$?
Is it true that, for every $k\geq 2$, if $n$ is sufficiently large then the admissible set which
maximises $G(n)$ contains at least one integer with at least $k$ prime factors?

Formalization notes:
* `main` states the first question. The second is not stated here: it speaks of the maximising
  admissible set, which need not be unique.
* `G(n) > H(n) - n^{1+o(1)}` is stated as: for every `ε > 0`, eventually
  `G(n) > H(n) - n^{1+ε}`. This is equivalent (take `o(1)` to be a function tending to `0`).
* `π(n^{1/2})` counts the primes `p ≤ √n`, i.e. `p ≤ ⌊√n⌋ = Nat.sqrt n`.
* Erdős and Van Lint proved `H(n) - n^{3/2 - o(1)} < G(n) < H(n)`; checked by computer:
  `G(n) < H(n)` for `n = 10, 15, 20, 25, 30` with these definitions.
-/

namespace OMA.S_erdos_879

open Filter

/-- `G(n)`: the largest sum of a pairwise coprime set `S ⊆ {1, …, n}`. -/
noncomputable def G (n : ℕ) : ℕ :=
  sSup {s : ℕ | ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧ (S : Set ℕ).Pairwise Nat.Coprime ∧
    ∑ a ∈ S, a = s}

/-- `H(n) = ∑_{p < n} p + n π(n^{1/2})`. -/
def H (n : ℕ) : ℕ :=
  (∑ p ∈ (Finset.range n).filter Nat.Prime, p) + n * Nat.primeCounting (Nat.sqrt n)

/-- Erdős Problem 879: is it true that `G(n) > H(n) - n^{1 + o(1)}`? -/
theorem main : ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    (H n : ℝ) - (n : ℝ) ^ (1 + ε) < (G n : ℝ) := by
  sorry

end OMA.S_erdos_879
