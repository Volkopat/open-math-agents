import Mathlib

/-!
# Erdős Problem 892

Source: https://www.erdosproblems.com/892
Credit: @mgv27

Is there a necessary and sufficient condition for a sequence of integers $b_1<b_2<\cdots$ that
ensures there exists a primitive sequence $a_1<a_2<\cdots$ (i.e. no element divides another)
with $a_n \ll b_n$ for all $n$? In particular, is this always possible if there are no
non-trivial solutions to $(b_i,b_j)=b_k$?

Similarly, find necessary and sufficient conditions on a sequence $n_1<n_2<\cdots$ that ensure
there exists a primitive set $A$ such that $\lvert A\cap [1,2^{n_i}]\rvert \gg 2^{n_i}$ for every
$i$.

Formalization notes:
* `main` states the precise sub-question ("in particular ..."); the requests for necessary and
  sufficient conditions are not precise and are not stated.
* Sequences are strictly increasing maps `ℕ → ℕ` with positive values (indexed from `0`).
* A non-trivial solution of `(b_i, b_j) = b_k` is one with `i, j, k` pairwise distinct. A
  solution with `k ∈ {i, j}` just says `b_k ∣` the other term; if those counted, the hypothesis
  would force `b` itself to be primitive and the question would be trivial (take `a = b`).
  Example: `b_n = 2^n` satisfies the hypothesis.
* `a_n ≪ b_n` means: there is a constant `C > 0` with `a_n ≤ C b_n` for all `n`.
* The source notes that `∑ 1/(b_n log b_n) < ∞` and
  `∑_{b_n < x} 1/b_n = o(log x / √(log log x))` are necessary.
-/

namespace OMA.S_erdos_892

/-- A sequence is primitive if no term divides a different term. -/
def Primitive (a : ℕ → ℕ) : Prop :=
  ∀ i j, i ≠ j → ¬ a i ∣ a j

/-- `(b_i, b_j) = b_k` has no solution with `i, j, k` pairwise distinct. -/
def NoNontrivialGcd (b : ℕ → ℕ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → Nat.gcd (b i) (b j) ≠ b k

/-- Erdős Problem 892: if `b` has no non-trivial solutions to `(b_i, b_j) = b_k`, is there a
primitive sequence `a_1 < a_2 < ⋯` with `a_n ≪ b_n`? -/
theorem main : ∀ b : ℕ → ℕ, StrictMono b → (∀ n, 0 < b n) → NoNontrivialGcd b →
    ∃ a : ℕ → ℕ, StrictMono a ∧ (∀ n, 0 < a n) ∧ Primitive a ∧
      ∃ C > (0 : ℝ), ∀ n, (a n : ℝ) ≤ C * (b n : ℝ) := by
  sorry

end OMA.S_erdos_892
