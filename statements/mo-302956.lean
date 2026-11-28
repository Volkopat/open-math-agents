import Mathlib

/-!
# An inequality related to Power sum and elementary symmetric polynomial and majorizes

Source: https://mathoverflow.net/questions/302956
Credit: @JeremyDevs

Question (MathOverflow 302956, 2018). With `p_k(x) = x_1^k + ... + x_n^k` the power sums and
`e_k(x)` the elementary symmetric polynomials (the sum of all products of `k` distinct
variables), and with "`x` majorizes `y`" meaning `x_1 + ... + x_n = y_1 + ... + y_n`,
`x_1 ≥ ... ≥ x_n`, `y_1 ≥ ... ≥ y_n` and `x_1 + ... + x_i ≥ y_1 + ... + y_i` for all
`i ∈ {1, ..., n - 1}`, the question asks for a proof of: for `n ≥ 2` and nonnegative reals
`x_1, ..., x_n`, `y_1, ..., y_n` with equal sums, `x` majorizes `y` **if and only if**
`e_k(x) ≤ e_k(y)` and `p_k(x) ≥ p_k(y)` for all `k ∈ {2, ..., n}`.

The "only if" direction is true (Karamata; see the comments at the source). The "if" direction
is false: the comments at the source (D. Grinberg) give the counterexample `n = 3`,
`x = (9, 2, 2)`, `y = (6, 6, 1)`. `main` states that the answer to the question as asked is
negative, namely that the "if" direction fails.

Conventions:
* Tuples are functions `Fin n → ℝ` (index `i : Fin n` is the source's `i + 1`).
* `esymm k x` is `e_k(x)`, the sum over all `k`-element sets `s` of indices of `∏ i ∈ s, x i`;
  `psum k x` is `p_k(x)`.
* `Majorizes x y` is the source's definition verbatim: equal sums, both tuples nonincreasing
  (`Antitone`), and for every `i` with `1 ≤ i ≤ n - 1` the sum of the first `i` entries of `x` is
  at least that of `y`.
* So that the counterexample does not depend on how the garbled sentence of the source is read,
  the tuples in `main` are required to be nonnegative, to have equal sums **and** to be
  nonincreasing already; the two families of inequalities hold for every `k` with `2 ≤ k ≤ n`;
  and still `x` does not majorize `y`. This is exactly the failure of the "if" direction.
-/

namespace OMA.S_mo_302956

/-- The elementary symmetric polynomial `e_k` evaluated at the tuple `x`. -/
def esymm {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, x i

/-- The power sum `p_k` evaluated at the tuple `x`. -/
def psum {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ k

/-- `x` majorizes `y` (definition of the source). -/
def Majorizes {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  ∑ i, x i = ∑ i, y i ∧ Antitone x ∧ Antitone y ∧
    ∀ m : ℕ, 1 ≤ m → m ≤ n - 1 →
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), y i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < m), x i

/-- The "if" direction fails: there are nonincreasing nonnegative tuples with equal sums such
that `e_k(x) ≤ e_k(y)` and `p_k(x) ≥ p_k(y)` for all `2 ≤ k ≤ n`, but `x` does not majorize
`y`. -/
theorem main :
    ∃ (n : ℕ) (x y : Fin n → ℝ), 2 ≤ n ∧ (∀ i, 0 ≤ x i) ∧ (∀ i, 0 ≤ y i) ∧
      ∑ i, x i = ∑ i, y i ∧ Antitone x ∧ Antitone y ∧
      (∀ k : ℕ, 2 ≤ k → k ≤ n → esymm k x ≤ esymm k y ∧ psum k y ≤ psum k x) ∧
      ¬ Majorizes x y := by
  sorry

end OMA.S_mo_302956
