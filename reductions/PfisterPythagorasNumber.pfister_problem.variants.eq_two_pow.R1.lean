import FormalConjectures.Paper.PfisterPythagorasNumber

/-!
# Reduction of Pfister's problem in its yes/no form: is p(ℝ(X_1, ..., X_n)) = 2^n?

The target `PfisterPythagorasNumber.pfister_problem.variants.eq_two_pow` says that for every `n`
the Pythagoras number of `ℝ(X_1, ..., X_n)` is exactly `2 ^ n`. It splits into three known
theorems and one open core:
- `H1`: Pfister's theorem (1967/1971), every sum of squares in `ℝ(X_1, ..., X_n)` is a sum of
  `2 ^ n` squares. This is the whole upper half of the target, word for word the catalogue
  statement `pfister_problem.variants.upper_bound`.
- `H2`: Cassels' theorem (1964), `1 + X_1^2 + ... + X_n^2` is not a sum of `n` squares, word for
  word `pfister_problem.variants.cassels`. It gives the lower half for `n = 0` and `n = 1`.
- `H3`: the Cassels-Ellison-Pfister lower bound `n + 2 ≤ p` for `n ≥ 2`, word for word
  `pfister_problem.variants.lower_bound` (which has its own merged reduction). It gives the lower
  half for `n = 2`.
- `H4`: the open core, the lower half of the target for `n ≥ 3` only: no `p < 2 ^ n` bounds the
  number of squares in `ℝ(X_1, ..., X_n)`. This is open for every `n ≥ 3`
  (Merkurjev-Parimala 2025, Question 5.7, already for `n = 3`).

All four hypotheses are consequences of the target or known theorems, so the reduction is
downward: it removes the upper bound and the cases `n ≤ 2` from the open statement.
-/

-- Reduction PfisterPythagorasNumber.pfister_problem.variants.eq_two_pow.R1 of Pfister's problem on the Pythagoras number of $\mathbb{R}(X_1, \dots, X_n)$, yes/no form
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_PfisterPythagorasNumber_pfister_problem_variants_eq_two_pow_R1

/-- Pfister's theorem: every sum of squares in R(X_1, ..., X_n) is a sum of 2^n squares. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 ^ n ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ)

/-- Cassels (1964): 1 + X_1^2 + ... + X_n^2 is not a sum of n squares in R(X_1, ..., X_n). -/
def H2 : Prop :=
  ∀ n : ℕ, ¬IsSumSqOfLength n (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
    (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i))

/-- Cassels-Ellison-Pfister lower bound: n + 2 ≤ p(R(X_1, ..., X_n)) for n ≥ 2. -/
def H3 : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∀ p : ℕ, p ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ) → n + 2 ≤ p

/-- Open core: for n ≥ 3, every bound for the number of squares in R(X_1, ..., X_n) is at
least 2^n. -/
def H4 : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∀ p : ℕ, p ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ) → 2 ^ n ≤ p

/-- Cassels' theorem gives n + 1 ≤ p for every bound p. -/
lemma add_one_le_of_cassels (h2 : H2) (n : ℕ) {p : ℕ}
    (hp : p ∈ pythagorasBounds (MvRatFunc (Fin n) ℝ)) : n + 1 ≤ p := by
  by_contra h
  have hsq : IsSumSqOfLength (n + 1) (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i)) :=
    ⟨Fin.cons 1 fun i ↦ algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (MvPolynomial.X i), by simp [Fin.sum_univ_succ, map_sum]⟩
  exact h2 n ((hp _ hsq.isSumSq).of_le (by omega))

theorem main : H1 → H2 → H3 → H4 →
    type_of% @PfisterPythagorasNumber.pfister_problem.variants.eq_two_pow := by
  intro h1 h2 h3 h4 n
  refine ⟨h1 n, fun p hp => ?_⟩
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · exact add_one_le_of_cassels h2 0 hp
    · exact add_one_le_of_cassels h2 1 hp
    · exact h3 2 le_rfl p hp
  · exact h4 n hn p hp

end OMA.R_PfisterPythagorasNumber_pfister_problem_variants_eq_two_pow_R1
