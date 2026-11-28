import FormalConjectures.Wikipedia.Euclid

-- Reduction EuclidNumbers.euclid_numbers_are_square_free.R1 of the Euclid numbers squarefree question
-- Credit: @marcusbuffett

/-!
# Euclid numbers are squarefree: Euclid's argument, and the open rest

The `n`-th Euclid number is `E n = 1 + p_0 * ... * p_(n-1)`, with `p_i = nth Prime i`.

* `H1` (classical, provable): Euclid's argument. Every prime factor `q` of `E n` satisfies
  `p_n ≤ q`: a smaller prime is one of `p_0, ..., p_(n-1)`, divides the product, and would divide
  `1`. So the square of a prime below `p_n` never divides `E n`.
* `H2` (open): no prime `q ≥ p_n` has `q ^ 2 ∣ E n`. This is the open part: the square factors
  of Euclid numbers that Euclid's argument cannot exclude.

This is the classical observation behind the question, not progress on it.
-/

namespace OMA.R_EuclidNumbers_euclid_numbers_are_square_free_R1

/-- Classical (Euclid): every prime factor of the `n`-th Euclid number is at least `p_n`. -/
def H1 : Prop :=
  ∀ n q : ℕ, q.Prime → q ∣ EuclidNumbers.Euclid n → Nat.nth Nat.Prime n ≤ q

/-- Open: no prime at least `p_n` divides the `n`-th Euclid number twice. -/
def H2 : Prop :=
  ∀ n q : ℕ, q.Prime → Nat.nth Nat.Prime n ≤ q → ¬ q ^ 2 ∣ EuclidNumbers.Euclid n

theorem main : H1 → H2 → type_of% @EuclidNumbers.euclid_numbers_are_square_free := by
  intro h1 h2 n
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hqq
  have hdvd : q ∣ EuclidNumbers.Euclid n := (Dvd.intro q rfl).trans hqq
  exact h2 n q hq (h1 n q hq hdvd) (by rw [pow_two]; exact hqq)

end OMA.R_EuclidNumbers_euclid_numbers_are_square_free_R1
