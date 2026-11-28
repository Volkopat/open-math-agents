import OMAStatements.S_wp_are_all_mersenne_numbers_of_prime_index_square_free
import Mathlib

-- Reduction wp-are-all-mersenne-numbers-of-prime-index-square-free.R1 of the question whether
-- all Mersenne numbers of prime index are square-free.
-- Credit: @marcusbuffett

/-!
# Square factors of Mersenne numbers: the classical constraints, and the open rest

The classical part (step `H1`): if `q ^ 2 ∣ 2 ^ p - 1` for primes `p` and `q`, then the order of
`2` modulo `q` is `p`, so `q ≡ 1 (mod 2p)`, and `2 ^ (q - 1) = (2 ^ p) ^ ((q - 1) / p) ≡ 1
(mod q ^ 2)`: `q` is a Wieferich prime. The only Wieferich primes below `100001` are `1093` and
`3511` (a finite check), and neither divides a Mersenne number of prime index (the orders of `2`
modulo them are `364` and `1755`), so `q > 100000`.

This is the textbook observation (Guy, Unsolved Problems in Number Theory, A3), not progress on
the conjecture: step `H2`, that no such Wieferich prime square divides `2 ^ p - 1`, is equivalent
to the open question.
-/

namespace OMA.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1

/-- A square of a prime dividing `2 ^ p - 1` for a prime `p` is the square of a Wieferich prime
`q > 100000` with `q ≡ 1 (mod 2p)`. -/
def H1 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → q ^ 2 ∣ 2 ^ p - 1 →
    2 ^ (q - 1) % q ^ 2 = 1 ∧ q % (2 * p) = 1 ∧ 100000 < q

/-- The open part: no such Wieferich prime square divides a Mersenne number of prime index. -/
def H2 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → 2 ^ (q - 1) % q ^ 2 = 1 → q % (2 * p) = 1 → 100000 < q →
    ¬ q ^ 2 ∣ 2 ^ p - 1

theorem main : H1 → H2 →
    type_of% @OMA.S_wp_are_all_mersenne_numbers_of_prime_index_square_free.main := by
  intro h1 h2 p hp
  unfold OMA.S_wp_are_all_mersenne_numbers_of_prime_index_square_free.mersenne
  rw [Nat.squarefree_iff_prime_squarefree]
  intro q hq hdvd
  have hq' : q.Prime := hq
  have hdvd' : q ^ 2 ∣ 2 ^ p - 1 := by rwa [sq]
  obtain ⟨hw, hc, hb⟩ := h1 p q hp hq' hdvd'
  exact h2 p q hp hq' hw hc hb hdvd'

end OMA.R_wp_are_all_mersenne_numbers_of_prime_index_square_free_R1
