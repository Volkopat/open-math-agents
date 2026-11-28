import FormalConjectures.OEIS.«107247»

open OeisA107247

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
lemma large_factor_prime : Nat.Prime 5045088967 := by norm_num

/-- Each witness records the two prime factors of the nonacci sum of squares. -/
theorem OMA.solution : type_of% @OeisA107247.known_prime_and_semiprimes := by
  have product (n p q : ℕ) (value : a n = p * q) (hp : p.Prime) (hq : q.Prime) :
      (a n).IsSemiprime := value ▸ hp.mul_isAlmostPrime_two hq
  have first : a 8 = 2 := by decide +kernel
  refine ⟨first ▸ Nat.prime_two,
    product 9 2 3 (by decide +kernel) ?_ ?_,
    product 10 2 11 (by decide +kernel) ?_ ?_,
    product 11 2 43 (by decide +kernel) ?_ ?_,
    product 13 2 683 (by decide +kernel) ?_ ?_,
    product 14 2 2731 (by decide +kernel) ?_ ?_,
    product 16 2 43691 (by decide +kernel) ?_ ?_,
    product 17 37 9419 (by decide +kernel) ?_ ?_,
    product 27 71 5045088967 (by decide +kernel) ?_ large_factor_prime⟩
  all_goals norm_num
