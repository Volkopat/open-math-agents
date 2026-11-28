import Mathlib

/-!
# Conjectured new primality test for Mersenne numbers

Source: https://math.stackexchange.com/questions/1416221/conjectured-new-primality-test-for-mersenne-numbers
Credit: @mgv27

Let $M_q = 2^q - 1$, $S_0 = 3^2 + 1/3^2$, and $S_{i+1} = S_i^2 - 2 \pmod{M_q}$.
Conjecture: $M_q$ is a prime iff $S_{q-1} \equiv S_0 \pmod{M_q}$ (and iff
$\prod_{i=0}^{q-2} S_i \equiv 1$, and iff $S_i \not\equiv S_0$ for $0 < i < q-1$).
The easy part (if $M_q$ is prime then $S_{q-1} \equiv S_0$) has been proven; a proof of the
converse is needed.

Formalization notes:
* `main` states the first (principal) equivalence for odd primes `q`:
  `M_q` prime `↔ S_{q-1} = S_0` in `ZMod M_q`. Only the direction `←` is open.
* The asker's context (Mersenne exponents, "universal seed works for all q prime") is prime
  `q`; `q = 2` is excluded since `9` is not invertible mod `M_2 = 3`. For odd `q`,
  `3 ∤ M_q`, so `1/9` is the genuine inverse in `ZMod M_q`.
* The secondary product and cycle-length conditions are not formalized (the asker remarks
  in comments that the product condition is not relevant).
* Sanity check: for odd primes `q < 37` the condition holds exactly for
  `q = 3, 5, 7, 13, 17, 19, 31`, the Mersenne prime exponents in that range.
-/

namespace OMA.S_mse_1416221

/-- The sequence `S_0 = 9 + 9⁻¹`, `S_{i+1} = S_i ^ 2 - 2` in `ZMod (2 ^ q - 1)`. -/
def S (q : ℕ) : ℕ → ZMod (mersenne q)
  | 0 => 9 + (9 : ZMod (mersenne q))⁻¹
  | i + 1 => S q i ^ 2 - 2

/-- Reix's conjectured test: for an odd prime `q`, `2^q - 1` is prime iff `S_{q-1} = S_0`. -/
theorem main : ∀ q : ℕ, q.Prime → 2 < q →
    ((mersenne q).Prime ↔ S q (q - 1) = S q 0) := by
  sorry

end OMA.S_mse_1416221
