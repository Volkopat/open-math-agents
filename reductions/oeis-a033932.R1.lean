import OMAStatements.S_oeis_a033932
import Mathlib

-- Reduction oeis-a033932.R1 of OEIS A033932 (least m ≥ 1 with n! + m prime is 1 or a prime)
-- Credit: @marcusbuffett

/-!
# A033932: prime factors of `a(n)` exceed `n`, and the open rest

`a(n)` is the least `m ≥ 1` with `n! + m` prime; Murthy's conjecture is that `a(n)` is `1` or
prime. This separates the elementary part (the same argument as for Fortunate numbers) from the
open part. It is a classical partial result, not progress on the conjecture itself.

* `H1` (proved): `a(n) ≥ 1`; if `a(n) > 1` then every prime factor `q` of `a(n)` satisfies
  `q > n`; and if moreover `a(n)` is composite then `(n + 1)^2 ≤ a(n)`. Proof: `a(n)` lies in its
  defining set since there are infinitely many primes. A prime `q ≤ n` dividing `a(n)` divides
  `n! + a(n)`, which is a prime larger than `q`. A composite `a(n)` has `minFac^2 ≤ a(n)`.
* `H2`: every `a(n) > 1` with all prime factors above `n` (hence, if composite, at least
  `(n + 1)^2`) is prime. This is the open rest; it would follow from a prime in
  `(n! + 1, n! + (n + 1)^2)`.
-/

namespace OMA.R_oeis_a033932_R1

open OMA.S_oeis_a033932

/-- The elementary facts about `a(n)`. -/
def H1 : Prop :=
  (∀ n : ℕ, 1 ≤ a n) ∧
  (∀ n : ℕ, 1 < a n → ∀ q : ℕ, q.Prime → q ∣ a n → n < q) ∧
  (∀ n : ℕ, 1 < a n → ¬ (a n).Prime → (n + 1) ^ 2 ≤ a n)

/-- The open rest. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < a n → (n + 1) ^ 2 ≤ a n → (∀ q : ℕ, q.Prime → q ∣ a n → n < q) → (a n).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a033932.main := by
  rintro ⟨hpos, hfac, hsq⟩ h2 n
  rcases (hpos n).lt_or_eq with hlt | heq
  · by_cases hp : (a n).Prime
    · exact Or.inr hp
    · exact Or.inr (h2 n hlt (hsq n hlt hp) (hfac n hlt))
  · exact Or.inl heq.symm

end OMA.R_oeis_a033932_R1
