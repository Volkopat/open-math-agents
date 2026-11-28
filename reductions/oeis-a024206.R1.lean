import OMAStatements.S_oeis_a024206
import Mathlib

-- Reduction oeis-a024206.R1 of OEIS A024206 (if ⌊q²/4⌋ = p# then q is prime)
-- Credit: @marcusbuffett

/-!
# A024206: `q` is odd with `q² = 4·p# + 1`, all prime factors of `q` exceed `p`, and the open rest

The conjecture: if `a(n) = ⌊(n+1)²/4⌋ - 1 = p# - 1` for a prime `p`, then `q = n + 1` is prime.
This separates the elementary part from the open part. It is a partial result, not progress on
the conjecture itself.

* `H1` (proved): under the hypotheses, `q` is odd, `q² = 4·p# + 1`, and every prime factor `r`
  of `q` satisfies `r > p`. Proof: `⌊q²/4⌋ = p#`. An even `q = 2t` gives `t² = p#`, impossible
  since `p#` is squarefree and `> 1`. For odd `q = 2t + 1`, `⌊q²/4⌋ = t² + t`, so
  `q² = 4·p# + 1`; a prime `r ≤ p` divides `p#`, so `r ∤ q² - 4·p# = 1`, hence `r ∤ q`.
* `H2`: such a `q` (odd, `q² = 4·p# + 1`, all prime factors above `p`) is prime. This is the
  open rest.
-/

namespace OMA.R_oeis_a024206_R1

open OMA.S_oeis_a024206

/-- The elementary facts. -/
def H1 : Prop :=
  ∀ n p : ℕ, 1 ≤ n → p.Prime → a n + 1 = primorial p →
    Odd (n + 1) ∧ (n + 1) ^ 2 = 4 * primorial p + 1 ∧ ∀ r : ℕ, r.Prime → r ∣ n + 1 → p < r

/-- The open rest. -/
def H2 : Prop :=
  ∀ n p : ℕ, 1 ≤ n → p.Prime → a n + 1 = primorial p →
    Odd (n + 1) → (n + 1) ^ 2 = 4 * primorial p + 1 → (∀ r : ℕ, r.Prime → r ∣ n + 1 → p < r) →
    (n + 1).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a024206.main := by
  intro h1 h2 n p hn hp h
  obtain ⟨hodd, hsq, hr⟩ := h1 n p hn hp h
  exact h2 n p hn hp h hodd hsq hr

end OMA.R_oeis_a024206_R1
