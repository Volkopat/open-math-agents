import FormalConjectures.Wikipedia.FortuneConjecture

-- Reduction FortuneConjecture.fortune_conjecture.R1 of Fortune's conjecture
-- Credit: @marcusbuffett

/-!
# Fortune's conjecture: the classical square bound criterion, and the open rest

The `n`-th Fortunate number `q = F n` is the least `m > 1` with `P + m` prime, where `P` is the
primorial of the `(n+1)`-st prime `p = nth Prime n`.

* `H1` (classical, provable): if `F n < (nth Prime (n + 1)) ^ 2` then `F n` is prime. Every prime
  `r ≤ p` divides `P`, so a prime factor `r ≤ p` of `q` would divide the prime `P + q` and equal
  it, which is impossible as `r ≤ q < P + q`. Hence every prime factor of `q` is at least the next
  prime, and a composite `q` is at least its square.
* `H2` (open): `F n < (nth Prime (n + 1)) ^ 2` for every `n`. This is a statement about the gap
  after a primorial; heuristically `F n` is of the order of `p`, but no unconditional bound of
  this kind is known.

This is the standard partial result quoted for the conjecture, not progress on it.
-/

namespace OMA.R_FortuneConjecture_fortune_conjecture_R1

/-- Classical: a Fortunate number below the square of the next prime is prime. -/
def H1 : Prop :=
  ∀ n : ℕ, FortuneConjecture.fortunateNumber n < (Nat.nth Nat.Prime (n + 1)) ^ 2 →
    (FortuneConjecture.fortunateNumber n).Prime

/-- Open: every Fortunate number is below the square of the next prime. -/
def H2 : Prop :=
  ∀ n : ℕ, FortuneConjecture.fortunateNumber n < (Nat.nth Nat.Prime (n + 1)) ^ 2

theorem main : H1 → H2 → type_of% @FortuneConjecture.fortune_conjecture := by
  intro h1 h2 n
  exact h1 n (h2 n)

end OMA.R_FortuneConjecture_fortune_conjecture_R1
