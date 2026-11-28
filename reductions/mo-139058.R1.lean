import OMAStatements.S_mo_139058
import Mathlib

/-!
# Reduction of MathOverflow 139058 (does the operation on pairs of primes always repeat?)

`A(p, q) = {m + n : m p + n q = 1}` and `f(p, q)` is the pair of the two least primes in `A(p, q)`.

* `H1` (classical, the pairs at distance `1`, `2` or `4`: `(2, 3)`, all twin prime pairs and all
  cousin prime pairs): the orbit repeats. For `p < q`, `s ∈ A(p, q)` iff `q - p ∣ 1 - s p` (put
  `m = s - n`), so `A(p, q)` is one residue class modulo `q - p`, and `f` sends these pairs to the
  fixed points `(2, 3)`, `(3, 5)`, `(3, 7)` or `(5, 13)`.
* `H2` (the open core): the pairs at distance `3` or at least `5`.

This is a classical partial case, not progress on the open question.
-/

namespace OMA.R_mo_139058_R1

/-- Pairs of distinct primes at distance `1`, `2` or `4` have a repeating orbit. -/
def H1 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → (q = p + 1 ∨ q = p + 2 ∨ q = p + 4 ∨
      p = q + 1 ∨ p = q + 2 ∨ p = q + 4) →
    ∃ i j : ℕ, i < j ∧ OMA.S_mo_139058.f^[i] (p, q) = OMA.S_mo_139058.f^[j] (p, q)

/-- The open core: pairs of distinct primes at any other distance. -/
def H2 : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
    ¬ (q = p + 1 ∨ q = p + 2 ∨ q = p + 4 ∨ p = q + 1 ∨ p = q + 2 ∨ p = q + 4) →
    ∃ i j : ℕ, i < j ∧ OMA.S_mo_139058.f^[i] (p, q) = OMA.S_mo_139058.f^[j] (p, q)

theorem main : H1 → H2 → type_of% @OMA.S_mo_139058.main := by
  intro h1 h2 p q hp hq hpq
  by_cases hc : q = p + 1 ∨ q = p + 2 ∨ q = p + 4 ∨ p = q + 1 ∨ p = q + 2 ∨ p = q + 4
  · exact h1 p q hp hq hc
  · exact h2 p q hp hq hpq hc

end OMA.R_mo_139058_R1
