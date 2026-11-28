import Mathlib

/-!
# Integer factorization in polynomial time

Source: https://en.wikipedia.org/wiki/Integer_factorization
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem: is there a classical (deterministic or randomized) algorithm that finds the prime
factorization of an `n`-bit integer in time polynomial in `n`?

Conventions:
* Algorithms are polynomial-time Turing machines (Mathlib's `Turing.TM2ComputableInPolyTime`) on
  bit strings. Randomness is modelled in the standard way by an extra input of random bits: on
  input `N` the machine reads `enc N ++ r` with `r` a uniformly random string of length `q(|enc N|)`
  for a fixed polynomial `q`, and it must output the factorization with probability at least
  `2/3` (any constant in `(1/2, 1)` gives the same class by repetition). A deterministic
  algorithm is the special case that ignores `r`.
* `enc` is a self-delimiting binary encoding. The output must be `enc p₁ ++ ⋯ ++ enc p_k` for some
  list of primes `p₁, …, p_k` with product `N` (`N ≥ 2`).
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wpc_factoring_in_p

/-- Self-delimiting binary encoding of a natural number. -/
def enc (k : ℕ) : List Bool := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false, false]

/-- `out` is a correct prime factorization of `N`. -/
def IsFactorizationOutput (N : ℕ) (out : List Bool) : Prop :=
  ∃ L : List ℕ, (∀ p ∈ L, p.Prime) ∧ L.prod = N ∧ out = L.flatMap enc

open Classical in
theorem main :
    ∃ (f : List Bool → List Bool) (q : Polynomial ℕ),
      Nonempty (Turing.TM2ComputableInPolyTime (id : List Bool → List Bool)
        (id : List Bool → List Bool) f) ∧
      ∀ N : ℕ, 2 ≤ N →
        (2 / 3 : ℚ) * 2 ^ (q.eval (enc N).length) ≤
          ((Finset.univ.filter (fun r : Fin (q.eval (enc N).length) → Bool =>
            IsFactorizationOutput N (f (enc N ++ List.ofFn r)))).card : ℚ) := by
  sorry

end OMA.S_wpc_factoring_in_p
