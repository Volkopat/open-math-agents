import Mathlib

/-!
# MathOverflow 300118: walking to infinity on the primes with finitely many affine steps

Source: https://mathoverflow.net/questions/300118
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Question (Stefan Kohl): let `(a_1,b_1), …, (a_k,b_k)` be finitely many pairs of positive
integers, and let `Γ` be the graph whose vertices are the prime numbers, in which `p` and `q`
are joined by an edge iff `a_i p + b_i = q` or `a_i q + b_i = p` for some `i`. Is it true that
necessarily all connected components of `Γ` are finite?

We state the affirmative answer (a disproof of `main` answers the question negatively).

Conventions:
* The finite family of pairs is a `Finset (ℕ × ℕ)` all of whose coordinates are positive;
  `k = 0` (the empty family) is allowed by the wording and is harmless (no edges).
* `SimpleGraph.fromRel r` has `Adj p q ↔ p ≠ q ∧ (r p q ∨ r q p)`, with `r p q` meaning
  `a_i p + b_i = q` for some `i`; this is the source's edge relation. Since `b_i ≥ 1`,
  `a_i p + b_i ≠ p`, so the clause `p ≠ q` added by `fromRel` changes nothing.
* The connected component of `p` is the set of primes reachable from `p` in `Γ`.
-/

namespace OMA.S_mo_300118

/-- The graph `Γ` on the primes defined by the affine steps in `S`. -/
def affineGraph (S : Finset (ℕ × ℕ)) : SimpleGraph {p : ℕ // p.Prime} :=
  SimpleGraph.fromRel fun p q => ∃ ab ∈ S, ab.1 * p.1 + ab.2 = q.1

/-- For every finite family of pairs of positive integers, every connected component of `Γ`
is finite. -/
theorem main : ∀ S : Finset (ℕ × ℕ), (∀ ab ∈ S, 0 < ab.1 ∧ 0 < ab.2) →
    ∀ p : {p : ℕ // p.Prime}, {q | (affineGraph S).Reachable p q}.Finite := by
  sorry

end OMA.S_mo_300118
