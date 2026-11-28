import FormalConjectures.OEIS.«217785»

-- Reduction OeisA217785.conjecture_4.R1 of Primes of the form 1 + 2s + ... + n s^(n-1) — conjecture4
-- Credit: @Andyi955
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- The target is an iff: `s_n` is reducible modulo every prime exactly when `n = 8k(k+1)`. The
-- forward direction (`8k(k+1)` forces reducibility at every prime) is a concrete algebraic
-- construction; the backward direction excludes every other `n` and needs a prime at which `s_n`
-- stays irreducible.

namespace OMA.R_OeisA217785_conjecture_4_R1

open OeisA217785

/-- Backward direction: if `n` is not of the form `8k(k+1)` with `k > 0`, then `s_n` is
irreducible modulo some prime. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ p : ℕ, p.Prime →
      ¬ Irreducible (Polynomial.map (Int.castRingHom (ZMod p)) (polyS n))) →
    ∃ k : ℕ, 0 < k ∧ n = 8 * k * (k + 1)

/-- Forward direction: for `n = 8k(k+1)` with `k > 0`, the polynomial `s_n` is reducible modulo
every prime. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 ≤ n → (∃ k : ℕ, 0 < k ∧ n = 8 * k * (k + 1)) →
    ∀ p : ℕ, p.Prime → ¬ Irreducible (Polynomial.map (Int.castRingHom (ZMod p)) (polyS n))

theorem main : H1 → H2 → type_of% @OeisA217785.conjecture_4 := by
  intro h1 h2 n hn
  exact ⟨fun h => h1 n hn h, fun h => h2 n hn h⟩

end OMA.R_OeisA217785_conjecture_4_R1
