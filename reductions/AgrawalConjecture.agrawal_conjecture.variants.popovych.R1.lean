import FormalConjectures.Wikipedia.Agrawal
import Mathlib

-- Reduction AgrawalConjecture.agrawal_conjecture.variants.popovych.R1 of Popovych's strengthening
-- of Agrawal's conjecture: if (X - 1)^n = X^n - 1 and (X + 2)^n = X^n + 2 modulo (n, X^r - 1),
-- then n is prime or n^2 = 1 mod r.
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the conjecture itself. H1 evaluates the second
-- congruence at X = 1, which gives the Fermat congruence 3^n = 3 mod n, and draws the classical
-- consequence for square factors: if p^2 divides n then p is not 3 and 3^(p - 1) = 1 mod p^2,
-- that is p is a base-3 Wieferich prime (only 11 and 1006003 are known). So the conjecture holds
-- for every n divisible by 9 or by the square of a prime that is not base-3 Wieferich. H2, the
-- remaining n (all squarefree n among them), carries the whole open difficulty.

namespace OMA.R_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1

open Polynomial

/-- The second Popovych congruence forces every square prime factor of `n` to be a base-3
Wieferich prime other than 3. -/
def H1 : Prop :=
  ∀ (n r : ℕ), n > 1 →
    let R := Polynomial (ZMod n)
    let X : R := Polynomial.X
    let I : Ideal R := Ideal.span ({X^r - 1} : Set R)
    Ideal.Quotient.mk I ((X + 2)^n) = Ideal.Quotient.mk I (X^n + 2) →
    ∀ p : ℕ, p.Prime → p ^ 2 ∣ n → p ≠ 3 ∧ (3 : ZMod (p ^ 2)) ^ (p - 1) = 1

/-- The conjecture for the `n` whose square prime factors are all base-3 Wieferich primes (open). -/
def H2 : Prop :=
  ∀ (n r : ℕ), n > 1 → r > 0 → n.gcd r = 1 →
    let R := Polynomial (ZMod n)
    let X : R := Polynomial.X
    let I : Ideal R := Ideal.span ({X^r - 1} : Set R)
    Ideal.Quotient.mk I ((X - 1)^n) = Ideal.Quotient.mk I (X^n - 1) →
    Ideal.Quotient.mk I ((X + 2)^n) = Ideal.Quotient.mk I (X^n + 2) →
    (∀ p : ℕ, p.Prime → p ^ 2 ∣ n → p ≠ 3 ∧ (3 : ZMod (p ^ 2)) ^ (p - 1) = 1) →
    (n.Prime ∨ (n^2 : ZMod r) = 1)

theorem main : H1 → H2 → type_of% @AgrawalConjecture.agrawal_conjecture.variants.popovych := by
  intro h1 h2 n r hn hr hg
  dsimp only
  intro c1 c2
  exact h2 n r hn hr hg c1 c2 (h1 n r hn c2)

end OMA.R_AgrawalConjecture_agrawal_conjecture_variants_popovych_R1
