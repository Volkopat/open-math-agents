import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Totient

/-!
# Eventual modular periods of A258903

The divisor sum is the coefficient formula on the original OEIS page.
A pair (d,e) with de=n indexes the term from exp(3*x^d) of degree n.
Peter Bala's conjecture, August 8, 2025: the eventual period modulo M
divides Euler's totient of M. https://oeis.org/A258903
-/

namespace OMA.S_oeis_a258903

def term (u v n : ℕ) (de : ℕ × ℕ) : ℕ :=
  u^de.1 * v^de.2 * n.factorial / (de.1.factorial * de.2.factorial)

def seq (u v n : ℕ) : ℕ :=
  if n = 0 then 1 else ∑ de ∈ n.divisorsAntidiagonal, term u v n de

theorem main : ∀ M : ℕ, 0 < M → ∃ N : ℕ, ∀ n ≥ N,
    seq 2 3 (n + M.totient) ≡ seq 2 3 n [MOD M] := by
  sorry

end OMA.S_oeis_a258903
