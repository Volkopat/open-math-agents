import Mathlib

/-!
# Lucas–Wieferich primes

Source: https://en.wikipedia.org/wiki/Lucas%E2%80%93Wieferich_prime
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: for integers `P` and `Q`, the Lucas sequence `U(P, Q)` is defined by `U_0 = 0`,
`U_1 = 1` and `U_{n+2} = P * U_{n+1} - Q * U_n`, with discriminant `D = P ^ 2 - 4 * Q`.  A prime
`p` is a **Lucas–Wieferich prime** associated with `(P, Q)` when `p` divides `U_{p - (D / p)}`,
where `(D / p)` is the Jacobi symbol.  The open question is whether, for any given integer `a > 0`,
there are infinitely many Lucas–Wieferich primes associated with the pair `(a, -1)`.  The case
`a = 1` gives the Fibonacci–Wieferich primes and `a = 2` the Pell–Wieferich primes.

So the proposition formalized below is: for every `a > 0` there are infinitely many primes `p`
dividing `U_{p - (a ^ 2 + 4 / p)}`, where `U` is the Lucas sequence of `(a, -1)`.
-/

namespace OMA.S_wp_lucas_wieferich_prime

-- definitions the statement needs (no sorry, no axiom)

/-- The **Lucas sequence** `U(a, -1)`: `U_0 = 0`, `U_1 = 1`, `U_{n+2} = a * U_{n+1} + U_n`. -/
def lucasU (a : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => a * lucasU a (n + 1) + lucasU a n

/-- The discriminant `D = a ^ 2 + 4` of the pair `(a, -1)`. -/
def lucasDiscriminant (a : ℤ) : ℤ :=
  a ^ 2 + 4

/-- `p` is a **Lucas–Wieferich prime** associated with `(a, -1)`: `p` is prime and divides the
Lucas term `U` at index `p - (D / p)`, where `(D / p)` is the Jacobi symbol. -/
def IsLucasWieferichPrime (a : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ (p : ℤ) ∣ lucasU a ((p : ℤ) - jacobiSym (lucasDiscriminant a) p).toNat

/-- Are there infinitely many Lucas–Wieferich primes for every `a > 0`? -/
theorem main : ∀ a : ℤ, 0 < a → {p : ℕ | IsLucasWieferichPrime a p}.Infinite := by
  sorry

end OMA.S_wp_lucas_wieferich_prime
