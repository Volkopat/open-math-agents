import Mathlib

/-!
# A091338: a(n) = (3/n), where (k/n) is the Kronecker symbol

Source: https://oeis.org/A091338
Credit: @jagong-cmu

Formalizes the conjecture of A.H.M. Smeets (Aug 01 2018), offset 1:
a(n) = 0 if and only if (n mod 3 = 0),
a(n) = 1 if (n mod 12 = 1 or n mod 12 = 11 or n mod 48 = 4 or n mod 48 = 44),
a(n) = -1 if (n mod 12 = 5 or n mod 12 = 7 or n mod 48 = 20 or n mod 48 = 28),
a(2) = -1, a(12*n+10) = -a(12*n+2) and a(12*n+14) = a(12*n+10) for n >= 0,
a(24*n+8) = -a(12*n+4) and a(24*n+16) = -a(12*n+4) for n >= 0.

Conventions:
* Mathlib has the Jacobi symbol `jacobiSym a b` for odd `b`, but no Kronecker symbol. The
  Kronecker symbol `(a/n)` is defined here by its standard rules: `(a/1) = 1`; for odd `n` it
  is the Jacobi symbol; and `(a/2n) = (a/2)*(a/n)`, where `(a/2) = 0` for even `a`, `1` for
  `a = 1 or 7 (mod 8)` and `-1` for `a = 3 or 5 (mod 8)`. The value at `n = 0` (outside the
  OEIS offset) is the usual one, `1` for `a = 1 or -1` and `0` otherwise; it is never used.
* The offset is 1. The first three clauses are stated for every `n >= 1`. The other clauses
  are stated for every `n >= 0`, as in the conjecture.
* All the clauses are stated as one conjunction, exactly as in the OEIS text. Note: the last
  clause `a(24*n+16) = -a(12*n+4)` appears to fail already at `n = 0`, since
  `a(16) = (3/2)^4 = 1` and `a(4) = (3/2)^2 = 1`.
* Note for the reviewer: the conjecture is FALSE as written. Its last clause,
  `a(24*n+16) = -a(12*n+4)`, fails at `n = 0`: `a(16) = (3/2)^4 = 1` and `a(4) = (3/2)^2 = 1`,
  so `a(16) = 1` but `-a(4) = -1`. The OEIS data shows the same values. All the other clauses
  hold for `n < 2000`. The statement keeps the literal text, so the prepared Lean result for it
  is a disproof.
-/

namespace OMA.S_oeis_a091338

/-- The Kronecker symbol `(a/2)`. -/
def kron2 (a : ℤ) : ℤ :=
  if a % 2 = 0 then 0 else if a % 8 = 1 ∨ a % 8 = 7 then 1 else -1

/-- The Kronecker symbol `(a/n)` for `n : ℕ`. -/
def kronecker (a : ℤ) : ℕ → ℤ
  | 0 => if a = 1 ∨ a = -1 then 1 else 0
  | n + 1 =>
    if (n + 1) % 2 = 0 then kron2 a * kronecker a ((n + 1) / 2) else jacobiSym a (n + 1)
decreasing_by omega

/-- `a(n) = (3/n)`. -/
def a (n : ℕ) : ℤ := kronecker 3 n

/-- The conjecture of A.H.M. Smeets, all clauses together. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n = 0 ↔ n % 3 = 0)) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n % 12 = 1 ∨ n % 12 = 11 ∨ n % 48 = 4 ∨ n % 48 = 44) → a n = 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      (n % 12 = 5 ∨ n % 12 = 7 ∨ n % 48 = 20 ∨ n % 48 = 28) → a n = -1) ∧
    a 2 = -1 ∧
    (∀ n : ℕ, a (12 * n + 10) = -a (12 * n + 2)) ∧
    (∀ n : ℕ, a (12 * n + 14) = a (12 * n + 10)) ∧
    (∀ n : ℕ, a (24 * n + 8) = -a (12 * n + 4)) ∧
    (∀ n : ℕ, a (24 * n + 16) = -a (12 * n + 4)) := by
  sorry

end OMA.S_oeis_a091338
