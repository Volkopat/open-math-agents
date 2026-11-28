import Mathlib

/-!
# A121627: Real part of a complex operation analogous to the factorials.

Source: https://oeis.org/A121627
Credit: @agchua

Definition (formula line of the entry): Let a(1) = 1, real part of (1 + i) = k(1); then
k(n) = (n + ni) * k(n-1), n>1. a(n) = real part of each k(n).
Here k is computed in the Gaussian integers. The start value k 0 = 1 gives k 1 = (1 + i) * 1 = 1 + i,
so k n = n! * (1 + i)^n and a n is its real part. The offset is 1 (data 1, 0, -12, -96, -480, 0, ...).

Conjectures of the entry (Gary W. Adamson, Aug 12 2006), verbatim:
  Conjecture (1): Current nonzero term divides next nonzero term; as an operation, getting a new
  sequence: 12, 8, 5, 84, 16, 9, 220, 24, 13, ...; using unsigned terms).
  Conjecture (2): If the term in (12, 8, 5, ...) is generated from a(n)/a(n-1) or a(n)/a(n-2),
  then n divides each (12, 8, 5, ...).
Formalised: if 1 <= n < m, a(n) and a(m) are nonzero and a(j) = 0 for every j with n < j < m
(so a(m) is the next nonzero term after a(n)), then a(n) divides a(m) (Conjecture 1), and m
divides the quotient a(m)/a(n) (Conjecture 2). Divisibility does not depend on signs, so the
unsigned terms give the same claims.
-/

namespace OMA.S_oeis_a121627

/-- k 0 = 1 and k (n + 1) = ((n + 1) + (n + 1) i) * k n in the Gaussian integers. -/
noncomputable def k : ℕ → GaussianInt
  | 0 => 1
  | n + 1 => (⟨(n : ℤ) + 1, (n : ℤ) + 1⟩ : GaussianInt) * k n

/-- A121627(n): the real part of k n. -/
noncomputable def a (n : ℕ) : ℤ := (k n).re

/-- Conjectures (1) and (2): if a(m) is the next nonzero term after the nonzero term a(n),
then a(n) divides a(m) and m divides a(m)/a(n). -/
theorem main : ∀ n m : ℕ, 1 ≤ n → n < m → a n ≠ 0 → a m ≠ 0 →
    (∀ j : ℕ, n < j → j < m → a j = 0) → a n ∣ a m ∧ (m : ℤ) ∣ a m / a n := by
  sorry

end OMA.S_oeis_a121627
