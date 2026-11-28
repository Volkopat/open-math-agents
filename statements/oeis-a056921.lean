import Mathlib

/-!
# A056921: a(0) = 0, a(1) = 1, a(2*n) = n*a(2*n-1) + a(2*n-2), a(2*n+1) = a(2*n) + a(2*n-1).

Source: https://oeis.org/A056921
Credit: @mrsirrisrm

Conjecture (Davide Oliveri, Oct 03 2025): for n >= 1, a(n-1) is not divisible by n,
except at n = 5 (verified for n <= 10^7).

Range: the source says n >= 1, but at n = 1 the claim is trivially false, since 1 divides
every integer (here a(0) = 0). The statement below therefore starts at n = 2, which is
the only reading under which the conjecture can hold. The exception at n = 5 is real:
a(4) = 5. Reading the exception as an iff (n divides a(n-1) exactly when n = 5) matches
the source, which says that n = 5 is the only exception.
-/

namespace OMA.S_oeis_a056921

/-- A056921: a(0) = 0, a(1) = 1, a(2k) = k * a(2k-1) + a(2k-2), a(2k+1) = a(2k) + a(2k-1).
Written for m = n + 2 >= 2: if m is even then a(m) = (m/2) * a(m-1) + a(m-2),
otherwise a(m) = a(m-1) + a(m-2). First terms: 0, 1, 1, 2, 5, 7, 26, 33, 158, 191, 1113. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => if (n + 2) % 2 = 0 then ((n + 2) / 2) * a (n + 1) + a n else a (n + 1) + a n

/-- For every n >= 2, n divides a(n-1) if and only if n = 5. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (n ∣ a (n - 1) ↔ n = 5) := by
  sorry

end OMA.S_oeis_a056921
