import OMAStatements.S_oeis_a079390
import Mathlib

/-! With `a(n) = lpf(n) lpf(n+1) lpf(n+2)`, the OEIS A079390 conjecture says that for `n > 2`
the value `a(n)` is a record exactly when `n, n + 2` are twin primes. Two parts are classical:
a twin prime pair gives `a(n) = 2n(n + 2)`, which beats every earlier value (an earlier odd
`m` has `a(m) ≤ 2m(m + 2)`, an earlier even `m` has `a(m) ≤ 4(m + 1)`); and an even `n > 2`
is never a record, since `a(n - 1) ≥ 3 · 2 · lpf(n + 1) > 4 lpf(n + 1) = a(n)`. The open rest
is that an odd record position starts a twin prime pair; it would need twin primes in short
intervals. -/

namespace OMA.R_oeis_a079390_R1

open OMA.S_oeis_a079390

/-- The classical parts: twin primes give records, and records sit at odd `n`. -/
def H1 : Prop :=
  ∀ n : ℕ, 2 < n →
    ((n.Prime ∧ (n + 2).Prime) → ∀ m, 1 ≤ m → m < n → a m < a n) ∧
    ((∀ m, 1 ≤ m → m < n → a m < a n) → n % 2 = 1)

/-- The open rest: an odd record position starts a twin prime pair. -/
def H2 : Prop :=
  ∀ n : ℕ, 2 < n → n % 2 = 1 → (∀ m, 1 ≤ m → m < n → a m < a n) →
    n.Prime ∧ (n + 2).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a079390.main := by
  intro h1 h2 n hn
  exact ⟨fun h => h2 n hn ((h1 n hn).2 h) h, (h1 n hn).1⟩

end OMA.R_oeis_a079390_R1
