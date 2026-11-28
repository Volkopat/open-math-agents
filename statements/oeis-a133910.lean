import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Order.Lattice.Nat

/-!
# A133910: Period numbers of A133900 divided by n^2

Source: https://oeis.org/A133910
Credit: @thtsben2

Ridouane Oudra conjectures that a(n) is divisible by n precisely when n belongs
to {1} ∪ A051283. The sequence has offset 1.

A133900 is the least positive period in m of binomial(m+n,n) modulo n.
A133910 divides that period by n². A051283 consists of n > 1 for which
the largest exact prime-power factor P of n satisfies P² < n.
-/

namespace OMA.S_oeis_a133910

/-- The least positive period of the sequence defining A133900. -/
noncomputable def period (n : ℕ) : ℕ :=
  sInf {t : ℕ | 0 < t ∧ ∀ m : ℕ, (m + t + n).choose n % n = (m + n).choose n % n}

/-- A133910. -/
noncomputable def a (n : ℕ) : ℕ :=
  period n / n ^ 2

/-- Membership in A051283, checking the square of every exact prime-power factor. -/
def inA051283 (n : ℕ) : Prop :=
  1 < n ∧ ∀ p e : ℕ, p.Prime → 0 < e → p ^ e ∣ n → ¬ p ^ (e + 1) ∣ n →
    (p ^ e) ^ 2 < n

theorem main : ∀ n : ℕ, 1 ≤ n → (n ∣ a n ↔ n = 1 ∨ inA051283 n) := by
  sorry

end OMA.S_oeis_a133910
