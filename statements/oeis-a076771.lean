import Mathlib

/-!
# A076771: Even numbers n representable as the sum of two non-coprime odd composites.

Source: https://oeis.org/A076771
Credit: @bnb9001

The OEIS entry states: it is conjectured that there is no N such that for all n > N, every even
number is represented (Charles R Greathouse IV notes that the conjecture is true, since 2p with
p prime is never a term).

A natural number is composite when it is greater than 1 and not prime. A number `n` is
represented when `n = a + b` for odd composites `a` and `b` that are not coprime. The
conjecture says that no threshold `N` makes every even `n > N` represented.
-/

namespace OMA.S_oeis_a076771

/-- `n` is the sum of two non-coprime odd composite numbers. -/
def IsRepresented (n : ℕ) : Prop :=
  ∃ a b : ℕ, Odd a ∧ 1 < a ∧ ¬ a.Prime ∧ Odd b ∧ 1 < b ∧ ¬ b.Prime ∧
    ¬ Nat.Coprime a b ∧ n = a + b

/-- There is no `N` such that every even `n > N` is a sum of two non-coprime odd composites. -/
theorem main : ¬ ∃ N : ℕ, ∀ n > N, Even n → IsRepresented n := by
  sorry

end OMA.S_oeis_a076771
