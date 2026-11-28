import Mathlib

/-!
# Products of prime counts in OEIS A262443

Zhi-Wei Sun conjectures that infinitely many indices satisfy the sequence's defining
equality with distinct smaller indices. He also conjectures that infinitely many
positive indices admit no such equality even when the two smaller indices may
coincide, and that the analogous equation for powers of degree at least three
has no solution in the stated range.

`Nat.primeCounting t` counts primes up to and including `t`.

Source: https://oeis.org/A262443 (OEIS Foundation, CC BY-SA 4.0).
Formalized by @Qwer2077.
-/

namespace OMA.S_oeis_a262443

open Nat (primeCounting)

theorem main :
    Set.Infinite {m : ℕ | ∃ j k : ℕ, 0 < j ∧ j < k ∧ k < m ∧
      primeCounting (m ^ 2) = primeCounting (j ^ 2) * primeCounting (k ^ 2)} ∧
    Set.Infinite {m : ℕ | 0 < m ∧ ¬ ∃ j k : ℕ, 0 < j ∧ j ≤ k ∧ k < m ∧
      primeCounting (m ^ 2) = primeCounting (j ^ 2) * primeCounting (k ^ 2)} ∧
    (∀ n : ℕ, 2 < n → ¬ ∃ x y z : ℕ, 0 < x ∧ x ≤ y ∧ y < z ∧
      primeCounting (x ^ n) * primeCounting (y ^ n) = primeCounting (z ^ n)) := by
  sorry

end OMA.S_oeis_a262443
