import Mathlib

/-!
# OEIS A077740: a(n) = A077739(n)/n

The quotient of Amarnath Murthy's sequence A077739: A077739(n) is the
smallest positive multiple m of n which begins and ends with the
decimal expansion of n and has digit sum n (zero when no such m
exists), and a(n) = A077739(n)/n is the exact integer quotient, since
A077739(n) is a multiple of n or zero. The conjectured zero indices of
a are exactly 11, 17, and 19. Positional digits in Mathlib are
little-endian, so the prefix condition checks the low digits of m and
the suffix condition checks its high digits. The two copies may
overlap.

Source: https://oeis.org/A077740
-/

namespace OMA.S_oeis_a077740

def qualifies (n m : ℕ) : Prop :=
  0 < m ∧ n ∣ m ∧
    (Nat.digits 10 n).IsPrefix (Nat.digits 10 m) ∧
    (Nat.digits 10 n).IsSuffix (Nat.digits 10 m) ∧
    (Nat.digits 10 m).sum = n

noncomputable def term739 (n : ℕ) : ℕ := sInf {m | qualifies n m}

noncomputable def a (n : ℕ) : ℕ := term739 n / n

theorem main : ∀ n : ℕ, 0 < n → (a n = 0 ↔ n = 11 ∨ n = 17 ∨ n = 19) := by
  sorry

end OMA.S_oeis_a077740
