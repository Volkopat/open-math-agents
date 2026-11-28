import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic

/-!
# Peter Bala's congruence for the ballot numbers A238977

Source: https://oeis.org/A238977. The entry counts ballot sequences of length
n having exactly two fixed points. Bala's published formula of October 2021,
a(n+3) = (I(n+3)-I(n))/3, defines the count here independently of his
congruence conjecture. The involution numbers I are A000085, with their
fixed-point/transposition recurrence. The first three entries are 0,0,1.
Source for the recurrence: https://oeis.org/A000085
Credit: @KoaOkano
-/

namespace OMA.S_oeis_a238977

def involutions : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n+2 => involutions (n+1) + (n+1)*involutions n

def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n+3 => (involutions (n+3)-involutions n)/3

theorem main : ∀ n : ℕ, 0 < n →
    (a (n+3) ≡ 1 [MOD n] ↔ n.Coprime 6) := by
  sorry

end OMA.S_oeis_a238977
