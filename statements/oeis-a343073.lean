import Mathlib

/-!
# A343073: number of 0 < b < n such that b^^x ≡ 1 (mod n) has a solution (^^ is tetration).

Source: https://oeis.org/A343073
Credit: @avivorly

Tetration: b^^1 = b and b^^(x+1) = b^(b^^x). For n ≥ 2 (the entry's offset), a(n) is the number of
integers 0 < b < n such that b^^x ≡ 1 (mod n) for some x ≥ 1.

The entry (Bernat Pagès Vives, 2021) says: a(n) ≤ A000010(n) (Euler's totient), since gcd(b, n) = 1 is a
necessary condition. There is equality when n = 2 and n = 3. It is a conjecture that there are no more
equality cases. Stated here as: the set of n ≥ 2 with a(n) = φ(n) is exactly {2, 3}.
-/

namespace OMA.S_oeis_a343073

/-- Tetration: `tet b x = b^^x`, with `tet b 1 = b`, `tet b (x + 1) = b ^ tet b x` (and `tet b 0 = 1`). -/
def tet (b : ℕ) : ℕ → ℕ
  | 0 => 1
  | x + 1 => b ^ tet b x

/-- a(n): the number of integers `0 < b < n` such that `b^^x ≡ 1 (mod n)` for some `x ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  {b : ℕ | 0 < b ∧ b < n ∧ ∃ x : ℕ, 1 ≤ x ∧ tet b x ≡ 1 [MOD n]}.ncard

theorem main : {n : ℕ | 2 ≤ n ∧ a n = Nat.totient n} = {2, 3} := by
  sorry

end OMA.S_oeis_a343073
