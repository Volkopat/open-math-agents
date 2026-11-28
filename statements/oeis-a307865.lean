import Mathlib

/-!
# A307865: a(n) is the number of natural bases b < 2n+1 such that b^n == -1 (mod 2n+1).

Source: https://oeis.org/A307865
Credit: @agchua

Comment line of A307865 (the entry is by Thomas Ordowski, May 02 2019):
  Conjecture: if 2n+1 is an absolute Euler pseudoprime, then a(n) = 0.
A307865 has offset 0. `a n` counts the bases b with 1 <= b <= 2n, as in the entry's
Mathematica and PARI programs (b runs over 1..2n), such that b^n = -1 in ZMod (2n+1).
An absolute Euler pseudoprime (A033181) is an odd composite number N such that
c^((N-1)/2) == +-1 (mod N) for every c coprime to N. `IsAbsEulerPsp N` says exactly this, with
composite meaning N > 1 and N not prime, and the congruence taken in ZMod N.
The claim is stated for every n >= 0.
-/

namespace OMA.S_oeis_a307865

/-- A307865(n): the number of bases 1 <= b <= 2n with b^n == -1 (mod 2n+1). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (2 * n)).filter (fun b : ℕ => ((b : ZMod (2 * n + 1)) ^ n = -1))).card

/-- N is an absolute Euler pseudoprime (A033181): an odd composite number such that
c^((N-1)/2) == +-1 (mod N) for every c coprime to N. -/
def IsAbsEulerPsp (N : ℕ) : Prop :=
  Odd N ∧ 1 < N ∧ ¬ N.Prime ∧
    ∀ c : ℕ, Nat.Coprime c N →
      ((c : ZMod N) ^ ((N - 1) / 2) = 1 ∨ (c : ZMod N) ^ ((N - 1) / 2) = -1)

/-- The conjecture: if 2n+1 is an absolute Euler pseudoprime, then a(n) = 0. -/
theorem main : ∀ n : ℕ, IsAbsEulerPsp (2 * n + 1) → a n = 0 := by
  sorry

end OMA.S_oeis_a307865
