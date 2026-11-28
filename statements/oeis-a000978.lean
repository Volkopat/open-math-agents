import Mathlib

/-!
# OEIS A000978: Wagstaff primes, two conjectures

Source: https://oeis.org/A000978
`A000978` lists the odd primes `p` (here: the numbers `p`) such that `W(p) = (2^p + 1)/3` is
prime: 3, 5, 7, 11, 13, 17, 19, 23, 31, 43, …. The entry records two conjectures.

1. (Vrba–Reix test.) Let `p > 3` be prime, `N = 2^p + 1`, `W = N/3`, `S 0 = 3/2` and
   `S (i+1) = S i ^ 2 - 2`. Then `W` is prime iff `S (p-1) ≡ S 0 (mod W)`. Since `W ∣ N`, the
   recursion is reduced mod `W` directly, with `3/2 = 3 * 2⁻¹` in `ZMod W`.
2. (Ordowski.) `a 1 = 3` and, for `n > 0`, `a (n+1)` is the least odd `k` such that
   `lpf((2^k + 1)/3) > lpf((2^(a n) + 1)/3)`, where `lpf` is the least prime factor.
   Here `a` is A000978 indexed from `1` (`Nat.nth` of the defining predicate at `n - 1`), the
   least `k` is taken over odd `k ≥ 3`, so that
   `(2^k + 1)/3 > 1` and `lpf` is a prime.

`main` is the conjunction of the two conjectures.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a000978

/-- `W p = (2^p + 1)/3`. -/
def W (p : ℕ) : ℕ := (2 ^ p + 1) / 3

/-- The Vrba–Reix sequence in `ZMod m`: `S 0 = 3/2`, `S (i+1) = S i ^ 2 - 2`. -/
def S (m : ℕ) : ℕ → ZMod m
  | 0 => 3 * (2 : ZMod m)⁻¹
  | i + 1 => S m i ^ 2 - 2

/-- A000978 predicate: `p` is odd (so `3 ∣ 2^p + 1`) and `W p` is prime. -/
def IsWagstaffExp (p : ℕ) : Prop := Odd p ∧ (W p).Prime

/-- A000978, indexed from `1`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsWagstaffExp (n - 1)

theorem main :
    (∀ p : ℕ, p.Prime → 3 < p → ((W p).Prime ↔ S (W p) (p - 1) = S (W p) 0)) ∧
    (a 1 = 3 ∧ ∀ n : ℕ, 0 < n →
      IsLeast {k : ℕ | 3 ≤ k ∧ Odd k ∧ (W (a n)).minFac < (W k).minFac} (a (n + 1))) := by
  sorry

end OMA.S_oeis_a000978
