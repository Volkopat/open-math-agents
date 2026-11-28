import Mathlib

/-!
# A171775: smallest number that is a k-digit palindrome in some base, for all k = 2 .. n

Source: https://oeis.org/A171775
Credit: @gaudinfrederic

`a(n)` is the smallest number `M` such that there exist bases `b2, b3, ..., bn`
with the property that `M` written in base `bk` is a `k`-digit palindrome.

Conjecture (Max Alekseyev, in the comments of A171775): `a(n) = 2^((n-1)*(n-2))`
for `n >= 7`; the values `a(10) = 2^72` and `a(11) = 2^90` are confirmed there.

## Encoding

* "M written in base b is a k-digit palindrome" is
  `(Nat.digits b M).length = k ∧ List.Palindrome (Nat.digits b M)`;
  `Nat.digits b` is the standard base-b expansion (least significant digit
  first), so for `b ≥ 2` the length condition forces `b^(k-1) ≤ M < b^k`.
* Only bases `b ≥ 2` are allowed: `Nat.digits` is degenerate for `b < 2`.
* `a(n)` is `sInf` of the set of good `M`; `sInf ∅ = 0`, so a `0` value encodes
  "no such `M` exists".
-/

namespace OMA.S_oeis_a171775

/-- `M` is a `k`-digit palindrome when written in some base `b ≥ 2`. -/
def palInSomeBase (M k : ℕ) : Prop :=
  ∃ b : ℕ, 2 ≤ b ∧ (Nat.digits b M).length = k ∧ List.Palindrome (Nat.digits b M)

/-- Candidate set of A171775: `M` works for every `k` in `2 .. n`. -/
def goodSet (n : ℕ) : Set ℕ :=
  {M : ℕ | ∀ k ∈ Finset.Icc 2 n, palInSomeBase M k}

/-- OEIS conjecture on A171775: `a(n) = 2^((n-1)*(n-2))` for `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    sInf (goodSet n) = 2 ^ ((n - 1) * (n - 2)) := by
  sorry

end OMA.S_oeis_a171775
