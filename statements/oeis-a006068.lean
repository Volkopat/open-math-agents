import Mathlib

/-!
# A006068: a(n) is Gray-coded into n

Source: https://oeis.org/A006068
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the inverse Gray code of `n`: the unique `m` with `m XOR (m >> 1) = n`. Conjecture
(Mikhail Kurkov, OEIS, 2023): `a(n) = a(A053645(A063946(n))) + A053644(n)` for `n > 0`, with
`a(0) = 0`.

## Encoding

* `a n` is defined by the prefix-XOR formula `a(n) = n ⊕ (n >> 1) ⊕ (n >> 2) ⊕ ⋯`, which is the
  inverse of the Gray code `m ↦ m ⊕ (m >> 1)` (values checked against the OEIS terms).
* A053644: the largest power of `2` that is `≤ n` (`0` for `n = 0`).
* A053645: `n` minus its leading binary digit, `n - A053644(n)`.
* A063946: complement the second binary digit from the left (`n ≥ 2`); `0 ↦ 0`, `1 ↦ 1`.
-/

namespace OMA.S_oeis_a006068

/-- Inverse Gray code: `n ⊕ (n >> 1) ⊕ ⋯ ⊕ (n >> log₂ n)`. -/
def a (n : ℕ) : ℕ :=
  (List.range (Nat.log 2 n + 1)).foldl (fun acc k => acc ^^^ (n >>> k)) 0

/-- A053644: largest power of two not exceeding `n` (`0` at `0`). -/
def A053644 (n : ℕ) : ℕ := if n = 0 then 0 else 2 ^ Nat.log 2 n

/-- A053645: `n` with its leading binary digit removed. -/
def A053645 (n : ℕ) : ℕ := n - A053644 n

/-- A063946: complement the second binary digit from the left. -/
def A063946 (n : ℕ) : ℕ := if n < 2 then n else n ^^^ 2 ^ (Nat.log 2 n - 1)

theorem main : ∀ n : ℕ, 0 < n → a n = a (A053645 (A063946 n)) + A053644 n := by
  sorry

end OMA.S_oeis_a006068
