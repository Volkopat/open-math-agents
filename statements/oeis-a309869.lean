import Mathlib

/-!
# A309869: a product-mod-sum recurrence, and the `n` with `a(n) = 5`

Source: https://oeis.org/A309869
Credit: @avivorly

Definition (OEIS %N, verbatim): Let b(0)=n, b(1)=n+1, b(2)=n+2, and
b(k)=(b(k-3)*b(k-2)*b(k-3)) mod (b(k-3)+b(k-2)+b(k-1)) for k>=3. Continue until either b(k)=0, in which case
a(n)=k, or the ordered triple [b(k-2),b(k-1),b(k)] has appeared before, in which case a(n)=-k. If neither of these
ever occur, then a(n)=0.

Claim (Robert Israel, Aug 21 2019, in %F, verbatim): a(26-6*(-1)^k+132*k)=5.  Conjecture: the only other n for
which a(n)=5 are 14 and 32.

Conventions:
- The product: the %N text repeats `b(k-3)`; we use `b(k-3)*b(k-2)*b(k-1)`, as the entry's example does
  (a(14)=5 because b(3)=(14*15*16) mod (14+15+16)=30, b(4)=(15*16*30) mod (15+16+30)=2, and
  b(5)=(16*30*2) mod (16+30+2)=0) and as its Maple program does. With this product the definition below reproduces
  the data for n = 1..40 (3, 50, 3, 3, 10, 3, 3, -17, ..., -1688, 3, 3; checked by evaluation); the literal %N
  product does not (it gives a(1) = -12, not 3).
- `b n k` is computed in `ℕ`. A modulus `0` never occurs before the stop: `b 0, b 1, b 2 ≥ 1`, and a zero sum
  would need `b (k-1) = 0`, which already stops at `k - 1`.
- The triples that have appeared before index `k` are those of consecutive terms ending at an earlier index:
  `(b (j-2), b (j-1), b j)` for `2 ≤ j < k`, the first being `(n, n+1, n+2)` (as in the Maple program).
- `Stop n k` holds when `k ≥ 3` and (`b n k = 0` or the triple at `k` appeared before). The stopping index is the
  least such `k`. If both tests hold at that `k`, the zero test wins and `a n = k` (the order of %N and of the Maple
  program); otherwise `a n = -k`. If no `k` stops, `a n = 0`.
- Offset 1: the claim is for `n ≥ 1`. The family is `n = 26 - 6*(-1)^k + 132*k` with `k` a natural number
  (k = 0, 1, 2, ... gives n = 20, 164, 284, ...); `main` states the printed formula and the conjecture together.
-/

namespace OMA.S_oeis_a309869

/-- `b n k`: `b n 0 = n`, `b n 1 = n + 1`, `b n 2 = n + 2`, and for `k ≥ 3`,
`b n k = (b n (k-3) * b n (k-2) * b n (k-1)) mod (b n (k-3) + b n (k-2) + b n (k-1))`. -/
def b (n : ℕ) : ℕ → ℕ
  | 0 => n
  | 1 => n + 1
  | 2 => n + 2
  | k + 3 => b n k * b n (k + 1) * b n (k + 2) % (b n k + b n (k + 1) + b n (k + 2))

/-- The sequence stops at `k` (with `k ≥ 3`): `b n k = 0`, or the ordered triple `(b n (k-2), b n (k-1), b n k)`
equals the triple `(b n (j-2), b n (j-1), b n j)` at some earlier index `2 ≤ j < k`. -/
def Stop (n k : ℕ) : Prop :=
  3 ≤ k ∧ (b n k = 0 ∨
    ∃ j, 2 ≤ j ∧ j < k ∧ (b n (j - 2), b n (j - 1), b n j) = (b n (k - 2), b n (k - 1), b n k))

/-- The stopping index: the least `k` with `Stop n k` (used only when such a `k` exists). -/
noncomputable def stopIdx (n : ℕ) : ℕ := sInf {k | Stop n k}

open Classical in
/-- A309869: `a n = k` if the stopping index `k` has `b n k = 0`, `a n = -k` if it stops by a repeated triple,
and `a n = 0` if it never stops. -/
noncomputable def a (n : ℕ) : ℤ :=
  if ∃ k, Stop n k then
    (if b n (stopIdx n) = 0 then (stopIdx n : ℤ) else -(stopIdx n : ℤ))
  else 0

/-- Israel's formula and conjecture: for `n ≥ 1`, `a(n) = 5` exactly for `n = 14`, `n = 32`, and
`n = 26 - 6*(-1)^k + 132*k`. -/
theorem main :
    ∀ n ≥ 1, a n = 5 ↔ (n = 14 ∨ n = 32 ∨ ∃ k : ℕ, (n : ℤ) = 26 - 6 * (-1) ^ k + 132 * k) := by
  sorry

end OMA.S_oeis_a309869
