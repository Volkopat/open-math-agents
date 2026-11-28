import Mathlib

/-!
# A396981: Conjectures 2 and 3 on the array built from A002024

Source: https://oeis.org/A396981
Credit: @avivorly

A396981 is the array read by ascending antidiagonals:
`A(n, k) = A(n, k-A002024(k)) + (n+A002024(k)-1) * A(n-1, k)` with `A(n, 0) = 0^n`, `A(0, k) = 1`.
Here `A002024` is `n` appearing `n` times: `1, 2, 2, 3, 3, 3, 4, ...`.

Conjectures (in the entry; `f(n) = A002024(n)`, as the entry defines it, and `A000217(j) = j(j+1)/2`):
- Conjecture 2: `A(n, k) = Sum_{j=1..k} A(n-1, j + f(j))` for `n > 0`.
- Conjecture 3: `Sum_{j=k..n} A(n-j, k + A000217(j)) = |Stirling1(n+1, k+1)|`.

This statement is the conjunction of Conjectures 2 and 3. The entry's Conjecture 1 is not part of it.

Conventions:
- `f k` is `A002024(k)` for `k ≥ 1`: the least `s` with `k ≤ s * (s + 1) / 2`. At `k = 0` this gives `f 0 = 0`;
  that value is never used, neither by the recursion (it applies `f` only at `k ≥ 1`) nor by Conjecture 2 (`j ≥ 1`).
- `A n k` is the array, by well-founded recursion on `(n, k)`: `A 0 k = 1`; `A (n + 1) 0 = 0` (the rule
  `A(n, 0) = 0^n` for `n ≥ 1`, while `A 0 0 = 1 = 0^0`); and for `k ≥ 1`,
  `A (n + 1) k = A (n + 1) (k - f k) + (n + f k) * A n k`, since `(n + 1) + f k - 1 = n + f k`.
  It terminates since `f k ≥ 1` for `k ≥ 1`.
- `A000217(j)` is written `j * (j + 1) / 2`.
- `|Stirling1(n, k)|` is Mathlib's `Nat.stirlingFirst n k`, the unsigned Stirling number of the first kind.
- Conjecture 2 is stated for all `n ≥ 1` and all `k ≥ 0` (at `k = 0` both sides are `0`). Conjecture 3 is stated
  for all `n, k ≥ 0`, as the entry gives no range; for `k > n` the sum is empty and `|Stirling1(n+1, k+1)| = 0`.
- `n - 1` and `n - j` are natural-number subtractions; they are exact where they occur (`n ≥ 1`, `j ≤ n`).
-/

namespace OMA.S_oeis_a396981

/-- `f k = A002024(k)` for `k ≥ 1`: the least `s` with `k ≤ s * (s + 1) / 2` (and `f 0 = 0`).
Such an `s` exists: `s = 2 * k` works. -/
def f (k : ℕ) : ℕ :=
  Nat.find (⟨2 * k, by
    have h : 2 * k * (2 * k + 1) = 2 * (k * (2 * k + 1)) := by ring
    rw [h, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
    nlinarith [Nat.zero_le (k * k)]⟩ : ∃ s : ℕ, k ≤ s * (s + 1) / 2)

/-- The array A396981: `A 0 k = 1`, `A (n + 1) 0 = 0`, and for `k ≥ 1`,
`A (n + 1) k = A (n + 1) (k - f k) + (n + f k) * A n k`. -/
def A : ℕ → ℕ → ℕ
  | 0, _ => 1
  | _ + 1, 0 => 0
  | n + 1, k + 1 => A (n + 1) (k + 1 - f (k + 1)) + (n + f (k + 1)) * A n (k + 1)
termination_by n k => (n, k)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right
       apply Nat.sub_lt (Nat.succ_pos _)
       unfold f
       exact (Nat.find_pos _).2 (by simp))
    | (apply Prod.Lex.left; omega)

theorem main :
    (∀ n k : ℕ, 1 ≤ n → A n k = ∑ j ∈ Finset.Icc 1 k, A (n - 1) (j + f j)) ∧
    (∀ n k : ℕ, ∑ j ∈ Finset.Icc k n, A (n - j) (k + j * (j + 1) / 2) =
      Nat.stirlingFirst (n + 1) (k + 1)) := by
  sorry

end OMA.S_oeis_a396981
