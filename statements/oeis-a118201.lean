import Mathlib

/-!
# A118201: Smallest difference such that both difference and number do not occur previously.

Source: https://oeis.org/A118201
Credit: @gblacher2

Conjecture (comment in A118201): "every nonnegative integer occurs in this sequence."

The rule, as given in the formula section of A118201: "a(n+1) = a(n)-d or a(n)+d, where a(n+1)
must be positive and must not have occurred previously in the sequence; choose the smallest
positive d such that this is possible where d is not |a(m+1)-a(m)| for any m < n; if both
a(n)-d and a(n)+d have not occurred, choose a(n)-d." The sequence starts with a(0) = 0
(offset 0).

Conventions:
* the sequence is encoded as `a : ℕ → ℕ` with the source's offset 0, so `a 0 = 0`;
* "has not occurred previously" for a candidate value `v` at step `n` means `v ∉ {a 0, ..., a n}`;
* a step `d` is admissible at step `n` when `d > 0`, `d` is not one of the earlier differences
  `|a (m + 1) - a m|` with `m < n`, and either `a n - d` is a positive value that has not
  occurred (encoded as `d < a n` together with freshness of the natural-number difference
  `a n - d`) or `a n + d` has not occurred;
* `a (n + 1)` uses the least admissible `d` and equals `a n - d` when that option is available,
  else `a n + d`; the predicate `IsA118201` pins the sequence down uniquely, and the conjecture
  is stated for every sequence satisfying it;
* "every nonnegative integer occurs" means that every `k : ℕ` is a value of `a`.
-/

namespace OMA.S_oeis_a118201

/-- `v` has not occurred among `a 0, ..., a n`. -/
def Fresh (a : ℕ → ℕ) (n v : ℕ) : Prop :=
  ∀ i ≤ n, a i ≠ v

/-- `d` is one of the differences `|a (m + 1) - a m|` with `m < n`. -/
def UsedDiff (a : ℕ → ℕ) (n d : ℕ) : Prop :=
  ∃ m < n, d = Nat.dist (a (m + 1)) (a m)

/-- Going down by `d` from `a n` is allowed: the result `a n - d` is positive and new. -/
def DownOK (a : ℕ → ℕ) (n d : ℕ) : Prop :=
  d < a n ∧ Fresh a n (a n - d)

/-- `d` is an admissible difference at step `n`. -/
def Admissible (a : ℕ → ℕ) (n d : ℕ) : Prop :=
  0 < d ∧ ¬ UsedDiff a n d ∧ (DownOK a n d ∨ Fresh a n (a n + d))

/-- `a` is the sequence A118201: `a 0 = 0` and, for every `n`, `a (n + 1)` is obtained from
`a n` with the least admissible difference `d`, going down when possible and up otherwise. -/
def IsA118201 (a : ℕ → ℕ) : Prop :=
  a 0 = 0 ∧ ∀ n : ℕ, ∃ d : ℕ, IsLeast {e : ℕ | Admissible a n e} d ∧
    ((DownOK a n d ∧ a (n + 1) = a n - d) ∨ (¬ DownOK a n d ∧ a (n + 1) = a n + d))

/-- The conjecture: every nonnegative integer occurs in A118201. -/
theorem main : ∀ a : ℕ → ℕ, IsA118201 a → ∀ k : ℕ, k ∈ Set.range a := by
  sorry

end OMA.S_oeis_a118201
