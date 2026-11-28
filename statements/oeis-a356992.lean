import Mathlib

/-!
# A356992: a(n) = n - b(n - b(n - b(n - b(n - b(n - b(n)))))) for n >= 2, where b(n) = A356988(n).

Source: https://oeis.org/A356992
Credit: @alexandreeberhardt

The entry says that a is slow (a(n+1) - a(n) is 0 or 1 for n >= 2), so its graph is a series of
plateaus joined by lines of slope 1. `main` states this (first clause) and then the conjectural
claims of the entry about these plateaus.

Reading choices.
* b = A356988 is given by b(1) = 1 and b(n) = n - b(b(n - b(b(b(n-1))))) for n >= 2. Rather than
  a recursive definition, `main` holds for every function `b` satisfying exactly these two
  equations. It is known that 1 <= b(n) <= n - 1 for n >= 2, so every index used by the recurrence
  lies between 1 and n - 1. Hence the equations determine b(n) for every n >= 1 (and such a `b`
  exists), the value b(0) is never used, and the truncated subtraction of ℕ never truncates, here
  and in the formula for a(n) with n >= 2.
* A plateau is a maximal run of at least two equal consecutive terms, see `IsPlateau`.
* The entry gives the plateau heights, starts and ends as lists read from left to right. `main`
  states that a is slow and then the sets of heights, starts and ends. Since a is slow, plateaus
  further to the right have larger heights, starts and ends, so each list is determined by its set
  of values. Slowness of n - a(n) follows from slowness of a.
* Kept: heights are the Lucas numbers L(k), k >= 3 (conjecturally); ends are A013655(k), k >= 3
  (conjecturally); starts are 5 and 2 F(k), k >= 5 (appears to be). The plateau lengths
  (appears to be: 2, then F(k), k >= 3) follow from the starts and ends, so they are not restated.
* Kept: n - a(n) has plateaus at Fibonacci heights. The Example section lists them as
  3, 5, 8, 13, 21, 34, ..., that is F(k) for k >= 4. It does not count the run of 1s at the very
  beginning (n = 2 to 5, before any line of slope 1), so `main` only counts the plateaus of
  n - a(n) that start after n = 2. Note that 2 = F(3) is not a plateau height.
* Left out: the claims on a(a(n)) and a(a(a(n))), which are vague (similar properties) and whose
  height lists contain typos (28 for 18, A000045 for the Lucas numbers).
-/

namespace OMA.S_oeis_a356992

/-- Lucas numbers A000032: L(0) = 2, L(1) = 1, L(k+2) = L(k) + L(k+1). -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | k + 2 => lucas k + lucas (k + 1)

/-- A013655(k) = F(k+1) + L(k): 3, 2, 5, 7, 12, 19, 31, ... -/
def a013655 (k : ℕ) : ℕ := Nat.fib (k + 1) + lucas k

/-- The sequence A356992, built from a function `b` playing the role of A356988 (used for n >= 2). -/
def a (b : ℕ → ℕ) (n : ℕ) : ℕ := n - b (n - b (n - b (n - b (n - b (n - b n)))))

/-- For a sequence `f` whose first index is `lo`, the terms f(s), ..., f(e) form a plateau:
at least two terms (s < e), all equal, and the run cannot be extended to the left (unless it
starts at the first index `lo`) nor to the right. -/
def IsPlateau (f : ℕ → ℕ) (lo s e : ℕ) : Prop :=
  lo ≤ s ∧ s < e ∧ (∀ i, s ≤ i → i ≤ e → f i = f s) ∧
    (lo < s → f (s - 1) ≠ f s) ∧ f (e + 1) ≠ f s

theorem main :
    ∀ b : ℕ → ℕ, b 1 = 1 →
      (∀ n, 2 ≤ n → b n = n - b (b (n - b (b (b (n - 1)))))) →
      -- a is slow: a(n+1) - a(n) is 0 or 1 for n >= 2
      (∀ n, 2 ≤ n → a b (n + 1) = a b n ∨ a b (n + 1) = a b n + 1) ∧
      -- plateau heights of a: the Lucas numbers L(k), k >= 3
      {h | ∃ s e, IsPlateau (a b) 2 s e ∧ a b s = h} = {h | ∃ k, 3 ≤ k ∧ h = lucas k} ∧
      -- plateau ends of a: A013655(k), k >= 3
      {e | ∃ s, IsPlateau (a b) 2 s e} = {e | ∃ k, 3 ≤ k ∧ e = a013655 k} ∧
      -- plateau starts of a: 5, then 2 F(k), k >= 5
      {s | ∃ e, IsPlateau (a b) 2 s e} = {s | s = 5 ∨ ∃ k, 5 ≤ k ∧ s = 2 * Nat.fib k} ∧
      -- plateau heights of n - a(n), not counting the initial run of 1s: F(k), k >= 4
      {h | ∃ s e, 2 < s ∧ IsPlateau (fun n => n - a b n) 2 s e ∧ s - a b s = h} =
        {h | ∃ k, 4 ≤ k ∧ h = Nat.fib k} := by
  sorry

end OMA.S_oeis_a356992
