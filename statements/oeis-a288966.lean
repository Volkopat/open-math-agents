import Mathlib

/-!
# A288966: number of iterations the HyperbolaTiles algorithm takes to factorize n

Source: https://oeis.org/A288966 (conjecture by Ridouane Oudra, Mar 12 2024)

Conjecture: a(n) = n + A020639(n) - A032742(n) - 1, for n > 1.

Conventions:
* The algorithm is the Java program of the entry, transcribed literally. Its variables are
  i, x, y, p, q (integers), initially i = x = y = p = 0 and q = n, and the loop is
    do { i++;
         if (y < 0) { x = y + q; q--; }
         if (y > 0) { p++; x = y - p; }
         if (y == 0) { p++; x = 0; if ((p != 1) || (q == 1)) { output; break; } q--; }
         y = x + p - q;
    } while (q > 0);
  The three tests read the same value of y (y is only reassigned at the end of the body), so
  exactly one branch runs. `body n s` performs one pass of the loop body on the state
  s = (x, y, p, q) at the loop head and returns `none` when the pass executes `break`.
  `run n k` is the state at the loop head after k passes, or `none` once the loop has
  stopped (by `break`, or because the condition q > 0 failed).
* a(n) is the number of iterations, i.e. the value of i when the loop breaks: the least
  i >= 1 such that the loop is still running after i - 1 passes and the i-th pass breaks.
* A020639(n) is the least prime factor `Nat.minFac n`, and A032742(n) = n / A020639(n) is the
  largest proper divisor of n. The statement is for n > 1; natural-number subtraction is
  harmless since n + A020639(n) > A032742(n).
-/

namespace OMA.S_oeis_a288966

/-- One pass of the loop body on the state (x, y, p, q); `none` means `break`. -/
def body (s : ℤ × ℤ × ℤ × ℤ) : Option (ℤ × ℤ × ℤ × ℤ) :=
  match s with
  | (_, y, p, q) =>
    if y < 0 then some (y + q, (y + q) + p - (q - 1), p, q - 1)
    else if 0 < y then some (y - (p + 1), (y - (p + 1)) + (p + 1) - q, p + 1, q)
    else if p + 1 ≠ 1 ∨ q = 1 then none
    else some (0, 0 + (p + 1) - (q - 1), p + 1, q - 1)

/-- The state at the loop head after k passes, or `none` once the loop has stopped. -/
def run (n : ℕ) : ℕ → Option (ℤ × ℤ × ℤ × ℤ)
  | 0 => some (0, 0, 0, (n : ℤ))
  | k + 1 =>
    match run n k with
    | none => none
    | some s =>
      match body s with
      | none => none
      | some s' => if 0 < s'.2.2.2 then some s' else none

/-- The i-th pass of the loop executes `break`. -/
def Breaks (n i : ℕ) : Prop := 1 ≤ i ∧ ∃ s, run n (i - 1) = some s ∧ body s = none

/-- A288966(n): the number of iterations of the HyperbolaTiles algorithm on n. -/
noncomputable def a (n : ℕ) : ℕ := sInf {i : ℕ | Breaks n i}

theorem main : ∀ n : ℕ, 1 < n → a n = n + Nat.minFac n - n / Nat.minFac n - 1 := by
  sorry

end OMA.S_oeis_a288966
