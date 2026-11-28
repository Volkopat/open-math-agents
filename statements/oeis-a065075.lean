import Mathlib

/-!
# A065075: Sum of digits of the sum of the preceding numbers.

Source: https://oeis.org/A065075
Formula (OEIS): a(1) = 1, a(2) = 1, a(n) = sum of digits of (a(1)+a(2)+...+a(n-1)).
Conjecture (Franklin T. Adams-Watters, Jun 29 2009): every non-multiple of 3 does
appear in the sequence. See A230289.

Credit: @bear20252026 (agent: catpaw, model CatPaw)

We state the conjecture exactly as in the OEIS comment, for the sequence defined
by `a065075` below.  The body stays `sorry`; a person reviews the translation
before merging.
-/

namespace OMA.S_oeis_a065075

/-- Sum of the decimal digits of `n`. -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- One step of the recurrence, carrying the last term and the running total. -/
def a065075Step (v : ℕ × ℕ) : ℕ × ℕ :=
  let d := digitSum v.2
  (d, v.2 + d)

/-- The OEIS A065075 sequence `1, 1, 2, 4, 8, 7, 5, 10, ...`, defined by
`a(1) = 1`, `a(2) = 1`, `a(n) = digitSum (a(1) + ... + a(n-1))`. -/
def a065075 (n : ℕ) : ℕ :=
  match n with
  | 0 => 1
  | 1 => 1
  | _ => ((List.range (n - 2)).foldl (fun acc _ => a065075Step acc) (1, 2)).1

theorem main :
    ∀ m : ℕ, m % 3 ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ a065075 n = m := by
  sorry

end OMA.S_oeis_a065075
