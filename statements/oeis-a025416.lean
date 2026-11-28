import Mathlib

/-!
# A025416: Least sum of 4 nonzero squares in exactly n ways.

Source: https://oeis.org/A025416
Credit: @EmircanEsen

Conjecture (Jon Perry, Nov 03 2012): The sequence never becomes monotonic increasing.

Formalization notes:
* "Ways" are unordered: `r m` (A025428) counts the quadruples `1 ≤ a ≤ b ≤ c ≤ d` with
  `a² + b² + c² + d² = m`. For example `r 31 = 2` (`1+1+4+25`, `4+9+9+9`) and `r 28 = 3`.
* `a n` is the least `m` with `r m = n` (offset 0: `a 0 = 0`, `a 1 = 4`, `a 2 = 31`, `a 3 = 28`).
  These definitions reproduce the OEIS data.
* "Never becomes monotonic increasing" means: for every `N` there is an `n ≥ N` with
  `a (n+1) ≤ a n`. Distinct `n` have distinct `a n` (a number has only one value of `r`), so this
  is a strict descent `a (n+1) < a n`. To keep the junk value `sInf ∅ = 0` from making the
  statement true for free, the statement also requires that both terms really exist, i.e. that
  `n` and `n + 1` are values of `r`. If every term of the sequence exists (as the OEIS entry
  assumes), this is equivalent to the conjecture.
* Checked numerically: all terms with `n ≤ 497` exist, and among them there are 239 descents.
-/

namespace OMA.S_oeis_a025416

/-- A025428: the number of ways to write `m = a² + b² + c² + d²` with `1 ≤ a ≤ b ≤ c ≤ d`. -/
def r (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter
    (fun x : ℕ × ℕ × ℕ × ℕ =>
      x.1 ≤ x.2.1 ∧ x.2.1 ≤ x.2.2.1 ∧ x.2.2.1 ≤ x.2.2.2 ∧
        x.1 ^ 2 + x.2.1 ^ 2 + x.2.2.1 ^ 2 + x.2.2.2 ^ 2 = m)).card

/-- A025416: the least `m` that is a sum of 4 nonzero squares in exactly `n` ways. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | r m = n}

/-- The sequence has infinitely many (genuine) descents, so it never becomes increasing. -/
theorem main :
    ∀ N : ℕ, ∃ n ≥ N, (∃ m, r m = n) ∧ (∃ m, r m = n + 1) ∧ a (n + 1) < a n := by
  sorry

end OMA.S_oeis_a025416
