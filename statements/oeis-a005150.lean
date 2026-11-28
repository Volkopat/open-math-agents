import Mathlib

/-!
# A005150: Look and Say sequence: describe the previous term! (method A - initial term is 1)

Source: https://oeis.org/A005150
Credit: @jrflga (agent: Claude Code, model claude-fable-5-2)

The OEIS entry (offset 1, `a(1) = 1`, then `11, 21, 1211, 111221, 312211, 13112221, ...`) records
two conjectures in its formula section:

* Bill McEachen, May 09 2025: Conjecture: `DC(a(n)) ~ k * (Conway's constant)^n` where `k` is
  approximately `1.021...` and `DC` denotes the number of digit changes in the decimal
  representation of n (e.g., `DC(13112221)=4` because `1->3, 3-1, 1->2, 2->1`).
  (Quoted as written; `3-1` is the change `3->1`.)
* Ya-Ping Lu, Jun 05 2025: Conjecture: `lim_{n->infinity} (c2+c3-c1)/(c1+c2+c3) = 0.01`
  approximately, where `ci` is the number of appearances of `i` in `a(n)`.

`main` is the conjunction of the two conjectures.

## Encoding

* `runs l` is the run-length encoding of a list of digits (most significant digit first): the
  list of pairs `(length of the run, repeated digit)`, in order.
* `describe l` reads the runs aloud: each run `(c, d)` becomes the decimal digits of `c` followed
  by `d`. `say m` applies this to the decimal representation of the natural number `m`.
* `a n` is the OEIS term `a(n)` for `n ≥ 1` (so `a 1 = 1`, `a 2 = 11`, `a 3 = 21`,
  `a 4 = 1211`); `a 0 = 1` is a junk value that no statement below depends on, since both
  conjectures are about `n → ∞`.
* `DC m` counts the adjacent pairs of decimal digits of `m` that differ; `DC 13112221 = 4`.
* `c i m` is the number of appearances of the digit `i` in the decimal representation of `m`,
  and `len m` is the number of decimal digits of `m`.
* Conway's constant is the growth rate of the number of digits of the terms: `lam` is pinned
  down as the limit of `len (a (n + 1)) / len (a n)`. No numerical value or polynomial is used.
* `~` is asymptotic equivalence as `n → ∞` (`Asymptotics.IsEquivalent` along `Filter.atTop`).
* The two approximate constants are read as the decimal digits the entry displays:
  `k` is approximately `1.021...` means `1.021 ≤ k < 1.022`; the limit `L` equals `0.01`
  approximately means that it exists and rounds to `0.01`, that is `0.005 ≤ L < 0.015`.
  (Numerical evidence, not a proof: for `49 ≤ n ≤ 60`, `DC(a(n)) / lam^n` stays between
  `1.0209` and `1.0213`, and the ratio of the second conjecture between `0.0095` and `0.0100`.)
-/

namespace OMA.S_oeis_a005150

/-- Run-length encoding of a list of digits: the pairs `(length of the run, repeated digit)`. -/
def runs : List ℕ → List (ℕ × ℕ)
  | [] => []
  | d :: l =>
    match runs l with
    | [] => [(1, d)]
    | (c, e) :: r => if d = e then (c + 1, e) :: r else (1, d) :: (c, e) :: r

/-- Read a list of digits aloud (most significant digit first): for each run, the decimal
digits of its length, then the repeated digit. -/
def describe (l : List ℕ) : List ℕ :=
  (runs l).flatMap fun p => (Nat.digits 10 p.1).reverse ++ [p.2]

/-- The look-and-say description of the decimal representation of `m`. -/
def say (m : ℕ) : ℕ :=
  Nat.ofDigits 10 (describe (Nat.digits 10 m).reverse).reverse

/-- The OEIS term `a(n)` for `n ≥ 1`: `a 1 = 1` and `a (n + 1) = say (a n)`. -/
def a (n : ℕ) : ℕ := say^[n - 1] 1

/-- The number of digit changes in the decimal representation of `m`. -/
def DC (m : ℕ) : ℕ :=
  ((Nat.digits 10 m).zip (Nat.digits 10 m).tail).countP fun p => p.1 != p.2

/-- The number of appearances of the digit `i` in the decimal representation of `m`. -/
def c (i m : ℕ) : ℕ := (Nat.digits 10 m).count i

/-- The number of decimal digits of `m`. -/
def len (m : ℕ) : ℕ := (Nat.digits 10 m).length

theorem main :
    ∃ lam k L : ℝ,
      Filter.Tendsto (fun n : ℕ => (len (a (n + 1)) : ℝ) / (len (a n) : ℝ))
        Filter.atTop (nhds lam) ∧
      (1.021 : ℝ) ≤ k ∧ k < (1.022 : ℝ) ∧
      Asymptotics.IsEquivalent Filter.atTop
        (fun n : ℕ => (DC (a n) : ℝ)) (fun n : ℕ => k * lam ^ n) ∧
      Filter.Tendsto
        (fun n : ℕ =>
          ((c 2 (a n) : ℝ) + (c 3 (a n) : ℝ) - (c 1 (a n) : ℝ)) /
            ((c 1 (a n) : ℝ) + (c 2 (a n) : ℝ) + (c 3 (a n) : ℝ)))
        Filter.atTop (nhds L) ∧
      (0.005 : ℝ) ≤ L ∧ L < (0.015 : ℝ) := by
  sorry

end OMA.S_oeis_a005150
