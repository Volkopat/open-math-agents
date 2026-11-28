import Mathlib

/-!
# A286667: Positions of 1 in A286665; complement of A286666.

Source: https://oeis.org/A286667
Credit: @rickmanelius

Conjecture (in the entry by Clark Kimberling, May 13 2017; the comment is unsigned):
a(n)/n -> 1 + sqrt(1/2). (Michel Dekking, Mar 11 2018: This conjecture follows easily from the
fact that (a(n)) is a Beatty sequence, see my comments in A286665.)

Formalization notes:
* A171588, the Pell word, is the fixed point of the morphism 0 -> 001, 1 -> 0. It is the limit
  of the words S(0) = 0, S(k+1) = image of S(k) under the morphism (`pellIter`). The function
  `pellMorph` sends every letter other than 0 to the word 0; only the letters 0 and 1 occur.
  S(k) is a prefix of S(k+1), and S(k) has length at least k + 1 (lengths 1, 3, 7, 17, 41, ...).
* A286665 is the {0->01}-transform of the Pell word: every 0 is replaced by 0, 1 and every 1 is
  kept (`psi`, the morphism psi_8 of Dekking's comment). The transform of S(k) is a prefix of the
  transform of S(k+1) and has length at least k + 1, so letter i (counting from 0) of A286665 is
  letter i of the transform of S(i+1). `w i` is that letter, which is term i + 1 of A286665
  (offset 1). Its values 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, ... match the data of A286665.
* A286667(n), for n ≥ 1, is the position of the n-th 1 in A286665, with positions counted from 1
  as in the entry (1 is in positions 2, 4, 5, 7, 9, ...). `Nat.nth (fun i => w i = 1) (n - 1)` is
  the n-th index i with w i = 1, counting indices from 0 (`Nat.nth` starts at 0), so `a n` adds 1.
  The values a(1), a(2), ... are 2, 4, 5, 7, 9, 10, 12, 14, 16, 17, ..., matching the data.
* `a 0` is a junk value (it equals a(1)); it does not affect the limit. The ratio a(n)/n is taken
  in the reals and sqrt is `Real.sqrt`.
* The comment begins with the remark a(n) - a(n-1) is in {2,3} for n>=2, before the word
  Conjecture. The remark is not part of the conjecture and is not stated. It is copied from
  A286666, where it holds; for this sequence the differences are 1 and 2 (2, 4, 5, 7, 9, ...).
-/

namespace OMA.S_oeis_a286667

/-- The Pell morphism 0 -> 001, 1 -> 0 (every letter other than 0 goes to 0). -/
def pellMorph : ℕ → List ℕ
  | 0 => [0, 0, 1]
  | _ => [0]

/-- S(0) = 0 and S(k+1) = image of S(k) under the Pell morphism; the Pell word is their limit. -/
def pellIter : ℕ → List ℕ
  | 0 => [0]
  | k + 1 => (pellIter k).flatMap pellMorph

/-- The {0->01}-transform letter by letter: 0 -> 01, 1 -> 1. -/
def psi : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [1]

/-- The {0->01}-transform of S(k); A286665 is the limit of these words. -/
def wIter (k : ℕ) : List ℕ := (pellIter k).flatMap psi

/-- A286665 counted from 0: `w i` is term i + 1 of A286665. -/
def w (i : ℕ) : ℕ := (wIter (i + 1)).getD i 0

/-- A286667(n) for n ≥ 1: the position, counted from 1, of the n-th 1 in A286665. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => w i = 1) (n - 1) + 1

/-- The conjecture: a(n)/n tends to 1 + sqrt(1/2). -/
theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / n) Filter.atTop (nhds (1 + Real.sqrt (1 / 2))) := by
  sorry

end OMA.S_oeis_a286667
