import Mathlib

/-!
# A082447: a(n) = the number k such that s(k)=0 where s(0)=n and s(i)=s(i-1)-(s(i-1) modulo (i+1)).

Source: https://oeis.org/A082447
Credit: @gblacher2

Conjecture (formula section of A082447): "a(n) = sqrt(Pi*n) + O(1)".

The sequence has offset 1. For `n ≥ 1` the numbers `s(i)` never increase, and once `s(i) = 0`
every later term is `0`, so "the number k such that s(k)=0" is read as the least such `k`.
This matches the name, the data section (1, 2, 2, 3, 3, 4, 4, 4, 4, 5, ...) and the PARI program
of the entry. The first example of the entry adds an extra step modulo 1 and writes a(4) = 4;
the name and the data give a(4) = 3, which we follow.

"a(n) = sqrt(Pi*n) + O(1)" is read in the standard way, as `n → ∞`:
`a(n) - sqrt(π n)` is bounded.
-/

namespace OMA.S_oeis_a082447

/-- `s n i`: `s(0) = n` and `s(i) = s(i-1) - (s(i-1) mod (i+1))` for `i ≥ 1`. -/
def s (n : ℕ) : ℕ → ℕ
  | 0 => n
  | i + 1 => s n i - s n i % (i + 2)

/-- A082447(n): the least `k` with `s(k) = 0`, where `s(0) = n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {k : ℕ | s n k = 0}

/-- Cloitre's conjecture: `a(n) = sqrt(π n) + O(1)`. -/
theorem main :
    (fun n : ℕ => (a n : ℝ) - Real.sqrt (Real.pi * n)) =O[Filter.atTop] (fun _ => (1 : ℝ)) := by
  sorry

end OMA.S_oeis_a082447
