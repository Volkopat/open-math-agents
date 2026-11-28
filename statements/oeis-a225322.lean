import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# A225322: Infinitely many lucky numbers are composite prime powers

Source: https://oeis.org/A225322 (Alex Ratushnyak)
Credit: @Alienchisel

A225322 intersects the lucky numbers A000959 with A025475, which contains 1
and prime powers with exponent at least 2. The inclusion of 1 is retained.

The lucky sieve acts by position. Restricting the starting list to a finite
initial interval preserves positions of its surviving entries at every pass.
If the next stride is outside that prefix, it and all later strides exceed
the length of the prefix, so no more entries in the prefix can be removed.
-/

namespace OMA.S_oeis_a225322

/-- Continue the lucky sieve from the given zero-based index of the next stride. -/
def sieve : ℕ → ℕ → List ℕ → List ℕ
  | 0, _, remaining => remaining
  | fuel + 1, index, remaining =>
    match remaining[index]? with
    | none => remaining
    | some stride =>
      let kept := (remaining.zipIdx 1).filterMap fun (n, position) =>
        if position % stride = 0 then none else some n
      sieve fuel (index + 1) kept

/-- Remove the even numbers first, then take the second survivor as the next stride. -/
def luckyUpTo (limit : ℕ) : List ℕ :=
  let odds := ((List.range limit).map Nat.succ).filter fun n => n % 2 == 1
  sieve limit 1 odds

theorem main : Set.Infinite
    {n : ℕ | n ∈ luckyUpTo n ∧ (n = 1 ∨ ∃ p e : ℕ, p.Prime ∧ 2 ≤ e ∧ n = p ^ e)} := by
  sorry

end OMA.S_oeis_a225322
