import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# The Fibonacci triangle of A385590

Write the source index as i = t + 2. Block t contains the rows from F(i)
through F(i+1)-1. The zero-based row and column offsets are r and j, so
the actual row and column numbers are F(i)+r and j+1.

Source: https://oeis.org/A385590
Credit: @CubeJerry
-/

namespace OMA.S_oeis_a385590

open Finset

def start (t : ℕ) := (Nat.fib (t+1))^2 + t%2

def width (t r : ℕ) := Nat.fib (t+2) + r

def entry (t r j : ℕ) := start t + Nat.fib t*r + Nat.fib (t+1)*j

structure Cell where
  block : ℕ
  row : Fin (Nat.fib (block+1))
  column : Fin (width block row.val)

def value (x : Cell) := entry x.block x.row x.column

def rowSum (t r : ℕ) : ℤ := ∑ j ∈ range (width t r),
  (-1 : ℤ)^(j+1) * ((width t r-1).choose j : ℤ) * entry t r j

theorem main : ((∀ x : Cell, 0 < value x) ∧
    (∀ v : ℕ, 0 < v → ∃! x : Cell, value x = v)) ∧
    ∀ t r : ℕ, r < Nat.fib (t+1) → rowSum t r =
      if width t r < 3 then (-1 : ℤ)^(width t r) else 0 := by
  sorry

end OMA.S_oeis_a385590
