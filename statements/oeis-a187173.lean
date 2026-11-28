import Mathlib

/-!
# A187173: 3-step left-handed knight tours on an n×n board

Source: https://oeis.org/A187173
Credit: @mbilenko03

A left-handed knight moves by one of `(2, 1)`, `(-1, 2)`, `(-2, -1)`, `(1, -2)`.
In the triangle A187172 an `n`-step tour is a self-avoiding walk through `n` squares,
so a 3-step tour uses two moves. The 4×4 illustrations mark those three squares
`1`, `2`, `3` (the zeros are empty). `a n` counts the tours on an `n × n` board,
summed over starting squares, and `a 0 = 0`.

Conjectures recorded in the entry: `a n = 12 n^2 - 64 n + 80` for `n > 3`, and
`4 x^4 (4 - x) (1 + x) / (1 - x)^3` as the generating function.
-/

namespace OMA.S_oeis_a187173

/-- The four left-handed knight steps, indexed in cyclic order. -/
def steps (i : Fin 4) : ℤ × ℤ :=
  match i.val with
  | 0 => (2, 1)
  | 1 => (-1, 2)
  | 2 => (-2, -1)
  | _ => (1, -2)

/-- Embed a move index into the three squares of the walk. -/
def here (i : Fin 2) : Fin 3 :=
  ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

/-- The square reached by move `i`. -/
def nxt (i : Fin 2) : Fin 3 :=
  ⟨i.val + 1, Nat.add_lt_add_right i.isLt 1⟩

/-- Integer displacement of move `i`. -/
def delta {n : ℕ} (p : Fin 3 → Fin n × Fin n) (i : Fin 2) : ℤ × ℤ :=
  ( ((p (nxt i)).1.val : ℤ) - ((p (here i)).1.val : ℤ)
  , ((p (nxt i)).2.val : ℤ) - ((p (here i)).2.val : ℤ) )

/-- `d` is one of the four left-handed steps. -/
def IsStep (d : ℤ × ℤ) : Prop :=
  d = steps 0 ∨ d = steps 1 ∨ d = steps 2 ∨ d = steps 3

/-- A 3-step left-handed knight tour: three distinct squares and two steps from `steps`. -/
def Tour (n : ℕ) : Type :=
  { p : Fin 3 → Fin n × Fin n // Function.Injective p ∧ ∀ i : Fin 2, IsStep (delta p i) }

/-- `a n` is the number of such tours. `a 0 = 0`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card (Tour n)

open PowerSeries in
/-- Barker's generating function, cleared of `(1 - X)^3`, and the closed form for `n > 3`. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) * (1 - X) ^ 3 =
      4 * X ^ 4 * (4 - X) * (1 + X) ∧
      ∀ n : ℕ, 3 < n → (a n : ℤ) = 12 * (n : ℤ) ^ 2 - 64 * (n : ℤ) + 80 := by
  sorry

end OMA.S_oeis_a187173
