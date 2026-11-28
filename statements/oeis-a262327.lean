import Mathlib

/-!
# OEIS A262327: binary rectangles with every row and column divisible by three

For the term of index `n ≥ 1`, there are `n+1` rows and four columns.
The least significant bit is last in each row or column. The two formulas
are stated after clearing their denominators. The odd formula thus includes
the rational power `3^(-1)` in the source at `n=1`.

Source: https://oeis.org/A262327. Conjectures by Colin Barker, December 31, 2018.
-/

namespace OMA.S_oeis_a262327

/-- The value of a binary word, with its last bit least significant. -/
def binaryValue : {h : ℕ} → (Fin h → Bool) → ℕ
  | 0, _ => 0
  | h+1, w => 2 * binaryValue (fun i : Fin h => w i.castSucc) +
      (if w (Fin.last h) then 1 else 0)

/-- A binary word of width four divisible by three. -/
abbrev Row := {r : Fin 4 → Bool // 3 ∣ binaryValue r}

/-- The number of binary rectangles satisfying both divisibility conditions. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {r : Fin (n+1) → Row //
    ∀ j : Fin 4, 3 ∣ binaryValue (fun i => (r i).val j)}

/-- The ordinary generating series has coefficient zero at index zero. -/
def generatingSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else a n

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 →
      2 * a n = 3^(n-2) * (14 + 2^(n+2))) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 1 →
      6 * a n = 3^(n-1) * (28 + 2^(n+2))) ∧
    (1 - C 3 * X) * (1 + C 3 * X) * (1 - C 6 * X) * generatingSeries =
      C 3 * X * (C 2 - C 7 * X - C 18 * X^2) := by
  sorry

end OMA.S_oeis_a262327
