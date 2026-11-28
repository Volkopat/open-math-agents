import Mathlib

/-!
# OEIS A262326: binary rectangles with every row and column divisible by three

For the term of index `n ≥ 1`, use `n+1` rows and three columns. The last bit
in each row or column is its least significant bit. For odd `n` the source
writes the exponent as `(n-3)/2+1`, which equals `(n-1)/2` in integers,
including at `n=1`.

Source: https://oeis.org/A262326. Conjectures by Colin Barker, March 20, 2018.
-/

namespace OMA.S_oeis_a262326

/-- The value of a binary word, with its last bit least significant. -/
def binaryValue : {h : ℕ} → (Fin h → Bool) → ℕ
  | 0, _ => 0
  | h+1, w => 2 * binaryValue (fun i : Fin h => w i.castSucc) +
      (if w (Fin.last h) then 1 else 0)

/-- A binary word of width three divisible by three. -/
abbrev Row := {r : Fin 3 → Bool // 3 ∣ binaryValue r}

/-- The number of binary rectangles satisfying both divisibility conditions. -/
def a (n : ℕ) : ℕ :=
  Fintype.card {r : Fin (n+1) → Row //
    ∀ j : Fin 3, 3 ∣ binaryValue (fun i => (r i).val j)}

/-- The ordinary generating series has coefficient zero at index zero. -/
def generatingSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else a n

open PowerSeries in
theorem main :
    (∀ n : ℕ, 1 ≤ n → n % 2 = 0 →
      a n = 2 * 3^(n/2-1) + 3^(n-1)) ∧
    (∀ n : ℕ, 1 ≤ n → n % 2 = 1 →
      a n = 2 * 3^((n-1)/2) + 3^(n-1)) ∧
    (1 - C 3 * X) * (1 - C 3 * X^2) * generatingSeries =
      X * (C 3 - C 4 * X - C 9 * X^2) := by
  sorry

end OMA.S_oeis_a262326
