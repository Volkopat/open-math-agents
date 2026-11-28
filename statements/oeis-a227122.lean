import Mathlib

/-!
# A227122: Number of n X 3 0,1 arrays indicating 2 X 2 subblocks of some larger (n+1) X 4 binary array having a sum of zero, with rows and columns of the latter in lexicographically nondecreasing order.

Source: https://oeis.org/A227122 (OEIS Foundation, CC BY-SA 4.0)
Credit: @marcusbuffett

Entry A227122 (R. H. Hardin), offset 1.
Data: 4, 13, 33, 81, 202, 492, 1143, 2524, 5315, 10718, ...
Formula section:
  Empirical: a(n) = (1/362880)*n^9 + (31/60480)*n^7 + (13/17280)*n^5 + (5/12)*n^4 - (167659/90720)*n^3 + (43/12)*n^2 + (12407/1260)*n - 14 for n>2.
  Conjectures from Colin Barker, Sep 07 2018: (Start)
  G.f.: x*(4 - 27*x + 83*x^2 - 144*x^3 + 157*x^4 - 121*x^5 + 87*x^6 - 62*x^7 + 28*x^8 - x^9 - 4*x^10 + x^11) / (1 - x)^10.
  a(n) = 10*a(n-1) - 45*a(n-2) + 120*a(n-3) - 210*a(n-4) + 252*a(n-5) - 210*a(n-6) + 120*a(n-7) - 45*a(n-8) + 10*a(n-9) - a(n-10) for n>12.
  (End)

Formalization notes:
* A larger array is A : Fin (n + 1) → Fin 4 → Fin 2, with A i j the entry in row i and
  column j. A row is read from left to right and a column from top to bottom. `LexLE x y` is the
  lexicographic order on binary words of one length m: x = y, or x has 0 and y has 1 at the first
  position where they differ. It is stated as: at every position p before which x and y agree,
  x p ≤ y p. `Sorted A` says that the rows of A, from top to bottom, and the columns of A, from
  left to right, are in lexicographically nondecreasing order.
* For i < n and j < 3 the 2 X 2 subblock of A at (i, j) is w x / y z with w = A i j,
  x = A i (j + 1), y = A (i + 1) j, z = A (i + 1) (j + 1). `blk w x y z` is the property of the
  entry (a sum of zero).
  `ind A` is the n X 3 0,1 array whose entry (i, j) is 1 when the subblock of A at (i, j) has
  the property and 0 when it does not.
* a n is the number of distinct arrays ind A as A runs over the sorted (n+1) X 4 binary
  arrays (the image of the sorted arrays under ind): it counts indicator arrays, not larger arrays.
* This reading reproduces all 31 listed terms of the entry: checked by a subset-construction
  transfer evaluation of exactly this definition, and by brute force over all larger arrays for
  n = 1 to 3.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^10 = N(x) in
  Z[[x]], which is equivalent to the quotient form because 1 - x is a unit. The recurrence is
  stated in the integers for every n > 12, the range given in the entry.
* `main` is the conjunction of Barker's two conjectures; the empirical polynomial is not part of it.
-/

namespace OMA.S_oeis_a227122

open PowerSeries

/-- Lexicographic order on binary words of length m: at every position p before which x and y
agree, x p ≤ y p. -/
def LexLE {m : ℕ} (x y : Fin m → Fin 2) : Prop :=
  ∀ p : Fin m, (∀ i : Fin m, i < p → x i = y i) → x p ≤ y p

instance {m : ℕ} (x y : Fin m → Fin 2) : Decidable (LexLE x y) := by
  unfold LexLE; infer_instance

/-- The rows (top to bottom) and the columns (left to right) of the (n+1) X 4 array A are in
lexicographically nondecreasing order. -/
def Sorted {n : ℕ} (A : Fin (n + 1) → Fin 4 → Fin 2) : Prop :=
  (∀ i : Fin n, LexLE (A i.castSucc) (A i.succ)) ∧
    ∀ j : Fin 3, LexLE (fun i => A i j.castSucc) (fun i => A i j.succ)

instance {n : ℕ} (A : Fin (n + 1) → Fin 4 → Fin 2) : Decidable (Sorted A) := by
  unfold Sorted; infer_instance

/-- The 2 X 2 subblock w x / y z has a sum of zero. -/
def blk (w x y z : Fin 2) : Prop := w.val + x.val + y.val + z.val = 0

instance (w x y z : Fin 2) : Decidable (blk w x y z) := by
  unfold blk; infer_instance

/-- The n X 3 array indicating which 2 X 2 subblocks of A have the property. -/
def ind {n : ℕ} (A : Fin (n + 1) → Fin 4 → Fin 2) : Fin n → Fin 3 → Fin 2 :=
  fun i j => if blk (A i.castSucc j.castSucc) (A i.castSucc j.succ) (A i.succ j.castSucc)
    (A i.succ j.succ) then 1 else 0

/-- A227122(n): the number of n X 3 arrays indicating the subblocks with the property of some
sorted (n+1) X 4 binary array. -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ.filter fun A : Fin (n + 1) → Fin 4 → Fin 2 => Sorted A).image ind).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 10 =
      X * (4 - 27 * X + 83 * X ^ 2 - 144 * X ^ 3 + 157 * X ^ 4 - 121 * X ^ 5 + 87 * X ^ 6 - 62 * X ^ 7 + 28 * X ^ 8 - X ^ 9 - 4 * X ^ 10 + X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 10 * a (n - 1) - 45 * a (n - 2) + 120 * a (n - 3) - 210 * a (n - 4) + 252 * a (n - 5) - 210 * a (n - 6) + 120 * a (n - 7) - 45 * a (n - 8) + 10 * a (n - 9) - a (n - 10) := by
  sorry

end OMA.S_oeis_a227122
