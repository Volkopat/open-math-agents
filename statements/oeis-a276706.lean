import Mathlib

/-!
# A276706: indices of records in A249860

Source: https://oeis.org/A276706 (conjectures in the entry)

Entry (offset 1): Indices of records in A249860, where A249860(n) = lcm(n + 3, n - 3) for
n >= 1 (offset 1).
Formula section, Conjectures:
a(n) = a(n-1)+a(n-2)-a(n-3) for n>3.
a(n) = (6*n-27-(-1)^n)/2 for n>6.
G.f.: x*(1+x+x^2-x^4+x^7+3*x^8) / ((1-x)^2*(1+x)).

Formalization notes:
* lcm is taken of absolute values, as in the entry's PARI programs (so A249860(1) = lcm(4, 2) = 4
  and A249860(3) = lcm(6, 0) = 0).
* As in the entry's PARI program (which starts with record value 0 and uses a strict
  comparison), an index n >= 1 is a record index when A249860(n) is positive and larger than
  A249860(j) for every 1 <= j < n. a(n) is the n-th record index, i.e. `Nat.nth` at `n - 1`.
  This reproduces the data 1, 2, 4, 5, 6, 7, 8, 10, 14, 16, ...
* The closed form is stated after multiplying both sides by 2. Both are stated in the integers.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`; since the denominator
  has constant term 1, `A = N/D` is stated as `A * D = N` in the formal power series ring over
  the integers.
-/

namespace OMA.S_oeis_a276706

open PowerSeries

/-- A249860(n) = lcm(n + 3, |n - 3|). -/
def L (n : ℕ) : ℕ := Nat.lcm (n + 3) ((n : ℤ) - 3).natAbs

/-- `n` is the index of a record of A249860. -/
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ 0 < L n ∧ ∀ j < n, 1 ≤ j → L j < L n

instance : DecidablePred IsRecord := fun n => by unfold IsRecord; infer_instance

/-- A276706(n): the n-th record index (n >= 1). -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsRecord (n - 1)

/-- The conjectured recurrence, closed form and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 3)) ∧
    (∀ n : ℕ, 6 < n → 2 * (a n : ℤ) = 6 * n - 27 - (-1) ^ n) ∧
    mk (fun n => if n = 0 then 0 else (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X)) =
      (X * (1 + X + X ^ 2 - X ^ 4 + X ^ 7 + 3 * X ^ 8) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a276706
