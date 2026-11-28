import Mathlib

/-!
# A276705: records in A249860

Source: https://oeis.org/A276705 (conjectures in the entry)

Entry (offset 1): Records in A249860, where A249860(n) = lcm(n + 3, n - 3) for n >= 1 (offset 1).
Formula section, Conjectures:
a(n) = (347+27*(-1)^n)/2 - 3*(27+(-1)^n)*n + 9*n^2 for n>6.
a(n) = a(n-1)+2*a(n-2)-2*a(n-3)-a(n-4)+a(n-5) for n>11.
G.f.: x*(4+x-6*x^2-x^3+x^4+10*x^5+35*x^6+15*x^7+27*x^8-x^9-13*x^10) / ((1-x)^3*(1+x)^2).

Formalization notes:
* lcm is taken of absolute values, as in the PARI programs of the entries (so A249860(1) =
  lcm(4, 2) = 4 and A249860(3) = lcm(6, 0) = 0).
* As in the PARI program of the sibling entry A276706 (record value starting from 0, strict
  comparison), an index n >= 1 is a record index when A249860(n) is positive and larger than
  A249860(j) for every 1 <= j < n; a(n) is the value of A249860 at the n-th record index
  (`Nat.nth` at `n - 1`). This reproduces the data 4, 5, 7, 8, 9, 20, 55, 91, 187, ...
* The closed form is stated after multiplying both sides by 2. It and the recurrence are stated
  in the integers, with the ranges given in the entry.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`; since the denominator
  has constant term 1, `A = N/D` is stated as `A * D = N` in the formal power series ring over
  the integers.
-/

namespace OMA.S_oeis_a276705

open PowerSeries

/-- A249860(n) = lcm(n + 3, |n - 3|). -/
def L (n : ℕ) : ℕ := Nat.lcm (n + 3) ((n : ℤ) - 3).natAbs

/-- `n` is the index of a record of A249860. -/
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ 0 < L n ∧ ∀ j < n, 1 ≤ j → L j < L n

instance : DecidablePred IsRecord := fun n => by unfold IsRecord; infer_instance

/-- A276705(n): the n-th record value of A249860 (n >= 1). -/
noncomputable def a (n : ℕ) : ℕ := L (Nat.nth IsRecord (n - 1))

/-- The conjectured closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      2 * (a n : ℤ) = (347 + 27 * (-1) ^ n) - 6 * (27 + (-1) ^ n) * n + 18 * (n : ℤ) ^ 2) ∧
    (∀ n : ℕ, 11 < n →
      (a n : ℤ) = a (n - 1) + 2 * a (n - 2) - 2 * a (n - 3) - a (n - 4) + a (n - 5)) ∧
    mk (fun n => if n = 0 then 0 else (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2) =
      (X * (4 + X - 6 * X ^ 2 - X ^ 3 + X ^ 4 + 10 * X ^ 5 + 35 * X ^ 6 + 15 * X ^ 7 + 27 * X ^ 8 -
        X ^ 9 - 13 * X ^ 10) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a276705
