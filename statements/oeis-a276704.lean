import Mathlib

/-!
# A276704: records in A249859

Source: https://oeis.org/A276704 (conjectures in the entry)

Entry (offset 1): Records in A249859, where A249859(n) = lcm(n + 2, n - 2) for n >= 1 (offset 1).
Formula section, Conjectures:
a(n) = 4*n^2-12*n+5 for n>3.
a(n) = 3*a(n-1)-3*a(n-2)+a(n-3) for n>6.
G.f.: x*(3-4*x+15*x^3-5*x^4-x^5) / (1-x)^3.

Formalization notes:
* lcm is taken of absolute values, as in PARI (so A249859(1) = lcm(3, 1) = 3 and
  A249859(2) = lcm(4, 0) = 0, matching the data of A249859).
* A record is a term larger than all earlier terms (record values start from 0, with a strict
  comparison, as in the programs of the sibling entries A276705/A276706): an index n >= 1 is a
  record index when A249859(n) is positive and larger than A249859(j) for every 1 <= j < n.
  a(n) is the value of A249859 at the n-th record index (`Nat.nth` at `n - 1`). This reproduces
  the data 3, 5, 6, 21, 45, 77, ...
* The closed form and recurrence are stated in the integers, with the ranges given in the entry.
* With offset 1 the generating function is `A(x) = Sum_(n >= 1) a(n) x^n`; since `(1-x)^3` has
  constant term 1, `A = N/D` is stated as `A * D = N` in the formal power series ring over the
  integers.
-/

namespace OMA.S_oeis_a276704

open PowerSeries

/-- A249859(n) = lcm(n + 2, |n - 2|). -/
def L (n : ℕ) : ℕ := Nat.lcm (n + 2) ((n : ℤ) - 2).natAbs

/-- `n` is the index of a record of A249859. -/
def IsRecord (n : ℕ) : Prop := 1 ≤ n ∧ 0 < L n ∧ ∀ j < n, 1 ≤ j → L j < L n

instance : DecidablePred IsRecord := fun n => by unfold IsRecord; infer_instance

/-- A276704(n): the n-th record value of A249859 (n >= 1). -/
noncomputable def a (n : ℕ) : ℕ := L (Nat.nth IsRecord (n - 1))

/-- The conjectured closed form, recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 3 < n → (a n : ℤ) = 4 * n ^ 2 - 12 * n + 5) ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3)) ∧
    mk (fun n => if n = 0 then 0 else (a n : ℤ)) * (1 - X) ^ 3 =
      (X * (3 - 4 * X + 15 * X ^ 3 - 5 * X ^ 4 - X ^ 5) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a276704
