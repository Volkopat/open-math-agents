import Mathlib

/-!
# A154293: Integers of the form t/6, where t is a triangular number (A000217).

Source: https://oeis.org/A154293
Credit: @rickmanelius

Conjecture (Omar E. Pol, Aug 19 2011): A193828 divided by 2. (Charles R Greathouse IV,
Jan 02 2012: The above conjecture is correct.)

The entry also marks a formula as conjectured (R. J. Mathar, Jan 07 2009): G.f.:
x^2*(x^2-x+1)*(x^2+4*x+1)/((1+x^2)^2*(1-x)^3) (conjectured). (Charles R Greathouse IV,
Jan 02 2012: The conjectured g.f. is correct.)

Formalization notes:
* A000217 is the triangular numbers T(m) = m(m+1)/2 for m ≥ 0, so T(0) = 0 is one of them.
  Every T(m) is ≥ 0, so an integer of the form t/6 with t triangular is a natural number x
  with T(m) = 6x for some m. `IsTriangularSixth x` says exactly this.
* A154293 has offset 1 and lists these integers in increasing order: `a n` is
  `Nat.nth IsTriangularSixth (n - 1)` (`Nat.nth` counts from 0). The set is infinite, since
  T(12j) = 6 j (12j + 1) for every j, so `Nat.nth` runs through all of it and gives no junk
  value. The data begin 0, 1, 6, 11, 13, 20, 35, 46, 50, 63, ..., matching the entry.
* A193828 (offset 0) is the even generalized pentagonal numbers in increasing order. The
  generalized pentagonal numbers (A001318) are k(3k-1)/2 for k = 0, 1, -1, 2, -2, ...; since
  k(3k-1) is always even, g is one of them exactly when 2g = k(3k-1) for some integer k
  (`IsGenPentagonal g`). `b n` is the n-th even one, counted from b(0) = 0. The data begin
  0, 2, 12, 22, 26, 40, 70, 92, ..., matching A193828.
* A193828 divided by 2 means a(n) = A193828(n-1)/2 for every n ≥ 1, with the two offsets
  (this is the formula a(n) = 2*A154293(n+1) in A193828). As every term of A193828 is even,
  it is stated without a division: 2 a(n) = b(n - 1).
* The g.f. of the offset-1 sequence is Sum_{n ≥ 1} a(n) x^n (the entry's example reads
  G.f. = x^2 + 6*x^3 + 11*x^4 + ...). `gf` is this integer power series, with constant term 0.
  The rational g.f. is stated after multiplying by the denominator (1+x^2)^2 (1-x)^3, whose
  constant term is 1, so the equation says exactly that gf equals the quotient.
* Both conjectures are stated, as a conjunction. The other formulas of the entry are not part
  of them and are not stated.
-/

namespace OMA.S_oeis_a154293

/-- The triangular numbers A000217: T(m) = m(m+1)/2. -/
def triangular (m : ℕ) : ℕ := m * (m + 1) / 2

/-- x is an integer of the form t/6 with t triangular: T(m) = 6x for some m. -/
def IsTriangularSixth (x : ℕ) : Prop := ∃ m : ℕ, triangular m = 6 * x

/-- A154293 (offset 1): a(n) is the n-th integer of the form t/6, in increasing order. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth IsTriangularSixth (n - 1)

/-- A001318: g is a generalized pentagonal number k(3k-1)/2 for some integer k. -/
def IsGenPentagonal (g : ℕ) : Prop := ∃ k : ℤ, 2 * (g : ℤ) = k * (3 * k - 1)

/-- A193828 (offset 0): b(n) is the n-th even generalized pentagonal number, in increasing
order, from b(0) = 0. -/
noncomputable def b (n : ℕ) : ℕ := Nat.nth (fun g => Even g ∧ IsGenPentagonal g) n

open PowerSeries

/-- The g.f. Sum_{n ≥ 1} a(n) x^n of A154293, an integer power series with constant term 0. -/
noncomputable def gf : PowerSeries ℤ := mk (fun n => if n = 0 then 0 else (a n : ℤ))

/-- Pol's conjecture (A193828 divided by 2) and Mathar's conjectured g.f. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → 2 * a n = b (n - 1)) ∧
      (1 + X ^ 2) ^ 2 * (1 - X) ^ 3 * gf = X ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + 4 * X + 1) := by
  sorry

end OMA.S_oeis_a154293
