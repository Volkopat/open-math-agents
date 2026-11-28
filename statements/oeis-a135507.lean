import Mathlib

/-!
# A135507: a(1) = 1; for n > 1, a(n) = 2*a(n-1) + lcm(a(n-1),n).

Source: https://oeis.org/A135507

Conjecture in the entry (Bill McEachen, Apr 04 2024):
Let p = a(n+1)/a(n)-2. If p is prime then p = A140460(m) or p = A140460(m) + 2 for some m.

Formalization notes:
* Offset 1 for A135507. Here `f k` is a(k+1), so `f 0 = 1` and
  `f (k+1) = 2 * f k + lcm(f k, k+2)`, which is the recurrence of the name with n = k+2.
  Then `a n = f (n - 1)` for n ≥ 1. The data begin 1, 4, 20, 60, 180, 540, 4860, 19440,
  58320, 174960, 2274480, 6823440.
* A140460 has offset 0: A140460(0) = 2, and each later term is the smallest integer not a
  multiple of an earlier term nor a sum of two earlier terms. As in the programs of A140460,
  the integers searched are those at least 2, and a sum of two earlier terms means a sum of
  two distinct earlier terms (a sum of a term with itself is a multiple of it anyway).
  `below m` is the list, in increasing order, of the terms of A140460 that are less than m,
  built by scanning m = 0, 1, 2, ... and keeping m exactly when m ≥ 2, m is not a multiple
  of a term kept before, and m is not a sum of two distinct terms kept before. Thus
  `InSieve m` says that m is a term of A140460, and `b n = Nat.nth InSieve n` is A140460(n).
  The data of A140460 begin 2, 3, 7, 11, 17, 23, 29, 37, 41, 47, 53, 59, 65.
* The quotient a(n+1)/a(n) is taken in the rationals, so p is the natural number with
  p = a(n+1)/a(n) - 2 exactly, as in the entry. The claim is for every n ≥ 1 and every
  index m ≥ 0 allowed.
-/

namespace OMA.S_oeis_a135507

/-- `f k` is a(k+1) of A135507. -/
def f : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * f k + Nat.lcm (f k) (k + 2)

/-- A135507, offset 1: a(n) = f(n-1). -/
def a (n : ℕ) : ℕ := f (n - 1)

/-- The terms of A140460 that are less than m, in increasing order. -/
def below : ℕ → List ℕ
  | 0 => []
  | m + 1 =>
    let L := below m
    if 2 ≤ m ∧ (∀ k ∈ L, ¬ k ∣ m) ∧ ¬ ∃ i ∈ L, ∃ j ∈ L, i < j ∧ i + j = m then
      L ++ [m]
    else L

/-- m is a term of A140460. -/
def InSieve (m : ℕ) : Prop := m ∈ below (m + 1)

/-- A140460, offset 0: the n-th term, in increasing order. -/
noncomputable def b (n : ℕ) : ℕ := Nat.nth InSieve n

/-- McEachen's conjecture on A135507: if p = a(n+1)/a(n) - 2 is prime, then p = A140460(m)
or p = A140460(m) + 2 for some m. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, (p : ℚ) = (a (n + 1) : ℚ) / (a n : ℚ) - 2 → p.Prime →
      ∃ m : ℕ, p = b m ∨ p = b m + 2 := by
  sorry

end OMA.S_oeis_a135507
