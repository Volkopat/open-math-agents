import Mathlib

/-!
# A072339: minimal length of an alternating binary representation

Source: https://oeis.org/A072339 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A072339 (Robert G. Wilson v, Jul 15 2002), offset 1: any number n can be written (in two
ways, one with m even and one with m odd) in the form
n = 2^k_1 - 2^k_2 + 2^k_3 - ... + 2^k_m where the signs alternate and
k_1 > k_2 > k_3 > ... > k_m >= 0; sequence gives minimal value of m.
Data 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 4, 2, 3, 2, 2, 1, 3, 3, 4, 3, 5, 4, 4, 2, 3, 3, 4, 2, ...

Formula section: Conjecture: a(n)=1 if n=2^k, a(n)=a(2^k-i)+1 if 2^k<n+i<2^(k+1).
- John W. Layman, Jul 18 2002

Formalization notes.
* A representation of n is a list `l = [k_1, ..., k_m]` of exponents that is strictly
  decreasing (`List.Pairwise (· > ·)`) and whose alternating sum of powers of two
  2^k_1 - 2^k_2 + 2^k_3 - ... (`List.alternatingSum`, computed in the integers) is equal to n.
* `a n` is the minimal length m of a representation of n (`sInf` of the set of lengths).
* The second clause of the conjecture is written in the OEIS with a variable clash. The
  intended recursion (it agrees with the data, for example a(5) = a(3) + 1, a(6) = a(2) + 1,
  a(7) = a(1) + 1) is the reflection at a power of two: for n = 2^k + i with 0 < i < 2^k,
  that is 2^k < n < 2^(k+1), a(2^k + i) = a(2^k - i) + 1.
* `main` is the conjunction of the two clauses.
-/

namespace OMA.S_oeis_a072339

/-- `IsRep n l`: the strictly decreasing list of exponents `l = [k_1, ..., k_m]` represents `n`
as `2^k_1 - 2^k_2 + 2^k_3 - ...`. -/
def IsRep (n : ℕ) (l : List ℕ) : Prop :=
  l.Pairwise (· > ·) ∧ (l.map (fun k => (2 : ℤ) ^ k)).alternatingSum = (n : ℤ)

/-- A072339: the minimal number of terms of an alternating representation of `n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ l : List ℕ, IsRep n l ∧ l.length = m}

/-- Conjecture of Layman: a(2^k) = 1, and a(2^k + i) = a(2^k - i) + 1 for 0 < i < 2^k. -/
theorem main :
    (∀ k : ℕ, a (2 ^ k) = 1) ∧
    ∀ k i : ℕ, 0 < i → i < 2 ^ k → a (2 ^ k + i) = a (2 ^ k - i) + 1 := by
  sorry

end OMA.S_oeis_a072339
