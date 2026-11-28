import Mathlib

/-!
# A280739: a(n) is the smallest composite number > a(n-1) for which the sum of the prime factors (counted with multiplicity) is n.

Source: https://oeis.org/A280739
Credit: @agchua

Comment line of A280739 (the entry is by Dimitris Valianatos, Jan 12 2017), verbatim:
  Conjecture: a(n) exists for every n >= 4.
Offset 4; data 4, 6, 8, 10, 15, 20, 21, 28, 35, 56, 70, 105, ...

Formalisation. sopfr c is the sum of the prime factors of c counted with multiplicity
(Nat.primeFactorsList c lists the prime factors of c with multiplicity). cands m n is the set
of the composite numbers c > m with sopfr c = n, and a (n + 1) is the least element of
cands (a n) (n + 1) (sInf, which is 0 when the set is empty). No composite number has sopfr
at most 3, so a 0 = a 1 = a 2 = a 3 = 0 and a 4 = 4, the least composite number with sopfr 4;
for n >= 5, a n is the least composite number > a (n - 1) with sopfr n, as in the entry.
The conjecture says that the set defining a(n) is nonempty for every n >= 4.
-/

namespace OMA.S_oeis_a280739

/-- The sum of the prime factors of c counted with multiplicity (A001414). -/
def sopfr (c : ℕ) : ℕ := (Nat.primeFactorsList c).sum

/-- The composite numbers c > m whose sum of prime factors with multiplicity is n. -/
def cands (m n : ℕ) : Set ℕ := {c | 1 < c ∧ ¬ c.Prime ∧ m < c ∧ sopfr c = n}

/-- a (n + 1) is the smallest composite number > a n whose sopfr is n + 1. -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => sInf (cands (a n) (n + 1))

/-- a(n) exists for every n >= 4: there is a composite number > a(n-1) with sopfr n. -/
theorem main : ∀ n : ℕ, 4 ≤ n → (cands (a (n - 1)) n).Nonempty := by
  sorry

end OMA.S_oeis_a280739
