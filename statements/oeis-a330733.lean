import Mathlib

/-!
# A330733: Triangle read by rows in which row n is the complete rhythm of n (see Comments for precise definition).

Source: https://oeis.org/A330733
Credit: @agchua

In the comments of A330733 (the entry is by Andrew Hood, Dec 28 2019):
  Right diagonal is A002033 (conjectured).
  Any prime column stripped of zeros also yields A002033 (conjectured).

(The name line puts the words complete rhythm in double quotes; they are omitted above.)

A330733 has offset 1: row n (n >= 1) consists of the n terms R(n,1), ..., R(n,n) of the complete
rhythm of n. From the comments: the natural rhythm of n is n-1 zeros followed by 1, so its j-th
term is 1 if j = n and 0 otherwise; the complete rhythm of n is the term-by-term sum of the natural
rhythm of n and of the complete rhythm of f, extended through n/f cycles, for every proper divisor
f of n. As the worked examples show (4 has the unique proper factor 2; the proper divisors of 12
used are 2, 3, 4 and 6), proper divisors here exclude 1 and n. The j-th term of the rhythm of f
repeated n/f times is its ((j - 1) mod f + 1)-th term. This is `R` below (used for 1 <= j <= n);
it reproduces the listed data.
A002033 (offset 0) is taken from its formula line a(n-1) = Sum_{i|n, i < n} a(i-1) (David
Wasserman, Nov 14 2006; printed with the typo i|d for i|n; it is also the recursion of the PARI
program of the entry), valid for n >= 2, together with a(0) = 1: this is `A002033` below.
The right diagonal is the sequence R(n,n), n >= 1, so the first claim is R(n,n) = A002033(n-1).
Column k consists of the entries R(n,k) with n >= k. For a prime p, column p stripped of zeros is
A002033 exactly when R(n,p) = 0 for every n >= p not divisible by p, R(m*p,p) = A002033(m-1) for
every m >= 1, and no term of A002033 is 0; the statement asserts these three facts.
-/

namespace OMA.S_oeis_a330733

/-- R(n,j): the j-th term of the complete rhythm of n (for 1 <= j <= n). -/
def R (n j : ℕ) : ℕ :=
  (if j = n then 1 else 0) +
    ∑ f ∈ ((Nat.properDivisors n).erase 1).attach,
      have : f.1 < n := (Nat.mem_properDivisors.mp (Finset.mem_of_mem_erase f.2)).2
      R f.1 ((j - 1) % f.1 + 1)
termination_by n

/-- A002033: a(0) = 1 and a(n-1) = Sum_{i|n, i < n} a(i-1) for n >= 2. -/
def A002033 : ℕ → ℕ
  | 0 => 1
  | m + 1 =>
    ∑ i ∈ (Nat.properDivisors (m + 2)).attach,
      have : i.1 - 1 < m + 1 := by
        have h := (Nat.mem_properDivisors.mp i.2).2
        omega
      A002033 (i.1 - 1)
termination_by n => n

/-- Hood's two conjectures: the right diagonal of A330733 is A002033, and every prime column of
A330733 stripped of zeros is A002033. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → R n n = A002033 (n - 1)) ∧
    (∀ m : ℕ, A002033 m ≠ 0) ∧
    (∀ p : ℕ, p.Prime →
      (∀ n : ℕ, p ≤ n → ¬ p ∣ n → R n p = 0) ∧
      (∀ m : ℕ, 1 ≤ m → R (m * p) p = A002033 (m - 1))) := by
  sorry

end OMA.S_oeis_a330733
