import Mathlib

/-!
# A237978: Number of partitions of n having depth 3; see Comments.

Source: https://oeis.org/A237978
Credit: @agchua

Comment of A237978 (the entry is by Clark Kimberling):
  Suppose that P is a partition of n. Let x(1), x(2),...,x(k) be the distinct parts of P, and
  let m(i) be the multiplicity of x(i) in P. Let f(P) be the partition [m(1)*x(1), m(2)*x(2),...,
  x(k)*m(k)] of n. Define c(0,P) = P, c(1,P) = f(P),..., c(n,P) = f(c(n-1,P)), and define
  d(P) = least n such that c(n,P) has no repeated parts; d(P) is introduced here as the depth of
  P. Clearly d(P) = 0 if and only if P is a strict partition, as in A000009. Conjecture: if
  d >= 0, then 2^d is the least n that has a partition of depth d.
A partition of n is a Nat.Partition n (a multiset of positive parts with sum n), and f acts on
its multiset of parts. P has depth d when c(d,P) has no repeated parts and c(j,P) has a repeated
part for every j < d. The offset of the entry is 1, so n ranges over the positive integers
(the empty partition of 0 would have depth 0).
-/

namespace OMA.S_oeis_a237978

/-- f(P): each distinct part x of multiplicity m is replaced by the single part m*x. -/
def f (s : Multiset ℕ) : Multiset ℕ := s.toFinset.val.map (fun x => s.count x * x)

/-- P has depth d: c(d,P) = f^[d] P has no repeated parts, and c(j,P) has one for each j < d. -/
def HasDepth (s : Multiset ℕ) (d : ℕ) : Prop := (f^[d] s).Nodup ∧ ∀ j < d, ¬ (f^[j] s).Nodup

/-- Kimberling's conjecture: for every d >= 0, 2^d is the least positive n that has a partition
of depth d. -/
theorem main : ∀ d : ℕ, (∃ P : Nat.Partition (2 ^ d), HasDepth P.parts d) ∧
    ∀ n : ℕ, 1 ≤ n → n < 2 ^ d → ∀ P : Nat.Partition n, ¬ HasDepth P.parts d := by
  sorry

end OMA.S_oeis_a237978
