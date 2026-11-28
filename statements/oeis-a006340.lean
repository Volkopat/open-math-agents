import Mathlib

/-!
# A006340: An eta-sequence: [ (n+1)*tau + 1/2 ] - [ n*tau + 1/2 ], tau = (1 + sqrt(5))/2.

Source: https://oeis.org/A006340
Credit: @HaZeLnU7

Conjecture stated in A006340 (Clark Kimberling, Jul 14 2014): A006340 = continued fraction
expansion of (2.729967741... = sup{f(n,1)}), where f(1,x) = x + 1 and thereafter
f(n,x) = x + 1 if n is in the lower Wythoff sequence (A000201), else f(n,x) = 1/x.
The first 12 values of f(n,1) are given in the Example at A245216.

The values f(n,1) are taken from the program in A245216 (Peter J. C. Moses), whose
first 12 values are exactly the set S(12) = {1, 2, 1/2, 3/2, 5/2, 2/5, 7/5, 5/7, 12/7, 19/7,
7/19, 26/19} listed there: s(1) = 1, and for n >= 2, s(n) = s(n-1) + 1 if n - 1 is in A000201,
else s(n) = 1/s(n-1). (Read literally, the name of A245216 starts one step later, with
f(1,1) = 2; the two readings differ only by the value 1, which is not the sup, so the sup
is the same.) Its sup is c = 2.7299677415998024878916467748759075211...
(A245216), and A245216 says the continued fraction of c is [2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, ...].

A006340 has offset 0: a(0) = 2, a(1) = 1, a(2) = 2, ... The conjecture says that a(0) is the
integer part of c and a(1), a(2), ... are the partial denominators of the regular continued
fraction of c (all partial numerators 1), computed by Mathlib's `GenContFract.of`. The
statement also asserts that the values s(n) are bounded above, so that the sup is finite.
-/

namespace OMA.S_oeis_a006340

/-- A006340, offset 0: a(n) = floor((n+1)*tau + 1/2) - floor(n*tau + 1/2), tau the golden ratio. -/
noncomputable def a (n : ℕ) : ℤ :=
  ⌊((n : ℝ) + 1) * Real.goldenRatio + 1 / 2⌋ - ⌊(n : ℝ) * Real.goldenRatio + 1 / 2⌋

/-- Membership in the lower Wythoff sequence A000201: m = floor(k*phi) for some k >= 1. -/
def IsLowerWythoff (m : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ m = ⌊(k : ℝ) * Real.goldenRatio⌋₊

open Classical in
/-- s n = f(n,1) for n >= 1, as in the program of A245216 (s 0 is not used). -/
noncomputable def s : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => if IsLowerWythoff (n + 1) then s (n + 1) + 1 else 1 / s (n + 1)

/-- c = sup{f(n,1) : n >= 1} (A245216). -/
noncomputable def c : ℝ := ⨆ n : ℕ, s (n + 1)

/-- Kimberling's conjecture: the values f(n,1) are bounded, and the regular continued
fraction of their sup c is [a(0); a(1), a(2), ...]. -/
theorem main :
    BddAbove (Set.range fun n : ℕ => s (n + 1)) ∧
      (GenContFract.of c).h = (a 0 : ℝ) ∧
      ∀ n : ℕ, (GenContFract.of c).s.get? n = some ⟨1, (a (n + 1) : ℝ)⟩ := by
  sorry

end OMA.S_oeis_a006340
