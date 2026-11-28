import Mathlib

/-!
# A291271: The arithmetic function v_4(n,2).

Source: https://oeis.org/A291271
Credit: @agchua

Wesley Ivan Hurt (Oct 02 2017), in the formula section of A291271:
  Conjecture: a(n) = (n-2-cos(n*Pi)-cos(n*Pi/2))/2.

The arithmetic function v_g(n,h) of B. Bajnok (Additive Combinatorics: A Menu of Research
Problems, arXiv:1705.07444, the reference of the entry) is the maximum of
(floor((d - 1 - gcd(d,g))/h) + 1) * n/d over the positive divisors d of n; this is also the
Mathematica program of the entry, which reproduces the listed data. Below this maximum is the
supremum `sSup` of the finite set of these values in ℝ, and a(n) = v_4(n,2). The offset of the
entry is 2, so the claim is stated for n >= 2.
-/

namespace OMA.S_oeis_a291271

/-- Bajnok's v_g(n,h): the maximum of (floor((d-1-gcd(d,g))/h) + 1) * n/d over the divisors
d of n. -/
noncomputable def v (g n h : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ d ∈ Nat.divisors n,
    x = ((⌊((d : ℝ) - 1 - (Nat.gcd d g : ℝ)) / (h : ℝ)⌋ + 1 : ℤ) : ℝ) * (n : ℝ) / (d : ℝ)}

/-- A291271(n) = v_4(n,2). -/
noncomputable def a (n : ℕ) : ℝ := v 4 n 2

/-- Hurt's conjecture: a(n) = (n - 2 - cos(n*Pi) - cos(n*Pi/2))/2 for n >= 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n = ((n : ℝ) - 2 - Real.cos (n * Real.pi) - Real.cos (n * Real.pi / 2)) / 2 := by
  sorry

end OMA.S_oeis_a291271
