import Mathlib

/-!
# Powers of two and bicolored cyclic patterns

A127804 is defined by separate recursions at even and odd indices.
The conjecture identifies its nth term with one plus A187767(n+1).

We use Andrew Howroyd's independent divisor formula (2017) for A187767:
a primitive first-row necklace of period d contributes d distinct rotation
steps, and the monochromatic pattern is excluded. The number of primitive
binary necklaces modulo color interchange is A000048(d). Its standard
necklace formula is (1/(2d)) times the sum of μ(e)·2^(d/e) over odd e|d.
Consequently d·A000048(d) is the Dirichlet convolution of the odd part
of μ with the function m ↦ 2^(m-1), evaluated at d.

Sources: https://oeis.org/A127804, https://oeis.org/A187767 and https://oeis.org/A000048
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a127804

def dyadicValue (n : ℕ) : ℤ :=
  (2:ℤ)^n + if n%2 = 1 then dyadicValue (n/2) else 0
termination_by n
decreasing_by omega

def oddTerms (f : ArithmeticFunction ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if Odd n then f n else 0, by simp⟩

def binaryWords : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else (2:ℤ)^(n-1), by simp⟩

def cyclicPatternCount (n : ℕ) : ℤ :=
  (∑ d ∈ n.divisors, (oddTerms ArithmeticFunction.moebius * binaryWords) d) - 1

theorem main : ∀ n : ℕ, dyadicValue n = 1 + cyclicPatternCount (n+1) := by
  sorry

end OMA.S_oeis_a127804
