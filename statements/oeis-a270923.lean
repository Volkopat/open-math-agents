import Mathlib

/-!
# The numerator and denominator product in A270923

A270923 takes the coefficient [x^n] in ∏_{k≥1} ((1+x^k)/(1-x^k))^(k^n).
For the coefficient of degree n, only k = 1,...,n contribute. The vector m
records the multiplicity of each part k. Each entry lies between 0 and n,
and the total degree is the sum of k*m(k). For each k, j occurrences may come from the numerator and the other m(k)-j from the reciprocal denominator. This gives the finite convolution below.
The empty product gives a(0) = 1. The conjectured constant is exp(exp(-1)).
Source: https://oeis.org/A270923
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a270923
open Filter Topology Finset

def multiplicities (n : ℕ) : Finset (Fin n → Fin (n+1)) :=
  univ.filter (fun m => (∑ i : Fin n, (i.val+1)*(m i).val) = n)

def factor (t m : ℕ) :=
  ∑ j ∈ range (m+1), t.choose j * Nat.multichoose t (m-j)

def term (n : ℕ) : ℕ :=
  ∑ m ∈ multiplicities n, ∏ i : Fin n, factor ((i.val+1)^n) (m i).val

theorem main :
    Tendsto (fun n : ℕ => (term n:ℝ)^(1/(n:ℝ)^2)) atTop (𝓝 (Real.exp (Real.exp (-1)))) := by
  sorry

end OMA.S_oeis_a270923
