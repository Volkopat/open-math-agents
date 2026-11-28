import Mathlib

/-!
# Coefficient growth of the Euler transform of n-th powers

Sequence A252782 is [x^n] ∏_{k≥1} (1-x^k)^(-k^n), the degree-n coefficient of the Euler transform of the n-th powers.
For the coefficient of degree n, only k = 1,...,n contribute. The vector m
records the multiplicity of each part k. Each entry lies between 0 and n,
and the total degree is the sum of k*m(k). Choosing m(k) occurrences among k^n types with repetitions allowed gives Nat.multichoose (k^n) (m k).
The empty product gives a(0) = 1. The conjectured constant is exp(exp(-1)).
Source: https://oeis.org/A252782
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a252782
open Filter Topology Finset

def multiplicities (n : ℕ) : Finset (Fin n → Fin (n+1)) :=
  univ.filter (fun m => (∑ i : Fin n, (i.val+1)*(m i).val) = n)

def factor (t m : ℕ) := Nat.multichoose t m

def term (n : ℕ) : ℕ :=
  ∑ m ∈ multiplicities n, ∏ i : Fin n, factor ((i.val+1)^n) (m i).val

theorem main :
    Tendsto (fun n : ℕ => (term n:ℝ)^(1/(n:ℝ)^2)) atTop (𝓝 (Real.exp (Real.exp (-1)))) := by
  sorry

end OMA.S_oeis_a252782
