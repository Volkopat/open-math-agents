import Mathlib

/-!
Source: https://oeis.org/A094856
Source text: https://github.com/oeis/oeisdata/blob/main/seq/A094/A094856.seq
Credit: @sntntHb

A094856: Expansion of e.g.f. exp(4x)/(1-4x)^(1/4).

Source text: Conjectured to be D-finite with recurrence:
a(n) -(4n+1)a(n-1) +16(n-1)a(n-2) = 0 (R. J. Mathar). From Peter Bala,
Oct 27 2026: the recurrence follows from A'(x)/A(x) = (16x-5)/(4x-1); for
every positive integer k the sequence reduced modulo k is eventually periodic.

Expanding the defining e.g.f. gives the exact integer coefficient formula used
below. The binomial-series coefficient of (1-4x)^(-1/4) at x^i is q(i)/i!,
where q(i)=Product_{r=0..i-1}(4r+1); multiplication by exp(4x) then gives the
finite sum over i+j=n (first terms 1, 5, 29, 217, 2297, 34349).

Both assertions are formalized: Mathar's recurrence (offset 0, so on its full
common domain n>=2) and Bala's eventual periodicity modulo each positive k.
-/

namespace OMA.S_oeis_a094856

def q (n : ℕ) : ℤ := (Finset.range n).prod (fun j => 4*(j:ℤ)+1)

def weight (n : ℕ) (ij : ℕ × ℕ) : ℤ :=
  (n.choose ij.1:ℤ)*((4:ℤ)^ij.2*q ij.1)

def a (n : ℕ) : ℤ := ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, weight n ij

theorem main :
    (∀ n : ℕ, 2 ≤ n → a n-(4*(n:ℤ)+1)*a (n-1)+16*((n:ℤ)-1)*a (n-2)=0) ∧
    (∀ k : ℕ, 0<k → ∃ N p : ℕ, 0<p ∧ ∀ n, N ≤ n →
      Int.ModEq (k:ℤ) (a (n+p)) (a n)) := by
  sorry

end OMA.S_oeis_a094856
