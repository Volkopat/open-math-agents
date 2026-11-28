import Mathlib

/-!
# Prime-power congruences for MacMahon's rectangular boxes

Source: https://oeis.org/A352656

MacMahon's symmetric product counts plane partitions fitting in a box.
Conjecture 1 in the source prints an exponent 4k while quantifying only r.
Conjecture 3 and the examples identify the intended exponent as 4r.
The two final assertions concern the sequence with side lengths n,n,2n.
-/

namespace OMA.S_oeis_a352656

/-- MacMahon's product for an arbitrary box, with zero-based indices. -/
def box (a b c : ℕ) : ℚ :=
  ∏ i ∈ Finset.range a, ∏ j ∈ Finset.range b, ∏ k ∈ Finset.range c,
    ((i+j+k+2:ℕ):ℚ) / ((i+j+k+1:ℕ):ℚ)

/-- Number of plane partitions in an n by n by 2n box. -/
def a (n : ℕ) : ℚ := box n n (2*n)

/-- The general box conjecture and the two sequence conjectures. -/
theorem main :
    (∀ p r a b c : ℕ, p.Prime → 0 < r →
      ∃ t : ℤ, box (a*p^r) (b*p^r) (c*p^r) -
        box (a*p^(r-1)) (b*p^(r-1)) (c*p^(r-1)) ^ p = (p:ℚ)^(4*r)*t) ∧
    (∀ p n r : ℕ, p.Prime → 0 < n → 0 < r →
      ∃ t : ℤ, a (n*p^r) - a (n*p^(r-1)) = (p:ℚ)^r*t) ∧
    (∀ p n r : ℕ, p.Prime → 0 < n → 0 < r →
      ∃ t : ℤ, a (n*p^r) - a (n*p^(r-1))^p = (p:ℚ)^(4*r)*t) := by
  sorry

end OMA.S_oeis_a352656
