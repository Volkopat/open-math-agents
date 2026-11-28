import OMAStatements.S_oeis_a338272
import Mathlib

/-! For every coefficient pair, a binary sum of squares suffices. In the
remaining squarefree kernel two distinct primes congruent to 3 modulo 4
must occur. Homogeneity then restores all removed square factors. -/
namespace OMA.R_oeis_a338272_R1

open OMA.S_oeis_a338272

def H1 : Prop := ∀ n : ℕ, 0 < n → n % 4 = 1 →
  (∃ x y : ℕ, n = x^2 + y^2) ∨
    ∃ s d : ℕ, 0 < s ∧ s % 4 = 1 ∧ Squarefree s ∧ n = d^2*s ∧
      ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ p*q ∣ s

def H2 : Prop := ∀ s : ℕ, 0 < s → s % 4 = 1 → Squarefree s →
  (∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≠ q ∧ p % 4 = 3 ∧ q % 4 = 3 ∧ p*q ∣ s) →
  ∀ a b : ℤ, (a,b) ∈ coefficientPairs → ∃ x y z w : ℕ,
    s = x^2+y^2+z^2+w^2 ∧ IsSquare (a*x*y+b*z*w)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a338272.main := by
  intro classify solve n hn hmod a b hab
  rcases classify n hn hmod with ⟨u,v,h⟩ | ⟨s,d,hs,hm,hsf,hn',hpq⟩
  · refine ⟨u,0,v,0,?_,?_⟩ <;> simp [h]
  obtain ⟨x,y,z,w,hs',r,hr⟩ := solve s hs hm hsf hpq a b hab
  refine ⟨d*x,d*y,d*z,d*w,?_,d*r,?_⟩
  · rw [hn', hs']
    ring
  · push_cast
    linear_combination (d:ℤ)^2 * hr

end OMA.R_oeis_a338272_R1
