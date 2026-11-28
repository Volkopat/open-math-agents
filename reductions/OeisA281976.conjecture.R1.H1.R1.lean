import OMAReductions.R_OeisA281976_conjecture_R1

-- Reduction OeisA281976.conjecture.R1.H1.R1 of step OeisA281976.conjecture.R1.H1
-- Credit: @AlfredMelson

namespace OMA.R_OeisA281976_conjecture_R1_H1_R1


open OeisA281976

private lemma assemble {n x y : ℕ} (hx : IsSquare x) (hy : IsSquare (x+24*y))
    (hle : x^2+y^2 ≤ n) (hr : ∀ q ∈ (n-(x^2+y^2)).primeFactors,
      q%4=3 → Even (padicValNat q (n-(x^2+y^2)))) : A n := by
  obtain ⟨z,w,hw⟩ := Nat.eq_sq_add_sq_iff.mpr hr
  rcases le_total z w with h|h
  · exact ⟨x,y,z,w,by omega,h,hx,hy⟩
  · exact ⟨x,y,w,z,by omega,h,hx,hy⟩

/-! Put x=a² and seek a second square (a+2t)². The required y then equals
t(a+t)/6. Once a and t are chosen, the sum-of-two-squares theorem recovers
the last two coordinates from prime valuations of the residual. The choices
(x,y)=(0,0),(1,0),(1,1) already handle three residuals. -/

def H1 : Prop := ∀ n : ℕ, n % 4 = 1 → (∀ p : ℕ, p.Prime → ¬ p^4 ∣ n) →
  (∀ i : ℕ, i ≤ 2 → ∃ q ∈ (n-i).primeFactors, q%4 = 3 ∧ ¬ Even (padicValNat q (n-i))) →
  ∃ a t : ℕ, 6 ∣ t*(a+t) ∧
    let y := t*(a+t)/6
    a^4+y^2 ≤ n ∧ ∀ q ∈ (n-(a^4+y^2)).primeFactors,
      q%4 = 3 → Even (padicValNat q (n-(a^4+y^2)))

def H2 : Prop := ∀ n : ℕ, n % 4 = 3 → (∀ p : ℕ, p.Prime → ¬ p^4 ∣ n) →
  (∀ i : ℕ, i ≤ 2 → ∃ q ∈ (n-i).primeFactors, q%4 = 3 ∧ ¬ Even (padicValNat q (n-i))) →
  ∃ a t : ℕ, 6 ∣ t*(a+t) ∧
    let y := t*(a+t)/6
    a^4+y^2 ≤ n ∧ ∀ q ∈ (n-(a^4+y^2)).primeFactors,
      q%4 = 3 → Even (padicValNat q (n-(a^4+y^2)))


theorem main : H1 → H2 → OMA.R_OeisA281976_conjecture_R1.H1 := by
  intro h1 h3 n hodd hfree
  by_cases small : n < 3
  · have : n = 1 := by omega
    simpa [this] using OeisA281976.a_1
  by_cases bad : ∀ i : ℕ, i ≤ 2 → ∃ q ∈ (n-i).primeFactors,
      q%4 = 3 ∧ ¬ Even (padicValNat q (n-i))
  · obtain ⟨a,t,hd,bound,hr⟩ := (show ∃ a t : ℕ, 6 ∣ t*(a+t) ∧
        let y := t*(a+t)/6
        a^4+y^2 ≤ n ∧ ∀ q ∈ (n-(a^4+y^2)).primeFactors,
          q%4 = 3 → Even (padicValNat q (n-(a^4+y^2))) from by
      rcases (show n%4=1 ∨ n%4=3 by omega) with h | h
      · exact h1 n h hfree bad
      · exact h3 n h hfree bad)
    let y := t*(a+t)/6
    have eq : y*6 = t*(a+t) := Nat.div_mul_cancel hd
    have hx : IsSquare (a^2) := ⟨a, pow_two a⟩
    have hy : IsSquare (a^2+24*y) := ⟨a+2*t, by nlinarith [eq]⟩
    apply assemble hx hy
    · simpa only [← pow_mul] using bound
    · simpa only [← pow_mul] using hr
  · push_neg at bad
    obtain ⟨i,hi,hv⟩ := bad
    interval_cases i
    · apply assemble (x:=0) (y:=0) (by exact ⟨0,rfl⟩) (by exact ⟨0,rfl⟩) <;> first | norm_num; omega | simpa using hv
    · apply assemble (x:=1) (y:=0) (by exact ⟨1,rfl⟩) (by exact ⟨1,rfl⟩) <;> first | norm_num; omega | simpa using hv
    · apply assemble (x:=1) (y:=1) (by exact ⟨1,rfl⟩) (by exact ⟨5,rfl⟩) <;> first | norm_num; omega | simpa using hv

end OMA.R_OeisA281976_conjecture_R1_H1_R1
