import FormalConjectures.OEIS.«262824»

/-!
Sun's square and three cubes conjecture. For coefficient six, a symmetric
pair of cubes embeds sums of two squares in the interval of inputs
24 s^6 + 36 s² q with q ≤ 2 s^4. The first step covers exactly the q in
this interval satisfying the classical two-square criterion. A separate
weighted dilation reduces the outstanding inputs for all four coefficients
to sixth-power-free positive integers outside the covered family.
-/

namespace OMA.R_OeisA262824_conjecture_1_R1

def H1 : Prop := ∀ s q : ℕ, q ≤ 2 * s^4 →
    (∀ p ∈ q.primeFactors, p % 4 = 3 → Even (padicValNat p q)) →
    ∃ w x y z : ℕ, 24*s^6 + 36*s^2*q = w^2 + x^3 + 2*y^3 + 6*z^3

def H2 : Prop := ∀ m ∈ ({3,4,5,6} : Finset ℕ), ∀ n : ℕ, 0 < n →
    (∀ d : ℕ, 2 ≤ d → ¬ d^6 ∣ n) →
    (m = 6 → ∀ s q : ℕ, q ≤ 2*s^4 →
      (∀ p ∈ q.primeFactors, p % 4 = 3 → Even (padicValNat p q)) →
      n ≠ 24*s^6 + 36*s^2*q) →
    ∃ w x y z : ℕ, n = w^2 + x^3 + 2*y^3 + m*z^3

section

private theorem dilate (d m r : ℕ)
    (hr : ∃ w x y z : ℕ, r = w^2 + x^3 + 2*y^3 + m*z^3) :
    ∃ w x y z : ℕ, d^6*r = w^2 + x^3 + 2*y^3 + m*z^3 := by
  obtain ⟨w,x,y,z,rfl⟩ := hr
  use d^3*w, d^2*x, d^2*y, d^2*z
  ring

private theorem smaller_cofactor (d r : ℕ) (hd : 2 ≤ d) (hr : 0 < r) :
    r < d^6*r := by
  have h : 2^6 ≤ d^6 := Nat.pow_le_pow_left hd 6
  exact lt_mul_of_one_lt_left hr (by omega)

private theorem primitive_case (h₁ : H1) (h₂ : H2)
    (m : ℕ) (hm : m ∈ ({3,4,5,6} : Finset ℕ))
    (n : ℕ) (hn : 0 < n) (hprim : ∀ d : ℕ, 2 ≤ d → ¬ d^6 ∣ n) :
    ∃ w x y z : ℕ, n = w^2 + x^3 + 2*y^3 + m*z^3 := by
  classical
  by_cases h : m = 6 ∧ ∃ s q : ℕ, q ≤ 2*s^4 ∧
      (∀ p ∈ q.primeFactors, p % 4 = 3 → Even (padicValNat p q)) ∧
      n = 24*s^6 + 36*s^2*q
  · obtain ⟨rfl,s,q,hq,hfac,rfl⟩ := h
    exact h₁ s q hq hfac
  · apply h₂ m hm n hn hprim
    intro hm6 s q hq hfac he
    exact h ⟨hm6,s,q,hq,hfac,he⟩

end

theorem main : H1 → H2 → type_of% @OeisA262824.conjecture_1 := by
  intro h₁ h₂ m hm n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0,0,0,0,by simp⟩
    by_cases prim : ∀ d : ℕ, 2 ≤ d → ¬ d^6 ∣ n
    · exact primitive_case h₁ h₂ m hm n hn prim
    push Not at prim
    obtain ⟨d,hd,r,he⟩ := prim
    have hr : 0 < r := by
      by_contra! hz
      simp [Nat.eq_zero_of_le_zero hz] at he
      omega
    have hlt : r < n := he ▸ smaller_cofactor d r hd hr
    rw [he]
    exact dilate d m r (ih r hlt)

end OMA.R_OeisA262824_conjecture_1_R1
