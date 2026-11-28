import OMAReductions.R_oeis_a352057_R1

-- Credit: @AlfredMelson
/-!
For the nonsingular unit digits, a square root of 8u+1 must be close enough to
a multiple of every power of five in u-d. This excludes sparse cores before
a square test. For suffix 003, dividing the root by five removes the singular
factor and drops three decimal places from the digit problem.
-/
namespace OMA.R_oeis_a352057_R1_H1_R1

open OMA.S_oeis_a352057

def H1 : Prop := ∀ u : ℕ, 1000000 ≤ u → u%10 = 1 → NonzeroDigitsAre u 1 →
  (∀ k : ℕ, 5^k ∣ u-1 → (5^k-3)^2 ≤ 8*u+1) → ∀ x : ℕ, x^2 ≠ 8*u+1

def H2 : Prop := ∀ u : ℕ, 1000000 ≤ u → u%10 = 6 → NonzeroDigitsAre u 6 →
  (∀ k : ℕ, 5^k ∣ u-6 → (5^k-7)^2 ≤ 8*u+1) → ∀ x : ℕ, x^2 ≠ 8*u+1

def H3 : Prop := ∀ v : ℕ, 1000 ≤ v → NonzeroDigitsAre v 3 →
  ∀ y : ℕ, y^2 ≠ 320*v+1

private lemma gap {u d r x : ℕ} (hd : d < u) (hr : r^2 = 8*d+1)
    (hunit : ¬5 ∣ 2*r) (hx : x^2 = 8*u+1) (k : ℕ) (hk : 5^k ∣ u-d) :
    (5^k-r)^2 ≤ 8*u+1 := by
  have hlt : r < x := by
    by_contra! h
    have := Nat.pow_le_pow_left h 2
    omega
  obtain ⟨v,hv⟩ := hk
  have hu : u = d+5^k*v := by omega
  have hsub := Nat.sub_add_cancel hlt.le
  have hprod : 5^k ∣ (x-r)*(x+r) := by
    refine ⟨8*v, ?_⟩
    nlinarith [congrArg (fun n : ℕ => n*(x+r)) hsub]
  have hp : Prime (5:ℕ) := Nat.prime_iff.mp (by decide)
  have hle : 5^k ≤ x+r := by
    by_cases h : 5 ∣ x-r
    · have hu' : ¬5 ∣ x+r := by omega
      have := Nat.le_of_dvd (by omega : 0 < x-r) (hp.pow_dvd_of_dvd_mul_right k hu' hprod)
      omega
    · exact Nat.le_of_dvd (by omega) (hp.pow_dvd_of_dvd_mul_left k h hprod)
  rw [← hx]
  exact Nat.pow_le_pow_left (by omega) 2

theorem main : H1 → H2 → H3 → OMA.R_oeis_a352057_R1.H1 := by
  intro h1 h6 h3 u d big last _ _ digs cases' x hx
  rcases cases' with rfl|rfl|suffix
  · exact h1 u big last digs (gap (by omega) (by decide) (by decide) hx) x hx
  · exact h6 u big last digs (gap (by omega) (by decide) (by decide) hx) x hx
  · have hd : d = 3 := by omega
    rw [hd] at digs
    obtain ⟨_, d1⟩ := OMA.R_oeis_a352057_R1.peel digs
    obtain ⟨_, d2⟩ := OMA.R_oeis_a352057_R1.peel d1
    obtain ⟨_, d3⟩ := OMA.R_oeis_a352057_R1.peel d2
    simp only [Nat.div_div_eq_div_mul] at d3
    have hx5 : 5 ∣ x := by
      apply Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5)
      rw [hx]
      omega
    obtain ⟨y,rfl⟩ := hx5
    apply h3 (u/1000) (by omega) d3 y
    have hu : u = 1000*(u/1000)+3 := by omega
    nlinarith
end OMA.R_oeis_a352057_R1_H1_R1
