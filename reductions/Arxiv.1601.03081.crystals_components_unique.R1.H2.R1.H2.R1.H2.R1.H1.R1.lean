import OMAReductions.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H2_R1

-- Reduction Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H2.R1.H1.R1 of step Arxiv.1601.03081.crystals_components_unique.R1.H2.R1.H2.R1.H2.R1.H1
-- Credit: @ehsanmok

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H2_R1_H1_R1

open NumberTheorySymbols

/-- Square lemma: in an odd crystal pair one of (a+1)/2, (b+1)/2 is a perfect square. -/
def H1 : Prop :=
  ∀ a b : ℕ, Odd a → Odd b → (a+1)*(b+1) ∣ (a+b)^2 →
    (∃ u : ℕ, a+1 = 2*u^2) ∨ (∃ v : ℕ, b+1 = 2*v^2)

/-- Target restricted to g, y, z = ±1 mod 8 with the two Pell-type witnesses. -/
def H2 : Prop :=
  ∀ g y z p q : ℕ, 1 < g → 13 ≤ y →
    Odd g → Odd y → Odd z → g*y ≤ 3*z → Nat.Coprime 3 y →
    (g % 8 = 1 ∨ g % 8 = 7) → (y % 8 = 1 ∨ y % 8 = 7) → (z % 8 = 1 ∨ z % 8 = 7) →
    y*z+1 = 2*q^2 → g*y+1 = 2*p^2 →
    (g*3+1)*(y*z+1) ∣ (g*3+y*z)^2 →
    (g*y+1)*(3*z+1) ∣ (g*y+3*z)^2 → g = z

theorem mod8_of_two_sq {n m q : ℕ} (hn : Odd n) (h : n*m+1 = 2*q^2) :
    n % 8 = 1 ∨ n % 8 = 7 := by
  have hcop : Int.gcd (q : ℤ) n = 1 := by
    rw [Int.gcd_natCast_natCast]
    have hd : Nat.gcd q n ∣ 1 := by
      have h1 : Nat.gcd q n ∣ n*m := (Nat.gcd_dvd_right q n).mul_right m
      have h2 : Nat.gcd q n ∣ 2*q^2 :=
        ((Nat.gcd_dvd_left q n).pow (by norm_num : 2 ≠ 0)).mul_left 2
      rw [← h] at h2
      exact (Nat.dvd_add_right h1).mp h2
    exact Nat.dvd_one.mp hd
  have hmod : ((2 : ℤ) * (q : ℤ)^2) % (n : ℤ) = (1 : ℤ) % (n : ℤ) := by
    have : (2 : ℤ) * (q : ℤ)^2 = 1 + (n : ℤ) * m := by exact_mod_cast (by omega : 2*q^2 = 1 + n*m)
    rw [this, Int.add_mul_emod_self_left]
  have hJ := jacobiSym.mod_left' hmod
  rw [jacobiSym.mul_left, jacobiSym.sq_one' hcop, jacobiSym.one_left, mul_one,
    jacobiSym.at_two hn, ZMod.χ₈_nat_eq_if_mod_eight] at hJ
  have h2 : n % 2 = 1 := Nat.odd_iff.mp hn
  by_contra hc
  rw [if_neg (by omega), if_neg hc] at hJ
  exact absurd hJ (by decide)

theorem not_three_mul_add_one (g u : ℕ) : g*3+1 ≠ 2*u^2 := by
  intro h
  have h3 : u^2 % 3 = 0 ∨ u^2 % 3 = 1 := by
    rcases (by omega : u % 3 = 0 ∨ u % 3 = 1 ∨ u % 3 = 2) with h | h | h <;>
      simp [Nat.pow_mod, h]
  omega

theorem main : H1 → H2 → OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro hA hB g y z hg hy hgo hyo hzo ho hcop hf hh
  have h3o : Odd 3 := by decide
  obtain ⟨q, hq⟩ : ∃ q : ℕ, y*z+1 = 2*q^2 := by
    rcases hA (g*3) (y*z) (hgo.mul h3o) (hyo.mul hzo) hf with ⟨u, hu⟩ | h
    · exact absurd hu (not_three_mul_add_one g u)
    · exact h
  obtain ⟨p, hp⟩ : ∃ p : ℕ, g*y+1 = 2*p^2 := by
    rcases hA (g*y) (3*z) (hgo.mul hyo) (h3o.mul hzo) hh with h | ⟨v, hv⟩
    · exact h
    · exact absurd (by rw [mul_comm z 3]; exact hv) (not_three_mul_add_one z v)
  have hy8 := mod8_of_two_sq hyo hq
  have hz8 := mod8_of_two_sq (m := y) hzo (by rw [mul_comm]; exact hq)
  have hg8 := mod8_of_two_sq hgo hp
  exact hB g y z p q hg hy hgo hyo hzo ho hcop hg8 hy8 hz8 hq hp hf hh

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R1_H2_R1_H2_R1_H2_R1_H1_R1
