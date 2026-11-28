import OMAReductions.R_LanderParkinSelfridge_lander_parkin_selfridge_variants_five_three_R1
import Mathlib

/-! Work modulo `m` (`m = 25` for `p = 5`, `m = p` otherwise). For every residue `r < m`,
`p ∣ r ↔ r ^ 5 ≡ 0 (mod m)`, and `r ^ 5 mod m` lies in a short list `V` of fifth-power residues.
A solution with an odd divisibility pattern would give `a + b + c ≡ d (mod m)` for `a, b, c, d ∈ V`
with an odd pattern of zeros; a kernel check over `V⁴` rules this out. -/

namespace OMA.Step_LPS_five_three_R1_H1

theorem crit (m p : ℕ) (V : List ℕ) (hm : 0 < m) (hpm : p ∣ m)
    (hV : ∀ r < m, r ^ 5 % m ∈ V) (hz : ∀ r < m, (p ∣ r ↔ r ^ 5 % m = 0))
    (hok : ∀ a ∈ V, ∀ b ∈ V, ∀ c ∈ V, ∀ d ∈ V,
      ¬ ((a = 0 ↔ b = 0) ↔ (c = 0 ↔ d = 0)) → (a + b + c) % m ≠ d) :
    ∀ x₁ x₂ x₃ y : ℕ, ¬ ((p ∣ x₁ ↔ p ∣ x₂) ↔ (p ∣ x₃ ↔ p ∣ y)) →
      x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 := by
  intro x₁ x₂ x₃ y hpat heq
  have e : ∀ x : ℕ, x ^ 5 % m = (x % m) ^ 5 % m := fun x => Nat.pow_mod x 5 m
  have hz' : ∀ x : ℕ, (p ∣ x ↔ x ^ 5 % m = 0) := fun x => by
    rw [← Nat.dvd_mod_iff hpm, e x]
    exact hz _ (Nat.mod_lt _ hm)
  have hV' : ∀ x : ℕ, x ^ 5 % m ∈ V := fun x => by
    rw [e x]
    exact hV _ (Nat.mod_lt _ hm)
  have h1 : x₁ ^ 5 % m + x₂ ^ 5 % m + x₃ ^ 5 % m ≡ x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 [MOD m] :=
    ((Nat.mod_modEq _ _).add (Nat.mod_modEq _ _)).add (Nat.mod_modEq _ _)
  have hmod : (x₁ ^ 5 % m + x₂ ^ 5 % m + x₃ ^ 5 % m) % m = y ^ 5 % m := by
    have := h1
    unfold Nat.ModEq at this
    rw [this, heq]
  rw [hz' x₁, hz' x₂, hz' x₃, hz' y] at hpat
  exact hok _ (hV' x₁) _ (hV' x₂) _ (hV' x₃) _ (hV' y) hpat hmod

def V_five : List ℕ := [0, 1, 7, 18, 24]

theorem case_five : ∀ x₁ x₂ x₃ y : ℕ, ¬ ((5 ∣ x₁ ↔ 5 ∣ x₂) ↔ (5 ∣ x₃ ↔ 5 ∣ y)) →
    x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 :=
  crit 25 5 V_five (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

def V_eleven : List ℕ := [0, 1, 10]

theorem case_eleven : ∀ x₁ x₂ x₃ y : ℕ, ¬ ((11 ∣ x₁ ↔ 11 ∣ x₂) ↔ (11 ∣ x₃ ↔ 11 ∣ y)) →
    x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 :=
  crit 11 11 V_eleven (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

def V_fortyone : List ℕ := [0, 1, 3, 9, 14, 27, 32, 38, 40]

theorem case_fortyone : ∀ x₁ x₂ x₃ y : ℕ, ¬ ((41 ∣ x₁ ↔ 41 ∣ x₂) ↔ (41 ∣ x₃ ↔ 41 ∣ y)) →
    x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 :=
  crit 41 41 V_fortyone (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

def V_seventyone : List ℕ := [0, 1, 20, 23, 26, 30, 32, 34, 37, 39, 41, 45, 48, 51, 70]

theorem case_seventyone : ∀ x₁ x₂ x₃ y : ℕ, ¬ ((71 ∣ x₁ ↔ 71 ∣ x₂) ↔ (71 ∣ x₃ ↔ 71 ∣ y)) →
    x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 :=
  crit 71 71 V_seventyone (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

def V_onehundredone : List ℕ := [0, 1, 6, 10, 14, 17, 32, 36, 39, 41, 44, 57, 60, 62, 65, 69, 84, 87, 91, 95, 100]

theorem case_onehundredone : ∀ x₁ x₂ x₃ y : ℕ, ¬ ((101 ∣ x₁ ↔ 101 ∣ x₂) ↔ (101 ∣ x₃ ↔ 101 ∣ y)) →
    x₁ ^ 5 + x₂ ^ 5 + x₃ ^ 5 ≠ y ^ 5 :=
  crit 101 101 V_onehundredone (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)

end OMA.Step_LPS_five_three_R1_H1

open OMA.Step_LPS_five_three_R1_H1 in
theorem OMA.solution :
    OMA.R_LanderParkinSelfridge_lander_parkin_selfridge_variants_five_three_R1.H1 := by
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact case_five
  · exact case_eleven
  · exact case_fortyone
  · exact case_seventyone
  · exact case_onehundredone
