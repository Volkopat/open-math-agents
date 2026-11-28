import OMAReductions.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1

/-!
The unit-fraction identity is from Thomas F. Bloom and Christian Elsholtz,
"Egyptian fractions," Nieuw Archief voor Wiskunde 5/23 (2022), p. 239.
https://www.math.tugraz.at/~elsholtz/WWW/papers/bloom-elsholtz-naw5-2022-23-4-237.pdf

The three admissible residues 19, 34, and 37 modulo 39 use the
parameter triples (1, 2, 5), (5, 1, 2), and (2, 1, 5), respectively.
-/

namespace OMA.Erdos242Mod13

private theorem fraction_identity {p a b c d : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : 4 * a * b * c * d = a + b + c * p) :
    (4 / (p : ℚ)) = 1 / ((a * b * d : ℕ) : ℚ) + 1 / ((a * c * d * p : ℕ) : ℚ) +
      1 / ((b * c * d * p : ℕ) : ℚ) := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hc' : (c : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have h' : (4 : ℚ) * a * b * c * d = a + b + c * p := by exact_mod_cast h
  push_cast
  calc
    _ = ((4 : ℚ) * a * b * c * d) / (a * b * c * d * p) := by
      field_simp [hp', ha', hb', hc', hd']
    _ = ((a : ℚ) + b + c * p) / (a * b * c * d * p) := by rw [h']
    _ = _ := by
      field_simp [hp', ha', hb', hc', hd']
      ring

private theorem ordered_witness {p a b c d : ℕ}
    (hp : 0 < p) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : 4 * a * b * c * d = a + b + c * p)
    (hab : a ≠ b) (hap : a < c * p) (hbp : b < c * p) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (4 / (p : ℚ)) = 1 / (x : ℚ) + 1 / (y : ℚ) + 1 / (z : ℚ) := by
  have hf := fraction_identity hp ha hb hc hd h
  have hx : 1 ≤ a * b * d := Nat.succ_le_iff.mpr (by positivity)
  have hxy : a * b * d < a * c * d * p := calc
    _ < a * (c * p) * d :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hbp ha) hd
    _ = _ := by ring
  have hxz : a * b * d < b * c * d * p := calc
    _ < (c * p) * b * d :=
      Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hap hb) hd
    _ = _ := by ring
  have hfactor : 0 < c * d * p := by positivity
  rcases lt_or_gt_of_ne hab with hab | hba
  · have hyz : a * c * d * p < b * c * d * p := by
      simpa only [mul_assoc] using Nat.mul_lt_mul_of_pos_right hab hfactor
    exact ⟨a * b * d, a * c * d * p, b * c * d * p, hx, hxy, hyz, hf⟩
  · have hzy : b * c * d * p < a * c * d * p := by
      simpa only [mul_assoc] using Nat.mul_lt_mul_of_pos_right hba hfactor
    exact ⟨a * b * d, b * c * d * p, a * c * d * p, hx, hxz, hzy, hf.trans (by ac_rfl)⟩

end OMA.Erdos242Mod13

theorem OMA.solution : OMA.R_Erdos242_erdos_242_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro p hp h24 _ _ h13
  have h3 : p % 3 = 1 := by omega
  have h13_mod : p % 39 % 13 = p % 13 := Nat.mod_mod_of_dvd _ (by decide)
  have h3_mod : p % 39 % 3 = p % 3 := Nat.mod_mod_of_dvd _ (by decide)
  have h39 := Nat.mod_lt p (by decide : 0 < 39)
  have hdiv := Nat.mod_add_div p 39
  rcases h13 with h0 | h6 | h8 | h11
  · have h13_dvd : 13 ∣ p := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime hp).mp h13_dvd with h | h
    · omega
    · omega
  · have heq : p = 39 * (p / 39) + 19 := by omega
    let b := 2 * (p / 39) + 1
    apply OMA.Erdos242Mod13.ordered_witness (a := 1) (b := b) (c := 2) (d := 5)
      hp.pos (by decide) (by dsimp [b]; omega) (by decide) (by decide)
    all_goals try dsimp [b]
    all_goals omega
  · have heq : p = 39 * (p / 39) + 34 := by omega
    let b := p / 39 + 1
    apply OMA.Erdos242Mod13.ordered_witness (a := 5) (b := b) (c := 1) (d := 2)
      hp.pos (by decide) (by dsimp [b]; omega) (by decide) (by decide)
    all_goals try dsimp [b]
    all_goals omega
  · have heq : p = 39 * (p / 39) + 37 := by omega
    let b := p / 39 + 1
    apply OMA.Erdos242Mod13.ordered_witness (a := 2) (b := b) (c := 1) (d := 5)
      hp.pos (by decide) (by dsimp [b]; omega) (by decide) (by decide)
    all_goals try dsimp [b]
    all_goals omega
