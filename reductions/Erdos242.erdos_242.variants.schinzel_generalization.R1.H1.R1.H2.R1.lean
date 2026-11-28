import OMAReductions.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1

/-!
# Divisibility criteria for Schinzel's three-term unit fractions

The two constructions are specializations of the Type I and Type II
parametrizations in Pomerance and Weingartner's work on exceptions to the
Erdős–Straus–Schinzel conjecture. We use bounds that make all denominators distinct.
-/

open Filter

namespace OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1_H2_R1

private lemma type_one {a p u d f : ℕ} (ha : 5 ≤ a) (hu : 1 ≤ u) (hd : 1 ≤ d)
    (hf : 1 ≤ f) (hp : 3 * (a * u * u * d) ≤ p)
    (hfactor : f ∣ a * u * u * d + 1) (hcong : a * u * d ∣ p + f) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨e, he⟩ := hfactor
  obtain ⟨c, hc⟩ := hcong
  let b := c * e - u
  have hau : 5 ≤ a * u * d := calc
    5 ≤ a := ha
    _ = a * 1 * 1 := by simp
    _ ≤ a * u * d := Nat.mul_le_mul (Nat.mul_le_mul_left a hu) hd
  have hauu : 5 ≤ a * u * u * d := calc
    5 ≤ a * u * d := hau
    _ = a * u * 1 * d := by simp
    _ ≤ a * u * u * d := Nat.mul_le_mul_right d (Nat.mul_le_mul_left (a * u) hu)
  have hapos : 0 < a * u * d := by omega
  have hppos : 0 < p := by omega
  have hepos : 0 < e := by
    by_contra! hn
    have : e = 0 := by omega
    simp [this] at he
  have hfbound : f ≤ p := by
    have hle : f * 1 ≤ f * e := Nat.mul_le_mul_left _ hepos
    rw [mul_one, ← he] at hle
    omega
  have hcu : 3 * u ≤ c := by
    apply Nat.le_of_mul_le_mul_left ?_ hapos
    calc
      (a * u * d) * (3 * u) = 3 * (a * u * u * d) := by ring
      _ ≤ p := hp
      _ ≤ (a * u * d) * c := by rw [← hc]; omega
  have hcpos : 0 < c := by omega
  have hc_lt : c < p := by
    have hm : 2 * c < (a * u * d) * c :=
      Nat.mul_lt_mul_of_pos_right (by omega) hcpos
    rw [← hc] at hm
    omega
  have hce : c ≤ c * e := by
    simpa only [mul_one] using Nat.mul_le_mul_left c (show 1 ≤ e from hepos)
  have hb : b + u = c * e := by dsimp [b]; omega
  have hub : u < b := by omega
  have hbpos : 0 < b := by omega
  have hcp : c < p * u := hc_lt.trans_le (by
    simpa only [mul_one] using Nat.mul_le_mul_left p hu)
  refine ⟨u * c * d, b * c * d, p * u * b * d,
    Nat.mul_pos (Nat.mul_pos hu hcpos) hd,
    Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_right hub hcpos) hd, ?_, ?_⟩
  · calc
      b * c * d < b * (p * u) * d :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hcp hbpos) hd
      _ = p * u * b * d := by ring
  · have heq : (a : ℚ) * u * u * d + 1 = f * e := by exact_mod_cast he
    have hcq : (p : ℚ) + f = a * u * d * c := by exact_mod_cast hc
    have hbq : (b : ℚ) + u = c * e := by exact_mod_cast hb
    have hmid : (a : ℚ) * u * b * d = p * e + 1 := by
      linear_combination (a : ℚ) * u * d * hbq - (e : ℚ) * hcq - heq
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hppos.ne'
    have huq : (u : ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
    have hc0 : (c : ℚ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hbpos.ne'
    have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    push_cast
    field_simp [hpq, huq, hc0, hb0, hd0]
    linear_combination (c : ℚ) * hmid - (p : ℚ) * hbq

private lemma type_two {a p u v d e : ℕ} (ha : 5 ≤ a) (hu : 1 ≤ u) (huv : u < v)
    (hd : 1 ≤ d) (hsum : e ∣ u + v) (hprod : a * u * v * d = p + e) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨t, ht⟩ := hsum
  have hvpos : 0 < v := by omega
  have htpos : 0 < t := by
    by_contra! ht0
    have : t = 0 := by omega
    simp [this] at ht
    omega
  have hel : e ≤ u + v := by
    simpa only [mul_one, ← ht] using Nat.mul_le_mul_left e (show 1 ≤ t from htpos)
  have h5 : 5 ≤ a * u * d := calc
    5 ≤ a := ha
    _ = a * 1 * 1 := by simp
    _ ≤ a * u * d := Nat.mul_le_mul (Nat.mul_le_mul_left a hu) hd
  have h5v : 5 * v ≤ p + e := calc
    5 * v ≤ (a * u * d) * v := Nat.mul_le_mul_right v h5
    _ = p + e := by rw [← hprod]; ring
  have hvp : v < p := by omega
  have hp0 : 0 < p := by omega
  have hvt : v < p * t := hvp.trans_le (by
    simpa only [mul_one] using Nat.mul_le_mul_left p (show 1 ≤ t from htpos))
  refine ⟨u * v * d, p * u * d * t, p * v * d * t,
    Nat.mul_pos (Nat.mul_pos hu hvpos) hd, ?_, ?_, ?_⟩
  · calc
      u * v * d < u * (p * t) * d :=
        Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left hvt hu) hd
      _ = p * u * d * t := by ring
  · exact Nat.mul_lt_mul_of_pos_right
      (Nat.mul_lt_mul_of_pos_right (Nat.mul_lt_mul_of_pos_left huv hp0) hd) htpos
  · have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    have huq : (u : ℚ) ≠ 0 := by exact_mod_cast (show u ≠ 0 by omega)
    have hvq : (v : ℚ) ≠ 0 := by exact_mod_cast hvpos.ne'
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    have htq : (t : ℚ) ≠ 0 := by exact_mod_cast htpos.ne'
    have hsq : (u : ℚ) + v = e * t := by exact_mod_cast ht
    have hmq : (a : ℚ) * u * v * d = p + e := by exact_mod_cast hprod
    push_cast
    field_simp [hpq, huq, hvq, hdq, htq]
    linear_combination (t : ℚ) * hmq - hsq

private lemma predecessor_divides {a p : ℕ} (ha : 5 ≤ a) (hp : 2 * a ≤ p)
    (h : a - 1 ∣ p + 1) :
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (a / p : ℚ) = 1 / x + 1 / y + 1 / z := by
  obtain ⟨v, hv⟩ := h
  have hv1 : 1 < v := by
    by_contra! hle
    have := Nat.mul_le_mul_left (a - 1) hle
    omega
  have heq : a * 1 * v * 1 = p + (1 + v) := by
    simp only [mul_one]
    calc
      a * v = (a - 1 + 1) * v := by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
      _ = p + (1 + v) := by rw [add_mul, one_mul, ← hv]; omega
  exact type_two ha (by decide) hv1 (by decide) (dvd_refl _) heq

private lemma residues_mod_420 {r : ℕ} (hr : r < 420) (hr60 : r % 60 = 1) (hr7 : r % 7 ≠ 0) :
    r = 1 ∨ r = 61 ∨ r = 121 ∨ r = 181 ∨ r = 241 ∨ r = 361 := by
  obtain ⟨k, hk, he⟩ : ∃ k ≤ 6, r = 60 * k + 1 := by
    refine ⟨r / 60, by omega, ?_⟩
    have := Nat.mod_add_div r 60
    omega
  subst r
  interval_cases k <;> first | decide | norm_num at hr7

private lemma five_residues {p : ℕ} (hp : 105 ≤ p) (hprime : p.Prime)
    (hr : 0 < p % 5 ∧ p % 5 + 2 < 5) :
    (∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (5 / p : ℚ) = 1 / x + 1 / y + 1 / z) ∨
      (p % 420 = 1 ∨ p % 420 = 121 ∨ p % 420 = 181 ∨ p % 420 = 361) := by
  have hp2 := (Nat.Prime.mod_two_eq_one_iff_ne_two hprime).2 (by omega)
  have not_dvd {r : ℕ} (hr2 : 2 ≤ r) (hrp : r < p) : ¬ r ∣ p :=
    fun hd => (ne_of_lt hrp) ((Nat.dvd_prime_two_le hprime hr2).1 hd)
  have hp3 : p % 3 ≠ 0 := fun h => not_dvd (by decide) (by omega : 3 < p)
    (Nat.dvd_of_mod_eq_zero h)
  have hp7 : p % 7 ≠ 0 := fun h => not_dvd (by decide) (by omega : 7 < p)
    (Nat.dvd_of_mod_eq_zero h)
  by_cases h5 : p % 5 = 2
  · left
    have h10 : p % 10 = 7 := by
      have hm2 := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 10)
      have hm5 := Nat.mod_mod_of_dvd p (by decide : 5 ∣ 10)
      omega
    have hm : 10 ∣ p + 3 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h10])
    obtain ⟨d, hd⟩ := hm
    exact type_two (a := 5) (u := 1) (v := 2) (d := d) (e := 3)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by omega)
  have h51 : p % 5 = 1 := by omega
  by_cases h3 : p % 3 = 2
  · left
    have h15 : p % 15 = 11 := by
      have hm3 := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 15)
      have hm5 := Nat.mod_mod_of_dvd p (by decide : 5 ∣ 15)
      omega
    have hm : 15 ∣ p + 4 := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h15])
    obtain ⟨d, hd⟩ := hm
    exact type_two (a := 5) (u := 1) (v := 3) (d := d) (e := 4)
      (by decide) (by decide) (by decide) (by omega) (by decide) (by omega)
  by_cases h4 : p % 4 = 3
  · exact Or.inl (predecessor_divides (a := 5) (by decide) (by omega)
      (Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h4])))
  have h41 : p % 4 = 1 := by
    have hm := Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4)
    omega
  have h31 : p % 3 = 1 := by omega
  have h60 : p % 60 = 1 := by
    have hm3 := Nat.mod_mod_of_dvd p (by decide : 3 ∣ 60)
    have hm4 := Nat.mod_mod_of_dvd p (by decide : 4 ∣ 60)
    have hm5 := Nat.mod_mod_of_dvd p (by decide : 5 ∣ 60)
    omega
  have cases420 : p % 420 = 1 ∨ p % 420 = 61 ∨ p % 420 = 121 ∨
      p % 420 = 181 ∨ p % 420 = 241 ∨ p % 420 = 361 := by
    have hm60 := Nat.mod_mod_of_dvd p (by decide : 60 ∣ 420)
    have hm7 := Nat.mod_mod_of_dvd p (by decide : 7 ∣ 420)
    exact residues_mod_420 (Nat.mod_lt _ (by decide)) (hm60.trans h60)
      (fun h => hp7 (hm7.symm.trans h))
  have hm35 := Nat.mod_mod_of_dvd p (by decide : 35 ∣ 420)
  rcases cases420 with h | h | h | h | h | h
  · exact Or.inr (Or.inl h)
  · left
    have h35 : p % 35 = 26 := by rw [h] at hm35; exact hm35.symm
    exact type_one (a := 5) (u := 1) (d := 7) (f := 9)
      (by decide) (by decide) (by decide) (by decide) (by omega) (by decide)
      (Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h35]))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · left
    have h35 : p % 35 = 31 := by rw [h] at hm35; exact hm35.symm
    exact type_one (a := 5) (u := 1) (d := 7) (f := 4)
      (by decide) (by decide) (by decide) (by decide) (by omega) (by decide)
      (Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, h35]))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- Remaining residue classes for numerator five. -/
def H1 : Prop :=
  ∀ᶠ p : ℕ in atTop, p.Prime →
    (p % 420 = 1 ∨ p % 420 = 121 ∨ p % 420 = 181 ∨ p % 420 = 361) →
    (∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (5 ∣ q + 1)) →
    ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
      (5 / p : ℚ) = 1 / x + 1 / y + 1 / z

/-- Larger numerators when the two divisibility criteria and the previous reductions fail. -/
def H2 : Prop :=
  ∀ a : ℕ, 6 ≤ a →
    ∀ᶠ p : ℕ in atTop, p.Prime → 0 < p % a ∧ p % a + 2 < a →
      (∀ q : ℕ, 2 ≤ q → q ≤ p → q ∣ p + 1 → ¬ (a ∣ q + 1)) →
      (¬ ∃ u d f : ℕ, 1 ≤ u ∧ 1 ≤ d ∧ 1 ≤ f ∧ 3 * (a * u * u * d) ≤ p ∧
        f ∣ a * u * u * d + 1 ∧ a * u * d ∣ p + f) →
      (¬ ∃ u v d e : ℕ, 1 ≤ u ∧ u < v ∧ 1 ≤ d ∧
        e ∣ u + v ∧ a * u * v * d = p + e) →
      ∃ x y z : ℕ, 1 ≤ x ∧ x < y ∧ y < z ∧
        (a / p : ℚ) = 1 / x + 1 / y + 1 / z

theorem main : H1 → H2 → OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1.H2 := by
  intro hFive hLarger a ha
  by_cases h5 : a = 5
  · subst a
    filter_upwards [hFive, eventually_ge_atTop (105 : ℕ)] with p hs hp hprime hr hq
    exact (five_residues hp hprime hr).elim id (fun h => hs hprime h hq)
  · filter_upwards [hLarger a (by omega)] with p hs hprime hr hq
    by_contra hn
    apply hn
    refine hs hprime hr hq ?_ ?_
    · rintro ⟨u, d, f, hu, hd, hf, hp, hfactor, hcong⟩
      exact hn (type_one ha hu hd hf hp hfactor hcong)
    · rintro ⟨u, v, d, e, hu, huv, hd, hsum, hprod⟩
      exact hn (type_two ha hu huv hd hsum hprod)

end OMA.R_Erdos242_erdos_242_variants_schinzel_generalization_R1_H1_R1_H2_R1
