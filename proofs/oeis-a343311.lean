import OMAStatements.S_oeis_a343311

/-!
Proof of OEIS A343311: a positive integer n is the sum of three distinct positive
integers dividing their product iff n is composite, > 1, and not in {4, 8, 9, 25}.
-/

private lemma not_8_of_odd_odd {a b c : ℕ} (hc : 0 < c)
    (hsum : a + b + c = 8) (hdvd : 8 ∣ a * b * c) (ha : a % 2 = 1) (hb : b % 2 = 1) : False := by
  have hcop : Nat.Coprime 8 (a * b) := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8]
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 3
    · exact (Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)).pow_left 3
  have h8c : 8 ∣ c := hcop.dvd_of_dvd_mul_left hdvd
  have hle := Nat.le_of_dvd hc h8c
  omega

private lemma not_sq_of_not_dvd_two {p a b c : ℕ} (hp : p.Prime) (hc : 0 < c)
    (hlt : c < p * p) (ha : ¬ p ∣ a) (hb : ¬ p ∣ b) (hd : p * p ∣ a * b * c) : False := by
  have hcop : Nat.Coprime (p * p) (a * b) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (hp.coprime_iff_not_dvd.mpr ha).mul_left (hp.coprime_iff_not_dvd.mpr ha)
    · exact (hp.coprime_iff_not_dvd.mpr hb).mul_left (hp.coprime_iff_not_dvd.mpr hb)
  have hpc : p * p ∣ c := hcop.dvd_of_dvd_mul_left hd
  have hle := Nat.le_of_dvd hc hpc
  omega

private lemma not_sq_prime {p x y z : ℕ} (hp : p.Prime) (hp5 : p ≤ 5)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hsum : x + y + z = p * p) (hdvd : p * p ∣ x * y * z) : False := by
  by_cases hpx : p ∣ x <;> by_cases hpy : p ∣ y <;> by_cases hpz : p ∣ z
  · obtain ⟨a, rfl⟩ := hpx
    obtain ⟨b, rfl⟩ := hpy
    obtain ⟨c, rfl⟩ := hpz
    have ha : 0 < a := Nat.pos_of_mul_pos_left hx
    have hb : 0 < b := Nat.pos_of_mul_pos_left hy
    have hc : 0 < c := Nat.pos_of_mul_pos_left hz
    have hab : a ≠ b := fun h => hxy (by rw [h])
    have hac : a ≠ c := fun h => hxz (by rw [h])
    have hbc : b ≠ c := fun h => hyz (by rw [h])
    have h6 : 6 ≤ a + b + c := by omega
    have hppos : 0 < p := hp.pos
    have hmul : p * (a + b + c) = p * p := by linarith
    have heq : a + b + c = p := mul_left_cancel₀ hppos.ne' hmul
    omega
  · exact hpz ((Nat.dvd_add_right (dvd_add hpx hpy)).mp (hsum ▸ dvd_mul_right p p))
  · exact hpy ((Nat.dvd_add_right (dvd_add hpx hpz)).mp
      ((show x + z + y = p * p by omega) ▸ dvd_mul_right p p))
  · exact not_sq_of_not_dvd_two hp hx (by omega) hpy hpz
      (by convert hdvd using 1; ring)
  · exact hpx ((Nat.dvd_add_right (dvd_add hpy hpz)).mp
      ((show y + z + x = p * p by omega) ▸ dvd_mul_right p p))
  · exact not_sq_of_not_dvd_two hp hy (by omega) hpx hpz
      (by convert hdvd using 1; ring)
  · exact not_sq_of_not_dvd_two hp hz (by omega) hpx hpy hdvd
  · exact not_sq_of_not_dvd_two hp hz (by omega) hpx hpy hdvd

theorem OMA.solution : type_of% @OMA.S_oeis_a343311.main := by
  intro n
  constructor
  · rintro ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz, hsum, hdvd⟩
    have hn6 : 6 ≤ n := by omega
    refine ⟨by omega, ?_, by omega, ?_, ?_, ?_⟩
    · intro hp
      have hdiv : n ∣ x ∨ n ∣ y ∨ n ∣ z := by
        rcases hp.dvd_mul.mp hdvd with hxy' | hz'
        · rcases hp.dvd_mul.mp hxy' with hx' | hy'
          · exact Or.inl hx'
          · exact Or.inr (Or.inl hy')
        · exact Or.inr (Or.inr hz')
      rcases hdiv with h | h | h
      · have := Nat.le_of_dvd hx h; omega
      · have := Nat.le_of_dvd hy h; omega
      · have := Nat.le_of_dvd hz h; omega
    · rintro rfl
      rcases Nat.mod_two_eq_zero_or_one x with hx2 | hx2 <;>
        rcases Nat.mod_two_eq_zero_or_one y with hy2 | hy2 <;>
        rcases Nat.mod_two_eq_zero_or_one z with hz2 | hz2
      · omega
      · omega
      · omega
      · exact not_8_of_odd_odd hx (by omega) (by convert hdvd using 1; ring) hy2 hz2
      · omega
      · exact not_8_of_odd_odd hy (by omega) (by convert hdvd using 1; ring) hx2 hz2
      · exact not_8_of_odd_odd hz hsum hdvd hx2 hy2
      · omega
    · rintro rfl
      exact not_sq_prime Nat.prime_three (by omega) hx hy hz hxy hxz hyz hsum hdvd
    · rintro rfl
      exact not_sq_prime (by norm_num : Nat.Prime 5) (by omega) hx hy hz hxy hxz hyz hsum hdvd
  · rintro ⟨h1, hprime, hn4, hn8, hn9, hn25⟩
    rcases Nat.mod_two_eq_zero_or_one n with hn2 | hn2
    · have hn_ne2 : n ≠ 2 := by
        rintro rfl
        exact hprime Nat.prime_two
      set k := n / 2
      have hk : 2 * k = n := by omega
      have hk3 : 3 ≤ k := by omega
      have hk4 : k ≠ 4 := by omega
      exact ⟨2, k, k - 2, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by rw [← hk]; exact dvd_mul_right _ _⟩
    · set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hpn : p ∣ n := Nat.minFac_dvd n
      have hp2 : p ≠ 2 := by
        rintro hp2eq
        rw [hp2eq] at hpn
        omega
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      set b := n / p
      have hnb : p * b = n := Nat.mul_div_cancel' hpn
      have hsq : p * p ≤ n := by
        simpa [sq] using Nat.minFac_sq_le_self (by omega) hprime
      have hpb_le : p ≤ b := by
        have : p * p ≤ p * b := by omega
        exact Nat.le_of_mul_le_mul_left this hp.pos
      by_cases hpb : p = b
      · have hnp : n = p * p := by rw [← hnb, hpb]
        have hp7 : 7 ≤ p := by
          by_contra hlt
          have hcases : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 := by omega
          rcases hcases with h | h | h | h <;> (rw [h] at hnp; omega)
        have hlt : 5 * p < n := by nlinarith
        refine ⟨p, 2 * p, n - 3 * p, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega, ?_⟩
        refine ⟨2 * (n - 3 * p), ?_⟩
        calc
          p * (2 * p) * (n - 3 * p) = (p * p) * (2 * (n - 3 * p)) := by ring
          _ = n * (2 * (n - 3 * p)) := by rw [← hnp]
      · have hlt_pb : p < b := by omega
        have hlt_bz : p + 2 * b < n := by nlinarith
        refine ⟨p, b, n - p - b, by omega, by omega, by omega,
          by omega, by omega, by omega, by omega, ?_⟩
        rw [← hnb]
        exact dvd_mul_right _ _
