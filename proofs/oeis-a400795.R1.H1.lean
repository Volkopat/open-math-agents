import OMAReductions.R_oeis_a400795_R1

namespace A400795H1

theorem key (p g u v y : ℕ) (hp : p.Prime) (hp3 : 3 < p) (hmod : p % 3 = 1)
    (hsplit : ∀ d : ℕ, d ∣ 4*p+1 → d % 4 ≠ 3)
    (hrough : ∀ d : ℕ, 1 < d → d ≤ y → ¬ d ∣ 2*p-1)
    (hg : 0 < g) (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v)
    (ha : 1 < g * u) (hb : 1 < g * v)
    (he : 2*(2*p-1) = g^2*(u*v) + g*(u+v-1)) : y < g := by
  by_contra hle
  have hle : g ≤ y := by omega
  have hdiv : g ∣ 2*(2*p-1) := ⟨g*(u*v) + (u+v-1), by rw [he]; ring⟩
  have g12 : g = 1 ∨ g = 2 := by
    rcases Nat.even_or_odd g with ⟨h, hh⟩ | hgo
    · have h2 : h ∣ 2*p-1 := by
        have : 2*h ∣ 2*(2*p-1) := by rw [show 2*h = h+h by ring, ← hh]; exact hdiv
        exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
      by_cases h1 : h = 1
      · omega
      · exact absurd h2 (hrough h (by omega) (by omega))
    · have hnd : ¬ 2 ∣ g := by obtain ⟨k, rfl⟩ := hgo; omega
      have hc : Nat.Coprime g 2 := (Nat.prime_two.coprime_iff_not_dvd.mpr hnd).symm
      have h2 : g ∣ 2*p-1 := hc.dvd_of_dvd_mul_left hdiv
      by_cases h1 : g = 1
      · exact Or.inl h1
      · exact absurd h2 (hrough g (by omega) hle)
  rcases g12 with rfl | rfl
  · have hprod : (u+1)*(v+1) = 4*p := by
      have : 2*(2*p-1) + 2 = 4*p := by omega
      rw [← this, he]
      have huv : 1 ≤ u + v := by omega
      zify [huv]
      ring
    simp only [one_mul] at ha hb
    have hpd : p ∣ (u+1)*(v+1) := ⟨4, by rw [hprod]; ring⟩
    rcases (Nat.Prime.dvd_mul hp).mp hpd with ⟨c, hc⟩ | ⟨c, hc⟩
    · rw [hc] at hprod
      have hc4 : c * (v+1) = 4 := by
        have : p * (c * (v+1)) = p * 4 := by rw [← mul_assoc, hprod]; ring
        exact Nat.eq_of_mul_eq_mul_left hp.pos this
      have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc4)
      have hc1 : c = 1 := by nlinarith
      subst hc1
      have hv3 : v = 3 := by omega
      subst hv3
      have h3 : 3 ∣ u := by omega
      have := Nat.Coprime.coprime_dvd_left h3 hcop
      norm_num at this
    · rw [hc] at hprod
      have hc4 : c * (u+1) = 4 := by
        have : p * (c * (u+1)) = p * 4 := by rw [show p * 4 = 4 * p by ring, ← hprod]; ring
        exact Nat.eq_of_mul_eq_mul_left hp.pos this
      have hcpos : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hc4)
      have hc1 : c = 1 := by nlinarith
      subst hc1
      have hu3 : u = 3 := by omega
      subst hu3
      have h3 : 3 ∣ v := by omega
      have := Nat.Coprime.coprime_dvd_right h3 hcop
      norm_num at this
  · have hprod : (2*u+1)*(2*v+1) = 4*p+1 := by
      have huv : 1 ≤ u + v := by omega
      have : 2*(2*p-1) + 3 = 4*p+1 := by omega
      rw [← this, he]
      zify [huv]
      ring
    have h1 := hsplit (2*u+1) ⟨2*v+1, hprod.symm⟩
    have h2 := hsplit (2*v+1) ⟨2*u+1, by rw [← hprod]; ring⟩
    have hu2 : 2 ∣ u := by omega
    have hv2 : 2 ∣ v := by omega
    have h21 : 2 ∣ Nat.gcd u v := Nat.dvd_gcd hu2 hv2
    rw [hcop] at h21
    omega

theorem even_part (g u v : ℕ) (hu : 0 < u) (hv : 0 < v) (hcop : Nat.Coprime u v) :
    Even (g^2*(u*v) + g*(u+v-1)) := by
  have huv : 1 ≤ u + v := by omega
  have hnot : ¬ (Even u ∧ Even v) := by
    rintro ⟨h2u, h2v⟩
    have h21 : 2 ∣ Nat.gcd u v := Nat.dvd_gcd (even_iff_two_dvd.mp h2u) (even_iff_two_dvd.mp h2v)
    rw [hcop] at h21
    omega
  have hfact : g^2*(u*v) + g*(u+v-1) = g * (g*(u*v) + (u+v-1)) := by ring
  rw [hfact, Nat.even_mul, Nat.even_add, Nat.even_mul, Nat.even_mul, Nat.even_sub huv,
    Nat.even_add]
  simp only [Nat.not_even_one, iff_false]
  tauto

theorem solution_aux : OMA.R_oeis_a400795_R1.H1 := by
  intro p a b y hp hp3 hmod hsplit hrough ha hb ht
  obtain ⟨g, u, v, hg, hcop, rfl, rfl⟩ :=
    Nat.exists_coprime' (Nat.gcd_pos_of_pos_left b (by omega : 0 < a))
  have hgcd : Nat.gcd (u*g) (v*g) = g := by
    rw [Nat.gcd_mul_right, hcop, one_mul]
  have hu : 0 < u := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
  have hv : 0 < v := Nat.pos_of_ne_zero (by rintro rfl; simp at hb)
  have huv : 1 ≤ u + v := by omega
  have hident : u*g*(v*g) + u*g + v*g - g = g^2*(u*v) + g*(u+v-1) := by
    zify [huv, show g ≤ u*g*(v*g) + u*g + v*g by nlinarith]
    ring
  have he : 2*(2*p-1) = g^2*(u*v) + g*(u+v-1) := by
    unfold OMA.S_oeis_a400795.triangleCount at ht
    rw [hgcd, hident] at ht
    obtain ⟨r, hr⟩ := even_part g u v hu hv hcop
    rw [hr] at ht ⊢
    omega
  rw [hgcd]
  refine ⟨key p g u v y hp hp3 hmod hsplit hrough hg hu hv hcop
    (by rw [mul_comm]; exact ha) (by rw [mul_comm]; exact hb) he, u, v, hu, hv, he⟩

end A400795H1

theorem OMA.solution : OMA.R_oeis_a400795_R1.H1 := A400795H1.solution_aux
