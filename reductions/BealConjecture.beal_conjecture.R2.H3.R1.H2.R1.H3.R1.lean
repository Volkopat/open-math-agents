import OMAReductions.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1

/-! Factor the difference of two squares in Brown's (2,3,10)
classification. Coprimality leaves two integral cubic-fifth equations,
depending on the parity of the factors. Signed cube roots are retained,
including when a factor is zero. -/

namespace OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H3_R1

private theorem cube_parity (a : ℤ) : a ^ 3 % 2 = a % 2 := by
  rw [show a ^ 3 = (a * a) * a by ring, Int.mul_emod, Int.mul_emod a a]
  rcases Int.emod_two_eq_zero_or_one a with h | h <;> norm_num [h]

private theorem int_cube_of_natAbs {a : ℤ} {d : ℕ} (h : a.natAbs = d ^ 3) :
    ∃ x : ℤ, a = x ^ 3 := by
  have h' : (a.natAbs : ℤ) = (d : ℤ) ^ 3 := by exact_mod_cast h
  rw [Int.natCast_natAbs] at h'
  rcases le_or_gt 0 a with ha | ha
  · exact ⟨d, by simpa only [abs_of_nonneg ha] using h'⟩
  · rw [abs_of_neg ha] at h'
    refine ⟨-(d : ℤ), ?_⟩
    calc
      a = -(d : ℤ) ^ 3 := by linarith
      _ = (-(d : ℤ)) ^ 3 := by ring

private theorem cube_factors {a b c : ℤ} (hc : a.natAbs.Coprime b.natAbs)
    (h : a * b = c ^ 3) :
    ∃ u v : ℤ, a = u ^ 3 ∧ b = v ^ 3 ∧ u.natAbs.Coprime v.natAbs := by
  have hn : a.natAbs * b.natAbs = c.natAbs ^ 3 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs h
  have hu : IsUnit (gcd a.natAbs b.natAbs) := by
    change IsUnit (Nat.gcd a.natAbs b.natAbs)
    rw [hc.gcd_eq_one]
    exact isUnit_one
  have hv : IsUnit (gcd b.natAbs a.natAbs) := by rw [gcd_comm]; exact hu
  obtain ⟨i, hi⟩ := exists_eq_pow_of_mul_eq_pow hu hn
  obtain ⟨j, hj⟩ := exists_eq_pow_of_mul_eq_pow hv (by simpa only [mul_comm] using hn)
  obtain ⟨u, hu⟩ := int_cube_of_natAbs hi
  obtain ⟨v, hv⟩ := int_cube_of_natAbs hj
  refine ⟨u, v, hu, hv, ?_⟩
  rw [hu, hv, Int.natAbs_pow, Int.natAbs_pow] at hc
  exact (hc.of_dvd_left (dvd_pow_self _ (by decide : 3 ≠ 0))).of_dvd_right
    (dvd_pow_self _ (by decide : 3 ≠ 0))

private theorem coprime_xz {x y z : ℤ} (hc : x.natAbs.Coprime y.natAbs)
    (h : x ^ 2 + y ^ 3 = z ^ 10) : x.natAbs.Coprime z.natAbs := by
  by_contra hbad
  obtain ⟨p, hp, hpx, hpz⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hpy : (p : ℤ) ∣ y ^ 3 := by
    rw [show y ^ 3 = z ^ 10 - x ^ 2 by linarith]
    exact dvd_sub (dvd_pow (Int.natCast_dvd.mpr hpz) (by decide))
      (dvd_pow (Int.natCast_dvd.mpr hpx) (by decide))
  have hd : p ∣ y.natAbs ^ 3 := by
    simpa only [Int.natAbs_pow] using Int.natCast_dvd.mp hpy
  exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpx, hp.dvd_of_dvd_pow hd⟩) hc

private theorem coprime_from_sum_diff {a b u x z : ℤ}
    (hxz : x.natAbs.Coprime z.natAbs) (hau : a.natAbs.Coprime u.natAbs)
    (hs : a + b = u * z ^ 5) (hd : b - a = u * x) :
    a.natAbs.Coprime b.natAbs := by
  by_contra hbad
  obtain ⟨p, hp, hpa, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hpu : ¬ p ∣ u.natAbs := fun h ↦
    (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, hp, hpa, h⟩) hau
  have hsum : p ∣ u.natAbs * z.natAbs ^ 5 := by
    rw [← Int.natAbs_pow, ← Int.natAbs_mul, ← hs]
    exact Int.natCast_dvd.mp (dvd_add (Int.natCast_dvd.mpr hpa) (Int.natCast_dvd.mpr hpb))
  have hdiff : p ∣ u.natAbs * x.natAbs := by
    rw [← Int.natAbs_mul, ← hd]
    exact Int.natCast_dvd.mp (dvd_sub (Int.natCast_dvd.mpr hpb) (Int.natCast_dvd.mpr hpa))
  exact (Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p, hp, (hp.dvd_mul.mp hdiff).resolve_left hpu,
      hp.dvd_of_dvd_pow ((hp.dvd_mul.mp hsum).resolve_left hpu)⟩) hxz

private theorem scaled_cubes {a b c : ℤ} (hc : a.natAbs.Coprime b.natAbs)
    (ha : a % 2 = 1) (hb : b % 2 = 0) (h : a * b = 2 * c ^ 3) :
    ∃ u v : ℤ, a = u ^ 3 ∧ b = 2 * v ^ 3 ∧
      u.natAbs.Coprime v.natAbs ∧ u % 2 = 1 := by
  let d := b / 2
  have hd : b = 2 * d := by dsimp [d]; omega
  have hcd : a.natAbs.Coprime d.natAbs := by
    apply hc.of_dvd_right
    exact Int.natAbs_dvd_natAbs.mpr ⟨2, by rw [hd, mul_comm]⟩
  have hprod : a * d = c ^ 3 := by
    have he : 2 * (a * d) = 2 * c ^ 3 := by
      calc
        _ = a * b := by rw [hd]; ring
        _ = _ := h
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) he
  obtain ⟨u, v, hu, hv, huv⟩ := cube_factors hcd hprod
  exact ⟨u, v, hu, hd.trans (congrArg (fun x : ℤ ↦ 2 * x) hv), huv, by
    simpa only [hu, cube_parity] using ha⟩

/-- The two odd cube factors give a sum of cubes equal to twice a fifth power. -/
def H1 : Prop :=
  ∀ u v z : ℤ, u.natAbs.Coprime v.natAbs → u % 2 = 1 → v % 2 = 1 →
    u ^ 3 + v ^ 3 = 2 * z ^ 5 → (v ^ 3 - u ^ 3).natAbs ≤ 6

/-- For even factors the asymmetric cubic equation has coefficients one and two. -/
def H2 : Prop :=
  ∀ u v z : ℤ, u.natAbs.Coprime v.natAbs → u % 2 = 1 →
    u ^ 3 + 2 * v ^ 3 = z ^ 5 → (2 * v ^ 3 - u ^ 3).natAbs ≤ 3

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1.H3 := by
  intro hOdd hEven X Y Z hcop hEq
  have hxz := coprime_xz hcop hEq
  let A := Z ^ 5 - X
  let B := Z ^ 5 + X
  have hprod : A * B = Y ^ 3 := by
    dsimp [A, B]
    linear_combination -hEq
  have hsum : A + B = 2 * Z ^ 5 := by dsimp [A, B]; ring
  have hdiff : B - A = 2 * X := by dsimp [A, B]; ring
  have hmod : A % 2 = B % 2 := by
    have he : B = A + 2 * X := by linarith
    omega
  rcases Int.emod_two_eq_zero_or_one A with ha | ha
  · have hb : B % 2 = 0 := hmod.symm.trans ha
    let a := A / 2
    let b := B / 2
    let c := Y / 2
    have hA : A = 2 * a := by dsimp [a]; omega
    have hB : B = 2 * b := by dsimp [b]; omega
    have hy : Y % 2 = 0 := by
      rw [← cube_parity Y, ← hprod, Int.mul_emod, ha]
      simp
    have hY : Y = 2 * c := by dsimp [c]; omega
    have hs : a + b = Z ^ 5 := by rw [hA, hB] at hsum; omega
    have hd : b - a = X := by rw [hA, hB] at hdiff; omega
    have hab : a.natAbs.Coprime b.natAbs := by
      apply coprime_from_sum_diff (u := 1) hxz
      · simp
      · simpa using hs
      · simpa using hd
    have hbc : a * b = 2 * c ^ 3 := by
      apply mul_left_cancel₀ (by decide : (4 : ℤ) ≠ 0)
      calc
        _ = A * B := by rw [hA, hB]; ring
        _ = Y ^ 3 := hprod
        _ = _ := by rw [hY]; ring
    have hmodprod : (a * b) % 2 = 0 := by
      rw [hbc]
      omega
    rcases Int.emod_two_eq_zero_or_one a with ha0 | ha1 <;>
      rcases Int.emod_two_eq_zero_or_one b with hb0 | hb1
    · have hdiva : 2 ∣ a.natAbs := Int.natCast_dvd.mp (show (2 : ℤ) ∣ a from ⟨a / 2, by omega⟩)
      have hdivb : 2 ∣ b.natAbs := Int.natCast_dvd.mp (show (2 : ℤ) ∣ b from ⟨b / 2, by omega⟩)
      exact ((Nat.Prime.not_coprime_iff_dvd.mpr ⟨2, Nat.prime_two, hdiva, hdivb⟩) hab).elim
    · obtain ⟨u, v, hu, hv, huv, huOdd⟩ := scaled_cubes hab.symm hb1 ha0 (by simpa [mul_comm] using hbc)
      have hz : u ^ 3 + 2 * v ^ 3 = Z ^ 5 := by rw [← hu, ← hv, add_comm]; exact hs
      have h := hEven u v Z huv huOdd hz
      rw [← hv, ← hu, show a - b = -X by omega, Int.natAbs_neg] at h
      exact h
    · obtain ⟨u, v, hu, hv, huv, huOdd⟩ := scaled_cubes hab ha1 hb0 hbc
      have hz : u ^ 3 + 2 * v ^ 3 = Z ^ 5 := by rw [← hu, ← hv]; exact hs
      have h := hEven u v Z huv huOdd hz
      rwa [← hv, ← hu, hd] at h
    · rw [Int.mul_emod, ha1, hb1] at hmodprod
      norm_num at hmodprod
  · have hb : B % 2 = 1 := hmod.symm.trans ha
    have htwo : A.natAbs.Coprime (2 : ℤ).natAbs := by
      change A.natAbs.Coprime 2
      apply Nat.Coprime.symm
      apply Nat.prime_two.coprime_iff_not_dvd.mpr
      intro h
      have hAdiv : (2 : ℤ) ∣ A := Int.natCast_dvd.mpr h
      obtain ⟨d, hd⟩ := hAdiv
      omega
    have hAB := coprime_from_sum_diff hxz htwo hsum hdiff
    obtain ⟨u, v, hu, hv, huv⟩ := cube_factors hAB hprod
    have huOdd : u % 2 = 1 := by simpa only [hu, cube_parity] using ha
    have hvOdd : v % 2 = 1 := by simpa only [hv, cube_parity] using hb
    have hz : u ^ 3 + v ^ 3 = 2 * Z ^ 5 := by rwa [← hu, ← hv]
    have h := hOdd u v Z huv huOdd hvOdd hz
    rw [← hv, ← hu, hdiff, Int.natAbs_mul] at h
    change 2 * X.natAbs ≤ 6 at h
    omega

end OMA.R_BealConjecture_beal_conjecture_R2_H3_R1_H2_R1_H3_R1
