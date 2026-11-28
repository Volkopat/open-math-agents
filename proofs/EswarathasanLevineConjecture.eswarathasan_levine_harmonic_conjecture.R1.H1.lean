import OMAReductions.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R1

-- The Eswarathasan-Levine conjecture for p = 2, 3, 5: J_2 is empty, J_3 = {2, 7, 22}, J_5 = {4, 20, 24}
-- (Eswarathasan and Levine, 1991).
-- Write |.| for the p-adic norm. p divides the numerator of q exactly when |q| < 1 (dvd_num_iff).
-- H_n - (1/p) H_(n / p) is a sum of 1/k with p not dividing k, so it has norm at most one (diff_norm).
-- Hence |H_n| < 1 gives |(1/p) H_(n/p)| <= 1, that is |H_(n/p)| <= 1/p < 1 (descent). So every element of
-- J_p above p arises from an element m of J_p as one of p m, ..., p m + p - 1, and J_p is found by evaluating
-- harmonic numbers level by level (lemmas v1 to v124, each one rational addition) until a level is empty.
-- For p = 2 the valuation of H_n is -log_2 n (Mathlib's padicValRat_two_harmonic).
-- This is the known theorem for three primes, not progress on the conjecture, which is open for general p.

namespace OMA.EswLev

theorem norm_inv (p : ℕ) [Fact p.Prime] (x : ℚ) : padicNorm p x⁻¹ = (padicNorm p x)⁻¹ := by
  rw [inv_eq_one_div, padicNorm.div, padicNorm.one, one_div]

/-- The harmonic number minus the part coming from multiples of `p` is `p`-integral. -/
theorem diff_norm (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicNorm p (harmonic n - (p : ℚ)⁻¹ * harmonic (n / p)) ≤ 1 := by
  have hp : p.Prime := Fact.out
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hd : p ∣ n + 1
    · have e1 : (n + 1) / p = n / p + 1 := Nat.succ_div_of_dvd hd
      have e2 : ((n + 1 : ℕ) : ℚ) = (p : ℚ) * ((n / p + 1 : ℕ) : ℚ) := by
        rw [← e1]
        exact_mod_cast (Nat.mul_div_cancel' hd).symm
      have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have e3 : harmonic (n + 1) - (p : ℚ)⁻¹ * harmonic ((n + 1) / p) =
          harmonic n - (p : ℚ)⁻¹ * harmonic (n / p) := by
        rw [e1, harmonic_succ, harmonic_succ, e2, mul_inv]
        ring
      rw [e3]
      exact ih
    · have e1 : (n + 1) / p = n / p := Nat.succ_div_of_not_dvd hd
      have e3 : harmonic (n + 1) - (p : ℚ)⁻¹ * harmonic ((n + 1) / p) =
          (harmonic n - (p : ℚ)⁻¹ * harmonic (n / p)) + ((n + 1 : ℕ) : ℚ)⁻¹ := by
        rw [e1, harmonic_succ]
        ring
      rw [e3]
      refine le_trans padicNorm.nonarchimedean (max_le ih ?_)
      rw [norm_inv, (padicNorm.nat_eq_one_iff (n + 1)).mpr hd, inv_one]

/-- Descent: if `p` divides the numerator of `H_n` (in norm form) and `n ≥ p`, the same holds for
`H_(n / p)`. -/
theorem descent (p : ℕ) [Fact p.Prime] (n : ℕ) (h : padicNorm p (harmonic n) < 1) :
    padicNorm p (harmonic (n / p)) < 1 := by
  have hp : p.Prime := Fact.out
  have h1 : padicNorm p ((p : ℚ)⁻¹ * harmonic (n / p)) ≤ 1 := by
    have e : (p : ℚ)⁻¹ * harmonic (n / p) =
        harmonic n - (harmonic n - (p : ℚ)⁻¹ * harmonic (n / p)) := by ring
    rw [e]
    exact le_trans (padicNorm.sub) (max_le h.le (diff_norm p n))
  rw [padicNorm.mul, norm_inv, padicNorm.padicNorm_p_of_prime, inv_inv] at h1
  have hp2 : (2 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp.two_le
  have hnn : 0 ≤ padicNorm p (harmonic (n / p)) := padicNorm.nonneg _
  nlinarith

/-- Membership in `J_p` in norm form. -/
theorem dvd_num_iff (p : ℕ) [Fact p.Prime] (q : ℚ) :
    (p : ℤ) ∣ q.num ↔ padicNorm p q < 1 := by
  have hp : p.Prime := Fact.out
  have hq : padicNorm p q = padicNorm p (q.num : ℚ) / padicNorm p (q.den : ℚ) := by
    rw [← padicNorm.div, Rat.num_div_den]
  constructor
  · intro h
    have h1 : padicNorm p (q.num : ℚ) < 1 := (padicNorm.int_lt_one_iff q.num).mpr h
    have h2 : ¬ p ∣ q.den := by
      intro hd
      have hcop : Nat.gcd q.num.natAbs q.den = 1 := q.reduced
      have h3 := Nat.dvd_gcd (Int.natCast_dvd.mp h) hd
      rw [hcop] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h3)
    rw [hq, (padicNorm.nat_eq_one_iff q.den).mpr h2, div_one]
    exact h1
  · intro h
    rw [hq] at h
    have hden0 : padicNorm p (q.den : ℚ) ≠ 0 :=
      padicNorm.nonzero (by exact_mod_cast q.den_nz)
    have hpos : 0 < padicNorm p (q.den : ℚ) := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hden0)
    have h1 : padicNorm p (q.num : ℚ) < padicNorm p (q.den : ℚ) := by
      rwa [div_lt_one hpos] at h
    exact (padicNorm.int_lt_one_iff q.num).mp (lt_of_lt_of_le h1 (padicNorm.of_nat _))

/-- A value `A / B` with `p` not dividing `A` has norm at least one. -/
theorem not_small (p : ℕ) [Fact p.Prime] (n A B : ℕ) (h : harmonic n = (A : ℚ) / (B : ℚ))
    (hB : B ≠ 0) (hA : ¬ p ∣ A) : ¬ padicNorm p (harmonic n) < 1 := by
  rw [h, padicNorm.div, (padicNorm.nat_eq_one_iff A).mpr hA]
  have hden0 : padicNorm p (B : ℚ) ≠ 0 := padicNorm.nonzero (by exact_mod_cast hB)
  have hpos : 0 < padicNorm p (B : ℚ) := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm hden0)
  rw [not_lt, le_div_iff₀ hpos, one_mul]
  exact padicNorm.of_nat _

theorem v1 : harmonic 1 = (1 : ℕ) / (1 : ℕ) := by
  norm_num [harmonic]
theorem v2 : harmonic 2 = (3 : ℕ) / (2 : ℕ) := by
  have e : harmonic 2 = harmonic 1 + ((2 : ℕ) : ℚ)⁻¹ := harmonic_succ 1
  rw [e, v1]
  norm_num
theorem v3 : harmonic 3 = (11 : ℕ) / (6 : ℕ) := by
  have e : harmonic 3 = harmonic 2 + ((3 : ℕ) : ℚ)⁻¹ := harmonic_succ 2
  rw [e, v2]
  norm_num
theorem v4 : harmonic 4 = (25 : ℕ) / (12 : ℕ) := by
  have e : harmonic 4 = harmonic 3 + ((4 : ℕ) : ℚ)⁻¹ := harmonic_succ 3
  rw [e, v3]
  norm_num
theorem v5 : harmonic 5 = (137 : ℕ) / (60 : ℕ) := by
  have e : harmonic 5 = harmonic 4 + ((5 : ℕ) : ℚ)⁻¹ := harmonic_succ 4
  rw [e, v4]
  norm_num
theorem v6 : harmonic 6 = (49 : ℕ) / (20 : ℕ) := by
  have e : harmonic 6 = harmonic 5 + ((6 : ℕ) : ℚ)⁻¹ := harmonic_succ 5
  rw [e, v5]
  norm_num
theorem v7 : harmonic 7 = (363 : ℕ) / (140 : ℕ) := by
  have e : harmonic 7 = harmonic 6 + ((7 : ℕ) : ℚ)⁻¹ := harmonic_succ 6
  rw [e, v6]
  norm_num
theorem v8 : harmonic 8 = (761 : ℕ) / (280 : ℕ) := by
  have e : harmonic 8 = harmonic 7 + ((8 : ℕ) : ℚ)⁻¹ := harmonic_succ 7
  rw [e, v7]
  norm_num
theorem v9 : harmonic 9 = (7129 : ℕ) / (2520 : ℕ) := by
  have e : harmonic 9 = harmonic 8 + ((9 : ℕ) : ℚ)⁻¹ := harmonic_succ 8
  rw [e, v8]
  norm_num
theorem v10 : harmonic 10 = (7381 : ℕ) / (2520 : ℕ) := by
  have e : harmonic 10 = harmonic 9 + ((10 : ℕ) : ℚ)⁻¹ := harmonic_succ 9
  rw [e, v9]
  norm_num
theorem v11 : harmonic 11 = (83711 : ℕ) / (27720 : ℕ) := by
  have e : harmonic 11 = harmonic 10 + ((11 : ℕ) : ℚ)⁻¹ := harmonic_succ 10
  rw [e, v10]
  norm_num
theorem v12 : harmonic 12 = (86021 : ℕ) / (27720 : ℕ) := by
  have e : harmonic 12 = harmonic 11 + ((12 : ℕ) : ℚ)⁻¹ := harmonic_succ 11
  rw [e, v11]
  norm_num
theorem v13 : harmonic 13 = (1145993 : ℕ) / (360360 : ℕ) := by
  have e : harmonic 13 = harmonic 12 + ((13 : ℕ) : ℚ)⁻¹ := harmonic_succ 12
  rw [e, v12]
  norm_num
theorem v14 : harmonic 14 = (1171733 : ℕ) / (360360 : ℕ) := by
  have e : harmonic 14 = harmonic 13 + ((14 : ℕ) : ℚ)⁻¹ := harmonic_succ 13
  rw [e, v13]
  norm_num
theorem v15 : harmonic 15 = (1195757 : ℕ) / (360360 : ℕ) := by
  have e : harmonic 15 = harmonic 14 + ((15 : ℕ) : ℚ)⁻¹ := harmonic_succ 14
  rw [e, v14]
  norm_num
theorem v16 : harmonic 16 = (2436559 : ℕ) / (720720 : ℕ) := by
  have e : harmonic 16 = harmonic 15 + ((16 : ℕ) : ℚ)⁻¹ := harmonic_succ 15
  rw [e, v15]
  norm_num
theorem v17 : harmonic 17 = (42142223 : ℕ) / (12252240 : ℕ) := by
  have e : harmonic 17 = harmonic 16 + ((17 : ℕ) : ℚ)⁻¹ := harmonic_succ 16
  rw [e, v16]
  norm_num
theorem v18 : harmonic 18 = (14274301 : ℕ) / (4084080 : ℕ) := by
  have e : harmonic 18 = harmonic 17 + ((18 : ℕ) : ℚ)⁻¹ := harmonic_succ 17
  rw [e, v17]
  norm_num
theorem v19 : harmonic 19 = (275295799 : ℕ) / (77597520 : ℕ) := by
  have e : harmonic 19 = harmonic 18 + ((19 : ℕ) : ℚ)⁻¹ := harmonic_succ 18
  rw [e, v18]
  norm_num
theorem v20 : harmonic 20 = (55835135 : ℕ) / (15519504 : ℕ) := by
  have e : harmonic 20 = harmonic 19 + ((20 : ℕ) : ℚ)⁻¹ := harmonic_succ 19
  rw [e, v19]
  norm_num
theorem v21 : harmonic 21 = (18858053 : ℕ) / (5173168 : ℕ) := by
  have e : harmonic 21 = harmonic 20 + ((21 : ℕ) : ℚ)⁻¹ := harmonic_succ 20
  rw [e, v20]
  norm_num
theorem v22 : harmonic 22 = (19093197 : ℕ) / (5173168 : ℕ) := by
  have e : harmonic 22 = harmonic 21 + ((22 : ℕ) : ℚ)⁻¹ := harmonic_succ 21
  rw [e, v21]
  norm_num
theorem v23 : harmonic 23 = (444316699 : ℕ) / (118982864 : ℕ) := by
  have e : harmonic 23 = harmonic 22 + ((23 : ℕ) : ℚ)⁻¹ := harmonic_succ 22
  rw [e, v22]
  norm_num
theorem v24 : harmonic 24 = (1347822955 : ℕ) / (356948592 : ℕ) := by
  have e : harmonic 24 = harmonic 23 + ((24 : ℕ) : ℚ)⁻¹ := harmonic_succ 23
  rw [e, v23]
  norm_num
theorem v25 : harmonic 25 = (34052522467 : ℕ) / (8923714800 : ℕ) := by
  have e : harmonic 25 = harmonic 24 + ((25 : ℕ) : ℚ)⁻¹ := harmonic_succ 24
  rw [e, v24]
  norm_num
theorem v26 : harmonic 26 = (34395742267 : ℕ) / (8923714800 : ℕ) := by
  have e : harmonic 26 = harmonic 25 + ((26 : ℕ) : ℚ)⁻¹ := harmonic_succ 25
  rw [e, v25]
  norm_num
theorem v27 : harmonic 27 = (312536252003 : ℕ) / (80313433200 : ℕ) := by
  have e : harmonic 27 = harmonic 26 + ((27 : ℕ) : ℚ)⁻¹ := harmonic_succ 26
  rw [e, v26]
  norm_num
theorem v28 : harmonic 28 = (315404588903 : ℕ) / (80313433200 : ℕ) := by
  have e : harmonic 28 = harmonic 27 + ((28 : ℕ) : ℚ)⁻¹ := harmonic_succ 27
  rw [e, v27]
  norm_num
theorem v29 : harmonic 29 = (9227046511387 : ℕ) / (2329089562800 : ℕ) := by
  have e : harmonic 29 = harmonic 28 + ((29 : ℕ) : ℚ)⁻¹ := harmonic_succ 28
  rw [e, v28]
  norm_num
theorem v30 : harmonic 30 = (9304682830147 : ℕ) / (2329089562800 : ℕ) := by
  have e : harmonic 30 = harmonic 29 + ((30 : ℕ) : ℚ)⁻¹ := harmonic_succ 29
  rw [e, v29]
  norm_num
theorem v31 : harmonic 31 = (290774257297357 : ℕ) / (72201776446800 : ℕ) := by
  have e : harmonic 31 = harmonic 30 + ((31 : ℕ) : ℚ)⁻¹ := harmonic_succ 30
  rw [e, v30]
  norm_num
theorem v32 : harmonic 32 = (586061125622639 : ℕ) / (144403552893600 : ℕ) := by
  have e : harmonic 32 = harmonic 31 + ((32 : ℕ) : ℚ)⁻¹ := harmonic_succ 31
  rw [e, v31]
  norm_num
theorem v33 : harmonic 33 = (53676090078349 : ℕ) / (13127595717600 : ℕ) := by
  have e : harmonic 33 = harmonic 32 + ((33 : ℕ) : ℚ)⁻¹ := harmonic_succ 32
  rw [e, v32]
  norm_num
theorem v34 : harmonic 34 = (54062195834749 : ℕ) / (13127595717600 : ℕ) := by
  have e : harmonic 34 = harmonic 33 + ((34 : ℕ) : ℚ)⁻¹ := harmonic_succ 33
  rw [e, v33]
  norm_num
theorem v35 : harmonic 35 = (54437269998109 : ℕ) / (13127595717600 : ℕ) := by
  have e : harmonic 35 = harmonic 34 + ((35 : ℕ) : ℚ)⁻¹ := harmonic_succ 34
  rw [e, v34]
  norm_num
theorem v36 : harmonic 36 = (54801925434709 : ℕ) / (13127595717600 : ℕ) := by
  have e : harmonic 36 = harmonic 35 + ((36 : ℕ) : ℚ)⁻¹ := harmonic_succ 35
  rw [e, v35]
  norm_num
theorem v37 : harmonic 37 = (2040798836801833 : ℕ) / (485721041551200 : ℕ) := by
  have e : harmonic 37 = harmonic 36 + ((37 : ℕ) : ℚ)⁻¹ := harmonic_succ 36
  rw [e, v36]
  norm_num
theorem v38 : harmonic 38 = (2053580969474233 : ℕ) / (485721041551200 : ℕ) := by
  have e : harmonic 38 = harmonic 37 + ((38 : ℕ) : ℚ)⁻¹ := harmonic_succ 37
  rw [e, v37]
  norm_num
theorem v39 : harmonic 39 = (2066035355155033 : ℕ) / (485721041551200 : ℕ) := by
  have e : harmonic 39 = harmonic 38 + ((39 : ℕ) : ℚ)⁻¹ := harmonic_succ 38
  rw [e, v38]
  norm_num
theorem v40 : harmonic 40 = (2078178381193813 : ℕ) / (485721041551200 : ℕ) := by
  have e : harmonic 40 = harmonic 39 + ((40 : ℕ) : ℚ)⁻¹ := harmonic_succ 39
  rw [e, v39]
  norm_num
theorem v41 : harmonic 41 = (85691034670497533 : ℕ) / (19914562703599200 : ℕ) := by
  have e : harmonic 41 = harmonic 40 + ((41 : ℕ) : ℚ)⁻¹ := harmonic_succ 40
  rw [e, v40]
  norm_num
theorem v42 : harmonic 42 = (12309312989335019 : ℕ) / (2844937529085600 : ℕ) := by
  have e : harmonic 42 = harmonic 41 + ((42 : ℕ) : ℚ)⁻¹ := harmonic_succ 41
  rw [e, v41]
  norm_num
theorem v43 : harmonic 43 = (532145396070491417 : ℕ) / (122332313750680800 : ℕ) := by
  have e : harmonic 43 = harmonic 42 + ((43 : ℕ) : ℚ)⁻¹ := harmonic_succ 42
  rw [e, v42]
  norm_num
theorem v44 : harmonic 44 = (5884182435213075787 : ℕ) / (1345655451257488800 : ℕ) := by
  have e : harmonic 44 = harmonic 43 + ((44 : ℕ) : ℚ)⁻¹ := harmonic_succ 43
  rw [e, v43]
  norm_num
theorem v45 : harmonic 45 = (5914085889685464427 : ℕ) / (1345655451257488800 : ℕ) := by
  have e : harmonic 45 = harmonic 44 + ((45 : ℕ) : ℚ)⁻¹ := harmonic_succ 44
  rw [e, v44]
  norm_num
theorem v46 : harmonic 46 = (5943339269060627227 : ℕ) / (1345655451257488800 : ℕ) := by
  have e : harmonic 46 = harmonic 45 + ((46 : ℕ) : ℚ)⁻¹ := harmonic_succ 45
  rw [e, v45]
  norm_num
theorem v47 : harmonic 47 = (280682601097106968469 : ℕ) / (63245806209101973600 : ℕ) := by
  have e : harmonic 47 = harmonic 46 + ((47 : ℕ) : ℚ)⁻¹ := harmonic_succ 46
  rw [e, v46]
  norm_num
theorem v48 : harmonic 48 = (282000222059796592919 : ℕ) / (63245806209101973600 : ℕ) := by
  have e : harmonic 48 = harmonic 47 + ((48 : ℕ) : ℚ)⁻¹ := harmonic_succ 47
  rw [e, v47]
  norm_num
theorem v49 : harmonic 49 = (13881256687139135026631 : ℕ) / (3099044504245996706400 : ℕ) := by
  have e : harmonic 49 = harmonic 48 + ((49 : ℕ) : ℚ)⁻¹ := harmonic_succ 48
  rw [e, v48]
  norm_num
theorem v50 : harmonic 50 = (13943237577224054960759 : ℕ) / (3099044504245996706400 : ℕ) := by
  have e : harmonic 50 = harmonic 49 + ((50 : ℕ) : ℚ)⁻¹ := harmonic_succ 49
  rw [e, v49]
  norm_num
theorem v51 : harmonic 51 = (14004003155738682347159 : ℕ) / (3099044504245996706400 : ℕ) := by
  have e : harmonic 51 = harmonic 50 + ((51 : ℕ) : ℚ)⁻¹ := harmonic_succ 50
  rw [e, v50]
  norm_num
theorem v52 : harmonic 52 = (14063600165435720745359 : ℕ) / (3099044504245996706400 : ℕ) := by
  have e : harmonic 52 = harmonic 51 + ((52 : ℕ) : ℚ)⁻¹ := harmonic_succ 51
  rw [e, v51]
  norm_num
theorem v53 : harmonic 53 = (748469853272339196210427 : ℕ) / (164249358725037825439200 : ℕ) := by
  have e : harmonic 53 = harmonic 52 + ((53 : ℕ) : ℚ)⁻¹ := harmonic_succ 52
  rw [e, v52]
  norm_num
theorem v54 : harmonic 54 = (250503836021181200128409 : ℕ) / (54749786241679275146400 : ℕ) := by
  have e : harmonic 54 = harmonic 53 + ((54 : ℕ) : ℚ)⁻¹ := harmonic_succ 53
  rw [e, v53]
  norm_num
theorem v55 : harmonic 55 = (251499286680120823312889 : ℕ) / (54749786241679275146400 : ℕ) := by
  have e : harmonic 55 = harmonic 54 + ((55 : ℕ) : ℚ)⁻¹ := harmonic_succ 54
  rw [e, v54]
  norm_num
theorem v56 : harmonic 56 = (252476961434436524654789 : ℕ) / (54749786241679275146400 : ℕ) := by
  have e : harmonic 56 = harmonic 55 + ((56 : ℕ) : ℚ)⁻¹ := harmonic_succ 55
  rw [e, v55]
  norm_num
theorem v57 : harmonic 57 = (253437484000080020709989 : ℕ) / (54749786241679275146400 : ℕ) := by
  have e : harmonic 57 = harmonic 56 + ((57 : ℕ) : ℚ)⁻¹ := harmonic_succ 56
  rw [e, v56]
  norm_num
theorem v58 : harmonic 58 = (254381445831833111660789 : ℕ) / (54749786241679275146400 : ℕ) := by
  have e : harmonic 58 = harmonic 57 + ((58 : ℕ) : ℚ)⁻¹ := harmonic_succ 57
  rw [e, v57]
  norm_num
theorem v59 : harmonic 59 = (15063255090319832863132951 : ℕ) / (3230237388259077233637600 : ℕ) := by
  have e : harmonic 59 = harmonic 58 + ((59 : ℕ) : ℚ)⁻¹ := harmonic_succ 58
  rw [e, v58]
  norm_num
theorem v60 : harmonic 60 = (15117092380124150817026911 : ℕ) / (3230237388259077233637600 : ℕ) := by
  have e : harmonic 60 = harmonic 59 + ((60 : ℕ) : ℚ)⁻¹ := harmonic_succ 59
  rw [e, v59]
  norm_num
theorem v61 : harmonic 61 = (925372872575832277072279171 : ℕ) / (197044480683803711251893600 : ℕ) := by
  have e : harmonic 61 = harmonic 60 + ((61 : ℕ) : ℚ)⁻¹ := harmonic_succ 60
  rw [e, v60]
  norm_num
theorem v62 : harmonic 62 = (928551009361054917576341971 : ℕ) / (197044480683803711251893600 : ℕ) := by
  have e : harmonic 62 = harmonic 61 + ((62 : ℕ) : ℚ)⁻¹ := harmonic_succ 61
  rw [e, v61]
  norm_num
theorem v63 : harmonic 63 = (310559566510213034489743057 : ℕ) / (65681493561267903750631200 : ℕ) := by
  have e : harmonic 63 = harmonic 62 + ((63 : ℕ) : ℚ)⁻¹ := harmonic_succ 62
  rw [e, v62]
  norm_num
theorem v64 : harmonic 64 = (623171679694215690971693339 : ℕ) / (131362987122535807501262400 : ℕ) := by
  have e : harmonic 64 = harmonic 63 + ((64 : ℕ) : ℚ)⁻¹ := harmonic_succ 63
  rw [e, v63]
  norm_num
theorem v65 : harmonic 65 = (625192648726870088010174299 : ℕ) / (131362987122535807501262400 : ℕ) := by
  have e : harmonic 65 = harmonic 64 + ((65 : ℕ) : ℚ)⁻¹ := harmonic_succ 64
  rw [e, v64]
  norm_num
theorem v66 : harmonic 66 = (209060999005535159677640233 : ℕ) / (43787662374178602500420800 : ℕ) := by
  have e : harmonic 66 = harmonic 65 + ((66 : ℕ) : ℚ)⁻¹ := harmonic_succ 65
  rw [e, v65]
  norm_num
theorem v67 : harmonic 67 = (14050874595745034300902316411 : ℕ) / (2933773379069966367528193600 : ℕ) := by
  have e : harmonic 67 = harmonic 66 + ((67 : ℕ) : ℚ)⁻¹ := harmonic_succ 66
  rw [e, v66]
  norm_num
theorem v68 : harmonic 68 = (14094018321907827923954201611 : ℕ) / (2933773379069966367528193600 : ℕ) := by
  have e : harmonic 68 = harmonic 67 + ((68 : ℕ) : ℚ)⁻¹ := harmonic_succ 67
  rw [e, v67]
  norm_num
theorem v69 : harmonic 69 = (42409610330030873613929048033 : ℕ) / (8801320137209899102584580800 : ℕ) := by
  have e : harmonic 69 = harmonic 68 + ((69 : ℕ) : ℚ)⁻¹ := harmonic_succ 68
  rw [e, v68]
  norm_num
theorem v70 : harmonic 70 = (42535343474848157886823113473 : ℕ) / (8801320137209899102584580800 : ℕ) := by
  have e : harmonic 70 = harmonic 69 + ((70 : ℕ) : ℚ)⁻¹ := harmonic_succ 69
  rw [e, v69]
  norm_num
theorem v71 : harmonic 71 = (3028810706851429109067025637383 : ℕ) / (624893729741902836283505236800 : ℕ) := by
  have e : harmonic 71 = harmonic 70 + ((71 : ℕ) : ℚ)⁻¹ := harmonic_succ 70
  rw [e, v70]
  norm_num
theorem v72 : harmonic 72 = (9112469359293533278712889630349 : ℕ) / (1874681189225708508850515710400 : ℕ) := by
  have e : harmonic 72 = harmonic 71 + ((72 : ℕ) : ℚ)⁻¹ := harmonic_succ 71
  rw [e, v71]
  norm_num
theorem v73 : harmonic 73 = (667084944417653637854891458725877 : ℕ) / (136851726813476721146087646859200 : ℕ) := by
  have e : harmonic 73 = harmonic 72 + ((73 : ℕ) : ℚ)⁻¹ := harmonic_succ 72
  rw [e, v72]
  norm_num
theorem v74 : harmonic 74 = (668934292077295215167676426926677 : ℕ) / (136851726813476721146087646859200 : ℕ) := by
  have e : harmonic 74 = harmonic 73 + ((74 : ℕ) : ℚ)⁻¹ := harmonic_succ 73
  rw [e, v73]
  norm_num
theorem v75 : harmonic 75 = (670758981768141571449624262218133 : ℕ) / (136851726813476721146087646859200 : ℕ) := by
  have e : harmonic 75 = harmonic 74 + ((75 : ℕ) : ℚ)⁻¹ := harmonic_succ 74
  rw [e, v74]
  norm_num
theorem v76 : harmonic 76 = (672559662384108370412072783887333 : ℕ) / (136851726813476721146087646859200 : ℕ) := by
  have e : harmonic 76 = harmonic 75 + ((76 : ℕ) : ℚ)⁻¹ := harmonic_succ 75
  rw [e, v75]
  norm_num
theorem v77 : harmonic 77 = (61303359776139104182852056677903 : ℕ) / (12441066073952429195098876987200 : ℕ) := by
  have e : harmonic 77 = harmonic 76 + ((77 : ℕ) : ℚ)⁻¹ := harmonic_succ 76
  rw [e, v76]
  norm_num
theorem v78 : harmonic 78 = (61462860623241058403302042280303 : ℕ) / (12441066073952429195098876987200 : ℕ) := by
  have e : harmonic 78 = harmonic 77 + ((78 : ℕ) : ℚ)⁻¹ := harmonic_succ 77
  rw [e, v77]
  norm_num
theorem v79 : harmonic 79 = (4868007055309996043055960217131137 : ℕ) / (982844219842241906412811281988800 : ℕ) := by
  have e : harmonic 79 = harmonic 78 + ((79 : ℕ) : ℚ)⁻¹ := harmonic_succ 78
  rw [e, v78]
  norm_num
theorem v80 : harmonic 80 = (4880292608058024066886120358155997 : ℕ) / (982844219842241906412811281988800 : ℕ) := by
  have e : harmonic 80 = harmonic 79 + ((80 : ℕ) : ℚ)⁻¹ := harmonic_succ 79
  rw [e, v79]
  norm_num
theorem v81 : harmonic 81 = (44031838385838021258243173365847173 : ℕ) / (8845597978580177157715301537899200 : ℕ) := by
  have e : harmonic 81 = harmonic 80 + ((81 : ℕ) : ℚ)⁻¹ := harmonic_succ 80
  rw [e, v80]
  norm_num
theorem v82 : harmonic 82 = (44139711531918267321142140457772773 : ℕ) / (8845597978580177157715301537899200 : ℕ) := by
  have e : harmonic 82 = harmonic 81 + ((82 : ℕ) : ℚ)⁻¹ := harmonic_succ 81
  rw [e, v81]
  norm_num
theorem v83 : harmonic 83 = (3672441655127796364812512959533039359 : ℕ) / (734184632222154704090370027645633600 : ℕ) := by
  have e : harmonic 83 = harmonic 82 + ((83 : ℕ) : ℚ)⁻¹ := harmonic_succ 82
  rw [e, v82]
  norm_num
theorem v84 : harmonic 84 = (3681181948368536301765969745576439759 : ℕ) / (734184632222154704090370027645633600 : ℕ) := by
  have e : harmonic 84 = harmonic 83 + ((84 : ℕ) : ℚ)⁻¹ := harmonic_succ 83
  rw [e, v83]
  norm_num
theorem v85 : harmonic 85 = (3689819414629973415931738804725211919 : ℕ) / (734184632222154704090370027645633600 : ℕ) := by
  have e : harmonic 85 = harmonic 84 + ((85 : ℕ) : ℚ)⁻¹ := harmonic_succ 84
  rw [e, v84]
  norm_num
theorem v86 : harmonic 86 = (3698356445237207772956045432953649519 : ℕ) / (734184632222154704090370027645633600 : ℕ) := by
  have e : harmonic 86 = harmonic 85 + ((86 : ℕ) : ℚ)⁻¹ := harmonic_succ 85
  rw [e, v85]
  norm_num
theorem v87 : harmonic 87 = (3706795349055853229324900260857622319 : ℕ) / (734184632222154704090370027645633600 : ℕ) := by
  have e : harmonic 87 = harmonic 86 + ((87 : ℕ) : ℚ)⁻¹ := harmonic_succ 86
  rw [e, v86]
  norm_num
theorem v88 : harmonic 88 = (40866521918642154860585199122889549709 : ℕ) / (8076030954443701744994070304101969600 : ℕ) := by
  have e : harmonic 88 = harmonic 87 + ((88 : ℕ) : ℚ)⁻¹ := harmonic_succ 87
  rw [e, v87]
  norm_num
theorem v89 : harmonic 89 = (3645196481713595484337076792241271893701 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 89 = harmonic 88 + ((89 : ℕ) : ℚ)⁻¹ := harmonic_succ 88
  rw [e, v88]
  norm_num
theorem v90 : harmonic 90 = (3653182778990767589396015372875328285861 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 90 = harmonic 89 + ((90 : ℕ) : ℚ)⁻¹ := harmonic_succ 89
  rw [e, v89]
  norm_num
theorem v91 : harmonic 91 = (3661081314759399341652108474601318124261 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 91 = harmonic 90 + ((91 : ℕ) : ℚ)⁻¹ := harmonic_succ 90
  rw [e, v90]
  norm_num
theorem v92 : harmonic 92 = (3668893996878372053122809260004199377461 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 92 = harmonic 91 + ((92 : ℕ) : ℚ)⁻¹ := harmonic_succ 91
  rw [e, v91]
  norm_num
theorem v93 : harmonic 93 = (3676622671662732154792749821908124918261 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 93 = harmonic 92 + ((93 : ℕ) : ℚ)⁻¹ := harmonic_succ 92
  rw [e, v92]
  norm_num
theorem v94 : harmonic 94 = (3684269126502577787295988888472646995861 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 94 = harmonic 93 + ((94 : ℕ) : ℚ)⁻¹ := harmonic_succ 93
  rw [e, v93]
  norm_num
theorem v95 : harmonic 95 = (3691835092344109255246562280652279367381 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 95 = harmonic 94 + ((95 : ℕ) : ℚ)⁻¹ := harmonic_succ 94
  rw [e, v94]
  norm_num
theorem v96 : harmonic 96 = (3699322246041458103739317199996707235031 : ℕ) / (718766754945489455304472257065075294400 : ℕ) := by
  have e : harmonic 96 = harmonic 95 + ((96 : ℕ) : ℚ)⁻¹ := harmonic_succ 95
  rw [e, v95]
  norm_num
theorem v97 : harmonic 97 = (359553024620966925518018240656745677092407 : ℕ) / (69720375229712477164533808935312303556800 : ℕ) := by
  have e : harmonic 97 = harmonic 96 + ((97 : ℕ) : ℚ)⁻¹ := harmonic_succ 96
  rw [e, v96]
  norm_num
theorem v98 : harmonic 98 = (360264457021270114060513483605065190394007 : ℕ) / (69720375229712477164533808935312303556800 : ℕ) := by
  have e : harmonic 98 = harmonic 97 + ((98 : ℕ) : ℚ)⁻¹ := harmonic_succ 97
  rw [e, v97]
  norm_num
theorem v99 : harmonic 99 = (360968703235711654233892612988250163157207 : ℕ) / (69720375229712477164533808935312303556800 : ℕ) := by
  have e : harmonic 99 = harmonic 98 + ((99 : ℕ) : ℚ)⁻¹ := harmonic_succ 98
  rw [e, v98]
  norm_num
theorem v100 : harmonic 100 = (14466636279520351160221518043104131447711 : ℕ) / (2788815009188499086581352357412492142272 : ℕ) := by
  have e : harmonic 100 = harmonic 99 + ((100 : ℕ) : ℚ)⁻¹ := harmonic_succ 99
  rw [e, v99]
  norm_num
theorem v101 : harmonic 101 = (1463919079240743966268954674710929768361083 : ℕ) / (281670315928038407744716588098661706369472 : ℕ) := by
  have e : harmonic 101 = harmonic 100 + ((101 : ℕ) : ℚ)⁻¹ := harmonic_succ 100
  rw [e, v100]
  norm_num
theorem v102 : harmonic 102 = (1466680552926312970266451896162877432149019 : ℕ) / (281670315928038407744716588098661706369472 : ℕ) := by
  have e : harmonic 102 = harmonic 101 + ((102 : ℕ) : ℚ)⁻¹ := harmonic_succ 101
  rw [e, v101]
  norm_num
theorem v103 : harmonic 103 = (151349767267338274345189261892875037217718429 : ℕ) / (29012042540587955997705808574162155756055616 : ℕ) := by
  have e : harmonic 103 = harmonic 102 + ((103 : ℕ) : ℚ)⁻¹ := harmonic_succ 102
  rw [e, v102]
  norm_num
theorem v104 : harmonic 104 = (151628729214843927768244125436857365638449733 : ℕ) / (29012042540587955997705808574162155756055616 : ℕ) := by
  have e : harmonic 104 = harmonic 103 + ((104 : ℕ) : ℚ)⁻¹ := harmonic_succ 103
  rw [e, v103]
  norm_num
theorem v105 : harmonic 105 = (759525171909485731983968522830675502275870361 : ℕ) / (145060212702939779988529042870810778780278080 : ℕ) := by
  have e : harmonic 105 = harmonic 104 + ((105 : ℕ) : ℚ)⁻¹ := harmonic_succ 104
  rw [e, v104]
  norm_num
theorem v106 : harmonic 106 = (760893664482154975191407476065305792641722041 : ℕ) / (145060212702939779988529042870810778780278080 : ℕ) := by
  have e : harmonic 106 = harmonic 105 + ((106 : ℕ) : ℚ)⁻¹ := harmonic_succ 105
  rw [e, v105]
  norm_num
theorem v107 : harmonic 107 = (81560682312293522125469128981858530591444536467 : ℕ) / (15521442759214556458772607587176753329489754560 : ℕ) := by
  have e : harmonic 107 = harmonic 106 + ((107 : ℕ) : ℚ)⁻¹ := harmonic_succ 106
  rw [e, v106]
  norm_num
theorem v108 : harmonic 108 = (81704399374878842092679986459517574603754626787 : ℕ) / (15521442759214556458772607587176753329489754560 : ℕ) := by
  have e : harmonic 108 = harmonic 107 + ((108 : ℕ) : ℚ)⁻¹ := harmonic_succ 107
  rw [e, v107]
  norm_num
theorem v109 : harmonic 109 = (8921300974621008344560891131674592385138744074343 : ℕ) / (1691837260754386654006214227002266112914383247040 : ℕ) := by
  have e : harmonic 109 = harmonic 108 + ((109 : ℕ) : ℚ)⁻¹ := harmonic_succ 108
  rw [e, v108]
  norm_num
theorem v110 : harmonic 110 = (812425573941376284756780362571245808659649778037 : ℕ) / (153803387341307877636928566091115101174034840640 : ℕ) := by
  have e : harmonic 110 = harmonic 109 + ((110 : ℕ) : ℚ)⁻¹ := harmonic_succ 109
  rw [e, v109]
  norm_num
theorem v111 : harmonic 111 = (813811190043550229600356295599093692454010452277 : ℕ) / (153803387341307877636928566091115101174034840640 : ℕ) := by
  have e : harmonic 111 = harmonic 110 + ((111 : ℕ) : ℚ)⁻¹ := harmonic_succ 110
  rw [e, v110]
  norm_num
theorem v112 : harmonic 112 = (815184434573383335650686014939192934428778620497 : ℕ) / (153803387341307877636928566091115101174034840640 : ℕ) := by
  have e : harmonic 112 = harmonic 111 + ((112 : ℕ) : ℚ)⁻¹ := harmonic_succ 111
  rw [e, v111]
  norm_num
theorem v113 : harmonic 113 = (92269644494133624806164448254219916691626018956801 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 113 = harmonic 112 + ((113 : ℕ) : ℚ)⁻¹ := harmonic_succ 112
  rw [e, v112]
  norm_num
theorem v114 : harmonic 114 = (92422098728954394895401052885520758853316071035681 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 114 = harmonic 113 + ((114 : ℕ) : ℚ)⁻¹ := harmonic_succ 113
  rw [e, v113]
  norm_num
theorem v115 : harmonic 115 = (92573227274776723505600817476549419778817513966049 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 115 = harmonic 114 + ((115 : ℕ) : ℚ)⁻¹ := harmonic_succ 114
  rw [e, v114]
  norm_num
theorem v116 : harmonic 116 = (92723052988307480317436790993517488799788772043569 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 116 = harmonic 115 + ((116 : ℕ) : ℚ)⁻¹ := harmonic_succ 115
  rw [e, v115]
  norm_num
theorem v117 : harmonic 117 = (92871598140184128096692969865041386290666258684529 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 117 = harmonic 116 + ((117 : ℕ) : ℚ)⁻¹ := harmonic_succ 116
  rw [e, v116]
  norm_num
theorem v118 : harmonic 118 = (93018884434841482250701215017315081260434614082769 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 118 = harmonic 117 + ((118 : ℕ) : ℚ)⁻¹ := harmonic_succ 117
  rw [e, v117]
  norm_num
theorem v119 : harmonic 119 = (93164933029543732588289222815367988877515840444049 : ℕ) / (17379782769567790172972927968296006432665936992320 : ℕ) := by
  have e : harmonic 119 = harmonic 118 + ((119 : ℕ) : ℚ)⁻¹ := harmonic_succ 118
  rw [e, v118]
  norm_num
theorem v120 : harmonic 120 = (18661952910524692834612799443020757786224277983797 : ℕ) / (3475956553913558034594585593659201286533187398464 : ℕ) := by
  have e : harmonic 120 = harmonic 119 + ((120 : ℕ) : ℚ)⁻¹ := harmonic_succ 119
  rw [e, v119]
  norm_num
theorem v121 : harmonic 121 = (2261572258727401391022743318199170893419670823437901 : ℕ) / (420590743023540522185944856832763355670515675214144 : ℕ) := by
  have e : harmonic 121 = harmonic 120 + ((121 : ℕ) : ℚ)⁻¹ := harmonic_succ 120
  rw [e, v120]
  norm_num
theorem v122 : harmonic 122 = (2265019723834151723171808439976488625843199640447853 : ℕ) / (420590743023540522185944856832763355670515675214144 : ℕ) := by
  have e : harmonic 122 = harmonic 121 + ((122 : ℕ) : ℚ)⁻¹ := harmonic_succ 121
  rw [e, v121]
  norm_num
theorem v123 : harmonic 123 = (2268439160769302459124539698975128978328325784148781 : ℕ) / (420590743023540522185944856832763355670515675214144 : ℕ) := by
  have e : harmonic 123 = harmonic 122 + ((123 : ℕ) : ℚ)⁻¹ := harmonic_succ 122
  rw [e, v122]
  norm_num
theorem v124 : harmonic 124 = (2271831021600137463335716673627006102164378329916637 : ℕ) / (420590743023540522185944856832763355670515675214144 : ℕ) := by
  have e : harmonic 124 = harmonic 123 + ((124 : ℕ) : ℚ)⁻¹ := harmonic_succ 123
  rw [e, v123]
  norm_num

instance fact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
instance fact5 : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

theorem n3_1 : ¬ padicNorm 3 (harmonic 1) < 1 :=
  not_small 3 1 _ _ v1 (by norm_num) (by norm_num)
theorem n3_6 : ¬ padicNorm 3 (harmonic 6) < 1 :=
  not_small 3 6 _ _ v6 (by norm_num) (by norm_num)
theorem n3_8 : ¬ padicNorm 3 (harmonic 8) < 1 :=
  not_small 3 8 _ _ v8 (by norm_num) (by norm_num)
theorem n3_21 : ¬ padicNorm 3 (harmonic 21) < 1 :=
  not_small 3 21 _ _ v21 (by norm_num) (by norm_num)
theorem n3_23 : ¬ padicNorm 3 (harmonic 23) < 1 :=
  not_small 3 23 _ _ v23 (by norm_num) (by norm_num)
theorem n3_66 : ¬ padicNorm 3 (harmonic 66) < 1 :=
  not_small 3 66 _ _ v66 (by norm_num) (by norm_num)
theorem n3_67 : ¬ padicNorm 3 (harmonic 67) < 1 :=
  not_small 3 67 _ _ v67 (by norm_num) (by norm_num)
theorem n3_68 : ¬ padicNorm 3 (harmonic 68) < 1 :=
  not_small 3 68 _ _ v68 (by norm_num) (by norm_num)

theorem tree3 (n : ℕ) (hn : 1 ≤ n) (h : padicNorm 3 (harmonic n) < 1) : n = 2 ∨ n = 7 ∨ n = 22 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h3 : n < 3
    · have hc : n = 1 ∨ n = 2 := by omega
      rcases hc with rfl | rfl
      · exact absurd h n3_1
      · exact Or.inl rfl
    · have hd := descent 3 n h
      have hm := ih (n / 3) (by omega) (by omega) hd
      have hc : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 66 ∨ n = 67 ∨ n = 68 := by
        omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd h n3_6
      · exact Or.inr (Or.inl rfl)
      · exact absurd h n3_8
      · exact absurd h n3_21
      · exact Or.inr (Or.inr rfl)
      · exact absurd h n3_23
      · exact absurd h n3_66
      · exact absurd h n3_67
      · exact absurd h n3_68

theorem n5_1 : ¬ padicNorm 5 (harmonic 1) < 1 :=
  not_small 5 1 _ _ v1 (by norm_num) (by norm_num)
theorem n5_2 : ¬ padicNorm 5 (harmonic 2) < 1 :=
  not_small 5 2 _ _ v2 (by norm_num) (by norm_num)
theorem n5_3 : ¬ padicNorm 5 (harmonic 3) < 1 :=
  not_small 5 3 _ _ v3 (by norm_num) (by norm_num)
theorem n5_21 : ¬ padicNorm 5 (harmonic 21) < 1 :=
  not_small 5 21 _ _ v21 (by norm_num) (by norm_num)
theorem n5_22 : ¬ padicNorm 5 (harmonic 22) < 1 :=
  not_small 5 22 _ _ v22 (by norm_num) (by norm_num)
theorem n5_23 : ¬ padicNorm 5 (harmonic 23) < 1 :=
  not_small 5 23 _ _ v23 (by norm_num) (by norm_num)
theorem n5_100 : ¬ padicNorm 5 (harmonic 100) < 1 :=
  not_small 5 100 _ _ v100 (by norm_num) (by norm_num)
theorem n5_101 : ¬ padicNorm 5 (harmonic 101) < 1 :=
  not_small 5 101 _ _ v101 (by norm_num) (by norm_num)
theorem n5_102 : ¬ padicNorm 5 (harmonic 102) < 1 :=
  not_small 5 102 _ _ v102 (by norm_num) (by norm_num)
theorem n5_103 : ¬ padicNorm 5 (harmonic 103) < 1 :=
  not_small 5 103 _ _ v103 (by norm_num) (by norm_num)
theorem n5_104 : ¬ padicNorm 5 (harmonic 104) < 1 :=
  not_small 5 104 _ _ v104 (by norm_num) (by norm_num)
theorem n5_120 : ¬ padicNorm 5 (harmonic 120) < 1 :=
  not_small 5 120 _ _ v120 (by norm_num) (by norm_num)
theorem n5_121 : ¬ padicNorm 5 (harmonic 121) < 1 :=
  not_small 5 121 _ _ v121 (by norm_num) (by norm_num)
theorem n5_122 : ¬ padicNorm 5 (harmonic 122) < 1 :=
  not_small 5 122 _ _ v122 (by norm_num) (by norm_num)
theorem n5_123 : ¬ padicNorm 5 (harmonic 123) < 1 :=
  not_small 5 123 _ _ v123 (by norm_num) (by norm_num)
theorem n5_124 : ¬ padicNorm 5 (harmonic 124) < 1 :=
  not_small 5 124 _ _ v124 (by norm_num) (by norm_num)

theorem tree5 (n : ℕ) (hn : 1 ≤ n) (h : padicNorm 5 (harmonic n) < 1) : n = 4 ∨ n = 20 ∨ n = 24 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h5 : n < 5
    · have hc : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 := by omega
      rcases hc with rfl | rfl | rfl | rfl
      · exact absurd h n5_1
      · exact absurd h n5_2
      · exact absurd h n5_3
      · exact Or.inl rfl
    · have hd := descent 5 n h
      have hm := ih (n / 5) (by omega) (by omega) hd
      have hc : n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 100 ∨ n = 101 ∨ n = 102 ∨
          n = 103 ∨ n = 104 ∨ n = 120 ∨ n = 121 ∨ n = 122 ∨ n = 123 ∨ n = 124 := by
        omega
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact absurd h n5_21
      · exact absurd h n5_22
      · exact absurd h n5_23
      · exact Or.inr (Or.inr rfl)
      · exact absurd h n5_100
      · exact absurd h n5_101
      · exact absurd h n5_102
      · exact absurd h n5_103
      · exact absurd h n5_104
      · exact absurd h n5_120
      · exact absurd h n5_121
      · exact absurd h n5_122
      · exact absurd h n5_123
      · exact absurd h n5_124

theorem finite3 : (EswarathasanLevineConjecture.harmonicNumDivisibleSet 3).Finite := by
  refine Set.Finite.subset (Set.toFinite ({2, 7, 22} : Set ℕ)) ?_
  intro n hn
  obtain ⟨h1, h2⟩ := hn
  have h := tree3 n h1 ((dvd_num_iff 3 (harmonic n)).mp h2)
  simpa using h

theorem finite5 : (EswarathasanLevineConjecture.harmonicNumDivisibleSet 5).Finite := by
  refine Set.Finite.subset (Set.toFinite ({4, 20, 24} : Set ℕ)) ?_
  intro n hn
  obtain ⟨h1, h2⟩ := hn
  have h := tree5 n h1 ((dvd_num_iff 5 (harmonic n)).mp h2)
  simpa using h

theorem empty2 : (EswarathasanLevineConjecture.harmonicNumDivisibleSet 2).Finite := by
  have h : EswarathasanLevineConjecture.harmonicNumDivisibleSet 2 = ∅ := by
    ext n
    constructor
    · rintro ⟨h1, h2⟩
      exfalso
      have hpos : 0 < harmonic n := harmonic_pos (by omega)
      have hlt := (dvd_num_iff 2 (harmonic n)).mp h2
      have hv := padicValRat_two_harmonic n
      have hne : harmonic n ≠ 0 := hpos.ne'
      rw [padicNorm.eq_zpow_of_nonzero hne, hv, neg_neg] at hlt
      have : (1 : ℚ) ≤ (2 : ℚ) ^ ((Nat.log 2 n : ℕ) : ℤ) := by
        rw [zpow_natCast]
        exact one_le_pow₀ (by norm_num)
      exact absurd hlt (not_lt.mpr (by exact_mod_cast this))
    · intro h
      exact absurd h (Set.notMem_empty n)
  rw [h]
  exact Set.finite_empty

end OMA.EswLev

theorem OMA.solution :
    OMA.R_EswarathasanLevineConjecture_eswarathasan_levine_harmonic_conjecture_R1.H1 := by
  intro p hp h7
  have hc : p = 2 ∨ p = 3 ∨ p = 5 := by
    interval_cases p
    · exact absurd hp (by norm_num)
    · exact absurd hp (by norm_num)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hp (by norm_num)
    · exact Or.inr (Or.inr rfl)
    · exact absurd hp (by norm_num)
  rcases hc with rfl | rfl | rfl
  · exact OMA.EswLev.empty2
  · exact OMA.EswLev.finite3
  · exact OMA.EswLev.finite5
