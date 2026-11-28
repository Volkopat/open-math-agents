import OMAStatements.S_oeis_a380530

namespace OeisA380530

open OMA.S_oeis_a380530

/-! Step 1: Primorials and congruence invariance of primorial digits -/

private lemma radix_prime (j : ℕ) : (radix j).Prime :=
  Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime j

private lemma radix_strictMono : StrictMono radix :=
  Nat.nth_strictMono Nat.infinite_setOfPred_prime

private lemma radix_zero : radix 0 = 2 := Nat.nth_prime_zero_eq_two
private lemma radix_one : radix 1 = 3 := Nat.nth_prime_one_eq_three
private lemma radix_two : radix 2 = 5 := Nat.nth_prime_two_eq_five

private lemma radix_ge_seven {k : ℕ} (hk : 3 ≤ k) : 7 ≤ radix k := by
  have h5 : 5 < radix k := by
    rw [← radix_two]
    exact radix_strictMono (by omega)
  have hne6 : radix k ≠ 6 := by
    intro h6
    have hp := radix_prime k
    rw [h6] at hp
    exact absurd hp (by decide)
  omega

private lemma radix_odd {k : ℕ} (hk : 3 ≤ k) : radix k % 2 = 1 := by
  have h7 := radix_ge_seven hk
  have hp := radix_prime k
  rcases hp.eq_two_or_odd with h2 | hodd
  · omega
  · exact hodd

private lemma place_zero : place 0 = 1 := by
  simp [place]

private lemma place_succ (j : ℕ) : place (j + 1) = place j * radix j := by
  simp [place, Finset.prod_range_succ]

private lemma place_one : place 1 = 2 := by
  rw [place_succ, place_zero, radix_zero, one_mul]

private lemma place_two : place 2 = 6 := by
  rw [place_succ, place_one, radix_one]

private lemma place_three : place 3 = 30 := by
  rw [place_succ, place_two, radix_two]

private lemma place_pos (j : ℕ) : 0 < place j := by
  apply Finset.prod_pos
  intro i _
  exact (radix_prime i).pos

private lemma place_dvd_place {j k : ℕ} (h : j ≤ k) : place j ∣ place k :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

private lemma place_le_place {j k : ℕ} (h : j ≤ k) : place j ≤ place k :=
  Nat.le_of_dvd (place_pos k) (place_dvd_place h)

private lemma digit_mod_place_succ (m j : ℕ) :
    digit m j = digit (m % place (j + 1)) j := by
  unfold digit
  have hPpos : 0 < place j := place_pos j
  have hdiv : m = m % place (j + 1) + (m / place (j + 1)) * place (j + 1) := by
    have h := Nat.div_add_mod m (place (j + 1))
    linarith
  have hquot : m / place j = (m % place (j + 1)) / place j + (m / place (j + 1)) * radix j := by
    conv_lhs => rw [hdiv, place_succ]
    have hrew : m % (place j * radix j) + m / (place j * radix j) * (place j * radix j) =
        m % (place j * radix j) + (m / (place j * radix j) * radix j) * place j := by ring
    rw [hrew, Nat.add_mul_div_right _ _ hPpos, ← place_succ]
  rw [hquot, Nat.add_mul_mod_self_right]

private lemma digit_congr {m m' j : ℕ} (h : m ≡ m' [MOD place (j + 1)]) :
    digit m j = digit m' j := by
  rw [digit_mod_place_succ m j, digit_mod_place_succ m' j, h]

private lemma digit_of_modEq_one {m k j : ℕ} (h : m ≡ 1 [MOD place k]) (hj : j < k) :
    digit m j = if j = 0 then 1 else 0 := by
  have hmod : m ≡ 1 [MOD place (j + 1)] := h.of_dvd (place_dvd_place hj)
  rw [digit_congr hmod]
  unfold digit
  by_cases hj0 : j = 0
  · subst hj0
    rw [place_zero, radix_zero]
    decide
  · simp only [hj0, if_false]
    have hge : 2 ≤ place j := by
      rw [← place_one]
      exact place_le_place (by omega)
    have hdiv : 1 / place j = 0 := Nat.div_eq_of_lt (by omega)
    rw [hdiv, Nat.zero_mod]

private lemma digit_of_modEq_two {m k j : ℕ} (h : m ≡ 2 [MOD place k]) (hj : j < k) :
    digit m j = if j = 1 then 1 else 0 := by
  have hmod : m ≡ 2 [MOD place (j + 1)] := h.of_dvd (place_dvd_place hj)
  rw [digit_congr hmod]
  unfold digit
  by_cases hj0 : j = 0
  · subst hj0
    rw [place_zero, radix_zero]
    decide
  · by_cases hj1 : j = 1
    · subst hj1
      rw [place_one, radix_one]
      decide
    · simp only [hj1, if_false]
      have hge : 6 ≤ place j := by
        rw [← place_two]
        exact place_le_place (by omega)
      have hdiv : 2 / place j = 0 := Nat.div_eq_of_lt (by omega)
      rw [hdiv, Nat.zero_mod]

private lemma digit_of_modEq_two_add_mul {m k d : ℕ} (hk : 3 ≤ k)
    (h : m ≡ 2 + d * place k [MOD place (k + 1)]) :
    digit m k = d % radix k := by
  set r := d % radix k
  have hd : d = r + (d / radix k) * radix k := by
    have := Nat.div_add_mod d (radix k)
    dsimp only [r]
    linarith
  have hmod : 2 + d * place k ≡ 2 + r * place k [MOD place (k + 1)] := by
    have heq : 2 + d * place k = (2 + r * place k) + (d / radix k) * place (k + 1) := by
      rw [place_succ]
      conv_lhs => rw [hd]
      ring
    rw [Nat.ModEq, heq, Nat.add_mul_mod_self_right]
  rw [digit_congr (h.trans hmod)]
  unfold digit
  have hP30 : 30 ≤ place k := by
    rw [← place_three]
    exact place_le_place hk
  have hPpos : 0 < place k := place_pos k
  rw [Nat.add_mul_div_right _ _ hPpos, Nat.div_eq_of_lt (by omega : 2 < place k), zero_add]
  exact Nat.mod_eq_of_lt (Nat.mod_lt d (radix_prime k).pos)

/-! Step 2: Coprime target residue a_k = 1 + c * place k -/

private noncomputable def cParam (k : ℕ) : ℕ :=
  if place k % radix k ≠ 2 then (radix k - 1) / 2 else (radix k - 3) / 2

private noncomputable def aParam (k : ℕ) : ℕ :=
  1 + cParam k * place k

private lemma coprime_aParam {k : ℕ} (hk : 3 ≤ k) :
    Nat.Coprime (aParam k) (place (k + 1)) := by
  unfold place
  apply Nat.Coprime.prod_right
  intro i hi
  rw [Finset.mem_range] at hi
  rw [Nat.coprime_comm, (radix_prime i).coprime_iff_not_dvd]
  intro hdvd
  by_cases hik : i < k
  · have hpi_Pk : radix i ∣ place k :=
      Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hik)
    have hpi_mul : radix i ∣ cParam k * place k := dvd_mul_of_dvd_right hpi_Pk _
    have hpi_one : radix i ∣ 1 := (Nat.dvd_add_left hpi_mul).mp hdvd
    exact (radix_prime i).not_dvd_one hpi_one
  · have hiek : i = k := by omega
    subst hiek
    have h7 : 7 ≤ radix i := radix_ge_seven hk
    have hodd : radix i % 2 = 1 := radix_odd hk
    have h2ak : radix i ∣ 2 * aParam i := dvd_mul_of_dvd_right hdvd 2
    by_cases hcase : place i % radix i ≠ 2
    · have h2c : 2 * cParam i = radix i - 1 := by
        unfold cParam; rw [if_pos hcase]; omega
      have hid : 2 * aParam i + place i = 2 + radix i * place i := by
        unfold aParam
        have : 2 * (1 + cParam i * place i) + place i = 2 + (2 * cParam i + 1) * place i := by ring
        rw [this, h2c, Nat.sub_add_cancel (by omega)]
      have hmod1 : (2 * aParam i + place i) % radix i = place i % radix i := by
        rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd h2ak, zero_add, Nat.mod_mod]
      have hmod2 : (2 + radix i * place i) % radix i = 2 := by
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hid, hmod2] at hmod1
      exact hcase hmod1.symm
    · push Not at hcase
      have h2c : 2 * cParam i = radix i - 3 := by
        unfold cParam; rw [if_neg (not_not.mpr hcase)]; omega
      have hPeq : place i = radix i * (place i / radix i) + 2 := by
        have := Nat.div_add_mod (place i) (radix i)
        omega
      have hid : 2 * aParam i + 4 = radix i * ((radix i - 3) * (place i / radix i) + 2) := by
        unfold aParam
        have hstep1 : 2 * (1 + cParam i * place i) + 4 = 6 + (2 * cParam i) * place i := by ring
        conv_lhs => rw [hstep1, h2c, hPeq]
        zify [show 3 ≤ radix i by omega]
        ring
      have h4 : radix i ∣ 4 := by
        have hsum : radix i ∣ 2 * aParam i + 4 := ⟨(radix i - 3) * (place i / radix i) + 2, hid⟩
        exact (Nat.dvd_add_right h2ak).mp hsum
      have hle4 : radix i ≤ 4 := Nat.le_of_dvd (by decide) h4
      omega

private lemma threshold_cParam {k : ℕ} (hk : 3 ≤ k) :
    radix k ≤ 2 * ((2 * cParam k) % radix k) := by
  have h7 : 7 ≤ radix k := radix_ge_seven hk
  have hodd : radix k % 2 = 1 := radix_odd hk
  by_cases hcase : place k % radix k ≠ 2
  · have h2c : 2 * cParam k = radix k - 1 := by
      unfold cParam; rw [if_pos hcase]; omega
    rw [h2c, Nat.mod_eq_of_lt (by omega)]
    omega
  · push Not at hcase
    have h2c : 2 * cParam k = radix k - 3 := by
      unfold cParam; rw [if_neg (not_not.mpr hcase)]; omega
    rw [h2c, Nat.mod_eq_of_lt (by omega)]
    omega

/-! Step 3: Dirichlet witness n_k = 2 * q1 * q2 and exact evaluation value n_k = radix k -/

private lemma column_two_mul_primes {q1 q2 : ℕ}
    (hq1 : q1.Prime) (hq2 : q2.Prime) (h2q1 : 2 < q1) (hq12 : q1 < q2) (j : ℕ) :
    column (2 * q1 * q2) j =
      digit (q1 * q2) j + digit (2 * q2) j + digit (2 * q1) j := by
  have h2ne1 : (2 : ℕ) ≠ q1 := by omega
  have h2ne2 : (2 : ℕ) ≠ q2 := by omega
  have h1ne2 : q1 ≠ q2 := by omega
  have hq1_ne0 : q1 ≠ 0 := hq1.ne_zero
  have hq2_ne0 : q2 ≠ 0 := hq2.ne_zero
  have hpf : (2 * q1 * q2).primeFactors = {2, q1, q2} := by
    rw [Nat.primeFactors_mul (mul_ne_zero (by decide) hq1_ne0) hq2_ne0,
      Nat.primeFactors_mul (by decide) hq1_ne0,
      Nat.Prime.primeFactors Nat.prime_two,
      hq1.primeFactors, hq2.primeFactors]
    ext p
    simp
  have hf2 : (2 * q1 * q2).factorization 2 = 1 := by
    rw [Nat.factorization_mul (mul_ne_zero (by decide) hq1_ne0) hq2_ne0,
      Nat.factorization_mul (by decide) hq1_ne0]
    simp [Nat.Prime.factorization Nat.prime_two, hq1.factorization, hq2.factorization,
      h2ne1.symm, h2ne2.symm]
  have hfq1 : (2 * q1 * q2).factorization q1 = 1 := by
    rw [Nat.factorization_mul (mul_ne_zero (by decide) hq1_ne0) hq2_ne0,
      Nat.factorization_mul (by decide) hq1_ne0]
    simp [Nat.Prime.factorization Nat.prime_two, hq1.factorization, hq2.factorization,
      h2ne1, h1ne2.symm]
  have hfq2 : (2 * q1 * q2).factorization q2 = 1 := by
    rw [Nat.factorization_mul (mul_ne_zero (by decide) hq1_ne0) hq2_ne0,
      Nat.factorization_mul (by decide) hq1_ne0]
    simp [Nat.Prime.factorization Nat.prime_two, hq1.factorization, hq2.factorization,
      h2ne2, h1ne2]
  unfold column
  rw [hpf]
  rw [Finset.sum_insert (by simp [h2ne1, h2ne2]),
    Finset.sum_insert (by simp [h1ne2]),
    Finset.sum_singleton]
  rw [hf2, hfq1, hfq2]
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, zero_add, pow_one]
  have hd1 : 2 * q1 * q2 / 2 = q1 * q2 := by
    have : 2 * q1 * q2 = 2 * (q1 * q2) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by decide)]
  have hd2 : 2 * q1 * q2 / q1 = 2 * q2 := by
    have : 2 * q1 * q2 = q1 * (2 * q2) := by ring
    rw [this, Nat.mul_div_cancel_left _ hq1.pos]
  have hd3 : 2 * q1 * q2 / q2 = 2 * q1 := by
    rw [Nat.mul_div_cancel _ hq2.pos]
  rw [hd1, hd2, hd3]
  omega

private lemma exists_value_eq_radix {k : ℕ} (hk : 3 ≤ k) :
    ∃ n > 0, value n = radix k := by
  have hP_ne0 : place (k + 1) ≠ 0 := (place_pos (k + 1)).ne'
  have hcop := coprime_aParam hk
  obtain ⟨q1, h2q1, hq1_prime, hq1_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq 2 hP_ne0 hcop
  obtain ⟨q2, hq12, hq2_prime, hq2_mod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq q1 hP_ne0 hcop
  refine ⟨2 * q1 * q2, ?_, ?_⟩
  · have := hq1_prime.pos; have := hq2_prime.pos; positivity
  have hPk_dvd : place k ∣ place (k + 1) := place_dvd_place (Nat.le_succ k)
  have ha_mod_Pk : aParam k ≡ 1 [MOD place k] := by
    unfold aParam
    rw [Nat.ModEq, Nat.add_mul_mod_self_right]
  have hq1_Pk : q1 ≡ 1 [MOD place k] := (hq1_mod.of_dvd hPk_dvd).trans ha_mod_Pk
  have hq2_Pk : q2 ≡ 1 [MOD place k] := (hq2_mod.of_dvd hPk_dvd).trans ha_mod_Pk
  have hq12_Pk : q1 * q2 ≡ 1 [MOD place k] := by
    simpa using hq1_Pk.mul hq2_Pk
  have h2q1_Pk : 2 * q1 ≡ 2 [MOD place k] := by
    simpa using (Nat.ModEq.refl 2).mul hq1_Pk
  have h2q2_Pk : 2 * q2 ≡ 2 [MOD place k] := by
    simpa using (Nat.ModEq.refl 2).mul hq2_Pk
  have h2a_eq : 2 * aParam k = 2 + (2 * cParam k) * place k := by
    unfold aParam; ring
  have h2q1_Pkp : 2 * q1 ≡ 2 + (2 * cParam k) * place k [MOD place (k + 1)] := by
    rw [← h2a_eq]
    exact (Nat.ModEq.refl 2).mul hq1_mod
  have h2q2_Pkp : 2 * q2 ≡ 2 + (2 * cParam k) * place k [MOD place (k + 1)] := by
    rw [← h2a_eq]
    exact (Nat.ModEq.refl 2).mul hq2_mod
  have hcol_k : radix k ≤ column (2 * q1 * q2) k := by
    rw [column_two_mul_primes hq1_prime hq2_prime h2q1 hq12 k,
      digit_of_modEq_two_add_mul hk h2q2_Pkp,
      digit_of_modEq_two_add_mul hk h2q1_Pkp]
    have hthr := threshold_cParam hk
    omega
  have hcol_lt : ∀ j < k, column (2 * q1 * q2) j < radix j := by
    intro j hj
    rw [column_two_mul_primes hq1_prime hq2_prime h2q1 hq12 j,
      digit_of_modEq_one hq12_Pk hj,
      digit_of_modEq_two h2q2_Pk hj,
      digit_of_modEq_two h2q1_Pk hj]
    by_cases hj0 : j = 0
    · subst hj0; rw [radix_zero]; decide
    · by_cases hj1 : j = 1
      · subst hj1; rw [radix_one]; decide
      · simp only [hj0, hj1, if_false]
        exact (radix_prime j).pos
  have hex : ∃ j, radix j ≤ column (2 * q1 * q2) j := ⟨k, hcol_k⟩
  unfold value
  rw [dif_pos hex]
  have hfind : Nat.find hex = k := by
    apply le_antisymm
    · exact Nat.find_min' hex hcol_k
    · by_contra hlt
      push Not at hlt
      exact absurd (Nat.find_spec hex) (not_le.mpr (hcol_lt _ hlt))
  rw [hfind]

/-! Step 4: Unboundedness of value implies records.Infinite -/

theorem main_proof : records.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  let M : ℕ := (Finset.Icc 1 B).sup value
  let k : ℕ := max 3 (M + 1)
  have hk3 : 3 ≤ k := le_max_left 3 (M + 1)
  have hkM : M + 1 ≤ k := le_max_right 3 (M + 1)
  obtain ⟨nk, hnk_pos, hnk_val⟩ := exists_value_eq_radix hk3
  have hpk_ge : k ≤ radix k := radix_strictMono.id_le k
  have hex : ∃ m, 0 < m ∧ M < value m :=
    ⟨nk, hnk_pos, by rw [hnk_val]; omega⟩
  classical
  let m0 : ℕ := Nat.find hex
  have hm0_spec : 0 < m0 ∧ M < value m0 := Nat.find_spec hex
  have hm0_gt : B < m0 := by
    by_contra hle
    have hmem : m0 ∈ Finset.Icc 1 B := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hleM : value m0 ≤ M := Finset.le_sup (f := value) hmem
    omega
  refine ⟨m0, ?_, hm0_gt⟩
  refine ⟨hm0_spec.1, fun i hi_pos hi_lt => ?_⟩
  have hmin := Nat.find_min hex hi_lt
  have hleM : value i ≤ M := by
    by_contra hgt
    exact hmin ⟨hi_pos, by omega⟩
  omega

end OeisA380530

theorem OMA.solution : type_of% @OMA.S_oeis_a380530.main :=
  OeisA380530.main_proof
