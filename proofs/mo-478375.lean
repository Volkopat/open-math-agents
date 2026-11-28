import OMAStatements.S_mo_478375
import Mathlib

namespace OMA.S_mo_478375

open Polynomial

lemma full_period {l : ℕ} (hl : Odd l) {ω : ℂ} (hω : IsPrimitiveRoot ω l) :
    ∏ j ∈ Finset.range l, (X + C (ω ^ j)) = (X ^ l + 1 : ℂ[X]) := by
  have hpos : 0 < l := hl.pos
  have h1 := X_pow_sub_one_eq_prod hpos hω
  have himg : nthRootsFinset l (1 : ℂ) = (Finset.range l).image (fun j => ω ^ j) := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hz
      rw [mem_nthRootsFinset hpos]
      rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    · rw [hω.card_nthRootsFinset, Finset.card_image_of_injOn, Finset.card_range]
      intro i hi j hj h
      exact hω.pow_inj (by simpa using hi) (by simpa using hj) h
  rw [himg, Finset.prod_image (by
    intro i hi j hj h
    exact hω.pow_inj (by simpa using hi) (by simpa using hj) h)] at h1
  have h2 : (-X : ℂ[X]) ^ l - 1 = ∏ j ∈ Finset.range l, ((-X : ℂ[X]) - C (ω ^ j)) := by
    have := congrArg (fun p : ℂ[X] => p.comp (-X)) h1
    simpa [Polynomial.prod_comp] using this
  have h3 : ∏ j ∈ Finset.range l, ((-X : ℂ[X]) - C (ω ^ j)) =
      (-1) ^ l * ∏ j ∈ Finset.range l, (X + C (ω ^ j)) := by
    have e : ∀ j : ℕ, ((-X : ℂ[X]) - C (ω ^ j)) = (-1) * (X + C (ω ^ j)) := by
      intro j; ring
    simp_rw [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [h3, hl.neg_pow, hl.neg_one_pow] at h2
  linear_combination h2

lemma prod_period {l : ℕ} (hl : Odd l) {ω : ℂ} (hω : IsPrimitiveRoot ω l) (a c : ℕ) :
    ∏ j ∈ Finset.range (a * l + c), (X + C (ω ^ j)) =
      (X ^ l + 1 : ℂ[X]) ^ a * ∏ j ∈ Finset.range c, (X + C (ω ^ j)) := by
  induction a with
  | zero => simp
  | succ a ih =>
    have e : (a + 1) * l + c = l + (a * l + c) := by ring
    rw [e, Finset.prod_range_add, full_period hl hω]
    have e3 : ∀ x : ℕ, (X + C (ω ^ (l + x)) : ℂ[X]) = X + C (ω ^ x) := by
      intro x; rw [pow_add, hω.pow_eq_one, one_mul]
    simp_rw [e3]
    rw [ih]; ring

lemma coeff_split {l : ℕ} (hl : 0 < l) (F h : ℂ[X]) (hh : h.natDegree < l) (u v : ℕ) (hv : v < l) :
    (expand ℂ l F * h).coeff (l * u + v) = F.coeff u * h.coeff v := by
  rw [coeff_mul]
  rw [Finset.sum_eq_single (l * u, v)]
  · simp [coeff_expand hl, Nat.mul_div_cancel_left _ hl]
  · rintro ⟨i, j⟩ hij hne
    have hs : i + j = l * u + v := by simpa using hij
    by_cases hj : j < l
    · by_cases hd : l ∣ i
      · obtain ⟨t, rfl⟩ := hd
        have : t = u ∧ j = v := by
          have h1 : (l * t + j) / l = t := by
            rw [Nat.mul_add_div hl, Nat.div_eq_of_lt hj]; simp
          have h2 : (l * u + v) / l = u := by
            rw [Nat.mul_add_div hl, Nat.div_eq_of_lt hv]; simp
          have h3 : (l * t + j) % l = j := by
            rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hj
          have h4 : (l * u + v) % l = v := by
            rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hv
          rw [hs] at h1 h3
          exact ⟨by rw [← h1, h2], by rw [← h3, h4]⟩
        exact absurd (by rw [this.1, this.2]) hne
      · simp [coeff_expand hl, hd]
    · have : h.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  · intro h; simp at h

lemma gen_deg (q : ℂ) (c : ℕ) : (generating q c).natDegree ≤ c := by
  unfold generating
  refine (natDegree_prod_le _ _).trans ?_
  calc ∑ j ∈ Finset.range c, (X + C ((q ^ 2) ^ j) : ℂ[X]).natDegree
      = ∑ j ∈ Finset.range c, 1 := Finset.sum_congr rfl (fun j _ => natDegree_X_add_C _)
    _ ≤ c := by simp

lemma gen_coeff {l : ℕ} (hlodd : Odd l) {q : ℂ} (hq : IsPrimitiveRoot q l) (r s : ℕ) :
    (generating q r).coeff s =
      ((r / l).choose (s / l) : ℂ) * (generating q (r % l)).coeff (s % l) := by
  have hl : 0 < l := hlodd.pos
  have hcop : Nat.Coprime 2 l := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
    obtain ⟨k, hk⟩ := hlodd; omega
  have hω : IsPrimitiveRoot (q ^ 2) l := hq.pow_of_coprime 2 hcop
  have hr : r = (r / l) * l + r % l := by
    rw [mul_comm]; exact (Nat.div_add_mod r l).symm
  have hs : s = l * (s / l) + s % l := (Nat.div_add_mod s l).symm
  have key : generating q r = expand ℂ l ((X + 1) ^ (r / l)) * generating q (r % l) := by
    unfold generating
    conv_lhs => rw [hr]
    rw [prod_period hlodd hω]
    simp
  rw [key]
  conv_lhs => rw [hs]
  rw [coeff_split hl _ _ (lt_of_le_of_lt (gen_deg q _) (Nat.mod_lt _ hl)) _ _ (Nat.mod_lt _ hl)]
  rw [coeff_X_add_one_pow]

lemma main_aux : ∀ l : ℕ, 1 < l → Odd l → ∀ q : ℂ, IsPrimitiveRoot q l →
    ∀ r s : ℕ, s ≤ r → quantumBinom q r s =
      quantumBinom q (r % l) (s % l) * (Nat.choose (r / l) (s / l) : ℂ) := by
  intro l hl1 hlodd q hq r s hsr
  have hq0 : q ≠ 0 := hq.ne_zero (by omega)
  unfold quantumBinom
  rw [gen_coeff hlodd hq r s]
  have hexp : q ^ (((s : ℤ) - r) * ((r : ℤ) - 1)) =
      q ^ ((((s % l : ℕ) : ℤ) - ((r % l : ℕ) : ℤ)) * (((r % l : ℕ) : ℤ) - 1)) := by
    have hs : (s : ℤ) = l * ((s / l : ℕ) : ℤ) + ((s % l : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod s l).symm
    have hr : (r : ℤ) = l * ((r / l : ℕ) : ℤ) + ((r % l : ℕ) : ℤ) := by
      exact_mod_cast (Nat.div_add_mod r l).symm
    set A : ℤ := ((s / l : ℕ) : ℤ)
    set B : ℤ := ((r / l : ℕ) : ℤ)
    set v : ℤ := ((s % l : ℕ) : ℤ)
    set c : ℤ := ((r % l : ℕ) : ℤ)
    have hdvd : (l : ℤ) ∣ ((s : ℤ) - r) * ((r : ℤ) - 1) - (v - c) * (c - 1) := by
      refine ⟨(A - B) * (l * B + c - 1) + (v - c) * B, ?_⟩
      rw [hs, hr]; ring
    have h1 : q ^ ((((s : ℤ) - r) * ((r : ℤ) - 1)) - (v - c) * (c - 1)) = 1 :=
      (hq.zpow_eq_one_iff_dvd _).mpr hdvd
    rw [zpow_sub₀ hq0, div_eq_one_iff_eq (zpow_ne_zero _ hq0)] at h1
    exact h1
  rw [hexp]
  ring

end OMA.S_mo_478375

theorem OMA.solution : type_of% @OMA.S_mo_478375.main := OMA.S_mo_478375.main_aux
