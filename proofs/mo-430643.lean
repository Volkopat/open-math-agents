import OMAStatements.S_mo_430643

/-! A proof of Pablo Spiga's arithmetic inequality.
Taking logarithms reduces the problem to a quadratic inequality. We prove this
term by term except on the prime supports {2,3} and {2,3,5}, where rational
lower bounds for the logarithms suffice. -/

section
namespace Mo430643
open Finset

noncomputable def ell (p : ℕ) : ℝ := Real.logb 2 (p : ℝ)
noncomputable def S (s : Finset ℕ) (a : ℕ → ℕ) : ℝ := ∑ p ∈ s, (a p : ℝ)*ell p
noncomputable def F (s : Finset ℕ) (a : ℕ → ℕ) : ℝ :=
  (S s a)^2 - 4*((s.card : ℝ)-1)*S s a - ∑ p ∈ s, (a p : ℝ)^2*ell p

end Mo430643
end

section
namespace Mo430643
open Finset Real

private theorem log_four_le {p : ℕ} (h : 4≤p) : 2 ≤ Real.logb 2 p := by
  apply (Real.le_logb_iff_rpow_le (by norm_num : 1 < (2:ℝ)) (by positivity : 0 < (p:ℝ))).mpr
  norm_num
  exact_mod_cast h

private theorem extend_support {s b : Finset ℕ} (hb : b ⊆ s)
    (h0 : 2*(b.card:ℝ)-1 ≤ ∑ p ∈ b, Real.logb 2 p)
    (hg : ∀ p ∈ s \ b, 4 ≤ p) :
    2*(s.card:ℝ)-1 ≤ ∑ p ∈ s, Real.logb 2 p := by
  have h := sum_le_sum (s := s \ b) (g := fun (p : ℕ) => Real.logb 2 (p:ℝ))
    (fun p hp => log_four_le (hg p hp))
  have eqsum := sum_sdiff hb (f := fun p : ℕ => Real.logb 2 (p:ℝ))
  have eqcard : (((s \ b).card:ℕ):ℝ) + b.card = s.card := by exact_mod_cast card_sdiff_add_card_eq_card hb
  simp only [sum_const, nsmul_eq_mul] at h
  linarith

theorem normal_support (s : Finset ℕ) (hp : ∀ p ∈ s, p.Prime)
    (h23 : s ≠ {2,3}) (h235 : s ≠ {2,3,5}) :
    2*(s.card:ℝ)-1 ≤ ∑ p ∈ s, Real.logb 2 p := by
  have prime_small {p : ℕ} (hps : p ∈ s) (h4 : p < 4) : p = 2 ∨ p = 3 := by
    have := (hp _ hps).two_le
    omega
  have hlog2 := Real.logb_self_eq_one (by norm_num : 1<(2:ℝ))
  have hlog3 : (1:ℝ) ≤ Real.logb 2 3 := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) (by norm_num)]; norm_num
  by_cases h2s : 2 ∈ s
  · by_cases h3s : 3 ∈ s
    · obtain ⟨p,hps,h7⟩ : ∃ p ∈ s, 7 ≤ p := by
        by_contra! hh
        have hmem (n : ℕ) (hn : n∈s) : n=2 ∨ n=3 ∨ n=5 := by
          have h := hh n hn
          have q := hp n hn
          interval_cases n <;> norm_num at *
        by_cases h5 : 5 ∈ s
        · apply h235
          ext n
          simp only [mem_insert,mem_singleton]
          exact ⟨hmem n, by rintro (rfl|rfl|rfl) <;> assumption⟩
        · apply h23
          ext n
          simp only [mem_insert,mem_singleton]
          constructor
          · intro hn; rcases hmem _ hn with h|h|rfl <;> tauto
          · rintro (rfl|rfl) <;> assumption
      have hlog : 5 ≤ Real.logb 2 (2*3*(p:ℝ)) := by
        rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
        norm_num
        have : (7:ℝ) ≤ p := by exact_mod_cast h7
        linarith
      rw [Real.logb_mul (by norm_num : (2*3 : ℝ) ≠ 0) (by positivity),Real.logb_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)] at hlog
      apply extend_support (b := {2,3,p})
      · intro j hj; simp only [mem_insert,mem_singleton] at hj; rcases hj with rfl|rfl|rfl <;> assumption
      · have h2p : (2:ℕ) ≠ p := by omega
        have h3p : (3:ℕ) ≠ p := by omega
        simp [h2p,h3p] at hlog ⊢; linarith
      · intro q hq
        obtain ⟨hq,hn⟩ := mem_sdiff.mp hq
        by_contra! h4
        rcases prime_small hq h4 with rfl|rfl <;> simp at hn
    · apply extend_support (b := {2})
      · simpa using h2s
      · norm_num [Real.logb_self_eq_one]
      · intro p hh
        obtain ⟨hh,hn⟩ := mem_sdiff.mp hh
        by_contra! h4
        rcases prime_small hh h4 with rfl|rfl <;> simp_all
  · by_cases h3s : 3 ∈ s
    · apply extend_support (b := {3})
      · simpa using h3s
      · simp; linarith
      · intro p hh
        obtain ⟨hh,hn⟩ := mem_sdiff.mp hh
        by_contra! h4
        rcases prime_small hh h4 with rfl|rfl <;> simp_all
    · apply extend_support (b := ∅)
      · simp
      · simp
      · intro p hh
        have hps := (mem_sdiff.mp hh).1
        by_contra! h4
        rcases prime_small hps h4 with rfl|rfl <;> contradiction
end Mo430643
end

section
namespace Mo430643

theorem log_three_lower : (19 / 12 : ℝ) < ell 3 := by
  have h := Real.logb_lt_logb (b := (2:ℝ)) (by norm_num)
    (x := (2:ℝ)^19) (y := (3:ℝ)^12) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at h
  change 19 / 12 < Real.logb 2 3
  norm_num at h
  linarith

theorem log_five_lower : (9 / 4 : ℝ) < ell 5 := by
  have h := Real.logb_lt_logb (b := (2:ℝ)) (by norm_num)
    (x := (2:ℝ)^9) (y := (5:ℝ)^4) (by norm_num) (by norm_num)
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] at h
  change 9 / 4 < Real.logb 2 5
  norm_num at h
  linarith

private theorem ell_two : ell 2 = 1 := Real.logb_self_eq_one (by norm_num)

theorem exception23 (a : ℕ → ℕ)
    (h : (4 ≤ a 2 ∧ 2 ≤ a 3) ∨ (2 ≤ a 2 ∧ 3 ≤ a 3)) : 0 ≤ F {2,3} a := by
  norm_num [F, S, ell_two]
  obtain ⟨u,hu,eu⟩ := exists_nonneg_add_of_le log_three_lower.le
  rcases h with ⟨h₂,h₃⟩ | ⟨h₂,h₃⟩ <;>
    obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le h₂ <;>
    obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le h₃ <;>
    rw [hx,hy,← eu] <;> apply sub_nonneg.mp <;> push_cast <;> ring_nf <;> positivity

set_option maxHeartbeats 1200000 in
theorem exception235 (a : ℕ → ℕ) (h2 : 2 ≤ a 2) (h3 : 2 ≤ a 3) (h5 : 2 ≤ a 5)
    (h : 3 ≤ a 2 ∨ 3 ≤ a 3 ∨ 3 ≤ a 5) : 0 ≤ F {2,3,5} a := by
  norm_num [F, S, ell_two]
  obtain ⟨u,hu,eu⟩ := exists_nonneg_add_of_le log_three_lower.le
  obtain ⟨v,hv,ev⟩ := exists_nonneg_add_of_le log_five_lower.le
  rcases h with h2 | h3 | h5 <;>
    obtain ⟨x,hx⟩ := Nat.exists_eq_add_of_le h2 <;>
    obtain ⟨y,hy⟩ := Nat.exists_eq_add_of_le h3 <;>
    obtain ⟨z,hz⟩ := Nat.exists_eq_add_of_le h5 <;>
    rw [hx,hy,hz,← eu,← ev] <;> apply sub_nonneg.mp <;> push_cast <;> ring_nf <;> positivity

end Mo430643
end

section
namespace Mo430643

/-- Taking base-two logarithms gives the scalar polynomial inequality in the
weighted logarithms of the distinct prime factors. -/
theorem power_of_scalar (s : Finset ℕ) (a : ℕ → ℕ) (r : ℕ)
    (hp : ∀ p ∈ s, Nat.Prime p) (hr : r = ∏ p ∈ s, p ^ a p)
    (hscalar : 0 ≤ (∑ p ∈ s, (a p : ℝ) * Real.logb 2 p)^2
      - 4 * ((s.card : ℝ) - 1) * (∑ p ∈ s, (a p : ℝ) * Real.logb 2 p)
      - ∑ p ∈ s, (a p : ℝ)^2 * Real.logb 2 p) :
    (∏ p ∈ s, (p : ℝ) ^ ((a p : ℝ) ^ 2 / 4)) ≤
      (r : ℝ) ^ (Real.logb 2 (r : ℝ) / 4 + 1 - (s.card : ℝ)) := by
  have hpos (p : ℕ) (h : p ∈ s) : 0 < (p : ℝ) := by exact_mod_cast (hp p h).pos
  have hcast : (r : ℝ) = ∏ p ∈ s, (p : ℝ) ^ (a p) := by exact_mod_cast hr
  have hrpos : 0 < (r : ℝ) := by
    rw [hcast]
    exact Finset.prod_pos (fun p h => pow_pos (hpos p h) _)
  have hlogr : Real.logb 2 (r : ℝ) = ∑ p ∈ s, (a p : ℝ) * Real.logb 2 p := by
    rw [hcast, Real.logb_prod _ _ (fun p h => (pow_pos (hpos p h) _).ne')]
    simp only [Real.logb_pow]
  have hfactor (p : ℕ) (h : p ∈ s) : 0 < (p : ℝ) ^ ((a p : ℝ) ^ 2 / 4) :=
    Real.rpow_pos_of_pos (hpos p h) _
  apply (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2)
    (Finset.prod_pos hfactor) (Real.rpow_pos_of_pos hrpos _)).mp
  rw [Real.logb_prod _ _ (fun p h => (hfactor p h).ne'),
    Real.logb_rpow_eq_mul_logb_of_pos hrpos, hlogr]
  have hl : (∑ p ∈ s, Real.logb 2 ((p : ℝ) ^ ((a p : ℝ)^2 / 4))) =
      (∑ p ∈ s, (a p : ℝ)^2 * Real.logb 2 p) / 4 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro p h
    rw [Real.logb_rpow_eq_mul_logb_of_pos (hpos p h)]
    ring
  rw [hl]
  linarith

end Mo430643
end

section
namespace Mo430643
open Finset

private theorem ell_ge_one {p : ℕ} (hp : p.Prime) : 1 ≤ ell p := by
  rw [ell, ← Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)]
  apply Real.logb_le_logb_of_le (by norm_num) (by norm_num)
  exact_mod_cast hp.two_le

private theorem S_ge (s : Finset ℕ) (a : ℕ → ℕ)
    (hp : ∀ p∈s, Nat.Prime p) (ha : ∀ p∈s, 2≤a p) (i : ℕ) (hi : i∈s) :
    2*(∑ j ∈ s, ell j) + ((a i : ℝ) - 2) ≤ S s a := by
  have h : (∑ j ∈ s, (2*ell j + (if j=i then (a i:ℝ)-2 else 0))) ≤ S s a := by
    unfold S
    apply sum_le_sum
    intro j hj
    have hj1 := ell_ge_one (hp j hj)
    have hj2 : (2:ℝ) ≤ a j := by exact_mod_cast ha j hj
    by_cases he : j=i
    · subst i
      simp only [if_true]
      nlinarith [mul_nonneg (sub_nonneg.mpr hj1) (sub_nonneg.mpr hj2)]
    · simp only [if_neg he, add_zero]
      exact mul_le_mul_of_nonneg_right hj2 (by linarith)
  simpa only [sum_add_distrib, ← mul_sum, sum_ite_eq', if_pos hi] using h

theorem normal_scalar (s : Finset ℕ) (a : ℕ → ℕ)
    (hp : ∀ p∈s, Nat.Prime p) (ha : ∀ p∈s, 2≤a p)
    (hs : 2*(s.card:ℝ)-1 ≤ ∑ p∈s, ell p) : 0 ≤ F s a := by
  have h (i : ℕ) (hi : i∈s) : a i * ell i * (S s a - 4*((s.card:ℝ)-1) - a i) ≥ 0 := by
    have h0 := S_ge s a hp ha i hi
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [ell_ge_one (hp i hi)]))
      (by linarith)
  have he (i : ℕ) : a i * ell i * (S s a - 4*((s.card:ℝ)-1) - a i) =
      a i * ell i * S s a - a i * ell i * (4*((s.card:ℝ)-1)) - (a i:ℝ)^2 * ell i := by ring
  have hsum := Finset.sum_nonneg h
  simp_rw [he, sum_sub_distrib, ← sum_mul] at hsum
  change 0 ≤ S s a * S s a - S s a * (4*((s.card:ℝ)-1)) - _ at hsum
  unfold F
  linarith only [hsum]

end Mo430643
end

section
namespace Mo430643
open Finset

theorem classify23 (a : ℕ → ℕ) (r : ℕ)
    (ha : ∀ p∈({2,3} : Finset ℕ), 2≤a p)
    (hr : r = ∏ p∈({2,3} : Finset ℕ), p^a p)
    (hex : r ∉ ({36,72,900} : Finset ℕ)) :
    (4 ≤ a 2 ∧ 2 ≤ a 3) ∨ (2 ≤ a 2 ∧ 3 ≤ a 3) := by
  have h2 := ha 2 (by simp)
  have h3 := ha 3 (by simp)
  have hx (e2 : a 2=2) (e3 : a 3=2) : False := by
    apply hex
    norm_num [hr,e2,e3]
  have hy (e2 : a 2=3) (e3 : a 3=2) : False := by
    apply hex
    norm_num [hr,e2,e3]
  have hbad₁ : ¬(a 2=2 ∧ a 3=2) := fun h => hx h.1 h.2
  have hbad₂ : ¬(a 2=3 ∧ a 3=2) := fun h => hy h.1 h.2
  omega

theorem classify235 (a : ℕ → ℕ) (r : ℕ)
    (ha : ∀ p∈({2,3,5} : Finset ℕ), 2≤a p)
    (hr : r = ∏ p∈({2,3,5} : Finset ℕ), p^a p)
    (hex : r ∉ ({36,72,900} : Finset ℕ)) :
    3 ≤ a 2 ∨ 3 ≤ a 3 ∨ 3 ≤ a 5 := by
  have h2 := ha 2 (by simp)
  have h3 := ha 3 (by simp)
  have h5 := ha 5 (by simp)
  have hx (e2 : a 2=2) (e3 : a 3=2) (e5 : a 5=2) : False := by
    apply hex
    norm_num [hr,e2,e3,e5]
  have hbad : ¬(a 2=2 ∧ a 3=2 ∧ a 5=2) := fun h => hx h.1 h.2.1 h.2.2
  omega

end Mo430643
end

theorem OMA.solution : type_of% @OMA.S_mo_430643.main := by
  intro s a r hp ha hr hex
  apply Mo430643.power_of_scalar s a r hp hr
  by_cases h23 : s = {2,3}
  · subst s
    exact Mo430643.exception23 a (Mo430643.classify23 a r ha hr hex)
  by_cases h235 : s = {2,3,5}
  · subst s
    exact Mo430643.exception235 a (ha 2 (by simp)) (ha 3 (by simp)) (ha 5 (by simp))
      (Mo430643.classify235 a r ha hr hex)
  exact Mo430643.normal_scalar s a hp ha (Mo430643.normal_support s hp h23 h235)
