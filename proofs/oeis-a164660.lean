import OMAStatements.S_oeis_a164660
import Mathlib

namespace OMA.P164660

open Polynomial OMA.S_oeis_a164660

lemma moment_monomial (i : ℕ) (c : ℚ) : moment (monomial i c) = ((i : ℚ) + 1)⁻¹ * c := by
  unfold moment
  rw [Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  · simp
  · simp

/-- The moment functional integrates over [0,1]. -/
lemma moment_derivative (q : ℚ[X]) : moment (derivative q) = q.eval 1 - q.eval 0 := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [derivative_add, map_add, hp, hq, eval_add, eval_add]
    ring
  | monomial j c =>
    rcases j with _ | j
    · rw [derivative_monomial]
      simp
    · rw [derivative_monomial, moment_monomial]
      simp only [Nat.add_sub_cancel, eval_monomial, one_pow, mul_one]
      have hj : ((j : ℚ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
      simp

lemma moment_intCast_mul (k : ℤ) (p : ℚ[X]) : moment ((k : ℚ[X]) * p) = (k : ℚ) * moment p := by
  have e : ((k : ℚ[X]) * p) = (k : ℚ) • p := by
    rw [← Polynomial.C_mul']
    simp
  rw [e, map_smul, smul_eq_mul]

/-- Values of T at 0. -/
noncomputable def e (j : ℕ) : ℚ := (Chebyshev.T ℚ (j : ℤ)).eval 0

lemma e_zero : e 0 = 1 := by simp [e]
lemma e_one : e 1 = 0 := by simp [e]
lemma e_add_two (j : ℕ) : e (j + 2) = - e j := by
  unfold e
  have h := Chebyshev.T_add_two ℚ (j : ℤ)
  have c : ((j + 2 : ℕ) : ℤ) = (j : ℤ) + 2 := by push_cast; ring
  rw [c, h]
  simp

lemma e_four (i : ℕ) : e (4 * i) = 1 ∧ e (4 * i + 1) = 0 ∧ e (4 * i + 2) = -1 ∧ e (4 * i + 3) = 0 := by
  induction i with
  | zero =>
    refine ⟨e_zero, e_one, ?_, ?_⟩
    · rw [show 4 * 0 + 2 = 0 + 2 from rfl, e_add_two, e_zero]
    · rw [show 4 * 0 + 3 = 1 + 2 from rfl, e_add_two, e_one, neg_zero]
  | succ i ih =>
    obtain ⟨h0, h1, h2, h3⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [show 4 * (i + 1) = 4 * i + 2 + 2 from by ring, e_add_two, h2, neg_neg]
    · rw [show 4 * (i + 1) + 1 = 4 * i + 3 + 2 from by ring, e_add_two, h3, neg_zero]
    · rw [show 4 * (i + 1) + 2 = 4 * i + 2 + 2 + 2 from by ring, e_add_two, e_add_two, h2]
      norm_num
    · rw [show 4 * (i + 1) + 3 = 4 * i + 3 + 2 + 2 from by ring, e_add_two, e_add_two, h3]
      simp

/-- (m + 1) times the moment of U_m. -/
lemma moment_U (m : ℕ) : ((m : ℚ) + 1) * moment (Chebyshev.U ℚ (m : ℤ)) = 1 - e (m + 1) := by
  have h := Chebyshev.T_derivative_eq_U (R := ℚ) ((m : ℤ) + 1)
  rw [add_sub_cancel_right] at h
  have h2 := moment_derivative (Chebyshev.T ℚ ((m : ℤ) + 1))
  rw [h, moment_intCast_mul, Chebyshev.T_eval_one] at h2
  unfold e
  push_cast at h2 ⊢
  exact h2

/-- The integral of T_(m+2). -/
lemma r_add_two (m : ℕ) :
    2 * r (m + 2) = (1 - e (m + 3)) / ((m : ℚ) + 3) - (1 - e (m + 1)) / ((m : ℚ) + 1) := by
  have h := Chebyshev.two_mul_T_eq_U_sub_U ℚ (m : ℤ)
  have h1 := moment_U (m + 2)
  have h2 := moment_U m
  have hm : moment (2 * Chebyshev.T ℚ ((m : ℤ) + 2)) = 2 * r (m + 2) := by
    unfold r
    have := moment_intCast_mul 2 (Chebyshev.T ℚ ((m : ℤ) + 2))
    push_cast at this ⊢
    exact this
  rw [← hm, h, map_sub]
  have a1 : ((m : ℚ) + 3) ≠ 0 := by positivity
  have a2 : ((m : ℚ) + 1) ≠ 0 := by positivity
  push_cast at h1
  field_simp
  linear_combination ((m : ℚ) + 1) * h1 - ((m : ℚ) + 3) * h2

lemma r_zero : r 0 = 1 := by
  unfold r
  have h : Chebyshev.T ℚ ((0 : ℕ) : ℤ) = monomial 0 1 := by simp
  rw [h, moment_monomial]
  norm_num

lemma r_one : r 1 = 1 / 2 := by
  unfold r
  have h : Chebyshev.T ℚ ((1 : ℕ) : ℤ) = monomial 1 1 := by
    simp [Polynomial.X]
  rw [h, moment_monomial]
  norm_num

/-- Closed forms by residue modulo 4. -/
lemma r_four (i : ℕ) : r (4 * i + 1) = 1 / (2 * (2 * (i : ℚ) + 1))
    ∧ r (4 * i + 2) = -1 / ((4 * (i : ℚ) + 1) * (4 * (i : ℚ) + 3))
    ∧ r (4 * i + 3) = -1 / (2 * (2 * (i : ℚ) + 1))
    ∧ r (4 * i + 4) = -1 / ((4 * (i : ℚ) + 3) * (4 * (i : ℚ) + 5)) := by
  obtain ⟨h0, h1, h2, h3⟩ := e_four i
  obtain ⟨k0, k1, k2, k3⟩ := e_four (i + 1)
  have p1 : (4 * (i : ℚ) + 1) ≠ 0 := by positivity
  have p2 : (2 * (i : ℚ) + 1) ≠ 0 := by positivity
  have p3 : (4 * (i : ℚ) + 3) ≠ 0 := by positivity
  have p5 : (4 * (i : ℚ) + 5) ≠ 0 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases i with _ | j
    · rw [show 4 * 0 + 1 = 1 from rfl, r_one]
      norm_num
    · have h := r_add_two (4 * j + 3)
      obtain ⟨g0, g1, g2, g3⟩ := e_four (j + 1)
      rw [show 4 * j + 3 + 3 = 4 * (j + 1) + 2 from by ring, show 4 * j + 3 + 1 = 4 * (j + 1) from by ring,
        g2, g0] at h
      rw [show 4 * (j + 1) + 1 = 4 * j + 3 + 2 from by ring]
      push_cast at h ⊢
      have q1 : (4 * (j : ℚ) + 3 + 3) ≠ 0 := by positivity
      have q2 : (2 * ((j : ℚ) + 1) + 1) ≠ 0 := by positivity
      have q4 : (4 * (j : ℚ) + 3 + 1) ≠ 0 := by positivity
      field_simp at h ⊢
      apply mul_left_cancel₀ q4
      linear_combination (1 / 2 : ℚ) * h
  · have h := r_add_two (4 * i)
    rw [show 4 * i + 3 = 4 * i + 3 from rfl, h3, h1] at h
    push_cast at h
    field_simp at h ⊢
    linarith
  · have h := r_add_two (4 * i + 1)
    rw [show 4 * i + 1 + 3 = 4 * (i + 1) from by ring, show 4 * i + 1 + 1 = 4 * i + 2 from by ring, k0, h2] at h
    rw [show 4 * i + 3 = 4 * i + 1 + 2 from by ring]
    push_cast at h ⊢
    have q1 : (4 * (i : ℚ) + 1 + 1) ≠ 0 := by positivity
    have q3 : (4 * (i : ℚ) + 1 + 3) ≠ 0 := by positivity
    field_simp at h ⊢
    apply mul_left_cancel₀ q3
    linear_combination (1 / 2 : ℚ) * h
  · have h := r_add_two (4 * i + 2)
    rw [show 4 * i + 2 + 3 = 4 * (i + 1) + 1 from by ring, show 4 * i + 2 + 1 = 4 * i + 3 from by ring, k1, h3] at h
    rw [show 4 * i + 4 = 4 * i + 2 + 2 from by ring]
    push_cast at h ⊢
    have q1 : (4 * (i : ℚ) + 2 + 1) ≠ 0 := by positivity
    have q3 : (4 * (i : ℚ) + 2 + 3) ≠ 0 := by positivity
    field_simp at h ⊢
    linarith

theorem main_closed (n : ℕ) (hn : 0 < n) :
    r n = if Even n then -1 / (((n : ℚ) - 1) * ((n : ℚ) + 1))
      else (-1 : ℚ) ^ ((n - 1) / 2) / (2 * (2 * (((n - 1) / 4 : ℕ) : ℚ) + 1)) := by
  obtain ⟨i, rfl | rfl | rfl | rfl⟩ : ∃ i, n = 4 * i + 1 ∨ n = 4 * i + 2 ∨ n = 4 * i + 3 ∨ n = 4 * i + 4 :=
    ⟨(n - 1) / 4, by omega⟩
  · rw [if_neg (by rw [Nat.even_iff]; omega), (r_four i).1]
    have a1 : (4 * i + 1 - 1) / 2 = 2 * i := by omega
    have a2 : (4 * i + 1 - 1) / 4 = i := by omega
    rw [a1, a2, pow_mul]
    norm_num
  · rw [if_pos (by rw [Nat.even_iff]; omega), (r_four i).2.1]
    push_cast
    ring
  · rw [if_neg (by rw [Nat.even_iff]; omega), (r_four i).2.2.1]
    have a1 : (4 * i + 3 - 1) / 2 = 2 * i + 1 := by omega
    have a2 : (4 * i + 3 - 1) / 4 = i := by omega
    rw [a1, a2, pow_succ, pow_mul]
    norm_num
  · rw [if_pos (by rw [Nat.even_iff]; omega), (r_four i).2.2.2]
    push_cast
    ring

/-! ### The product -/

lemma term_eq (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (1 - 2 * (((k ^ n / n : ℕ) : ℤ) - (((k ^ n - 1) / n : ℕ) : ℤ)))
      = if radical n ∣ k then (-1 : ℤ) else 1 := by
  obtain ⟨m, hm⟩ : ∃ m, k ^ n = m + 1 := ⟨k ^ n - 1, by have := Nat.pow_pos (n := n) hk; omega⟩
  have hdiv : (n ∣ k ^ n) ↔ radical n ∣ k := by
    unfold radical
    rw [Nat.dvd_pow_self_iff (by omega) (by omega), Nat.prod_primeFactors_dvd_iff (by omega)]
  rw [hm, Nat.add_sub_cancel, Nat.succ_div]
  by_cases h : radical n ∣ k
  · rw [if_pos h, if_pos (by rw [← hm]; exact hdiv.mpr h)]
    push_cast
    ring
  · rw [if_neg h, if_neg (by rw [← hm]; exact fun h' => h (hdiv.mp h'))]
    push_cast
    ring

lemma browne (n : ℕ) (hn : 0 < n) : browneProduct n = (-1 : ℤ) ^ (n / radical n) := by
  unfold browneProduct
  rw [Finset.prod_congr rfl (fun k hk => term_eq n k hn (by rw [Finset.mem_Ioc] at hk; omega)),
    Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one, Nat.Ioc_filter_dvd_card_eq_div]

/-! ### Parity of n / radical n -/

lemma rad_dvd (n : ℕ) : radical n ∣ n := Nat.prod_primeFactors_dvd n

lemma odd_case (n : ℕ) (h : Odd n) : Odd (n / radical n) :=
  Odd.of_dvd_nat h (Nat.div_dvd_of_dvd (rad_dvd n))

lemma rad_two_mul_even (m : ℕ) (hm : m ≠ 0) (h2 : 2 ∣ m) : radical (2 * m) = radical m := by
  unfold radical
  rw [Nat.primeFactors_mul (by norm_num) hm]
  have hsub : (2 : ℕ).primeFactors ⊆ m.primeFactors := by
    rw [Nat.Prime.primeFactors Nat.prime_two]
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2, hm⟩
  rw [Finset.union_eq_right.mpr hsub]

lemma rad_two_mul_odd (m : ℕ) (hm : Odd m) : radical (2 * m) = 2 * radical m := by
  unfold radical
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  rw [Nat.primeFactors_mul (by norm_num) hm0, Nat.Prime.primeFactors Nat.prime_two, Finset.prod_union,
    Finset.prod_singleton]
  rw [Finset.disjoint_singleton_left]
  intro h
  have h2 := (Nat.mem_primeFactors.mp h).2.1
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h2)

lemma even_case (i : ℕ) : Even ((4 * i + 4) / radical (4 * i + 4)) := by
  have e : 4 * i + 4 = 2 * (2 * i + 2) := by ring
  rw [e, rad_two_mul_even (2 * i + 2) (by omega) ⟨i + 1, by ring⟩, Nat.mul_div_assoc 2 (rad_dvd _)]
  exact even_two_mul _

lemma odd_case2 (i : ℕ) : Odd ((4 * i + 2) / radical (4 * i + 2)) := by
  have e : 4 * i + 2 = 2 * (2 * i + 1) := by ring
  have ho : Odd (2 * i + 1) := ⟨i, rfl⟩
  rw [e, rad_two_mul_odd _ ho, Nat.mul_div_mul_left _ _ (by norm_num)]
  exact odd_case _ ho

/-! ### Numerators -/

lemma num_neg (d : ℕ) (hd : 0 < d) (x : ℚ) (hx : x = -1 / (d : ℚ)) : x.num = -1 := by
  have h := Rat.num_div_eq_of_coprime (a := -1) (b := (d : ℤ)) (by exact_mod_cast hd) (by simp)
  push_cast at h
  rw [hx]
  exact h

lemma num_pos (d : ℕ) (hd : 0 < d) (x : ℚ) (hx : x = 1 / (d : ℚ)) : x.num = 1 := by
  have h := Rat.num_div_eq_of_coprime (a := 1) (b := (d : ℤ)) (by exact_mod_cast hd) (by simp)
  push_cast at h
  rw [hx]
  exact h

theorem num_eq (n : ℕ) (hn : 0 < n) : (r (n + 1)).num = (-1 : ℤ) ^ (n / radical n) := by
  obtain ⟨i, rfl | rfl | rfl | rfl⟩ : ∃ i, n = 4 * i + 1 ∨ n = 4 * i + 2 ∨ n = 4 * i + 3 ∨ n = 4 * i + 4 :=
    ⟨(n - 1) / 4, by omega⟩
  · rw [(odd_case (4 * i + 1) ⟨2 * i, by ring⟩).neg_one_pow]
    refine num_neg ((4 * i + 1) * (4 * i + 3)) (by positivity) _ ?_
    rw [show 4 * i + 1 + 1 = 4 * i + 2 from rfl, (r_four i).2.1]
    push_cast
    ring
  · rw [(odd_case2 i).neg_one_pow]
    refine num_neg (2 * (2 * i + 1)) (by positivity) _ ?_
    rw [show 4 * i + 2 + 1 = 4 * i + 3 from rfl, (r_four i).2.2.1]
    push_cast
    ring
  · rw [(odd_case (4 * i + 3) ⟨2 * i + 1, by ring⟩).neg_one_pow]
    refine num_neg ((4 * i + 3) * (4 * i + 5)) (by positivity) _ ?_
    rw [show 4 * i + 3 + 1 = 4 * i + 4 from rfl, (r_four i).2.2.2]
    push_cast
    ring
  · rw [(even_case i).neg_one_pow]
    refine num_pos (2 * (2 * (i + 1) + 1)) (by positivity) _ ?_
    rw [show 4 * i + 4 + 1 = 4 * (i + 1) + 1 from by ring, (r_four (i + 1)).1]
    push_cast
    ring

end OMA.P164660

theorem OMA.solution : type_of% @OMA.S_oeis_a164660.main :=
  ⟨⟨OMA.P164660.r_zero, OMA.P164660.main_closed⟩,
    fun n hn => ⟨by rw [OMA.P164660.browne n hn]; exact OMA.P164660.num_eq n hn, OMA.P164660.browne n hn⟩⟩
