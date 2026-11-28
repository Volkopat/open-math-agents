import OMAReductions.R_OeisA242174_conjecture_1_R1

/-! Largest modular zeros for fourth-order Franel numbers.
Source: https://oeis.org/A242174
Credit: @Dolcruz and @marcusbuffett (binomial reflection).
The reflection and zero-extension lemmas are from the project reduction in PR #3721. -/

namespace OMA.R_OeisA242174_conjecture_1_R1_H1_R1

open OeisA242174 Finset Polynomial

private theorem extend_sum (r n N : ℕ) (hr : 0 < r) (hn : n < N) :
    franel r n = ∑ k ∈ range N, n.choose k ^ r := by
  apply sum_subset (range_mono hn)
  intro k _ hk
  simp only [mem_range,not_lt] at hk
  simp [Nat.choose_eq_zero_of_lt (show n < k by omega),hr.ne']

private theorem reflected (p j k : ℕ) (hp : p.Prime) (hj : j < p) (hk : k < p) :
    (((p-1-j).choose k : ℕ) : ZMod p) = (-1)^k * (((k+j).choose j : ℕ) : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  let n := p-1-j
  have hn : n+1+j = p := by dsimp [n]; omega
  have hc : (n : ZMod p)+1+(j : ZMod p)=0 := by
    have hh : ((n+1+j : ℕ) : ZMod p) = 0 := by rw [hn,ZMod.natCast_self]
    push_cast at hh
    exact hh
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : k < p := by omega
    have hk0 : ((k+1 : ℕ) : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr
      (Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hk)
    have hstep : ((n.choose (k+1) : ℕ) : ZMod p) * (k+1) =
        (n.choose k : ZMod p) * ((n : ZMod p)-k) := by
      by_cases hkn : k ≤ n
      · have hh := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.choose_succ_right_eq n k)
        push_cast [hkn] at hh
        exact hh
      · rw [Nat.choose_eq_zero_of_lt (by omega : n < k+1),Nat.choose_eq_zero_of_lt (by omega : n < k)]
        simp
    have haux := Nat.choose_mul_succ_eq (k+j) j
    have hsmall : k+j+1-j = k+1 := by omega
    rw [hsmall,show k+j+1 = k+1+j by omega] at haux
    have haux' := congrArg (fun t : ℕ => (t : ZMod p)) haux
    push_cast at haux'
    apply mul_right_cancel₀ (b := (k : ZMod p)+1) (by simpa using hk0)
    change (n.choose (k+1) : ZMod p) * _ = _
    rw [hstep,show (n.choose k : ZMod p) = _ from ih hk',pow_succ]
    linear_combination (-1 : ZMod p)^k * haux'.symm + (-1 : ZMod p)^k * ((k+j).choose j : ZMod p) * hc

private theorem field_moment (p : ℕ) [Fact p.Prime] (t : ℕ) (ht : t < 2*(p-1)) :
    (∑ x : ZMod p, x^t) = if t = p-1 then -1 else 0 := by
  have hp := (Fact.out : p.Prime).two_le
  split_ifs with h
  · subst t
    simp_rw [ZMod.pow_card_sub_one]
    simp [Finset.sum_ite, Finset.filter_ne', Nat.cast_sub (by omega : 1 ≤ p)]
  · by_cases small : t < p-1
    · exact FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) _ (by simpa using small)
    · have reduce (x : ZMod p) : x^t = x^(t-(p-1)) := by
        by_cases hx : x = 0
        · simp [hx, zero_pow (by omega : t ≠ 0), zero_pow (by omega : t-(p-1) ≠ 0)]
        · conv_lhs => rw [← Nat.sub_add_cancel (by omega : p-1 ≤ t), pow_add,
            ZMod.pow_card_sub_one_eq_one hx, mul_one]
      simp_rw [reduce]
      exact FiniteField.sum_pow_lt_card_sub_one (K := ZMod p) _ (by rw [ZMod.card]; omega)

private theorem field_moments (p : ℕ) [Fact p.Prime] (t : ℕ) (ht : t < 4*(p-1)) :
    (∑ x : ZMod p, x^t) = (if t = p-1 then -1 else 0) +
      (if t = 2*(p-1) then -1 else 0) + (if t = 3*(p-1) then -1 else 0) := by
  have hp := (Fact.out : p.Prime).two_le
  have period (a b : ℕ) (ha : a = b+(p-1)) (hb : 0 < b) :
      (∑ x : ZMod p, x^a) = ∑ x : ZMod p, x^b := by
    apply sum_congr rfl
    intro x _
    by_cases hx : x = 0
    · simp [hx, zero_pow (by omega : a ≠ 0), zero_pow hb.ne']
    · rw [ha, pow_add, ZMod.pow_card_sub_one_eq_one hx, mul_one]
  by_cases h : t < 2*(p-1)
  · rw [field_moment p t h]
    simp [show t ≠ 2*(p-1) by omega, show t ≠ 3*(p-1) by omega]
  by_cases h' : t < 3*(p-1)
  · rw [period t (t-(p-1)) (by omega) (by omega), field_moment _ _ (by omega)]
    simp [show t ≠ p-1 by omega, show t ≠ 3*(p-1) by omega,
      show t-(p-1) = p-1 ↔ t = 2*(p-1) by omega]
  · rw [period t (t-(p-1)) (by omega) (by omega),
      period (t-(p-1)) (t-2*(p-1)) (by omega) (by omega),
      field_moment _ _ (by omega)]
    simp [show t ≠ p-1 by omega, show t ≠ 2*(p-1) by omega,
      show t-2*(p-1) = p-1 ↔ t = 3*(p-1) by omega]


private theorem polynomial_moment (p : ℕ) [Fact p.Prime] (P : (ZMod p)[X])
    (bound : P.natDegree < 4*(p-1)) :
    (∑ k ∈ range p, P.eval (k : ZMod p)) = -(P.coeff (p-1) + P.coeff (2*(p-1)) + P.coeff (3*(p-1))) := by
  have hp := (Fact.out : p.Prime)
  have hcast (i : Fin p) : (ZMod.finEquiv p) i = ((i : ℕ) : ZMod p) := by
    cases p with
    | zero => exact (hp.ne_zero rfl).elim
    | succ q =>
      apply Fin.ext
      change i.val = ((i.val : ℕ) : ZMod (q+1)).val
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt]
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← hcast]
  trans ∑ x : ZMod p, P.eval x
  · exact (ZMod.finEquiv p).toEquiv.sum_comp (fun x => P.eval x)
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [sum_comm]
  have selectCoeff (a : ℕ) :
      (∑ t ∈ range (P.natDegree+1), if t=a then -P.coeff t else 0) = -P.coeff a := by
    simp only [Finset.sum_ite_eq', Finset.mem_range]
    split_ifs with h
    · rfl
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), neg_zero]
  calc
    _ = ∑ t ∈ range (P.natDegree+1),
          ((if t = p-1 then -P.coeff t else 0) + (if t = 2*(p-1) then -P.coeff t else 0) +
          (if t = 3*(p-1) then -P.coeff t else 0)) := by
      apply sum_congr rfl
      intro t h
      rw [← mul_sum, field_moments p t (by have := mem_range.mp h; omega), mul_add, mul_add]
      split_ifs <;> simp
    _ = _ := by rw [sum_add_distrib, sum_add_distrib, selectCoeff, selectCoeff, selectCoeff]; ring


private theorem degree_rising (p j : ℕ) [Fact p.Prime] : (∏ i ∈ range j, (X + C (1+(i : ZMod p)))).natDegree = j := by
  rw [natDegree_prod_of_monic _ _ (fun i _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, sum_const, card_range, smul_eq_mul, mul_one]

theorem reflected_coefficients (p j : ℕ) (hp : p.Prime) (hj : j < p) (bound : 4*j < 4*(p-1)) :
    (j.factorial : ZMod p)^4 * (franel 4 (p-1-j) : ZMod p) =
      -(((∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4).coeff (p-1) + ((∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4).coeff (2*(p-1)) +
        ((∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4).coeff (3*(p-1))) := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hQ (k : ℕ) : (∏ i ∈ range j, (X + C (1+(i : ZMod p)))).eval (k : ZMod p) =
      (j.factorial : ZMod p) * ((k+j).choose j : ZMod p) := by
    have hh := congrArg (fun t : ℕ => (t : ZMod p)) (Nat.ascFactorial_eq_factorial_mul_choose k j)
    rw [Nat.ascFactorial_eq_prod_range] at hh
    push_cast at hh
    simpa [Polynomial.eval_prod, add_assoc] using hh
  have hsum := polynomial_moment p ((∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4) (by
    rw [Polynomial.natDegree_pow, degree_rising]; omega)
  rw [← hsum, extend_sum 4 (p-1-j) p (by decide) (by omega)]
  push_cast
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  rw [reflected p j k hp hj (mem_range.mp hk), Polynomial.eval_pow, hQ, mul_pow, mul_pow]
  rw [← pow_mul, Nat.mul_comm k 4, pow_mul]
  norm_num

/-- For positive rows below p, the zero test uses at most three coefficients. -/
theorem zero_criterion (p k : ℕ) (hp : p.Prime) (hk : 0 < k) (hkp : k < p) :
    let j := p-1-k
    let Q := (∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4
    p ∣ franel 4 k ↔ Q.coeff (p-1) + Q.coeff (2*(p-1)) + Q.coeff (3*(p-1)) = 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  let j := p-1-k
  have hj : j < p-1 := by dsimp [j]; omega
  have hfac : (j.factorial : ZMod p) ≠ 0 := (ZMod.natCast_eq_zero_iff ..).not.mpr
    (fun hd => (show j < p by omega).not_ge (hp.dvd_factorial.mp hd))
  have he := reflected_coefficients p j hp (by omega) (by omega)
  have idx : p-1-j = k := by dsimp [j]; omega
  rw [idx] at he
  dsimp only
  rw [← ZMod.natCast_eq_zero_iff, ← mul_eq_zero_iff_left (pow_ne_zero 4 hfac), he, neg_eq_zero]

/-- The end of the automatic-zero range is sharp when its endpoint is integral. -/
theorem monic_boundary (p j : ℕ) (hp : p.Prime) (e : 4*j = p-1) :
    (j.factorial : ZMod p)^4 * (franel 4 (p-1-j) : ZMod p) = -1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have := hp.two_le
  rw [reflected_coefficients p j hp (by omega) (by omega)]
  let P := (∏ i ∈ range j, (X + C (1+(i : ZMod p))))
  have mon : P.Monic := monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)
  have deg : (P^4).natDegree = p-1 := by
    rw [natDegree_pow, degree_rising]; omega
  change -((P^4).coeff (p-1) + (P^4).coeff (2*(p-1)) + (P^4).coeff (3*(p-1))) = -1
  rw [coeff_eq_zero_of_natDegree_lt (show (P^4).natDegree < 2*(p-1) by omega),
    coeff_eq_zero_of_natDegree_lt (show (P^4).natDegree < 3*(p-1) by omega),
    add_zero, add_zero, ← deg, coeff_natDegree, mon.pow 4]

/-- Primitivity is the largest zero in the reflected index. The third coefficient
vanishes at the candidate row throughout the smooth-case search interval. -/
theorem first_occurrence_iff (p n : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hnp : n < p) (cut : p ≤ 4*(n-1)+1) :
    let Q : ℕ → (ZMod p)[X] := fun j => (∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4
    let j := p-1-n
    (p ∣ franel 4 n ∧ ∀ k : ℕ, 0 < k → k < n → ¬p ∣ franel 4 k) ↔
    (Q j).coeff (p-1) + (Q j).coeff (2*(p-1)) = 0 ∧
    ∀ i : ℕ, j < i → i < p-1 →
      (Q i).coeff (p-1) + (Q i).coeff (2*(p-1)) + (Q i).coeff (3*(p-1)) ≠ 0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro Q j
  have third : (Q j).coeff (3*(p-1)) = 0 := by
    apply coeff_eq_zero_of_natDegree_lt
    dsimp only [Q]
    rw [natDegree_pow, degree_rising]
    dsimp [j]
    omega
  have current := zero_criterion p n hp hn hnp
  change p ∣ franel 4 n ↔ (Q j).coeff _ + (Q j).coeff _ + (Q j).coeff _ = 0 at current
  rw [third, add_zero] at current
  constructor
  · rintro ⟨hd, fresh⟩
    refine ⟨current.mp hd, ?_⟩
    intro i hji hip hzero
    let k := p-1-i
    have hkn : k < n := by dsimp [k,j] at *; omega
    have idx : p-1-k = i := by dsimp [k]; omega
    apply fresh k (by dsimp [k]; omega) hkn
    apply (zero_criterion p k hp (by dsimp [k]; omega) (by omega)).mpr
    rw [idx]
    exact hzero
  · rintro ⟨hzero, largest⟩
    refine ⟨current.mpr hzero, ?_⟩
    intro k hk hkn hd
    exact largest (p-1-k) (by dsimp [j]; omega) (by omega)
      ((zero_criterion p k hp hk (by omega)).mp hd)

/-- The finite block has no indices satisfying the smoothness premise. -/
def H1 : Prop := ∀ n : ℕ, 1024 < n → n ≤ 4096 →
  ∃ p : ℕ, p.Prime ∧ 16381 < p ∧ p ∣ franel 4 n

/-- On a smooth row in the tail, find a prime for which the specified reflected
index is the greatest zero of the coefficient sums. -/
def H2 : Prop := ∀ n : ℕ, 4096 < n →
  (∀ p : ℕ, p.Prime → p ∣ franel 4 n → p ≤ 4*(n-1)+1) →
  ∃ p : ℕ, p.Prime ∧ 4*n ≤ 3*p+1 ∧ p ≤ 4*(n-1)+1 ∧ 3*p ≠ 4*n+3 ∧
    let Q : ℕ → (ZMod p)[X] := fun j => (∏ i ∈ range j, (X + C (1+(i : ZMod p))))^4
    let j := p-1-n
    (Q j).coeff (p-1) + (Q j).coeff (2*(p-1)) = 0 ∧
    ∀ i : ℕ, j < i → i < p-1 →
      (Q i).coeff (p-1) + (Q i).coeff (2*(p-1)) + (Q i).coeff (3*(p-1)) ≠ 0

theorem main : H1 → H2 → OMA.R_OeisA242174_conjecture_1_R1.H1 := by
  intro finite tail n hn smooth
  by_cases hi : n ≤ 4096
  · obtain ⟨p,hp,hbig,hd⟩ := finite n hn hi
    have := smooth p hp hd
    omega
  · obtain ⟨p,hp,lo,cut,_,hzero⟩ := tail n (by omega) smooth
    obtain ⟨hd,fresh⟩ := (first_occurrence_iff p n hp (by omega) (by omega) cut).mpr hzero
    exact ⟨p,hp,lo,cut,hd,fresh⟩

theorem tail_necessary (h : OMA.R_OeisA242174_conjecture_1_R1.H1) : H2 := by
  intro n hn smooth
  obtain ⟨p,hp,lo,cut,hd,fresh⟩ := h n (by omega) smooth
  refine ⟨p,hp,lo,cut,?_,(first_occurrence_iff p n hp (by omega) (by omega) cut).mp ⟨hd,fresh⟩⟩
  intro edge
  let _ : Fact p.Prime := ⟨hp⟩
  have h := monic_boundary p (p-1-n) hp (by omega)
  rw [show p-1-(p-1-n) = n by omega, (ZMod.natCast_eq_zero_iff ..).mpr hd, mul_zero] at h
  exact one_ne_zero (neg_eq_zero.mp h.symm)

end OMA.R_OeisA242174_conjecture_1_R1_H1_R1
