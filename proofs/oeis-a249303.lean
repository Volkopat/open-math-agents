import OMAStatements.S_oeis_a249303

namespace OMA.S_oeis_a249303
open Polynomial

private noncomputable def H : ℕ → ℤ[X]
  | 0 => 0
  | 1 => 1
  | m+2 => 2*H (m+1)+(X-1)*H m

private theorem H_coeff (m j : ℕ) : (H m).coeff j = m.choose (2*j+1) := by
  induction m using Nat.twoStepInduction generalizing j with
  | zero => simp [H,Nat.choose_eq_zero_of_lt (by omega : 0<2*j+1)]
  | one =>
    cases j with
    | zero => simp [H]
    | succ j => simp [H,coeff_one,Nat.choose_eq_zero_of_lt (by omega : 1<2*(j+1)+1)]
  | more m h h' =>
    change (2*H (m+1)+(X-1)*H m).coeff j=_
    rw [sub_mul,one_mul,coeff_add,coeff_sub,show (2:ℤ[X])=C 2 by simp,coeff_C_mul]
    cases j with
    | zero => simp [h,h']; ring
    | succ j =>
      rw [coeff_X_mul,h,h,h']
      have e : (m+2).choose (2*(j+1)+1) + m.choose (2*(j+1)+1) =
          2*(m+1).choose (2*(j+1)+1)+m.choose (2*j+1) := by
        have aux (r : ℕ) : (m+2).choose (r+2)+m.choose (r+2) =
            2*(m+1).choose (r+2)+m.choose r := by
          rw [Nat.choose_succ_succ (m+1) (r+1),Nat.choose_succ_succ m (r+1),Nat.choose_succ_succ m r]
          simp only [Nat.succ_eq_add_one,show r+1+1=r+2 by omega]
          omega
        rw [show 2*(j+1)+1=2*j+1+2 by omega]
        exact aux (2*j+1)
      have e' : ((m+2).choose (2*(j+1)+1):ℤ) + (m.choose (2*(j+1)+1):ℤ) =
          2*((m+1).choose (2*(j+1)+1):ℤ)+(m.choose (2*j+1):ℤ) := by exact_mod_cast e
      linarith

private theorem H_degree (m : ℕ) (hm : 0 < m) : (H m).natDegree=(m-1)/2 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr ?_) ?_
  · intro k hk
    rw [H_coeff,Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero]
  · rw [H_coeff]
    exact_mod_cast (Nat.choose_pos (by omega : 2*((m-1)/2)+1 ≤ m)).ne'

private theorem H_irred {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : Irreducible (H p) := by
  have hdeg := H_degree p hp.pos
  have hpodd := hp.odd_of_ne_two (by omega)
  have hi : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmon : (H p).Monic := by
    change (H p).coeff (H p).natDegree=1
    rw [hdeg,H_coeff,show 2*((p-1)/2)+1=p by have := Nat.odd_iff.mp hpodd; omega]
    simp
  apply irreducible_of_eisenstein_criterion (Ideal.isPrime_span_singleton_of_prime hi)
  · simpa [hmon.leadingCoeff,Ideal.mem_span_singleton] using hi.not_dvd_one
  · intro k hk
    have hh := coe_lt_degree.mp hk
    rw [hdeg] at hh
    rw [Ideal.mem_span_singleton,H_coeff]
    exact_mod_cast hp.dvd_choose_self (by omega) (by omega)
  · exact natDegree_pos_iff_degree_pos.mp (by omega)
  · rw [Ideal.span_singleton_pow,Ideal.mem_span_singleton,H_coeff]
    simp only [mul_zero,zero_add,Nat.choose_one_right]
    exact_mod_cast (show ¬p^2 ∣ p from fun h => by
      have := Nat.le_of_dvd hp.pos h
      nlinarith)
  · exact hmon.isPrimitive

private noncomputable def affine (c : ℚ) : ℚ[X] := C 4*X + C (1+4*c)

private noncomputable def transformed (c : ℚ) (m : ℕ) : ℚ[X] :=
  ((H m).map (Int.castRingHom ℚ)).comp (affine c)

private theorem transform_relation (c : ℚ) (m : ℕ) :
    2*transformed c m = 2^m*U c m := by
  induction m using Nat.twoStepInduction with
  | zero => simp [transformed,H,U]
  | one => simp [transformed,H,U]
  | more m ih ih' =>
    have hrec : transformed c (m+2) = 2*transformed c (m+1) + (4*(X+C c))*transformed c m := by
      have haf : affine c-1=4*(X+C c) := by
        simp only [affine,map_add,map_one,map_mul,C_ofNat]
        ring
      simp only [transformed,H,Polynomial.map_add,Polynomial.map_sub,Polynomial.map_mul,
        Polynomial.map_ofNat,map_X,Polynomial.map_one,add_comp,mul_comp,ofNat_comp,sub_comp,X_comp,one_comp,haf]
      norm_num
    rw [hrec,show U c (m+2)=U c (m+1)+(X+C c)*U c m from rfl]
    linear_combination 2*ih'+4*(X+C c)*ih

private theorem U_degree (c : ℚ) {m : ℕ} (hm : 0 < m) : (U c m).natDegree=(m-1)/2 := by
  have h := congrArg natDegree (transform_relation c m)
  rw [show (2:ℚ[X])=C 2 from (C_ofNat 2).symm,← map_pow,natDegree_C_mul (by norm_num),natDegree_C_mul (by positivity)] at h
  rw [transformed,natDegree_comp,affine,natDegree_linear (by norm_num),mul_one,
    natDegree_map_eq_of_injective (Int.cast_injective (α := ℚ)),H_degree m hm] at h
  exact h.symm

private theorem U_irred_prime (c : ℚ) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : Irreducible (U c p) := by
  have hi := H_irred hp hp3
  have hprimitive := hi.isPrimitive (by rw [H_degree _ hp.pos]; omega)
  have hq := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprimitive).mp hi
  let : Invertible (4:ℚ) := invertibleOfNonzero (by norm_num)
  let e := algEquivCMulXAddC (4:ℚ) (1+4*c)
  have ht : Irreducible (transformed c p) := by
    simpa only [e,algEquivCMulXAddC_apply,← comp_eq_aeval,transformed,affine] using hq.map e
  have ht' : IsUnit (2:ℚ[X]) := by
    rw [show (2:ℚ[X])=C 2 from (C_ofNat 2).symm]
    exact (isUnit_iff_ne_zero.mpr (by norm_num : (2:ℚ)≠0)).map C
  have hs := (associated_unit_mul_left (transformed c p) 2 ht').irreducible_iff.mpr ht
  rw [transform_relation] at hs
  exact (associated_unit_mul_left _ _ (ht'.pow p)).irreducible_iff.mp hs

private theorem U_add (c : ℚ) (a b : ℕ) :
    U c (a+1+b) = U c (a+1)*U c (b+1)+(X+C c)*U c a*U c b := by
  induction b using Nat.twoStepInduction with
  | zero => simp [U]
  | one => change U c (a+2) = U c (a+1)*(1+_ * 0) + _; simp [U]
  | more b ih ih' =>
    change U c (a+1+b+1)+(X+C c)*U c (a+1+b) =
      U c (a+1)*(U c (b+2)+(X+C c)*U c (b+1)) + (X+C c)*U c a*(U c (b+1)+(X+C c)*U c b)
    rw [show a+1+b+1=a+1+(b+1) by omega,ih,ih']
    ring

private theorem U_divides (c : ℚ) {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : U c a ∣ U c b := by
  obtain ⟨k,rfl⟩ := h
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  induction k with
  | zero => simp [U]
  | succ k ih =>
    rw [Nat.mul_succ,Nat.add_comm,U_add]
    exact dvd_add (dvd_mul_right _ _) (dvd_mul_of_dvd_right ih _)

private theorem proper_factor {m : ℕ} (hm : 5 ≤ m) (hn : ¬m.Prime) :
    ∃ d, d ∣ m ∧ 3 ≤ d ∧ 2*d ≤ m := by
  obtain ⟨a,hab,ha,ham⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hn
  obtain ⟨b,rfl⟩ := hab
  have hb : 2 ≤ b := by
    by_contra! hh
    interval_cases b <;> simp_all
  by_cases h : a ≤ b
  · use b
    refine ⟨dvd_mul_left _ _,?_,Nat.mul_le_mul_right b ha⟩
    by_contra! hle
    have : a=2 ∧ b=2 := by omega
    rcases this with ⟨rfl,rfl⟩
    omega
  · exact ⟨a,dvd_mul_right _ _,by omega,by simpa [Nat.mul_comm] using Nat.mul_le_mul_left a hb⟩

/-- Consecutive continuants are coprime, so the numerator does not cancel
when the continued fraction is put in lowest terms. -/
theorem U_consecutive_coprime (c : ℚ) (m : ℕ) : IsCoprime (U c (m+1)) (U c m) := by
  have mod_one (k : ℕ) : ∃ q, U c (k+1)=1+(X+C c)*q := by
    induction k with
    | zero => exact ⟨0,by simp [U]⟩
    | succ k ih =>
      obtain ⟨q,hq⟩ := ih
      refine ⟨q+U c k,?_⟩
      change U c (k+1)+(X+C c)*U c k=_
      rw [hq]; ring
  induction m with
  | zero => exact ⟨1,0,by simp [U]⟩
  | succ m ih =>
    obtain ⟨q,hq⟩ := mod_one m
    have h : IsCoprime (X+C c) (U c (m+1)) := ⟨-q,1,by rw [hq]; ring⟩
    change IsCoprime (U c (m+1)+(X+C c)*U c m) (U c (m+1))
    simpa using (h.mul_left ih.symm).mul_add_left_left 1

end OMA.S_oeis_a249303

open OMA.S_oeis_a249303 Polynomial

theorem OMA.solution : type_of% @OMA.S_oeis_a249303.main := by
  intro c n hn
  refine ⟨fun hi => ?_,fun hp => U_irred_prime c hp (by omega)⟩
  by_contra hnp
  obtain ⟨d,hd,h3,hle⟩ := proper_factor (by omega : 5 ≤ n+2) hnp
  obtain ⟨q,hq⟩ := U_divides c (by omega : 0 < d) hd
  have hddeg := U_degree c (by omega : 0 < d)
  have hndeg := U_degree c (by omega : 0 < n+2)
  rcases hi.isUnit_or_isUnit hq with h | h
  · have hh := natDegree_eq_zero_of_isUnit h
    omega
  · have hh := congrArg natDegree hq
    rw [natDegree_mul (by intro hz; simp [hz] at hddeg; omega) h.ne_zero,natDegree_eq_zero_of_isUnit h] at hh
    omega
