import OMAStatements.S_oeis_a238977
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

open Polynomial OMA.S_oeis_a238977

namespace BallotCongruence

-- Perfect matchings vanish on an odd number of elements. On even indices
-- this recursion produces the product of the smaller odd positive integers.
private def matching : ℕ → ℕ
  | 0 => 1
  | 1 => 0
  | k+2 => (k+1)*matching k

private noncomputable def moment : ℕ[X] →ₗ[ℕ] ℕ :=
  Polynomial.lsum fun j => matching j • (LinearMap.id : ℕ →ₗ[ℕ] ℕ)

private lemma on_monomial (k b : ℕ) : moment (monomial k b) = matching k * b := by
  simp [moment, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

private lemma integration_by_parts (P : ℕ[X]) : moment (X*P) = moment P.derivative := by
  induction P using Polynomial.induction_on' with
  | add P Q hp hq => simp [mul_add, hp, hq]
  | monomial k b =>
    rw [X_mul_monomial]
    cases k with
    | zero => simp [on_monomial, matching]
    | succ k =>
      rw [derivative_monomial_succ, on_monomial, on_monomial, matching]
      simp only [Nat.cast_id]
      ring

private lemma binomial_moment (n : ℕ) : moment ((X+1)^n) = involutions n := by
  induction n using Nat.twoStepInduction with
  | zero =>
    rw [pow_zero, ← Polynomial.monomial_zero_one, on_monomial]
    rfl
  | one =>
    have h1 : moment (1:ℕ[X]) = 1 := by
      rw [← Polynomial.monomial_zero_one, on_monomial]; rfl
    rw [pow_one, map_add, h1, ← Polynomial.monomial_one_one_eq_X, on_monomial]
    rfl
  | more n h h' =>
    rw [pow_succ' (X+1:ℕ[X]) (n+1), add_mul, one_mul, map_add, h', integration_by_parts]
    have hd : (((X+1:ℕ[X])^(n+1)).derivative) = (n+1) • (X+1:ℕ[X])^n := by
      simp [derivative_pow, nsmul_eq_mul]
    rw [hd, map_nsmul, h, involutions, Nat.add_comm]
    rfl

private lemma matching_odd (k : ℕ) (hk : Odd k) : matching k = 0 := by
  induction k using Nat.twoStepInduction with
  | zero => simp at hk
  | one => rfl
  | more k ih _ =>
    have o : Odd k := Nat.odd_iff.mpr (by have := Nat.odd_iff.mp hk; omega)
    simp [matching, ih o]

private lemma odd_factor (d : ℕ) (hd : Odd d) (k : ℕ) (he : Even k) (hlt : d < k) :
    d ∣ matching k := by
  induction k using Nat.twoStepInduction with
  | zero => omega
  | one => simp at he
  | more k ih _ =>
    have he' : Even k := Nat.even_iff.mpr (by have := Nat.even_iff.mp he; omega)
    rw [matching]
    by_cases h : d < k
    · exact dvd_mul_of_dvd_right (ih he' h) _
    · have eq : d = k+1 := by
        have := Nat.odd_iff.mp hd
        have := Nat.even_iff.mp he'
        omega
      exact dvd_mul_of_dvd_left (dvd_of_eq eq) _

private lemma divisible_term (m k : ℕ) (ho : Odd (m+1)) (hk : 0 < k) :
    m+1 ∣ matching k * (m+1).choose k := by
  by_cases he : Even k
  · let g := (m+1).gcd k
    have gd : g ∣ m+1 := Nat.gcd_dvd_left _ _
    have gk : g ∣ k := Nat.gcd_dvd_right _ _
    have go : Odd g := Nat.odd_iff.mpr (by
      have htwo : ¬ 2 ∣ g := fun h => (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr (h.trans gd))
      omega)
    have gs : g < k := by
      have := Nat.le_of_dvd hk gk
      have := Nat.odd_iff.mp go
      have := Nat.even_iff.mp he
      omega
    have di : m+1 ∣ k*(m+1).choose k := by
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      exact ⟨m.choose j, by simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq m j).symm⟩
    have dg : m+1 ∣ g*(m+1).choose k := dvd_gcd_mul_of_dvd_mul di
    exact dg.trans (mul_dvd_mul (odd_factor g go k he gs) dvd_rfl)
  · simp [matching_odd k (Nat.not_even_iff_odd.mp he)]

private lemma odd_congruence (n : ℕ) (hn : Odd n) : ∃ z : ℕ, involutions n = 1+n*z := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by
    intro h; subst n; simp at hn : n ≠ 0)
  let P := (X+1 : ℕ[X])^(m+1)
  have hc (k : ℕ) : P.coeff k = (m+1).choose k := by simp [P, coeff_X_add_one_pow]
  have hz : 0 ∈ P.support := by simp [Polynomial.mem_support_iff, hc]
  have hd : m+1 ∣ ∑ k ∈ P.support.erase 0, matching k * P.coeff k := by
    apply Finset.dvd_sum
    intro k hk
    rw [hc]
    exact divisible_term m k hn (Nat.pos_of_ne_zero (Finset.mem_erase.mp hk).1)
  obtain ⟨z,he⟩ := hd
  refine ⟨z, ?_⟩
  rw [← binomial_moment]
  change (∑ k ∈ P.support, matching k * P.coeff k) = _
  rw [← Finset.sum_erase_add _ _ hz, he, hc, Nat.choose_zero_right]
  simp [matching, Nat.add_comm]

private lemma tel_rec (n : ℕ) :
    involutions (n+2) = involutions (n+1)+(n+1)*involutions n := rfl

private lemma periodic_three (n : ℕ) : involutions (n+3) ≡ involutions n [MOD 3] := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h h' =>
    change involutions ((n+3)+2) ≡ involutions (n+2) [MOD 3]
    rw [tel_rec (n+3), tel_rec n]
    exact h'.add ((show (n+3)+1 ≡ n+1 [MOD 3] by unfold Nat.ModEq; omega).mul h)

private lemma even_terms (k : ℕ) : 2 ∣ involutions (k+2) := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h h' =>
    rw [involutions]
    exact dvd_add h' (dvd_mul_of_dvd_right h _)

private lemma slope (n : ℕ) : involutions n ≤ involutions (n+1) := by
  cases n with
  | zero => decide
  | succ n => rw [tel_rec n]; omega

private lemma ballot_identity (n : ℕ) :
    3*(a (n+3):ℤ) = (involutions (n+3):ℤ)-involutions n := by
  have le := (slope n).trans ((slope (n+1)).trans (slope (n+2)))
  have dv := (Nat.modEq_iff_dvd' le).mp (periodic_three n).symm
  have eq : 3*a (n+3) = involutions (n+3)-involutions n := by
    rw [a, Nat.mul_div_cancel' dv]
  have lifted := congrArg (fun k : ℕ => (k:ℤ)) eq
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub le] using lifted

private lemma even_ballot (n : ℕ) (hn : 2 ≤ n) : (2:ℤ) ∣ (a (n+3):ℤ) := by
  have e : n-2+2 = n := by omega
  obtain ⟨b,hb⟩ := even_terms (n-2)
  rw [e] at hb
  obtain ⟨c,hc⟩ := even_terms (n+1)
  have h := ballot_identity n
  have b' : (involutions n:ℤ)=2*b := by exact_mod_cast hb
  have c' : (involutions (n+3):ℤ)=2*c := by exact_mod_cast hc
  omega

private lemma factor_for_odd (n : ℕ) (hn : 0<n) (ho : Odd n) :
    ∃ K : ℤ, 3*((a (n+3):ℤ)-1)=(n:ℤ)*K ∧ (3 ∣ n → ¬ (3:ℤ) ∣ K) := by
  obtain ⟨z,hz⟩ := odd_congruence n ho
  have z' : (involutions n:ℤ)=1+(n:ℤ)*z := by exact_mod_cast hz
  have h := ballot_identity n
  have st : involutions (n+1) = involutions n + n*involutions (n-1) := by
    cases n with
    | zero => omega
    | succ j => rfl
  have t : involutions (n+3) = (n+3)*involutions (n+1)+(n+1)*involutions n := by
    rw [tel_rec (n+1), tel_rec n]
    ring
  have ti : (involutions (n+3):ℤ)=((n:ℤ)+3)*(involutions (n+1):ℤ)+((n:ℤ)+1)*involutions n := by
    exact_mod_cast t
  have si : (involutions (n+1):ℤ)=involutions n+(n:ℤ)*involutions (n-1) := by exact_mod_cast st
  refine ⟨3*(z:ℤ)+2*(involutions n:ℤ)+((n:ℤ)+3)*involutions (n-1), ?_, ?_⟩
  · rw [ti,si] at h
    rw [z'] at h ⊢
    nlinarith only [h]
  · intro d
    have di : (3:ℤ) ∣ (n:ℤ) := by exact_mod_cast d
    obtain ⟨m,hm⟩ := di
    rintro ⟨j,hj⟩
    rw [z',hm] at hj
    ring_nf at hj
    omega

private lemma coprime_six (n : ℕ) : n.Coprime 6 ↔ ¬2∣n ∧ ¬3∣n := by
  rw [show (6:ℕ)=2*3 by decide, Nat.coprime_mul_iff_right]
  exact ⟨fun h => ⟨Nat.prime_two.coprime_iff_not_dvd.mp h.1.symm,
    Nat.prime_three.coprime_iff_not_dvd.mp h.2.symm⟩,
    fun h => ⟨(Nat.prime_two.coprime_iff_not_dvd.mpr h.1).symm,
    (Nat.prime_three.coprime_iff_not_dvd.mpr h.2).symm⟩⟩

private lemma result (n : ℕ) (hn : 0 < n) : a (n+3) ≡ 1 [MOD n] ↔ n.Coprime 6 := by
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd, coprime_six]
  simp only [Nat.cast_one]
  by_cases he : 2 ∣ n
  · have ne : (2:ℤ) ∣ (n:ℤ) := by exact_mod_cast he
    have even := even_ballot n (by omega)
    constructor
    · intro h
      have twice := ne.trans h
      omega
    · exact fun h => (h.1 he).elim
  · have ho : Odd n := Nat.odd_iff.mpr (by omega)
    obtain ⟨K,eqn,ex⟩ := factor_for_odd n hn ho
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨he, fun h3 => ?_⟩
      have eq : (n:ℤ)*K = (n:ℤ)*(3*w) := by rw [← eqn, hw]; ring
      exact ex h3 ⟨w, mul_left_cancel₀ (by exact_mod_cast hn.ne' : (n:ℤ)≠0) eq⟩
    · rintro ⟨_,h3⟩
      have prime : Prime (3:ℤ) := by norm_num
      have dv : (3:ℤ) ∣ (n:ℤ)*K := ⟨(a (n+3):ℤ)-1, eqn.symm⟩
      have bad : ¬ (3:ℤ) ∣ (n:ℤ) := by exact_mod_cast h3
      obtain ⟨w,hw⟩ := (prime.dvd_mul.mp dv).resolve_left bad
      refine ⟨w, ?_⟩
      rw [hw] at eqn
      nlinarith only [eqn]

end BallotCongruence

theorem OMA.solution : type_of% @OMA.S_oeis_a238977.main := BallotCongruence.result
