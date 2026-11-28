import OMAStatements.S_oeis_a110612
import Mathlib

namespace OMA.A110612Proof

open OMA.S_oeis_a110612

/-- `lcm(1, ..., k)`. -/
def L (k : ℕ) : ℕ := (Finset.Icc 1 k).lcm id

theorem P_unfold (k : ℕ) : P k = k.primeFactors.sup (fun p => p ^ k.factorization p) := rfl

theorem lcm_fact_le (p B : ℕ) (s : Finset ℕ) :
    (∀ i ∈ s, i ≠ 0) → (∀ i ∈ s, i.factorization p ≤ B) →
      s.lcm id ≠ 0 ∧ (s.lcm id).factorization p ≤ B := by
  induction s using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a s ha ih =>
    intro h0 hB
    obtain ⟨hne, hle⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => hB i (Finset.mem_insert_of_mem hi))
    have ha0 : a ≠ 0 := h0 a (Finset.mem_insert_self a s)
    have haB : a.factorization p ≤ B := hB a (Finset.mem_insert_self a s)
    rw [Finset.lcm_insert]
    change Nat.lcm a (s.lcm id) ≠ 0 ∧ (Nat.lcm a (s.lcm id)).factorization p ≤ B
    refine ⟨Nat.lcm_ne_zero ha0 hne, ?_⟩
    rw [Nat.factorization_lcm ha0 hne, Finsupp.sup_apply]
    exact sup_le haB hle

theorem L_fact (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    L k ≠ 0 ∧ (L k).factorization p ≤ Nat.log p k := by
  unfold L
  apply lcm_fact_le
  · intro i hi
    rw [Finset.mem_Icc] at hi
    omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    have hi0 : i ≠ 0 := by omega
    have h1 : p ^ i.factorization p ∣ i := (hp.pow_dvd_iff_le_factorization hi0).mpr le_rfl
    have h2 : p ^ i.factorization p ≤ k := le_trans (Nat.le_of_dvd (by omega) h1) hi.2
    exact (Nat.le_log_iff_pow_le hp.one_lt hk).mpr h2

theorem ppow_dvd_L_iff (p a k : ℕ) (hp : p.Prime) (hk : k ≠ 0) : p ^ a ∣ L k ↔ p ^ a ≤ k := by
  obtain ⟨hL, hle⟩ := L_fact p k hp hk
  constructor
  · intro h
    have ha : a ≤ (L k).factorization p := (hp.pow_dvd_iff_le_factorization hL).mp h
    exact (Nat.le_log_iff_pow_le hp.one_lt hk).mp (le_trans ha hle)
  · intro h
    have hmem : p ^ a ∈ Finset.Icc 1 k := Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hp.pos, h⟩
    exact Finset.dvd_lcm (f := id) hmem

theorem pow_sup_le (s : Finset ℕ) (f : ℕ → ℕ) (m k : ℕ) (hk : 1 ≤ k)
    (h : ∀ p ∈ s, f p ^ m ≤ k) : s.sup f ^ m ≤ k := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs, Finset.sup_empty]
    rcases m with _ | m
    · simpa using hk
    · simp
  · obtain ⟨p, hp, he⟩ := Finset.exists_mem_eq_sup s hs f
    rw [he]
    exact h p hp

theorem P_one : P 1 = 0 := by simp [P]

theorem A_one : A346418 1 = 1 := by simp [A346418]

theorem P_spec {k : ℕ} (hk : 2 ≤ k) :
    ∃ p, p.Prime ∧ 0 < k.factorization p ∧ P k = p ^ k.factorization p := by
  have hne : k.primeFactors.Nonempty := by
    refine ⟨k.minFac, ?_⟩
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd k, by omega⟩
  obtain ⟨p, hp, he⟩ :=
    Finset.exists_mem_eq_sup k.primeFactors hne (fun p => p ^ k.factorization p)
  rw [Nat.mem_primeFactors] at hp
  exact ⟨p, hp.1, hp.1.factorization_pos_of_dvd hp.2.2 hp.2.1, he⟩

theorem P_ge_two {k : ℕ} (hk : 2 ≤ k) : 2 ≤ P k := by
  obtain ⟨p, hp, he, hPk⟩ := P_spec hk
  rw [hPk]
  calc 2 ≤ p := hp.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ k.factorization p := Nat.pow_le_pow_right hp.pos he

theorem P_dvd {k : ℕ} (hk : 2 ≤ k) : P k ∣ k := by
  obtain ⟨p, hp, _, hPk⟩ := P_spec hk
  rw [hPk]
  exact (hp.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl

theorem P_pow_ne {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) : P k ^ (n + 1) ≠ k := by
  obtain ⟨p, hp, he, hPk⟩ := P_spec hk
  intro heq
  have h1 : (p ^ (k.factorization p * (n + 1))).factorization p = k.factorization p * (n + 1) := by
    rw [hp.factorization_pow, Finsupp.single_eq_same]
  rw [pow_mul, ← hPk, heq] at h1
  have he1 : 1 ≤ k.factorization p := he
  nlinarith [Nat.mul_le_mul he1 hn]

theorem P_mono {c k : ℕ} (hck : c ∣ k) (hk : k ≠ 0) : P c ≤ P k := by
  have hc : c ≠ 0 := by
    rintro rfl
    exact hk (Nat.eq_zero_of_zero_dvd hck)
  rw [P_unfold c]
  apply Finset.sup_le
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqk : q ∈ k.primeFactors := Nat.primeFactors_mono hck hk hq
  have hle : c.factorization q ≤ k.factorization q :=
    (Nat.factorization_prime_le_iff_dvd hc hk).mpr hck q hqp
  calc q ^ c.factorization q ≤ q ^ k.factorization q := Nat.pow_le_pow_right hqp.pos hle
    _ ≤ P k := by
      rw [P_unfold k]
      exact Finset.le_sup (f := fun q => q ^ k.factorization q) hqk

theorem dvd_L_iff (k m : ℕ) (hk : k ≠ 0) : k ^ m ∣ L k ↔ P k ^ m ≤ k := by
  have hL : L k ≠ 0 := (L_fact 2 k Nat.prime_two hk).1
  constructor
  · intro h
    rw [P_unfold]
    apply pow_sup_le _ _ _ _ (by omega)
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have h1 : p ^ k.factorization p ∣ k := (hp'.pow_dvd_iff_le_factorization hk).mpr le_rfl
    have h2 : (p ^ k.factorization p) ^ m ∣ L k := dvd_trans (pow_dvd_pow_of_dvd h1 m) h
    show (p ^ k.factorization p) ^ m ≤ k
    rw [← pow_mul] at h2 ⊢
    exact (ppow_dvd_L_iff p _ k hp' hk).mp h2
  · intro h
    rw [← Nat.factorization_prime_le_iff_dvd (pow_ne_zero m hk) hL]
    intro p hp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hpk : p ∣ k
    · have hmem : p ∈ k.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpk, hk⟩
      have h1 : p ^ k.factorization p ≤ P k := by
        rw [P_unfold]
        exact Finset.le_sup (f := fun q => q ^ k.factorization q) hmem
      have h2 : (p ^ k.factorization p) ^ m ≤ k := le_trans (Nat.pow_le_pow_left h1 m) h
      rw [← pow_mul] at h2
      have h3 := (ppow_dvd_L_iff p _ k hp hk).mpr h2
      rw [hp.pow_dvd_iff_le_factorization hL] at h3
      rw [mul_comm]
      exact h3
    · rw [Nat.factorization_eq_zero_of_not_dvd hpk]
      simp

theorem A_eq_log (k : ℕ) (hk : 2 ≤ k) : A346418 k = Nat.log (P k) k := by
  have hk0 : k ≠ 0 := by omega
  have hk1 : k ≠ 1 := by omega
  have hP : 1 < P k := by have := P_ge_two hk; omega
  have hset : {m : ℕ | k ^ m ∣ (Finset.Icc 1 k).lcm id} = Set.Iic (Nat.log (P k) k) := by
    ext m
    show k ^ m ∣ (Finset.Icc 1 k).lcm id ↔ m ≤ Nat.log (P k) k
    rw [Nat.le_log_iff_pow_le hP hk0]
    exact dvd_L_iff k m hk0
  rw [A346418, if_neg hk1, hset, csSup_Iic]

theorem le_A_iff (k j : ℕ) (hk : 2 ≤ k) : j ≤ A346418 k ↔ P k ^ j ≤ k := by
  have hP : 1 < P k := by have := P_ge_two hk; omega
  rw [A_eq_log k hk]
  exact Nat.le_log_iff_pow_le hP (by omega)

theorem cond_iff (n k : ℕ) (hn : 1 ≤ n) : A110612Cond n k ↔ 2 ≤ k ∧ P k ^ (n + 1) ≤ k := by
  unfold A110612Cond
  constructor
  · rintro ⟨hk1, hlt⟩
    have hk2 : 2 ≤ k := by
      by_contra hcon
      have hk : k = 1 := by omega
      subst hk
      rw [P_one] at hlt
      simp at hlt
    refine ⟨hk2, ?_⟩
    obtain ⟨c, hc⟩ := P_dvd hk2
    have hP := P_ge_two hk2
    have hdiv : k / P k = c := by
      have := Nat.mul_div_cancel_left c (show 0 < P k by omega)
      rwa [← hc] at this
    rw [hdiv] at hlt
    rw [pow_succ']
    calc P k * P k ^ n ≤ P k * c := Nat.mul_le_mul (le_refl _) hlt.le
      _ = k := hc.symm
  · rintro ⟨hk2, hle⟩
    refine ⟨by omega, ?_⟩
    have hne := P_pow_ne hk2 hn
    have hlt' : P k ^ (n + 1) < k := lt_of_le_of_ne hle hne
    obtain ⟨c, hc⟩ := P_dvd hk2
    have hP := P_ge_two hk2
    have hdiv : k / P k = c := by
      have := Nat.mul_div_cancel_left c (show 0 < P k by omega)
      rwa [← hc] at this
    rw [hdiv]
    have h' : P k * P k ^ n < P k * c := by
      rw [← pow_succ', ← hc]
      exact hlt'
    exact Nat.lt_of_mul_lt_mul_left h'

theorem T_iff (n k : ℕ) (hn : 1 ≤ n) :
    (1 ≤ k ∧ A346418 k = n + 1) ↔
      (2 ≤ k ∧ P k ^ (n + 1) ≤ k) ∧ ¬ (2 ≤ k ∧ P k ^ (n + 2) ≤ k) := by
  constructor
  · rintro ⟨hk1, hA⟩
    have hk2 : 2 ≤ k := by
      by_contra hcon
      have hk : k = 1 := by omega
      subst hk
      rw [A_one] at hA
      omega
    refine ⟨⟨hk2, (le_A_iff k (n + 1) hk2).mp (by omega)⟩, ?_⟩
    rintro ⟨_, h2⟩
    have := (le_A_iff k (n + 2) hk2).mpr h2
    omega
  · rintro ⟨⟨hk2, h1⟩, h2⟩
    refine ⟨by omega, ?_⟩
    have a1 := (le_A_iff k (n + 1) hk2).mpr h1
    have a2 : ¬ (n + 2 ≤ A346418 k) := fun h => h2 ⟨hk2, (le_A_iff k (n + 2) hk2).mp h⟩
    omega

theorem descent {j k : ℕ} (hj : 1 ≤ j) (hk : 2 ≤ k) (h : P k ^ (j + 1) ≤ k) :
    ∃ c, c < k ∧ 2 ≤ c ∧ P c ^ j ≤ c := by
  have hk0 : k ≠ 0 := by omega
  have hP := P_ge_two hk
  obtain ⟨c, hc⟩ := P_dvd hk
  have hPc : P k ^ j ≤ c := by
    have h' : P k * P k ^ j ≤ P k * c := by
      rw [← pow_succ', ← hc]
      exact h
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  have hPj : P k ≤ P k ^ j := by
    calc P k = P k ^ 1 := (pow_one _).symm
      _ ≤ P k ^ j := Nat.pow_le_pow_right (by omega) hj
  have hc2 : 2 ≤ c := by omega
  refine ⟨c, ?_, hc2, ?_⟩
  · have h' : c < P k * c := by nlinarith
    rw [← hc] at h'
    exact h'
  · have hmono : P c ≤ P k := P_mono (Dvd.intro_left _ hc.symm) hk0
    exact le_trans (Nat.pow_le_pow_left hmono j) hPc

theorem lt_two_pow' (u : ℕ) : u < 2 ^ u := by
  induction u with
  | zero => norm_num
  | succ n ih => rw [pow_succ]; omega

theorem key_ineq (u : ℕ) : (2 * u + 1) * u ≤ 2 ^ (2 * u + 1) := by
  have h : u + 1 ≤ 2 ^ u := lt_two_pow' u
  have h2 : (u + 1) * (u + 1) ≤ 2 ^ u * 2 ^ u := Nat.mul_le_mul h h
  have e : 2 ^ (2 * u + 1) = 2 * (2 ^ u * 2 ^ u) := by ring
  rw [e]
  nlinarith [h2]

theorem exists_S (j : ℕ) (hj : 1 ≤ j) : ∃ k, 2 ≤ k ∧ P k ^ j ≤ k := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 ^ (2 * (j + 1)) := ⟨_, rfl⟩
  have hm0 : 0 < m := by rw [hm]; positivity
  have h2m : 2 * m = 2 ^ (2 * (j + 1) + 1) := by rw [hm]; ring
  have hpow : (2 * m) ^ (j + 1) ≤ 4 ^ m := by
    have e1 : (2 * m) ^ (j + 1) = 2 ^ ((2 * (j + 1) + 1) * (j + 1)) := by
      rw [h2m, ← pow_mul]
    have e2 : (4 : ℕ) ^ m = 2 ^ (2 * m) := by
      rw [pow_mul]
      norm_num
    rw [e1, e2, h2m]
    exact Nat.pow_le_pow_right (by norm_num) (key_ineq (j + 1))
  have h4 := Nat.four_pow_le_two_mul_self_mul_centralBinom m hm0
  have hPk : P (Nat.centralBinom m) ≤ 2 * m := by
    rw [P_unfold]
    apply Finset.sup_le
    intro p _
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact Nat.pow_factorization_choose_le (by omega)
  have hcb : (2 * m) ^ j ≤ Nat.centralBinom m := by
    have h' : 2 * m * (2 * m) ^ j ≤ 2 * m * Nat.centralBinom m := by
      rw [← pow_succ']
      exact le_trans hpow h4
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  refine ⟨Nat.centralBinom m, ?_, le_trans (Nat.pow_le_pow_left hPk j) hcb⟩
  have h2 : 2 * m ≤ (2 * m) ^ j := by
    calc 2 * m = (2 * m) ^ 1 := (pow_one _).symm
      _ ≤ (2 * m) ^ j := Nat.pow_le_pow_right (by omega) hj
  omega

/-- The least `k ≥ 2` with `P k ^ j ≤ k`. -/
noncomputable def mS (j : ℕ) : ℕ := sInf {k : ℕ | 2 ≤ k ∧ P k ^ j ≤ k}

theorem mS_mem (j : ℕ) (hj : 1 ≤ j) : 2 ≤ mS j ∧ P (mS j) ^ j ≤ mS j := by
  obtain ⟨k, hk⟩ := exists_S j hj
  exact Nat.sInf_mem (s := {k : ℕ | 2 ≤ k ∧ P k ^ j ≤ k}) ⟨k, hk⟩

theorem mS_le (j k : ℕ) (h1 : 2 ≤ k) (h2 : P k ^ j ≤ k) : mS j ≤ k :=
  Nat.sInf_le ⟨h1, h2⟩

theorem mS_lt (j : ℕ) (hj : 1 ≤ j) : mS j < mS (j + 1) := by
  obtain ⟨h1, h2⟩ := mS_mem (j + 1) (by omega)
  obtain ⟨c, hc, hc2, hcP⟩ := descent hj h1 h2
  exact lt_of_le_of_lt (mS_le j c hc2 hcP) hc

end OMA.A110612Proof

open OMA.S_oeis_a110612 OMA.A110612Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a110612.main := by
  intro n hn
  have hmem := mS_mem (n + 1) (by omega)
  have hnot : ¬ (2 ≤ mS (n + 1) ∧ P (mS (n + 1)) ^ (n + 2) ≤ mS (n + 1)) := by
    rintro ⟨h1, h2⟩
    have h3 : mS (n + 2) ≤ mS (n + 1) := mS_le (n + 2) _ h1 h2
    have h4 : mS (n + 1) < mS (n + 2) := mS_lt (n + 1) (by omega)
    omega
  have hT : 1 ≤ mS (n + 1) ∧ A346418 (mS (n + 1)) = n + 1 := (T_iff n _ hn).mpr ⟨hmem, hnot⟩
  have hC : A110612Cond n (mS (n + 1)) := (cond_iff n _ hn).mpr hmem
  refine ⟨⟨_, hC⟩, ⟨_, hT⟩, ?_⟩
  have hset : {k : ℕ | A110612Cond n k} = {k : ℕ | 2 ≤ k ∧ P k ^ (n + 1) ≤ k} := by
    ext k
    exact cond_iff n k hn
  have hleast : IsLeast {k : ℕ | 1 ≤ k ∧ A346418 k = n + 1} (mS (n + 1)) := by
    refine ⟨hT, ?_⟩
    intro k hk
    have h5 := ((T_iff n k hn).mp hk).1
    exact mS_le (n + 1) k h5.1 h5.2
  rw [hleast.csInf_eq, A110612, hset, mS]
