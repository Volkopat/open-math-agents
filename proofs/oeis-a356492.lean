import OMAStatements.S_oeis_a356492

-- Problem: A356492, the determinant is prime only for n = 1, 2 (4 divides it for n >= 5).
-- Credit: @bnb9001

namespace OMA_A356492_Proof

open Matrix OMA.S_oeis_a356492

lemma four_dvd_det {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hj : ∀ c, 2 ∣ A j c - A i c) (hk : ∀ c, 2 ∣ A k c - A i c) : 4 ∣ A.det := by
  choose u hu using hj
  choose w hw using hk
  have e1 : A.det = (A.updateRow j (A j + (-1 : ℤ) • A i)).det :=
    (det_updateRow_add_smul_self A hij.symm (-1)).symm
  set A' := A.updateRow j (A j + (-1 : ℤ) • A i) with hA'
  have hA'k : A' k = A k := by rw [hA', updateRow_ne hjk.symm]
  have hA'i : A' i = A i := by rw [hA', updateRow_ne hij]
  have e2 : A'.det = (A'.updateRow k (A' k + (-1 : ℤ) • A' i)).det :=
    (det_updateRow_add_smul_self A' hik.symm (-1)).symm
  have hB : A'.updateRow k (A' k + (-1 : ℤ) • A' i) =
      (A.updateRow j ((2 : ℤ) • u)).updateRow k ((2 : ℤ) • w) := by
    rw [hA'k, hA'i, hA']
    congr 1
    · congr 1
      funext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hu c]
    · funext c
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linarith [hw c]
  rw [e1, e2, hB, det_updateRow_smul, updateRow_comm _ hjk, det_updateRow_smul]
  exact ⟨_, by ring⟩

lemma nth_prime_odd {m : ℕ} (hm : 1 ≤ m) : Nat.nth Nat.Prime m % 2 = 1 := by
  have hp := Nat.prime_nth_prime m
  have hgt : 2 < Nat.nth Nat.Prime m := by
    rw [← Nat.nth_prime_zero_eq_two]
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime (by omega)
  rcases hp.eq_two_or_odd with h | h
  · omega
  · exact h

lemma four_dvd_of_five_le {n : ℕ} (hn : 5 ≤ n) : 4 ∣ a n := by
  have hodd : ∀ r c : Fin n, 1 ≤ (r : ℕ) → (r : ℕ) ≤ 3 → (toep n r c) % 2 = 1 := by
    intro r c hr1 hr3
    simp only [toep, Matrix.of_apply]
    have hc := c.isLt
    have := nth_prime_odd (m := n - 1 - Int.natAbs ((r : ℤ) - c)) (by omega)
    omega
  apply four_dvd_det (toep n) ⟨1, by omega⟩ ⟨2, by omega⟩ ⟨3, by omega⟩
    (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
  · intro c
    have h1 := hodd ⟨1, by omega⟩ c (by simp) (by simp)
    have h2 := hodd ⟨2, by omega⟩ c (by simp) (by simp)
    omega
  · intro c
    have h1 := hodd ⟨1, by omega⟩ c (by simp) (by simp)
    have h3 := hodd ⟨3, by omega⟩ c (by simp) (by simp)
    omega

end OMA_A356492_Proof

open Matrix OMA_A356492_Proof OMA.S_oeis_a356492 in
theorem OMA.solution : type_of% @OMA.S_oeis_a356492.main := by
  have p0 := Nat.nth_prime_zero_eq_two
  have p1 := Nat.nth_prime_one_eq_three
  have p2 := Nat.nth_prime_two_eq_five
  have p3 := Nat.nth_prime_three_eq_seven
  intro n
  constructor
  · rintro ⟨p, hp, hap⟩
    by_contra h
    rcases Nat.lt_or_ge n 5 with h5 | h5
    · interval_cases n
      · simp [a] at hap
        have : p = 1 := by exact_mod_cast hap.symm
        subst this; exact Nat.not_prime_one hp
      · exact h (Or.inl rfl)
      · exact h (Or.inr rfl)
      · have e : toep 3 = !![5, 3, 2; 3, 5, 3; 2, 3, 5] := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [toep, p0, p1, p2]
        have hd : (!![5, 3, 2; 3, 5, 3; 2, 3, 5] : Matrix (Fin 3) (Fin 3) ℤ).det = 51 := by decide
        rw [a, e, hd] at hap
        have : p = 51 := by exact_mod_cast hap.symm
        subst this; norm_num at hp
      · have e : toep 4 = !![7, 5, 3, 2; 5, 7, 5, 3; 3, 5, 7, 5; 2, 3, 5, 7] := by
          ext i j; fin_cases i <;> fin_cases j <;> simp [toep, p0, p1, p2, p3]
        have hd : (!![7, 5, 3, 2; 5, 7, 5, 3; 3, 5, 7, 5; 2, 3, 5, 7] : Matrix (Fin 4) (Fin 4) ℤ).det = 264 := by
          decide
        rw [a, e, hd] at hap
        have : p = 264 := by exact_mod_cast hap.symm
        subst this; norm_num at hp
    · have h4 := four_dvd_of_five_le h5
      rw [hap] at h4
      have : (4 : ℕ) ∣ p := by exact_mod_cast h4
      have h2 : 2 ∣ p := (show 2 ∣ 4 by norm_num).trans this
      have := hp.eq_one_or_self_of_dvd 2 h2
      have hp4 := Nat.le_of_dvd hp.pos ‹4 ∣ p›
      omega
  · rintro (rfl | rfl)
    · refine ⟨2, Nat.prime_two, ?_⟩
      simp [a, toep, p0]
    · refine ⟨5, by norm_num, ?_⟩
      have e : toep 2 = !![3, 2; 2, 3] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [toep, p0, p1]
      rw [a, e, Matrix.det_fin_two_of]
      norm_num
