import OMAStatements.S_oeis_a373725
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

open OMA.S_oeis_a373725

namespace FactorialNeighbors

private lemma repeated_factor (b t : ℕ) (hb : 0 < b) : b ^ t ∣ (b*t).factorial := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (Nat.mul_dvd_mul ih (Nat.dvd_factorial hb le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

private lemma product_exponent {b c f e : ℕ} (h : b.Coprime c) (hb : b ^ e ∣ f)
    (hc : c ^ e ∣ f) (hnext : ¬ b ^ (e+1) ∣ f) : multiplicity (b*c) f = e := by
  apply multiplicity_eq_of_dvd_of_not_dvd
  · rw [mul_pow]
    exact (h.pow e e).mul_dvd_of_dvd_of_dvd hb hc
  · intro hf
    rw [mul_pow] at hf
    exact hnext ((Nat.dvd_mul_right _ _).trans hf)

private lemma near_prime {q : ℕ} (hq : q.Prime) (h2 : 2 < q) :
    (q*(q+2)).factorial.factorization q = q+3 := by
  have h1 : ¬ q ∣ q+1 := by
    simpa using (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 1) (by omega : 1 < q))
  have h2' : ¬ q ∣ q+2 := by
    simpa using (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) h2)
  have hqf : q.factorial.factorization q = 1 := by
    simpa using Nat.factorization_factorial_mul (n := 1) hq
  rw [Nat.factorization_factorial_mul hq, Nat.factorial_succ (q+1), Nat.factorial_succ q,
    Nat.factorization_mul (by omega) (by positivity), Nat.factorization_mul (by omega)
      (Nat.factorial_ne_zero q)]
  simp [Nat.factorization_eq_zero_of_not_dvd h1, Nat.factorization_eq_zero_of_not_dvd h2', hqf]
  omega

private lemma left_value {q s : ℕ} (hq : q.Prime) (hs : 4 ≤ s) (hrs : q+2 = 3*s) :
    multiplicity (q*(q+2)) (q*(q+2)).factorial = q+3 := by
  have hq2 : 2 < q := by omega
  have hc : q.Coprime (q+2) := by
    apply hq.coprime_iff_not_dvd.mpr
    simpa using (Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hq2)
  have hval := near_prime hq hq2
  apply product_exponent hc
  · exact (hq.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mpr hval.ge
  · let e := q+3
    change (q+2)^e ∣ (q*(q+2)).factorial
    have h1 : 3+s ≤ q+2 := by omega
    have h2 : 3+s+1 ≤ q := by omega
    have limit : 3*e+s*e ≤ q*(q+2) := calc
      3*e+s*e = (3+s)*(q+2)+(3+s) := by dsimp [e]; ring
      _ ≤ (3+s)*(q+2)+(q+2) := Nat.add_le_add_left h1 _
      _ = (3+s+1)*(q+2) := by ring
      _ ≤ q*(q+2) := Nat.mul_le_mul_right _ h2
    rw [hrs, mul_pow]
    exact ((Nat.mul_dvd_mul (repeated_factor 3 e (by decide)) (repeated_factor s e (by omega))).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)).trans
      (Nat.factorial_dvd_factorial (by simpa [← hrs] using limit))
  · intro hn
    have := (hq.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp hn
    omega

private lemma right_value {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    multiplicity (4*p^2) (4*p^2).factorial = 2*p+2 := by
  let e := 2*p+2
  have hfac : (4*p^2).factorial.factorization p = 2*e := by
    rw [show 4*p^2 = p*(p*4) by ring, Nat.factorization_factorial_mul hp,
      Nat.factorization_factorial_mul hp, Nat.factorization_factorial_eq_zero_of_lt (by omega)]
    dsimp [e]
    omega
  have hcop : (p^2).Coprime 4 := by
    have hc : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt (by decide) (by omega))
    exact hc.pow 2 2
  change multiplicity (4*p^2) (4*p^2).factorial = e
  conv_lhs => lhs; rw [Nat.mul_comm]
  apply product_exponent hcop
  · rw [← pow_mul]
    exact (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mpr hfac.ge
  · apply (repeated_factor 4 e (by decide)).trans (Nat.factorial_dvd_factorial ?_)
    dsimp [e]
    nlinarith [Nat.mul_le_mul h5 h5, Nat.mul_le_mul_right p h5]
  · intro h
    rw [← pow_mul] at h
    have := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero _)).mp h
    omega

end FactorialNeighbors

theorem OMA.solution : type_of% @OMA.S_oeis_a373725.main := by
  intro p hp h3 hq
  by_cases h2 : p = 2
  · subst p
    change multiplicity 15 (Nat.factorial 15) = multiplicity 16 (Nat.factorial 16)
    have hl : multiplicity 15 (Nat.factorial 15) = 3 :=
      multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
    have hr : multiplicity 16 (Nat.factorial 16) = 3 :=
      multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
    exact hl.trans hr.symm
  have h4 : p ≠ 4 := by rintro rfl; exact (by decide : ¬ Nat.Prime 4) hp
  have h5 : 5 ≤ p := by have := hp.two_le; omega
  let q := 2*p-1
  have hq1 : q+1 = 2*p := by dsimp [q]; omega
  have hprim : q.Prime := hq
  have hpn : ¬3 ∣ p := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h | h <;> omega
  have hqn : ¬3 ∣ q := by
    intro h
    rcases (Nat.dvd_prime hprim).mp h with h | h <;> omega
  have decomp := Nat.mod_add_div p 3
  have hdiv : 3 ∣ q+2 := by
    have hrem := Nat.mod_lt p (by decide : 0 < 3)
    by_cases h : p % 3 = 1
    · exact ⟨2*(p/3)+1, by omega⟩
    · by_cases hz : p % 3 = 0
      · exact (hpn ⟨p/3, by omega⟩).elim
      · exact (hqn ⟨2*(p/3)+1, by omega⟩).elim
  obtain ⟨s, hs⟩ := hdiv
  have hs4 : 4 ≤ s := by omega
  have hmul : q*(q+2)+1 = 4*p^2 := by
    calc
      q*(q+2)+1 = (q+1)^2 := by ring
      _ = 4*p^2 := by rw [hq1]; ring
  have hbase : 4*p^2-1 = q*(q+2) := by omega
  change multiplicity (4*p^2-1) (4*p^2-1).factorial = multiplicity (4*p^2) (4*p^2).factorial
  rw [hbase, FactorialNeighbors.left_value hprim hs4 hs, FactorialNeighbors.right_value hp h5]
  omega
