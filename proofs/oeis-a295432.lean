import OMAStatements.S_oeis_a295432
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Tactic

namespace BalaDivisibility

def lower (t : ℕ) := 2*(t/2)+t/3+t/12
def upper (t : ℕ) := t+t/4+t/6

-- Legendre's summand is periodic after the two sides are subtracted.
lemma table (t : ℕ) :
    lower t + (if t%12=1 ∨ t%12=5 ∨ t%12=7 ∨ t%12=8 ∨ t%12=9 ∨ t%12=11
               then 1 else 0) = upper t := by
  obtain ⟨a, b, hb, rfl⟩ : ∃ a b, b < 12 ∧ t = b+12*a :=
    ⟨t/12, t%12, Nat.mod_lt _ (by decide), (Nat.mod_add_div t 12).symm⟩
  interval_cases b <;> simp [lower, upper, Nat.add_mul_div_left,
    Nat.add_mul_mod_self_left] <;> omega

lemma floor_scale (c k n q : ℕ) (hc : 0 < c) (hck : c*k = 12) :
    12*n/q/c = k*n/q := by
  rw [← hck, Nat.mul_assoc, Nat.div_div_eq_div_mul, Nat.mul_comm q c,
    Nat.mul_div_mul_left _ _ hc]

lemma two_factors (n q : ℕ) (hn : 0 < n) (hq : 1 < q) :
    ¬ (q ∣ 6*n+1 ∧ q ∣ 12*n-1) := by
  rintro ⟨h₁, h₂⟩
  have h3 : q ∣ 3 := by
    rw [show 3 = 2*(6*n+1)-(12*n-1) by omega]
    exact Nat.dvd_sub (dvd_mul_of_dvd_right h₁ 2) h₂
  have := Nat.le_of_dvd (by decide : 0 < 3) h3
  interval_cases q <;> omega

lemma first_residue (n q : ℕ) (hq : 1 < q) (hd : q ∣ 6*n+1) :
    (12*n/q)%12 = 1 ∨ (12*n/q)%12 = 9 := by
  obtain ⟨k, hk⟩ := hd
  cases k with
  | zero => simp at hk
  | succ k =>
    have dk : k+1 ∣ 6*n+1 := ⟨q, by simpa [Nat.mul_comm] using hk⟩
    have h2 : ¬2 ∣ k+1 := fun h => (by omega : ¬2 ∣ 6*n+1) (h.trans dk)
    have h3 : ¬3 ∣ k+1 := fun h => (by omega : ¬3 ∣ 6*n+1) (h.trans dk)
    have ht : 12*n/q = 2*k+1 := by
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).2
        nlinarith [hk]
      · apply (Nat.le_div_iff_mul_le (by omega : 0 < q)).2
        nlinarith [hk]
    rw [ht]
    omega

lemma second_residue (n q : ℕ) (hn : 0 < n) (hq : 1 < q) (hd : q ∣ 12*n-1) :
    (12*n/q)%12=1 ∨ (12*n/q)%12=5 ∨ (12*n/q)%12=7 ∨ (12*n/q)%12=11 := by
  obtain ⟨k, hk⟩ := hd
  have dk : k ∣ 12*n-1 := ⟨q, by simpa [Nat.mul_comm] using hk⟩
  have h2 : ¬2 ∣ k := fun h => (by omega : ¬2 ∣ 12*n-1) (h.trans dk)
  have h3 : ¬3 ∣ k := fun h => (by omega : ¬3 ∣ 12*n-1) (h.trans dk)
  have he : 12*n = q*k+1 := by omega
  have ht : 12*n/q = k := by
    apply Nat.le_antisymm
    · apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul (by omega : 0 < q)).2
      nlinarith [he]
    · apply (Nat.le_div_iff_mul_le (by omega : 0 < q)).2
      nlinarith [he]
  rw [ht]
  omega

lemma one_level (n q : ℕ) (hn : 0 < n) (hq : 1 < q) :
    (if q ∣ 6*n+1 then 1 else 0) + (if q ∣ 12*n-1 then 1 else 0) +
      (6*n/q+6*n/q+4*n/q+n/q) ≤ 12*n/q+3*n/q+2*n/q := by
  have h := table (12*n/q)
  unfold lower upper at h
  rw [floor_scale 2 6 n q (by decide) (by decide),
      floor_scale 3 4 n q (by decide) (by decide),
      floor_scale 12 1 n q (by decide) (by decide),
      floor_scale 4 3 n q (by decide) (by decide),
      floor_scale 6 2 n q (by decide) (by decide), one_mul] at h
  by_cases h₁ : q ∣ 6*n+1
  · have h₂ : ¬q ∣ 12*n-1 := fun h₂ => two_factors n q hn hq ⟨h₁,h₂⟩
    have r := first_residue n q hq h₁
    simp only [if_pos h₁, if_neg h₂]
    split at h <;> omega
  · by_cases h₂ : q ∣ 12*n-1
    · have r := second_residue n q hn hq h₂
      simp only [if_neg h₁, if_pos h₂]
      split at h <;> omega
    · simp only [if_neg h₁, if_neg h₂]
      split at h <;> omega

lemma valuations (n p : ℕ) (hn : 0 < n) (hp : p.Prime) :
    (6*n+1).factorization p + (12*n-1).factorization p +
      ((6*n).factorial.factorization p + (6*n).factorial.factorization p +
       (4*n).factorial.factorization p + n.factorial.factorization p) ≤
      (12*n).factorial.factorization p + (3*n).factorial.factorization p +
      (2*n).factorial.factorization p := by
  let b := 12*n+2
  have bound (k : ℕ) (hk : k ≤ 12*n+1) : Nat.log p k < b :=
    (Nat.log_le_self p k).trans_lt (by dsimp [b]; omega)
  have val (k : ℕ) (hk : 0 < k) (hle : k ≤ 12*n+1) :
      k.factorization p = ∑ i ∈ Finset.Ico 1 b, if p^i ∣ k then 1 else 0 := by
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp hk
      (Nat.lt_pow_of_log_lt hp.one_lt (bound k hle))]
    simp [Finset.sum_boole]
  rw [val (6*n+1) (by omega) (by omega), val (12*n-1) (by omega) (by omega)]
  simp only [Nat.factorization_factorial hp (bound (6*n) (by omega)),
    Nat.factorization_factorial hp (bound (4*n) (by omega)),
    Nat.factorization_factorial hp (bound n (by omega)),
    Nat.factorization_factorial hp (bound (12*n) (by omega)),
    Nat.factorization_factorial hp (bound (3*n) (by omega)),
    Nat.factorization_factorial hp (bound (2*n) (by omega)), ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact one_level n (p^i) hn (one_lt_pow₀ hp.one_lt (by have := (Finset.mem_Ico.mp hi).1; omega))

lemma strict_factorial (p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    (p-1)*m.factorial.factorization p < m := by
  have h := Nat.sub_one_mul_factorization_factorial (n := m) hp
  have last := Nat.getLast_digit_ne_zero p hm.ne'
  have mem := List.getLast_mem (l := p.digits m) (Nat.digits_ne_nil_iff_ne_zero.mpr hm.ne')
  have le := List.le_sum_of_mem mem
  omega

lemma two_prime (n : ℕ) (hn : 0 < n) :
    1 + ((6*n).factorial.factorization 2 + (6*n).factorial.factorization 2 +
       (4*n).factorial.factorization 2 + n.factorial.factorization 2) ≤
      (12*n).factorial.factorization 2 + (3*n).factorial.factorization 2 +
      (2*n).factorial.factorization 2 := by
  have h12 := Nat.factorization_factorial_mul (n := 6*n) Nat.prime_two
  have h6 := Nat.factorization_factorial_mul (n := 3*n) Nat.prime_two
  have h4 := Nat.factorization_factorial_mul (n := 2*n) Nat.prime_two
  have h := strict_factorial 2 n Nat.prime_two hn
  norm_num [← Nat.mul_assoc] at h12 h6 h4 h
  omega

lemma three_prime (n : ℕ) (hn : 0 < n) :
    1 + ((6*n).factorial.factorization 3 + (6*n).factorial.factorization 3 +
       (4*n).factorial.factorization 3 + n.factorial.factorization 3) ≤
      (12*n).factorial.factorization 3 + (3*n).factorial.factorization 3 +
      (2*n).factorial.factorization 3 := by
  have h12 := Nat.factorization_factorial_mul (n := 4*n) Nat.prime_three
  have h6 := Nat.factorization_factorial_mul (n := 2*n) Nat.prime_three
  have h3 := Nat.factorization_factorial_mul (n := n) Nat.prime_three
  have h := strict_factorial 3 (2*n) Nat.prime_three (by omega)
  norm_num [← Nat.mul_assoc] at h12 h6 h3 h
  omega

end BalaDivisibility

open BalaDivisibility

theorem OMA.solution : type_of% @OMA.S_oeis_a295432.main := by
  intro n hn
  have positiveFactor : 0 < 12*n-1 := by omega
  apply (Nat.factorization_le_iff_dvd (by positivity) (by positivity)).mp
  intro p
  by_cases hp : p.Prime
  · simp (disch := positivity) only [Nat.factorization_mul, Finsupp.add_apply]
    by_cases h2 : p = 2
    · subst p
      have hu : ¬2 ∣ 6*n+1 := by omega
      have hv : ¬2 ∣ 12*n-1 := by omega
      rw [Nat.factorization_eq_zero_of_not_dvd hu, Nat.factorization_eq_zero_of_not_dvd hv]
      rw [show (6 : ℕ).factorization 2 = 1 by
        rw [show (6 : ℕ) = 2*3 by decide, Nat.factorization_mul (by decide : (2:ℕ) ≠ 0)
          (by decide : (3:ℕ) ≠ 0), Finsupp.add_apply, Nat.prime_two.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 3)]]
      simp only [add_zero]
      exact two_prime n hn
    by_cases h3 : p = 3
    · subst p
      have hu : ¬3 ∣ 6*n+1 := by omega
      have hv : ¬3 ∣ 12*n-1 := by omega
      rw [Nat.factorization_eq_zero_of_not_dvd hu, Nat.factorization_eq_zero_of_not_dvd hv]
      rw [show (6 : ℕ).factorization 3 = 1 by
        rw [show (6 : ℕ) = 2*3 by decide, Nat.factorization_mul (by decide : (2:ℕ) ≠ 0)
          (by decide : (3:ℕ) ≠ 0), Finsupp.add_apply, Nat.prime_three.factorization_self,
          Nat.factorization_eq_zero_of_not_dvd (by decide : ¬3 ∣ 2)]]
      simp only [add_zero]
      exact three_prime n hn
    have h6 : ¬p ∣ 6 := by
      rw [show 6 = 2*3 by decide, hp.dvd_mul]
      simpa [Nat.prime_dvd_prime_iff_eq hp Nat.prime_two,
        Nat.prime_dvd_prime_iff_eq hp Nat.prime_three] using (show ¬(p = 2 ∨ p = 3) by tauto)
    rw [Nat.factorization_eq_zero_of_not_dvd h6, zero_add]
    exact valuations n p hn hp
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
