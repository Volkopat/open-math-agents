import OMAStatements.S_oeis_a088112

/-! One prime-reversal seed per exponent suffices. The square seed is 4. -/

namespace OMA.R_oeis_a088112_R1

open OMA.S_oeis_a088112

def H1 : Prop := ∃ k : ℕ, 2 ≤ k ∧ (rev (k^2)).Prime

def H2 : Prop := ∀ e : ℕ, 3 ≤ e → ∃ k : ℕ, 2 ≤ k ∧ (rev (k^e)).Prime

lemma append_zeros {v : ℕ} (hv : 0 < v) (j : ℕ) :
    rev (10^j*v) = rev v := by
  simp [rev, Nat.digits_base_pow_mul (by decide : 1 < 10) hv, List.reverse_append]

lemma roots_infinite {e k : ℕ} (hk : 2 ≤ k) (seed : (rev (k^e)).Prime) :
    {a : ℕ | 2 ≤ a ∧ (rev (a^e)).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  let a := 10^B*k
  have ka : k ≤ a := Nat.le_mul_of_pos_left _ (by positivity)
  have val : a^e = 10^(B*e)*k^e := by simp only [a, mul_pow, pow_mul]
  have good : (rev (a^e)).Prime := by
    rw [val, append_zeros (pow_pos (by omega) e)]
    exact seed
  refine ⟨a, ⟨by omega, good⟩, ?_⟩
  have hB := B.lt_pow_self (by decide : 1 < 10)
  have ba : 10^B ≤ a := Nat.le_mul_of_pos_right _ (by omega)
  omega

lemma square_values_infinite {k : ℕ} (hk : 2 ≤ k) (seed : (rev (k^2)).Prime) :
    {v : ℕ | (∃ a e : ℕ, 2 ≤ a ∧ 2 ≤ e ∧ v=a^e) ∧ (rev v).Prime}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro B
  let a := 10^B*k
  have ka : k ≤ a := Nat.le_mul_of_pos_left _ (by positivity)
  have val : a^2 = 10^(B*2)*k^2 := by simp only [a, mul_pow, pow_mul]
  have good : (rev (a^2)).Prime := by
    rw [val, append_zeros (pow_pos (by omega) 2)]
    exact seed
  refine ⟨a^2, ⟨⟨a,2,by omega,by decide,rfl⟩,good⟩, ?_⟩
  have hB := B.lt_pow_self (by decide : 1 < 10)
  have ba : 10^B ≤ a := Nat.le_mul_of_pos_right _ (by omega)
  have ap : a ≤ a^2 := Nat.le_self_pow (by decide) a
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a088112.main := by
  rintro square higher
  obtain ⟨k,hk,seed⟩ := square
  refine ⟨square_values_infinite hk seed, ?_⟩
  intro e he
  by_cases two : e=2
  · subst e
    exact roots_infinite hk seed
  · obtain ⟨a,ha,prime⟩ := higher e (by omega)
    exact roots_infinite ha prime

end OMA.R_oeis_a088112_R1
