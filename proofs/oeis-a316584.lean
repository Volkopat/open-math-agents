import OMAStatements.S_oeis_a316584

namespace OMA.S_oeis_a316584

open Matrix


section Field

variable {p : ℕ} [hp : Fact p.Prime]

lemma sq_eq (N : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    N * N = (N 0 0 + N 1 1) • N - (N 0 0 * N 1 1 - N 0 1 * N 1 0) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply] <;> ring

lemma smul_pow (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (t : ZMod p) (h : N * N = t • N) :
    ∀ k, N ^ (k + 1) = t ^ k • N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, smul_mul_assoc, h, smul_smul, pow_succ]

lemma nil_of_pow (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (h : N ^ p = 0) : N * N = 0 := by
  have hdet : N.det = 0 := by
    have : N.det ^ p = 0 := by rw [← det_pow, h, det_zero]
    exact pow_eq_zero_iff (hp.out.ne_zero) |>.mp this
  rw [det_fin_two] at hdet
  have hsq : N * N = (N 0 0 + N 1 1) • N := by
    rw [sq_eq, hdet, zero_smul, sub_zero]
  have hp1 : p = (p - 1) + 1 := by have := hp.out.two_le; omega
  have hpow := smul_pow N _ hsq (p - 1)
  rw [← hp1, h] at hpow
  by_cases ht : N 0 0 + N 1 1 = 0
  · rw [hsq, ht, zero_smul]
  · have : (N 0 0 + N 1 1) ^ (p - 1) ≠ 0 := pow_ne_zero _ ht
    have hN : N = 0 := by
      rcases smul_eq_zero.mp hpow.symm with h' | h'
      · exact absurd h' this
      · exact h'
    rw [hN, zero_mul]

lemma one_add_pow (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (h : N * N = 0) :
    ∀ k : ℕ, (1 + N) ^ k = 1 + (k : ZMod p) • N := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    have : (1 + (k : ZMod p) • N) * (1 + N) = 1 + N + (k : ZMod p) • N + (k : ZMod p) • (N * N) := by
      rw [add_mul, one_mul, mul_add, mul_one, smul_mul_assoc]
      abel
    rw [this, h, smul_zero, add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

lemma pow_eq_one_iff (M : Matrix (Fin 2) (Fin 2) (ZMod p)) :
    M ^ p = 1 ↔ (M - 1) * (M - 1) = 0 := by
  constructor
  · intro h
    apply nil_of_pow
    rw [sub_pow_char_of_commute _ (Commute.one_right M), h, one_pow, sub_self]
  · intro h
    have := one_add_pow (M - 1) h p
    rw [add_sub_cancel, ZMod.natCast_self, zero_smul, add_zero] at this
    exact this

/-- Elements of order dividing p correspond to square-zero matrices. -/
noncomputable def equivNil :
    {x : GL (Fin 2) (ZMod p) // x ^ p = 1} ≃ {N : Matrix (Fin 2) (Fin 2) (ZMod p) // N * N = 0} where
  toFun x := ⟨(x.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1, by
    rw [← pow_eq_one_iff]
    have := congrArg Units.val x.2
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this⟩
  invFun N := ⟨⟨1 + N.1, 1 - N.1, by
      have : (1 + N.1) * (1 - N.1) = 1 - N.1 * N.1 := by noncomm_ring
      rw [this, N.2, sub_zero], by
      have : (1 - N.1) * (1 + N.1) = 1 - N.1 * N.1 := by noncomm_ring
      rw [this, N.2, sub_zero]⟩, by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    show (1 + N.1) ^ p = 1
    rw [pow_eq_one_iff, add_sub_cancel_left]
    exact N.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    show 1 + ((x.1 : Matrix (Fin 2) (Fin 2) (ZMod p)) - 1) = x.1
    abel
  right_inv N := by
    apply Subtype.ext
    show 1 + N.1 - 1 = N.1
    abel

lemma nil_entries (N : Matrix (Fin 2) (Fin 2) (ZMod p)) (h : N * N = 0) :
    N 1 1 = -N 0 0 ∧ N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
  have e : ∀ i j, (N * N) i j = 0 := fun i j => by rw [h]; rfl
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  set a := N 0 0
  set b := N 0 1
  set c := N 1 0
  set d := N 1 1
  have had : a + d = 0 := by
    by_contra hne
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by rw [← e01]; ring
      exact (mul_eq_zero.mp this).resolve_right hne
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by rw [← e10]; ring
      exact (mul_eq_zero.mp this).resolve_right hne
    have ha : a = 0 := by
      rw [hb, zero_mul, add_zero] at e00
      exact mul_self_eq_zero.mp e00
    have hd : d = 0 := by
      rw [hb, mul_zero, zero_add] at e11
      exact mul_self_eq_zero.mp e11
    exact hne (by rw [ha, hd, add_zero])
  exact ⟨by linear_combination had, e00⟩

/-- Square-zero matrices correspond to pairs (b, s). -/
noncomputable def equivPair :
    {N : Matrix (Fin 2) (Fin 2) (ZMod p) // N * N = 0} ≃ ZMod p × ZMod p where
  toFun N := (N.1 0 1, if N.1 0 1 = 0 then N.1 1 0 else N.1 0 0)
  invFun q := ⟨if q.1 = 0 then !![0, 0; q.2, 0] else !![q.2, q.1; -(q.2 * q.2) / q.1, -q.2], by
    split_ifs with h
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩
  left_inv N := by
    obtain ⟨N, hN⟩ := N
    obtain ⟨hd, hrel⟩ := nil_entries N hN
    apply Subtype.ext
    simp only
    by_cases hb : N 0 1 = 0
    · rw [if_pos hb, if_pos hb]
      have ha : N 0 0 = 0 := by
        rw [hb, zero_mul, add_zero] at hrel
        exact mul_self_eq_zero.mp hrel
      ext i j
      fin_cases i <;> fin_cases j <;> simp [ha, hb, hd]
    · rw [if_neg hb, if_neg hb]
      have hc : N 1 0 = -(N 0 0 * N 0 0) / N 0 1 := by
        field_simp
        linear_combination hrel
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hd, hc]
  right_inv q := by
    obtain ⟨b, s⟩ := q
    by_cases hb : b = 0
    · simp [hb]
    · simp [hb]

theorem T_prime : T p p = p ^ 2 := by
  unfold T
  rw [Nat.card_congr (equivNil.trans equivPair), Nat.card_prod, Nat.card_zmod, sq]

end Field

/-- Howroyd's conjecture. -/
theorem conjecture : ∀ p : ℕ, p.Prime → T p p = p ^ 2 := by
  intro p hp
  have : Fact p.Prime := ⟨hp⟩
  exact T_prime

end OMA.S_oeis_a316584

theorem OMA.solution : type_of% @OMA.S_oeis_a316584.main :=
  OMA.S_oeis_a316584.conjecture
