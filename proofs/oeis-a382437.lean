import OMAStatements.S_oeis_a382437

namespace OMA.S_oeis_a382437_proof

private def p : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (2 * (p n).1 + 3 * (p n).2, (p n).1 + 2 * (p n).2)

private lemma p_succ (k : ℕ) :
    p (k + 1) = (2 * (p k).1 + 3 * (p k).2, (p k).1 + 2 * (p k).2) := rfl

private lemma p_add (m n : ℕ) :
    p (m + n) = ((p m).1 * (p n).1 + 3 * (p m).2 * (p n).2,
                 (p m).1 * (p n).2 + (p m).2 * (p n).1) := by
  induction n with
  | zero => simp [p]
  | succ n ih =>
    change p ((m + n) + 1) = _
    rw [p_succ, ih, p_succ]
    ext <;> dsimp <;> ring

private lemma p_pell (m : ℕ) : (p m).1 ^ 2 - 3 * (p m).2 ^ 2 = 1 := by
  induction m with
  | zero => simp [p]
  | succ m ih =>
    rw [p]
    dsimp
    calc (2 * (p m).1 + 3 * (p m).2) ^ 2 - 3 * ((p m).1 + 2 * (p m).2) ^ 2
        = (p m).1 ^ 2 - 3 * (p m).2 ^ 2 := by ring
      _ = 1 := ih

private def V (m : ℕ) : ℤ := 2 * (p m).1

private lemma V_rec (m : ℕ) : V (m + 2) + V m = 4 * V (m + 1) := by
  simp only [V, p]
  ring

private lemma V_two_mul (m : ℕ) : V (2 * m) = V m ^ 2 - 2 := by
  rw [two_mul, V, p_add]
  have h := p_pell m
  dsimp [V]
  calc 2 * ((p m).1 * (p m).1 + 3 * (p m).2 * (p m).2)
      = (2 * (p m).1) ^ 2 - 2 * ((p m).1 ^ 2 - 3 * (p m).2 ^ 2) := by ring
    _ = (2 * (p m).1) ^ 2 - 2 * 1 := by rw [h]
    _ = (2 * (p m).1) ^ 2 - 2 := by ring

private lemma V_pow_two (n : ℕ) : V (2 ^ n) = (OMA.S_oeis_a382437.a n : ℤ) + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', V_two_mul, ih, OMA.S_oeis_a382437.a]
    push_cast
    ring

private def F (m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (m + 1), 2 ^ k * Nat.choose (m + k) (2 * k)

private lemma F_eq_sum_range (n N : ℕ) (hN : n + 1 ≤ N) :
    F n = ∑ k ∈ Finset.range N, 2 ^ k * Nat.choose (n + k) (2 * k) := by
  unfold F
  apply Finset.sum_subset (Finset.range_mono hN)
  intro k _ hk
  simp only [Finset.mem_range, not_lt] at hk
  rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]

private lemma choose_two_step (n r : ℕ) :
    Nat.choose (n + 2) (r + 2) + Nat.choose n (r + 2) =
      2 * Nat.choose (n + 1) (r + 2) + Nat.choose n r := by
  rw [Nat.choose_succ_succ (n + 1) (r + 1)]
  rw [Nat.choose_succ_succ n r]
  rw [Nat.choose_succ_succ n (r + 1)]
  ring

private lemma F_rec (m : ℕ) : F (m + 2) + F m = 4 * F (m + 1) := by
  have h2 : F (m + 2) = ∑ k ∈ Finset.range (m + 3), 2 ^ k * Nat.choose (m + 2 + k) (2 * k) := rfl
  have h0 : F m = ∑ k ∈ Finset.range (m + 3), 2 ^ k * Nat.choose (m + k) (2 * k) :=
    F_eq_sum_range m (m + 3) (by omega)
  have h1 : F (m + 1) = ∑ k ∈ Finset.range (m + 3), 2 ^ k * Nat.choose (m + 1 + k) (2 * k) :=
    F_eq_sum_range (m + 1) (m + 3) (by omega)
  have hsum : F (m + 2) + F m =
      ∑ k ∈ Finset.range (m + 3),
        (2 ^ k * Nat.choose (m + 2 + k) (2 * k) + 2 ^ k * Nat.choose (m + k) (2 * k)) := by
    rw [h2, h0, Finset.sum_add_distrib]
  rw [hsum, Finset.sum_range_succ']
  have h_zero : 2 ^ 0 * Nat.choose (m + 2 + 0) (2 * 0) + 2 ^ 0 * Nat.choose (m + 0) (2 * 0) = 2 := by
    simp
  rw [h_zero]
  have h_step : ∀ j : ℕ,
      2 ^ (j + 1) * Nat.choose (m + 2 + (j + 1)) (2 * (j + 1)) +
          2 ^ (j + 1) * Nat.choose (m + (j + 1)) (2 * (j + 1)) =
        2 * (2 ^ (j + 1) * Nat.choose (m + 1 + (j + 1)) (2 * (j + 1))) +
          2 * (2 ^ j * Nat.choose (m + 1 + j) (2 * j)) := by
    intro j
    have hc := choose_two_step (m + j + 1) (2 * j)
    have ha : m + 2 + (j + 1) = (m + j + 1) + 2 := by omega
    have hb : m + (j + 1) = m + j + 1 := by omega
    have hd : m + 1 + (j + 1) = (m + j + 1) + 1 := by omega
    have he : m + 1 + j = m + j + 1 := by omega
    have hr : 2 * (j + 1) = 2 * j + 2 := by omega
    rw [ha, hb, hd, he, hr]
    calc 2 ^ (j + 1) * Nat.choose ((m + j + 1) + 2) (2 * j + 2) +
          2 ^ (j + 1) * Nat.choose (m + j + 1) (2 * j + 2)
        = 2 ^ (j + 1) * (Nat.choose ((m + j + 1) + 2) (2 * j + 2) +
            Nat.choose (m + j + 1) (2 * j + 2)) := by ring
      _ = 2 ^ (j + 1) * (2 * Nat.choose ((m + j + 1) + 1) (2 * j + 2) +
            Nat.choose (m + j + 1) (2 * j)) := by rw [hc]
      _ = 2 * (2 ^ (j + 1) * Nat.choose ((m + j + 1) + 1) (2 * j + 2)) +
            2 * (2 ^ j * Nat.choose (m + j + 1) (2 * j)) := by
          rw [pow_succ']
          ring
  simp_rw [h_step, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1_split : F (m + 1) =
      (∑ j ∈ Finset.range (m + 2), 2 ^ (j + 1) * Nat.choose (m + 1 + (j + 1)) (2 * (j + 1))) + 1 := by
    rw [h1, Finset.sum_range_succ']
    simp
  have h1_direct : F (m + 1) =
      ∑ j ∈ Finset.range (m + 2), 2 ^ j * Nat.choose (m + 1 + j) (2 * j) := rfl
  omega

private lemma F_add_eq_V (m : ℕ) : (F (m + 1) : ℤ) + (F m : ℤ) = V (m + 1) := by
  induction m using Nat.twoStepInduction with
  | zero =>
    have h0 : F 0 = 1 := by decide
    have h1 : F 1 = 3 := by decide
    rw [h0, h1]
    rfl
  | one =>
    have h1 : F 1 = 3 := by decide
    have h2 : F 2 = 11 := by decide
    rw [h1, h2]
    rfl
  | more m ih1 ih2 =>
    have hF1 : (F (m + 3) : ℤ) + (F (m + 1) : ℤ) = 4 * (F (m + 2) : ℤ) := by
      exact_mod_cast F_rec (m + 1)
    have hF0 : (F (m + 2) : ℤ) + (F m : ℤ) = 4 * (F (m + 1) : ℤ) := by
      exact_mod_cast F_rec m
    have hV := V_rec (m + 1)
    linarith

private lemma add_one_mul_choose_eq (n k : ℕ) :
    (n + 1) * Nat.choose n k = (k + 1) * Nat.choose (n + 1) (k + 1) := by
  by_cases hk : k ≤ n
  · have h := Nat.choose_succ_right_eq n k
    rw [Nat.choose_succ_succ n k]
    have hd : (k + 1) + (n - k) = n + 1 := by omega
    calc (n + 1) * Nat.choose n k
        = Nat.choose n k * (k + 1) + Nat.choose n k * (n - k) := by
          rw [← mul_add, hd, mul_comm]
      _ = Nat.choose n k * (k + 1) + Nat.choose n (k + 1) * (k + 1) := by rw [← h]
      _ = (k + 1) * (Nat.choose n k + Nat.choose n (k + 1)) := by ring
  · have h1 : Nat.choose n k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : Nat.choose (n + 1) (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    simp

private lemma mul_choose_add_choose (M j : ℕ) :
    (j + 1) * (Nat.choose (M + j + 1) (2 * j + 2) + Nat.choose (M + j) (2 * j + 2)) =
      M * Nat.choose (M + j) (2 * j + 1) := by
  by_cases hM : M ≤ j
  · have h1 : Nat.choose (M + j + 1) (2 * j + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : Nat.choose (M + j) (2 * j + 2) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h3 : Nat.choose (M + j) (2 * j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2, h3]
    simp
  · have hM' : j + 1 ≤ M := by omega
    have h1 := add_one_mul_choose_eq (M + j) (2 * j + 1)
    have h2 := Nat.choose_succ_right_eq (M + j) (2 * j + 1)
    have hb : 2 * j + 1 + 1 = 2 * j + 2 := by omega
    have hc : M + j - (2 * j + 1) = M - j - 1 := by omega
    rw [hb] at h1 h2
    rw [hc] at h2
    have h_double :
        2 * ((j + 1) * (Nat.choose (M + j + 1) (2 * j + 2) + Nat.choose (M + j) (2 * j + 2))) =
          2 * (M * Nat.choose (M + j) (2 * j + 1)) := by
      calc 2 * ((j + 1) * (Nat.choose (M + j + 1) (2 * j + 2) + Nat.choose (M + j) (2 * j + 2)))
          = (2 * j + 2) * Nat.choose (M + j + 1) (2 * j + 2) +
              Nat.choose (M + j) (2 * j + 2) * (2 * j + 2) := by ring
        _ = (M + j + 1) * Nat.choose (M + j) (2 * j + 1) +
              Nat.choose (M + j) (2 * j + 1) * (M - j - 1) := by rw [← h1, h2]
        _ = ((M + j + 1) + (M - j - 1)) * Nat.choose (M + j) (2 * j + 1) := by ring
        _ = 2 * (M * Nat.choose (M + j) (2 * j + 1)) := by
            have hd : M + j + 1 + (M - j - 1) = 2 * M := by omega
            rw [hd]
            ring
    omega

private lemma sum_eq_F_add (m : ℕ) :
    (∑ k ∈ Finset.Icc 1 (m + 1),
      ((m + 1 : ℚ) * 2 ^ k * (Nat.choose (m + 1 + k - 1) (2 * k - 1) : ℚ) / (k : ℚ))) + 2 =
      (F (m + 1) : ℚ) + (F m : ℚ) := by
  have hF0 : (F m : ℚ) = ∑ k ∈ Finset.range (m + 2), (2 : ℚ) ^ k * (Nat.choose (m + k) (2 * k) : ℚ) := by
    have h := F_eq_sum_range m (m + 2) (by omega)
    exact_mod_cast h
  have hF1 : (F (m + 1) : ℚ) = ∑ k ∈ Finset.range (m + 2), (2 : ℚ) ^ k * (Nat.choose (m + 1 + k) (2 * k) : ℚ) := by
    unfold F
    push_cast
    rfl
  rw [hF1, hF0, ← Finset.sum_add_distrib, Finset.sum_range_succ']
  have h_zero :
      (2 : ℚ) ^ 0 * (Nat.choose (m + 1 + 0) (2 * 0) : ℚ) +
        (2 : ℚ) ^ 0 * (Nat.choose (m + 0) (2 * 0) : ℚ) = 2 := by
    norm_num
  rw [h_zero]
  have h_icc : Finset.Icc 1 (m + 1) = (Finset.range (m + 1)).image (· + 1) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro ⟨hx1, hx2⟩
      exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  rw [h_icc, Finset.sum_image (fun a _ b _ h => by omega)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have hc : ((j + 1 : ℕ) : ℚ) *
      ((Nat.choose (m + 1 + (j + 1)) (2 * (j + 1)) : ℚ) +
        (Nat.choose (m + (j + 1)) (2 * (j + 1)) : ℚ)) =
      (m + 1 : ℚ) * (Nat.choose (m + 1 + j) (2 * j + 1) : ℚ) := by
    have hnat := mul_choose_add_choose (m + 1) j
    rw [show m + 1 + (j + 1) = m + 1 + j + 1 by omega,
        show m + (j + 1) = m + 1 + j by omega,
        show 2 * (j + 1) = 2 * j + 2 by omega]
    exact_mod_cast hnat
  have hj_ne : ((j + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have ha' : m + 1 + (j + 1) - 1 = m + 1 + j := by omega
  have hb' : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  rw [ha', hb']
  have h_div :
      (Nat.choose (m + 1 + (j + 1)) (2 * (j + 1)) : ℚ) +
        (Nat.choose (m + (j + 1)) (2 * (j + 1)) : ℚ) =
      (m + 1 : ℚ) * (Nat.choose (m + 1 + j) (2 * j + 1) : ℚ) / ((j + 1 : ℕ) : ℚ) := by
    rw [eq_div_iff hj_ne]
    linarith [hc]
  calc (m + 1 : ℚ) * 2 ^ (j + 1) * (Nat.choose (m + 1 + j) (2 * j + 1) : ℚ) / ((j + 1 : ℕ) : ℚ)
      = (2 : ℚ) ^ (j + 1) * ((m + 1 : ℚ) * (Nat.choose (m + 1 + j) (2 * j + 1) : ℚ) / ((j + 1 : ℕ) : ℚ)) := by ring
    _ = (2 : ℚ) ^ (j + 1) * ((Nat.choose (m + 1 + (j + 1)) (2 * (j + 1)) : ℚ) +
          (Nat.choose (m + (j + 1)) (2 * (j + 1)) : ℚ)) := by rw [← h_div]
    _ = (2 : ℚ) ^ (j + 1) * (Nat.choose (m + 1 + (j + 1)) (2 * (j + 1)) : ℚ) +
          (2 : ℚ) ^ (j + 1) * (Nat.choose (m + (j + 1)) (2 * (j + 1)) : ℚ) := by ring

end OMA.S_oeis_a382437_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a382437.main := by
  intro n
  have hp : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  set m := 2 ^ n - 1
  have hm : 2 ^ n = m + 1 := by omega
  have hsum := OMA.S_oeis_a382437_proof.sum_eq_F_add m
  have hFV : ((OMA.S_oeis_a382437_proof.F (m + 1) : ℤ) + (OMA.S_oeis_a382437_proof.F m : ℤ) : ℚ) =
      (OMA.S_oeis_a382437_proof.V (m + 1) : ℚ) := by
    exact_mod_cast OMA.S_oeis_a382437_proof.F_add_eq_V m
  have hVa : (OMA.S_oeis_a382437_proof.V (2 ^ n) : ℚ) = (OMA.S_oeis_a382437.a n : ℚ) + 2 := by
    exact_mod_cast OMA.S_oeis_a382437_proof.V_pow_two n
  have hm_q : ((m + 1 : ℕ) : ℚ) = (2 : ℚ) ^ n := by
    have : m + 1 = 2 ^ n := hm.symm
    exact_mod_cast this
  rw [hm] at hVa
  rw [hVa] at hFV
  have h_eq :
      ∑ k ∈ Finset.Icc 1 (2 ^ n),
        (2 : ℚ) ^ n * 2 ^ k * (Nat.choose (2 ^ n + k - 1) (2 * k - 1) : ℚ) / (k : ℚ) =
      ∑ k ∈ Finset.Icc 1 (m + 1),
        (m + 1 : ℚ) * 2 ^ k * (Nat.choose (m + 1 + k - 1) (2 * k - 1) : ℚ) / (k : ℚ) := by
    rw [hm]
    apply Finset.sum_congr rfl
    intro k _
    have hm_q' : (2 : ℚ) ^ n = (m : ℚ) + 1 := by
      push_cast at hm_q
      exact hm_q.symm
    rw [hm_q']
  rw [h_eq]
  push_cast at hFV
  linarith
