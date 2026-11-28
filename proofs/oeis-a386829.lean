import OMAStatements.S_oeis_a386829

open scoped BigOperators

namespace OMA.S_oeis_a386829_proof

private noncomputable def c (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) * 3 ^ k * 2 ^ (n - k)

private noncomputable def I (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), c n k / (2 * (n : ℚ) + 1 - k)

private lemma succ_mul_choose_eq' (n k : ℕ) :
    (n + 1) * n.choose k = (k + 1) * (n + 1).choose (k + 1) := by
  by_cases hk : k ≤ n
  · rw [Nat.choose_succ_succ, mul_add, mul_comm (k + 1) (n.choose (k + 1)),
      Nat.choose_succ_right_eq n k]
    calc
      (n + 1) * n.choose k = (k + 1 + (n - k)) * n.choose k := by congr 1; omega
      _ = (k + 1) * n.choose k + n.choose k * (n - k) := by ring
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (n + 1).choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2, mul_zero, mul_zero]

private lemma sum_c (n : ℕ) : ∑ k ∈ Finset.range (n + 1), c n k = (5 : ℚ) ^ n := by
  have h := add_pow (3 : ℚ) 2 n
  have h5 : (3 + 2 : ℚ) ^ n = (5 : ℚ) ^ n := by norm_num
  rw [h5] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold c
  ring

private lemma c_succ_n (n j : ℕ) (hn : 1 ≤ n) (hj : j < n) :
    (j + 1 : ℚ) * c n (j + 1) = 3 * (n : ℚ) * c (n - 1) j := by
  unfold c
  have hnat : (j + 1) * n.choose (j + 1) = n * (n - 1).choose j := by
    have h := succ_mul_choose_eq' (n - 1) j
    have hm : n - 1 + 1 = n := by omega
    rw [hm] at h
    exact h.symm
  have hcast := congrArg (Nat.cast (R := ℚ)) hnat
  push_cast at hcast
  have hsub : n - (j + 1) = (n - 1) - j := by omega
  rw [hsub]
  calc
    (j + 1 : ℚ) * ((n.choose (j + 1) : ℚ) * 3 ^ (j + 1) * 2 ^ ((n - 1) - j))
      = ((j + 1 : ℚ) * (n.choose (j + 1) : ℚ)) * (3 * 3 ^ j) * 2 ^ ((n - 1) - j) := by
          rw [pow_succ']; ring
    _ = ((n : ℚ) * ((n - 1).choose j : ℚ)) * (3 * 3 ^ j) * 2 ^ ((n - 1) - j) := by rw [hcast]
    _ = 3 * (n : ℚ) * (((n - 1).choose j : ℚ) * 3 ^ j * 2 ^ ((n - 1) - j)) := by ring

private lemma c_step (m j : ℕ) (hj : j ≤ m) :
    2 * (j + 1 : ℚ) * c m (j + 1) = 3 * ((m : ℚ) - j) * c m j := by
  unfold c
  by_cases hlt : j < m
  · have hnat : m.choose (j + 1) * (j + 1) = m.choose j * (m - j) :=
      Nat.choose_succ_right_eq m j
    have hcast := congrArg (Nat.cast (R := ℚ)) hnat
    push_cast at hcast
    rw [Nat.cast_sub (by omega)] at hcast
    have hpow2 : (2 : ℚ) ^ (m - j) = 2 * (2 : ℚ) ^ (m - (j + 1)) := by
      have hm : m - j = (m - (j + 1)) + 1 := by omega
      rw [hm, pow_succ']
    calc
      2 * (j + 1 : ℚ) * ((m.choose (j + 1) : ℚ) * 3 ^ (j + 1) * 2 ^ (m - (j + 1)))
        = ((m.choose (j + 1) : ℚ) * (j + 1 : ℚ)) * (3 * 3 ^ j) * (2 * 2 ^ (m - (j + 1))) := by
            rw [pow_succ']; ring
      _ = ((m.choose j : ℚ) * ((m : ℚ) - j)) * (3 * 3 ^ j) * 2 ^ (m - j) := by
            rw [hcast, ← hpow2]
      _ = 3 * ((m : ℚ) - j) * ((m.choose j : ℚ) * 3 ^ j * 2 ^ (m - j)) := by ring
  · have hjeq : j = m := by omega
    subst hjeq
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

private lemma choose_identity (n k : ℕ) (hk : k ≤ n) :
    (2 * n + 1 - k) * ((2 * n + 1).choose k * (2 * n - k).choose (n - k)) =
      (2 * n + 1) * ((2 * n).choose n * n.choose k) := by
  have h1 : (2 * n + 1 - k) * (2 * n + 1).choose k = (2 * n + 1) * (2 * n).choose k := by
    have hk2 : k ≤ 2 * n + 1 := by omega
    have hsym := Nat.choose_symm hk2
    have hsuc := succ_mul_choose_eq' (2 * n) (2 * n - k)
    have hsub : 2 * n + 1 - k = (2 * n - k) + 1 := by omega
    rw [hsub] at hsym ⊢
    rw [← hsym, ← hsuc]
    have hsym2 : (2 * n).choose (2 * n - k) = (2 * n).choose k := Nat.choose_symm (by omega)
    rw [hsym2]
  have h2 : (2 * n).choose n * n.choose k = (2 * n).choose k * (2 * n - k).choose (n - k) :=
    Nat.choose_mul hk
  calc
    (2 * n + 1 - k) * ((2 * n + 1).choose k * (2 * n - k).choose (n - k))
      = ((2 * n + 1 - k) * (2 * n + 1).choose k) * (2 * n - k).choose (n - k) := by ring
    _ = ((2 * n + 1) * (2 * n).choose k) * (2 * n - k).choose (n - k) := by rw [h1]
    _ = (2 * n + 1) * ((2 * n).choose k * (2 * n - k).choose (n - k)) := by ring
    _ = (2 * n + 1) * ((2 * n).choose n * n.choose k) := by rw [h2]

private lemma a_eq_mul_I (n : ℕ) :
    (OMA.S_oeis_a386829.a n : ℚ) =
      (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ) * I n := by
  unfold OMA.S_oeis_a386829.a I c
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hden : (2 * (n : ℚ) + 1 - (k : ℚ)) ≠ 0 := by
    have : (k : ℚ) ≤ n := Nat.cast_le.mpr hk_le
    linarith
  have hid := congrArg (Nat.cast (R := ℚ)) (choose_identity n k hk_le)
  push_cast at hid
  rw [Nat.cast_sub (by omega)] at hid
  push_cast at hid
  rw [mul_div_assoc', eq_div_iff hden]
  calc
    3 ^ k * 2 ^ (n - k) * ((2 * n + 1).choose k : ℚ) * ((2 * n - k).choose (n - k) : ℚ) *
        (2 * (n : ℚ) + 1 - k)
      = 3 ^ k * 2 ^ (n - k) *
          ((2 * (n : ℚ) + 1 - k) * (((2 * n + 1).choose k : ℚ) * ((2 * n - k).choose (n - k) : ℚ))) := by ring
    _ = 3 ^ k * 2 ^ (n - k) *
          ((2 * (n : ℚ) + 1) * (((2 * n).choose n : ℚ) * (n.choose k : ℚ))) := by rw [hid]
    _ = (2 * (n : ℚ) + 1) * ((2 * n).choose n : ℚ) * ((n.choose k : ℚ) * 3 ^ k * 2 ^ (n - k)) := by ring

private lemma I_rec1 (n : ℕ) (hn : 1 ≤ n) :
    (8 * (n : ℚ) + 4) * I n + 9 * (n : ℚ) * I (n - 1) = 7 * (5 : ℚ) ^ n := by
  have hsplit : (8 * (n : ℚ) + 4) * I n =
      4 * (5 : ℚ) ^ n + ∑ j ∈ Finset.range n, 12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) := by
    unfold I
    rw [Finset.mul_sum]
    have hterm : ∑ k ∈ Finset.range (n + 1), (8 * (n : ℚ) + 4) * (c n k / (2 * (n : ℚ) + 1 - k)) =
        ∑ k ∈ Finset.range (n + 1), (4 * c n k + 4 * (k : ℚ) * c n k / (2 * (n : ℚ) + 1 - k)) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hden : 2 * (n : ℚ) + 1 - k ≠ 0 := by
        have : (k : ℚ) ≤ n := Nat.cast_le.mpr hk_le
        linarith
      calc
        (8 * (n : ℚ) + 4) * (c n k / (2 * (n : ℚ) + 1 - k))
          = (4 * (2 * (n : ℚ) + 1 - k) * c n k + 4 * (k : ℚ) * c n k) / (2 * (n : ℚ) + 1 - k) := by
              ring
        _ = 4 * c n k * ((2 * (n : ℚ) + 1 - k) / (2 * (n : ℚ) + 1 - k)) +
              4 * (k : ℚ) * c n k / (2 * (n : ℚ) + 1 - k) := by ring
        _ = 4 * c n k + 4 * (k : ℚ) * c n k / (2 * (n : ℚ) + 1 - k) := by
              rw [div_self hden, mul_one]
    rw [hterm, Finset.sum_add_distrib]
    have h4 : ∑ k ∈ Finset.range (n + 1), 4 * c n k = 4 * (5 : ℚ) ^ n := by
      rw [← Finset.mul_sum, sum_c]
    rw [h4]
    congr 1
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < n := Finset.mem_range.mp hj
    have hc := c_succ_n n j hn hj_lt
    push_cast
    have hden : 2 * (n : ℚ) + 1 - ((j : ℚ) + 1) = 2 * (n : ℚ) - j := by ring
    rw [hden]
    calc
      4 * ((j : ℚ) + 1) * c n (j + 1) / (2 * (n : ℚ) - j)
        = 4 * ((j + 1 : ℚ) * c n (j + 1)) / (2 * (n : ℚ) - j) := by ring
      _ = 4 * (3 * (n : ℚ) * c (n - 1) j) / (2 * (n : ℚ) - j) := by rw [hc]
      _ = 12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) := by ring
  have hIprev : 9 * (n : ℚ) * I (n - 1) =
      ∑ j ∈ Finset.range n, 9 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - 1 - j) := by
    unfold I
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      rw [Nat.cast_sub hn]
      push_cast
      ring
    rw [hcast]
    ring
  have h5 : 3 * (5 : ℚ) ^ n = ∑ j ∈ Finset.range n, 15 * c (n - 1) j := by
    have hpow : (5 : ℚ) ^ n = 5 * (5 : ℚ) ^ (n - 1) := by
      have hn1 : n = (n - 1) + 1 := by omega
      conv_lhs => rw [hn1, pow_succ']
    have hsum := sum_c (n - 1)
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1] at hsum
    rw [hpow, ← hsum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  let G : ℕ → ℚ := fun j => -(6 * (j : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j))
  have htel : ∑ j ∈ Finset.range n,
      (12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) +
        9 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - 1 - j) - 15 * c (n - 1) j) =
      ∑ j ∈ Finset.range n, (G (j + 1) - G j) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj_lt : j < n := Finset.mem_range.mp hj
    have hj_le : j ≤ n - 1 := by omega
    have hstep := c_step (n - 1) j hj_le
    have hcast : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      rw [Nat.cast_sub hn]
      push_cast
      ring
    rw [hcast] at hstep
    have hd1 : 2 * (n : ℚ) - j ≠ 0 := by
      have : (j : ℚ) + 1 ≤ n := by exact_mod_cast hj_lt
      linarith
    have hd2 : 2 * (n : ℚ) - 1 - j ≠ 0 := by
      have : (j : ℚ) + 1 ≤ n := by exact_mod_cast hj_lt
      linarith
    dsimp only [G]
    push_cast
    have hd2' : 2 * (n : ℚ) - ((j : ℚ) + 1) = 2 * (n : ℚ) - 1 - j := by ring
    rw [hd2']
    have hA : 12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) -
        6 * (j : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) = 6 * c (n - 1) j := by
      calc
        12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) -
            6 * (j : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j)
          = 6 * c (n - 1) j * ((2 * (n : ℚ) - j) / (2 * (n : ℚ) - j)) := by ring
        _ = 6 * c (n - 1) j := by rw [div_self hd1, mul_one]
    have hB : 9 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - 1 - j) +
        6 * ((j : ℚ) + 1) * c (n - 1) (j + 1) / (2 * (n : ℚ) - 1 - j) = 9 * c (n - 1) j := by
      have hmul : 6 * ((j : ℚ) + 1) * c (n - 1) (j + 1) =
          9 * ((n : ℚ) - 1 - j) * c (n - 1) j := by
        linear_combination 3 * hstep
      calc
        9 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - 1 - j) +
            6 * ((j : ℚ) + 1) * c (n - 1) (j + 1) / (2 * (n : ℚ) - 1 - j)
          = (9 * (n : ℚ) * c (n - 1) j + 9 * ((n : ℚ) - 1 - j) * c (n - 1) j) /
              (2 * (n : ℚ) - 1 - j) := by rw [hmul]; ring
        _ = 9 * c (n - 1) j * ((2 * (n : ℚ) - 1 - j) / (2 * (n : ℚ) - 1 - j)) := by ring
        _ = 9 * c (n - 1) j := by rw [div_self hd2, mul_one]
    linear_combination hA + hB
  have hsumG : ∑ j ∈ Finset.range n, (G (j + 1) - G j) = G n - G 0 :=
    Finset.sum_range_sub G n
  have hG0 : G 0 = 0 := by simp [G]
  have hGn : G n = 0 := by
    simp only [G]
    unfold c
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [hG0, hGn, sub_zero] at hsumG
  rw [hsumG] at htel
  have hdiff : (8 * (n : ℚ) + 4) * I n + 9 * (n : ℚ) * I (n - 1) - 7 * (5 : ℚ) ^ n = 0 := by
    calc
      (8 * (n : ℚ) + 4) * I n + 9 * (n : ℚ) * I (n - 1) - 7 * (5 : ℚ) ^ n
        = (4 * (5 : ℚ) ^ n +
            ∑ j ∈ Finset.range n, 12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j)) +
          ∑ j ∈ Finset.range n, 9 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - 1 - j) -
          (4 * (5 : ℚ) ^ n + 3 * (5 : ℚ) ^ n) := by rw [hsplit, hIprev]; ring
      _ = ∑ j ∈ Finset.range n,
            (12 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - j) +
              9 * (n : ℚ) * c (n - 1) j / (2 * (n : ℚ) - 1 - j) - 15 * c (n - 1) j) := by
          rw [h5]
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          ring
      _ = 0 := htel
  linear_combination hdiff

private lemma central_binom_succ (m : ℕ) :
    (m + 1) * (2 * (m + 1)).choose (m + 1) = 2 * (2 * m + 1) * (2 * m).choose m := by
  have h1 := succ_mul_choose_eq' (2 * m + 1) m
  have h2 := succ_mul_choose_eq' (2 * m) m
  have h3 := Nat.choose_symm (by omega : m ≤ 2 * m + 1)
  have hsub : 2 * m + 1 - m = m + 1 := by omega
  rw [hsub] at h3
  have h4 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
  calc
    (m + 1) * (2 * (m + 1)).choose (m + 1)
      = (m + 1) * (2 * m + 1 + 1).choose (m + 1) := by rw [h4]
    _ = (2 * m + 1 + 1) * (2 * m + 1).choose m := h1.symm
    _ = 2 * ((m + 1) * (2 * m + 1).choose (m + 1)) := by rw [h3]; ring
    _ = 2 * ((2 * m + 1) * (2 * m).choose m) := by rw [← h2]
    _ = 2 * (2 * m + 1) * (2 * m).choose m := by ring

end OMA.S_oeis_a386829_proof

theorem OMA.solution : type_of% @OMA.S_oeis_a386829.main := by
  intro n hn
  have h1 := OMA.S_oeis_a386829_proof.I_rec1 n (by omega)
  have h2 := OMA.S_oeis_a386829_proof.I_rec1 (n - 1) (by omega)
  have hI_rec2 : (8 * (n : ℚ) + 4) * OMA.S_oeis_a386829_proof.I n +
      (-31 * (n : ℚ) + 20) * OMA.S_oeis_a386829_proof.I (n - 1) -
      45 * ((n : ℚ) - 1) * OMA.S_oeis_a386829_proof.I (n - 2) = 0 := by
    have hsub1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hsub2 : n - 1 - 1 = n - 2 := by omega
    have hpow : (5 : ℚ) ^ n = 5 * (5 : ℚ) ^ (n - 1) := by
      have : n = (n - 1) + 1 := by omega
      conv_lhs => rw [this, pow_succ']
    rw [hsub1, hsub2] at h2
    linear_combination h1 - 5 * h2 + 7 * hpow
  have ha0 := OMA.S_oeis_a386829_proof.a_eq_mul_I n
  have ha1 := OMA.S_oeis_a386829_proof.a_eq_mul_I (n - 1)
  have ha2 := OMA.S_oeis_a386829_proof.a_eq_mul_I (n - 2)
  have hsub1 : ((n - 1 : ℕ) : ℚ) = (n : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hsub2 : ((n - 2 : ℕ) : ℚ) = (n : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hsub1] at ha1
  rw [hsub2] at ha2
  have hc1 : (n : ℚ) * ((2 * n).choose n : ℚ) =
      2 * (2 * (n : ℚ) - 1) * ((2 * (n - 1)).choose (n - 1) : ℚ) := by
    have hm := OMA.S_oeis_a386829_proof.central_binom_succ (n - 1)
    have hmeq : n - 1 + 1 = n := by omega
    rw [hmeq] at hm
    have hcast := congrArg (Nat.cast (R := ℚ)) hm
    push_cast at hcast
    rw [hsub1] at hcast
    linear_combination hcast
  have hc2 : ((n : ℚ) - 1) * ((2 * (n - 1)).choose (n - 1) : ℚ) =
      2 * (2 * (n : ℚ) - 3) * ((2 * (n - 2)).choose (n - 2) : ℚ) := by
    have hm := OMA.S_oeis_a386829_proof.central_binom_succ (n - 2)
    have hmeq : n - 2 + 1 = n - 1 := by omega
    rw [hmeq] at hm
    have hcast := congrArg (Nat.cast (R := ℚ)) hm
    push_cast at hcast
    rw [hsub1, hsub2] at hcast
    linear_combination hcast
  have hgoal_q : 2 * (n : ℚ) * (OMA.S_oeis_a386829.a n : ℚ) +
      (-31 * (n : ℚ) + 20) * (OMA.S_oeis_a386829.a (n - 1) : ℚ) +
      90 * (-2 * (n : ℚ) + 1) * (OMA.S_oeis_a386829.a (n - 2) : ℚ) = 0 := by
    have hmul : (2 * (n : ℚ) - 1) * ((2 * (n - 1)).choose (n - 1) : ℚ) *
        ((8 * (n : ℚ) + 4) * OMA.S_oeis_a386829_proof.I n +
          (-31 * (n : ℚ) + 20) * OMA.S_oeis_a386829_proof.I (n - 1) -
          45 * ((n : ℚ) - 1) * OMA.S_oeis_a386829_proof.I (n - 2)) = 0 := by
      rw [hI_rec2, mul_zero]
    have hterm1 : (2 * (n : ℚ) - 1) * ((2 * (n - 1)).choose (n - 1) : ℚ) *
        ((8 * (n : ℚ) + 4) * OMA.S_oeis_a386829_proof.I n) =
        2 * (n : ℚ) * (OMA.S_oeis_a386829.a n : ℚ) := by
      rw [ha0]
      linear_combination -2 * (2 * (n : ℚ) + 1) * OMA.S_oeis_a386829_proof.I n * hc1
    have hterm2 : (2 * (n : ℚ) - 1) * ((2 * (n - 1)).choose (n - 1) : ℚ) *
        ((-31 * (n : ℚ) + 20) * OMA.S_oeis_a386829_proof.I (n - 1)) =
        (-31 * (n : ℚ) + 20) * (OMA.S_oeis_a386829.a (n - 1) : ℚ) := by
      rw [ha1]
      ring
    have hterm3 : (2 * (n : ℚ) - 1) * ((2 * (n - 1)).choose (n - 1) : ℚ) *
        (45 * ((n : ℚ) - 1) * OMA.S_oeis_a386829_proof.I (n - 2)) =
        -(90 * (-2 * (n : ℚ) + 1) * (OMA.S_oeis_a386829.a (n - 2) : ℚ)) := by
      rw [ha2]
      linear_combination 45 * (2 * (n : ℚ) - 1) * OMA.S_oeis_a386829_proof.I (n - 2) * hc2
    linear_combination hmul - hterm1 - hterm2 + hterm3
  exact_mod_cast hgoal_q
