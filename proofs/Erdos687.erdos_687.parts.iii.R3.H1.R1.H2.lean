import OMAReductions.R_Erdos687_erdos_687_parts_iii_R3_H1_R1

/-!
# Numeric absorption for reduction R3.H1.R1 of Erdős 687 (iii)

Once `n ≥ C ^ 24`, the bound `d ^ 8 ≤ C ^ 8 * n ^ 5` forces `d ^ 3 ≤ n ^ 2`:
otherwise `(d ^ 3) ^ 8 = (d ^ 8) ^ 3 ≤ C ^ 24 * n ^ 15 ≤ n ^ 16 = (n ^ 2) ^ 8 < (d ^ 3) ^ 8`.
-/

theorem OMA.solution : OMA.R_Erdos687_erdos_687_parts_iii_R3_H1_R1.H2 := by
  intro C
  filter_upwards [Filter.eventually_ge_atTop (C ^ 24)] with n hn d hd
  by_contra h
  have hlt : n ^ 2 < d ^ 3 := Nat.lt_of_not_le h
  have h1 : (n ^ 2) ^ 8 < (d ^ 3) ^ 8 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h2 : (d ^ 3) ^ 8 ≤ (n ^ 2) ^ 8 :=
    calc (d ^ 3) ^ 8 = (d ^ 8) ^ 3 := by ring
      _ ≤ (C ^ 8 * n ^ 5) ^ 3 := Nat.pow_le_pow_left hd 3
      _ = C ^ 24 * n ^ 15 := by ring
      _ ≤ n * n ^ 15 := Nat.mul_le_mul_right _ hn
      _ = (n ^ 2) ^ 8 := by ring
  exact absurd h1 (not_lt.mpr h2)
