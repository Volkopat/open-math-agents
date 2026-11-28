import OMAStatements.S_oeis_a028355
import Mathlib
open OMA.S_oeis_a028355 PowerSeries

theorem Pa028355.d_add (i k : ℕ) : d (i + 6 * k) = d i := by
  unfold d
  rw [Nat.add_mul_mod_self_left]

theorem Pa028355.d_pos (i : ℕ) : 1 ≤ d i := by
  unfold d
  have h : i % 6 < 6 := Nat.mod_lt _ (by norm_num)
  generalize i % 6 = r at h
  interval_cases r <;> simp

theorem Pa028355.six (m : ℕ) : d m + d (m + 1) + d (m + 2) + d (m + 3) + d (m + 4) + d (m + 5) = 15 := by
  unfold d
  have h : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  rw [Nat.add_mod m 1, Nat.add_mod m 2, Nat.add_mod m 3, Nat.add_mod m 4, Nat.add_mod m 5]
  generalize m % 6 = r at h
  interval_cases r <;> simp

theorem Pa028355.S_succ (m : ℕ) : S (m + 1) = S m + d m := by
  unfold S; rw [Finset.sum_range_succ]

theorem Pa028355.S_add6 (m : ℕ) : S (m + 6) = S m + 15 := by
  unfold S
  rw [Finset.sum_range_add]
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, add_zero]
  have := Pa028355.six m
  omega

theorem Pa028355.S_mul (m k : ℕ) : S (m + 6 * k) = S m + 15 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show m + 6 * (k + 1) = m + 6 * k + 6 by ring, Pa028355.S_add6, ih]; ring

theorem Pa028355.S_strict : StrictMono S := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [Pa028355.S_succ]
  have := Pa028355.d_pos m
  omega

theorem Pa028355.S_ge (m : ℕ) : m ≤ S m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Pa028355.S_succ]; have := Pa028355.d_pos m; omega

theorem Pa028355.sInf_spec (t : ℕ) :
    t ≤ S (sInf {m : ℕ | t ≤ S m}) ∧ ∀ m, m < sInf {m : ℕ | t ≤ S m} → S m < t := by
  have hne : ({m : ℕ | t ≤ S m}).Nonempty := ⟨t, Pa028355.S_ge t⟩
  refine ⟨Nat.sInf_mem hne, fun m hm => ?_⟩
  by_contra hc
  push Not at hc
  exact absurd (Nat.sInf_le (show m ∈ {m : ℕ | t ≤ S m} from hc)) (not_le.mpr hm)

theorem Pa028355.sInf_eq (t q : ℕ) (h1 : t ≤ S q) (h2 : ∀ m, m < q → S m < t) :
    sInf {m : ℕ | t ≤ S m} = q := by
  apply le_antisymm (Nat.sInf_le (show q ∈ {m : ℕ | t ≤ S m} from h1))
  by_contra hc
  push Not at hc
  have := h2 _ hc
  have := (Pa028355.sInf_spec t).1
  omega

theorem Pa028355.sInf_shift (t k : ℕ) :
    sInf {m : ℕ | t + 15 * k ≤ S m} = sInf {m : ℕ | t ≤ S m} + 6 * k := by
  obtain ⟨h1, h2⟩ := Pa028355.sInf_spec t
  set p := sInf {m : ℕ | t ≤ S m}
  apply Pa028355.sInf_eq
  · rw [Pa028355.S_mul]; omega
  · intro m hm
    rcases Nat.lt_or_ge m (6 * k) with h | h
    · have := Pa028355.S_strict h
      have h0 := Pa028355.S_mul 0 k
      simp only [zero_add] at h0
      have : S 0 = 0 := by simp [S]
      omega
    · obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 6 * k := ⟨m - 6 * k, by omega⟩
      rw [Pa028355.S_mul]
      have := h2 m0 (by omega)
      omega

theorem Pa028355.T_add (n : ℕ) : (n + 15) * (n + 15 + 1) / 2 = n * (n + 1) / 2 + 15 * (n + 8) := by
  rw [show (n + 15) * (n + 15 + 1) = n * (n + 1) + 2 * (15 * (n + 8)) by ring,
    Nat.add_mul_div_left _ _ (by norm_num)]

theorem Pa028355.P_add (n : ℕ) : P (n + 15) = P n + 6 * (n + 8) := by
  unfold P
  rw [Pa028355.T_add, Pa028355.sInf_shift]

theorem Pa028355.P_mono (n : ℕ) : P n ≤ P (n + 1) := by
  unfold P
  apply Nat.sInf_le
  show n * (n + 1) / 2 ≤ S (sInf {m : ℕ | (n + 1) * (n + 1 + 1) / 2 ≤ S m})
  have := (Pa028355.sInf_spec ((n + 1) * (n + 1 + 1) / 2)).1
  have h : n * (n + 1) / 2 ≤ (n + 1) * (n + 1 + 1) / 2 :=
    Nat.div_le_div_right (by nlinarith)
  omega

def Pa028355.G (s e : ℕ) : ℕ := ∑ i ∈ Finset.Ico s e, d i * 10 ^ (e - 1 - i)

theorem Pa028355.a_eq (n : ℕ) : a n = Pa028355.G (P (n - 1)) (P n) := rfl

theorem Pa028355.G_shift (s e k : ℕ) : Pa028355.G (s + 6 * k) (e + 6 * k) = Pa028355.G s e := by
  unfold Pa028355.G
  rw [← Finset.sum_Ico_add']
  apply Finset.sum_congr rfl
  intro i _
  rw [Pa028355.d_add]
  congr 2
  omega

theorem Pa028355.G_concat (s e : ℕ) (h : s ≤ e) :
    Pa028355.G s (e + 6) = Pa028355.G s e * 10 ^ 6 + Pa028355.G e (e + 6) := by
  unfold Pa028355.G
  rw [← Finset.sum_Ico_consecutive _ h (by omega : e ≤ e + 6), Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  rw [mul_assoc, ← pow_add]
  congr 2
  omega

theorem Pa028355.step (m : ℕ) (hm : 1 ≤ m) :
    a (m + 15) = a m * 10 ^ 6 + Pa028355.G (P m) (P m + 6) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Pa028355.a_eq, Pa028355.a_eq, show j + 1 + 15 - 1 = j + 15 by omega,
    show j + 1 - 1 = j by omega, Pa028355.P_add, Pa028355.P_add,
    show P (j + 1) + 6 * (j + 1 + 8) = (P (j + 1) + 6) + 6 * (j + 8) by ring,
    Pa028355.G_shift, Pa028355.G_concat _ _ (Pa028355.P_mono j)]

theorem Pa028355.rec (n : ℕ) (hn : 30 < n) :
    (a n : ℤ) = 1000001 * a (n - 15) - 1000000 * a (n - 30) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 30 := ⟨n - 30, by omega⟩
  have h1 := Pa028355.step m (by omega)
  have h2 := Pa028355.step (m + 15) (by omega)
  rw [Pa028355.P_add, show P m + 6 * (m + 8) + 6 = (P m + 6) + 6 * (m + 8) by ring,
    Pa028355.G_shift, show m + 15 + 15 = m + 30 by ring] at h2
  rw [show m + 30 - 15 = m + 15 by omega, show m + 30 - 30 = m by omega]
  zify at h1 h2
  linear_combination h2 - h1

theorem Pa028355.Pval (n v : ℕ) (h1 : n * (n + 1) / 2 ≤ S v)
    (h2 : v = 0 ∨ S (v - 1) < n * (n + 1) / 2) : P n = v := by
  unfold P
  apply Pa028355.sInf_eq _ _ h1
  intro m hm
  rcases h2 with h | h
  · omega
  · have := Pa028355.S_strict.monotone (show m ≤ v - 1 by omega)
    omega

theorem Pa028355.cm (f : ℕ → ℤ) (c : ℤ) (k n : ℕ) :
    coeff n (C c * (PowerSeries.mk f * X ^ k)) = c * (if k ≤ n then f (n - k) else 0) := by
  rw [coeff_C_mul, coeff_mul_X_pow', coeff_mk]

theorem Pa028355.vals : a 1 = 1 ∧ a 2 = 2 ∧ a 3 = 3 ∧ a 4 = 4 ∧ a 5 = 32 ∧ a 6 = 123 ∧ a 7 = 43 ∧ a 8 = 2123 ∧ a 9 = 432 ∧ a 10 = 1234 ∧ a 11 = 32123 ∧ a 12 = 43212 ∧ a 13 = 34321 ∧ a 14 = 23432 ∧ a 15 = 123432 ∧ a 16 = 1234321 ∧ a 17 = 2343212 ∧ a 18 = 3432123 ∧ a 19 = 4321234 ∧ a 20 = 32123432 ∧ a 21 = 123432123 ∧ a 22 = 43212343 ∧ a 23 = 2123432123 ∧ a 24 = 432123432 ∧ a 25 = 1234321234 ∧ a 26 = 32123432123 ∧ a 27 = 43212343212 ∧ a 28 = 34321234321 ∧ a 29 = 23432123432 ∧ a 30 = 123432123432 := by
  have p0 : P 0 = 0 := Pa028355.Pval 0 0 (by decide +kernel) (by decide +kernel)
  have p1 : P 1 = 1 := Pa028355.Pval 1 1 (by decide +kernel) (by decide +kernel)
  have p2 : P 2 = 2 := Pa028355.Pval 2 2 (by decide +kernel) (by decide +kernel)
  have p3 : P 3 = 3 := Pa028355.Pval 3 3 (by decide +kernel) (by decide +kernel)
  have p4 : P 4 = 4 := Pa028355.Pval 4 4 (by decide +kernel) (by decide +kernel)
  have p5 : P 5 = 6 := Pa028355.Pval 5 6 (by decide +kernel) (by decide +kernel)
  have p6 : P 6 = 9 := Pa028355.Pval 6 9 (by decide +kernel) (by decide +kernel)
  have p7 : P 7 = 11 := Pa028355.Pval 7 11 (by decide +kernel) (by decide +kernel)
  have p8 : P 8 = 15 := Pa028355.Pval 8 15 (by decide +kernel) (by decide +kernel)
  have p9 : P 9 = 18 := Pa028355.Pval 9 18 (by decide +kernel) (by decide +kernel)
  have p10 : P 10 = 22 := Pa028355.Pval 10 22 (by decide +kernel) (by decide +kernel)
  have p11 : P 11 = 27 := Pa028355.Pval 11 27 (by decide +kernel) (by decide +kernel)
  have p12 : P 12 = 32 := Pa028355.Pval 12 32 (by decide +kernel) (by decide +kernel)
  have p13 : P 13 = 37 := Pa028355.Pval 13 37 (by decide +kernel) (by decide +kernel)
  have p14 : P 14 = 42 := Pa028355.Pval 14 42 (by decide +kernel) (by decide +kernel)
  have p15 : P 15 = 48 := Pa028355.Pval 15 48 (by decide +kernel) (by decide +kernel)
  have p16 : P 16 = 55 := Pa028355.Pval 16 55 (by decide +kernel) (by decide +kernel)
  have p17 : P 17 = 62 := Pa028355.Pval 17 62 (by decide +kernel) (by decide +kernel)
  have p18 : P 18 = 69 := Pa028355.Pval 18 69 (by decide +kernel) (by decide +kernel)
  have p19 : P 19 = 76 := Pa028355.Pval 19 76 (by decide +kernel) (by decide +kernel)
  have p20 : P 20 = 84 := Pa028355.Pval 20 84 (by decide +kernel) (by decide +kernel)
  have p21 : P 21 = 93 := Pa028355.Pval 21 93 (by decide +kernel) (by decide +kernel)
  have p22 : P 22 = 101 := Pa028355.Pval 22 101 (by decide +kernel) (by decide +kernel)
  have p23 : P 23 = 111 := Pa028355.Pval 23 111 (by decide +kernel) (by decide +kernel)
  have p24 : P 24 = 120 := Pa028355.Pval 24 120 (by decide +kernel) (by decide +kernel)
  have p25 : P 25 = 130 := Pa028355.Pval 25 130 (by decide +kernel) (by decide +kernel)
  have p26 : P 26 = 141 := Pa028355.Pval 26 141 (by decide +kernel) (by decide +kernel)
  have p27 : P 27 = 152 := Pa028355.Pval 27 152 (by decide +kernel) (by decide +kernel)
  have p28 : P 28 = 163 := Pa028355.Pval 28 163 (by decide +kernel) (by decide +kernel)
  have p29 : P 29 = 174 := Pa028355.Pval 29 174 (by decide +kernel) (by decide +kernel)
  have p30 : P 30 = 186 := Pa028355.Pval 30 186 (by decide +kernel) (by decide +kernel)
  have v1 : a 1 = 1 := by
    rw [show a 1 = Pa028355.G (P 0) (P 1) from rfl, p0, p1]
    decide +kernel
  have v2 : a 2 = 2 := by
    rw [show a 2 = Pa028355.G (P 1) (P 2) from rfl, p1, p2]
    decide +kernel
  have v3 : a 3 = 3 := by
    rw [show a 3 = Pa028355.G (P 2) (P 3) from rfl, p2, p3]
    decide +kernel
  have v4 : a 4 = 4 := by
    rw [show a 4 = Pa028355.G (P 3) (P 4) from rfl, p3, p4]
    decide +kernel
  have v5 : a 5 = 32 := by
    rw [show a 5 = Pa028355.G (P 4) (P 5) from rfl, p4, p5]
    decide +kernel
  have v6 : a 6 = 123 := by
    rw [show a 6 = Pa028355.G (P 5) (P 6) from rfl, p5, p6]
    decide +kernel
  have v7 : a 7 = 43 := by
    rw [show a 7 = Pa028355.G (P 6) (P 7) from rfl, p6, p7]
    decide +kernel
  have v8 : a 8 = 2123 := by
    rw [show a 8 = Pa028355.G (P 7) (P 8) from rfl, p7, p8]
    decide +kernel
  have v9 : a 9 = 432 := by
    rw [show a 9 = Pa028355.G (P 8) (P 9) from rfl, p8, p9]
    decide +kernel
  have v10 : a 10 = 1234 := by
    rw [show a 10 = Pa028355.G (P 9) (P 10) from rfl, p9, p10]
    decide +kernel
  have v11 : a 11 = 32123 := by
    rw [show a 11 = Pa028355.G (P 10) (P 11) from rfl, p10, p11]
    decide +kernel
  have v12 : a 12 = 43212 := by
    rw [show a 12 = Pa028355.G (P 11) (P 12) from rfl, p11, p12]
    decide +kernel
  have v13 : a 13 = 34321 := by
    rw [show a 13 = Pa028355.G (P 12) (P 13) from rfl, p12, p13]
    decide +kernel
  have v14 : a 14 = 23432 := by
    rw [show a 14 = Pa028355.G (P 13) (P 14) from rfl, p13, p14]
    decide +kernel
  have v15 : a 15 = 123432 := by
    rw [show a 15 = Pa028355.G (P 14) (P 15) from rfl, p14, p15]
    decide +kernel
  have v16 : a 16 = 1234321 := by
    rw [show a 16 = Pa028355.G (P 15) (P 16) from rfl, p15, p16]
    decide +kernel
  have v17 : a 17 = 2343212 := by
    rw [show a 17 = Pa028355.G (P 16) (P 17) from rfl, p16, p17]
    decide +kernel
  have v18 : a 18 = 3432123 := by
    rw [show a 18 = Pa028355.G (P 17) (P 18) from rfl, p17, p18]
    decide +kernel
  have v19 : a 19 = 4321234 := by
    rw [show a 19 = Pa028355.G (P 18) (P 19) from rfl, p18, p19]
    decide +kernel
  have v20 : a 20 = 32123432 := by
    rw [show a 20 = Pa028355.G (P 19) (P 20) from rfl, p19, p20]
    decide +kernel
  have v21 : a 21 = 123432123 := by
    rw [show a 21 = Pa028355.G (P 20) (P 21) from rfl, p20, p21]
    decide +kernel
  have v22 : a 22 = 43212343 := by
    rw [show a 22 = Pa028355.G (P 21) (P 22) from rfl, p21, p22]
    decide +kernel
  have v23 : a 23 = 2123432123 := by
    rw [show a 23 = Pa028355.G (P 22) (P 23) from rfl, p22, p23]
    decide +kernel
  have v24 : a 24 = 432123432 := by
    rw [show a 24 = Pa028355.G (P 23) (P 24) from rfl, p23, p24]
    decide +kernel
  have v25 : a 25 = 1234321234 := by
    rw [show a 25 = Pa028355.G (P 24) (P 25) from rfl, p24, p25]
    decide +kernel
  have v26 : a 26 = 32123432123 := by
    rw [show a 26 = Pa028355.G (P 25) (P 26) from rfl, p25, p26]
    decide +kernel
  have v27 : a 27 = 43212343212 := by
    rw [show a 27 = Pa028355.G (P 26) (P 27) from rfl, p26, p27]
    decide +kernel
  have v28 : a 28 = 34321234321 := by
    rw [show a 28 = Pa028355.G (P 27) (P 28) from rfl, p27, p28]
    decide +kernel
  have v29 : a 29 = 23432123432 := by
    rw [show a 29 = Pa028355.G (P 28) (P 29) from rfl, p28, p29]
    decide +kernel
  have v30 : a 30 = 123432123432 := by
    rw [show a 30 = Pa028355.G (P 29) (P 30) from rfl, p29, p30]
    decide +kernel
  exact ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30⟩

theorem OMA.solution : type_of% @OMA.S_oeis_a028355.main := by
  refine ⟨Pa028355.rec, ?_⟩
  set A := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (a n : ℤ)) with hA
  have hL : A * (1000000 * X ^ 30 - 1000001 * X ^ 15 + 1) =
      C 1000000 * (A * X ^ 30) + C (-1000001) * (A * X ^ 15) + C 1 * (A * X ^ 0) := by
    simp only [map_neg, map_one, map_ofNat]
    ring
  have hR : (X : PowerSeries ℤ) * (100000*X^28 + 200000*X^27 + 300000*X^26 + 400000*X^25 + 320000*X^24 + 123000*X^23 + 430000*X^22 + 212300*X^21 + 432000*X^20 + 123400*X^19 + 321230*X^18 + 432120*X^17 + 343210*X^16 + 234320*X^15 + 123432*X^14 + 23432*X^13 + 34321*X^12 + 43212*X^11 + 32123*X^10 + 1234*X^9 + 432*X^8 + 2123*X^7 + 43*X^6 + 123*X^5 + 32*X^4 + 4*X^3 + 3*X^2 + 2*X + 1) = C (100000 : ℤ) * X ^ 29 + C (200000 : ℤ) * X ^ 28 + C (300000 : ℤ) * X ^ 27 + C (400000 : ℤ) * X ^ 26 + C (320000 : ℤ) * X ^ 25 + C (123000 : ℤ) * X ^ 24 + C (430000 : ℤ) * X ^ 23 + C (212300 : ℤ) * X ^ 22 + C (432000 : ℤ) * X ^ 21 + C (123400 : ℤ) * X ^ 20 + C (321230 : ℤ) * X ^ 19 + C (432120 : ℤ) * X ^ 18 + C (343210 : ℤ) * X ^ 17 + C (234320 : ℤ) * X ^ 16 + C (123432 : ℤ) * X ^ 15 + C (23432 : ℤ) * X ^ 14 + C (34321 : ℤ) * X ^ 13 + C (43212 : ℤ) * X ^ 12 + C (32123 : ℤ) * X ^ 11 + C (1234 : ℤ) * X ^ 10 + C (432 : ℤ) * X ^ 9 + C (2123 : ℤ) * X ^ 8 + C (43 : ℤ) * X ^ 7 + C (123 : ℤ) * X ^ 6 + C (32 : ℤ) * X ^ 5 + C (4 : ℤ) * X ^ 4 + C (3 : ℤ) * X ^ 3 + C (2 : ℤ) * X ^ 2 + C (1 : ℤ) * X ^ 1 := by
    simp only [map_one, map_ofNat]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, Pa028355.cm, hA, coeff_C_mul_X_pow]
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30⟩ := Pa028355.vals
  rcases Nat.lt_or_ge n 31 with hn | hn
  · interval_cases n <;> simp [v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 31 := ⟨n - 31, by omega⟩
    have hr := Pa028355.rec (m + 31) (by omega)
    simp only [show m + 31 - 15 = m + 16 by omega, show m + 31 - 30 = m + 1 by omega] at hr
    simp
    linear_combination hr
