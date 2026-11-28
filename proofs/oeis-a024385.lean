import OMAStatements.S_oeis_a024385
import Mathlib

namespace OMA.P024385

open OMA.S_oeis_a024385

lemma closed (N : ℕ) :
    6 * (stats N).1 = 12 * (N : ℤ) ^ 2 - 6 * (N : ℤ) ∧
    6 * (stats N).2 = 12 * (N : ℤ) ^ 4 - 28 * (N : ℤ) ^ 3 + 15 * (N : ℤ) ^ 2 + (N : ℤ) := by
  induction N with
  | zero => simp [stats]
  | succ N ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : stats (N + 1) = ((stats N).1 + (4 * (N : ℤ) + 1),
        (stats N).2 + (4 * (N : ℤ) + 1) * (stats N).1) := rfl
    rw [e]
    refine ⟨?_, ?_⟩
    · push_cast
      linear_combination h1 + 6 * (4 * (N : ℤ) + 1)
    · push_cast
      linear_combination h2 + (4 * (N : ℤ) + 1) * h1

lemma val1 (q : ℕ) : a (6 * q + 1) = 36 * (q : ℤ) ^ 2 + 13 * (q : ℤ) := by
  obtain ⟨h1, hj⟩ := closed (6 * q + 1 + 1)
  unfold a
  rw [if_neg (by omega)]
  generalize (stats (6 * q + 1 + 1)).1 = A at h1 ⊢
  generalize (stats (6 * q + 1 + 1)).2 = B at hj ⊢
  push_cast at h1 hj
  have hA : 6 * (A : ℤ) = 432 * (q : ℤ) ^ 2 + 252 * (q : ℤ) + 36 := by linear_combination h1
  have hP : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 252 * (q : ℤ) + 36 := by positivity
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 6 * ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 13 * (q : ℤ))) = 288 * (q : ℤ) ^ 2 + 186 * (q : ℤ) + 30 := by
    linear_combination hj - (36 * (q : ℤ) ^ 2 + 13 * (q : ℤ)) * h1
  have hV : 6 * ((A : ℤ) - ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 13 * (q : ℤ)))) = 144 * (q : ℤ) ^ 2 + 66 * (q : ℤ) + 6 := by
    linear_combination (1 + (36 * (q : ℤ) ^ 2 + 13 * (q : ℤ))) * h1 - hj
  have hW0 : (0 : ℤ) ≤ 288 * (q : ℤ) ^ 2 + 186 * (q : ℤ) + 30 := by positivity
  have hV0 : (0 : ℤ) < 144 * (q : ℤ) ^ 2 + 66 * (q : ℤ) + 6 := by positivity
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 13 * (q : ℤ))) (q := 36 * (q : ℤ) ^ 2 + 13 * (q : ℤ)) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma val2 (q : ℕ) : a (6 * q + 2) = 36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3 := by
  obtain ⟨h1, hj⟩ := closed (6 * q + 2 + 1)
  unfold a
  rw [if_neg (by omega)]
  generalize (stats (6 * q + 2 + 1)).1 = A at h1 ⊢
  generalize (stats (6 * q + 2 + 1)).2 = B at hj ⊢
  push_cast at h1 hj
  have hA : 6 * (A : ℤ) = 432 * (q : ℤ) ^ 2 + 396 * (q : ℤ) + 90 := by linear_combination h1
  have hP : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 396 * (q : ℤ) + 90 := by positivity
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 6 * ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3)) = 360 * (q : ℤ) ^ 2 + 348 * (q : ℤ) + 84 := by
    linear_combination hj - (36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3) * h1
  have hV : 6 * ((A : ℤ) - ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3))) = 72 * (q : ℤ) ^ 2 + 48 * (q : ℤ) + 6 := by
    linear_combination (1 + (36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3)) * h1 - hj
  have hW0 : (0 : ℤ) ≤ 360 * (q : ℤ) ^ 2 + 348 * (q : ℤ) + 84 := by positivity
  have hV0 : (0 : ℤ) < 72 * (q : ℤ) ^ 2 + 48 * (q : ℤ) + 6 := by positivity
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3)) (q := 36 * (q : ℤ) ^ 2 + 25 * (q : ℤ) + 3) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma val3 (q : ℕ) : a (6 * q + 3) = 36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9 := by
  obtain ⟨h1, hj⟩ := closed (6 * q + 3 + 1)
  unfold a
  rw [if_neg (by omega)]
  generalize (stats (6 * q + 3 + 1)).1 = A at h1 ⊢
  generalize (stats (6 * q + 3 + 1)).2 = B at hj ⊢
  push_cast at h1 hj
  have hA : 6 * (A : ℤ) = 432 * (q : ℤ) ^ 2 + 540 * (q : ℤ) + 168 := by linear_combination h1
  have hP : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 540 * (q : ℤ) + 168 := by positivity
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 6 * ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9)) = 18 * (q : ℤ) + 12 := by
    linear_combination hj - (36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9) * h1
  have hV : 6 * ((A : ℤ) - ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9))) = 432 * (q : ℤ) ^ 2 + 522 * (q : ℤ) + 156 := by
    linear_combination (1 + (36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9)) * h1 - hj
  have hW0 : (0 : ℤ) ≤ 18 * (q : ℤ) + 12 := by positivity
  have hV0 : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 522 * (q : ℤ) + 156 := by positivity
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9)) (q := 36 * (q : ℤ) ^ 2 + 37 * (q : ℤ) + 9) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma val4 (q : ℕ) : a (6 * q + 4) = 36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16 := by
  obtain ⟨h1, hj⟩ := closed (6 * q + 4 + 1)
  unfold a
  rw [if_neg (by omega)]
  generalize (stats (6 * q + 4 + 1)).1 = A at h1 ⊢
  generalize (stats (6 * q + 4 + 1)).2 = B at hj ⊢
  push_cast at h1 hj
  have hA : 6 * (A : ℤ) = 432 * (q : ℤ) ^ 2 + 684 * (q : ℤ) + 270 := by linear_combination h1
  have hP : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 684 * (q : ℤ) + 270 := by positivity
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 6 * ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16)) = 72 * (q : ℤ) ^ 2 + 132 * (q : ℤ) + 60 := by
    linear_combination hj - (36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16) * h1
  have hV : 6 * ((A : ℤ) - ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16))) = 360 * (q : ℤ) ^ 2 + 552 * (q : ℤ) + 210 := by
    linear_combination (1 + (36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16)) * h1 - hj
  have hW0 : (0 : ℤ) ≤ 72 * (q : ℤ) ^ 2 + 132 * (q : ℤ) + 60 := by positivity
  have hV0 : (0 : ℤ) < 360 * (q : ℤ) ^ 2 + 552 * (q : ℤ) + 210 := by positivity
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16)) (q := 36 * (q : ℤ) ^ 2 + 49 * (q : ℤ) + 16) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma val5 (q : ℕ) : a (6 * q + 5) = 36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25 := by
  obtain ⟨h1, hj⟩ := closed (6 * q + 5 + 1)
  unfold a
  rw [if_neg (by omega)]
  generalize (stats (6 * q + 5 + 1)).1 = A at h1 ⊢
  generalize (stats (6 * q + 5 + 1)).2 = B at hj ⊢
  push_cast at h1 hj
  have hA : 6 * (A : ℤ) = 432 * (q : ℤ) ^ 2 + 828 * (q : ℤ) + 396 := by linear_combination h1
  have hP : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 828 * (q : ℤ) + 396 := by positivity
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 6 * ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25)) = 144 * (q : ℤ) ^ 2 + 294 * (q : ℤ) + 150 := by
    linear_combination hj - (36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25) * h1
  have hV : 6 * ((A : ℤ) - ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25))) = 288 * (q : ℤ) ^ 2 + 534 * (q : ℤ) + 246 := by
    linear_combination (1 + (36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25)) * h1 - hj
  have hW0 : (0 : ℤ) ≤ 144 * (q : ℤ) ^ 2 + 294 * (q : ℤ) + 150 := by positivity
  have hV0 : (0 : ℤ) < 288 * (q : ℤ) ^ 2 + 534 * (q : ℤ) + 246 := by positivity
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25)) (q := 36 * (q : ℤ) ^ 2 + 61 * (q : ℤ) + 25) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma val6 (q : ℕ) : a (6 * q + 6) = 36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36 := by
  obtain ⟨h1, hj⟩ := closed (6 * q + 6 + 1)
  unfold a
  rw [if_neg (by omega)]
  generalize (stats (6 * q + 6 + 1)).1 = A at h1 ⊢
  generalize (stats (6 * q + 6 + 1)).2 = B at hj ⊢
  push_cast at h1 hj
  have hA : 6 * (A : ℤ) = 432 * (q : ℤ) ^ 2 + 972 * (q : ℤ) + 546 := by linear_combination h1
  have hP : (0 : ℤ) < 432 * (q : ℤ) ^ 2 + 972 * (q : ℤ) + 546 := by positivity
  have hpos : 0 < (A : ℤ) := by linarith
  have hW : 6 * ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36)) = 216 * (q : ℤ) ^ 2 + 504 * (q : ℤ) + 294 := by
    linear_combination hj - (36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36) * h1
  have hV : 6 * ((A : ℤ) - ((B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36))) = 216 * (q : ℤ) ^ 2 + 468 * (q : ℤ) + 252 := by
    linear_combination (1 + (36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36)) * h1 - hj
  have hW0 : (0 : ℤ) ≤ 216 * (q : ℤ) ^ 2 + 504 * (q : ℤ) + 294 := by positivity
  have hV0 : (0 : ℤ) < 216 * (q : ℤ) ^ 2 + 468 * (q : ℤ) + 252 := by positivity
  exact ((Int.ediv_emod_unique (r := (B : ℤ) - A * (36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36)) (q := 36 * (q : ℤ) ^ 2 + 73 * (q : ℤ) + 36) hpos).2
    ⟨by ring, by linarith, by linarith⟩).1

lemma va1 : a 1 = 0 := by
  have h := val1 0
  norm_num at h
  exact_mod_cast h

lemma va2 : a 2 = 3 := by
  have h := val2 0
  norm_num at h
  exact_mod_cast h

lemma va3 : a 3 = 9 := by
  have h := val3 0
  norm_num at h
  exact_mod_cast h

lemma va4 : a 4 = 16 := by
  have h := val4 0
  norm_num at h
  exact_mod_cast h

lemma va5 : a 5 = 25 := by
  have h := val5 0
  norm_num at h
  exact_mod_cast h

lemma va6 : a 6 = 36 := by
  have h := val6 0
  norm_num at h
  exact_mod_cast h

lemma va7 : a 7 = 49 := by
  have h := val1 1
  norm_num at h
  exact_mod_cast h

lemma va8 : a 8 = 64 := by
  have h := val2 1
  norm_num at h
  exact_mod_cast h

lemma rec (n : ℕ) (hn : 9 ≤ n) : (a n : ℤ) = 2 * (a (n - 1) : ℤ) - (a (n - 2) : ℤ) + (a (n - 6) : ℤ) - 2 * (a (n - 7) : ℤ) + (a (n - 8) : ℤ) := by
  obtain ⟨q, s, hs, hq⟩ : ∃ q s, s < 6 ∧ n = 6 * q + s + 9 :=
    ⟨(n - 9) / 6, (n - 9) % 6, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases s
  · have e0 : n = 6 * (q + 1) + 3 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 2 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 1 := by omega
    have e6 : n - 6 = 6 * q + 3 := by omega
    have e7 : n - 7 = 6 * q + 2 := by omega
    have e8 : n - 8 = 6 * q + 1 := by omega
    rw [e1, e2, e6, e7, e8, e0]
    rw [val3 (q + 1), val2 (q + 1), val1 (q + 1), val3 q, val2 q, val1 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 4 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 3 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 2 := by omega
    have e6 : n - 6 = 6 * q + 4 := by omega
    have e7 : n - 7 = 6 * q + 3 := by omega
    have e8 : n - 8 = 6 * q + 2 := by omega
    rw [e1, e2, e6, e7, e8, e0]
    rw [val4 (q + 1), val3 (q + 1), val2 (q + 1), val4 q, val3 q, val2 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 5 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 4 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 3 := by omega
    have e6 : n - 6 = 6 * q + 5 := by omega
    have e7 : n - 7 = 6 * q + 4 := by omega
    have e8 : n - 8 = 6 * q + 3 := by omega
    rw [e1, e2, e6, e7, e8, e0]
    rw [val5 (q + 1), val4 (q + 1), val3 (q + 1), val5 q, val4 q, val3 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 1) + 6 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 5 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 4 := by omega
    have e6 : n - 6 = 6 * q + 6 := by omega
    have e7 : n - 7 = 6 * q + 5 := by omega
    have e8 : n - 8 = 6 * q + 4 := by omega
    rw [e1, e2, e6, e7, e8, e0]
    rw [val6 (q + 1), val5 (q + 1), val4 (q + 1), val6 q, val5 q, val4 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 2) + 1 := by omega
    have e1 : n - 1 = 6 * (q + 1) + 6 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 5 := by omega
    have e6 : n - 6 = 6 * (q + 1) + 1 := by omega
    have e7 : n - 7 = 6 * q + 6 := by omega
    have e8 : n - 8 = 6 * q + 5 := by omega
    rw [e1, e2, e6, e7, e8, e0]
    rw [val1 (q + 2), val6 (q + 1), val5 (q + 1), val1 (q + 1), val6 q, val5 q]
    push_cast
    ring
  · have e0 : n = 6 * (q + 2) + 2 := by omega
    have e1 : n - 1 = 6 * (q + 2) + 1 := by omega
    have e2 : n - 2 = 6 * (q + 1) + 6 := by omega
    have e6 : n - 6 = 6 * (q + 1) + 2 := by omega
    have e7 : n - 7 = 6 * (q + 1) + 1 := by omega
    have e8 : n - 8 = 6 * q + 6 := by omega
    rw [e1, e2, e6, e7, e8, e0]
    rw [val2 (q + 2), val1 (q + 2), val6 (q + 1), val2 (q + 1), val1 (q + 1), val6 q]
    push_cast
    ring

lemma va0 : a 0 = 0 := by
  unfold a
  simp

end OMA.P024385

theorem OMA.solution : type_of% @OMA.S_oeis_a024385.main := by
  refine ⟨fun n hn => OMA.P024385.rec n hn, ?_⟩
  have key : (PowerSeries.C (1 : ℤ) * PowerSeries.mk OMA.S_oeis_a024385.a)
      - (PowerSeries.C (2 : ℤ) * (PowerSeries.mk OMA.S_oeis_a024385.a * PowerSeries.X ^ 1))
      + (PowerSeries.C (1 : ℤ) * (PowerSeries.mk OMA.S_oeis_a024385.a * PowerSeries.X ^ 2))
      - (PowerSeries.C (1 : ℤ) * (PowerSeries.mk OMA.S_oeis_a024385.a * PowerSeries.X ^ 6))
      + (PowerSeries.C (2 : ℤ) * (PowerSeries.mk OMA.S_oeis_a024385.a * PowerSeries.X ^ 7))
      - (PowerSeries.C (1 : ℤ) * (PowerSeries.mk OMA.S_oeis_a024385.a * PowerSeries.X ^ 8))
      - ((PowerSeries.X ^ 2 * PowerSeries.C (3 : ℤ))
      + (PowerSeries.X ^ 3 * PowerSeries.C (3 : ℤ))
      + (PowerSeries.X ^ 4 * PowerSeries.C (1 : ℤ))
      + (PowerSeries.X ^ 5 * PowerSeries.C (2 : ℤ))
      + (PowerSeries.X ^ 6 * PowerSeries.C (2 : ℤ))
      + (PowerSeries.X ^ 7 * PowerSeries.C (2 : ℤ))
      - (PowerSeries.X ^ 8 * PowerSeries.C (1 : ℤ))) = 0 := by
    ext n
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
      PowerSeries.coeff_mk, PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow, map_zero]
    rcases Nat.lt_or_ge n 9 with hlt | hge
    · interval_cases n <;> norm_num [OMA.P024385.va0, OMA.P024385.va1, OMA.P024385.va2, OMA.P024385.va3, OMA.P024385.va4, OMA.P024385.va5, OMA.P024385.va6, OMA.P024385.va7, OMA.P024385.va8]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
      have h := OMA.P024385.rec (m + 9) (by omega)
      have z2 : ¬ (m + 9 = 2) := by omega
      have z3 : ¬ (m + 9 = 3) := by omega
      have z4 : ¬ (m + 9 = 4) := by omega
      have z5 : ¬ (m + 9 = 5) := by omega
      have z6 : ¬ (m + 9 = 6) := by omega
      have z7 : ¬ (m + 9 = 7) := by omega
      have z8 : ¬ (m + 9 = 8) := by omega
      have w1 : 1 ≤ m + 9 := by omega
      have w2 : 2 ≤ m + 9 := by omega
      have w6 : 6 ≤ m + 9 := by omega
      have w7 : 7 ≤ m + 9 := by omega
      have w8 : 8 ≤ m + 9 := by omega
      simp only [z2, z3, z4, z5, z6, z7, z8, w1, w2, w6, w7, w8, if_true, if_false, zero_mul, mul_zero, add_zero, sub_zero]
      linear_combination h
  simp only [map_ofNat, map_one] at key
  linear_combination key
