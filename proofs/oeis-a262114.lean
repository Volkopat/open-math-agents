import OMAStatements.S_oeis_a262114
import Mathlib

/-!
# A262114: proof of Barker's recurrence and g.f.

For b = 5j + r the digits of 1/5 in base b are explicit affine functions of j (b^(k+1) = 5 Q + R and
Q = b D + d with d < b). The rows for b = 5j+2, ..., 5j+6 have lengths 4, 4, 2, 1, 1, so the
concatenation is made of blocks of 12 entries, block j having entries affine in j. Hence
a(12 j + t + 1) is affine in j for each t < 12, which gives a(n) = 2 a(n-12) - a(n-24) for n > 24,
and the g.f. follows from the recurrence and the first 25 terms.
-/

open OMA.S_oeis_a262114

namespace OMA.P_a262114

lemma dig {b k Q D d R : ℕ} (h1 : b ^ (k + 1) = 5 * Q + R) (hR : R < 5) (h2 : Q = b * D + d)
    (hd : d < b) : digit b k = d := by
  unfold digit
  rw [h1, show (5 * Q + R) / 5 = Q by omega, h2, Nat.add_comm, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hd]

lemma row2 (j : ℕ) : row (5 * j + 2) = [1 * j, 2 * j, 1 + 4 * j, 1 + 3 * j] := by
  have h5 : ¬ 5 ∣ 5 * j + 2 := by omega
  have hz : ((5 * j + 2 : ℕ) : ZMod 5) = 2 := by
    push_cast
    rw [show (5 : ZMod 5) = 0 from rfl]
    simp
  have ho : orderOf ((5 * j + 2 : ℕ) : ZMod 5) = 4 := by
    rw [hz, orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, by decide⟩
  unfold row
  rw [if_neg h5, ho, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [dig (k := 0) (Q := 1 * j) (D := 0) (d := 1 * j) (R := 2) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 1) (Q := 4 * j + 5 * j ^ 2) (D := 1 * j) (d := 2 * j) (R := 4) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 2) (Q := 1 + 12 * j + 30 * j ^ 2 + 25 * j ^ 3) (D := 4 * j + 5 * j ^ 2) (d := 1 + 4 * j) (R := 3) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 3) (Q := 3 + 32 * j + 120 * j ^ 2 + 200 * j ^ 3 + 125 * j ^ 4) (D := 1 + 12 * j + 30 * j ^ 2 + 25 * j ^ 3) (d := 1 + 3 * j) (R := 1) (by ring) (by norm_num) (by ring) (by omega)]

lemma row3 (j : ℕ) : row (5 * j + 3) = [1 * j, 1 + 3 * j, 2 + 4 * j, 1 + 2 * j] := by
  have h5 : ¬ 5 ∣ 5 * j + 3 := by omega
  have hz : ((5 * j + 3 : ℕ) : ZMod 5) = 3 := by
    push_cast
    rw [show (5 : ZMod 5) = 0 from rfl]
    simp
  have ho : orderOf ((5 * j + 3 : ℕ) : ZMod 5) = 4 := by
    rw [hz, orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, by decide⟩
  unfold row
  rw [if_neg h5, ho, show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [dig (k := 0) (Q := 1 * j) (D := 0) (d := 1 * j) (R := 3) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 1) (Q := 1 + 6 * j + 5 * j ^ 2) (D := 1 * j) (d := 1 + 3 * j) (R := 4) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 2) (Q := 5 + 27 * j + 45 * j ^ 2 + 25 * j ^ 3) (D := 1 + 6 * j + 5 * j ^ 2) (d := 2 + 4 * j) (R := 2) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 3) (Q := 16 + 108 * j + 270 * j ^ 2 + 300 * j ^ 3 + 125 * j ^ 4) (D := 5 + 27 * j + 45 * j ^ 2 + 25 * j ^ 3) (d := 1 + 2 * j) (R := 1) (by ring) (by norm_num) (by ring) (by omega)]

lemma row4 (j : ℕ) : row (5 * j + 4) = [1 * j, 3 + 4 * j] := by
  have h5 : ¬ 5 ∣ 5 * j + 4 := by omega
  have hz : ((5 * j + 4 : ℕ) : ZMod 5) = 4 := by
    push_cast
    rw [show (5 : ZMod 5) = 0 from rfl]
    simp
  have ho : orderOf ((5 * j + 4 : ℕ) : ZMod 5) = 2 := by
    rw [hz, orderOf_eq_iff (by norm_num)]
    exact ⟨by decide, by decide⟩
  unfold row
  rw [if_neg h5, ho, show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [dig (k := 0) (Q := 1 * j) (D := 0) (d := 1 * j) (R := 4) (by ring) (by norm_num) (by ring) (by omega)]
  rw [dig (k := 1) (Q := 3 + 8 * j + 5 * j ^ 2) (D := 1 * j) (d := 3 + 4 * j) (R := 1) (by ring) (by norm_num) (by ring) (by omega)]

lemma row5 (j : ℕ) : row (5 * j + 5) = [j + 1] := by
  have h5 : 5 ∣ 5 * j + 5 := ⟨j + 1, by ring⟩
  unfold row
  rw [if_pos h5, dig (k := 0) (Q := j + 1) (D := 0) (d := j + 1) (R := 0) (by ring) (by norm_num)
    (by ring) (by omega)]

lemma row6 (j : ℕ) : row (5 * j + 6) = [j + 1] := by
  have h5 : ¬ 5 ∣ 5 * j + 6 := by omega
  have hz : ((5 * j + 6 : ℕ) : ZMod 5) = 1 := by
    push_cast
    rw [show (5 : ZMod 5) = 0 from rfl, show (6 : ZMod 5) = 1 from rfl]
    simp
  unfold row
  rw [if_neg h5, hz, orderOf_one, show List.range 1 = [0] from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [dig (k := 0) (Q := j + 1) (D := 0) (d := j + 1) (R := 1) (by ring) (by norm_num) (by ring)
    (by omega)]

noncomputable def LL (N : ℕ) : List ℕ := (List.range N).flatMap (fun k => row (k + 2))

lemma Lsucc (N : ℕ) : LL (N + 1) = LL N ++ row (N + 2) := by
  simp [LL, List.range_succ, List.flatMap_append]

def blk (j : ℕ) : List ℕ :=
  [j, 2 * j, 4 * j + 1, 3 * j + 1, j, 3 * j + 1, 4 * j + 2, 2 * j + 1, j, 4 * j + 3, j + 1, j + 1]

lemma Lblock (j : ℕ) : LL (5 * j + 5) = LL (5 * j) ++ blk j := by
  rw [show 5 * j + 5 = 5 * j + 4 + 1 by ring, Lsucc, show 5 * j + 4 = 5 * j + 3 + 1 by ring, Lsucc,
    show 5 * j + 3 = 5 * j + 2 + 1 by ring, Lsucc, show 5 * j + 2 = 5 * j + 1 + 1 by ring, Lsucc,
    Lsucc]
  rw [show 5 * j + 1 + 1 + 2 = 5 * j + 4 by ring, show 5 * j + 1 + 2 = 5 * j + 3 by ring,
    show 5 * j + 3 + 2 = 5 * j + 5 by ring, show 5 * j + 4 + 2 = 5 * j + 6 by ring,
    row2, row3, row4, row5, row6]
  simp [blk]
  omega

lemma LL_len (j : ℕ) : (LL (5 * j)).length = 12 * j := by
  induction j with
  | zero => simp [LL]
  | succ j ih =>
    rw [show 5 * (j + 1) = 5 * j + 5 by ring, Lblock, List.length_append, ih]
    simp [blk]
    ring

lemma row_pos (b : ℕ) (hb : 2 ≤ b) : 1 ≤ (row b).length := by
  obtain ⟨j, r, hr, rfl⟩ : ∃ j r, r < 5 ∧ b = 5 * j + r + 2 :=
    ⟨(b - 2) / 5, (b - 2) % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · rw [row2]; simp
  · rw [show 5 * j + 1 + 2 = 5 * j + 3 by ring, row3]; simp
  · rw [show 5 * j + 2 + 2 = 5 * j + 4 by ring, row4]; simp
  · rw [show 5 * j + 3 + 2 = 5 * j + 5 by ring, row5]; simp
  · rw [show 5 * j + 4 + 2 = 5 * j + 6 by ring, row6]; simp

lemma LL_len_ge (N : ℕ) : N ≤ (LL N).length := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Lsucc, List.length_append]
    have := row_pos (N + 2) (by omega)
    omega

lemma LL_add (N e : ℕ) : ∃ R, LL (N + e) = LL N ++ R := by
  induction e with
  | zero => exact ⟨[], by simp⟩
  | succ e ih =>
    obtain ⟨R, hR⟩ := ih
    exact ⟨R ++ row (N + e + 2), by rw [← add_assoc, Lsucc, hR, List.append_assoc]⟩

lemma a_LL (n M : ℕ) (hn : 1 ≤ n) (h : n ≤ M) : a n = (LL M).getD (n - 1) 0 := by
  obtain ⟨R, hR⟩ := LL_add n (M - n)
  rw [show M = n + (M - n) by omega, hR, List.getD_append _ _ _ _ (by have := LL_len_ge n; omega)]
  rfl

lemma hblk (j t : ℕ) (ht : t < 12) : a (12 * j + t + 1) = (blk j).getD t 0 := by
  rw [a_LL _ (5 * j + 5 + (12 * j + t + 1)) (by omega) (by omega)]
  obtain ⟨R, hR⟩ := LL_add (5 * j + 5) (12 * j + t + 1)
  rw [hR, Lblock, List.append_assoc, List.getD_append_right _ _ _ _ (by rw [LL_len]; omega),
    LL_len, show 12 * j + t + 1 - 1 - 12 * j = t by omega,
    List.getD_append _ _ _ _ (by simp [blk]; omega)]

lemma a_zero : a 0 = 0 := by
  simp [a]

lemma cnumZ (c : ℕ) [c.AtLeastTwo] (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((no_index (OfNat.ofNat c : PowerSeries ℤ)) * p) =
      (OfNat.ofNat c : ℤ) * PowerSeries.coeff n p := by
  rw [← map_ofNat (PowerSeries.C (R := ℤ)) c, PowerSeries.coeff_C_mul]


open PowerSeries in
theorem mainP :
    (∀ n : ℕ, 24 < n → (a n : ℤ) = 2 * a (n - 12) - a (n - 24)) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * (X ^ 24 - 2 * X ^ 12 + 1) =
      X ^ 3 * (X ^ 19 + X ^ 18 + X ^ 17 + 2 * X ^ 16 + 2 * X ^ 15 + X ^ 14 + 2 * X ^ 13 + 3 * X ^ 12 +
        2 * X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + 3 * X ^ 7 + X ^ 5 + 2 * X ^ 4 + X ^ 3 + X + 1) := by
  have h0 := a_zero
  have hb := hblk
  generalize a = f at h0 hb ⊢
  have hrec : ∀ n : ℕ, 24 < n → (f n : ℤ) = 2 * f (n - 12) - f (n - 24) := by
    intro n hn
    obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 12 ∧ n = 12 * (i + 2) + t + 1 :=
      ⟨(n - 1) / 12 - 2, (n - 1) % 12, Nat.mod_lt _ (by norm_num), by omega⟩
    rw [show 12 * (i + 2) + t + 1 - 12 = 12 * (i + 1) + t + 1 by omega,
      show 12 * (i + 2) + t + 1 - 24 = 12 * i + t + 1 by omega, hb _ _ ht, hb _ _ ht, hb _ _ ht]
    interval_cases t <;> simp only [blk, List.getD_cons_succ, List.getD_cons_zero] <;> push_cast <;> ring
  refine ⟨hrec, ?_⟩
  have hL : ∀ S : PowerSeries ℤ, S * (X ^ 24 - 2 * X ^ 12 + 1) = S * X ^ 24 - 2 * (S * X ^ 12) + S :=
    fun S => by ring
  rw [hL]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', cnumZ, coeff_mk]
  rcases lt_or_ge n 25 with hn | hn
  · have v1 : f 1 = 0 := by simpa [blk] using hb 0 0 (by norm_num)
    have v2 : f 2 = 0 := by simpa [blk] using hb 0 1 (by norm_num)
    have v3 : f 3 = 1 := by simpa [blk] using hb 0 2 (by norm_num)
    have v4 : f 4 = 1 := by simpa [blk] using hb 0 3 (by norm_num)
    have v5 : f 5 = 0 := by simpa [blk] using hb 0 4 (by norm_num)
    have v6 : f 6 = 1 := by simpa [blk] using hb 0 5 (by norm_num)
    have v7 : f 7 = 2 := by simpa [blk] using hb 0 6 (by norm_num)
    have v8 : f 8 = 1 := by simpa [blk] using hb 0 7 (by norm_num)
    have v9 : f 9 = 0 := by simpa [blk] using hb 0 8 (by norm_num)
    have v10 : f 10 = 3 := by simpa [blk] using hb 0 9 (by norm_num)
    have v11 : f 11 = 1 := by simpa [blk] using hb 0 10 (by norm_num)
    have v12 : f 12 = 1 := by simpa [blk] using hb 0 11 (by norm_num)
    have v13 : f 13 = 1 := by simpa [blk] using hb 1 0 (by norm_num)
    have v14 : f 14 = 2 := by simpa [blk] using hb 1 1 (by norm_num)
    have v15 : f 15 = 5 := by simpa [blk] using hb 1 2 (by norm_num)
    have v16 : f 16 = 4 := by simpa [blk] using hb 1 3 (by norm_num)
    have v17 : f 17 = 1 := by simpa [blk] using hb 1 4 (by norm_num)
    have v18 : f 18 = 4 := by simpa [blk] using hb 1 5 (by norm_num)
    have v19 : f 19 = 6 := by simpa [blk] using hb 1 6 (by norm_num)
    have v20 : f 20 = 3 := by simpa [blk] using hb 1 7 (by norm_num)
    have v21 : f 21 = 1 := by simpa [blk] using hb 1 8 (by norm_num)
    have v22 : f 22 = 7 := by simpa [blk] using hb 1 9 (by norm_num)
    have v23 : f 23 = 2 := by simpa [blk] using hb 1 10 (by norm_num)
    have v24 : f 24 = 2 := by simpa [blk] using hb 1 11 (by norm_num)
    clear hb hrec hL
    interval_cases n <;> simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnumZ, map_ofNat, h0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24]
  · have hR : coeff n (X ^ 3 * (X ^ 19 + X ^ 18 + X ^ 17 + 2 * X ^ 16 + 2 * X ^ 15 + X ^ 14 + 2 * X ^ 13 + 3 * X ^ 12 +
        2 * X ^ 11 + X ^ 10 + X ^ 9 + X ^ 8 + 3 * X ^ 7 + X ^ 5 + 2 * X ^ 4 + X ^ 3 + X + 1) : PowerSeries ℤ) = 0 := by
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 25 := ⟨n - 25, by omega⟩
      simp [coeff_X_pow, coeff_X_pow_mul', coeff_X, cnumZ]
    rw [hR, if_pos (by omega), if_pos (by omega), hrec n (by omega)]
    ring

end OMA.P_a262114

theorem OMA.solution : type_of% @OMA.S_oeis_a262114.main := OMA.P_a262114.mainP
