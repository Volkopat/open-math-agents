import OMAStatements.S_oeis_a309952

namespace OMA.S_oeis_a309952




/-- The XOR of the two bits of a residue mod 4. -/
def xr (r : ℕ) : ℕ := if r = 1 ∨ r = 2 then 1 else 0

lemma a_rec (n : ℕ) : a n = xr (n % 4) + 2 * a (n / 4) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a, xr, pairXor]
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have : n = 1 := by omega
    subst this
    simp [a, pairXor, xr]
  · have hd : Nat.digits 2 n = n % 2 :: (n / 2) % 2 :: Nat.digits 2 (n / 4) := by
      rw [Nat.digits_def' (by norm_num) hn, Nat.digits_def' (by norm_num) (by omega),
        Nat.div_div_eq_div_mul]
    unfold a
    rw [hd, pairXor, Nat.ofDigits_cons]
    congr 1
    have h4 : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
    have e1 : n % 2 = n % 4 % 2 := by omega
    have e2 : n / 2 % 2 = n % 4 / 2 := by omega
    rw [e1, e2]
    interval_cases (n % 4) <;> decide

lemma mdb_rec (k : ℕ) : mdb k = k % 2 + 4 * mdb (k / 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [mdb]
  · unfold mdb
    rw [Nat.digits_def' (by norm_num) hk, Nat.ofDigits_cons]

lemma a_mdb (k : ℕ) : a (mdb k) = k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [mdb, a, pairXor]
    · rw [a_rec, mdb_rec]
      have h1 : (k % 2 + 4 * mdb (k / 2)) % 4 = k % 2 := by omega
      have h2 : (k % 2 + 4 * mdb (k / 2)) / 4 = mdb (k / 2) := by omega
      rw [h1, h2, ih (k / 2) (by omega)]
      have : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
      interval_cases h : k % 2 <;> simp [xr] <;> omega

lemma mdb_le (m : ℕ) : mdb (a m) ≤ m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [mdb, a, pairXor]
    · rw [mdb_rec, a_rec]
      have hx : xr (m % 4) ≤ 1 := by unfold xr; split_ifs <;> omega
      have h1 : (xr (m % 4) + 2 * a (m / 4)) % 2 = xr (m % 4) := by omega
      have h2 : (xr (m % 4) + 2 * a (m / 4)) / 2 = a (m / 4) := by omega
      rw [h1, h2]
      have := ih (m / 4) (by omega)
      have hxr : xr (m % 4) ≤ m % 4 := by
        have h4 : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
        interval_cases (m % 4) <;> decide
      omega

/-- Ianakiev's conjecture: k first occurs in A309952 at index A000695(k). -/
theorem conjecture (k : ℕ) : a (mdb k) = k ∧ ∀ m < mdb k, a m ≠ k := by
  refine ⟨a_mdb k, fun m hm hmk => ?_⟩
  have := mdb_le m
  rw [hmk] at this
  omega

end OMA.S_oeis_a309952

theorem OMA.solution : type_of% @OMA.S_oeis_a309952.main :=
  fun k => OMA.S_oeis_a309952.conjecture k
