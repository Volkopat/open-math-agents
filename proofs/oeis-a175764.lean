import OMAStatements.S_oeis_a175764

namespace OMA.S_oeis_a175764




theorem nextLargest_eq {m : ℕ} (hm : 2 ≤ m) : nextLargest m = m / m.minFac := by
  apply le_antisymm
  · apply Finset.sup_le
    intro e he
    rw [Nat.mem_properDivisors] at he
    obtain ⟨⟨c, hc⟩, hlt⟩ := he
    have hc2 : 2 ≤ c := by
      by_contra hc2
      push_neg at hc2
      interval_cases c <;> simp at hc <;> omega
    have hcm : c ∣ m := ⟨e, by rw [hc]; ring⟩
    have hmin : m.minFac ≤ c := Nat.minFac_le_of_dvd hc2 hcm
    have he' : e = m / c := by rw [hc, Nat.mul_div_cancel _ (by omega)]
    show e ≤ m / m.minFac
    rw [he']
    exact Nat.div_le_div_left hmin (Nat.minFac_pos m)
  · apply Finset.le_sup (f := id)
    rw [Nat.mem_properDivisors]
    exact ⟨Nat.div_dvd_of_dvd (Nat.minFac_dvd m),
      Nat.div_lt_self (by omega) (Nat.minFac_prime (by omega)).one_lt⟩

theorem f_eq (k : ℕ) : f k = (k ^ 2 + 4).minFac := by
  unfold f
  have h2 : 2 ≤ k ^ 2 + 4 := by
    have := Nat.zero_le (k ^ 2)
    omega
  rw [nextLargest_eq h2]
  exact Nat.div_div_self (Nat.minFac_dvd _) (by omega)

theorem sq4_mod (k r : ℕ) : (k ^ 2 + 4) % r = ((k % r) ^ 2 + 4) % r := by
  set s := k % r
  set q := k / r
  have hk : k = s + r * q := (Nat.mod_add_div k r).symm
  have h : k ^ 2 + 4 = ((s ^ 2 + 4) + r * (r * q ^ 2 + 2 * q * s)) := by
    rw [hk]
    ring
  rw [h, Nat.add_mul_mod_self_left]

theorem minFac_eq_of {m q : ℕ} (hq : q.Prime) (hqm : q ∣ m)
    (hlow : ∀ r, r.Prime → r < q → ¬ r ∣ m) : m.minFac = q := by
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hq.one_lt.ne' (Nat.dvd_one.mp hqm)
  have hle : m.minFac ≤ q := Nat.minFac_le_of_dvd hq.two_le hqm
  by_contra hne
  exact hlow m.minFac (Nat.minFac_prime hm1) (lt_of_le_of_ne hle hne) (Nat.minFac_dvd m)

theorem res3 : ∀ s < 3, (s ^ 2 + 4) % 3 ≠ 0 := by decide
theorem res7 : ∀ s < 7, (s ^ 2 + 4) % 7 ≠ 0 := by decide
theorem res11 : ∀ s < 11, (s ^ 2 + 4) % 11 ≠ 0 := by decide

theorem not3 (k : ℕ) : ¬ 3 ∣ k ^ 2 + 4 := by
  intro h
  have := res3 (k % 3) (Nat.mod_lt _ (by norm_num))
  rw [← sq4_mod] at this
  omega

theorem not7 (k : ℕ) : ¬ 7 ∣ k ^ 2 + 4 := by
  intro h
  have := res7 (k % 7) (Nat.mod_lt _ (by norm_num))
  rw [← sq4_mod] at this
  omega

theorem not11 (k : ℕ) : ¬ 11 ∣ k ^ 2 + 4 := by
  intro h
  have := res11 (k % 11) (Nat.mod_lt _ (by norm_num))
  rw [← sq4_mod] at this
  omega

/-- First conjecture: a(n) = 1 for n > 29 with n mod 10 in {0,1,2,4,6,8,9}. -/
theorem conjecture_one (n : ℕ) (hn : 29 < n)
    (hc : n % 10 = 0 ∨ n % 10 = 1 ∨ n % 10 = 2 ∨ n % 10 = 4 ∨ n % 10 = 6 ∨ n % 10 = 8 ∨
      n % 10 = 9) :
    IsLeast {t : ℕ | Target (f^[t] n)} 1 := by
  constructor
  · show Target (f n)
    rw [f_eq]
    by_cases he : n % 2 = 0
    · left
      apply (Nat.minFac_eq_two_iff _).mpr
      have h := sq4_mod n 2
      rw [he] at h
      omega
    · right; left
      have h5 : (n ^ 2 + 4) % 5 = 0 := by
        rw [sq4_mod]
        have : n % 5 = 1 ∨ n % 5 = 4 := by omega
        rcases this with h | h <;> rw [h] <;> norm_num
      apply minFac_eq_of (by norm_num) (Nat.dvd_of_mod_eq_zero h5)
      intro r hr hr5
      interval_cases r
      · norm_num at hr
      · norm_num at hr
      · intro h2
        have h := sq4_mod n 2
        have : n % 2 = 1 := by omega
        rw [this] at h
        omega
      · exact not3 n
      · norm_num at hr
  · intro t ht
    by_contra hlt
    push_neg at hlt
    interval_cases t
    · simp only [Set.mem_setOf_eq, Function.iterate_zero, id, Target] at ht
      omega

theorem c1 : f 13 = 173 := by rw [f_eq]; norm_num
theorem c2 : f 173 = 37 := by rw [f_eq]; norm_num
theorem c3 : f 37 = 1373 := by rw [f_eq]; norm_num
theorem c4 : f 1373 = 1217 := by rw [f_eq]; norm_num
theorem c5 : f 1217 = 97 := by rw [f_eq]; norm_num
theorem c6 : f 97 = 9413 := by rw [f_eq]; norm_num
theorem c7 : f 9413 = 89 := by rw [f_eq]; norm_num
theorem c8 : f 89 = 5 := by rw [f_eq]; norm_num

/-- Second conjecture: a(n) = 9 for n mod 130 in {3,23,55,75,107,127}. -/
theorem conjecture_nine (n : ℕ)
    (hc : n % 130 = 3 ∨ n % 130 = 23 ∨ n % 130 = 55 ∨ n % 130 = 75 ∨ n % 130 = 107 ∨
      n % 130 = 127) :
    IsLeast {t : ℕ | Target (f^[t] n)} 9 := by
  have h13 : (n ^ 2 + 4) % 13 = 0 := by
    rw [sq4_mod]
    have : n % 13 = 3 ∨ n % 13 = 10 := by omega
    rcases this with h | h <;> rw [h] <;> norm_num
  have hfn : f n = 13 := by
    rw [f_eq]
    apply minFac_eq_of (by norm_num) (Nat.dvd_of_mod_eq_zero h13)
    intro r hr hr13
    interval_cases r
    · norm_num at hr
    · norm_num at hr
    · intro h2
      have h := sq4_mod n 2
      have : n % 2 = 1 := by omega
      rw [this] at h
      omega
    · exact not3 n
    · norm_num at hr
    · intro h5
      have h := sq4_mod n 5
      have : n % 5 = 0 ∨ n % 5 = 2 ∨ n % 5 = 3 := by omega
      rcases this with h' | h' | h' <;> rw [h'] at h <;> omega
    · norm_num at hr
    · exact not7 n
    · norm_num at hr
    · norm_num at hr
    · norm_num at hr
    · exact not11 n
    · norm_num at hr
  have i1 : f^[1] 13 = 173 := by rw [Function.iterate_one]; exact c1
  have i2 : f^[2] 13 = 37 := by rw [Function.iterate_succ_apply', i1]; exact c2
  have i3 : f^[3] 13 = 1373 := by rw [Function.iterate_succ_apply', i2]; exact c3
  have i4 : f^[4] 13 = 1217 := by rw [Function.iterate_succ_apply', i3]; exact c4
  have i5 : f^[5] 13 = 97 := by rw [Function.iterate_succ_apply', i4]; exact c5
  have i6 : f^[6] 13 = 9413 := by rw [Function.iterate_succ_apply', i5]; exact c6
  have i7 : f^[7] 13 = 89 := by rw [Function.iterate_succ_apply', i6]; exact c7
  have i8 : f^[8] 13 = 5 := by rw [Function.iterate_succ_apply', i7]; exact c8
  have shift : ∀ t, f^[t + 1] n = f^[t] 13 := fun t => by
    rw [Function.iterate_succ_apply, hfn]
  constructor
  · show Target (f^[9] n)
    rw [shift 8, i8]
    right; left; rfl
  · intro t ht
    by_contra hlt
    push_neg at hlt
    simp only [Set.mem_setOf_eq] at ht
    interval_cases t
    · simp only [Function.iterate_zero, id, Target] at ht
      omega
    · rw [shift 0] at ht; simp [Target] at ht
    · rw [shift 1, i1] at ht; simp [Target] at ht
    · rw [shift 2, i2] at ht; simp [Target] at ht
    · rw [shift 3, i3] at ht; simp [Target] at ht
    · rw [shift 4, i4] at ht; simp [Target] at ht
    · rw [shift 5, i5] at ht; simp [Target] at ht
    · rw [shift 6, i6] at ht; simp [Target] at ht
    · rw [shift 7, i7] at ht; simp [Target] at ht

end OMA.S_oeis_a175764

theorem OMA.solution : type_of% @OMA.S_oeis_a175764.main :=
  ⟨fun n hn hc => OMA.S_oeis_a175764.conjecture_one n hn hc,
    fun n hc => OMA.S_oeis_a175764.conjecture_nine n hc⟩
