import OMAStatements.S_oeis_a002063

/-!
# OEIS A002063

The squares expressible as the sum of exactly two distinct powers of two are precisely the
terms `9 * 4^n`.

Writing `x ^ 2 = 2 ^ i * (1 + 2 ^ (j - i))`, the odd factor `1 + 2 ^ (j - i)` must be the whole
odd part of the square: it is a perfect square, and the exponent `i` is even. A descent shows the
first, and `y ^ 2 = 2 ^ d + 1` then forces `d = 3`, because the two neighbours `y - 1`, `y + 1`
of the odd number `y` are powers of two differing by `2`, hence `2` and `4`.
-/

namespace OMA.S_oeis_a002063

/-- If `x ^ 2 = 2 ^ i * m` with `m` odd, then `i` is even and `m` is a perfect square: the odd
factor must absorb the whole odd part of the square. -/
lemma even_and_sq_of_odd {i m : ℕ} (hm : Odd m) :
    ∀ x : ℕ, x ^ 2 = 2 ^ i * m → ∃ e : ℕ, i = 2 * e ∧ ∃ y : ℕ, m = y ^ 2 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro x hx
    rcases i with _ | k
    · exact ⟨0, rfl, x, by simpa using hx.symm⟩
    · -- `x ^ 2 = 2 ^ (k + 1) * m`, so `x` is even
      have hdvd : 2 ∣ x ^ 2 := by
        rw [hx]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) m
      obtain ⟨u, rfl⟩ := Nat.prime_two.dvd_of_dvd_pow hdvd
      -- cancel one factor `2`: `2 * u ^ 2 = 2 ^ k * m`
      have hstep : 2 * (2 * u ^ 2) = 2 * (2 ^ k * m) := by
        calc 2 * (2 * u ^ 2) = (2 * u) ^ 2 := by ring
          _ = 2 ^ (k + 1) * m := hx
          _ = 2 * (2 ^ k * m) := by rw [pow_succ]; ring
      have hu2 : 2 * u ^ 2 = 2 ^ k * m := Nat.mul_left_cancel (by norm_num) hstep
      rcases k with _ | j
      · -- `2 * u ^ 2 = m` makes `m` even
        exfalso
        rw [pow_zero, one_mul] at hu2
        obtain ⟨t, ht⟩ := hm
        omega
      · -- cancel a second `2` and apply the induction hypothesis
        have hstep2 : 2 * u ^ 2 = 2 * (2 ^ j * m) := by
          rw [hu2, pow_succ]
          ring
        have hu3 : u ^ 2 = 2 ^ j * m := Nat.mul_left_cancel (by norm_num) hstep2
        obtain ⟨e, he, y, hy⟩ := ih j (by omega) u hu3
        exact ⟨e + 1, by omega, y, hy⟩

/-- `y ^ 2 = 2 ^ d + 1` with `d ≥ 1` forces `d = 3`: the two neighbours of the odd number `y`,
whose product is a power of two, must be `2` and `4`. -/
lemma three_of_sq {y d : ℕ} (hd : 1 ≤ d) (h : y ^ 2 = 2 ^ d + 1) : d = 3 := by
  have hpow : 0 < 2 ^ d := pow_pos (by norm_num) d
  have hy2 : 2 ≤ y := by
    rcases Nat.lt_or_ge y 2 with h' | h'
    · interval_cases y <;> omega
    · exact h'
  obtain ⟨u, rfl⟩ : ∃ u, y = u + 1 := ⟨y - 1, by omega⟩
  -- `u * (u + 2) = 2 ^ d`
  have hu2 : u * (u + 2) = 2 ^ d := by
    have h1 : (u + 1) ^ 2 = u * (u + 2) + 1 := by ring
    omega
  -- both factors are powers of two
  obtain ⟨a, _, hua⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp ⟨u + 2, hu2.symm⟩
  obtain ⟨c, _, huc⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp ⟨u, by rw [mul_comm]; exact hu2.symm⟩
  have hlt : 2 ^ a < 2 ^ c := by omega
  have hac : a < c := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  -- `u = 2`: the two powers of two differ by `2`, so the smaller one is `2`
  have ha : a = 1 := by
    rcases Nat.eq_zero_or_pos a with h0 | hapos
    · exfalso
      have h1 : u = 1 := by simp [hua, h0]
      have h3 : 2 ^ d = 3 := by rw [← hu2, h1]
      have h4 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
      rw [h3] at h4
      norm_num at h4
    · have hu2' : 2 ≤ u := by
        have hpos : 0 < 2 ^ (a - 1) := pow_pos (by norm_num) _
        rw [hua, show a = a - 1 + 1 by omega, pow_succ]
        omega
      have hle : 2 ^ c ≤ 2 ^ (a + 1) := by
        have h1 : 2 ^ c = u + 2 := huc.symm
        have h2 : 2 ^ (a + 1) = 2 * u := by rw [pow_succ, ← hua]; ring
        omega
      have hca : c = a + 1 := by
        have hc : c ≤ a + 1 := (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
        omega
      have hu : u = 2 := by
        have h1 : u + 2 = 2 ^ (a + 1) := by rw [huc, hca]
        have h2 : 2 ^ (a + 1) = 2 * u := by rw [pow_succ, ← hua]; ring
        omega
      have h2a : 2 ^ a = 2 := by rw [← hua]; exact hu
      have h2a' : (2 : ℕ) ^ a = 2 ^ 1 := by rw [h2a]; norm_num
      exact Nat.pow_right_injective (by norm_num) h2a'
  have h8 : 2 ^ d = 8 := by rw [← hu2, hua, ha]; norm_num
  have h98 : (2 : ℕ) ^ d = 2 ^ 3 := by norm_num [h8]
  exact Nat.pow_right_injective (by norm_num) h98

end OMA.S_oeis_a002063

theorem OMA.solution : type_of% @OMA.S_oeis_a002063.main := by
  intro x
  constructor
  · rintro ⟨i, j, hij, hx⟩
    obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd : 1 ≤ d := by omega
    have hxd : x ^ 2 = 2 ^ i * (1 + 2 ^ d) := by
      rw [hx, pow_add]
      ring
    have hodd : Odd (1 + 2 ^ d) := by
      have h2 : 2 ^ d = 2 * 2 ^ (d - 1) := by
        calc 2 ^ d = 2 ^ (d - 1 + 1) := by rw [show d - 1 + 1 = d by omega]
          _ = 2 ^ (d - 1) * 2 := pow_succ _ _
          _ = 2 * 2 ^ (d - 1) := by ring
      exact ⟨2 ^ (d - 1), by rw [h2]; ring⟩
    obtain ⟨e, he, y, hy⟩ := OMA.S_oeis_a002063.even_and_sq_of_odd hodd x hxd
    have h3 : d = 3 := OMA.S_oeis_a002063.three_of_sq hd (by rw [← hy]; ring)
    have h4 : (4 : ℕ) ^ e = 2 ^ (2 * e) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    refine ⟨e, ?_⟩
    calc x ^ 2 = 2 ^ i * (1 + 2 ^ d) := hxd
      _ = 2 ^ (2 * e) * 9 := by rw [he, h3]; norm_num
      _ = 9 * 4 ^ e := by rw [← h4]; ring
  · rintro ⟨n, hx⟩
    refine ⟨2 * n, 2 * n + 3, by omega, ?_⟩
    have h4 : (2 : ℕ) ^ (2 * n) = 4 ^ n := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
    have h8 : (2 : ℕ) ^ (2 * n + 3) = 8 * 4 ^ n := by
      rw [pow_add, h4, show (2 : ℕ) ^ 3 = 8 by norm_num]
      ring
    rw [hx, h4, h8]
    ring
