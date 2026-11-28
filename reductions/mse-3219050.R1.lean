import OMAStatements.S_mse_3219050

/-!
# Reduction R1 of mse-3219050: `2 ^ n - n` and `2 ^ n + n` both prime

The question asks whether `n = 3` and `n = 9` are the only natural numbers for
which both `2 ^ n - n` and `2 ^ n + n` are prime.

The reduction has three hypotheses; the first two are proved in this file, so
only `H3` stays open.

* `H1` (proved): no even `n` works.  If `n` is even then `2 ^ n + n` is even as
  well, and it is bigger than `2`, so it cannot be prime.
* `H2` (proved): an odd solution is divisible by `3`.  For odd `n` we have
  `2 ^ n = 2 (mod 3)`; when `n = 1 (mod 3)` this gives `3 | 2 ^ n + n`, and
  when `n = 2 (mod 3)` it gives `3 | 2 ^ n - n`.  A prime divisible by `3` must
  be `3` itself, which forces `n = 1`, respectively `n <= 2`, and neither
  works.
* `H3` (open): for odd `n` divisible by `3`, that is `n = 3 (mod 6)`, the two
  numbers are not both prime away from `n = 3` and `n = 9`.  This is the whole
  remaining difficulty: for `n = 3 m` with `m` odd and `n > 9`, one of
  `2 ^ n - n`, `2 ^ n + n` is composite.

So the target is reduced to the single family `n = 3 (mod 6)` with `n > 9`.

An exact primality search over `n <= 6000` finds only `n = 3` and `n = 9`, and
no solution that is even or that is not a multiple of `3`, so all three
hypotheses are consistent with the small cases.
-/

namespace OMA.R_mse_3219050_R1

/-- No even `n` makes both `2 ^ n - n` and `2 ^ n + n` prime, because then
`2 ^ n + n` is an even number larger than `2`. -/
def H1 : Prop := ∀ n : ℕ, Even n → (2 ^ n - n).Prime → (2 ^ n + n).Prime → False

/-- An odd `n` for which both numbers are prime is divisible by `3`: modulo `3`
one of `2 ^ n - n`, `2 ^ n + n` is a multiple of `3`, and being prime it would
have to be `3` itself. -/
def H2 : Prop := ∀ n : ℕ, Odd n → (2 ^ n - n).Prime → (2 ^ n + n).Prime → 3 ∣ n

/-- The remaining case: for odd multiples of `3`, the only `n` for which both
`2 ^ n - n` and `2 ^ n + n` are prime are `n = 3` and `n = 9`. -/
def H3 : Prop :=
  ∀ n : ℕ, Odd n → 3 ∣ n → (2 ^ n - n).Prime → (2 ^ n + n).Prime → n = 3 ∨ n = 9

lemma three_dvd_pow_odd (k : ℕ) : 3 ∣ 2 ^ (2 * k + 1) - 2 := by
  induction k with
  | zero => norm_num
  | succ m ih =>
    have hexp : 2 ^ (2 * (m + 1) + 1) = 4 * 2 ^ (2 * m + 1) := by
      have h : 2 * (m + 1) + 1 = 2 * m + 1 + 2 := by omega
      rw [h, pow_add]
      ring
    rw [hexp]
    have hP : 2 ≤ 2 ^ (2 * m + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have heq : 4 * 2 ^ (2 * m + 1) - 2 = 4 * (2 ^ (2 * m + 1) - 2) + 6 := by omega
    rw [heq]
    exact Nat.dvd_add (dvd_mul_of_dvd_right ih 4) (by norm_num)

lemma modEq_two_of_odd (n : ℕ) (hn : Odd n) : 2 ^ n ≡ 2 [MOD 3] := by
  obtain ⟨k, rfl⟩ := hn
  have hd := three_dvd_pow_odd k
  have hP : 2 ≤ 2 ^ (2 * k + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact ((Nat.modEq_iff_dvd' hP).2 hd).symm

lemma pow_bound (m : ℕ) (hm : 3 ≤ m) : m + 3 < 2 ^ m := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · norm_num at hm
      · norm_num at hm
      · norm_num
    · have h1 := ih hk
      have hP : 0 < 2 ^ k := pow_pos (by norm_num) k
      rw [pow_succ]
      nlinarith

theorem H1_proof : H1 := by
  intro n hn hp hq
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num at hp
    · exact h
  have h2n : 2 ∣ 2 ^ n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    exact ⟨2 ^ m, by rw [pow_succ']⟩
  have h2sum : 2 ∣ 2 ^ n + n := Nat.dvd_add h2n (even_iff_two_dvd.mp hn)
  have hbig : 3 ≤ 2 ^ n + n := by
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hnpos
    omega
  rcases hq.eq_one_or_self_of_dvd 2 h2sum with h | h <;> omega

theorem H2_proof : H2 := by
  intro n hn hp hq
  by_contra h3
  have h2n : 2 ^ n ≡ 2 [MOD 3] := modEq_two_of_odd n hn
  have hle : n ≤ 2 ^ n := Nat.le_of_lt Nat.lt_two_pow_self
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hne : n % 3 ≠ 0 := by
    intro h
    exact h3 (Nat.dvd_of_mod_eq_zero h)
  have hres : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hres with h1 | h2
  · have hm : n ≡ 1 [MOD 3] := by
      show n % 3 = 1 % 3
      simpa using h1
    have h30 : (3 : ℕ) ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr (dvd_refl 3)
    have hs : 2 ^ n + n ≡ 0 [MOD 3] := (h2n.add hm).trans h30
    have hd : 3 ∣ 2 ^ n + n := Nat.modEq_zero_iff_dvd.mp hs
    rcases hq.eq_one_or_self_of_dvd 3 hd with h | h
    · omega
    · have hn1 : n = 1 := by
        rcases Nat.lt_or_ge n 2 with h' | h'
        · have hpos : n ≠ 0 := by
            rintro rfl
            norm_num at hp
          omega
        · have h4 : 4 ≤ 2 ^ n := by
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h'
          omega
      subst hn1
      norm_num at hp
  · have hdr : n = 3 * (n / 3) + 2 := by
      have := Nat.div_add_mod n 3
      omega
    have hd2 : 3 ∣ n - 2 := ⟨n / 3, by omega⟩
    have hd2' : 3 ∣ 2 ^ n - 2 := by
      obtain ⟨k, rfl⟩ := hn
      exact three_dvd_pow_odd k
    have hdn : 3 ∣ 2 ^ n - n := by
      have hsub : 3 ∣ (2 ^ n - 2) - (n - 2) := Nat.dvd_sub hd2' hd2
      have heq : (2 ^ n - 2) - (n - 2) = 2 ^ n - n := by omega
      rwa [heq] at hsub
    rcases hp.eq_one_or_self_of_dvd 3 hdn with h | h
    · omega
    · have h3n : 2 ^ n - n = 3 := h.symm
      rcases Nat.lt_or_ge n 3 with h' | h'
      · obtain ⟨k, hk⟩ := hn
        omega
      · have heq : 2 ^ n = n + 3 := by
          have := (Nat.sub_eq_iff_eq_add hle).1 h3n
          omega
        have hkey := pow_bound n h'
        rw [heq] at hkey
        exact absurd hkey (lt_irrefl _)

theorem main : H1 → H2 → H3 → type_of% @OMA.S_mse_3219050.main := by
  intro h1 h2 h3 n hp hq
  rcases Nat.even_or_odd n with he | ho
  · exact (h1 n he hp hq).elim
  · exact h3 n ho (h2 n ho hp hq) hp hq

end OMA.R_mse_3219050_R1
