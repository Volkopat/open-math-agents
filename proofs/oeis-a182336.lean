import OMAStatements.S_oeis_a182336
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

namespace OMA.P_oeis_a182336

open OMA.S_oeis_a182336

private lemma count_one_digits2_zero : (Nat.digits 2 0).count 1 = 0 := by
  simp

private lemma count_one_digits2_mul_two (x : ℕ) :
    (Nat.digits 2 (2 * x)).count 1 = (Nat.digits 2 x).count 1 := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [Nat.digits_def' (by norm_num) (by omega : 0 < 2 * x)]
    have hm : (2 * x) % 2 = 0 := by omega
    have hd : (2 * x) / 2 = x := by omega
    rw [hm, hd, List.count_cons]
    simp

private lemma count_one_digits2_mul_pow_two (k x : ℕ) :
    (Nat.digits 2 (x * 2 ^ k)).count 1 = (Nat.digits 2 x).count 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, mul_comm (x * 2 ^ k) 2, count_one_digits2_mul_two, ih]

private lemma count_one_digits2_fifteen : (Nat.digits 2 15).count 1 = 4 := by
  decide

private lemma count_one_digits2_25 : (Nat.digits 2 25).count 1 = 3 := by
  decide

private lemma count_one_digits2_27 : (Nat.digits 2 27).count 1 = 4 := by
  decide

private lemma count_one_digits2_49 : (Nat.digits 2 49).count 1 = 3 := by
  decide

private lemma count_one_digits2_57 : (Nat.digits 2 57).count 1 = 4 := by
  decide

private lemma count_one_digits2_xor_pow (k : ℕ) :
    (Nat.digits 2 (15 * 2 ^ k)).count 1 = 4 := by
  rw [count_one_digits2_mul_pow_two, count_one_digits2_fifteen]

/-- For any `n`, `m = n ^^^ mask` has `n ^^^ m = mask`. -/
private lemma xor_cancel_left' (n mask : ℕ) : n ^^^ (n ^^^ mask) = mask := by
  rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]

/-- Finding the least bit index `p ≥ 3` where `n.testBit p = false`. -/
private lemma exists_false_bit_ge_three (n : ℕ) :
    ∃ p : ℕ, 3 ≤ p ∧ n.testBit p = false ∧ ∀ j : ℕ, 3 ≤ j → j < p → n.testBit j = true := by
  have hex : ∃ p : ℕ, 3 ≤ p ∧ n.testBit p = false := by
    refine ⟨max 3 (Nat.log 2 n + 1), le_max_left _ _, ?_⟩
    apply Nat.testBit_eq_false_of_lt
    have hlt : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    have hpow : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ max 3 (Nat.log 2 n + 1) :=
      Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
    omega
  classical
  let p := Nat.find hex
  have hp := Nat.find_spec hex
  refine ⟨p, hp.1, hp.2, fun j hj3 hjp => ?_⟩
  have hnot := Nat.find_min hex hjp
  cases h : n.testBit j
  · exact absurd ⟨hj3, h⟩ hnot
  · rfl

/-- If bits `a..b-1` of `n` are all true (`a ≤ b`), then `2^b - 2^a ≤ n % 2^b`. -/
private lemma mod_pow_ge_of_all_true (n a b : ℕ) (hab : a ≤ b)
    (hall : ∀ j : ℕ, a ≤ j → j < b → n.testBit j = true) :
    2 ^ b - 2 ^ a ≤ n % 2 ^ b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha; simp
  | succ b ih =>
    by_cases hEq : a = b + 1
    · subst hEq; simp
    · have hab' : a ≤ b := by omega
      have hprev := ih hab' (fun j hj1 hj2 => hall j hj1 (by omega))
      have hb : n.testBit b = true := hall b hab' (by omega)
      have hmod : n % 2 ^ (b + 1) = n % 2 ^ b + 2 ^ b * ((n / 2 ^ b) % 2) := by
        have h1 : 2 ^ b * (n / 2 ^ b) + n % 2 ^ b = n := Nat.div_add_mod n (2 ^ b)
        have h2 : 2 * ((n / 2 ^ b) / 2) + (n / 2 ^ b) % 2 = n / 2 ^ b := Nat.div_add_mod (n / 2 ^ b) 2
        have hdecomp : n = 2 ^ (b + 1) * ((n / 2 ^ b) / 2) + (n % 2 ^ b + 2 ^ b * ((n / 2 ^ b) % 2)) := by
          have hr : 2 ^ (b + 1) * ((n / 2 ^ b) / 2) + (n % 2 ^ b + 2 ^ b * ((n / 2 ^ b) % 2)) =
              2 ^ b * (2 * ((n / 2 ^ b) / 2) + (n / 2 ^ b) % 2) + n % 2 ^ b := by
            rw [pow_succ]; ring
          rw [hr, h2, h1]
        have hlt1 : n % 2 ^ b < 2 ^ b := Nat.mod_lt n (Nat.pow_pos (by norm_num))
        have hlt2 : (n / 2 ^ b) % 2 < 2 := Nat.mod_lt _ (by norm_num)
        have hlt : n % 2 ^ b + 2 ^ b * ((n / 2 ^ b) % 2) < 2 ^ (b + 1) := by
          rw [pow_succ]; nlinarith
        conv_lhs => rw [hdecomp]
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
      have hbit : (n / 2 ^ b) % 2 = 1 := by
        rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at hb
        simpa [Nat.and_one_is_mod] using hb
      rw [hmod, hbit, mul_one, pow_succ]
      have hpow : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab'
      omega

/-- Arithmetic of `n ^^^ (15 * 2^k)` when bit `k+3` of `n` is `false` and bits `k, k+1, k+2`
are `true`. -/
private lemma xor_fifteen_pow_eq (n k : ℕ)
    (h0 : n.testBit k = true) (h1 : n.testBit (k + 1) = true)
    (h2 : n.testBit (k + 2) = true) (h3 : n.testBit (k + 3) = false) :
    n ^^^ (15 * 2 ^ k) = n + 2 ^ k := by
  -- Express via quotient/remainder mod 2^k and mod 2^(k+4)
  have hdiv : (n / 2 ^ k) % 16 = 7 := by
    have b0 : ((n / 2 ^ k) / 1) % 2 = 1 := by
      rw [Nat.div_one]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at h0
      simpa [Nat.and_one_is_mod] using h0
    have b1 : ((n / 2 ^ k) / 2) % 2 = 1 := by
      rw [Nat.div_div_eq_div_mul, ← pow_succ]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at h1
      simpa [Nat.and_one_is_mod] using h1
    have b2 : ((n / 2 ^ k) / 4) % 2 = 1 := by
      rw [Nat.div_div_eq_div_mul, show 2 ^ k * 4 = 2 ^ (k + 2) by ring]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at h2
      simpa [Nat.and_one_is_mod] using h2
    have b3 : ((n / 2 ^ k) / 8) % 2 = 0 := by
      rw [Nat.div_div_eq_div_mul, show 2 ^ k * 8 = 2 ^ (k + 3) by ring]
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow] at h3
      simpa [Nat.and_one_is_mod] using h3
    omega
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor]
  by_cases hi : i < k
  · have h15 : (15 * 2 ^ k).testBit i = false := by
      rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
      have hd : 2 ^ (i + 1) ∣ 15 * 2 ^ k := by
        exact dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 (by omega)) 15
      have hmod : (15 * 2 ^ k / 2 ^ i) % 2 = 0 := by
        have : 2 * 2 ^ i ∣ 15 * 2 ^ k := by
          simpa [pow_succ, mul_comm] using hd
        rcases this with ⟨c, hc⟩
        have hpos : 0 < 2 ^ i := Nat.pow_pos (by norm_num)
        rw [hc, show 2 * 2 ^ i * c = 2 ^ i * (2 * c) by ring, Nat.mul_div_cancel_left _ hpos]
        omega
      simpa [Nat.and_one_is_mod] using hmod
    have hadd : (n + 2 ^ k).testBit i = n.testBit i := by
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hd : 2 ^ (i + 1) ∣ 2 ^ k := Nat.pow_dvd_pow 2 (by omega)
      have hpos : 0 < 2 ^ i := Nat.pow_pos (by norm_num)
      rcases hd with ⟨c, hc⟩
      have hc' : 2 ^ k = 2 ^ i * (2 * c) := by
        rw [hc, pow_succ]; ring
      rw [hc', Nat.add_mul_div_left _ _ hpos]
      simp
    rw [h15, Bool.xor_false, hadd]
  · push Not at hi
    set j := i - k
    have hij : i = k + j := by omega
    rw [hij]
    have hshift : ∀ x : ℕ, x.testBit (k + j) = (x / 2 ^ k).testBit j := by
      intro x
      rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
        Nat.div_div_eq_div_mul, pow_add]
    rw [hshift n, hshift (15 * 2 ^ k), hshift (n + 2 ^ k)]
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
    rw [Nat.mul_div_cancel _ hpos, Nat.add_div_right _ hpos]
    set q := n / 2 ^ k
    have hq : q = 16 * (q / 16) + 7 := by omega
    rw [hq]
    by_cases hj : j < 4
    · have hmod4 : ∀ x : ℕ, (16 * (q / 16) + x).testBit j = x.testBit j := by
        intro x
        rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
        have hd : 2 ^ (j + 1) ∣ 16 := by
          have : 2 ^ (j + 1) ∣ 2 ^ 4 := Nat.pow_dvd_pow 2 (by omega)
          simpa using this
        rcases hd with ⟨c, hc⟩
        have hposj : 0 < 2 ^ j := Nat.pow_pos (by norm_num)
        have h16 : 16 * (q / 16) = 2 ^ j * (2 * (c * (q / 16))) := by
          rw [hc, pow_succ]; ring
        rw [h16, add_comm, Nat.add_mul_div_left _ _ hposj]
        simp
      rw [hmod4 7, show 16 * (q / 16) + 7 + 1 = 16 * (q / 16) + 8 by ring, hmod4 8]
      interval_cases j <;> decide
    · push Not at hj
      have h15j : (15 : ℕ).testBit j = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : 15 < 2 ^ 4)
          (Nat.pow_le_pow_right (by norm_num) hj))
      rw [h15j, Bool.xor_false]
      have htop : ∀ x : ℕ, x < 16 → (16 * (q / 16) + x).testBit j = (q / 16).testBit (j - 4) := by
        intro x hx
        rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
        have hj4 : j = 4 + (j - 4) := by omega
        conv_lhs => rw [hj4, pow_add, ← Nat.div_div_eq_div_mul]
        have hdiv16 : (16 * (q / 16) + x) / 2 ^ 4 = q / 16 := by omega
        rw [hdiv16]
      rw [htop 7 (by norm_num), show 16 * (q / 16) + 7 + 1 = 16 * (q / 16) + 8 by ring,
        htop 8 (by norm_num)]

/-- Explicit witness `m > n` with `hammingDist n m = 4` and `8 * (m - 1) ≤ 9 * n` for `n > 96`. -/
private lemma exists_good_witness {n : ℕ} (hn : 96 < n) :
    ∃ m : ℕ, n < m ∧ hammingDist n m = 4 ∧ 8 * (m - 1) ≤ 9 * n := by
  obtain ⟨p, hp3, hpf, hall⟩ := exists_false_bit_ge_three n
  by_cases hp6 : 6 ≤ p
  · refine ⟨n ^^^ (15 * 2 ^ (p - 3)), ?_, ?_, ?_⟩
    · have h0 : n.testBit (p - 3) = true := hall (p - 3) (by omega) (by omega)
      have h1 : n.testBit (p - 3 + 1) = true := hall (p - 3 + 1) (by omega) (by omega)
      have h2 : n.testBit (p - 3 + 2) = true := hall (p - 3 + 2) (by omega) (by omega)
      have h3 : n.testBit (p - 3 + 3) = false := by rwa [show p - 3 + 3 = p by omega]
      rw [xor_fifteen_pow_eq n (p - 3) h0 h1 h2 h3]
      have : 0 < 2 ^ (p - 3) := Nat.pow_pos (by norm_num)
      omega
    · unfold hammingDist
      rw [xor_cancel_left', count_one_digits2_xor_pow]
    · have h0 : n.testBit (p - 3) = true := hall (p - 3) (by omega) (by omega)
      have h1 : n.testBit (p - 3 + 1) = true := hall (p - 3 + 1) (by omega) (by omega)
      have h2 : n.testBit (p - 3 + 2) = true := hall (p - 3 + 2) (by omega) (by omega)
      have h3 : n.testBit (p - 3 + 3) = false := by rwa [show p - 3 + 3 = p by omega]
      rw [xor_fifteen_pow_eq n (p - 3) h0 h1 h2 h3]
      have hge : 2 ^ p - 2 ^ 3 ≤ n % 2 ^ p := mod_pow_ge_of_all_true n 3 p (by omega) hall
      have hle : n % 2 ^ p ≤ n := Nat.mod_le n (2 ^ p)
      have hpow : 8 * 2 ^ (p - 3) = 2 ^ p := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add, show 3 + (p - 3) = p by omega]
      have h8 : 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  · -- p ∈ {3, 4, 5}: operate purely within low 6 bits (mod 64)!
    have hp_cases : p = 3 ∨ p = 4 ∨ p = 5 := by omega
    -- Write n = 64 * q + r with r < 64
    set q := n / 64
    set r := n % 64
    have hnr : n = 64 * q + r := by omega
    have hr64 : r < 64 := Nat.mod_lt n (by norm_num)
    have hbit_r : ∀ j < 6, n.testBit j = r.testBit j := by
      intro j hj
      rw [hnr, Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
      have hd : 2 ^ (j + 1) ∣ 64 := by
        have : 2 ^ (j + 1) ∣ 2 ^ 6 := Nat.pow_dvd_pow 2 (by omega)
        simpa using this
      rcases hd with ⟨c, hc⟩
      have hpos : 0 < 2 ^ j := Nat.pow_pos (by norm_num)
      have h64 : 64 * q = 2 ^ j * (2 * (c * q)) := by rw [hc, pow_succ]; ring
      rw [h64, add_comm, Nat.add_mul_div_left _ _ hpos]
      simp
    have hxor_low : ∀ mask < 64, n ^^^ mask = 64 * q + (r ^^^ mask) := by
      intro mask hmask
      apply Nat.eq_of_testBit_eq
      intro i
      rw [Nat.testBit_xor]
      by_cases hi : i < 6
      · rw [hbit_r i hi]
        have hrm : (r ^^^ mask) < 64 := by
          have : r ^^^ mask < 2 ^ 6 := Nat.xor_lt_two_pow hr64 hmask
          simpa using this
        have hright : (64 * q + (r ^^^ mask)).testBit i = (r ^^^ mask).testBit i := by
          rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
          have hd : 2 ^ (i + 1) ∣ 64 := by
            have : 2 ^ (i + 1) ∣ 2 ^ 6 := Nat.pow_dvd_pow 2 (by omega)
            simpa using this
          rcases hd with ⟨c, hc⟩
          have hpos : 0 < 2 ^ i := Nat.pow_pos (by norm_num)
          have h64 : 64 * q = 2 ^ i * (2 * (c * q)) := by rw [hc, pow_succ]; ring
          rw [h64, add_comm, Nat.add_mul_div_left _ _ hpos]
          simp
        rw [hright, Nat.testBit_xor]
      · push Not at hi
        have hmj : mask.testBit i = false :=
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (show mask < 2 ^ 6 by omega)
            (Nat.pow_le_pow_right (by norm_num) hi))
        rw [hmj, Bool.xor_false]
        have hrm : r ^^^ mask < 64 := by
          have : r ^^^ mask < 2 ^ 6 := Nat.xor_lt_two_pow hr64 hmask
          simpa using this
        have htop : ∀ x < 64, (64 * q + x).testBit i = q.testBit (i - 6) := by
          intro x hx
          rw [Nat.testBit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
          have hi6 : i = 6 + (i - 6) := by omega
          conv_lhs => rw [hi6, pow_add, ← Nat.div_div_eq_div_mul]
          have hdiv : (64 * q + x) / 2 ^ 6 = q := by omega
          rw [hdiv]
        rw [hnr, htop r hr64, htop (r ^^^ mask) hrm]
    rcases hp_cases with rfl | rfl | rfl
    · -- p = 3: mask = 15 (bits 3,2,1,0)
      refine ⟨n ^^^ 15, ?_, ?_, ?_⟩
      · rw [hxor_low 15 (by norm_num)]
        have hr3 : r.testBit 3 = false := by rw [← hbit_r 3 (by norm_num)]; exact hpf
        have hlt : r < r ^^^ 15 := by
          have : ∀ x : ℕ, x < 64 → x.testBit 3 = false → x < x ^^^ 15 := by decide
          exact this r hr64 hr3
        omega
      · unfold hammingDist; rw [xor_cancel_left']; exact count_one_digits2_fifteen
      · rw [hxor_low 15 (by norm_num)]
        have hr3 : r.testBit 3 = false := by rw [← hbit_r 3 (by norm_num)]; exact hpf
        by_cases hr8 : r % 8 = 0
        · have h16 : n % 16 = 0 := by
            have : ∀ x : ℕ, x < 64 → x.testBit 3 = false → x % 8 = 0 → x % 16 = 0 := by decide
            have hrm16 := this r hr64 hr3 hr8
            omega
          have hn112 : 112 ≤ n := by omega
          have hle : r ^^^ 15 ≤ r + 15 := by
            have : ∀ x : ℕ, x < 64 → x ^^^ 15 ≤ x + 15 := by decide
            exact this r hr64
          omega
        · have hle : r ^^^ 15 ≤ r + 13 := by
            have : ∀ x : ℕ, x < 64 → x.testBit 3 = false → x % 8 ≠ 0 → x ^^^ 15 ≤ x + 13 := by decide
            exact this r hr64 hr3 hr8
          omega
    · -- p = 4: mask = 27 (bits 4,3,1,0)
      refine ⟨n ^^^ 27, ?_, ?_, ?_⟩
      · rw [hxor_low 27 (by norm_num)]
        have hr3 : r.testBit 3 = true := by rw [← hbit_r 3 (by norm_num)]; exact hall 3 (by omega) (by omega)
        have hr4 : r.testBit 4 = false := by rw [← hbit_r 4 (by norm_num)]; exact hpf
        have hlt : r < r ^^^ 27 := by
          have : ∀ x : ℕ, x < 64 → x.testBit 3 = true → x.testBit 4 = false → x < x ^^^ 27 := by decide
          exact this r hr64 hr3 hr4
        omega
      · unfold hammingDist; rw [xor_cancel_left']; exact count_one_digits2_27
      · rw [hxor_low 27 (by norm_num)]
        have hr3 : r.testBit 3 = true := by rw [← hbit_r 3 (by norm_num)]; exact hall 3 (by omega) (by omega)
        have hr4 : r.testBit 4 = false := by rw [← hbit_r 4 (by norm_num)]; exact hpf
        have hle : r ^^^ 27 ≤ r + 11 := by
          have : ∀ x : ℕ, x < 64 → x.testBit 3 = true → x.testBit 4 = false → x ^^^ 27 ≤ x + 11 := by decide
          exact this r hr64 hr3 hr4
        omega
    · -- p = 5: mask = 57 (bits 5,4,3,0)
      refine ⟨n ^^^ 57, ?_, ?_, ?_⟩
      · rw [hxor_low 57 (by norm_num)]
        have hr3 : r.testBit 3 = true := by rw [← hbit_r 3 (by norm_num)]; exact hall 3 (by omega) (by omega)
        have hr4 : r.testBit 4 = true := by rw [← hbit_r 4 (by norm_num)]; exact hall 4 (by omega) (by omega)
        have hr5 : r.testBit 5 = false := by rw [← hbit_r 5 (by norm_num)]; exact hpf
        have hlt : r < r ^^^ 57 := by
          have : ∀ x : ℕ, x < 64 → x.testBit 3 = true → x.testBit 4 = true → x.testBit 5 = false →
            x < x ^^^ 57 := by decide
          exact this r hr64 hr3 hr4 hr5
        omega
      · unfold hammingDist; rw [xor_cancel_left']; exact count_one_digits2_57
      · rw [hxor_low 57 (by norm_num)]
        have hr3 : r.testBit 3 = true := by rw [← hbit_r 3 (by norm_num)]; exact hall 3 (by omega) (by omega)
        have hr4 : r.testBit 4 = true := by rw [← hbit_r 4 (by norm_num)]; exact hall 4 (by omega) (by omega)
        have hr5 : r.testBit 5 = false := by rw [← hbit_r 5 (by norm_num)]; exact hpf
        have hle : r ^^^ 57 ≤ r + 9 := by
          have : ∀ x : ℕ, x < 64 → x.testBit 3 = true → x.testBit 4 = true → x.testBit 5 = false →
            x ^^^ 57 ≤ x + 9 := by decide
          exact this r hr64 hr3 hr4 hr5
        omega

private theorem prove_main : type_of% @OMA.S_oeis_a182336.main := by
  intro n hn
  obtain ⟨m, hnm, hdist, hbound⟩ := exists_good_witness hn
  have hex : ({k : ℕ | n ≤ k ∧ hammingDist n k = 4}).Nonempty := ⟨m, le_of_lt hnm, hdist⟩
  have hamem : a n ∈ {k : ℕ | n ≤ k ∧ hammingDist n k = 4} := Nat.sInf_mem hex
  have hale : a n ≤ m := Nat.sInf_le ⟨le_of_lt hnm, hdist⟩
  have hne : a n ≠ n := by
    intro heq
    have h0 : hammingDist n n = 0 := by
      unfold hammingDist
      rw [Nat.xor_self]
      exact count_one_digits2_zero
    have := hamem.2
    rw [heq, h0] at this
    omega
  have hge : n + 1 ≤ a n := by have := hamem.1; omega
  have hub : 8 * (a n - 1) ≤ 9 * n := by omega
  constructor
  · exact_mod_cast hge
  · have hq : (8 : ℚ) * ((a n : ℚ) - 1) ≤ 9 * (n : ℚ) := by
      have ha1 : 1 ≤ a n := by omega
      have hcast : ((8 * (a n - 1) : ℕ) : ℚ) ≤ ((9 * n : ℕ) : ℚ) := by exact_mod_cast hub
      rw [Nat.cast_mul, Nat.cast_sub ha1] at hcast
      push_cast at hcast
      linarith
    linarith

end OMA.P_oeis_a182336

theorem OMA.solution : type_of% @OMA.S_oeis_a182336.main :=
  OMA.P_oeis_a182336.prove_main
