import OMAStatements.S_oeis_a216498
import Mathlib

namespace OMA.S_oeis_a216498

def noDiv (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | f + 1, k => if n < k * k then true else if n % k = 0 then false else noDiv n f (k + 1)

lemma noDiv_sound (n : ℕ) : ∀ f k, noDiv n f k = true → ∀ j, k ≤ j → j < k + f → j * j ≤ n → n % j ≠ 0 := by
  intro f
  induction f with
  | zero => intro k _ j hk hj; omega
  | succ f ih =>
    intro k h j hk hj hjn
    unfold noDiv at h
    by_cases h1 : n < k * k
    · have : k * k ≤ j * j := Nat.mul_le_mul hk hk
      omega
    · rw [if_neg h1] at h
      by_cases h2 : n % k = 0
      · rw [if_pos h2] at h; simp at h
      · rw [if_neg h2] at h
        rcases Nat.eq_or_lt_of_le hk with rfl | hk'
        · exact h2
        · exact ih (k + 1) h j hk' (by omega) hjn

lemma noDiv_complete (n : ℕ) : ∀ f k, noDiv n f k = false → ∃ j, k ≤ j ∧ j * j ≤ n ∧ n % j = 0 := by
  intro f
  induction f with
  | zero => intro k h; simp [noDiv] at h
  | succ f ih =>
    intro k h
    unfold noDiv at h
    by_cases h1 : n < k * k
    · rw [if_pos h1] at h; simp at h
    · rw [if_neg h1] at h
      by_cases h2 : n % k = 0
      · exact ⟨k, le_refl _, by omega, h2⟩
      · rw [if_neg h2] at h
        obtain ⟨j, hj1, hj2, hj3⟩ := ih (k + 1) h
        exact ⟨j, by omega, hj2, hj3⟩

def isP (n : ℕ) : Bool := decide (2 ≤ n) && noDiv n n 2

lemma isP_sound {n : ℕ} (h : isP n = true) : n.Prime := by
  unfold isP at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [Nat.prime_def_le_sqrt]
  refine ⟨h1, fun m hm hms hd => ?_⟩
  have hmm : m * m ≤ n := by
    have := Nat.sqrt_le n
    calc m * m ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul hms hms
      _ ≤ n := this
  have hmn : m < 2 + n := by nlinarith
  exact noDiv_sound n n 2 h2 m hm hmn hmm (Nat.mod_eq_zero_of_dvd hd)

def qk (n : ℕ) : Bool := decide (n ≤ 31) ||
  (n % 2 != 0 && n % 3 != 0 && n % 5 != 0 && n % 7 != 0 && n % 11 != 0 && n % 13 != 0 &&
    n % 17 != 0 && n % 19 != 0 && n % 23 != 0 && n % 29 != 0 && n % 31 != 0)

lemma pm {n : ℕ} (hn : n.Prime) (h : 31 < n) (q : ℕ) (hq : 2 ≤ q) (hq2 : q ≤ 31) : n % q ≠ 0 := by
  intro h0
  rcases (Nat.dvd_prime hn).1 (Nat.dvd_of_mod_eq_zero h0) with h1 | h1
  · omega
  · omega

lemma qk_prime {n : ℕ} (hn : n.Prime) : qk n = true := by
  by_cases h : n ≤ 31
  · simp [qk, h]
  · have h' : 31 < n := by omega
    have := pm hn h'
    have h2 := this 2 (by norm_num) (by norm_num)
    simp [qk, this 3 (by norm_num) (by norm_num), this 5 (by norm_num) (by norm_num), this 7 (by norm_num) (by norm_num),
      this 11 (by norm_num) (by norm_num), this 13 (by norm_num) (by norm_num), this 17 (by norm_num) (by norm_num), this 19 (by norm_num) (by norm_num),
      this 23 (by norm_num) (by norm_num), this 29 (by norm_num) (by norm_num), this 31 (by norm_num) (by norm_num)]
    omega

lemma isP_complete {n : ℕ} (h : n.Prime) : isP n = true := by
  unfold isP
  have h2 := h.two_le
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨h2, ?_⟩
  by_contra hc
  rw [Bool.not_eq_true] at hc
  obtain ⟨j, hj1, hj2, hj3⟩ := noDiv_complete n n 2 hc
  have hd : j ∣ n := Nat.dvd_of_mod_eq_zero hj3
  rcases (Nat.dvd_prime h).1 hd with rfl | rfl
  · omega
  · nlinarith

def chkR (p lo : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => !(qk (p - 6 * (lo + k + 1)) && qk (p - 2 * (6 * (lo + k + 1))) &&
      qk (p - 3 * (6 * (lo + k + 1))) && qk (p - 4 * (6 * (lo + k + 1))) &&
      qk (p - 5 * (6 * (lo + k + 1))) && isP (p - 6 * (lo + k + 1)) &&
      isP (p - 2 * (6 * (lo + k + 1))) && isP (p - 3 * (6 * (lo + k + 1))) &&
      isP (p - 4 * (6 * (lo + k + 1))) && isP (p - 5 * (6 * (lo + k + 1)))) && chkR p lo k

lemma chkR_sound (p lo : ℕ) : ∀ N, chkR p lo N = true → ∀ j, lo < j → j ≤ lo + N →
    ¬ ((p - 6 * j).Prime ∧ (p - 2 * (6 * j)).Prime ∧ (p - 3 * (6 * j)).Prime ∧
      (p - 4 * (6 * j)).Prime ∧ (p - 5 * (6 * j)).Prime) := by
  intro N
  induction N with
  | zero => intro _ j h1 h2; omega
  | succ N ih =>
    intro h j hd hdN
    unfold chkR at h
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    rcases Nat.eq_or_lt_of_le hdN with rfl | hlt
    · rintro ⟨a, b, c, e, f⟩
      simp [qk_prime a, qk_prime b, qk_prime c, qk_prime e, qk_prime f, isP_complete a, isP_complete b, isP_complete c, isP_complete e, isP_complete f, show lo + N + 1 = lo + (N + 1) by omega] at h1
    · exact ih h2 j hd (by omega)

theorem c0 : chkR 2668453 0 6000 = true := by decide +kernel
theorem c1 : chkR 2668453 6000 6000 = true := by decide +kernel
theorem c2 : chkR 2668453 12000 6000 = true := by decide +kernel
theorem c3 : chkR 2668453 18000 6000 = true := by decide +kernel
theorem c4 : chkR 2668453 24000 6000 = true := by decide +kernel
theorem c5 : chkR 2668453 30000 6000 = true := by decide +kernel
theorem c6 : chkR 2668453 36000 6000 = true := by decide +kernel
theorem c7 : chkR 2668453 42000 6000 = true := by decide +kernel
theorem c8 : chkR 2668453 48000 6000 = true := by decide +kernel
theorem c9 : chkR 2668453 54000 6000 = true := by decide +kernel
theorem c10 : chkR 2668453 60000 6000 = true := by decide +kernel
theorem c11 : chkR 2668453 66000 6000 = true := by decide +kernel
theorem c12 : chkR 2668453 72000 6000 = true := by decide +kernel
theorem c13 : chkR 2668453 78000 6000 = true := by decide +kernel
theorem c14 : chkR 2668453 84000 6000 = true := by decide +kernel

lemma tbl (i : ℕ) (hi : i < 15) : chkR 2668453 (i * 6000) 6000 = true := by
  match i, hi with
  | 0, _ => exact c0
  | 1, _ => exact c1
  | 2, _ => exact c2
  | 3, _ => exact c3
  | 4, _ => exact c4
  | 5, _ => exact c5
  | 6, _ => exact c6
  | 7, _ => exact c7
  | 8, _ => exact c8
  | 9, _ => exact c9
  | 10, _ => exact c10
  | 11, _ => exact c11
  | 12, _ => exact c12
  | 13, _ => exact c13
  | 14, _ => exact c14
  | n + 15, h => omega

lemma allc (j : ℕ) (h0 : 0 < j) (h1 : j ≤ 90000) :
    ¬ (((2668453:ℕ) - (6 * j)).Prime ∧ (2668453 - 2 * (6 * j)).Prime ∧ (2668453 - 3 * (6 * j)).Prime ∧ (2668453 - 4 * (6 * j)).Prime ∧ (2668453 - 5 * (6 * j)).Prime) := by
  have hi : (j - 1) / 6000 < 15 := by omega
  exact chkR_sound _ _ _ (tbl _ hi) j (by omega) (by omega)

lemma prime_p : (2668453 : ℕ).Prime := isP_sound (by decide +kernel)

lemma pre {q : ℕ} (hq : q.Prime) (r : ℕ) (hr : 2 ≤ r) (hd : r ∣ q) : q = r := by
  rcases (Nat.dvd_prime hq).1 hd with h | h
  · omega
  · exact h.symm

lemma allD (d : ℕ) (hd : 0 < d) (hlt : 5 * d < 2668453) :
    ¬ (((2668453:ℕ) - d).Prime ∧ (2668453 - 2 * d).Prime ∧ (2668453 - 3 * d).Prime ∧ (2668453 - 4 * d).Prime ∧ (2668453 - 5 * d).Prime) := by
  rintro ⟨h1, h2, h3, h4, h5⟩
  by_cases h6 : 6 ∣ d
  · obtain ⟨j, rfl⟩ := h6
    exact allc j (by omega) (by omega) ⟨h1, h2, h3, h4, h5⟩
  · have hp2 := h5.two_le
    by_cases h2d : 2 ∣ d
    · -- 3 does not divide d
      have h3d : ¬ 3 ∣ d := fun h => h6 (by omega)
      have : d % 3 = 1 ∨ d % 3 = 2 := by omega
      rcases this with h | h
      · have := pre h1 3 (by norm_num) (by omega)
        omega
      · have := pre h2 3 (by norm_num) (by omega)
        omega
    · have := pre h1 2 (by norm_num) (by omega)
      omega

end OMA.S_oeis_a216498

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a216498.main) := by
  intro h
  have hmem : (2668453 : ℕ) ∈ OMA.S_oeis_a216498.S := by
    refine ⟨OMA.S_oeis_a216498.prime_p, ?_⟩
    rintro ⟨d, hd, hlt, h1, h2, h3, h4, h5⟩
    exact OMA.S_oeis_a216498.allD d hd hlt ⟨h1, h2, h3, h4, h5⟩
  have := h.2.2.2 hmem
  omega
