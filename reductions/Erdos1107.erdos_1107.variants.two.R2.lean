import FormalConjectures.ErdosProblems.«1107»

-- Reduction Erdos1107.erdos_1107.variants.two.R2 of Erdős Problem 1107 — two
-- Credit: @mucoucah
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
-- H1 is Legendre's three-square theorem. H2 is Heath-Brown's theorem restricted to n = 7 mod 8.
-- Every other large n is handled here: non-exceptional n are three squares, and
-- n = 4^a (8b+7) with a >= 1 is (2x)^2 + (2y)^2 + 2^3 z^2 via Legendre applied to n/2.

namespace OMA.R_Erdos1107_erdos_1107_variants_two_R2

open Filter

-- Legendre's three-square theorem (sufficiency direction).
def H1 : Prop :=
  ∀ n : ℕ, (∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)) → ∃ x y z : ℕ, x ^ 2 + y ^ 2 + z ^ 2 = n

-- Heath-Brown: every large n = 7 mod 8 is a sum of three squarefull numbers.
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, n % 8 = 7 → ∃ a b c : ℕ, (∀ p ∈ a.primeFactors, p ^ 2 ∣ a) ∧
    (∀ p ∈ b.primeFactors, p ^ 2 ∣ b) ∧ (∀ p ∈ c.primeFactors, p ^ 2 ∣ c) ∧ a + b + c = n

lemma full_sq (x : ℕ) : Nat.Full 2 (x ^ 2) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  exact pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2

lemma full_mul {a b : ℕ} (ha : Nat.Full 2 a) (hb : Nat.Full 2 b) : Nat.Full 2 (a * b) := by
  intro p hp
  have h := Nat.mem_primeFactors.mp hp
  rcases a.eq_zero_or_pos with rfl | ha0
  · simp
  rcases b.eq_zero_or_pos with rfl | hb0
  · simp
  rcases h.1.dvd_mul.mp h.2.1 with hd | hd
  · exact dvd_mul_of_dvd_left (ha p (Nat.mem_primeFactors.mpr ⟨h.1, hd, ha0.ne'⟩)) _
  · exact dvd_mul_of_dvd_right (hb p (Nat.mem_primeFactors.mpr ⟨h.1, hd, hb0.ne'⟩)) _

lemma full_cube_mul_sq (q x : ℕ) : Nat.Full 2 (q ^ 3 * x ^ 2) := by
  have hq : Nat.Full 2 (q ^ 3) := by
    intro p hp
    have h := Nat.mem_primeFactors.mp hp
    exact (pow_dvd_pow_of_dvd (h.1.dvd_of_dvd_pow h.2.1) 2).trans (pow_dvd_pow q (by norm_num))
  exact full_mul hq (full_sq x)

lemma of_three {a b c n : ℕ} (ha : Nat.Full 2 a) (hb : Nat.Full 2 b) (hc : Nat.Full 2 c)
    (h : a + b + c = n) : Erdos1107.SumOfRPowerful 2 n := by
  refine ⟨[a, b, c], by simp, ?_, ?_⟩
  · intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl <;> assumption
  · simp [← h, add_assoc]

-- 2 * 4^k * m (m odd) is never of the form 4^c (8d+7): odd versus even 2-adic valuation.
lemma not_exc (k m : ℕ) (hm : m % 2 = 1) : ∀ c d : ℕ, 2 * 4 ^ k * m ≠ 4 ^ c * (8 * d + 7) := by
  induction k with
  | zero =>
    intro c d h
    rcases c with _ | c
    · simp only [pow_zero, mul_one, one_mul] at h; omega
    · have h' : 2 * m = 4 * (4 ^ c * (8 * d + 7)) := by rw [pow_succ] at h; linarith
      omega
  | succ k ih =>
    intro c d h
    rcases c with _ | c
    · have h' : 2 * (4 * (4 ^ k * m)) = 8 * d + 7 := by rw [pow_succ] at h; linarith
      omega
    · apply ih c d
      have h' : 4 * (2 * 4 ^ k * m) = 4 * (4 ^ c * (8 * d + 7)) := by
        rw [pow_succ, pow_succ] at h; linarith
      omega

theorem main : H1 → H2 → type_of% @Erdos1107.erdos_1107.variants.two := by
  intro legendre hb
  filter_upwards [hb] with n hn
  by_cases hexc : ∀ a b : ℕ, n ≠ 4 ^ a * (8 * b + 7)
  · obtain ⟨x, y, z, h⟩ := legendre n hexc
    exact of_three (full_sq x) (full_sq y) (full_sq z) h
  push Not at hexc
  obtain ⟨a, b, rfl⟩ := hexc
  rcases a with _ | a
  · obtain ⟨u, v, w, hu, hv, hw, h⟩ := hn (by simp only [pow_zero, one_mul]; omega)
    exact of_three hu hv hw h
  · obtain ⟨x, y, z, h⟩ := legendre (2 * 4 ^ a * (8 * b + 7)) (not_exc a _ (by omega))
    -- two of x, y, z have the same parity
    have key : ∃ u v w : ℕ, u ^ 2 + v ^ 2 + 2 * w ^ 2 = 4 ^ a * (8 * b + 7) := by
      have hpar : ∀ s t r : ℕ, s ^ 2 + t ^ 2 + r ^ 2 = 2 * 4 ^ a * (8 * b + 7) → s % 2 = t % 2 →
          ∃ u v w : ℕ, u ^ 2 + v ^ 2 + 2 * w ^ 2 = 4 ^ a * (8 * b + 7) := by
        intro s t r hst hp
        wlog hle : t ≤ s generalizing s t
        · exact this t s (by linarith) hp.symm (by omega)
        obtain ⟨e, he⟩ : ∃ e, s + t = 2 * e := ⟨(s + t) / 2, by omega⟩
        obtain ⟨f, hf⟩ : ∃ f, s - t = 2 * f := ⟨(s - t) / 2, by omega⟩
        have hs : s = e + f := by omega
        have ht : t = e - f := by omega
        have hfe : f ≤ e := by omega
        obtain ⟨g, rfl⟩ : ∃ g, e = f + g := ⟨e - f, by omega⟩
        subst hs; rw [ht] at hst
        simp only [Nat.add_sub_cancel_left] at hst
        -- (2f+g)^2 + g^2 + r^2 = 2N, so r is even
        have hr : r % 2 = 0 := by
          have h2 : (r ^ 2) % 2 = 0 := by
            have : (f + g + f) ^ 2 + g ^ 2 + r ^ 2 = 2 * ((f + g) ^ 2 + f ^ 2) + r ^ 2 := by ring
            have hh : 2 * ((f + g) ^ 2 + f ^ 2) + r ^ 2 = 2 * (4 ^ a * (8 * b + 7)) := by
              rw [← this, ← mul_assoc]; convert hst using 2
            omega
          rcases Nat.even_or_odd r with ⟨k, hk⟩ | ⟨k, hk⟩
          · omega
          · subst hk; ring_nf at h2; omega
        obtain ⟨r', rfl⟩ : ∃ r', r = 2 * r' := ⟨r / 2, by omega⟩
        refine ⟨f + g, f, r', ?_⟩
        have : 2 * ((f + g) ^ 2 + f ^ 2 + 2 * r' ^ 2) = 2 * (4 ^ a * (8 * b + 7)) := by
          rw [← mul_assoc, ← hst]; ring
        omega
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
      rcases Nat.mod_two_eq_zero_or_one z with hz | hz
      all_goals first
        | exact hpar x y z h (by omega)
        | exact hpar x z y (by linarith) (by omega)
        | exact hpar y z x (by linarith) (by omega)
    obtain ⟨u, v, w, hk⟩ := key
    refine of_three (full_cube_mul_sq 2 w) (full_sq (2 * u)) (full_sq (2 * v)) ?_
    rw [pow_succ 4 a, mul_right_comm, ← hk]; ring

end OMA.R_Erdos1107_erdos_1107_variants_two_R2
