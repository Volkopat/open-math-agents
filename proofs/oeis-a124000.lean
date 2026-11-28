import OMAStatements.S_oeis_a124000
import Mathlib.Tactic.Simproc.Factors

-- Problem: A124000: Semiprimes in A006987(n), or semiprime binomial coefficients C(n,k), 2 <= k <= n-2.
-- Upstream: formal-conjectures statements/oeis-a124000.lean:0 (declaration OMA.S_oeis_a124000.main)
-- Credit: @nerotulip90 (the owner of the agent is credited as the solver)
-- Proof: every prime power dividing C(n,k) is at most n (Mathlib's pow_factorization_choose_le), so a
-- semiprime C(n,k) is at most n^2. For 3 <= k <= n-3 we have C(n,k) >= C(n,3) > n^2 once n >= 9,
-- leaving finitely many cases (only C(7,3) = 35 is a semiprime). For k = 2 (or n-2),
-- C(n,2) = a(2a-1) or a(2a+1); counting prime factors with multiplicity forces both factors prime.

namespace OMA.W2_a124000

/-- Number of prime factors with multiplicity. -/
abbrev Ω (m : ℕ) : ℕ := m.primeFactorsList.length

lemma Ω_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : Ω (a * b) = Ω a + Ω b := by
  simp only [Ω, (Nat.perm_primeFactorsList_mul ha hb).length_eq, List.length_append]

lemma one_le_Ω {x : ℕ} (hx : 2 ≤ x) : 1 ≤ Ω x := by
  unfold Ω
  rcases h : x.primeFactorsList with _ | ⟨r, l⟩
  · rw [Nat.primeFactorsList_eq_nil] at h; omega
  · simp

lemma prime_of_Ω {x : ℕ} (hx : Ω x = 1) : x.Prime := by
  unfold Ω at hx
  obtain ⟨r, hr⟩ := List.length_eq_one_iff.mp hx
  have h0 : x ≠ 0 := by rintro rfl; simp at hr
  have hp : r.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hr]; simp)
  have := Nat.prod_primeFactorsList h0
  rw [hr] at this; simp at this; rw [← this]; exact hp

/-- A number with two prime factors that is a binomial coefficient `C(n, k)` is at most `n ^ 2`. -/
lemma le_sq {n k : ℕ} (hn : 0 < n) (h : Ω (n.choose k) = 2) : n.choose k ≤ n ^ 2 := by
  unfold Ω at h
  obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp h
  have h0 : n.choose k ≠ 0 := by intro h0; rw [h0] at hpq; simp at hpq
  have hp : p.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hpq]; simp)
  have hq : q.Prime := Nat.prime_of_mem_primeFactorsList (by rw [hpq]; simp)
  have hprod := Nat.prod_primeFactorsList h0
  rw [hpq] at hprod; simp at hprod
  have key : ∀ r : ℕ, r.Prime → r ∣ n.choose k → r ≤ n := by
    intro r hr hd
    have h1 : 1 ≤ (n.choose k).factorization r :=
      (hr.dvd_iff_one_le_factorization h0).mp hd
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ (n.choose k).factorization r := Nat.pow_le_pow_right hr.pos h1
      _ ≤ n := Nat.pow_factorization_choose_le hn
  have hp' := key p hp ⟨q, hprod.symm⟩
  have hq' := key q hq ⟨p, by rw [← hprod]; ring⟩
  rw [← hprod, sq]; exact Nat.mul_le_mul hp' hq'

lemma choose_three_le {n k : ℕ} (h3 : 3 ≤ k) (hk : k + 3 ≤ n) : n.choose 3 ≤ n.choose k := by
  have aux : ∀ j, 3 + j ≤ n / 2 → n.choose 3 ≤ n.choose (3 + j) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  by_cases hk2 : k ≤ n / 2
  · have := aux (k - 3) (by omega)
    rwa [show 3 + (k - 3) = k by omega] at this
  · rw [← Nat.choose_symm (by omega : k ≤ n)]
    have := aux (n - k - 3) (by omega)
    rwa [show 3 + (n - k - 3) = n - k by omega] at this

/-- The case `k = 2`: `C(n, 2)` with two prime factors is `r (2 r ± 1)` for a prime `r`. -/
lemma two_case {n : ℕ} (hn : 4 ≤ n) (h : Ω (n.choose 2) = 2) :
    ∃ r : ℕ, r.Prime ∧ (n.choose 2 = r * (2 * r + 1) ∨ n.choose 2 = r * (2 * r - 1)) := by
  rw [Nat.choose_two_right] at h ⊢
  obtain ⟨a, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e : 2 * a * (2 * a - 1) / 2 = a * (2 * a - 1) := by
      rw [show 2 * a * (2 * a - 1) = a * (2 * a - 1) * 2 by ring]
      exact Nat.mul_div_cancel _ two_pos
    rw [e] at h ⊢
    rw [Ω_mul (by omega) (by omega)] at h
    have h1 := one_le_Ω (x := a) (by omega)
    have h2 := one_le_Ω (x := 2 * a - 1) (by omega)
    exact ⟨a, prime_of_Ω (by omega), Or.inr rfl⟩
  · have e : (2 * a + 1) * (2 * a + 1 - 1) / 2 = a * (2 * a + 1) := by
      rw [show 2 * a + 1 - 1 = 2 * a by omega,
        show (2 * a + 1) * (2 * a) = a * (2 * a + 1) * 2 by ring]
      exact Nat.mul_div_cancel _ two_pos
    rw [e] at h ⊢
    rw [Ω_mul (by omega) (by omega)] at h
    have h1 := one_le_Ω (x := a) (by omega)
    have h2 := one_le_Ω (x := 2 * a + 1) (by omega)
    exact ⟨a, prime_of_Ω (by omega), Or.inl rfl⟩

lemma conclude {m : ℕ} (h : ∃ r : ℕ, r.Prime ∧ (m = r * (2 * r + 1) ∨ m = r * (2 * r - 1))) :
    (m ≠ 6 → m ≠ 10 → Odd m) ∧ (m ≠ 35 → ∃ p : ℕ, p.Prime ∧
        (m = p * (2 * p + 1) ∨ m = p * (2 * p - 1))) := by
  refine ⟨fun h6 h10 => ?_, fun _ => h⟩
  obtain ⟨r, hr, hm | hm⟩ := h
  · rcases hr.eq_two_or_odd' with rfl | ho
    · exact absurd hm (by simpa using h10)
    · rw [hm]; exact ho.mul (by obtain ⟨t, rfl⟩ := ho; exact ⟨2 * t + 1, by ring⟩)
  · rcases hr.eq_two_or_odd' with rfl | ho
    · exact absurd hm (by simpa using h6)
    · rw [hm]; refine ho.mul ?_
      obtain ⟨t, rfl⟩ := ho; exact ⟨2 * t, by omega⟩

end OMA.W2_a124000

open OMA.W2_a124000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a124000.main := by
  intro n k hk hkn hΩ
  have hΩ' : Ω (n.choose k) = 2 := hΩ
  by_cases h2 : k = 2 ∨ k = n - 2
  · have e : n.choose k = n.choose 2 := by
      rcases h2 with rfl | rfl
      · rfl
      · exact Nat.choose_symm (by omega)
    rw [e] at hΩ' ⊢
    exact conclude (two_case (by omega) hΩ')
  · push Not at h2
    have h3 := choose_three_le (n := n) (k := k) (by omega) (by omega)
    have hsq := le_sq (by omega) hΩ'
    have hn : n ≤ 8 := by
      by_contra hn
      push Not at hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hd := Nat.descFactorial_eq_factorial_mul_choose (m + 3) 3
      simp [Nat.descFactorial, Nat.factorial] at hd
      nlinarith
    have hk8 : k ≤ 8 := by omega
    obtain ⟨p, q, hpq⟩ := List.length_eq_two.mp hΩ
    interval_cases n <;> interval_cases k <;> (try omega) <;> simp [Nat.choose, Nat.primeFactorsList_ofNat] at hpq ⊢ <;> decide
