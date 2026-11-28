import OMAStatements.S_mse_2259412
import Mathlib

-- Problem: mse-2259412, infinitely many primes divide some 1! + 2! + ... + n!.
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Suppose only the primes of a finite set P divide some a(n), and let M be their product.
-- For m > n one has a(m) = a(n) + (n+1)! * (1 + (n+2) * V), so for a prime p dividing n + 2
-- the difference a(m) - a(n) has the same p-adic valuation as (n+1)!, which is at most n + 1.
-- Hence, for each p in P, as soon as p^(n0+2) divides a(n0) for one n0 with M | n0 + 2, the
-- power p^(n0+2) divides no later a(m). So for all large n with M | n + 2, no p^(n+2) with p
-- in P divides a(n), which forces a(n) to divide M^(n+1). But a(n) >= n! > M^(n+1) for large n.

namespace MSE2259412

open OMA.S_mse_2259412

lemma a_succ (n : ℕ) : a (n + 1) = a n + (n + 1).factorial := by
  unfold a
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma le_a (n : ℕ) (hn : 1 ≤ n) : n.factorial ≤ a n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [a_succ]
  omega

lemma a_diff (n : ℕ) (d : ℕ) :
    ∃ V : ℕ, a (n + 1 + d) = a n + (n + 1).factorial * (1 + (n + 2) * V) := by
  induction d with
  | zero => exact ⟨0, by simp [a_succ]⟩
  | succ d ih =>
    obtain ⟨V, hV⟩ := ih
    obtain ⟨W, hW⟩ : (n + 2).factorial ∣ (n + 1 + d + 1).factorial :=
      Nat.factorial_dvd_factorial (by omega)
    have h2 : (n + 2).factorial = (n + 2) * (n + 1).factorial := Nat.factorial_succ (n + 1)
    refine ⟨V + W, ?_⟩
    have e : n + 1 + (d + 1) = (n + 1 + d) + 1 := by omega
    rw [e, a_succ, hV, hW, h2]
    ring

lemma not_pow_dvd_factorial {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ¬ p ^ (N + 1) ∣ N.factorial := by
  intro h
  have h1 := (hp.pow_dvd_iff_le_factorization (Nat.factorial_ne_zero N)).mp h
  have h2 := Nat.factorization_factorial_le_div_pred hp N
  have h3 : N / (p - 1) ≤ N := Nat.div_le_self _ _
  omega

lemma bound_exists (M p : ℕ) (hp : p.Prime) (hpM : p ∣ M) :
    ∃ B : ℕ, ∀ n : ℕ, B ≤ n → M ∣ n + 2 → ¬ p ^ (n + 2) ∣ a n := by
  by_cases h : ∃ n0, M ∣ n0 + 2 ∧ p ^ (n0 + 2) ∣ a n0
  · obtain ⟨n0, hM, hdiv⟩ := h
    refine ⟨n0 + 1, fun n hn _ hcon => ?_⟩
    obtain ⟨d, rfl⟩ : ∃ d, n = n0 + 1 + d := ⟨n - (n0 + 1), by omega⟩
    obtain ⟨V, hV⟩ := a_diff n0 d
    have h1 : p ^ (n0 + 2) ∣ a (n0 + 1 + d) := (pow_dvd_pow p (by omega)).trans hcon
    rw [hV] at h1
    have h2 : p ^ (n0 + 2) ∣ (n0 + 1).factorial * (1 + (n0 + 2) * V) :=
      (Nat.dvd_add_right hdiv).mp h1
    have hpn : p ∣ n0 + 2 := hpM.trans hM
    have hcop : Nat.Coprime (p ^ (n0 + 2)) (1 + (n0 + 2) * V) := by
      apply Nat.Coprime.pow_left
      rw [hp.coprime_iff_not_dvd]
      intro h3
      have h4 : p ∣ (n0 + 2) * V := Dvd.dvd.mul_right hpn V
      have h5 : p ∣ 1 := (Nat.dvd_add_left h4).mp h3
      exact hp.one_lt.ne' (Nat.dvd_one.mp h5)
    have h6 : p ^ (n0 + 2) ∣ (n0 + 1).factorial := hcop.dvd_of_dvd_mul_right h2
    exact not_pow_dvd_factorial hp (n0 + 1) h6
  · exact ⟨0, fun n _ hM hcon => h ⟨n, hM, hcon⟩⟩

theorem main_proof : {p : ℕ | p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ p ∣ a n}.Infinite := by
  intro hfin
  have hPmem : ∀ p, p ∈ hfin.toFinset ↔ (p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ p ∣ a n) := by
    intro p
    rw [Set.Finite.mem_toFinset]
    rfl
  generalize hfin.toFinset = P at hPmem
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => ((hPmem p).mp hp).1
  have hMpos : 0 < ∏ p ∈ P, p := Finset.prod_pos (fun p hp => (hprime p hp).pos)
  have hB : ∀ p ∈ P, ∃ B : ℕ, ∀ n : ℕ, B ≤ n → (∏ q ∈ P, q) ∣ n + 2 → ¬ p ^ (n + 2) ∣ a n :=
    fun p hp => bound_exists _ p (hprime p hp) (Finset.dvd_prod_of_mem _ hp)
  choose! f hf using hB
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (Nat.eventually_pow_lt_factorial_sub (∏ p ∈ P, p) 1)
  obtain ⟨n, hn2, hnB, hnN, hn1⟩ : ∃ n : ℕ, n + 2 = (P.sup f + N0 + 3) * (∏ p ∈ P, p) ∧
      P.sup f ≤ n ∧ N0 ≤ n + 1 ∧ 1 ≤ n := by
    have htM : P.sup f + N0 + 3 ≤ (P.sup f + N0 + 3) * (∏ p ∈ P, p) :=
      Nat.le_mul_of_pos_right _ hMpos
    refine ⟨(P.sup f + N0 + 3) * (∏ p ∈ P, p) - 2, ?_, ?_, ?_, ?_⟩ <;> omega
  have hMn : (∏ p ∈ P, p) ∣ n + 2 := by
    rw [hn2]
    exact dvd_mul_left _ _
  have hdvd : a n ∣ ∏ p ∈ P, p ^ (n + 1) := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro p k hp hpk
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hpa : p ∣ a n := (dvd_pow_self p hk.ne').trans hpk
      have hpP : p ∈ P := (hPmem p).mpr ⟨hp, n, hn1, hpa⟩
      have hk' : k ≤ n + 1 := by
        by_contra hcon
        exact hf p hpP n ((Finset.le_sup hpP).trans hnB) hMn
          ((pow_dvd_pow p (by omega)).trans hpk)
      exact (pow_dvd_pow p hk').trans (Finset.dvd_prod_of_mem (fun q => q ^ (n + 1)) hpP)
  have hle : a n ≤ (∏ p ∈ P, p) ^ (n + 1) := by
    rw [← Finset.prod_pow]
    exact Nat.le_of_dvd (Finset.prod_pos (fun p hp => pow_pos (hprime p hp).pos _)) hdvd
  have hlt : (∏ p ∈ P, p) ^ (n + 1) < n.factorial := by
    have h := hN0 (n + 1) hnN
    simpa using h
  have hge := le_a n hn1
  omega

end MSE2259412

theorem OMA.solution : type_of% @OMA.S_mse_2259412.main := MSE2259412.main_proof
