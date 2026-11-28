import OMAStatements.S_mse_886041
import Mathlib

-- Problem: mse-886041, the sum of the largest divisors at most k equals the number of distinct
-- products in the k times m multiplication table (m = k! or m = lcm(1..k)).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Let m be divisible by every d in [1, k]. Then beta(., k) has period m. A number x in
-- [1, k m] is a product i * j with i <= k and j <= m exactly when x <= beta(x, k) * m. Writing
-- x = n + t m with n in [1, m] gives beta(x, k) = beta(n, k), and the condition becomes
-- t < beta(n, k). So the table has exactly sum over n in [1, m] of beta(n, k) entries.

namespace MSE886041

open OMA.S_mse_886041

lemma beta_le (n k : ℕ) : beta n k ≤ k := Nat.findGreatest_le k

lemma le_beta {n k d : ℕ} (hk : d ≤ k) (hd : d ∣ n) : d ≤ beta n k :=
  Nat.le_findGreatest (P := fun d => d ∣ n) hk hd

lemma beta_dvd (n k : ℕ) (hk : 1 ≤ k) : beta n k ∣ n :=
  Nat.findGreatest_spec (P := fun d => d ∣ n) hk (one_dvd n)

lemma one_le_beta (n k : ℕ) (hk : 1 ≤ k) : 1 ≤ beta n k := le_beta hk (one_dvd n)

lemma beta_add (n k m : ℕ) (hk : 1 ≤ k) (hm : ∀ d, 1 ≤ d → d ≤ k → d ∣ m) :
    beta (n + m) k = beta n k := by
  apply le_antisymm
  · apply le_beta (beta_le _ _)
    have h1 := beta_dvd (n + m) k hk
    have h2 := hm _ (one_le_beta (n + m) k hk) (beta_le _ _)
    exact (Nat.dvd_add_left h2).mp h1
  · apply le_beta (beta_le _ _)
    have h1 := beta_dvd n k hk
    have h2 := hm _ (one_le_beta n k hk) (beta_le _ _)
    exact (Nat.dvd_add_left h2).mpr h1

lemma beta_add_mul (n k m t : ℕ) (hk : 1 ≤ k) (hm : ∀ d, 1 ≤ d → d ≤ k → d ∣ m) :
    beta (n + t * m) k = beta n k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have e : n + (t + 1) * m = (n + t * m) + m := by ring
    rw [e, beta_add _ _ _ hk hm, ih]

lemma table_eq (k m : ℕ) (hk : 1 ≤ k) :
    table k m = (Finset.Icc 1 (k * m)).filter (fun x => x ≤ beta x k * m) := by
  ext x
  unfold table
  simp only [Finset.mem_image, Finset.mem_product, Finset.mem_Icc, Finset.mem_filter,
    Prod.exists]
  constructor
  · rintro ⟨i, j, ⟨⟨hi1, hik⟩, hj1, hjm⟩, rfl⟩
    have hb : i ≤ beta (i * j) k := le_beta hik (dvd_mul_right i j)
    exact ⟨⟨Nat.mul_pos hi1 hj1, Nat.mul_le_mul hik hjm⟩, Nat.mul_le_mul hb hjm⟩
  · rintro ⟨⟨hx1, _⟩, hxb⟩
    have hb1 := one_le_beta x k hk
    have hbd := beta_dvd x k hk
    exact ⟨beta x k, x / beta x k,
      ⟨⟨hb1, beta_le x k⟩, Nat.div_pos (Nat.le_of_dvd hx1 hbd) hb1, Nat.div_le_of_le_mul hxb⟩,
      Nat.mul_div_cancel' hbd⟩

theorem general (k m : ℕ) (hk : 1 ≤ k) (hm : ∀ d, 1 ≤ d → d ≤ k → d ∣ m) :
    divisorSum k m = (table k m).card := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [divisorSum, table]
  rw [table_eq k m hk]
  have hS : divisorSum k m
      = ((Finset.range m).sigma (fun r => Finset.range (beta (r + 1) k))).card := by
    rw [Finset.card_sigma]
    simp [divisorSum]
  rw [hS]
  apply Finset.card_bij (fun (x : Σ _ : ℕ, ℕ) _ => x.1 + 1 + x.2 * m)
  · rintro ⟨r, t⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨hr, ht⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [beta_add_mul _ _ _ _ hk hm]
    have hbk := beta_le (r + 1) k
    have h1 : (t + 1) * m ≤ beta (r + 1) k * m := Nat.mul_le_mul_right _ ht
    have h2 : beta (r + 1) k * m ≤ k * m := Nat.mul_le_mul_right _ hbk
    have h3 : (t + 1) * m = t * m + m := by ring
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨r1, t1⟩ hx1 ⟨r2, t2⟩ hx2 heq
    simp only [Finset.mem_sigma, Finset.mem_range] at hx1 hx2
    simp only at heq
    obtain ⟨hr1, _⟩ := hx1
    obtain ⟨hr2, _⟩ := hx2
    have key : t1 = t2 := by
      rcases lt_trichotomy t1 t2 with h | h | h
      · exfalso
        have h1 : (t1 + 1) * m ≤ t2 * m := Nat.mul_le_mul_right _ h
        have h3 : (t1 + 1) * m = t1 * m + m := by ring
        omega
      · exact h
      · exfalso
        have h1 : (t2 + 1) * m ≤ t1 * m := Nat.mul_le_mul_right _ h
        have h3 : (t2 + 1) * m = t2 * m + m := by ring
        omega
    subst key
    have hr : r1 = r2 := by omega
    subst hr
    rfl
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, _⟩, hxb⟩ := hx
    obtain ⟨q, hq⟩ : ∃ q, q = (x - 1) / m := ⟨_, rfl⟩
    have h1 : q * m ≤ x - 1 := by
      rw [hq]
      exact Nat.div_mul_le_self _ _
    have h2 : x - 1 < (q + 1) * m := by
      rw [hq, mul_comm]
      exact Nat.lt_mul_div_succ _ hm0
    have h3 : (q + 1) * m = q * m + m := by ring
    have hxeq : x = (x - 1 - q * m) + 1 + q * m := by omega
    have hb : beta (x - 1 - q * m + 1) k = beta x k := by
      conv_rhs => rw [hxeq]
      rw [beta_add_mul _ _ _ _ hk hm]
    refine ⟨⟨x - 1 - q * m, q⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [hb]
      have h4 : q * m < beta x k * m := by omega
      exact Nat.lt_of_mul_lt_mul_right h4
    · simp only
      omega

theorem main_proof : ∀ (k : ℕ), 0 < k →
    divisorSum k k.factorial = (table k k.factorial).card ∧
    divisorSum k (period k) = (table k (period k)).card := by
  intro k hk
  refine ⟨general k _ hk fun d hd1 hdk => Nat.dvd_factorial hd1 hdk,
    general k _ hk fun d hd1 hdk => ?_⟩
  unfold period
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hd1, hdk⟩)

end MSE886041

theorem OMA.solution : type_of% @OMA.S_mse_886041.main := MSE886041.main_proof
