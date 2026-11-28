import OMAReductions.R_Erdos891_erdos_891_variants_case_k_2_R1
import Mathlib

/-! The parity cases follow by factoring the difference of two squares. -/

open Filter
open scoped ArithmeticFunction.omega

namespace Erdos891Parity

private theorem prime_other_of_not_pow {n p : ℕ} (hn : 1 < n)
    (hnot : ∀ e, n ≠ p ^ e) : ∃ q, q.Prime ∧ q ∣ n ∧ q ≠ p := by
  by_contra! h
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn.ne'
  have hpn : p.Prime ∧ p ∣ n := h q hq hqn ▸ ⟨hq, hqn⟩
  have hs : n.primeFactors = {p} := by
    ext t
    simp only [Nat.mem_primeFactors, Finset.mem_singleton]
    exact ⟨fun ht => h t ht.1 ht.2.1, fun ht => ht ▸ ⟨hpn.1, hpn.2, by omega⟩⟩
  exact hnot (n.factorization p) (by simpa [hs] using
    Nat.prod_primeFactors_pow_factorization (by omega : n ≠ 0))

private theorem prime_other_of_not_dvd {n p : ℕ} (hn : 1 < n) (hpn : ¬ p ∣ n) :
    ∃ q, q.Prime ∧ q ∣ n ∧ q ≠ p := by
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd hn.ne'
  exact ⟨q, hq, hqn, fun h => hpn (h ▸ hqn)⟩

private theorem odd_prime_of_mod {n t : ℕ} (h : 2 ^ t < n)
    (hmod : n % 2 ^ (t + 1) ≠ 0) : ∃ q, q.Prime ∧ q ∣ n ∧ q ≠ 2 := by
  apply prime_other_of_not_pow (lt_of_le_of_lt (Nat.one_le_pow _ _ (by decide)) h)
  intro e he
  have ht : t < e := by
    by_contra! hte
    exact (Nat.not_le_of_gt h) (he ▸ Nat.pow_le_pow_right (by decide) hte)
  exact hmod (Nat.mod_eq_zero_of_dvd (he ▸ Nat.pow_dvd_pow 2 ht))

private theorem three_even (r : ℕ) : 3 ^ (r + r) % 8 = 1 := by
  have h : 3 ^ 2 ≡ 1 [MOD 8] := by decide
  have hr := h.pow r
  rwa [← pow_mul, two_mul, one_pow] at hr

private theorem three_odd (r : ℕ) : 3 ^ (r + r + 1) % 8 = 3 := by
  have he : 3 ^ (r + r) ≡ 1 [MOD 8] := three_even r
  have h : 3 ≡ 3 [MOD 8] := rfl
  have hh := he.mul h
  change (3 ^ (r + r) * 3) % 8 = 3 at hh
  rwa [pow_succ]

private theorem square_sub_one (x : ℕ) (hx : 1 ≤ x) :
    x ^ 2 - 1 = (x - 1) * (x + 1) := by
  have h : (x - 1) * (x + 1) + 1 = x ^ 2 := by
    calc
      _ = ((x - 1) + 1) ^ 2 := by
        rw [show x + 1 = (x - 1) + 2 by omega]
        ring
      _ = _ := by rw [Nat.sub_add_cancel hx]
  omega

private theorem odd_neighbors_three_pow (s : ℕ) (hx : 10 ≤ 3 ^ s) :
    (∃ q, q.Prime ∧ q ∣ 3^s - 1 ∧ q ≠ 2) ∧
    (∃ q, q.Prime ∧ q ∣ 3^s + 1 ∧ q ≠ 2) := by
  rcases Nat.even_or_odd s with ⟨r, hr⟩ | ⟨r, hr⟩
  · have he : s = r + r := by omega
    have hm : 3 ^ s % 8 = 1 := he ▸ three_even r
    refine ⟨?_, odd_prime_of_mod (t := 2) (by norm_num; omega) (by norm_num; omega)⟩
    let y := 3 ^ r
    have hy : 4 ≤ y := by
      have hxy : 3 ^ s = y ^ 2 := by rw [he, pow_add, pow_two]
      by_contra! hsmall
      have hsq := Nat.pow_le_pow_left (show y ≤ 3 by omega) 2
      norm_num at hsq
      omega
    have hym : y % 8 = 1 ∨ y % 8 = 3 := by
      dsimp [y]
      rcases Nat.even_or_odd r with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact Or.inl ((show r = j+j by omega) ▸ three_even j)
      · exact Or.inr ((show r = j+j+1 by omega) ▸ three_odd j)
    have hfac : 3 ^ s - 1 = (y - 1) * (y + 1) := by
      rw [he, pow_add, ← pow_two]
      exact square_sub_one y (by omega)
    rw [hfac]
    rcases hym with h | h
    · obtain ⟨q, hq, hd, hne⟩ := odd_prime_of_mod (n := y + 1) (t := 1)
        (by norm_num; omega) (by norm_num; omega)
      exact ⟨q, hq, dvd_mul_of_dvd_right hd _, hne⟩
    · obtain ⟨q, hq, hd, hne⟩ := odd_prime_of_mod (n := y - 1) (t := 1)
        (by norm_num; omega) (by norm_num; omega)
      exact ⟨q, hq, dvd_mul_of_dvd_left hd _, hne⟩
  · have ho : s = r + r + 1 := by omega
    have hm : 3 ^ s % 8 = 3 := ho ▸ three_odd r
    exact ⟨odd_prime_of_mod (t := 2) (by norm_num; omega) (by norm_num; omega),
      odd_prime_of_mod (t := 2) (by norm_num; omega) (by norm_num; omega)⟩

private theorem nonthree_neighbors_two_pow (r : ℕ) (hx : 10 ≤ 2 ^ r) :
    (∃ q, q.Prime ∧ q ∣ 2^r - 1 ∧ q ≠ 3) ∧
    (∃ q, q.Prime ∧ q ∣ 2^r + 1 ∧ q ≠ 3) := by
  have hr : 3 ≤ r := by
    by_contra! h
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show r ≤ 2 by omega)
    norm_num at this
    omega
  have hm : 2 ^ r % 8 = 0 := Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 hr)
  constructor <;> apply prime_other_of_not_pow (by omega) <;> intro e he
  · rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
    · have h := (show e = j+j by omega) ▸ three_even j
      omega
    · have h := (show e = j+j+1 by omega) ▸ three_odd j
      omega
  · rcases Nat.even_or_odd e with ⟨j, hj⟩ | ⟨j, hj⟩
    · let y := 3 ^ j
      have ey : 2 ^ r + 1 = y ^ 2 := by rw [he, show e = j+j by omega, pow_add, pow_two]
      have hy : 4 ≤ y := by
        by_contra! hsmall
        have hsq := Nat.pow_le_pow_left (show y ≤ 3 by omega) 2
        norm_num at hsq
        omega
      have hfac : 2 ^ r = (y - 1) * (y + 1) := by
        rw [← square_sub_one y (by omega), ← ey]
        omega
      have h₁ : y - 1 ∣ 2 ^ r := by rw [hfac]; exact dvd_mul_right _ _
      have h₂ : y + 1 ∣ 2 ^ r := by rw [hfac]; exact dvd_mul_left _ _
      obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h₁
      obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h₂
      have hi' : 2 ≤ i := by
        by_contra! h
        have := Nat.pow_le_pow_right (by decide : 0 < 2) (show i ≤ 1 by omega)
        norm_num at this
        omega
      have hk' : 2 ≤ k := by
        by_contra! h
        have := Nat.pow_le_pow_right (by decide : 0 < 2) (show k ≤ 1 by omega)
        norm_num at this
        omega
      have hm₁ : (y - 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd (hi ▸ Nat.pow_dvd_pow 2 hi')
      have hm₂ : (y + 1) % 4 = 0 := Nat.mod_eq_zero_of_dvd (hk ▸ Nat.pow_dvd_pow 2 hk')
      omega
    · have h := (show e = j+j+1 by omega) ▸ three_odd j
      omega

private theorem enough_factors {c p x : ℕ} (hc : c ≠ 0) (hx : 10 ≤ x)
    (hp : p.Prime) (hpc : p ∣ c)
    (hm : ∃ q, q.Prime ∧ q ∣ x - 1 ∧ q ≠ p)
    (hplus : ∃ q, q.Prime ∧ q ∣ x + 1 ∧ q ≠ p)
    (ha : p = 2 ∨ x % 2 = 0) : 3 ≤ ω (c * x^2 - c) := by
  obtain ⟨q, hq, hqm, hqp⟩ := hm
  obtain ⟨r, hr, hrp, hrne⟩ := hplus
  have hq2 : q ≠ 2 := by
    rcases ha with rfl | he
    · exact hqp
    · rintro rfl
      have := Nat.mod_eq_zero_of_dvd hqm
      omega
  have hqr : q ≠ r := by
    rintro rfl
    have htwo := Nat.dvd_sub hrp hqm
    rw [show x + 1 - (x - 1) = 2 by omega] at htwo
    exact hq2 (le_antisymm (Nat.le_of_dvd (by decide) htwo) hq.two_le)
  rw [show c*x^2 - c = c*(x^2 - 1) by simp [Nat.mul_sub_left_distrib],
    square_sub_one x (by omega)]
  let m := c * ((x - 1) * (x + 1))
  have hn : m ≠ 0 := by
    dsimp [m]
    exact Nat.mul_ne_zero hc (Nat.mul_ne_zero (by omega) (by omega))
  change 3 ≤ m.primeFactors.card
  have hs : ({p, q, r} : Finset ℕ) ⊆ m.primeFactors := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl
    · exact Nat.mem_primeFactors.mpr ⟨hp, dvd_mul_of_dvd_left hpc _, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨hq, dvd_mul_of_dvd_right (dvd_mul_of_dvd_left hqm _) _, hn⟩
    · exact Nat.mem_primeFactors.mpr ⟨hr, dvd_mul_of_dvd_right (dvd_mul_of_dvd_right hrp _) _, hn⟩
  simpa [Ne.symm hqp, Ne.symm hrne, hqr] using Finset.card_le_card hs

private theorem two_case (r s c : ℕ) (hc : c ≠ 0) (h2 : 2 ∣ c)
    (h : 10 ≤ 2^r * 3^s) : 3 ≤ ω (c * (2^r * 3^s)^2 - c) := by
  cases r with
  | zero =>
    simp only [pow_zero, one_mul] at h ⊢
    obtain ⟨hm, hp⟩ := odd_neighbors_three_pow s h
    exact enough_factors hc h Nat.prime_two h2 hm hp (Or.inl rfl)
  | succ r =>
    have he : (2^(r+1)*3^s) % 2 = 0 := Nat.mod_eq_zero_of_dvd
      (dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 (Nat.succ_pos r)) _)
    exact enough_factors hc h Nat.prime_two h2
      (prime_other_of_not_dvd (by omega) (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega))
      (prime_other_of_not_dvd (by omega) (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega))
      (Or.inl rfl)

private theorem three_case (r s : ℕ) (hr : 0 < r)
    (h : 10 ≤ 2^r * 3^s) : 3 ≤ ω (3 * (2^r * 3^s)^2 - 3) := by
  have he : (2^r*3^s) % 2 = 0 := Nat.mod_eq_zero_of_dvd
    (dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hr) _)
  cases s with
  | zero =>
    simp only [pow_zero, mul_one] at h he ⊢
    obtain ⟨hm, hp⟩ := nonthree_neighbors_two_pow r h
    exact enough_factors (by decide) h Nat.prime_three (dvd_refl 3) hm hp (Or.inr he)
  | succ s =>
    have h3 : (2^r*3^(s+1)) % 3 = 0 := Nat.mod_eq_zero_of_dvd
      (dvd_mul_of_dvd_right (Nat.pow_dvd_pow 3 (Nat.succ_pos s)) _)
    exact enough_factors (by decide) h Nat.prime_three (dvd_refl 3)
      (prime_other_of_not_dvd (by omega) (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega))
      (prime_other_of_not_dvd (by omega) (fun hd => by have := Nat.mod_eq_zero_of_dvd hd; omega))
      (Or.inr he)

private theorem root_large {c x : ℕ} (hc : c ≤ 4) (h : 325 ≤ c*x^2) : 10 ≤ x := by
  by_contra! hx
  have hh := Nat.mul_le_mul hc (Nat.pow_le_pow_left (show x ≤ 9 by omega) 2)
  norm_num at hh
  omega

theorem parity :
    ∀ᶠ M : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b → M = 2 ^ a * 3 ^ b →
      (Odd a → Even b → 3 ≤ ω (M - 2)) ∧ (Even a → Odd b → 3 ≤ ω (M - 3)) ∧
        (Even a → Even b → 3 ≤ ω (M - 4)) := by
  filter_upwards [eventually_ge_atTop (325 : ℕ)] with M hM
  intro a b ha hb hMab
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨r, hr⟩ ⟨s, hs⟩
    rw [hMab, show a = r+r+1 by omega, show b = s+s by omega] at hM ⊢
    have he : 2^(r+r+1)*3^(s+s) = 2*(2^r*3^s)^2 := by simp only [pow_add]; ring
    rw [he] at hM ⊢
    exact two_case r s 2 (by decide) (dvd_refl 2) (root_large (by decide) hM)
  · rintro ⟨r, hr⟩ ⟨s, hs⟩
    rw [hMab, show a = r+r by omega, show b = s+s+1 by omega] at hM ⊢
    have he : 2^(r+r)*3^(s+s+1) = 3*(2^r*3^s)^2 := by simp only [pow_add]; ring
    rw [he] at hM ⊢
    exact three_case r s (by omega) (root_large (by decide) hM)
  · rintro ⟨r, hr⟩ ⟨s, hs⟩
    rw [hMab, show a = (r-1)+(r-1)+2 by omega, show b = s+s by omega] at hM ⊢
    have he : 2^((r-1)+(r-1)+2)*3^(s+s) = 4*(2^(r-1)*3^s)^2 := by
      simp only [pow_add]
      ring
    rw [he] at hM ⊢
    exact two_case (r-1) s 4 (by decide) (by decide) (root_large (by decide) hM)

end Erdos891Parity

theorem OMA.solution : OMA.R_Erdos891_erdos_891_variants_case_k_2_R1.H1 := Erdos891Parity.parity