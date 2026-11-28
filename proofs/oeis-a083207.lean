import OMAStatements.S_oeis_a083207
import Mathlib

namespace OMA.A083207Proof
open OMA.S_oeis_a083207


open ArithmeticFunction
open scoped ArithmeticFunction.sigma

lemma sig_mul {a b : ℕ} (h : Nat.Coprime a b) : σ 1 (a * b) = σ 1 a * σ 1 b :=
  isMultiplicative_sigma.map_mul_of_coprime h

lemma sig_pp {p k : ℕ} (hp : p.Prime) : σ 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i :=
  sigma_one_apply_prime_pow hp

lemma zk_nec {n : ℕ} (h : IsZumkeller n) : 2 ∣ σ 1 n ∧ 2 * n ≤ σ 1 n := by
  obtain ⟨hn, S, hS, heq⟩ := h
  have hsum : σ 1 n = ∑ d ∈ S, d + ∑ d ∈ n.divisors \ S, d := by
    rw [sigma_one_apply, ← Finset.sum_sdiff hS]; ring
  have hmem : n ∈ n.divisors := Nat.mem_divisors_self n hn.ne'
  refine ⟨⟨∑ d ∈ S, d, by omega⟩, ?_⟩
  by_cases hnS : n ∈ S
  · have := Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) hnS
    omega
  · have := Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _)
      (Finset.mem_sdiff.2 ⟨hmem, hnS⟩)
    omega

lemma zk_of {n : ℕ} (S : Finset ℕ) (hn : 0 < n) (hS : S ⊆ n.divisors)
    (h : σ 1 n = 2 * ∑ d ∈ S, d) : IsZumkeller n := by
  refine ⟨hn, S, hS, ?_⟩
  have := Finset.sum_sdiff (f := fun d => d) hS
  rw [sigma_one_apply] at h
  omega

lemma not_zk_def {n : ℕ} (h : σ 1 n < 2 * n) : ¬ IsZumkeller n := fun hz => by
  have := (zk_nec hz).2; omega

lemma not_zk_odd {n : ℕ} (h : σ 1 n % 2 = 1) : ¬ IsZumkeller n := fun hz => by
  have := (zk_nec hz).1; omega

lemma s56 : σ 1 273456 = 795212 := by rw [show (273456:ℕ) = 2^4 * (3^4 * 211^1) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s57 : σ 1 273457 = 273458 := by rw [show (273457:ℕ) = 273457^1 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s58 : σ 1 273458 = 416028 := by rw [show (273458:ℕ) = 2^1 * (73^1 * 1873^1) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s59 : σ 1 273459 = 364616 := by rw [show (273459:ℕ) = 3^1 * 91153^1 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s60 : σ 1 273460 = 636804 := by
  rw [show (273460:ℕ) = 2^2 * (5^1 * (11^2 * 113^1)) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s61 : σ 1 273461 = 275424 := by rw [show (273461:ℕ) = 151^1 * 1811^1 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s62 : σ 1 273462 = 663552 := by
  rw [show (273462:ℕ) = 2^1 * (3^1 * (7^1 * (17^1 * 383^1))) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s63 : σ 1 273463 = 278008 := by rw [show (273463:ℕ) = 61^1 * 4483^1 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s64 : σ 1 273464 = 512760 := by rw [show (273464:ℕ) = 2^3 * 34183^1 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s65 : σ 1 273465 = 486720 := by
  rw [show (273465:ℕ) = 3^2 * (5^1 * (59^1 * 103^1)) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s66 : σ 1 273466 = 410202 := by rw [show (273466:ℕ) = 2^1 * 136733^1 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s67 : σ 1 273467 = 296400 := by
  rw [show (273467:ℕ) = 19^1 * (37^1 * 389^1) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma s68 : σ 1 273468 = 687568 := by
  rw [show (273468:ℕ) = 2^2 * (3^1 * (13^1 * 1753^1)) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma t1 : σ 1 397606 = 689472 := by
  rw [show (397606:ℕ) = 2^1 * (11^2 * (31^1 * 53^1)) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma t2 : σ 1 318402 = 846963 := by
  rw [show (318402:ℕ) = 2^1 * (3^2 * (7^2 * 19^2)) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma t3 : σ 1 331776 = 991111 := by
  rw [show (331776:ℕ) = 2^12 * 3^4 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma t4 : σ 1 343784 = 750690 := by
  rw [show (343784:ℕ) = 2^3 * (7^2 * 877^1) by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]
lemma t5 : σ 1 392 = 855 := by
  rw [show (392:ℕ) = 2^3 * 7^2 by norm_num]; (repeat rw [sig_mul]); (repeat rw [sig_pp]); all_goals norm_num [Finset.sum_range_succ]

lemma z56 : IsZumkeller 273456 :=
  zk_of {273456, 91152, 30384, 2532, 81, 1} (by norm_num)
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_divisors]; norm_num)
    (by rw [s56]; rfl)
lemma z60 : IsZumkeller 273460 :=
  zk_of {273460, 27346, 13673, 2486, 1243, 121, 55, 11, 5, 2} (by norm_num)
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_divisors]; norm_num)
    (by rw [s60]; rfl)
lemma z62 : IsZumkeller 273462 :=
  zk_of {273462, 45577, 8043, 2681, 1149, 766, 51, 42, 3, 2} (by norm_num)
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_divisors]; norm_num)
    (by rw [s62]; rfl)
lemma z68 : IsZumkeller 273468 :=
  zk_of {273468, 68367, 1753, 156, 39, 1} (by norm_num)
    (by simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_divisors]; norm_num)
    (by rw [s68]; rfl)

lemma nz4 : ¬ IsZumkeller 343784 := by
  rintro ⟨-, S, hS, heq⟩
  have hsum : ∑ d ∈ S, d + ∑ d ∈ (343784 : ℕ).divisors \ S, d = 750690 := by
    rw [← t4, sigma_one_apply, ← Finset.sum_sdiff hS]; ring
  have hp : Nat.Prime 877 := by norm_num
  set A := S.filter (· ∣ 392) with hA
  set B := S.filter (fun d => ¬ d ∣ 392) with hB
  have hsplit := Finset.sum_filter_add_sum_filter_not S (· ∣ 392) (fun d => d)
  have hAle : ∑ d ∈ A, d ≤ 855 := by
    rw [← t5, sigma_one_apply]
    apply Finset.sum_le_sum_of_subset
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.2 ⟨hd.2, by norm_num⟩
  have hBdvd : 877 ∣ ∑ d ∈ B, d := by
    apply Finset.dvd_sum
    intro d hd
    rw [Finset.mem_filter] at hd
    have hdn : d ∣ 392 * 877 := Nat.dvd_of_mem_divisors (hS hd.1)
    by_contra hc
    have hcop : Nat.Coprime d 877 := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hc))
    exact hd.2 (hcop.dvd_of_dvd_mul_right hdn)
  obtain ⟨k, hk⟩ := hBdvd
  simp only [← hA, ← hB] at hsplit
  omega

noncomputable instance : DecidablePred IsZumkeller := Classical.decPred _

lemma cpos {n : ℕ} (h : IsZumkeller n) : Nat.count IsZumkeller (n + 1) = Nat.count IsZumkeller n + 1 := by
  rw [Nat.count_succ, if_pos h]
lemma cneg {n : ℕ} (h : ¬ IsZumkeller n) : Nat.count IsZumkeller (n + 1) = Nat.count IsZumkeller n := by
  rw [Nat.count_succ, if_neg h, add_zero]

lemma n57 : ¬ IsZumkeller 273457 := not_zk_def (by rw [s57]; norm_num)
lemma n58 : ¬ IsZumkeller 273458 := not_zk_def (by rw [s58]; norm_num)
lemma n59 : ¬ IsZumkeller 273459 := not_zk_def (by rw [s59]; norm_num)
lemma n61 : ¬ IsZumkeller 273461 := not_zk_def (by rw [s61]; norm_num)
lemma n63 : ¬ IsZumkeller 273463 := not_zk_def (by rw [s63]; norm_num)
lemma n64 : ¬ IsZumkeller 273464 := not_zk_def (by rw [s64]; norm_num)
lemma n65 : ¬ IsZumkeller 273465 := not_zk_def (by rw [s65]; norm_num)
lemma n66 : ¬ IsZumkeller 273466 := not_zk_def (by rw [s66]; norm_num)
lemma n67 : ¬ IsZumkeller 273467 := not_zk_def (by rw [s67]; norm_num)

lemma c60 : Nat.count IsZumkeller 273460 = Nat.count IsZumkeller 273456 + 1 := by
  have h1 := cpos z56
  have h2 := cneg n57
  have h3 := cneg n58
  have h4 := cneg n59
  norm_num at h1 h2 h3 h4
  omega
lemma c62 : Nat.count IsZumkeller 273462 = Nat.count IsZumkeller 273456 + 2 := by
  have h1 := cpos z60
  have h2 := cneg n61
  norm_num at h1 h2
  have := c60
  omega
lemma c68 : Nat.count IsZumkeller 273468 = Nat.count IsZumkeller 273456 + 3 := by
  have h1 := cpos z62
  have h2 := cneg n63
  have h3 := cneg n64
  have h4 := cneg n65
  have h5 := cneg n66
  have h6 := cneg n67
  norm_num at h1 h2 h3 h4 h5 h6
  have := c62
  omega

lemma consec_main' : ¬ (∀ i : ℕ, ∃ j, i ≤ j ∧ j < i + 4 ∧
    IsZumkeller (ArithmeticFunction.sigma 1 (Nat.nth IsZumkeller j) / 2)) := by
  intro h
  obtain ⟨j, hij, hj4, hz⟩ := h (Nat.count IsZumkeller 273456)
  have e0 : Nat.nth IsZumkeller (Nat.count IsZumkeller 273456) = 273456 := Nat.nth_count z56
  have e1 := Nat.nth_count z60
  have e2 := Nat.nth_count z62
  have e3 := Nat.nth_count z68
  rw [c60] at e1
  rw [c62] at e2
  rw [c68] at e3
  have : j = Nat.count IsZumkeller 273456 ∨ j = Nat.count IsZumkeller 273456 + 1 ∨
      j = Nat.count IsZumkeller 273456 + 2 ∨ j = Nat.count IsZumkeller 273456 + 3 := by omega
  rcases this with hj | hj | hj | hj
  · rw [hj, e0, s56] at hz
    norm_num at hz
    exact not_zk_def (by rw [t1]; norm_num) hz
  · rw [hj, e1, s60] at hz
    norm_num at hz
    exact not_zk_odd (n := 318402) (by norm_num [t2]) hz
  · rw [hj, e2, s62] at hz
    norm_num at hz
    exact not_zk_odd (n := 331776) (by norm_num [t3]) hz
  · rw [hj, e3, s68] at hz
    norm_num at hz
    exact nz4 hz

theorem disproof_main :
    ¬ ((∀ n : ℕ, 1 ≤ n → ∃ k, n ≤ k ∧ k < n + 12 ∧ IsZumkeller k) ∧
    (∀ i : ℕ, ∃ j, i ≤ j ∧ j < i + 4 ∧ IsZumkeller (ArithmeticFunction.sigma 1 (Nat.nth IsZumkeller j) / 2)) ∧
    (∀ d k : ℕ, 1 < d → d ∣ k → d.divisors.card * ArithmeticFunction.sigma 1 d = k → IsZumkeller k)) :=
  fun h => consec_main' h.2.1

end OMA.A083207Proof

open OMA.A083207Proof in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a083207.main) := disproof_main
