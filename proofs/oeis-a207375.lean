import OMAStatements.S_oeis_a207375
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

namespace OMA.P_oeis_a207375

open OMA.S_oeis_a207375

private lemma lowerCentral_mem {n : ℕ} (hn : 1 ≤ n) :
    lowerCentral n ∈ n.divisors.filter (fun d => d * d ≤ n) := by
  have hne : (n.divisors.filter (fun d => d * d ≤ n)).Nonempty :=
    ⟨1, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩, by omega⟩⟩
  obtain ⟨m, hm⟩ := Finset.max_of_nonempty hne
  have hmem := Finset.mem_of_max hm
  unfold lowerCentral
  rw [hm]
  exact hmem

private lemma upperCentral_mem {n : ℕ} (hn : 1 ≤ n) :
    upperCentral n ∈ n.divisors.filter (fun d => n ≤ d * d) := by
  have hne : (n.divisors.filter (fun d => n ≤ d * d)).Nonempty :=
    ⟨n, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩, by nlinarith⟩⟩
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
  have hmem := Finset.mem_of_min hm
  unfold upperCentral
  rw [hm]
  exact hmem

private lemma upperCentral_le {n d : ℕ} (hn : 1 ≤ n) (hd : d ∣ n) (hsq : n ≤ d * d) :
    upperCentral n ≤ d := by
  have hmem : d ∈ n.divisors.filter (fun x => n ≤ x * x) :=
    Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, by omega⟩, hsq⟩
  obtain ⟨m, hm⟩ := Finset.min_of_nonempty ⟨d, hmem⟩
  have hle : m ≤ d := Finset.min_le_of_eq hmem hm
  unfold upperCentral
  rw [hm]
  exact hle

private lemma upperCentral_le_self {n : ℕ} (hn : 1 ≤ n) : upperCentral n ≤ n :=
  upperCentral_le hn (dvd_refl n) (by nlinarith)

private lemma lowerCentral_le_upperCentral {n : ℕ} (hn : 1 ≤ n) :
    lowerCentral n ≤ upperCentral n := by
  have h1 := (Finset.mem_filter.mp (lowerCentral_mem hn)).2
  have h2 := (Finset.mem_filter.mp (upperCentral_mem hn)).2
  nlinarith

private lemma upperCentral_one : upperCentral 1 = 1 := by
  have hmem := upperCentral_mem (by omega : 1 ≤ 1)
  have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hmem).1).1
  exact Nat.eq_one_of_dvd_one hdvd

private lemma upperCentral_prime {p : ℕ} (hp : p.Prime) : upperCentral p = p := by
  have hmem := upperCentral_mem hp.one_lt.le
  have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hmem).1).1
  have hsq := (Finset.mem_filter.mp hmem).2
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp_eq
  · rw [h1] at hsq; have := hp.two_le; omega
  · exact hp_eq

private lemma lowerCentral_prime {p : ℕ} (hp : p.Prime) : lowerCentral p = 1 := by
  have hmem := lowerCentral_mem hp.one_lt.le
  have hdvd := (Nat.mem_divisors.mp (Finset.mem_filter.mp hmem).1).1
  have hsq := (Finset.mem_filter.mp hmem).2
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hp_eq
  · exact h1
  · rw [hp_eq] at hsq; have := hp.two_le; nlinarith

private lemma upperCentral_composite_le_half {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) :
    upperCentral n ≤ n / 2 := by
  set p := n.minFac
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpd : p ∣ n := Nat.minFac_dvd n
  have hpsq : p * p ≤ n := by simpa [sq] using Nat.minFac_sq_le_self (by omega) hnp
  set d := n / p
  have hpd_eq : p * d = n := Nat.mul_div_cancel' hpd
  have hd_dvd : d ∣ n := ⟨p, by rw [mul_comm, hpd_eq]⟩
  have hp_le_d : p ≤ d := by nlinarith
  have hd_sq : n ≤ d * d := by nlinarith
  have hle : upperCentral n ≤ d := upperCentral_le (by omega) hd_dvd hd_sq
  have hp2 : 2 ≤ p := hp.two_le
  have hd_half : d ≤ n / 2 := by
    have : 2 * d ≤ n := by nlinarith
    omega
  omega

private lemma exists_prime_gt_upperCentral {n : ℕ} (hn : 2 ≤ n) (hnp : ¬ n.Prime) :
    ∃ p : ℕ, 1 ≤ p ∧ p < n ∧ upperCentral n < upperCentral p := by
  have hle_half : upperCentral n ≤ n / 2 := upperCentral_composite_le_half hn hnp
  have hn4 : 4 ≤ n := by
    by_contra hlt
    interval_cases n
    · exact hnp Nat.prime_two
    · exact hnp Nat.prime_three
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (n / 2) (by omega)
  have hpn : p < n := by
    have hple : p ≤ n := by omega
    rcases lt_or_eq_of_le hple with h | rfl
    · exact h
    · exact absurd hp hnp
  refine ⟨p, hp.one_lt.le, hpn, ?_⟩
  rw [upperCentral_prime hp]
  omega

private lemma prove_main :
    (∀ n : ℕ, 1 ≤ n → lowerCentral n ≤ upperCentral n) ∧
    (∀ n : ℕ, 2 ≤ n → ∃ m : ℕ, 1 ≤ m ∧ m < n ∧ lowerCentral n ≤ upperCentral m) ∧
    (∀ n : ℕ, 1 ≤ n →
      ((∀ m : ℕ, 1 ≤ m → m < n → upperCentral m < upperCentral n) ↔ (n = 1 ∨ n.Prime))) := by
  refine ⟨fun n hn => lowerCentral_le_upperCentral hn, ?_, ?_⟩
  · intro n hn
    by_cases hp : n.Prime
    · refine ⟨1, le_rfl, hp.one_lt, ?_⟩
      rw [lowerCentral_prime hp, upperCentral_one]
    · obtain ⟨p, hp1, hpn, hlt⟩ := exists_prime_gt_upperCentral hn hp
      exact ⟨p, hp1, hpn, le_trans (lowerCentral_le_upperCentral (by omega)) hlt.le⟩
  · intro n hn
    constructor
    · intro hrec
      by_cases hn1 : n = 1
      · exact Or.inl hn1
      · right
        by_contra hnp
        obtain ⟨p, hp1, hpn, hlt⟩ := exists_prime_gt_upperCentral (by omega) hnp
        have := hrec p hp1 hpn
        omega
    · rintro (rfl | hp)
      · intro m hm1 hmlt; omega
      · intro m hm1 hmlt
        rw [upperCentral_prime hp]
        exact lt_of_le_of_lt (upperCentral_le_self hm1) hmlt

end OMA.P_oeis_a207375

theorem OMA.solution : type_of% @OMA.S_oeis_a207375.main :=
  OMA.P_oeis_a207375.prove_main
