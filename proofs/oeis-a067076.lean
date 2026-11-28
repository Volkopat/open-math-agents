import OMAStatements.S_oeis_a067076
import Mathlib

namespace OMA.P067076

open OMA.S_oeis_a067076

/-- Primes below N are the odd primes below N, plus the prime 2 when 2 < N. -/
lemma count_prime_eq (N : ℕ) :
    Nat.count Nat.Prime N =
      Nat.count (fun m => Odd m ∧ m.Prime) N + (if 2 < N then 1 else 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.count_succ, Nat.count_succ, ih]
    by_cases hp : N.Prime
    · rcases hp.eq_two_or_odd' with h2 | hodd
      · subst h2
        have h : ¬ (Odd 2 ∧ Nat.Prime 2) := by
          rintro ⟨⟨k, hk⟩, _⟩
          omega
        rw [if_pos Nat.prime_two, if_neg h, if_neg (lt_irrefl 2), if_pos (by norm_num : 2 < 2 + 1)]
      · have hN : 3 ≤ N := by
          have := hp.two_le
          obtain ⟨k, hk⟩ := hodd
          omega
        rw [if_pos hp, if_pos (⟨hodd, hp⟩ : Odd N ∧ N.Prime), if_pos (by omega : 2 < N),
          if_pos (by omega : 2 < N + 1)]
    · have h : ¬ (Odd N ∧ N.Prime) := fun h => hp h.2
      rw [if_neg hp, if_neg h]
      by_cases h2 : 2 < N
      · rw [if_pos h2, if_pos (by omega : 2 < N + 1)]
      · have hN2 : N ≠ 2 := fun h => hp (h ▸ Nat.prime_two)
        rw [if_neg h2, if_neg (by omega : ¬ 2 < N + 1)]

/-- k ↦ 2k + 3 matches the k below K with 2k + 3 prime and the odd primes below 2K + 3. -/
lemma count_shift (K : ℕ) :
    Nat.count (fun k => (2 * k + 3).Prime) K =
      Nat.count (fun m => Odd m ∧ m.Prime) (2 * K + 3) := by
  induction K with
  | zero =>
    have h0 : ¬ (Odd 0 ∧ Nat.Prime 0) := fun h => Nat.not_prime_zero h.2
    have h1 : ¬ (Odd 1 ∧ Nat.Prime 1) := fun h => Nat.not_prime_one h.2
    have h2 : ¬ (Odd 2 ∧ Nat.Prime 2) := by
      rintro ⟨⟨k, hk⟩, _⟩
      omega
    rw [Nat.count_zero, show 2 * 0 + 3 = 0 + 1 + 1 + 1 by norm_num, Nat.count_succ,
      Nat.count_succ, Nat.count_succ, Nat.count_zero]
    rw [if_neg h0, if_neg h1, if_neg h2]
  | succ K ih =>
    rw [Nat.count_succ (fun k => (2 * k + 3).Prime) K, ih,
      show 2 * (K + 1) + 3 = (2 * K + 3) + 1 + 1 by ring,
      Nat.count_succ (fun m => Odd m ∧ m.Prime) (2 * K + 3 + 1),
      Nat.count_succ (fun m => Odd m ∧ m.Prime) (2 * K + 3)]
    have hodd : Odd (2 * K + 3) := ⟨K + 1, by ring⟩
    have hev : ¬ (Odd (2 * K + 3 + 1) ∧ (2 * K + 3 + 1).Prime) := by
      rintro ⟨⟨j, hj⟩, _⟩
      omega
    rw [if_neg hev]
    by_cases hp : (2 * K + 3).Prime
    · rw [if_pos hp, if_pos (⟨hodd, hp⟩ : Odd (2 * K + 3) ∧ (2 * K + 3).Prime)]
    · have h : ¬ (Odd (2 * K + 3) ∧ (2 * K + 3).Prime) := fun h => hp h.2
      rw [if_neg hp, if_neg h]

/-- The odd numbers below N: 1 (when 1 < N), the odd primes and the odd composites. -/
lemma count_odd_split (N : ℕ) :
    Nat.count (fun m => Odd m ∧ 1 < m ∧ ¬ m.Prime) N + Nat.count (fun m => Odd m ∧ m.Prime) N
      + (if 1 < N then 1 else 0) = N / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.count_succ, Nat.count_succ]
    rcases Nat.even_or_odd N with he | ho
    · have hno : ¬ Odd N := Nat.not_odd_iff_even.mpr he
      have h1 : ¬ (Odd N ∧ 1 < N ∧ ¬ N.Prime) := fun h => hno h.1
      have h2 : ¬ (Odd N ∧ N.Prime) := fun h => hno h.1
      rw [if_neg h1, if_neg h2]
      obtain ⟨k, hk⟩ := he
      by_cases hN : 1 < N
      · rw [if_pos hN] at ih
        rw [if_pos (by omega : 1 < N + 1)]
        omega
      · rw [if_neg hN] at ih
        rw [if_neg (by omega : ¬ 1 < N + 1)]
        omega
    · have ho' := ho
      obtain ⟨k, hk⟩ := ho'
      by_cases hp : N.Prime
      · have h1 : ¬ (Odd N ∧ 1 < N ∧ ¬ N.Prime) := fun h => h.2.2 hp
        have h2 : Odd N ∧ N.Prime := ⟨ho, hp⟩
        have h3 : 1 < N := hp.one_lt
        rw [if_neg h1, if_pos h2]
        rw [if_pos h3] at ih
        rw [if_pos (by omega : 1 < N + 1)]
        omega
      · by_cases hN1 : N = 1
        · subst hN1
          have h1 : ¬ (Odd 1 ∧ 1 < 1 ∧ ¬ Nat.Prime 1) := fun h => lt_irrefl 1 h.2.1
          have h2 : ¬ (Odd 1 ∧ Nat.Prime 1) := fun h => Nat.not_prime_one h.2
          rw [if_neg h1, if_neg h2]
          rw [if_neg (lt_irrefl 1)] at ih
          rw [if_pos (by norm_num : 1 < 1 + 1)]
          omega
        · have h3 : 1 < N := by omega
          have h1 : Odd N ∧ 1 < N ∧ ¬ N.Prime := ⟨ho, h3, hp⟩
          have h2 : ¬ (Odd N ∧ N.Prime) := fun h => hp h.2
          rw [if_pos h1, if_neg h2]
          rw [if_pos h3] at ih
          rw [if_pos (by omega : 1 < N + 1)]
          omega

/-- The positive even numbers below N number (N - 1) / 2. -/
lemma count_even (N : ℕ) : Nat.count (fun m => 0 < m ∧ Even m) N = (N - 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.count_succ, ih]
    by_cases h : 0 < N ∧ Even N
    · rw [if_pos h]
      obtain ⟨h0, k, hk⟩ := h
      omega
    · rw [if_neg h]
      rcases Nat.even_or_odd N with he | ho
      · have hN : N = 0 := by
          by_contra hne
          exact h ⟨Nat.pos_of_ne_zero hne, he⟩
        subst hN
        simp
      · obtain ⟨k, hk⟩ := ho
        omega

theorem sol : type_of% @OMA.S_oeis_a067076.main := by
  intro n hn
  have hinf := Nat.infinite_setOf_prime
  set q := Nat.nth Nat.Prime n with hq
  have hqp : q.Prime := Nat.prime_nth_prime n
  have hcount : Nat.count Nat.Prime q = n := Nat.count_nth_of_infinite hinf n
  have hq2 : 2 < q := by
    have h0 : 2 ≤ Nat.nth Nat.Prime 0 := (Nat.prime_nth_prime 0).two_le
    have hlt : Nat.nth Nat.Prime 0 < Nat.nth Nat.Prime n :=
      Nat.nth_strictMono hinf (show 0 < n by omega)
    omega
  have hqodd : Odd q := hqp.eq_two_or_odd'.resolve_left (by omega)
  obtain ⟨r, hr⟩ := hqodd
  have hpn : prime (n + 1) = q := by
    show Nat.nth Nat.Prime (n + 1 - 1) = q
    rw [Nat.add_sub_cancel]
  have h1 := count_prime_eq q
  rw [if_pos hq2, hcount] at h1
  have h3 := count_odd_split q
  rw [if_pos (by omega : 1 < q)] at h3
  have hK : 2 * (r - 1) + 3 = q := by omega
  have hc := count_shift (r - 1)
  rw [hK] at hc
  have hpK : (2 * (r - 1) + 3).Prime := by
    rw [hK]
    exact hqp
  have hnth := Nat.nth_count (p := fun k => (2 * k + 3).Prime) hpK
  have ha : a n = r - 1 := by
    show Nat.nth (fun k => (2 * k + 3).Prime) (n - 1) = r - 1
    rw [show n - 1 = Nat.count (fun k => (2 * k + 3).Prime) (r - 1) by omega]
    exact hnth
  have hA8 : A008507 n = Nat.count (fun m => Odd m ∧ 1 < m ∧ ¬ m.Prime) q := by
    unfold A008507
    rw [hpn, Nat.count_eq_card_filter_range]
  have hA5 : A005097 n = (q - 1) / 2 := by
    unfold A005097
    rw [hpn]
  have hA1 : A102781 (n + 1) = (q - 1) / 2 := by
    unfold A102781
    rw [hpn, ← Nat.count_eq_card_filter_range, count_even]
  refine ⟨?_, ?_, ?_⟩ <;> omega

end OMA.P067076

theorem OMA.solution : type_of% @OMA.S_oeis_a067076.main := OMA.P067076.sol

