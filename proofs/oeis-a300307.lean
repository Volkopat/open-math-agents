import OMAStatements.S_oeis_a300307
import Mathlib

-- Problem: OEIS A300307, conjecture: a(2^n) = 2^(2^n - n) for n > 0, where a(N) is the number
-- of sign choices with 1 +- 3 +- 6 +- ... +- N(N+1)/2 == 0 (mod N).
-- Statement: statements/oeis-a300307.lean (declaration OMA.S_oeis_a300307.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let w(k) = k(k+1)/2 and N = 2^n. A sign choice is the set A of indices in {2..N} with
-- the sign -, and the signed sum is W - 2 Sum_{k in A} w(k) with W = Sum_{k=1..N} w(k).
-- Step 1 (uniform distribution). Let S be a finite set that contains, for each i < j, an
-- element a with w(a) = 2^i (odd number). Then for each c the number of subsets A of S with
-- Sum_{k in A} w(k) == c (mod 2^j) is 2^(|S| - j). Induction on j: remove an element a with
-- w(a) = 2^(j-1) (odd). The subsets of S without a and with a give the conditions
-- x == c and x + w(a) == c (mod 2^j), and exactly one of them is true when x == c (mod 2^(j-1)).
-- Step 2. 6 W = N (N+1) (N+2), thus W = 2 h is even for N = 2^n, n > 0. The condition is
-- Sum_{k in A} w(k) == h (mod 2^(n-1)). The set {2..N} contains 2^(i+1) for i < n - 1, and
-- w(2^(i+1)) = 2^i (2^(i+1) + 1). Step 1 gives the number 2^(N - 1 - (n - 1)) = 2^(N - n).

namespace OMA.A300307

open Finset OMA.S_oeis_a300307

/-- The triangular number T(k) as an integer. -/
def w (k : ℕ) : ℤ := ((k * (k + 1) / 2 : ℕ) : ℤ)

/-- The number of subsets A of S with Sum_{k in A} w(k) ≡ c (mod 2^j). -/
def cnt (j : ℕ) (S : Finset ℕ) (c : ℤ) : ℕ :=
  (S.powerset.filter (fun A => (2 : ℤ) ^ j ∣ ∑ k ∈ A, w k - c)).card

lemma val_ne (i j : ℕ) (hij : i < j) (s t : ℤ) :
    (2 : ℤ) ^ i * (2 * s + 1) ≠ 2 ^ j * (2 * t + 1) := by
  intro h
  obtain ⟨d, rfl⟩ : ∃ d, j = i + (d + 1) := ⟨j - i - 1, by omega⟩
  rw [pow_add, mul_assoc] at h
  have h2 := mul_left_cancel₀ (pow_ne_zero i (by norm_num : (2 : ℤ) ≠ 0)) h
  rw [pow_succ] at h2
  generalize (2 : ℤ) ^ d = z at h2
  have h3 : 2 * s + 1 = 2 * (z * (2 * t + 1)) := by rw [h2]; ring
  omega

lemma unif : ∀ (j : ℕ) (S : Finset ℕ),
    (∀ i < j, ∃ a ∈ S, ∃ t : ℤ, w a = 2 ^ i * (2 * t + 1)) →
    ∀ c : ℤ, cnt j S c * 2 ^ j = 2 ^ S.card := by
  intro j
  induction j with
  | zero =>
    intro S _ c
    simp [cnt]
  | succ j ih =>
    intro S hS c
    obtain ⟨a, haS, t, hat⟩ := hS j (Nat.lt_succ_self j)
    have hS' : ∀ i < j, ∃ b ∈ S.erase a, ∃ t : ℤ, w b = 2 ^ i * (2 * t + 1) := by
      intro i hi
      obtain ⟨b, hb, s, hbs⟩ := hS i (by omega)
      refine ⟨b, mem_erase.2 ⟨?_, hb⟩, s, hbs⟩
      rintro rfl
      exact val_ne i j hi s t (hbs.symm.trans hat)
    have hIH := ih (S.erase a) hS' c
    have hna : a ∉ S.erase a := notMem_erase a S
    have key : cnt (j + 1) (insert a (S.erase a)) c = cnt j (S.erase a) c := by
      unfold cnt
      rw [card_filter, card_filter, sum_powerset_insert hna, ← sum_add_distrib]
      apply sum_congr rfl
      intro A hA
      have haA : a ∉ A := fun h => hna (mem_powerset.1 hA h)
      rw [sum_insert haA, hat]
      generalize ∑ k ∈ A, w k = x
      have h2 : (2 : ℤ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
      by_cases h : (2 : ℤ) ^ j ∣ x - c
      · obtain ⟨m, hm⟩ := h
        have d1 : (2 : ℤ) ^ (j + 1) ∣ x - c ↔ 2 ∣ m := by
          rw [hm, pow_succ]; exact mul_dvd_mul_iff_left h2
        have d2 : (2 : ℤ) ^ (j + 1) ∣ 2 ^ j * (2 * t + 1) + x - c ↔ 2 ∣ m + 2 * t + 1 := by
          have e : (2 : ℤ) ^ j * (2 * t + 1) + x - c = 2 ^ j * (m + 2 * t + 1) := by
            linear_combination hm
          rw [e, pow_succ]; exact mul_dvd_mul_iff_left h2
        rw [if_pos (Dvd.intro m hm.symm)]
        by_cases hm2 : (2 : ℤ) ∣ m
        · rw [if_pos (d1.2 hm2), if_neg (fun h' => by have := d2.1 h'; omega)]
        · rw [if_neg (fun h' => hm2 (d1.1 h')), if_pos (d2.2 (by omega))]
      · have n1 : ¬ (2 : ℤ) ^ (j + 1) ∣ x - c := fun h' =>
          h (Dvd.dvd.trans (pow_dvd_pow 2 (Nat.le_succ j)) h')
        have n2 : ¬ (2 : ℤ) ^ (j + 1) ∣ 2 ^ j * (2 * t + 1) + x - c := by
          intro h'
          have h3 : (2 : ℤ) ^ j ∣ 2 ^ j * (2 * t + 1) + x - c :=
            Dvd.dvd.trans (pow_dvd_pow 2 (Nat.le_succ j)) h'
          have h4 : (2 : ℤ) ^ j ∣ 2 ^ j * (2 * t + 1) := Dvd.intro _ rfl
          apply h
          have h5 := dvd_sub h3 h4
          have e : (2 : ℤ) ^ j * (2 * t + 1) + x - c - 2 ^ j * (2 * t + 1) = x - c := by ring
          rwa [e] at h5
        rw [if_neg n1, if_neg n2, if_neg h]
    rw [insert_erase haS] at key
    rw [key, pow_succ, ← mul_assoc, hIH]
    have hcard : S.card = (S.erase a).card + 1 := by
      rw [card_erase_of_mem haS]; have := card_pos.2 ⟨a, haS⟩; omega
    rw [hcard, pow_succ]

lemma tri_sum (N : ℕ) : 6 * ∑ k ∈ Icc 1 N, (k * (k + 1) / 2) = N * (N + 1) * (N + 2) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), mul_add, ih]
    have h : (N + 1) * (N + 1 + 1) / 2 * 2 = (N + 1) * (N + 1 + 1) :=
      Nat.div_mul_cancel (even_iff_two_dvd.1 (Nat.even_mul_succ_self (N + 1)))
    have h6 : 6 * ((N + 1) * (N + 1 + 1) / 2) = 3 * ((N + 1) * (N + 1 + 1)) := by omega
    rw [h6]; ring

theorem main' (n : ℕ) (hn : 0 < n) : a (2 ^ n) = 2 ^ (2 ^ n - n) := by
  obtain ⟨M, hM⟩ : ∃ M, 2 ^ n = 2 * M := ⟨2 ^ (n - 1), by rw [← pow_succ']; congr 1; omega⟩
  have hMp : M = 2 ^ (n - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  generalize hN : 2 ^ n = N at hM ⊢
  -- the total sum is even
  obtain ⟨h, hh⟩ : ∃ h : ℕ, ∑ k ∈ Icc 1 N, (k * (k + 1) / 2) = 2 * h := by
    have h6 := tri_sum N
    rw [hM] at h6
    have e : 2 * M * (2 * M + 1) * (2 * M + 2) = 4 * (M * (2 * M + 1) * (M + 1)) := by ring
    rw [e] at h6
    rw [hM]
    exact ⟨(∑ k ∈ Icc 1 (2 * M), (k * (k + 1) / 2)) / 2, by omega⟩
  have hhz : ∑ k ∈ Icc 1 N, w k = 2 * (h : ℤ) := by
    unfold w; exact_mod_cast hh
  have hsum : ∀ A ∈ (Icc 2 N).powerset,
      ∑ k ∈ Icc 1 N, (if k ∈ A then (-1 : ℤ) else 1) * ((k * (k + 1) / 2 : ℕ) : ℤ)
        = 2 * (h : ℤ) - 2 * ∑ k ∈ A, w k := by
    intro A hA
    have hsub : A ⊆ Icc 1 N := fun x hx => by
      have := mem_Icc.1 (mem_powerset.1 hA hx)
      exact mem_Icc.2 ⟨by omega, this.2⟩
    have e : ∑ k ∈ Icc 1 N, (if k ∈ A then (-1 : ℤ) else 1) * ((k * (k + 1) / 2 : ℕ) : ℤ)
        = ∑ k ∈ Icc 1 N, w k - 2 * ∑ k ∈ Icc 1 N, (if k ∈ A then w k else 0) := by
      rw [mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro k _
      unfold w
      split_ifs <;> ring
    rw [e, hhz, sum_ite_mem, inter_eq_right.2 hsub]
  have hNc : (N : ℤ) = 2 * 2 ^ (n - 1) := by rw [hM, hMp]; push_cast; ring
  have hcnt : a N = cnt (n - 1) (Icc 2 N) h := by
    unfold a cnt
    congr 1
    apply filter_congr
    intro A hA
    rw [hsum A hA, hNc, show (2 : ℤ) * h - 2 * ∑ k ∈ A, w k = 2 * (h - ∑ k ∈ A, w k) by ring,
      mul_dvd_mul_iff_left (by norm_num), ← dvd_neg, neg_sub]
  have hH : ∀ i < n - 1, ∃ b ∈ Icc 2 N, ∃ t : ℤ, w b = 2 ^ i * (2 * t + 1) := by
    intro i hi
    refine ⟨2 ^ (i + 1), mem_Icc.2 ⟨?_, ?_⟩, 2 ^ i, ?_⟩
    · have : 2 ^ 1 ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      simpa using this
    · rw [← hN]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    · unfold w
      have e : 2 ^ (i + 1) * (2 ^ (i + 1) + 1) / 2 = 2 ^ i * (2 * 2 ^ i + 1) := by
        have : 2 ^ (i + 1) * (2 ^ (i + 1) + 1) = 2 * (2 ^ i * (2 * 2 ^ i + 1)) := by ring
        rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
      rw [e]; push_cast; ring
  have hU := unif (n - 1) (Icc 2 N) hH h
  rw [← hcnt, Nat.card_Icc] at hU
  have hlt : n < N := by rw [← hN]; exact Nat.lt_two_pow_self
  have e : N + 1 - 2 = (N - n) + (n - 1) := by omega
  rw [e, pow_add] at hU
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hU

end OMA.A300307

theorem OMA.solution : type_of% @OMA.S_oeis_a300307.main :=
  fun n hn => OMA.A300307.main' n hn
