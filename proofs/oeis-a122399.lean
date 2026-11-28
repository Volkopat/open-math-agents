import OMAStatements.S_oeis_a122399
import Mathlib

-- Problem: OEIS A122399, a(n) = Sum_{j=0..n} j^n * j! * Stirling2(n,j). Conjecture:
-- a(n + p - 1) = a(n) mod p for every prime p and every n >= 1.
-- Proof. Stirling2(n,j) * j! = Sum_{i=0..j} (-1)^(j+i) * C(j,i) * i^n (number of surjections),
-- by induction on n from the recurrence. By Fermat, i^(n+p-1) = i^n mod p for all i when n >= 1.
-- So each term j^n * j! * Stirling2(n,j) is unchanged mod p when n is replaced by n + p - 1,
-- and the terms with j > n vanish because Stirling2(n,j) = 0 there.

open Finset

lemma OMA.surj (s : ℕ → ℕ → ℕ) (h00 : s 0 0 = 1) (hn0 : ∀ n, s (n + 1) 0 = 0)
    (h0j : ∀ j, s 0 (j + 1) = 0)
    (hrec : ∀ n j, s (n + 1) (j + 1) = (j + 1) * s n (j + 1) + s n j) :
    ∀ n j : ℕ, (s n j : ℤ) * (j.factorial : ℤ)
      = ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
  intro n
  induction n with
  | zero =>
    intro j
    rcases j with _ | j
    · simp [h00]
    · rw [h0j]
      have h := Int.alternating_sum_range_choose (n := j + 1)
      have h2 : ∑ i ∈ range (j + 1 + 1), (-1 : ℤ) ^ (j + 1 + i) * ((j + 1).choose i : ℤ) * (i : ℤ) ^ 0
          = (-1 : ℤ) ^ (j + 1) * ∑ i ∈ range (j + 1 + 1), (-1 : ℤ) ^ i * ((j + 1).choose i : ℤ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [pow_add]
        ring
      rw [h2, h]
      simp
  | succ n ih =>
    intro j
    rcases j with _ | j
    · rw [hn0]
      simp
    · have e1 : (s (n + 1) (j + 1) : ℤ) * ((j + 1).factorial : ℤ)
          = ((j : ℤ) + 1) * ((s n (j + 1) : ℤ) * ((j + 1).factorial : ℤ))
            + ((j : ℤ) + 1) * ((s n j : ℤ) * (j.factorial : ℤ)) := by
        rw [hrec, Nat.factorial_succ]
        push_cast
        ring
      have e2 : ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n
          = ∑ i ∈ range (j + 1 + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
        rw [Finset.sum_range_succ _ (j + 1), Nat.choose_succ_self]
        simp
      rw [e1, ih (j + 1), ih j, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rcases i with _ | i
      · simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, add_zero, mul_one]
        ring
      · have hc : ((j + 1).choose (i + 1) : ℤ) = (j.choose i : ℤ) + (j.choose (i + 1) : ℤ) := by
          rw [Nat.choose_succ_succ]
          push_cast
          ring
        have hm : ((j : ℤ) + 1) * (j.choose i : ℤ)
            = ((j + 1).choose (i + 1) : ℤ) * ((i : ℤ) + 1) := by
          have h3 := Nat.add_one_mul_choose_eq j i
          exact_mod_cast h3
        rw [hc] at hm
        have hs : (-1 : ℤ) ^ (j + 1 + (i + 1)) = -(-1 : ℤ) ^ (j + (i + 1)) := by
          have h4 : j + 1 + (i + 1) = (j + (i + 1)) + 1 := by ring
          rw [h4, pow_succ]
          ring
        push_cast
        rw [hs, hc, pow_succ]
        linear_combination (-(-1 : ℤ) ^ (j + (i + 1)) * ((i : ℤ) + 1) ^ n) * hm

lemma OMA.s_zero (s : ℕ → ℕ → ℕ) (h0j : ∀ j, s 0 (j + 1) = 0)
    (hrec : ∀ n j, s (n + 1) (j + 1) = (j + 1) * s n (j + 1) + s n j) :
    ∀ n j : ℕ, n < j → s n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact h0j j'
  | succ n ih =>
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [hrec, ih (j' + 1) (by omega), ih j' (by omega)]
    simp

lemma OMA.pow_per_prime (p i n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    i ^ (n + (p - 1)) ≡ i ^ n [MOD p] := by
  by_cases hpi : p ∣ i
  · have hd1 : p ∣ i ^ n := dvd_pow hpi (by omega)
    have hd2 : p ∣ i ^ (n + (p - 1)) := dvd_pow hpi (by omega)
    exact (Nat.modEq_zero_iff_dvd.mpr hd2).trans (Nat.modEq_zero_iff_dvd.mpr hd1).symm
  · have hcop : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpi).symm
    have h1 : i ^ Nat.totient p ≡ 1 [MOD p] := Nat.ModEq.pow_totient hcop
    rw [Nat.totient_prime hp] at h1
    have h3 := h1.mul_left (i ^ n)
    rw [← pow_add, mul_one] at h3
    exact h3

lemma OMA.T_per_prime (s : ℕ → ℕ → ℕ) (h00 : s 0 0 = 1) (hn0 : ∀ n, s (n + 1) 0 = 0)
    (h0j : ∀ j, s 0 (j + 1) = 0)
    (hrec : ∀ n j, s (n + 1) (j + 1) = (j + 1) * s n (j + 1) + s n j)
    (p n j : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    (s (n + (p - 1)) j : ℤ) * (j.factorial : ℤ)
      ≡ (s n j : ℤ) * (j.factorial : ℤ) [ZMOD p] := by
  rw [OMA.surj s h00 hn0 h0j hrec, OMA.surj s h00 hn0 h0j hrec]
  refine Int.ModEq.sum (fun i _ => ?_)
  have h := OMA.pow_per_prime p i n hp hn
  have h' : ((i ^ (n + (p - 1)) : ℕ) : ℤ) ≡ ((i ^ n : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    Int.natCast_modEq_iff.mpr h
  push_cast at h'
  exact Int.ModEq.mul_left _ h'

open OMA.S_oeis_a122399

theorem OMA.solution : type_of% @OMA.S_oeis_a122399.main := by
  have h00 : stirling2 0 0 = 1 := by
    rw [stirling2]
  have hn0 : ∀ n, stirling2 (n + 1) 0 = 0 := fun n => by
    rw [stirling2]
  have h0j : ∀ j, stirling2 0 (j + 1) = 0 := fun j => by
    rw [stirling2]
  have hrec : ∀ n j, stirling2 (n + 1) (j + 1)
      = (j + 1) * stirling2 n (j + 1) + stirling2 n j := fun n j => by
    rw [stirling2]
  intro p n hp hn
  have e : ∀ m, ((a m : ℕ) : ℤ)
      = ∑ j ∈ range (m + 1), (j : ℤ) ^ m * ((stirling2 m j : ℤ) * (j.factorial : ℤ)) := by
    intro m
    unfold a
    push_cast
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  apply Int.natCast_modEq_iff.mp
  rw [e, e]
  have hB : ∑ j ∈ range (n + 1), (j : ℤ) ^ n * ((stirling2 n j : ℤ) * (j.factorial : ℤ))
      = ∑ j ∈ range (n + (p - 1) + 1),
          (j : ℤ) ^ n * ((stirling2 n j : ℤ) * (j.factorial : ℤ)) := by
    refine Finset.sum_subset (fun x hx => ?_) (fun j _ hj => ?_)
    · simp only [Finset.mem_range] at hx ⊢
      omega
    · have hlt : n < j := by
        simp only [Finset.mem_range] at hj
        omega
      rw [OMA.s_zero stirling2 h0j hrec n j hlt]
      simp
  rw [hB]
  refine Int.ModEq.sum (fun j _ => ?_)
  have h1 := OMA.pow_per_prime p j n hp hn
  have h1' : ((j ^ (n + (p - 1)) : ℕ) : ℤ) ≡ ((j ^ n : ℕ) : ℤ) [ZMOD (p : ℤ)] :=
    Int.natCast_modEq_iff.mpr h1
  push_cast at h1'
  exact h1'.mul (OMA.T_per_prime stirling2 h00 hn0 h0j hrec p n j hp hn)
