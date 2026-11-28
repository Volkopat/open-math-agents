import OMAReductions.R_oeis_a065515_R1
import Mathlib

-- Step oeis-a065515.R1.H1: hypothesis H1 of reduction oeis-a065515.R1
-- Credit: @Raimo33

namespace Raimo515

theorem pc (n : ℕ) : Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]

theorem card_img (s k : ℕ) (hk : 0 < k) :
    (((Finset.range (s + 1)).filter Nat.Prime).image (fun p => p ^ k)).card
      = ((Finset.range (s + 1)).filter Nat.Prime).card :=
  Finset.card_image_of_injective _ (Nat.pow_left_injective hk.ne')

theorem not_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 2 ≤ k) : ¬ (p ^ k).Prime :=
  Nat.Prime.not_prime_pow' (by omega)

theorem sq_ne_cube {p q : ℕ} (hp : p.Prime) (hq : q.Prime) : p ^ 2 ≠ q ^ 3 := by
  intro h
  have : q ∣ p ^ 2 := by rw [h]; exact dvd_pow_self q (by norm_num)
  have hqp := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow this)
  subst hqp
  have h2 := hp.two_le
  have : q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

end Raimo515

open Raimo515
theorem OMA.solution : OMA.R_oeis_a065515_R1.H1 := by
  show ∀ n s c : ℕ, 1≤n → s^2≤n → c^3≤n →
  Nat.primeCounting n + Nat.primeCounting s + Nat.primeCounting c + 1 ≤ OMA.S_oeis_a065515.a n
  intro n s c hn hs hc
  set P1 := (Finset.range (n + 1)).filter Nat.Prime
  set P2 := ((Finset.range (s + 1)).filter Nat.Prime).image (fun p => p ^ 2)
  set P3 := ((Finset.range (c + 1)).filter Nat.Prime).image (fun p => p ^ 3)
  have e1 : Nat.primeCounting n = P1.card := pc n
  have e2 : Nat.primeCounting s = P2.card := by rw [pc, card_img s 2 (by norm_num)]
  have e3 : Nat.primeCounting c = P3.card := by rw [pc, card_img c 3 (by norm_num)]
  have d12 : Disjoint P1 P2 := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [P1, P2, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hx1 hx2
    obtain ⟨p, ⟨_, hp⟩, rfl⟩ := hx2
    exact not_prime_pow hp le_rfl hx1.2
  have d123 : Disjoint (P1 ∪ P2) P3 := by
    rw [Finset.disjoint_left]
    intro x hx hx3
    simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at hx hx3
    obtain ⟨q, ⟨_, hq⟩, rfl⟩ := hx3
    rcases hx with h | ⟨p, ⟨_, hp⟩, hpq⟩
    · exact not_prime_pow hq (by norm_num) h.2
    · exact sq_ne_cube hp hq hpq
  have d0 : Disjoint (P1 ∪ P2 ∪ P3) {1} := by
    rw [Finset.disjoint_singleton_right]
    intro h
    simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_range] at h
    rcases h with (h | ⟨p, ⟨_, hp⟩, hp1⟩) | ⟨p, ⟨_, hp⟩, hp1⟩
    · exact Nat.not_prime_one h.2
    · have := hp.two_le; have : 4 ≤ p ^ 2 := by nlinarith
      omega
    · have := hp.two_le; have : 8 ≤ p ^ 3 := by
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ p ^ 3 := Nat.pow_le_pow_left this 3
      omega
  have hsub : P1 ∪ P2 ∪ P3 ∪ {1} ⊆ (Finset.Icc 1 n).filter fun m => m = 1 ∨ IsPrimePow m := by
    intro x hx
    simp only [P1, P2, P3, Finset.mem_union, Finset.mem_filter, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton, Finset.mem_Icc] at hx ⊢
    rcases hx with ((h | ⟨p, ⟨hps, hp⟩, rfl⟩) | ⟨p, ⟨hps, hp⟩, rfl⟩) | rfl
    · exact ⟨⟨h.2.one_le, by omega⟩, Or.inr h.2.isPrimePow⟩
    · refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero), ?_⟩, Or.inr (hp.isPrimePow.pow (by norm_num))⟩
      exact le_trans (Nat.pow_le_pow_left (by omega) 2) hs
    · refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero), ?_⟩, Or.inr (hp.isPrimePow.pow (by norm_num))⟩
      exact le_trans (Nat.pow_le_pow_left (by omega) 3) hc
    · exact ⟨⟨le_rfl, hn⟩, Or.inl rfl⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint d0, Finset.card_union_of_disjoint d123,
    Finset.card_union_of_disjoint d12] at this
  simp only [Finset.card_singleton] at this
  unfold OMA.S_oeis_a065515.a
  omega
