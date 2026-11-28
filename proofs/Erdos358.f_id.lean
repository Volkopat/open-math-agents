import FormalConjectures.ErdosProblems.«358»

/-! Original proof by @philipsaint. An odd divisor and its complementary factor in twice the
integer determine the interval length as their minimum. -/

namespace OMA.E358

open Finset Erdos358

lemma sumIcc (u k : ℕ) : 2 * ∑ i ∈ Icc u (u + k), i = (k + 1) * (2 * u + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    ring

lemma mem_iff (n u v : ℕ) :
    (u, v) ∈ intervalRepresentations id n ↔ 0 < u ∧ 0 < v ∧ n = ∑ i ∈ Icc u v, i :=
  Iff.rfl

lemma rep_param {n u v : ℕ} (hn : 0 < n) (h : (u, v) ∈ intervalRepresentations id n) :
    ∃ k, v = u + k ∧ 0 < u ∧ 2 * n = (k + 1) * (2 * u + k) := by
  rw [mem_iff] at h
  obtain ⟨hu, hv, hs⟩ := h
  have hle : u ≤ v := by
    by_contra hc
    rw [Finset.Icc_eq_empty hc, Finset.sum_empty] at hs
    omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact ⟨k, rfl, hu, hs ▸ sumIcc u k⟩

lemma rep_of {n u k : ℕ} (hu : 0 < u) (h : 2 * n = (k + 1) * (2 * u + k)) :
    (u, u + k) ∈ intervalRepresentations id n := by
  rw [mem_iff]
  refine ⟨hu, by omega, ?_⟩
  have h2 := sumIcc u k
  omega

/-- The odd divisor attached to a representation. -/
def g (p : ℕ × ℕ) : ℕ := if Odd (p.2 - p.1 + 1) then p.2 - p.1 + 1 else p.1 + p.2

lemma g_param (u k : ℕ) : g (u, u + k) = if Odd (k + 1) then k + 1 else 2 * u + k := by
  simp [g, two_mul, add_assoc]

lemma odd_dvd {a b n : ℕ} (h : 2 * n = a * b) (ha : Odd a) : a ∣ n :=
  (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr ha)) ⟨b, h⟩

lemma g_mem {n u k : ℕ} (h : 2 * n = (k + 1) * (2 * u + k)) :
    g (u, u + k) ∣ n ∧ Odd (g (u, u + k)) := by
  rw [g_param]
  split <;> rename_i ho
  · exact ⟨odd_dvd h ho, ho⟩
  · have hodd : Odd (2 * u + k) := by simp only [Nat.odd_iff] at *; omega
    exact ⟨odd_dvd (h.trans (mul_comm _ _)) hodd, hodd⟩

lemma g_inj {n u k u' k' : ℕ} (hu : 0 < u) (hu' : 0 < u')
    (h : 2 * n = (k + 1) * (2 * u + k)) (h' : 2 * n = (k' + 1) * (2 * u' + k'))
    (hg : g (u, u + k) = g (u', u' + k')) : u = u' ∧ k = k' := by
  have lo (u k : ℕ) (hu : 0 < u) (hp : 2 * n = (k + 1) * (2 * u + k)) :
      min (g (u, u + k)) (2 * n / g (u, u + k)) = k + 1 := by
    rw [g_param, hp]
    split
    · rw [Nat.mul_div_cancel_left _ (by omega), min_eq_left (by omega)]
    · rw [Nat.mul_div_cancel _ (by omega), min_eq_right (by omega)]
  have hk : k + 1 = k' + 1 := by rw [← lo u k hu h, hg, lo u' k' hu' h']
  obtain rfl : k = k' := by omega
  have := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) (h.symm.trans h')
  omega

lemma g_surj {n d : ℕ} (hn : 0 < n) (hd : d ∣ n) (ho : Odd d) :
    ∃ u k, 0 < u ∧ 2 * n = (k + 1) * (2 * u + k) ∧ g (u, u + k) = d := by
  obtain ⟨c, rfl⟩ := hd
  obtain ⟨j, rfl⟩ := ho
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  by_cases hlt : j < c
  · refine ⟨c - j, 2 * j, by omega, ?_, ?_⟩
    · have : 2 * (c - j) + 2 * j = 2 * c := by omega
      rw [this]; ring
    · simp [g_param, show Odd (2 * j + 1) from ⟨j, rfl⟩]
  · obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hev : ¬ Odd (2 * c' + 1 + 1) := by
      rw [Nat.not_odd_iff_even]; exact ⟨c' + 1, by omega⟩
    refine ⟨j - c', 2 * c' + 1, by omega, ?_, ?_⟩
    · have : 2 * (j - c') + (2 * c' + 1) = 2 * j + 1 := by omega
      rw [this]; ring
    · rw [g_param, if_neg hev]; omega

end OMA.E358

open Finset Erdos358 OMA.E358 in
theorem OMA.solution : type_of% @Erdos358.f_id := by
  funext n
  show Nat.card (intervalRepresentations id n) = _
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hinf : (intervalRepresentations id 0).Infinite := by
      refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k + 2, 1)) ?_ ?_
      · intro a b hab
        simp only [Prod.mk.injEq] at hab
        omega
      · intro k
        rw [mem_iff]
        refine ⟨by omega, by omega, ?_⟩
        rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    have := hinf.to_subtype
    rw [Nat.card_eq_zero_of_infinite]
    simp
  · rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    refine Set.ncard_congr (fun p _ => g p) ?_ ?_ ?_
    · rintro ⟨u, v⟩ hp
      obtain ⟨k, rfl, hu, h⟩ := rep_param hn hp
      have := g_mem h
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨this.1, by omega⟩, this.2⟩
    · rintro ⟨u, v⟩ ⟨u', v'⟩ hp hp' hg
      obtain ⟨k, rfl, hu, h⟩ := rep_param hn hp
      obtain ⟨k', rfl, hu', h'⟩ := rep_param hn hp'
      obtain ⟨rfl, rfl⟩ := g_inj hu hu' h h' hg
      rfl
    · intro d hd
      simp only [Finset.mem_coe, Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨u, k, hu, h, hgd⟩ := g_surj hn hd.1.1 hd.2
      exact ⟨(u, u + k), rep_of hu h, hgd⟩
