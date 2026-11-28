import OMAStatements.S_oeis_a210445

/-!
If the divisors of k < n have subset sums covering 0 through n−1, the
divisors of kn represent a number t by representing its quotient and
remainder modulo n separately. Doubling k doubles the covered interval
by allowing 1 and the doubled divisors. Four starting multipliers suffice
for the stronger bound.
-/

namespace PracticalMultipliers

open Finset OMA.S_oeis_a210445

private def Rep (m t : ℕ) : Prop := ∃ s ⊆ m.divisors, ∑ d ∈ s, d = t
private def Covers (m B : ℕ) : Prop := ∀ t ≤ B, Rep m t

private theorem scale {k n t : ℕ} (hk : 0 < k) (hn : 0 < n) (ht : Rep k t) :
    ∃ s ⊆ (k * n).divisors, (∀ d ∈ s, n ≤ d) ∧ ∑ d ∈ s, d = t * n := by
  obtain ⟨s,hs,hval⟩ := ht
  refine ⟨s.image (· * n), ?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
    obtain ⟨w,hw⟩ := Nat.dvd_of_mem_divisors (hs hv)
    exact Nat.mem_divisors.mpr ⟨⟨w, by rw [hw]; ring⟩, by positivity⟩
  · intro d hd
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hd
    have hp := Nat.pos_of_mem_divisors (hs hv)
    simpa using Nat.mul_le_mul_right n hp
  · rw [sum_image (by intro a _ b _ h; exact Nat.eq_of_mul_eq_mul_right hn h),
      ← sum_mul, hval]

private theorem practical {k n : ℕ} (hk : 0 < k) (hkn : k < n) (hc : Covers k (n - 1)) :
    IsPractical (k * n) := by
  have hn : 0 < n := by omega
  refine ⟨Nat.mul_pos hk hn, ?_⟩
  intro t _ ht
  have hq : t / n ≤ k := (Nat.div_le_div_right ht).trans_eq (Nat.mul_div_cancel _ hn)
  obtain ⟨s,hs,hsum⟩ := hc (t % n) (by have := Nat.mod_lt t hn; omega)
  obtain ⟨u,hu,hlarge,husum⟩ := scale hk hn (hc (t / n) (by omega))
  have hdis : Disjoint s u := Finset.disjoint_left.mpr (by
    intro d hd hu'
    have h₁ := Nat.le_of_dvd hk (Nat.dvd_of_mem_divisors (hs hd))
    have h₂ := hlarge d hu'
    omega)
  refine ⟨s ∪ u, union_subset ?_ hu, ?_⟩
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨dvd_trans (Nat.dvd_of_mem_divisors (hs hd)) (dvd_mul_right k n), by positivity⟩
  · rw [sum_union hdis, hsum, husum, Nat.mul_comm (t / n) n, Nat.mod_add_div]

private theorem doubled {k B : ℕ} (hk : 0 < k) (hc : Covers k B) : Covers (k * 2) (2 * B + 1) := by
  intro t ht
  obtain ⟨s,hs,hlarge,hval⟩ := scale hk (by decide : 0 < 2) (hc (t / 2) (by omega))
  by_cases he : t % 2 = 0
  · exact ⟨s, hs, by omega⟩
  · have hmem : 1 ∉ s := by intro h; have := hlarge 1 h; omega
    refine ⟨insert 1 s, insert_subset (Nat.one_mem_divisors.mpr (by positivity)) hs, ?_⟩
    rw [sum_insert hmem, hval]
    omega

private def sums (m : ℕ) : Finset ℕ := m.divisors.powerset.image (fun s => ∑ d ∈ s, d)

private theorem coverage {k b : ℕ} (h : Icc 0 b ⊆ sums k) : Covers k b := by
  intro t ht
  obtain ⟨s,hs,hval⟩ := mem_image.mp (h (mem_Icc.mpr ⟨Nat.zero_le _,ht⟩))
  exact ⟨s,mem_powerset.mp hs,hval⟩

private theorem one : Covers 1 1 := coverage (by decide +kernel)

private theorem small_multiplier (n : ℕ) (hn : 1 < n) : ∃ k, 0 < k ∧ k < n ∧ Covers k (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n = 2
    · subst n
      exact ⟨1, by decide, by decide, one⟩
    let m := (n + 1) / 2
    obtain ⟨k,hk,hkm,hc⟩ := ih m (by dsimp [m]; omega) (by dsimp [m]; omega)
    refine ⟨k * 2, by positivity, by dsimp [m] at hkm; omega, ?_⟩
    intro t ht
    apply doubled hk hc t
    dsimp [m]
    omega

set_option maxRecDepth 10000 in
private theorem base_interval (n : ℕ) (hl : 49 ≤ n) (hu : n ≤ 97) :
    ∃ k, 0 < k ∧ 2 * k < n ∧ Covers k (n - 1) := by
  by_cases h₁ : n ≤ 61
  · exact ⟨24, by decide, by omega, fun t ht => coverage (k := 24) (b := 60) (by decide +kernel) t (by omega)⟩
  by_cases h₂ : n ≤ 73
  · exact ⟨30, by decide, by omega, fun t ht => coverage (k := 30) (b := 72) (by decide +kernel) t (by omega)⟩
  by_cases h₃ : n ≤ 92
  · exact ⟨36, by decide, by omega, fun t ht => coverage (k := 36) (b := 91) (by decide +kernel) t (by omega)⟩
  exact ⟨42, by decide, by omega, fun t ht => coverage (k := 42) (b := 96) (by decide +kernel) t (by omega)⟩

private theorem half_multiplier (n : ℕ) (hn : 49 ≤ n) : ∃ k, 0 < k ∧ 2 * k < n ∧ Covers k (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n ≤ 97
    · exact base_interval n hn h
    let m := (n + 1) / 2
    obtain ⟨k,hk,hkm,hc⟩ := ih m (by dsimp [m]; omega) (by dsimp [m]; omega)
    refine ⟨k * 2, by positivity, by dsimp [m] at hkm; omega, ?_⟩
    intro t ht
    apply doubled hk hc t
    dsimp [m]
    omega

end PracticalMultipliers

open OMA.S_oeis_a210445 PracticalMultipliers

theorem OMA.solution : type_of% @OMA.S_oeis_a210445.main := by
  constructor
  · intro n hn
    obtain ⟨k,hk,hkn,hc⟩ := small_multiplier n hn
    exact ⟨k,hk,hkn,practical hk hkn hc⟩
  · intro n hn
    by_cases h : n = 48
    · subst n
      refine ⟨1, by decide, by decide, ?_⟩
      change IsPractical 48
      exact ⟨by decide, fun t _ ht => coverage (k := 48) (b := 48) (by decide +kernel) t ht⟩
    obtain ⟨k,hk,hkn,hc⟩ := half_multiplier n (by omega)
    exact ⟨k,hk,hkn,practical hk (by omega) hc⟩
