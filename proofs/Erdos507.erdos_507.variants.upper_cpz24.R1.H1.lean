import OMAReductions.R_Erdos507_erdos_507_variants_upper_cpz24_R1

-- Proof of Erdos507.erdos_507.variants.upper_cpz24.R1.H1 (elementary packing in the disk).
-- Grid pigeonhole: cut [-1,1]^2 into (2M+1)^2 cells of side 1/M (floor of M times each
-- coordinate). Any set of more than (2M+1)^2 points has two distinct points in one cell.
-- Remove such a pair and repeat (greedy pairing), giving n/8 disjoint pairs as long as
-- (2M+1)^2 + 2 (n/8) is at most n. Take M = (Nat.sqrt n)/4; then 1/M is at most 8/sqrt n.

namespace E507H1

open Filter
open scoped EuclideanGeometry

/-- Greedy pairing: if every large subset of `S` contains two distinct related points, then a
subset of `S` with at least `c + 2 j` points contains `j` disjoint related pairs. -/
theorem greedy_pairs {α : Type*} [DecidableEq α] (S : Finset α) (R : α → α → Prop) (c : ℕ)
    (hR : ∀ T : Finset α, T ⊆ S → c < T.card → ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ R x y) :
    ∀ j : ℕ, ∀ T : Finset α, T ⊆ S → c + 2 * j ≤ T.card →
      ∃ p : Fin j × Bool → α, Function.Injective p ∧ (∀ k, p k ∈ T) ∧
        ∀ i, R (p (i, true)) (p (i, false)) := by
  intro j
  induction j with
  | zero =>
    intro T _ _
    exact ⟨fun k => k.1.elim0, fun a _ _ => a.1.elim0, fun k => k.1.elim0, fun i => i.elim0⟩
  | succ j ih =>
    intro T hT hc
    obtain ⟨x, hx, y, hy, hxy, hRxy⟩ := hR T hT (by omega)
    have hyx : y ∈ T.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
    have hcard : ((T.erase x).erase y).card + 2 = T.card := by
      rw [Finset.card_erase_of_mem hyx, Finset.card_erase_of_mem hx]
      omega
    obtain ⟨q, hqi, hqm, hqR⟩ := ih ((T.erase x).erase y)
      (fun z hz => hT (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hz))) (by omega)
    have hqT : ∀ k, q k ∈ T := fun k =>
      Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (hqm k))
    have hqx : ∀ k, q k ≠ x := fun k h => by
      have h' := hqm k
      rw [h] at h'
      simp at h'
    have hqy : ∀ k, q k ≠ y := fun k h => by
      have h' := hqm k
      rw [h] at h'
      simp at h'
    let p : Fin (j + 1) × Bool → α := fun k =>
      Fin.cases (motive := fun _ => α) (if k.2 then x else y) (fun i => q (i, k.2)) k.1
    refine ⟨p, ?_, ?_, ?_⟩
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      cases a using Fin.cases <;> cases a' using Fin.cases <;> cases b <;> cases b' <;>
        simp only [p, Fin.cases_zero, Fin.cases_succ, Bool.false_eq_true, if_true,
          if_false] at h
      all_goals first
        | rfl
        | exact absurd h hxy
        | exact absurd h.symm hxy
        | exact absurd h.symm (hqx _)
        | exact absurd h.symm (hqy _)
        | exact absurd h (hqx _)
        | exact absurd h (hqy _)
        | (have h2 := hqi h
           simp only [Prod.mk.injEq] at h2
           rcases h2 with ⟨rfl, h3⟩
           first | rfl | exact absurd h3 (by decide))
    · rintro ⟨a, b⟩
      cases a using Fin.cases <;> cases b <;>
        simp only [p, Fin.cases_zero, Fin.cases_succ, Bool.false_eq_true, if_true, if_false]
      · exact hy
      · exact hx
      · exact hqT _
      · exact hqT _
    · intro i
      cases i using Fin.cases
      · simpa [p] using hRxy
      · simpa [p] using hqR _

/-- Grid pigeonhole in the unit disk with cells of side `1/M`. -/
theorem close_pair (M : ℕ) (hM : 0 < M) (T : Finset ℝ²)
    (hT : (T : Set ℝ²) ⊆ Metric.closedBall 0 1) (hc : (2 * M + 1) ^ 2 < T.card) :
    ∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ ∀ k : Fin 2, |x k - y k| ≤ 1 / (M : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let f : ℝ² → ℤ × ℤ := fun x => (⌊x 0 * M⌋, ⌊x 1 * M⌋)
  let C : Finset (ℤ × ℤ) := Finset.Icc (-(M : ℤ)) M ×ˢ Finset.Icc (-(M : ℤ)) M
  have hCc : C.card = (2 * M + 1) ^ 2 := by
    have h1 : ((M : ℤ) + 1 - -(M : ℤ)).toNat = 2 * M + 1 := by omega
    simp only [C, Finset.card_product, Int.card_Icc, h1]
    ring
  have hcoord : ∀ x ∈ T, ∀ k : Fin 2, |x k| ≤ 1 := by
    intro x hx k
    have h1 : ‖x‖ ≤ 1 := by
      have := hT hx
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact this
    have h2 := PiLp.norm_apply_le x k
    rw [Real.norm_eq_abs] at h2
    linarith
  have hfl : ∀ a : ℝ, |a| ≤ 1 → ⌊a * M⌋ ∈ Finset.Icc (-(M : ℤ)) M := by
    intro a ha
    rw [abs_le] at ha
    rw [Finset.mem_Icc]
    constructor
    · rw [Int.le_floor]
      push_cast
      nlinarith
    · have h3 := Int.floor_le (a * M)
      have h2 : ((⌊a * M⌋ : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by
        push_cast
        nlinarith
      exact_mod_cast h2
  have hmaps : Set.MapsTo f T C := fun x hx =>
    Finset.mem_product.mpr ⟨hfl _ (hcoord x hx 0), hfl _ (hcoord x hx 1)⟩
  obtain ⟨x, hx, y, hy, hne, hxy⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (by rw [hCc]; exact hc) hmaps
  refine ⟨x, hx, y, hy, hne, fun k => ?_⟩
  have hk : ⌊x k * M⌋ = ⌊y k * M⌋ := by
    fin_cases k
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  have h := Int.abs_sub_lt_one_of_floor_eq_floor hk
  rw [← sub_mul, abs_mul, abs_of_pos hMr] at h
  rw [le_div_iff₀ hMr]
  linarith

theorem packing : OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1.H1 := by
  classical
  refine ⟨8, by norm_num, ?_⟩
  filter_upwards [eventually_ge_atTop 256] with n hn
  intro S hS hball
  have hs16 : 16 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
  have hsn : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hM4 : 4 ≤ Nat.sqrt n / 4 := by omega
  have hsM : Nat.sqrt n ≤ 4 * (Nat.sqrt n / 4) + 3 := by omega
  have hMs : 4 * (Nat.sqrt n / 4) ≤ Nat.sqrt n := Nat.mul_div_le _ _
  have h8 : n / 8 * 8 ≤ n := Nat.div_mul_le_self n 8
  have hsq2 : (4 * (Nat.sqrt n / 4) + 2) ^ 2 ≤ (Nat.sqrt n + 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hcount : (2 * (Nat.sqrt n / 4) + 1) ^ 2 + 2 * (n / 8) ≤ n := by
    nlinarith
  obtain ⟨p, hpi, hpm, hpR⟩ := greedy_pairs S
    (fun x y => ∀ k : Fin 2, |x k - y k| ≤ 1 / ((Nat.sqrt n / 4 : ℕ) : ℝ))
    ((2 * (Nat.sqrt n / 4) + 1) ^ 2)
    (fun T hT hc => close_pair (Nat.sqrt n / 4) (by omega) T
      (fun z hz => hball (hT hz)) hc) (n / 8) S le_rfl (by omega)
  refine ⟨⟨p, hpi⟩, hpm, fun j k => ?_⟩
  refine (hpR j k).trans ?_
  rw [← Real.sqrt_eq_rpow]
  have hsq : √(n : ℝ) < (Nat.sqrt n : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
  have hMr : (4 : ℝ) ≤ ((Nat.sqrt n / 4 : ℕ) : ℝ) := by exact_mod_cast hM4
  have hsMr : (Nat.sqrt n : ℝ) ≤ 4 * ((Nat.sqrt n / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast hsM
  have hpos : 0 < √(n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < n by omega))
  rw [div_le_div_iff₀ (by linarith) hpos]
  linarith

end E507H1

/-- Proof of the step Erdos507.erdos_507.variants.upper_cpz24.R1.H1. -/
theorem OMA.solution : OMA.R_Erdos507_erdos_507_variants_upper_cpz24_R1.H1 := E507H1.packing

