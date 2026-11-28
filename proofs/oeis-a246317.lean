import OMAStatements.S_oeis_a246317
import Mathlib

namespace OMA.A246317Proof

open OMA.S_oeis_a246317

/-- The rule `r` agrees with rule 324 on every bit except bits 3, 5, 7 and 9. -/
def Good (r : ℕ) : Prop :=
  ∀ m : ℕ, m ≠ 3 → m ≠ 5 → m ≠ 7 → m ≠ 9 → r.testBit m = (324 : ℕ).testBit m

/-- Checkerboard invariant at stage `t`: every ON cell `(x, y)` has `x + y + t` even. -/
def Inv (t : ℕ) (S : Finset (ℤ × ℤ)) : Prop :=
  ∀ p ∈ S, (p.1 + p.2 + (t : ℤ)) % 2 = 0

lemma good_of_lt (r : ℕ) (hr : r < 1024)
    (h : ∀ m < 10, m ≠ 3 → m ≠ 5 → m ≠ 7 → m ≠ 9 → r.testBit m = (324 : ℕ).testBit m) : Good r := by
  intro m h3 h5 h7 h9
  by_cases hm : m < 10
  · exact h m hm h3 h5 h7 h9
  · have h2 : 2 ^ 10 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2' : (1024 : ℕ) ≤ 2 ^ m := by simpa using h2
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hr h2'),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (by norm_num) h2')]

lemma nbr_sum {p q : ℤ × ℤ} (h : q ∈ nbrs p) :
    q.1 + q.2 = p.1 + p.2 + 1 ∨ q.1 + q.2 = p.1 + p.2 - 1 := by
  simp only [nbrs, Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff] at h
  omega

lemma card_zero_of_mem {t : ℕ} {S : Finset (ℤ × ℤ)} {p : ℤ × ℤ} (hS : Inv t S) (hp : p ∈ S) :
    (nbrs p ∩ S).card = 0 := by
  by_contra h
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_inter] at hq
  have h1 := hS q hq.2
  have h2 := hS p hp
  have h3 := nbr_sum hq.1
  omega

lemma step_eq (r : ℕ) (hr : Good r) (t : ℕ) (S : Finset (ℤ × ℤ)) (hS : Inv t S) :
    step r S = step 324 S := by
  unfold step
  apply Finset.filter_congr
  intro p _
  by_cases hpS : p ∈ S
  · rw [if_pos hpS, card_zero_of_mem hS hpS]
    rw [hr (2 * 0 + 1) (by omega) (by omega) (by omega) (by omega)]
  · rw [if_neg hpS]
    rw [hr (2 * (nbrs p ∩ S).card + 0) (by omega) (by omega) (by omega) (by omega)]

lemma step_inv (t : ℕ) (S : Finset (ℤ × ℤ)) (hS : Inv t S) : Inv (t + 1) (step 324 S) := by
  intro p hp
  unfold step at hp
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hb⟩ := hp
  by_cases hpS : p ∈ S
  · rw [if_pos hpS, card_zero_of_mem hS hpS] at hb
    exact absurd hb (by decide)
  · rw [if_neg hpS] at hb
    have hk : 0 < (nbrs p ∩ S).card := by
      rcases Nat.eq_zero_or_pos (nbrs p ∩ S).card with h | h
      · rw [h] at hb
        exact absurd hb (by decide)
      · exact h
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hk
    rw [Finset.mem_inter] at hq
    have h1 := hS q hq.2
    have h2 := nbr_sum hq.1
    push_cast
    omega

lemma stage_eq (r : ℕ) (hr : Good r) (t : ℕ) : stage r t = stage 324 t ∧ Inv t (stage 324 t) := by
  induction t with
  | zero =>
    refine ⟨rfl, ?_⟩
    intro p hp
    change p ∈ ({(0, 0)} : Finset (ℤ × ℤ)) at hp
    rw [Finset.mem_singleton] at hp
    subst hp
    norm_num
  | succ t ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : stage r (t + 1) = step r (stage r t) := Function.iterate_succ_apply' _ _ _
    have e2 : stage 324 (t + 1) = step 324 (stage 324 t) := Function.iterate_succ_apply' _ _ _
    rw [e1, e2, h1, step_eq r hr t _ h2]
    exact ⟨rfl, step_inv t _ h2⟩

lemma good_of_mem (r : ℕ)
    (hr : r ∈ ({332, 356, 364, 452, 460, 484, 492, 836, 844, 868, 876, 964, 972, 996, 1004} : Finset ℕ)) :
    Good r := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact good_of_lt _ (by norm_num) (by decide)

end OMA.A246317Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a246317.main := by
  intro r hr n
  show (OMA.S_oeis_a246317.stage r (2 ^ n - 1)).card =
    (OMA.S_oeis_a246317.stage 452 (2 ^ n - 1)).card
  rw [(OMA.A246317Proof.stage_eq r (OMA.A246317Proof.good_of_mem r hr) _).1,
    (OMA.A246317Proof.stage_eq 452 (OMA.A246317Proof.good_of_lt 452 (by norm_num) (by decide)) _).1]
