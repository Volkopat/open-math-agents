import OMAReductions.R_Erdos980_erdos_980_R1

/-!
# Erdős 980 fixed-pattern densities: upward patterns and strictness

The Chebotarev input is cleaner when stated for upward residue patterns:
the first `r` rational primes are all `k`-th power residues.  The exact
fixed pattern in the parent step is the difference of two consecutive upward
patterns.  Positivity of the first exact density is the separate Kummer
independence input that adjoining the first radical strictly lowers the
complete-splitting density.
-/

open Filter
open scoped Topology Classical

namespace OMA.R_Erdos980_erdos_980_R1_H1_R1

/-- Chebotarev input: every upward Kummer-residue pattern has a natural
density on the prime-number-theorem scale. -/
def H1 : Prop := ∀ k : ℕ, 2 ≤ k → ∃ c : ℕ → ℝ, ∀ r : ℕ,
  Tendsto (fun x : ℝ ↦ ((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < r, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) * (Real.log x / x))
    atTop (𝓝 (c r))

/-- Kummer-independence input: the first radical strictly lowers the
complete-splitting density.  Equivalently, the first exact pattern has
positive density. -/
def H2 : Prop := ∀ k : ℕ, ∀ c : ℕ → ℝ, 2 ≤ k →
  (∀ r : ℕ, Tendsto (fun x : ℝ ↦ ((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < r, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) * (Real.log x / x))
    atTop (𝓝 (c r))) →
  c 1 < c 0

lemma upward_succ_iff (k p i : ℕ) :
    (p % k = 1 ∧ ∀ j < i + 1, ∃ y : ZMod p,
      y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ↔
    (p % k = 1 ∧ ∀ j < i, ∃ y : ZMod p,
      y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
      (∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p)) := by
  constructor
  · intro h
    refine ⟨⟨h.1, fun j hj ↦ h.2 j (hj.trans (Nat.lt_succ_self i))⟩,
      h.2 i (Nat.lt_succ_self i)⟩
  · rintro ⟨hprev, hi⟩
    refine ⟨hprev.1, fun j hj ↦ ?_⟩
    by_cases hji : j = i
    · subst hji
      exact hi
    · exact hprev.2 j (by omega)

lemma upwardCount_mono_succ (k i : ℕ) (x : ℝ) :
    (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) ≤ (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) := by
  classical
  apply Finset.card_le_card
  intro p hp
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, (upward_succ_iff k p i).mp hp.2 |>.1⟩

lemma exactCount_eq_sub (k i : ℕ) (x : ℝ) :
    (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
      (∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p)).card : ℝ) =
    ((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) - (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) := by
  classical
  let P := Nat.primesBelow ⌈x⌉₊
  let res : ℕ → Prop := fun p ↦ ∃ y : ZMod p,
    y ^ k = (Nat.nth Nat.Prime i : ZMod p)
  let Ui : Finset ℕ := P.filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)
  have hexact : (P.filter fun p ↦ p % k = 1 ∧
      (∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p)) =
      Ui.filter fun p ↦ ¬ res p := by
    symm
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  have hsucc : Ui.filter res = P.filter fun p ↦ p % k = 1 ∧
      ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p) := by
    rw [Finset.filter_filter]
    apply Finset.filter_congr
    intro p hp
    exact (upward_succ_iff k p i).symm
  have hcard := Finset.card_filter_add_card_filter_not (s := Ui) res
  rw [hsucc] at hcard
  have hnat : (Ui.filter fun p ↦ ¬ res p).card =
      (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) - (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) := by
    dsimp [P, Ui] at hcard ⊢
    omega
  calc
    (((P.filter fun p ↦ p % k = 1 ∧
      (∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
      ¬ ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p)).card : ℝ))
        = ((Ui.filter fun p ↦ ¬ res p).card : ℝ) := by rw [hexact]
    _ = (((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) - (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = ((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) - (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) := by
        exact Nat.cast_sub (upwardCount_mono_succ k i x)

theorem main : H1 → H2 → OMA.R_Erdos980_erdos_980_R1.H1 := by
  classical
  intro h1 h2 k hk
  obtain ⟨c, hc⟩ := h1 k hk
  have hstrict : c 1 < c 0 := h2 k c hk hc
  refine ⟨fun i ↦ c i - c (i + 1), ?_, ?_⟩
  · simpa using sub_pos.mpr hstrict
  · intro i
    have hsub := (hc i).sub (hc (i + 1))
    refine hsub.congr' ?_
    exact Eventually.of_forall fun x ↦ by
      calc
        ((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) * (Real.log x / x) -
            ((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) * (Real.log x / x)
            = (((((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card) : ℝ) - (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
    ∀ j < i + 1, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)).card)) *
              (Real.log x / x) := by ring
        _ = (((Nat.primesBelow ⌈x⌉₊).filter fun p ↦ p % k = 1 ∧
              (∀ j < i, ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime j : ZMod p)) ∧
              ¬ ∃ y : ZMod p, y ^ k = (Nat.nth Nat.Prime i : ZMod p)).card : ℝ) *
              (Real.log x / x) := by
              rw [← exactCount_eq_sub k i x]

end OMA.R_Erdos980_erdos_980_R1_H1_R1
