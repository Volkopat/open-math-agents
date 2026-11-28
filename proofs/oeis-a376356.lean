import OMAStatements.S_oeis_a376356
import Mathlib.Tactic

/-!
In each triangular block the terminal digits copy an initial segment. Ending a block just before a repeat of the digit extends the old gap by that digit. This yields the complete set of gaps.
-/

namespace TwoGaps
open OMA.S_oeis_a376356

private theorem tri_succ (k : ℕ) : triangular (k+1) = triangular k + (k+1) := by
  unfold triangular
  have e : (k+1)*(k+1+1) = k*(k+1)+2*(k+1) := by ring
  rw [e]
  omega

private theorem tri_mono : Monotone triangular := by
  apply monotone_nat_of_le_succ
  intro k
  rw [tri_succ]
  omega

private theorem above_index (k : ℕ) : k < triangular (k+1) := by
  rw [tri_succ]
  omega

private theorem cutoff (n : ℕ) : n < triangular (Nat.sqrt (2*n)+1+1) := by
  let s := Nat.sqrt (2*n)
  have hs : 2*n < (s+1)*(s+1) := Nat.lt_succ_sqrt _
  change n < (s+1+1)*(s+1+1+1)/2
  have : 2*n+2 ≤ (s+1+1)*(s+1+1+1) := by nlinarith
  omega

private theorem stable (n k : ℕ) (hk : 1 ≤ k) (hn : n < triangular (k+1))
    (l : ℕ) (hl : k ≤ l) : descend n l = descend n k := by
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l hl ih =>
    have ht := lt_of_lt_of_le hn (tri_mono (Nat.succ_le_succ hl))
    cases l with
    | zero => omega
    | succ j => simpa only [descend, Nat.mod_eq_of_lt ht] using ih

private theorem digit_at (n k : ℕ) (hk : 1 ≤ k) (hn : n < triangular (k+1)) :
    digit n = descend n k := by
  let l := max k (Nat.sqrt (2*n)+1)
  exact (stable n _ (by omega) (cutoff n) l (le_max_right ..)).symm.trans
    (stable n k hk hn l (le_max_left ..))

private theorem descend_zero (k : ℕ) : descend 0 k = 0 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 | 1 => rfl
    | j+2 => simpa only [descend, Nat.zero_mod] using ih (j+1) (by omega)

private theorem descend_step (n k : ℕ) :
    descend (n+1) k = 0 ∨ descend (n+1) k = descend n k + 1 := by
  induction k using Nat.strong_induction_on generalizing n with
  | h k ih =>
    match k with
    | 0 | 1 => exact Or.inr rfl
    | j+2 =>
      let t := triangular (j+2)
      have ht : 0 < t := lt_trans (by omega : 0 < j+1) (above_index (j+1))
      have hm := Nat.mod_lt n ht
      change descend ((n+1)%t) (j+1) = 0 ∨
        descend ((n+1)%t) (j+1) = descend (n%t) (j+1) + 1
      rw [Nat.add_mod n 1 t]
      by_cases h : n%t+1 < t
      · have ht1 : 1 < t := by omega
        rw [Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt h]
        exact ih (j+1) (by omega) _
      · have ht1 : 1 < t := lt_of_le_of_lt (by omega : 1 ≤ j+1) (above_index (j+1))
        rw [Nat.mod_eq_of_lt ht1, show n%t+1=t by omega, Nat.mod_self, descend_zero]
        exact Or.inl rfl

private theorem digit_step (n : ℕ) : digit (n+1) = 0 ∨ digit (n+1) = digit n+1 := by
  have hs := above_index (n+2)
  rw [digit_at (n+1) (n+2) (by omega) (by omega), digit_at n (n+2) (by omega) (by omega)]
  exact descend_step n (n+2)

private theorem small_digit {n : ℕ} (hn : n ≤ 16) : digit n = descend n 6 :=
  digit_at n 6 (by decide) (lt_of_le_of_lt hn (by decide))

private theorem tri_large (k : ℕ) (hk : 2 ≤ k) : k < triangular k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  rw [tri_succ (j+1)]
  have := above_index j
  omega

private theorem copy_prefix (k r : ℕ) (hk : 2 ≤ k) (hr : r ≤ k) :
    digit (triangular k+r) = digit r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j+2 := ⟨k-2, by omega⟩
  have ht := tri_large (j+2) (by omega)
  have hr' : r < triangular (j+2) := by omega
  rw [digit_at _ (j+2) (by omega) (by rw [tri_succ (j+2)]; omega)]
  change descend ((triangular (j+2)+r) % triangular (j+2)) (j+1) = digit r
  rw [Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr']
  exact (digit_at r (j+1) (by omega) hr').symm

/-- Copy the old gap to the end of a triangular block, followed by the next block's first digit d. -/
private theorem extend_gap {d a b : ℕ} (hd : 1 ≤ d ∧ d ≤ 2) (hb : 3 ≤ b)
    (h : Consecutive d a b) :
    ∃ x y, Consecutive d x y ∧ y-x = (b-a)+d ∧ 3 ≤ y := by
  obtain ⟨k, rfl⟩ : ∃ k, b=k+1 := ⟨b-1, by omega⟩
  obtain ⟨ha, hab, hda, _, hbetween⟩ := h
  have hk : 2 ≤ k := by omega
  have hdigit (j : ℕ) (hj : j ≤ 2) : digit j = j := by
    interval_cases j <;> rw [small_digit (by decide)] <;> decide
  refine ⟨triangular k+a, triangular (k+1)+d, ⟨by omega, by rw [tri_succ]; omega, ?_, ?_, ?_⟩,
    by rw [tri_succ]; omega, by rw [tri_succ]; omega⟩
  · rw [copy_prefix _ _ hk (by omega), hda]
  · rw [copy_prefix _ _ (by omega) (by omega), hdigit d hd.2]
  · intro m hm
    rw [Finset.mem_Ioo] at hm
    by_cases hlast : m < triangular (k+1)
    · let j := m-triangular k
      have ej : m = triangular k+j := by dsimp [j]; omega
      rw [tri_succ] at hlast
      have hj : j ≤ k := by omega
      rw [ej, copy_prefix _ _ hk hj]
      exact hbetween j (Finset.mem_Ioo.mpr (by omega))
    · let j := m-triangular (k+1)
      have ej : m = triangular (k+1)+j := by dsimp [j]; omega
      have hj : j < d := by omega
      rw [ej, copy_prefix _ _ (by omega) (by omega), hdigit j (by omega)]
      omega

private def Realized (g : ℕ) : Prop :=
  ∃ a b, Consecutive 2 a b ∧ b-a=g ∧ 3 ≤ b

private theorem seed3 : Realized 3 := by
  refine ⟨2, 5, ⟨by decide, by decide, by rw [small_digit (by decide)]; decide, by rw [small_digit (by decide)]; decide, ?_⟩, rfl, by decide⟩
  intro j hj
  rw [Finset.mem_Ioo] at hj
  obtain ⟨lo, hi⟩ := hj
  interval_cases j <;> rw [small_digit (by decide)] <;> decide

private theorem seed4 : Realized 4 := by
  refine ⟨8, 12, ⟨by decide, by decide, by rw [small_digit (by decide)]; decide, by rw [small_digit (by decide)]; decide, ?_⟩, rfl, by decide⟩
  intro j hj
  rw [Finset.mem_Ioo] at hj
  obtain ⟨lo, hi⟩ := hj
  interval_cases j <;> rw [small_digit (by decide)] <;> decide

private theorem next_gap {g : ℕ} (h : Realized g) : Realized (g+2) := by
  obtain ⟨a, b, hab, rfl, hb⟩ := h
  exact extend_gap (by omega) hb hab

private theorem all_large (g : ℕ) (hg : 3 ≤ g) : Realized g := by
  induction g using Nat.strong_induction_on with
  | h g ih =>
    by_cases small : g < 5
    · interval_cases g <;> first | exact seed3 | exact seed4
    · have e : g-2+2 = g := by omega
      simpa only [e] using next_gap (ih (g-2) (by omega) (by omega))

/-- Exact positive gaps between successive occurrences of the terminal digit 2. -/
theorem gaps : {g : ℕ | ∃ a b, Consecutive 2 a b ∧ g = b-a} = {g | 3 ≤ g} := by
  ext g
  constructor
  · rintro ⟨a, b, ⟨_, hab, h₁, h₂, _⟩, rfl⟩
    change 3 ≤ b-a
    have s₁ := digit_step a
    have s₂ := digit_step (a+1)
    change digit (a+2)=0 ∨ digit (a+2)=digit (a+1)+1 at s₂
    by_contra! h
    have e : b=a+1 ∨ b=a+2 := by omega
    rcases e with rfl|rfl
    · rcases s₁ with s₁|s₁ <;> omega
    · rcases s₁ with s₁|s₁ <;> rcases s₂ with s₂|s₂ <;> omega
  · intro hg
    obtain ⟨a,b,hab,e,_⟩ := all_large g hg
    exact ⟨a,b,hab,e.symm⟩

end TwoGaps

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a376356.main) := by
  intro h
  rw [TwoGaps.gaps] at h
  have hm : 10 ∈ ({g : ℕ | 3 ≤ g}) := by decide
  rw [h] at hm
  norm_num at hm
