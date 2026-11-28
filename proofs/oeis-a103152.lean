import OMAStatements.S_oeis_a103152
import Mathlib

namespace OMA.S_oeis_a103152

def M : ℕ := 2760529851718890358268076798578308459400086460667767524382036453062798643029691111456041629571334607485359782341806658644021097812034336826194874419862978234595417052425593627301893980692263665201876798434959239555244

lemma primeBit : ∀ n < 726, (n.Prime ↔ Nat.testBit M n = true) := by
  decide +kernel

def rep' (m : ℕ) : ℕ :=
  ((Finset.range (m / 2 + 1)).filter fun p =>
    Nat.testBit M p = true ∧ p % 2 = 1 ∧ Nat.testBit M (m - 2 * p) = true ∧ (m - 2 * p) % 2 = 1).card

lemma rep_eq (m : ℕ) (hm : m < 726) : representations m = rep' m := by
  unfold representations rep'
  congr 1
  apply Finset.filter_congr
  intro p hp
  have hp' : p < 726 := by simp at hp; omega
  have h2 : m - 2 * p < 726 := by omega
  rw [primeBit p hp', primeBit _ h2, Nat.odd_iff, Nat.odd_iff]

lemma rep725 : representations 725 = 23 := by
  rw [rep_eq _ (by norm_num)]; decide +kernel

lemma low : ∀ m < 726, Odd m ∧ representations m = 23 → m = 725 := by
  intro m hm ⟨ho, hr⟩
  rw [rep_eq m hm] at hr
  revert m
  decide +kernel

lemma a23 : a 23 = 725 := by
  have hmem : (725 : ℕ) ∈ {m : ℕ | Odd m ∧ representations m = 23} :=
    ⟨by decide, rep725⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · have h := Nat.sInf_mem (s := {m : ℕ | Odd m ∧ representations m = 23}) ⟨_, hmem⟩
    have hle : sInf {m : ℕ | Odd m ∧ representations m = 23} ≤ 725 := Nat.sInf_le hmem
    have := low _ (by omega) h
    show 725 ≤ sInf {m : ℕ | Odd m ∧ representations m = 23}
    omega

end OMA.S_oeis_a103152

open OMA.S_oeis_a103152 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a103152.main) := by
  intro h
  have := h 23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [a23] at this
  revert this
  decide
