import OMAReductions.R_OeisA247824_conjecture_2_R2_H4_R1

/-! The first three bounds can be checked independently.
The remaining five bounds are recorded individually. -/

namespace OMA.R_OeisA247824_conjecture_2_R2_H4_R1_H1_R1

private theorem count_le (n : ℕ) : Nat.primeCounting n ≤ n := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  have sub : Nat.primesLE n ⊆ Finset.Icc 1 n := fun p hp =>
    Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primesLE hp).pos, Nat.le_of_mem_primesLE hp⟩
  simpa using Finset.card_le_card sub

def H1 : Prop := Nat.primeCounting 94085731 = 5439846

def H2 : Prop := 30841324 ≤ Nat.primeCounting 590237761

def H3 : Prop := 473516370 ≤ Nat.primeCounting 10425579253

def H4 : Prop :=
  Nat.primeCounting 28006150079 ≤ 1217243859 ∧
  8190661670 ≤ Nat.primeCounting 204778727327 ∧
  21351698637 ≤ Nat.primeCounting 555157672301 ∧
  (382482495195 ≤ Nat.primeCounting 11092009835083 ∧
    Nat.primeCounting 11092009835083 ≤ 382482495196) ∧
  Nat.primeCounting 30110134441897 ≤ 1003670521508

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA247824_conjecture_2_R2_H4_R1.H1 := by
  intro a b c rest k
  change Nat.primeCounting 94085731 = 5439846 at a
  obtain ⟨d,e,f,g,h⟩ := rest
  dsimp only
  split
  · exact ⟨a.ge,a.le⟩
  · exact ⟨b,count_le _⟩
  · exact ⟨c,count_le _⟩
  · exact ⟨Nat.zero_le _,d⟩
  · exact ⟨e,count_le _⟩
  · exact ⟨f,count_le _⟩
  · exact g
  · exact ⟨Nat.zero_le _,h⟩
  · decide

end OMA.R_OeisA247824_conjecture_2_R2_H4_R1_H1_R1
