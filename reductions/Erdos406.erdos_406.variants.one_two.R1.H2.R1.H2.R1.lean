import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1

namespace OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1_H2_R1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
private theorem seed : ∀ i : Fin 32, (2^82286 / 3^i.val)%3 ≠ 0 := by
  decide +kernel

/- At width 32, exponent 82286 has a zero-free suffix. Hence only
exponents below twice 82286 can satisfy the no-predecessor condition.
A modular doubling scan finds only 82286 itself survives the low 32
digits on this interval, and digit 32 of that power is zero. -/
def H1 : Prop := ∀ k : ℕ, 4096 ≤ k → k < 164572 →
  ∃ i < 64, (2^k / 3^i)%3 = 0

/-- Only the first exponent with a zero-free doubled suffix needs a predecessor. -/
def H2 : Prop := ∀ j t : ℕ, 6 ≤ j →
  let r := 2^j
  t < 2*3^(r-1) →
  (∀ i < 2*r, (2^t / 3^i)%3 ≠ 0) →
  (∀ s < t, ∃ i < 2*r, (2^s / 3^i)%3 = 0) →
  ∃ l, 2*l ≤ t ∧ ∀ i < r, (2^l / 3^i)%3 ≠ 0

theorem main : H1 → H2 → OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1.H2 := by
  classical
  intro small recordGap j k hj hk width period low prior
  dsimp [width] at period low prior ⊢
  by_cases five : j = 5
  · subst j
    have bound : k < 164572 := by
      by_contra! h
      obtain ⟨i, hi, hz⟩ := prior 82286 (by omega)
      exact seed ⟨i, hi⟩ hz
    obtain ⟨i, hi, hz⟩ := small k hk bound
    have hlow : 32 ≤ i := by
      by_contra! h
      exact low i h hz
    exact ⟨i, hlow, hi, hz⟩
  · by_contra! noZero
    let good := fun s : ℕ => ∀ i < 2*(2^j), (2^s / 3^i)%3 ≠ 0
    have gk : good k := by
      intro i hi
      by_cases h : i < 2^j
      · exact low i h
      · exact noZero i (by omega) hi
    have ex : ∃ s, good s := ⟨k, gk⟩
    have hle : Nat.find ex ≤ k := Nat.find_min' ex gk
    have earlier : ∀ s < Nat.find ex, ∃ i < 2*(2^j), (2^s / 3^i)%3 = 0 := by
      intro s hs
      have hn : ¬ good s := Nat.find_min ex hs
      unfold good at hn
      push_neg at hn
      exact hn
    obtain ⟨l, half, clear⟩ := recordGap j (Nat.find ex) (by omega)
      (lt_of_le_of_lt hle period) (Nat.find_spec ex) earlier
    obtain ⟨i, hi, hz⟩ := prior l (by omega)
    exact clear i hi hz

end OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1_H2_R1
