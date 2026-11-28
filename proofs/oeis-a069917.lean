import OMAStatements.S_oeis_a069917

lemma OMA.properDivisors_1749715 :
    (1749715 : ℕ).properDivisors =
      {1, 5, 11, 29, 55, 145, 319, 1097, 1595, 5485, 12067, 31813, 60335, 159065, 349943} := by
  ext d
  constructor
  · intro h
    obtain ⟨hd, hlt⟩ := Nat.mem_properDivisors.mp h
    change d ∣ (5 * 11) * (29 * 1097) at hd
    obtain ⟨a, b, ha, hb, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ha
    obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hb
    rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 5)).mp ha₁ with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 11)).mp ha₂ with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 29)).mp hb₁ with rfl | rfl <;>
    rcases (Nat.dvd_prime (by decide +kernel : Nat.Prime 1097)).mp hb₂ with rfl | rfl <;>
    norm_num at hlt <;> norm_num
  · intro h
    fin_cases h <;> rw [Nat.mem_properDivisors] <;> norm_num

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a069917.main) := by
  intro h
  have hp : OMA.S_oeis_a069917.IsBase6PicturePerfect 1749715 := by
    constructor
    · norm_num
    · rw [OMA.properDivisors_1749715]
      decide +kernel
  have hn : (Nat.digits 10 1749715).sum ≠ 10 := by decide +kernel
  exact hn (h 1749715 hp)

