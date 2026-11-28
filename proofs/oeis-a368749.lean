import OMAStatements.S_oeis_a368749

/-- Consecutive offsets dividing a factorial give a product of two coprime factors above one. -/
private theorem factorial_block (M j : ℕ) (hj : 2 ≤ j) (hM : 0 < M) (hdiv : j ∣ M) :
    ¬ IsPrimePow (M ^ 2 + j) := by
  obtain ⟨k, rfl⟩ := hdiv
  have hk : 0 < k := Nat.pos_of_mul_pos_left hM
  let b := j * k ^ 2 + 1
  have hb : 1 < b := by
    dsimp [b]
    have : 0 < j * k ^ 2 := by positivity
    omega
  have cop : j.Coprime b := by simp [b]
  have he : (j * k) ^ 2 + j = j * b := by dsimp [b]; ring
  rw [he]
  intro h
  rcases (cop.isPrimePow_dvd_mul h).mp (dvd_refl _) with ha | hb'
  · have := Nat.le_of_dvd (by omega : 0 < j) ha
    nlinarith
  · have := Nat.le_of_dvd (by omega : 0 < b) hb'
    nlinarith

theorem OMA.solution : type_of% @OMA.S_oeis_a368749.main := by
  intro bound
  let M := (bound + 2).factorial
  let T := M ^ 2
  have hm : 0 < M := Nat.factorial_pos _
  have ht : 0 < T := by dsimp [T]; positivity
  have block (n : ℕ) (h₁ : T + 2 ≤ n) (h₂ : n ≤ T + bound + 1) : ¬ IsPrimePow n := by
    let j := n - T
    have hj : 2 ≤ j := by dsimp [j]; omega
    have hd : j ∣ M := Nat.dvd_factorial (by omega) (by dsimp [j]; omega)
    have e : M ^ 2 + j = n := by change T + (n - T) = n; omega
    exact e ▸ factorial_block M j hj hm hd
  let P := (Finset.Icc 2 (T + 1)).filter Nat.Prime
  have hP : P.Nonempty := ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by decide, by omega⟩, Nat.prime_two⟩⟩
  let p := P.max' hP
  have pmem := Finset.mem_filter.mp (P.max'_mem hP)
  have ple : p ≤ T + 1 := (Finset.mem_Icc.mp pmem.1).2
  have ex := Nat.exists_infinite_primes (T + 2)
  let q := Nat.find ex
  have hq : T + 2 ≤ q ∧ q.Prime := Nat.find_spec ex
  have above : T + bound + 1 < q := by
    by_contra! h
    exact block q hq.1 h hq.2.isPrimePow
  refine ⟨p, q, pmem.2, hq.2, by omega, ?_, ?_⟩
  · intro r hpr hrq hr
    by_cases hrT : r ≤ T + 1
    · have hm' : r ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hr.two_le, hrT⟩, hr⟩
      exact (Nat.not_le_of_lt hpr) (P.le_max' r hm')
    · exact (Nat.not_le_of_lt hrq) (Nat.find_min' ex ⟨by omega, hr⟩)
  · calc
      bound = (Finset.Icc (T + 2) (T + bound + 1)).card := by
        rw [Nat.card_Icc]
        omega
      _ ≤ _ := Finset.card_le_card (by
        intro n hn
        obtain ⟨h₁, h₂⟩ := Finset.mem_Icc.mp hn
        exact Finset.mem_filter.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega, by omega⟩, block n h₁ h₂⟩)
