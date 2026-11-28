import OMAStatements.S_oeis_a299068

namespace OMA.P_oeis_a299068

lemma three_dvd (m : ℕ) : 3 ∣ m * (m + 1) * (m + 2) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h := Nat.mod_lt m (show 3 > 0 by norm_num)
  interval_cases hm : m % 3 <;> simp [Nat.mul_mod, Nat.add_mod, hm]

lemma mem {n N d e : ℕ} (hN : N ≠ 0) (he : d + n = e) (h1 : d ∣ N) (h2 : e ∣ N) :
    d ∈ N.divisors.filter (fun x => x + n ∣ N) :=
  Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨h1, hN⟩, he ▸ h2⟩

lemma seven_le (F : Finset ℕ) (x1 x2 x3 x4 x5 x6 x7 : ℕ)
    (h12 : x1 < x2) (h23 : x2 < x3) (h34 : x3 < x4) (h45 : x4 < x5) (h56 : x5 < x6)
    (h67 : x6 < x7) (m1 : x1 ∈ F) (m2 : x2 ∈ F) (m3 : x3 ∈ F) (m4 : x4 ∈ F) (m5 : x5 ∈ F)
    (m6 : x6 ∈ F) (m7 : x7 ∈ F) : 7 ≤ F.card := by
  have hS : ({x1, x2, x3, x4, x5, x6, x7} : Finset ℕ) ⊆ F := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hc : ({x1, x2, x3, x4, x5, x6, x7} : Finset ℕ).card = 7 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton] <;> simp <;> omega
  calc 7 = ({x1, x2, x3, x4, x5, x6, x7} : Finset ℕ).card := hc.symm
    _ ≤ F.card := Finset.card_le_card hS

end OMA.P_oeis_a299068

open OMA.P_oeis_a299068 in
theorem OMA.solution : type_of% @OMA.S_oeis_a299068.main := by
  intro n hn
  unfold OMA.S_oeis_a299068.a
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · -- `n = 2 * (j + 1)`
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have hj : 3 ≤ j := by omega
    have e : (2 * (j + 1)) ^ 2 - 1 = (2 * j + 1) * (2 * j + 3) := Nat.sub_eq_of_eq_add (by ring)
    rw [e]
    have hN : (2 * (j + 1)) ^ 2 * ((2 * j + 1) * (2 * j + 3)) ≠ 0 := by positivity
    obtain ⟨c, hc⟩ := three_dvd (2 * j + 1)
    have hP : (2 * (j + 1)) ^ 2 * ((2 * j + 1) * (2 * j + 3)) =
        2 * (j + 1) * ((2 * j + 1) * (2 * j + 1 + 1) * (2 * j + 1 + 2)) := by ring
    apply seven_le _ 1 (j + 1) (2 * (j + 1)) (4 * (j + 1)) ((j + 1) * (2 * j + 1))
      (2 * (j + 1) * (2 * j + 1)) ((2 * (j + 1)) ^ 2)
    · omega
    · omega
    · omega
    · nlinarith
    · nlinarith
    · nlinarith
    · exact mem hN (e := 2 * j + 3) (by ring) (one_dvd _)
        ⟨(2 * (j + 1)) ^ 2 * (2 * j + 1), by ring⟩
    · exact mem hN (e := 3 * (j + 1)) (by ring)
        ⟨4 * (j + 1) * ((2 * j + 1) * (2 * j + 3)), by ring⟩
        ⟨2 * c, by rw [hP, hc]; ring⟩
    · exact mem hN (e := 4 * (j + 1)) (by ring)
        ⟨2 * (j + 1) * ((2 * j + 1) * (2 * j + 3)), by ring⟩
        ⟨(j + 1) * ((2 * j + 1) * (2 * j + 3)), by ring⟩
    · exact mem hN (e := 6 * (j + 1)) (by ring)
        ⟨(j + 1) * ((2 * j + 1) * (2 * j + 3)), by ring⟩
        ⟨c, by rw [hP, hc]; ring⟩
    · exact mem hN (e := (j + 1) * (2 * j + 3)) (by ring)
        ⟨4 * (j + 1) * (2 * j + 3), by ring⟩
        ⟨4 * (j + 1) * (2 * j + 1), by ring⟩
    · exact mem hN (e := (2 * (j + 1)) ^ 2) (by ring)
        ⟨2 * (j + 1) * (2 * j + 3), by ring⟩
        ⟨(2 * j + 1) * (2 * j + 3), by ring⟩
    · exact mem hN (e := 2 * (j + 1) * (2 * j + 3)) (by ring)
        ⟨(2 * j + 1) * (2 * j + 3), by ring⟩
        ⟨2 * (j + 1) * (2 * j + 1), by ring⟩
  · -- `n = 2 * k + 1`
    have hk : 4 ≤ k := by omega
    have e : (2 * k + 1) ^ 2 - 1 = 4 * k * (k + 1) := Nat.sub_eq_of_eq_add (by ring)
    rw [e]
    have hN : (2 * k + 1) ^ 2 * (4 * k * (k + 1)) ≠ 0 := by positivity
    obtain ⟨c, hc⟩ := three_dvd (2 * k)
    have hP : (2 * k + 1) ^ 2 * (4 * k * (k + 1)) =
        (2 * k + 1) * (2 * k * (2 * k + 1) * (2 * k + 2)) := by ring
    apply seven_le _ 1 (2 * k + 1) (2 * (2 * k + 1)) (3 * (2 * k + 1)) (k * (2 * k + 1))
      (2 * k * (2 * k + 1)) ((2 * k + 1) ^ 2)
    · omega
    · omega
    · omega
    · nlinarith
    · nlinarith
    · nlinarith
    · exact mem hN (e := 2 * k + 2) (by ring) (one_dvd _)
        ⟨(2 * k + 1) ^ 2 * (2 * k), by ring⟩
    · exact mem hN (e := 2 * (2 * k + 1)) (by ring)
        ⟨(2 * k + 1) * (4 * k * (k + 1)), by ring⟩
        ⟨(2 * k + 1) * (2 * k * (k + 1)), by ring⟩
    · exact mem hN (e := 3 * (2 * k + 1)) (by ring)
        ⟨(2 * k + 1) * (2 * k * (k + 1)), by ring⟩
        ⟨c, by rw [hP, hc]; ring⟩
    · exact mem hN (e := 4 * (2 * k + 1)) (by ring)
        ⟨c, by rw [hP, hc]; ring⟩
        ⟨(2 * k + 1) * (k * (k + 1)), by ring⟩
    · exact mem hN (e := (k + 1) * (2 * k + 1)) (by ring)
        ⟨(2 * k + 1) * (4 * (k + 1)), by ring⟩
        ⟨(2 * k + 1) * (4 * k), by ring⟩
    · exact mem hN (e := (2 * k + 1) ^ 2) (by ring)
        ⟨(2 * k + 1) * (2 * (k + 1)), by ring⟩
        ⟨4 * k * (k + 1), by ring⟩
    · exact mem hN (e := (2 * k + 1) * (2 * k + 2)) (by ring)
        ⟨4 * k * (k + 1), by ring⟩
        ⟨(2 * k + 1) * (2 * k), by ring⟩
