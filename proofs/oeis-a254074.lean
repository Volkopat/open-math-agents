import OMAStatements.S_oeis_a254074

open OMA.S_oeis_a254074 in
theorem OMA.solution : type_of% @OMA.S_oeis_a254074.main := by
  intro n hn h5
  have hn₀ : n ≠ 0 := by
    intro he
    have h := hn.1.1
    simp [he] at h
  have hlast : n % 10 ∈ Nat.digits 10 n := by
    rw [Nat.digits_eq_cons_digits_div (by decide : 1 < 10) hn₀]
    exact List.mem_cons_self
  have hlo := (hn.1.2.2 _ hlast).1
  have hmod : n % 10 = 5 := by omega
  let q := n / 10
  have hrepr : n = 10 * q + 5 := by dsimp [q]; omega
  have hs : n ^ 2 = 5 + 10 * (2 + 10 * (q ^ 2 + q)) := by
    rw [hrepr]
    ring
  have hmem : 2 ∈ Nat.digits 10 (n ^ 2) := by
    rw [hs, Nat.digits_add 10 (by decide) 5 _ (by decide) (Or.inl (by decide)),
      Nat.digits_add 10 (by decide) 2 _ (by decide) (Or.inl (by decide))]
    simp
  have hn₂ := (hn.2.2.2 _ hmem).1
  omega