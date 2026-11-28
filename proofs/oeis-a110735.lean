import OMAStatements.S_oeis_a110735

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a110735.main) := by
  intro h
  obtain ⟨gaps, hlen, hbd, hlast, hdvd⟩ := h 101 (by decide)
  have hd : Nat.digits 10 101 = [1, 0, 1] := by decide
  rw [hd] at hlen hdvd
  have hglen : gaps.length = 4 := by simpa using hlen
  rcases gaps with _ | ⟨a, gaps⟩
  · simp at hglen
  rcases gaps with _ | ⟨b, gaps⟩
  · simp at hglen
  rcases gaps with _ | ⟨c, gaps⟩
  · simp at hglen
  rcases gaps with _ | ⟨d, gaps⟩
  · simp at hglen
  rcases gaps with _ | ⟨e, gaps⟩
  · have ha := hbd a (by simp)
    have hb := hbd b (by simp)
    have hc := hbd c (by simp)
    have hd := hbd d (by simp)
    simp [OMA.S_oeis_a110735.insertDigits, Nat.ofDigits] at hdvd
    obtain ⟨k, hk⟩ := hdvd
    have heq : 101 * k + (b + d) =
        101 * (990 + b + 99 * c + 9901 * d) + (20 + a + c) := by omega
    have hmod := congrArg (fun x : ℕ => x % 101) heq
    simp only [Nat.mul_add_mod] at hmod
    rw [Nat.mod_eq_of_lt (by omega : b + d < 101),
      Nat.mod_eq_of_lt (by omega : 20 + a + c < 101)] at hmod
    omega
  · simp at hglen
