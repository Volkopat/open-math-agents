import OMAStatements.S_oeis_a065942

open OMA.S_oeis_a065942 in
theorem OMA.solution : type_of% @OMA.S_oeis_a065942.main := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  have e (s c : ℕ) : a (2*s+c) = (3*s+(2*c-(c+1)/2)).choose (s+c/2) := by
    unfold a T
    congr 1 <;> omega
  have p (s : ℕ) : ((3*s).choose s * (3*s+1) : ℤ) = (3*s+1).choose s * (2*s+1) := by
    have := Nat.choose_mul_succ_eq (3*s) s
    rw [show 3*s+1-s = 2*s+1 by omega] at this
    exact_mod_cast this
  have g (s : ℕ) : ((3*s+2) * (3*s+1).choose s : ℤ) = (3*s+2).choose (s+1) * (s+1) :=
    mod_cast Nat.add_one_mul_choose_eq (3*s+1) s
  have h (s : ℕ) : ((3*s+2).choose (s+1) * (3*s+3) : ℤ) = (3*s+3).choose (s+1) * (2*s+2) := by
    have := Nat.choose_mul_succ_eq (3*s+2) (s+1)
    rw [show 3*s+2+1-(s+1) = 2*s+2 by omega] at this
    exact_mod_cast this
  obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' k
  · have p0 := p i
    have g0 := g i
    have h0 := h i
    have p1 := p (i+1)
    simp [e, mul_add, add_assoc, show a (2*i) = (3*i).choose i by simpa using e i 0] at *
    linear_combination -(-324*i-54)*p0 -(-144*i+96)*g0 -(-48*i+32)*h0 -(16*i+16)*p1
  · have g0 := g i
    have h0 := h i
    have p1 := p (i+1)
    have g1 := g (i+1)
    have h1 := h (i+1)
    simp [e, mul_add, add_assoc] at *
    linear_combination -(-324*i-270)*g0 -(-108*i-90)*h0 -84*p1 -(48*i+72)*g1 -(16*i+24)*h1
