import OMAStatements.S_oeis_a283050
open OMA.S_oeis_a283050
theorem OMA.solution : type_of% @OMA.S_oeis_a283050.main := by
  classical
  have t (k : ℕ) : IsTerm (4 * k + 4) :=
    ⟨by omega, by rw [(Nat.minFac_eq_two_iff _).2 ⟨2 * k + 2, by ring⟩]; exact ⟨k + 1, by ring⟩⟩
  have m : StrictMono a := Nat.nth_strictMono (Set.infinite_of_forall_exists_gt fun k => ⟨_, t k, by omega⟩)
  intro n
  have c : a _ = _ := Nat.nth_count (t (a n / 4))
  have := m.lt_iff_lt (a := n) (b := Nat.count IsTerm (4 * (a n / 4) + 4))
  have := m.le_iff_le (a := n + 1) (b := Nat.count IsTerm (4 * (a n / 4) + 4))
  have := m n.lt_add_one
  omega
