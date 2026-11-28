import OMAStatements.S_oeis_a094303

/-!
Proof of OEIS A094303: for every m : ℕ, state (m + 1) equals the swapped
companion pair ((companion (m + 2)).2, (companion (m + 2)).1).
Then for n = m + 3, u (n + 1) - u n = (companion (m + 2)).2 = a n.
-/

private lemma state_eq_swap (m : ℕ) :
    OMA.S_oeis_a094303.state (m + 1) =
      ((OMA.S_oeis_a094303.companion (m + 2)).2, (OMA.S_oeis_a094303.companion (m + 2)).1) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : OMA.S_oeis_a094303.state (m + 1 + 1) =
        ((OMA.S_oeis_a094303.state (m + 1)).1 * (OMA.S_oeis_a094303.state (m + 1)).2,
         (OMA.S_oeis_a094303.state (m + 1)).2 + (OMA.S_oeis_a094303.state (m + 1)).1) := rfl
    have h2 : OMA.S_oeis_a094303.companion (m + 1 + 2) =
        ((OMA.S_oeis_a094303.companion (m + 2)).1 + (OMA.S_oeis_a094303.companion (m + 2)).2,
         (OMA.S_oeis_a094303.companion (m + 2)).1 * (OMA.S_oeis_a094303.companion (m + 2)).2) := rfl
    rw [h1, h2, ih]
    exact Prod.ext (Nat.mul_comm _ _) rfl

theorem OMA.solution : type_of% @OMA.S_oeis_a094303.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h1 : OMA.S_oeis_a094303.a (m + 3) = (OMA.S_oeis_a094303.state (m + 1)).1 := rfl
  have h2 : OMA.S_oeis_a094303.u (m + 3 + 1) =
      (OMA.S_oeis_a094303.companion (m + 2)).1 + (OMA.S_oeis_a094303.companion (m + 2)).2 := by
    change (OMA.S_oeis_a094303.companion (m + 3)).1 = _
    rw [OMA.S_oeis_a094303.companion]
  have h3 : OMA.S_oeis_a094303.u (m + 3) = (OMA.S_oeis_a094303.companion (m + 2)).1 := rfl
  rw [h1, h2, h3, state_eq_swap m, Nat.add_sub_cancel_left]
