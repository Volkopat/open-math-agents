import FormalConjectures.OEIS.«238281»

/-!
The witness 14 was previously recorded by OEIS Open in its A238281 results.
Original formalization for this target: @rleshner.
-/

set_option maxRecDepth 4096 in
theorem OMA.disproof : ¬ (type_of% @OeisA238281.conjecture_2) := by
  intro h
  obtain ⟨k, hk, hlt, hp, he⟩ := h 14 (by decide) (by decide)
  have finite : ∀ i : Fin 14, (2 * i.val + 1).Prime →
      Nat.primeCounting (i.val * 14) - Nat.primeCounting ((i.val - 1) * 14) ≠
      Nat.primeCounting ((i.val + 1) * 14) - Nat.primeCounting (i.val * 14) := by decide
  exact finite ⟨k, hlt⟩ hp he
