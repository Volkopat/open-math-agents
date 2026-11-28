import FormalConjectures.GreensOpenProblems.«22»

theorem OMA.solution : type_of% @Green22.green_22.variants.lower_nine := by
  intro r hr N hN
  obtain ⟨x, y, hx, hy, _, hprod, _⟩ := hN (fun _ => ⟨0, Nat.pos_of_ne_zero hr⟩)
  exact (Nat.mul_le_mul hx hy).trans (Finset.mem_Icc.mp hprod).2
