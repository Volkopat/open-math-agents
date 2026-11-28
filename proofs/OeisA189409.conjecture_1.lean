import FormalConjectures.OEIS.«189409»

theorem OMA.disproof : ¬ (type_of% @OeisA189409.conjecture_1) := by
  intro h
  exact Nat.squarefree_iff_prime_squarefree.mp (h 9) 29 (by decide)
    (by norm_num [OeisA189409.a, Nat.kthPrimorial_succ])
