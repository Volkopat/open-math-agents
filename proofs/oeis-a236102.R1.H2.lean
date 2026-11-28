import OMAReductions.R_oeis_a236102_R1

/-! Adding a part 1 maps partitions of m injectively into partitions of m + 1. For m ≥ 1 the
one-part partition of m + 1 has no part equal to 1, so it is not in the image. -/

theorem OMA.solution : OMA.R_oeis_a236102_R1.H2 := by
  intro m hm
  let f : Nat.Partition m → Nat.Partition (m + 1) := fun p =>
    ⟨1 ::ₘ p.parts, by
      intro i hi
      rcases Multiset.mem_cons.1 hi with rfl | hi
      · exact Nat.one_pos
      · exact p.parts_pos hi, by
      rw [Multiset.sum_cons, p.parts_sum, add_comm]⟩
  have hf : Function.Injective f := by
    intro p q hpq
    have h : 1 ::ₘ p.parts = 1 ::ₘ q.parts := congrArg Nat.Partition.parts hpq
    exact Nat.Partition.ext ((Multiset.cons_inj_right 1).1 h)
  apply Fintype.card_lt_of_injective_of_notMem f hf (b := Nat.Partition.indiscrete (m + 1))
  rintro ⟨p, hp⟩
  have h : 1 ::ₘ p.parts = (Nat.Partition.indiscrete (m + 1)).parts := congrArg Nat.Partition.parts hp
  rw [Nat.Partition.indiscrete_parts (by omega)] at h
  have h1 : (1 : ℕ) ∈ ({m + 1} : Multiset ℕ) := by
    rw [← h]
    exact Multiset.mem_cons_self 1 _
  rw [Multiset.mem_singleton] at h1
  omega
