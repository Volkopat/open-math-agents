import OMAReductions.R_Erdos430_erdos_430_R1

theorem OMA.solution : OMA.R_Erdos430_erdos_430_R1.H2 := by
  intro n p q hp hq _ h _
  refine Finset.mem_filter.2 ⟨Finset.mem_Ioo.2 ⟨by nlinarith [hp.two_le, hq.two_le], h⟩, fun r hr => ?_⟩
  simp [Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors] at hr
  omega
