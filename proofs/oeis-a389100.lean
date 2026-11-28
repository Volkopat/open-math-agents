import OMAStatements.S_oeis_a389100
import Mathlib

open OMA.S_oeis_a389100 in
theorem OMA.solution : type_of% @OMA.S_oeis_a389100.main := by
  intro k hk
  unfold InA387054 InA388654 at hk
  obtain ⟨⟨a, b, hab, hak, hkb⟩, hn⟩ := hk
  refine ⟨a, b, hab, ?_, hak, hkb⟩
  by_contra h
  have hb : b = a := by have := hab.2.1; omega
  have hka : k = a := by omega
  rw [hb] at hab
  apply hn
  rw [hka]
  simpa [InA070003] using hab.2.2
