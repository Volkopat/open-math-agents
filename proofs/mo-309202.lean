import OMAStatements.S_mo_309202
import Mathlib

-- Retains @AkiRA-COM-FP’s counterexample from #15789.
-- Open singletons give the discrete topology and continuity through the library API.

open Set

open OMA.S_mo_309202

private structure CounterexamplePoint where
  down : ℕ
  deriving DecidableEq

/-- The reverse implication for an arbitrary uniformity. -/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_309202.main) := by
  classical
  let P := CounterexamplePoint
  let bounded := {f : P → ℝ // ∃ C : ℝ, ∀ x, |f x| ≤ C}
  let eval : P → (bounded → ℝ) := fun x f => f.val x
  let u : UniformSpace P := UniformSpace.comap eval inferInstance
  let _ : UniformSpace P := u
  have hInd : IsUniformInducing eval := ⟨rfl⟩
  have hTest (f : P → ℝ) (hBound : ∃ C : ℝ, ∀ x, |f x| ≤ C) :
      UniformContinuous f :=
    (uniformContinuous_pi.mp hInd.uniformContinuous) ⟨f,hBound⟩
  have hSingleton (x : P) : IsOpen ({x} : Set P) := by
    let d (y : P) : ℝ := if y = x then 0 else 1
    have hb : ∀ y, |d y| ≤ 1 := by
      intro y
      by_cases h : y = x <;> simp [d,h]
    have he : d ⁻¹' Iio (1 / 2 : ℝ) = {x} := by
      ext y
      by_cases h : y = x
      · subst y
        norm_num [d]
      · norm_num [d,h]
    rw [← he]
    exact isOpen_Iio.preimage (hTest d ⟨1,hb⟩).continuous
  let number (x : P) : ℝ := x.down
  let : DiscreteTopology P := discreteTopology_iff_isOpen_singleton.mpr hSingleton
  have hCompact : IsCompact (Set.pi univ fun f : bounded =>
      Icc (-(Classical.choose f.property)) (Classical.choose f.property)) :=
    by
      simpa [Set.pi] using (isCompact_pi_infinite (fun f : bounded =>
        (isCompact_Icc : IsCompact (Icc (-(Classical.choose f.property)) (Classical.choose f.property)))))
  have hSub : range eval ⊆ Set.pi univ (fun f : bounded =>
      Icc (-(Classical.choose f.property)) (Classical.choose f.property)) := by
    rintro _ ⟨x,rfl⟩ f _
    exact abs_le.mp (Classical.choose_spec f.property x)
  have hAll : TotallyBounded (univ : Set P) := by
    apply (totallyBounded_image_iff hInd).mp
    rw [image_univ]
    exact hCompact.totallyBounded.subset hSub
  intro h
  have hu : UniformContinuous number := h P (fun f _ hb => hTest f hb) number continuous_of_discreteTopology
  have hImage : TotallyBounded (range number) := by
    rw [← image_univ]
    exact hAll.image hu
  obtain ⟨R,hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hImage.isBounded
  obtain ⟨k,hk⟩ := exists_nat_gt R
  have hBall := hR (show number ⟨k⟩ ∈ range number from mem_range_self _)
  have hle : (k : ℝ) ≤ R := by simpa [number,Metric.mem_closedBall,Real.dist_eq] using hBall
  exact (not_le_of_gt hk) hle
