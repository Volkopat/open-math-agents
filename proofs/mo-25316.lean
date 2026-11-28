import OMAStatements.S_mo_25316

/-!
Retains @justusklocke-cloud’s proof #14088; the infinite-dimensional witness uses
Mathlib’s canonical Hilbert basis of ℓ².

Put two disjoint sequences on one line, one bounded and the other unbounded. The map
interleaves the sequences and its square shifts each separately. Any square root must
map the bounded sequence onto a tail of the unbounded sequence, ruling out even weak
continuity along that line.
-/

namespace OMA.HemicontinuousSquare

open Function OMA.S_mo_25316

private noncomputable def interleave {E : Type*} (A B : ℕ → E) (x : E) : E := by
  classical
  exact if h : x ∈ Set.range A then B (Classical.choose h) else
    if h' : x ∈ Set.range B then A (Classical.choose h' + 1) else x

private theorem interleave_a {E : Type*} {A B : ℕ → E} (hA : Injective A) (i : ℕ) :
    interleave A B (A i) = B i := by
  classical
  have h : A i ∈ Set.range A := ⟨i,rfl⟩
  simp only [interleave, dif_pos h]
  exact congrArg B (hA (Classical.choose_spec h))

private theorem interleave_b {E : Type*} {A B : ℕ → E} (hB : Injective B)
    (hAB : ∀ i j, A i ≠ B j) (i : ℕ) :
    interleave A B (B i) = A (i + 1) := by
  classical
  have h : B i ∉ Set.range A := by
    rintro ⟨j,hj⟩
    exact hAB j i hj
  have h' : B i ∈ Set.range B := ⟨i,rfl⟩
  simp only [interleave, dif_neg h, dif_pos h']
  exact congrArg (fun k => A (k + 1)) (hB (Classical.choose_spec h'))

private theorem interleave_other {E : Type*} {A B : ℕ → E} {x : E}
    (hA : x ∉ Set.range A) (hB : x ∉ Set.range B) : interleave A B x = x := by
  classical
  simp [interleave, hA, hB]

private theorem square_root_moves_sequences {E : Type*} {A B : ℕ → E}
    (hA : Injective A) (hB : Injective B) (hAB : ∀ i j, A i ≠ B j)
    {V : E → E} (hs : ∀ x, V (V x) = interleave A B (interleave A B x)) :
    ∃ k, ∀ n, V (A n) = B (k+n) := by
  let T : E → E := interleave A B ∘ interleave A B
  have hsq (x : E) : V (V x) = T x := hs x
  have hTA (n : ℕ) : T (A n) = A (n+1) := by
    simp [T, interleave_a hA, interleave_b hB hAB]
  have hTB (n : ℕ) : T (B n) = B (n+1) := by
    simp [T, interleave_a hA, interleave_b hB hAB]
  have hcomm (x : E) : V (T x) = T (V x) := by
    rw [← hsq x, ← hsq (V x)]
  have hrange : V (A 0) ∈ Set.range A ∨ V (A 0) ∈ Set.range B := by
    by_contra! hn
    have hfix : T (V (A 0)) = V (A 0) := by
      simp [T, interleave_other hn.1 hn.2]
    have h0 := hcomm (A 0)
    rw [hTA, hfix] at h0
    have h1 := congrArg V h0
    change V (V (A (0+1))) = V (V (A 0)) at h1
    rw [hsq, hsq, hTA, hTA] at h1
    have hfalse : (0+1+1 : ℕ) = 0+1 := hA h1
    omega
  rcases hrange with ⟨k,hk⟩ | ⟨k,hk⟩
  · have hi (n : ℕ) : V (A n) = A (k+n) := by
      induction n with
      | zero => exact hk.symm
      | succ n ih => rw [← hTA n, hcomm, ih, hTA, Nat.add_assoc]
    have hp := hsq (A 0)
    rw [hTA, ← hk, hi] at hp
    have hfalse : k+k = 0+1 := hA hp
    omega
  · refine ⟨k, fun n => ?_⟩
    induction n with
    | zero => exact hk.symm
    | succ n ih => rw [← hTA n, hcomm, ih, hTB, Nat.add_assoc]

private abbrev Hilbert := lp (fun _ : ℕ => ℝ) 2

private theorem hilbert_infinite : ¬ FiniteDimensional ℝ Hilbert := by
  intro h
  have hc := (default : HilbertBasis ℕ ℝ Hilbert).orthonormal.linearIndependent.lt_aleph0_of_finiteDimensional
  simp at hc

private noncomputable def coordinate : Hilbert →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 0

private noncomputable def basisPoint : Hilbert := lp.single 2 0 1

private theorem coordinate_smul (r : ℝ) : coordinate (r • basisPoint) = r := by
  rw [map_smul]
  change r * (lp.single (E := fun _ : ℕ => ℝ) 2 0 1) 0 = r
  rw [lp.single_apply_self, mul_one]

private noncomputable def boundedParam (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

private noncomputable def A (n : ℕ) : Hilbert := boundedParam n • basisPoint

private noncomputable def B (n : ℕ) : Hilbert := ((n : ℝ) + 2) • basisPoint

private theorem coordinate_A (n : ℕ) : coordinate (A n) = boundedParam n := coordinate_smul _

private theorem coordinate_B (n : ℕ) : coordinate (B n) = (n : ℝ) + 2 := coordinate_smul _

private theorem boundedParam_mem (n : ℕ) : boundedParam n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold boundedParam
  refine ⟨by positivity, (div_le_one (by positivity)).2 ?_⟩
  have hn : 0 ≤ (n : ℝ) := by positivity
  linarith

private theorem A_injective : Injective A := by
  intro i j he
  simpa [coordinate_A, boundedParam, one_div] using congrArg coordinate he

private theorem B_injective : Injective B := by
  intro i j he
  have h := congrArg coordinate he
  rw [coordinate_B, coordinate_B] at h
  have hij : (i : ℝ) = j := by linarith
  exact_mod_cast hij

private theorem disjoint_sequences (i j : ℕ) : A i ≠ B j := by
  intro he
  have h := congrArg coordinate he
  rw [coordinate_A, coordinate_B] at h
  have hi := (boundedParam_mem i).2
  have hj : (0 : ℝ) ≤ j := by positivity
  linarith

private theorem scalar_continuous {V : Hilbert → Hilbert} (hV : Hemicontinuous V) :
    Continuous (fun t : ℝ => coordinate (V (t • basisPoint))) := by
  have he := WeakBilin.eval_continuous (topDualPairing ℝ Hilbert).flip coordinate
  change Continuous (fun x : WeakSpace ℝ Hilbert => coordinate ((toWeakSpace ℝ Hilbert).symm x)) at he
  have hc := he.comp (hV 0 basisPoint)
  change Continuous (fun t : ℝ => coordinate ((toWeakSpace ℝ Hilbert).symm
    (toWeakSpace ℝ Hilbert (V (0 + t • basisPoint))))) at hc
  simpa only [zero_add, LinearEquiv.symm_apply_apply] using hc

theorem counterexample : ¬ (type_of% @OMA.S_mo_25316.main) := by
  intro h
  obtain ⟨V, hV, hsq⟩ := h Hilbert hilbert_infinite (interleave A B)
  have hEq (x : Hilbert) : V (V x) = interleave A B (interleave A B x) :=
    (congrFun hsq x).symm
  obtain ⟨k,hk⟩ := square_root_moves_sequences A_injective B_injective disjoint_sequences hEq
  let f : ℝ → ℝ := fun t => coordinate (V (t • basisPoint))
  have hf : Continuous f := scalar_continuous hV
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hf.continuousOn
    (K := Set.Icc (0 : ℝ) 1)
  obtain ⟨n,hn⟩ := exists_nat_gt M
  have hle : f (boundedParam n) ≤ M := hM (Set.mem_image_of_mem _ (boundedParam_mem n))
  have he : f (boundedParam n) = ((k+n : ℕ) : ℝ) + 2 := by
    change coordinate (V (A n)) = _
    rw [hk, coordinate_B]
  rw [he, Nat.cast_add] at hle
  have hk0 : 0 ≤ (k : ℝ) := by positivity
  linarith

end OMA.HemicontinuousSquare

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_25316.main) :=
  OMA.HemicontinuousSquare.counterexample
