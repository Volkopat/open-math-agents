import OMAStatements.S_arxiv_2101_07103

/-!
# Nine-vertex counterexample to Estrada–Mugnolo, Conjecture 4.13

Two disjoint four-cliques on 0–3 and 5–8 are joined along the path 0–4–5.
The exact rational certificates below verify all four Moore–Penrose equations.
Source: https://arxiv.org/abs/2101.07103. Credit: @rleshner.
-/

namespace HubWitness
open OMA.S_arxiv_2101_07103

private abbrev V := Fin 9
private abbrev Mat := Matrix V V ℚ

private def adjacent (i j : V) : Prop := i ≠ j ∧
  ((i.val < 4 ∧ j.val < 4) ∨ (5 ≤ i.val ∧ 5 ≤ j.val) ∨
   (i = 4 ∧ (j = 0 ∨ j = 5)) ∨ (j = 4 ∧ (i = 0 ∨ i = 5)))

private def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨by intro i j h; unfold adjacent at *; tauto⟩
  loopless := ⟨fun i h => h.1 rfl⟩

private instance : DecidableRel graph.Adj := fun i j => by
  change Decidable (adjacent i j)
  unfold adjacent
  infer_instance

private theorem connected : graph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable graph).mpr
  refine ⟨4, ?_⟩
  have left : graph.Reachable 4 0 := SimpleGraph.Adj.reachable (by decide : graph.Adj 4 0)
  have right : graph.Reachable 4 5 := SimpleGraph.Adj.reachable (by decide : graph.Adj 4 5)
  intro i
  fin_cases i <;> first
    | exact SimpleGraph.Reachable.refl _
    | exact left
    | exact right
    | exact left.trans (SimpleGraph.Adj.reachable (by decide))
    | exact right.trans (SimpleGraph.Adj.reachable (by decide))

private def lapRep : Mat :=
  fun i j => (!![72, -16, -16, -16, -24, 0, 0, 0, 0;
    -9, 33, -12, -12, 0, 0, 0, 0, 0;
    -9, -12, 33, -12, 0, 0, 0, 0, 0;
    -9, -12, -12, 33, 0, 0, 0, 0, 0;
    -6, 0, 0, 0, 12, -6, 0, 0, 0;
    0, 0, 0, 0, -24, 72, -16, -16, -16;
    0, 0, 0, 0, 0, -9, 33, -12, -12;
    0, 0, 0, 0, 0, -9, -12, 33, -12;
    0, 0, 0, 0, 0, -9, -12, -12, 33] : Mat) i j / 12

private def mpRep : Mat :=
  fun i j => (!![27375, 35360, 35360, 35360, 9700, -17535, -44480, -44480, -44480;
    21615, 81008, 57056, 57056, -13340, -23295, -54720, -54720, -54720;
    21615, 57056, 81008, 57056, -13340, -23295, -54720, -54720, -54720;
    21615, 57056, 57056, 81008, -13340, -23295, -54720, -54720, -54720;
    -4800, -21840, -21840, -21840, 60640, -4800, -21840, -21840, -21840;
    -17535, -44480, -44480, -44480, 9700, 27375, 35360, 35360, 35360;
    -23295, -54720, -54720, -54720, -13340, 21615, 81008, 57056, 57056;
    -23295, -54720, -54720, -54720, -13340, 21615, 57056, 81008, 57056;
    -23295, -54720, -54720, -54720, -13340, 21615, 57056, 57056, 81008] : Mat) i j / 89820

private def lapOrd : Mat :=
  fun i j => (!![4, -1, -1, -1, -1, 0, 0, 0, 0;
    -1, 3, -1, -1, 0, 0, 0, 0, 0;
    -1, -1, 3, -1, 0, 0, 0, 0, 0;
    -1, -1, -1, 3, 0, 0, 0, 0, 0;
    -1, 0, 0, 0, 2, -1, 0, 0, 0;
    0, 0, 0, 0, -1, 4, -1, -1, -1;
    0, 0, 0, 0, 0, -1, 3, -1, -1;
    0, 0, 0, 0, 0, -1, -1, 3, -1;
    0, 0, 0, 0, 0, -1, -1, -1, 3] : Mat) i j / 1

private def mpOrd : Mat :=
  fun i j => (!![188, 152, 152, 152, 8, -136, -172, -172, -172;
    152, 278, 197, 197, -28, -172, -208, -208, -208;
    152, 197, 278, 197, -28, -172, -208, -208, -208;
    152, 197, 197, 278, -28, -172, -208, -208, -208;
    8, -28, -28, -28, 152, 8, -28, -28, -28;
    -136, -172, -172, -172, 8, 188, 152, 152, 152;
    -172, -208, -208, -208, -28, 152, 278, 197, 197;
    -172, -208, -208, -208, -28, 152, 197, 278, 197;
    -172, -208, -208, -208, -28, 152, 197, 197, 278] : Mat) i j / 324

private def lapAtt : Mat :=
  fun i j => (!![33, -9, -9, -9, -6, 0, 0, 0, 0;
    -16, 40, -12, -12, 0, 0, 0, 0, 0;
    -16, -12, 40, -12, 0, 0, 0, 0, 0;
    -16, -12, -12, 40, 0, 0, 0, 0, 0;
    -24, 0, 0, 0, 48, -24, 0, 0, 0;
    0, 0, 0, 0, -6, 33, -9, -9, -9;
    0, 0, 0, 0, 0, -16, 40, -12, -12;
    0, 0, 0, 0, 0, -16, -12, 40, -12;
    0, 0, 0, 0, 0, -16, -12, -12, 40] : Mat) i j / 12

private def mpAtt : Mat :=
  fun i j => (!![78320, 37971, 37971, 37971, -700, -67696, -44163, -44163, -44163;
    70544, 63081, 46233, 46233, -2644, -75472, -48537, -48537, -48537;
    70544, 46233, 63081, 46233, -2644, -75472, -48537, -48537, -48537;
    70544, 46233, 46233, 63081, -2644, -75472, -48537, -48537, -48537;
    4160, -3744, -3744, -3744, 17264, 4160, -3744, -3744, -3744;
    -67696, -44163, -44163, -44163, -700, 78320, 37971, 37971, 37971;
    -75472, -48537, -48537, -48537, -2644, 70544, 63081, 46233, 46233;
    -75472, -48537, -48537, -48537, -2644, 70544, 46233, 63081, 46233;
    -75472, -48537, -48537, -48537, -2644, 70544, 46233, 46233, 63081] : Mat) i j / 73008

private def groupAtt : Mat :=
  fun i j => (!![455728, 224757, 224757, 224757, 3952, -386672, -249093, -249093, -249093;
    399568, 363267, 266067, 266067, -10088, -442832, -280683, -280683, -280683;
    399568, 266067, 363267, 266067, -10088, -442832, -280683, -280683, -280683;
    399568, 266067, 266067, 363267, -10088, -442832, -280683, -280683, -280683;
    15808, -22698, -22698, -22698, 104572, 15808, -22698, -22698, -22698;
    -386672, -249093, -249093, -249093, 3952, 455728, 224757, 224757, 224757;
    -442832, -280683, -280683, -280683, -10088, 399568, 363267, 266067, 266067;
    -442832, -280683, -280683, -280683, -10088, 399568, 266067, 363267, 266067;
    -442832, -280683, -280683, -280683, -10088, 399568, 266067, 266067, 363267] : Mat) i j / 421200

private def L : Bias → Mat
  | .repelling => lapRep
  | .ordinary => lapOrd
  | .attracting => lapAtt

private def P : Bias → Mat
  | .repelling => mpRep
  | .ordinary => mpOrd
  | .attracting => mpAtt

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem lap_cert (b : Bias) : lap graph b = L b := by
  cases b <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem mp_cert (b : Bias) : Penrose (L b) (P b) := by
  cases b <;> unfold Penrose <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem weights :
    index (P .attracting) = 92065 / 1352 ∧ index (P .ordinary) = 61 ∧
    index (P .repelling) = 300719 / 4990 := by
  decide +kernel

/- On this diagonalizable Laplacian the spectral reciprocal construction is
the commuting group inverse. It too violates the proposed ordering. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem group_certificate :
    lapAtt * groupAtt * lapAtt = lapAtt ∧
    groupAtt * lapAtt * groupAtt = groupAtt ∧
    lapAtt * groupAtt = groupAtt * lapAtt ∧
    index groupAtt = 35507 / 520 ∧ index mpOrd < index groupAtt := by
  decide +kernel

private theorem cast_penrose {A B : Mat} (h : Penrose A B) :
    Penrose (A.map (Rat.castHom ℝ)) (B.map (Rat.castHom ℝ)) := by
  rcases h with ⟨h₁, h₂, h₃, h₄⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Matrix.map_mul] using congrArg (fun T : Mat => T.map (Rat.castHom ℝ)) h₁
  · simpa only [Matrix.map_mul] using congrArg (fun T : Mat => T.map (Rat.castHom ℝ)) h₂
  · simpa only [← Matrix.map_mul, Matrix.transpose_map] using congrArg (fun T : Mat => T.map (Rat.castHom ℝ)) h₃
  · simpa only [← Matrix.map_mul, Matrix.transpose_map] using congrArg (fun T : Mat => T.map (Rat.castHom ℝ)) h₄

private theorem cast_index (A : Mat) : index (A.map (Rat.castHom ℝ)) = ((index A : ℚ) : ℝ) := by
  simp [index, Matrix.map_apply, Rat.cast_sum]

end HubWitness
open OMA.S_arxiv_2101_07103 HubWitness in
theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2101_07103.main) := by
  intro claimed
  let cert (b : Bias) := (P b).map (Rat.castHom ℝ)
  have pen (b : Bias) : Penrose ((lap graph b).map (Rat.castHom ℝ)) (cert b) := by
    rw [lap_cert]
    exact cast_penrose (mp_cert b)
  have h := (claimed graph connected cert pen).1
  change index ((P .attracting).map (Rat.castHom ℝ)) ≤ index ((P .ordinary).map (Rat.castHom ℝ)) at h
  rw [cast_index, cast_index, weights.1, weights.2.1] at h
  norm_num at h
