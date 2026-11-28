import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H2_R1

/-!
Split the first 13-table residual batch into four micro-batches for independent
nonhalting proofs.

Parent: @pageman `…H4.R1.H2.R1`.
-/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H2_R1_H1_R1

open Turing Turing.BusyBeaver

def H1 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([192926630, 394870650, 515740378] : List ℕ), ¬ Machine.IsHalting (entry z)

def H2 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([1336417724, 1408830431, 1627390098] : List ℕ), ¬ Machine.IsHalting (entry z)

def H3 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([1689441169, 2446657396, 2452336858, 2460855813] : List ℕ), ¬ Machine.IsHalting (entry z)

def H4 : Prop :=
  let entry (z : ℕ) (r : Fin 4) (s : Fin 2) : Option (Option (Fin 4) × Stmt (Fin 2)) :=
    let k := z / 17 ^ (2 * r.val + s.val) % 17
    if k = 16 then none
    else some (some (Fin.ofNat 4 (k / 4)),
      .write (Fin.ofNat 2 (k / 2)) (if k % 2 = 0 then .left else .right))
  ∀ z ∈ ([2460855983, 2930234279, 3133858477] : List ℕ), ¬ Machine.IsHalting (entry z)

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H2_R1.H1 := by
  intro h1 h2 h3 h4 z hz
  let L1 : List ℕ := [192926630, 394870650, 515740378]
  let L2 : List ℕ := [1336417724, 1408830431, 1627390098]
  let L3 : List ℕ := [1689441169, 2446657396, 2452336858, 2460855813]
  let L4 : List ℕ := [2460855983, 2930234279, 3133858477]
  have hEq :
      ([192926630, 394870650, 515740378, 1336417724, 1408830431, 1627390098,
         1689441169, 2446657396, 2452336858, 2460855813, 2460855983, 2930234279,
         3133858477] : List ℕ) = L1 ++ L2 ++ L3 ++ L4 := rfl
  have hz' : z ∈ L1 ++ L2 ++ L3 ++ L4 := by rwa [← hEq]
  rcases (List.mem_append.mp hz') with h123 | h4mem
  · rcases (List.mem_append.mp h123) with h12 | h3mem
    · rcases (List.mem_append.mp h12) with h1mem | h2mem
      · exact h1 z h1mem
      · exact h2 z h2mem
    · exact h3 z h3mem
  · exact h4 z h4mem

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H1_R1_H3_R1_H2_R1_H4_R1_H2_R1_H1_R1
