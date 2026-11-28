import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1

open SimpleGraph

namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1_H2_R1

def H1 : Prop :=
  ∀ G : SimpleGraph (Fin 16), G.CliqueFree 4 → Gᶜ.CliqueFree 4 →
    (∀ i : Fin 16, G.Adj (Fin.last 15) i ↔ i.val < 7) →
    ∀ a b : Nat, (a,b) ∈ ([0x75688, 0xe6844, 0xe684c, 0x76101, 0x1a2a03, 0xe7093] : List Nat).zip [0xc4c5061, 0x395508b, 0x9236960, 0xc4c5061, 0xc4c5061, 0x395508b] →
      (∀ i j : Fin 7, i < j → (G.Adj ((Fin.castAdd 8 i).castSucc) ((Fin.castAdd 8 j).castSucc) ↔
        a.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      (∀ i j : Fin 8, i < j → (Gᶜ.Adj ((Fin.natAdd 7 i).castSucc) ((Fin.natAdd 7 j).castSucc) ↔
        b.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      ∃ w : Nat, (w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) ∧
        ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
          (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true)

def H2 : Prop :=
  ∀ G : SimpleGraph (Fin 16), G.CliqueFree 4 → Gᶜ.CliqueFree 4 →
    (∀ i : Fin 16, G.Adj (Fin.last 15) i ↔ i.val < 7) →
    ∀ a b : Nat, (a,b) ∈ ([0x75688, 0x75688, 0xb6421, 0x182121, 0xa2a03, 0x1a2a03, 0xe7093] : List Nat).zip [0x9236960, 0x395508b, 0xc4c5061, 0xc4c5061, 0xc4c5061, 0x9236960, 0xc4c5061] →
      (∀ i j : Fin 7, i < j → (G.Adj ((Fin.castAdd 8 i).castSucc) ((Fin.castAdd 8 j).castSucc) ↔
        a.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      (∀ i j : Fin 8, i < j → (Gᶜ.Adj ((Fin.natAdd 7 i).castSucc) ((Fin.natAdd 7 j).castSucc) ↔
        b.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      ∃ w : Nat, (w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) ∧
        ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
          (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true)

def H3 : Prop :=
  ∀ G : SimpleGraph (Fin 16), G.CliqueFree 4 → Gᶜ.CliqueFree 4 →
    (∀ i : Fin 16, G.Adj (Fin.last 15) i ↔ i.val < 7) →
    ∀ a b : Nat, (a,b) ∈ ([0xe6844, 0xe684c, 0xe684c, 0xb6421, 0x182121, 0xa2a03, 0xe7093] : List Nat).zip [0x9236960, 0xc4c5061, 0x395508b, 0x395508b, 0x395508b, 0x9236960, 0x9236960] →
      (∀ i j : Fin 7, i < j → (G.Adj ((Fin.castAdd 8 i).castSucc) ((Fin.castAdd 8 j).castSucc) ↔
        a.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      (∀ i j : Fin 8, i < j → (Gᶜ.Adj ((Fin.natAdd 7 i).castSucc) ((Fin.natAdd 7 j).castSucc) ↔
        b.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      ∃ w : Nat, (w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) ∧
        ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
          (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true)

def H4 : Prop :=
  ∀ G : SimpleGraph (Fin 16), G.CliqueFree 4 → Gᶜ.CliqueFree 4 →
    (∀ i : Fin 16, G.Adj (Fin.last 15) i ↔ i.val < 7) →
    ∀ a b : Nat, (a,b) ∈ ([0xe6844, 0x76101, 0x76101, 0xb6421, 0x182121, 0xa2a03, 0x1a2a03] : List Nat).zip [0xc4c5061, 0x9236960, 0x395508b, 0x9236960, 0x9236960, 0x395508b, 0x395508b] →
      (∀ i j : Fin 7, i < j → (G.Adj ((Fin.castAdd 8 i).castSucc) ((Fin.castAdd 8 j).castSucc) ↔
        a.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      (∀ i j : Fin 8, i < j → (Gᶜ.Adj ((Fin.natAdd 7 i).castSucc) ((Fin.natAdd 7 j).castSucc) ↔
        b.testBit (j.val*(j.val-1)/2+i.val) = true)) →
      ∃ w : Nat, (w = 0xcb94e332f53ae143a3b6933356490b ∨ w = 0xacb96354eb266b51b2b6553699403b) ∧
        ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i < j →
          (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val) = true)

theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1.H2 := by
  intro h1 h2 h3 h4 G hG hC rooted a ha b hb
  have hit : (a,b) ∈ ([0x75688, 0xe6844, 0xe684c, 0x76101, 0x1a2a03, 0xe7093] : List Nat).zip [0xc4c5061, 0x395508b, 0x9236960, 0xc4c5061, 0xc4c5061, 0x395508b] ∨
      (a,b) ∈ ([0x75688, 0x75688, 0xb6421, 0x182121, 0xa2a03, 0x1a2a03, 0xe7093] : List Nat).zip [0x9236960, 0x395508b, 0xc4c5061, 0xc4c5061, 0xc4c5061, 0x9236960, 0xc4c5061] ∨
      (a,b) ∈ ([0xe6844, 0xe684c, 0xe684c, 0xb6421, 0x182121, 0xa2a03, 0xe7093] : List Nat).zip [0x9236960, 0xc4c5061, 0x395508b, 0x395508b, 0x395508b, 0x9236960, 0x9236960] ∨
      (a,b) ∈ ([0xe6844, 0x76101, 0x76101, 0xb6421, 0x182121, 0xa2a03, 0x1a2a03] : List Nat).zip [0xc4c5061, 0x9236960, 0x395508b, 0x9236960, 0x9236960, 0x395508b, 0x395508b] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hb with rfl | rfl | rfl <;> decide +kernel
  rcases hit with hit | hit | hit | hit
  · exact h1 G hG hC rooted a b hit
  · exact h2 G hG hC rooted a b hit
  · exact h3 G hG hC rooted a b hit
  · exact h4 G hG hC rooted a b hit

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1_H2_R1