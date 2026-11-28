import OMAReductions.R_wpc_prouhet_tarry_escott_R1
import Mathlib

/-! Explicit ideal Prouhet–Tarry–Escott solutions of degrees `k ≤ 9` and `k = 11` (sizes 1–10 and
12; Prouhet, Tarry, Escott, Letac, Smyth, Kuosa–Meyrignac–Chen), each checked by computation. -/

open OMA.S_wpc_prouhet_tarry_escott

lemma ideal_of {k : ℕ} {A B : Multiset ℤ} (h1 : A.card = k + 1) (h2 : B.card = k + 1)
    (h3 : ∀ a ∈ A, a ∉ B)
    (h4 : ∀ i ∈ Finset.Icc 1 k, (A.map (fun a => a ^ i)).sum = (B.map (fun b => b ^ i)).sum) :
    IsIdealSolution k A B :=
  ⟨h1, h2, Multiset.disjoint_left.mpr fun ha => h3 _ ha, h4⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_wpc_prouhet_tarry_escott_R1.H1 := by
  intro k hk
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl :
      k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 11 := by
    omega
  · exact ⟨{0}, {1}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 3}, {1, 2}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{1, 5, 6}, {2, 3, 7}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 4, 7, 11}, {1, 2, 9, 10}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{1, 5, 9, 17, 18}, {2, 3, 11, 15, 19}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 5, 6, 16, 17, 22}, {1, 2, 10, 12, 20, 21}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 18, 27, 58, 64, 89, 101}, {1, 13, 38, 44, 75, 84, 102}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 4, 9, 23, 27, 41, 46, 50}, {1, 2, 11, 20, 30, 39, 48, 49}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 24, 30, 83, 86, 133, 157, 181, 197}, {1, 17, 41, 65, 112, 115, 168, 174, 198},
      ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 3083, 3301, 11893, 23314, 24186, 35607, 44199, 44417, 47500},
      {12, 2865, 3519, 11869, 23738, 23762, 35631, 43981, 44635, 47488}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
  · exact ⟨{0, 11, 24, 65, 90, 129, 173, 212, 237, 278, 291, 302},
      {3, 5, 30, 57, 104, 116, 186, 198, 245, 272, 297, 299}, ideal_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩
