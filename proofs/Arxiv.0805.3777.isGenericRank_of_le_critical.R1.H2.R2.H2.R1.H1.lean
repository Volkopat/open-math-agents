import OMAReductions.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2_H2_R1
import Mathlib

/-! A finite modular right inverse for the tangent matrix of six rank-one 3×4×5 tensors.
The coordinates and right inverse were discovered by Gaussian elimination over F₃.
Each product row is independently checked by Lean's kernel. The reduction and its
transport to complex surjectivity are due to @steveDOTdigital (PR #17733). -/
namespace TensorCertificate
abbrev I := Fin 3 × Fin 4 × Fin 5
abbrev J := Fin 6 × (Fin 3 ⊕ Fin 4 ⊕ Fin 5)
def X : Fin 6 → Fin 3 → Fin 121 := ![![1, 1, 0], ![2, 2, 1], ![1, 2, 0], ![2, 1, 2], ![0, 1, 1], ![2, 1, 1]]
def Y : Fin 6 → Fin 4 → Fin 121 := ![![1, 0, 0, 2], ![0, 1, 1, 2], ![1, 2, 0, 2], ![0, 1, 0, 2], ![0, 0, 2, 1], ![1, 0, 2, 2]]
def Z : Fin 6 → Fin 5 → Fin 121 := ![![2, 0, 0, 1, 2], ![1, 1, 1, 2, 0], ![1, 1, 0, 2, 1], ![2, 0, 0, 2, 1], ![0, 1, 0, 1, 0], ![1, 0, 2, 0, 0]]
def B : Matrix J I (ZMod 3) := fun (t,s) (i,j,k) =>
  (![Sum.elim ![![![![0, 1, 2, 2, 0], ![2, 0, 1, 2, 1], ![0, 1, 1, 2, 2], ![1, 2, 2, 1, 2]], ![![2, 0, 0, 1, 1], ![1, 2, 1, 0, 1], ![0, 1, 2, 0, 0], ![1, 2, 0, 2, 0]], ![![1, 2, 2, 0, 1], ![0, 2, 2, 2, 2], ![2, 1, 1, 1, 0], ![1, 0, 0, 2, 0]]], ![![![2, 0, 2, 0, 1], ![1, 2, 1, 0, 1], ![2, 1, 2, 2, 1], ![0, 2, 0, 1, 1]], ![![1, 0, 1, 1, 0], ![0, 0, 0, 2, 0], ![2, 0, 2, 1, 1], ![0, 1, 0, 0, 1]], ![![0, 2, 0, 0, 2], ![1, 2, 1, 2, 1], ![0, 1, 0, 1, 2], ![2, 0, 2, 2, 2]]], ![![![1, 0, 2, 0, 0], ![0, 0, 1, 1, 1], ![2, 0, 1, 0, 2], ![2, 0, 1, 0, 2]], ![![1, 2, 0, 0, 1], ![2, 0, 2, 1, 2], ![0, 2, 1, 0, 2], ![0, 2, 1, 0, 2]], ![![1, 0, 0, 1, 0], ![2, 0, 0, 2, 0], ![1, 2, 2, 2, 2], ![1, 2, 2, 2, 2]]]] (Sum.elim ![![![![1, 0, 1, 0, 1], ![0, 0, 0, 1, 1], ![2, 1, 2, 2, 1], ![1, 0, 1, 0, 1]], ![![0, 2, 0, 0, 0], ![0, 0, 0, 1, 1], ![1, 0, 1, 2, 0], ![0, 2, 0, 0, 0]], ![![2, 2, 2, 2, 1], ![0, 0, 0, 2, 2], ![1, 1, 1, 0, 1], ![2, 2, 2, 2, 1]]], ![![![1, 2, 1, 1, 2], ![2, 2, 2, 0, 2], ![1, 2, 1, 1, 2], ![1, 2, 1, 1, 2]], ![![2, 0, 2, 1, 0], ![2, 2, 2, 0, 2], ![2, 0, 2, 1, 0], ![2, 0, 2, 1, 0]], ![![2, 2, 2, 0, 2], ![1, 1, 1, 0, 1], ![2, 2, 2, 0, 2], ![2, 2, 2, 0, 2]]], ![![![1, 1, 1, 2, 0], ![0, 0, 0, 2, 2], ![0, 0, 0, 0, 0], ![1, 1, 1, 2, 0]], ![![2, 2, 2, 2, 1], ![0, 0, 0, 2, 2], ![1, 1, 1, 0, 1], ![2, 2, 2, 2, 1]], ![![1, 1, 1, 1, 2], ![0, 0, 0, 1, 1], ![2, 2, 2, 0, 2], ![1, 1, 1, 1, 2]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]] ![![![![0, 2, 1, 1, 1], ![0, 0, 2, 2, 2], ![0, 2, 2, 1, 1], ![0, 2, 2, 1, 1]], ![![2, 2, 2, 2, 0], ![1, 0, 1, 2, 1], ![1, 2, 1, 2, 1], ![1, 2, 1, 2, 1]], ![![2, 0, 0, 2, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 2, 1], ![1, 0, 0, 2, 1]]], ![![![0, 0, 0, 1, 1], ![0, 2, 0, 2, 2], ![0, 1, 0, 1, 1], ![0, 1, 0, 1, 1]], ![![0, 0, 0, 2, 2], ![0, 2, 0, 2, 2], ![0, 1, 0, 2, 2], ![0, 1, 0, 2, 2]], ![![0, 2, 0, 2, 2], ![0, 1, 0, 1, 1], ![0, 1, 0, 2, 2], ![0, 1, 0, 2, 2]]], ![![![1, 0, 1, 0, 2], ![0, 0, 2, 2, 2], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 2, 1, 1], ![1, 0, 1, 2, 1], ![1, 0, 2, 1, 0], ![1, 0, 2, 1, 0]], ![![2, 0, 0, 2, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 2, 1], ![1, 0, 0, 2, 1]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 1, 0, 1, 1], ![0, 1, 0, 1, 1]], ![![0, 1, 0, 2, 2], ![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 2, 2], ![0, 0, 0, 2, 2]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]),
   Sum.elim ![![![![2, 1, 1, 1, 2], ![2, 0, 1, 1, 2], ![1, 0, 2, 1, 1], ![2, 1, 0, 0, 1]], ![![2, 1, 0, 0, 1], ![2, 0, 2, 2, 0], ![0, 2, 2, 0, 2], ![2, 1, 1, 1, 2]], ![![2, 0, 0, 2, 1], ![2, 1, 1, 0, 2], ![1, 0, 0, 1, 2], ![2, 1, 1, 0, 2]]], ![![![1, 0, 2, 2, 1], ![2, 0, 0, 1, 2], ![1, 2, 0, 2, 2], ![2, 0, 1, 1, 2]], ![![2, 0, 1, 1, 2], ![1, 0, 1, 2, 1], ![2, 1, 0, 1, 1], ![1, 0, 2, 2, 1]], ![![0, 0, 2, 2, 0], ![1, 1, 2, 0, 0], ![0, 0, 1, 1, 0], ![1, 1, 2, 0, 0]]], ![![![0, 2, 0, 2, 2], ![1, 0, 1, 0, 2], ![2, 0, 2, 2, 2], ![1, 2, 1, 0, 2]], ![![1, 2, 1, 2, 1], ![0, 0, 0, 2, 2], ![2, 1, 2, 2, 1], ![0, 2, 0, 1, 1]], ![![2, 0, 2, 2, 2], ![0, 2, 0, 2, 1], ![1, 0, 1, 0, 0], ![0, 2, 0, 1, 0]]]] (Sum.elim ![![![![1, 1, 0, 2, 1], ![0, 0, 2, 2, 2], ![0, 1, 1, 2, 2], ![0, 1, 1, 2, 2]], ![![0, 1, 1, 0, 0], ![1, 0, 1, 2, 1], ![1, 1, 0, 0, 2], ![1, 1, 0, 0, 2]], ![![2, 0, 0, 2, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 2, 1], ![1, 0, 0, 2, 1]]], ![![![2, 1, 1, 2, 1], ![0, 0, 2, 1, 1], ![1, 0, 2, 0, 1], ![2, 1, 0, 2, 1]], ![![1, 0, 2, 2, 0], ![0, 0, 0, 1, 1], ![2, 1, 1, 1, 0], ![1, 0, 0, 2, 0]], ![![0, 0, 1, 1, 1], ![1, 1, 0, 1, 2], ![2, 2, 1, 2, 1], ![0, 0, 2, 1, 1]]], ![![![2, 1, 0, 2, 0], ![0, 0, 1, 1, 1], ![0, 1, 2, 2, 2], ![0, 1, 2, 2, 2]], ![![0, 1, 2, 1, 1], ![2, 0, 2, 1, 2], ![2, 1, 0, 1, 2], ![2, 1, 0, 1, 2]], ![![1, 0, 0, 1, 0], ![2, 0, 0, 2, 0], ![2, 0, 0, 1, 2], ![2, 0, 0, 1, 2]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]] ![![![![0, 1, 0, 1, 1], ![1, 0, 0, 1, 0], ![1, 1, 1, 0, 2], ![1, 1, 1, 0, 2]], ![![1, 1, 1, 0, 2], ![0, 0, 2, 2, 2], ![0, 1, 0, 1, 1], ![0, 1, 0, 1, 1]], ![![1, 0, 1, 2, 1], ![2, 0, 2, 1, 2], ![2, 0, 2, 1, 2], ![2, 0, 2, 1, 2]]], ![![![1, 1, 1, 0, 1], ![2, 0, 2, 1, 2], ![0, 1, 0, 1, 0], ![0, 1, 0, 1, 0]], ![![1, 2, 1, 1, 1], ![0, 0, 0, 0, 0], ![2, 2, 2, 0, 2], ![2, 2, 2, 0, 2]], ![![1, 2, 1, 1, 1], ![2, 1, 2, 2, 2], ![0, 2, 0, 2, 0], ![0, 2, 0, 2, 0]]], ![![![1, 1, 2, 1, 2], ![2, 0, 1, 0, 1], ![0, 1, 2, 0, 2], ![0, 1, 2, 0, 2]], ![![1, 2, 0, 0, 0], ![0, 0, 1, 1, 1], ![2, 2, 0, 1, 0], ![2, 2, 0, 1, 0]], ![![1, 0, 0, 1, 1], ![2, 0, 0, 2, 2], ![0, 1, 1, 2, 0], ![0, 1, 1, 2, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![1, 1, 0, 2, 2], ![1, 0, 0, 1, 0], ![0, 1, 1, 2, 0], ![0, 1, 1, 2, 0]], ![![2, 0, 0, 2, 2], ![2, 0, 2, 1, 2], ![0, 0, 2, 2, 1], ![0, 0, 2, 2, 1]], ![![0, 0, 1, 1, 0], ![0, 0, 2, 2, 0], ![2, 2, 1, 2, 2], ![2, 2, 1, 2, 2]]]]),
   Sum.elim ![![![![2, 2, 1, 1, 0], ![0, 0, 2, 1, 2], ![0, 1, 1, 2, 2], ![0, 0, 1, 0, 1]], ![![0, 1, 1, 1, 0], ![2, 2, 2, 2, 2], ![2, 1, 1, 1, 2], ![2, 0, 1, 2, 2]], ![![1, 0, 2, 1, 1], ![2, 2, 1, 0, 2], ![2, 2, 1, 2, 0], ![2, 0, 1, 1, 0]]], ![![![2, 2, 2, 1, 1], ![0, 2, 0, 0, 2], ![0, 0, 0, 0, 0], ![0, 1, 0, 2, 1]], ![![0, 0, 0, 1, 2], ![2, 0, 2, 2, 1], ![2, 0, 2, 1, 2], ![2, 1, 2, 0, 2]], ![![1, 2, 1, 0, 1], ![2, 2, 2, 2, 2], ![2, 2, 2, 0, 1], ![2, 1, 2, 1, 1]]], ![![![1, 2, 0, 1, 0], ![0, 0, 2, 0, 0], ![0, 1, 1, 2, 2], ![0, 2, 1, 1, 1]], ![![0, 2, 1, 1, 1], ![1, 0, 1, 0, 2], ![1, 1, 0, 2, 1], ![1, 2, 0, 1, 0]], ![![2, 1, 0, 2, 0], ![1, 0, 0, 0, 2], ![1, 1, 0, 2, 1], ![1, 0, 0, 0, 2]]]] (Sum.elim ![![![![0, 1, 1, 2, 1], ![0, 0, 1, 1, 1], ![2, 0, 1, 0, 2], ![1, 1, 0, 2, 0]], ![![2, 1, 1, 1, 0], ![2, 0, 2, 1, 2], ![0, 2, 1, 0, 2], ![1, 1, 2, 1, 1]], ![![1, 0, 0, 1, 0], ![1, 1, 2, 1, 1], ![0, 0, 1, 1, 0], ![2, 1, 0, 0, 1]]], ![![![2, 0, 0, 0, 2], ![0, 2, 1, 1, 1], ![1, 1, 0, 2, 0], ![2, 1, 1, 2, 1]], ![![1, 2, 0, 1, 2], ![0, 1, 0, 2, 2], ![2, 2, 0, 1, 0], ![1, 1, 2, 2, 0]], ![![0, 1, 2, 2, 2], ![1, 2, 2, 1, 2], ![2, 2, 0, 1, 0], ![0, 0, 1, 0, 0]]], ![![![0, 1, 2, 2, 0], ![0, 0, 2, 1, 1], ![1, 0, 2, 0, 1], ![2, 1, 0, 2, 1]], ![![1, 0, 2, 2, 0], ![1, 0, 1, 1, 0], ![0, 0, 2, 2, 0], ![2, 0, 1, 2, 2]], ![![2, 2, 0, 2, 0], ![2, 2, 1, 0, 0], ![0, 1, 2, 0, 1], ![1, 1, 0, 0, 2]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]] ![![![![1, 1, 0, 2, 0], ![1, 0, 0, 0, 2], ![2, 2, 0, 1, 0], ![2, 1, 0, 2, 2]], ![![1, 2, 1, 1, 1], ![1, 0, 0, 0, 2], ![0, 1, 2, 2, 1], ![0, 2, 1, 1, 2]], ![![2, 0, 1, 0, 1], ![2, 2, 2, 1, 0], ![0, 1, 2, 2, 1], ![0, 0, 0, 0, 0]]], ![![![2, 0, 1, 1, 2], ![0, 1, 2, 0, 2], ![1, 1, 2, 1, 2], ![2, 0, 0, 2, 0]], ![![1, 0, 2, 1, 0], ![0, 2, 0, 2, 0], ![2, 2, 1, 1, 0], ![1, 0, 0, 0, 2]], ![![0, 1, 1, 1, 0], ![1, 2, 0, 0, 0], ![2, 2, 1, 1, 0], ![0, 1, 2, 2, 1]]], ![![![0, 1, 2, 2, 1], ![0, 0, 2, 0, 0], ![2, 2, 0, 1, 0], ![1, 1, 2, 2, 0]], ![![2, 2, 1, 1, 0], ![2, 0, 0, 0, 1], ![0, 1, 2, 2, 1], ![1, 2, 1, 1, 1]], ![![1, 0, 1, 0, 2], ![1, 2, 2, 1, 1], ![0, 1, 2, 2, 1], ![2, 0, 0, 0, 1]]], ![![![2, 0, 0, 1, 2], ![0, 0, 1, 1, 1], ![0, 0, 2, 2, 2], ![0, 0, 2, 2, 2]], ![![0, 0, 2, 1, 1], ![2, 0, 2, 1, 2], ![2, 0, 0, 0, 1], ![2, 0, 0, 0, 1]], ![![1, 0, 0, 2, 1], ![2, 0, 0, 2, 0], ![2, 0, 0, 0, 1], ![2, 0, 0, 0, 1]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]),
   Sum.elim ![![![![1, 0, 0, 0, 0], ![2, 0, 1, 2, 0], ![1, 0, 2, 0, 2], ![0, 0, 1, 0, 1]], ![![0, 2, 1, 2, 1], ![0, 0, 0, 2, 2], ![1, 0, 0, 1, 0], ![1, 2, 0, 2, 0]], ![![2, 1, 0, 1, 0], ![0, 2, 2, 2, 0], ![0, 0, 2, 2, 2], ![0, 1, 2, 1, 2]]], ![![![1, 1, 2, 2, 0], ![1, 0, 2, 1, 0], ![1, 1, 0, 2, 1], ![2, 1, 1, 2, 2]], ![![2, 2, 1, 0, 2], ![0, 0, 0, 1, 1], ![1, 1, 2, 1, 0], ![1, 2, 2, 0, 0]], ![![1, 2, 0, 2, 0], ![0, 1, 1, 1, 0], ![0, 0, 1, 1, 1], ![0, 2, 1, 2, 1]]], ![![![2, 2, 1, 1, 2], ![1, 0, 0, 0, 2], ![1, 0, 2, 0, 0], ![1, 2, 2, 1, 0]], ![![1, 2, 2, 1, 0], ![2, 0, 2, 0, 1], ![0, 2, 2, 1, 0], ![2, 2, 1, 1, 2]], ![![1, 1, 2, 2, 2], ![2, 1, 1, 2, 2], ![1, 1, 0, 2, 0], ![2, 1, 1, 2, 1]]]] (Sum.elim ![![![![2, 2, 0, 1, 1], ![2, 0, 0, 2, 0], ![2, 0, 1, 0, 2], ![0, 2, 2, 1, 0]], ![![1, 0, 0, 1, 1], ![1, 0, 1, 2, 1], ![1, 2, 2, 2, 0], ![0, 0, 1, 1, 2]], ![![0, 0, 2, 2, 2], ![1, 2, 2, 2, 2], ![1, 1, 2, 1, 2], ![2, 0, 0, 2, 0]]], ![![![2, 1, 1, 2, 1], ![2, 0, 1, 1, 2], ![1, 0, 2, 0, 1], ![1, 1, 2, 2, 2]], ![![0, 0, 1, 2, 1], ![0, 0, 0, 1, 1], ![2, 1, 1, 1, 0], ![1, 0, 0, 2, 0]], ![![2, 0, 0, 1, 2], ![1, 1, 0, 1, 2], ![2, 2, 1, 2, 1], ![0, 0, 2, 1, 1]]], ![![![0, 2, 0, 1, 2], ![1, 0, 1, 1, 0], ![2, 1, 2, 2, 2], ![0, 2, 0, 1, 2]], ![![2, 1, 2, 1, 1], ![1, 0, 1, 1, 0], ![2, 2, 2, 0, 2], ![2, 1, 2, 1, 1]], ![![0, 0, 0, 1, 1], ![1, 1, 1, 1, 2], ![0, 2, 0, 2, 0], ![0, 0, 0, 1, 1]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]] ![![![![0, 1, 0, 2, 2], ![0, 0, 2, 2, 2], ![2, 2, 2, 1, 0], ![0, 1, 0, 2, 2]], ![![0, 1, 2, 0, 0], ![0, 0, 2, 2, 2], ![1, 1, 1, 0, 1], ![0, 1, 2, 0, 0]], ![![2, 1, 0, 1, 0], ![1, 1, 1, 0, 1], ![1, 1, 1, 1, 2], ![2, 1, 0, 1, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 2, 2], ![0, 1, 0, 2, 2], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 2, 2], ![0, 0, 0, 2, 2], ![0, 1, 0, 1, 1], ![0, 0, 0, 2, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 0, 0, 1, 1], ![0, 1, 0, 0, 0]]], ![![![1, 1, 1, 2, 0], ![0, 0, 1, 2, 2], ![2, 2, 2, 1, 0], ![1, 1, 1, 2, 0]], ![![2, 2, 0, 2, 1], ![0, 0, 1, 2, 2], ![1, 1, 1, 0, 1], ![2, 2, 0, 2, 1]], ![![0, 0, 2, 2, 2], ![2, 2, 2, 2, 1], ![1, 1, 1, 1, 2], ![0, 0, 2, 2, 2]]], ![![![0, 2, 0, 1, 1], ![0, 0, 0, 0, 0], ![0, 2, 0, 1, 1], ![0, 2, 0, 1, 1]], ![![0, 2, 0, 2, 2], ![0, 0, 0, 0, 0], ![0, 2, 0, 2, 2], ![0, 2, 0, 2, 2]], ![![0, 0, 0, 2, 2], ![0, 0, 0, 0, 0], ![0, 0, 0, 2, 2], ![0, 0, 0, 2, 2]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]]),
   Sum.elim ![![![![2, 1, 2, 1, 1], ![0, 0, 0, 2, 2], ![2, 2, 2, 0, 2], ![1, 1, 1, 2, 0]], ![![2, 2, 2, 2, 1], ![1, 0, 1, 1, 0], ![2, 1, 2, 2, 2], ![0, 2, 0, 1, 2]], ![![2, 0, 2, 2, 0], ![0, 2, 0, 0, 1], ![2, 1, 2, 2, 2], ![1, 0, 1, 0, 2]]], ![![![0, 2, 0, 0, 2], ![2, 0, 2, 0, 1], ![2, 1, 2, 2, 1], ![0, 2, 0, 1, 0]], ![![1, 0, 1, 2, 2], ![2, 0, 2, 2, 0], ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 1]], ![![1, 2, 1, 2, 0], ![0, 2, 0, 2, 2], ![1, 0, 1, 0, 1], ![1, 0, 1, 0, 1]]], ![![![2, 0, 2, 0, 2], ![2, 0, 2, 1, 2], ![1, 0, 1, 2, 0], ![1, 0, 1, 2, 2]], ![![0, 2, 0, 0, 2], ![0, 0, 0, 2, 2], ![0, 1, 0, 2, 0], ![1, 2, 1, 1, 2]], ![![0, 2, 0, 2, 1], ![0, 1, 0, 0, 1], ![0, 1, 0, 2, 0], ![2, 0, 2, 1, 1]]]] (Sum.elim ![![![![1, 2, 0, 0, 2], ![0, 0, 2, 2, 2], ![0, 2, 1, 0, 0], ![0, 2, 1, 0, 0]], ![![0, 2, 1, 0, 0], ![1, 0, 1, 2, 1], ![1, 2, 0, 0, 2], ![1, 2, 0, 0, 2]], ![![2, 0, 0, 2, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 1, 0]]], ![![![1, 1, 1, 0, 2], ![0, 0, 0, 0, 0], ![0, 1, 0, 1, 1], ![0, 1, 0, 1, 1]], ![![0, 1, 0, 1, 1], ![1, 0, 1, 2, 1], ![1, 1, 1, 0, 2], ![1, 1, 1, 0, 2]], ![![2, 0, 2, 1, 2], ![1, 0, 1, 2, 1], ![1, 0, 1, 2, 1], ![1, 0, 1, 2, 1]]], ![![![2, 0, 0, 2, 0], ![0, 0, 1, 1, 1], ![0, 0, 2, 2, 2], ![0, 0, 2, 2, 2]], ![![0, 0, 2, 2, 2], ![2, 0, 2, 1, 2], ![2, 0, 0, 2, 0], ![2, 0, 0, 2, 0]], ![![1, 0, 0, 1, 0], ![2, 0, 0, 2, 0], ![2, 0, 0, 2, 0], ![2, 0, 0, 2, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]] ![![![![0, 0, 0, 0, 2], ![2, 0, 2, 0, 1], ![2, 0, 1, 0, 2], ![0, 0, 1, 0, 2]], ![![1, 1, 2, 2, 2], ![2, 0, 1, 0, 1], ![1, 2, 2, 1, 2], ![1, 1, 1, 2, 2]], ![![2, 1, 1, 2, 1], ![1, 2, 2, 1, 2], ![1, 2, 2, 1, 2], ![2, 0, 0, 0, 2]]], ![![![0, 0, 2, 0, 1], ![1, 0, 0, 0, 2], ![1, 0, 2, 0, 1], ![0, 0, 1, 0, 1]], ![![2, 2, 0, 1, 1], ![1, 0, 1, 0, 2], ![2, 1, 1, 2, 1], ![2, 2, 1, 1, 1]], ![![2, 0, 0, 0, 2], ![0, 2, 2, 1, 1], ![2, 1, 1, 2, 1], ![2, 1, 1, 2, 1]]], ![![![0, 1, 0, 2, 1], ![0, 0, 0, 0, 0], ![2, 2, 0, 1, 0], ![1, 1, 0, 2, 0]], ![![2, 2, 1, 1, 0], ![2, 0, 0, 0, 1], ![0, 1, 2, 2, 1], ![1, 2, 1, 1, 1]], ![![1, 0, 2, 0, 2], ![1, 2, 0, 1, 1], ![0, 1, 2, 2, 1], ![2, 0, 1, 0, 1]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![2, 2, 1, 1, 2], ![1, 0, 0, 0, 2], ![0, 1, 1, 2, 2], ![1, 2, 2, 1, 0]], ![![1, 2, 2, 1, 0], ![2, 0, 2, 0, 1], ![1, 1, 0, 2, 1], ![2, 2, 1, 1, 2]], ![![1, 1, 2, 2, 2], ![0, 0, 2, 0, 1], ![1, 1, 0, 2, 1], ![0, 0, 2, 0, 1]]]]),
   Sum.elim ![![![![1, 0, 1, 0, 0], ![0, 0, 0, 1, 1], ![1, 2, 1, 1, 2], ![2, 0, 0, 0, 2]], ![![1, 2, 0, 0, 1], ![2, 0, 1, 1, 2], ![1, 0, 2, 2, 2], ![0, 2, 1, 0, 2]], ![![1, 0, 2, 1, 0], ![0, 1, 1, 1, 0], ![1, 2, 0, 2, 2], ![2, 0, 1, 1, 2]]], ![![![2, 1, 0, 2, 2], ![0, 0, 0, 2, 2], ![2, 2, 0, 1, 0], ![1, 1, 1, 2, 0]], ![![2, 2, 1, 2, 1], ![1, 0, 2, 2, 1], ![2, 1, 2, 0, 0], ![0, 2, 0, 2, 0]], ![![2, 0, 1, 2, 0], ![0, 2, 2, 2, 0], ![2, 1, 0, 1, 1], ![1, 0, 2, 2, 1]]], ![![![0, 1, 1, 2, 0], ![0, 0, 1, 1, 1], ![1, 0, 2, 0, 1], ![2, 1, 2, 2, 1]], ![![1, 0, 0, 2, 0], ![1, 0, 0, 1, 0], ![0, 1, 2, 1, 2], ![2, 0, 2, 2, 2]], ![![2, 0, 1, 1, 2], ![2, 1, 1, 1, 1], ![0, 2, 2, 2, 0], ![1, 0, 2, 1, 0]]]] (Sum.elim ![![![![1, 0, 2, 0, 1], ![0, 0, 1, 1, 1], ![2, 1, 2, 2, 1], ![1, 0, 2, 0, 1]], ![![2, 1, 1, 1, 0], ![0, 0, 1, 1, 1], ![1, 0, 1, 2, 0], ![2, 1, 1, 1, 0]], ![![0, 0, 1, 1, 1], ![2, 2, 2, 0, 2], ![1, 1, 1, 0, 1], ![0, 0, 1, 1, 1]]], ![![![2, 0, 2, 0, 2], ![0, 0, 0, 2, 2], ![1, 2, 1, 1, 2], ![2, 0, 2, 0, 2]], ![![1, 2, 0, 2, 0], ![0, 0, 0, 2, 2], ![2, 0, 2, 1, 0], ![1, 2, 0, 2, 0]], ![![0, 0, 1, 2, 2], ![1, 1, 0, 0, 1], ![2, 2, 2, 0, 2], ![0, 0, 1, 2, 2]]], ![![![0, 1, 0, 2, 0], ![0, 0, 1, 2, 2], ![1, 0, 2, 0, 1], ![2, 1, 1, 2, 1]], ![![1, 0, 2, 1, 2], ![1, 0, 0, 2, 1], ![0, 1, 2, 0, 1], ![2, 0, 1, 1, 1]], ![![2, 0, 1, 2, 0], ![2, 1, 1, 0, 0], ![0, 2, 1, 0, 1], ![1, 0, 2, 2, 1]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]]] ![![![![2, 0, 2, 0, 0], ![1, 0, 1, 1, 0], ![0, 0, 0, 0, 0], ![2, 0, 2, 0, 0]], ![![0, 1, 0, 1, 2], ![1, 0, 1, 1, 0], ![2, 0, 2, 2, 0], ![0, 1, 0, 1, 2]], ![![2, 2, 2, 2, 1], ![1, 1, 1, 1, 2], ![0, 0, 0, 1, 0], ![2, 2, 2, 2, 1]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 2, 2], ![0, 2, 0, 2, 2], ![0, 1, 0, 0, 0]], ![![0, 1, 0, 2, 2], ![0, 0, 0, 2, 2], ![0, 2, 0, 1, 1], ![0, 1, 0, 2, 2]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 1, 1], ![0, 2, 0, 1, 1], ![0, 0, 0, 0, 0]]], ![![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0]]], ![![![1, 2, 1, 2, 1], ![1, 0, 1, 0, 2], ![2, 0, 2, 1, 0], ![1, 2, 1, 2, 1]], ![![1, 2, 1, 0, 2], ![1, 0, 1, 0, 2], ![0, 2, 0, 0, 2], ![1, 2, 1, 0, 2]], ![![1, 1, 1, 0, 1], ![1, 1, 1, 2, 0], ![2, 1, 2, 0, 1], ![1, 1, 1, 0, 1]]], ![![![2, 0, 2, 0, 1], ![2, 0, 2, 0, 1], ![1, 2, 1, 1, 2], ![2, 0, 2, 0, 1]], ![![2, 0, 2, 0, 1], ![2, 0, 2, 0, 1], ![0, 0, 0, 0, 1], ![2, 0, 2, 0, 1]], ![![2, 2, 2, 1, 0], ![2, 2, 2, 1, 0], ![1, 2, 1, 1, 0], ![2, 2, 2, 1, 0]]]])]) t s i j k
def A : Matrix I J ℤ := fun (i,j,k) (t,s) =>
  match s with
  | .inl h => if h = i then ((Y t j).val : ℤ) * ((Z t k).val : ℤ) else 0
  | .inr (.inl h) => if h = j then ((X t i).val : ℤ) * ((Z t k).val : ℤ) else 0
  | .inr (.inr h) => if h = k then ((X t i).val : ℤ) * ((Y t j).val : ℤ) else 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row0 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,0,0) l =
    (1 : Matrix I I (ZMod 3)) (0,0,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row1 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,0,1) l =
    (1 : Matrix I I (ZMod 3)) (0,0,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row2 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,0,2) l =
    (1 : Matrix I I (ZMod 3)) (0,0,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row3 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,0,3) l =
    (1 : Matrix I I (ZMod 3)) (0,0,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row4 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,0,4) l =
    (1 : Matrix I I (ZMod 3)) (0,0,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row5 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,1,0) l =
    (1 : Matrix I I (ZMod 3)) (0,1,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row6 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,1,1) l =
    (1 : Matrix I I (ZMod 3)) (0,1,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row7 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,1,2) l =
    (1 : Matrix I I (ZMod 3)) (0,1,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row8 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,1,3) l =
    (1 : Matrix I I (ZMod 3)) (0,1,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row9 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,1,4) l =
    (1 : Matrix I I (ZMod 3)) (0,1,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row10 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,2,0) l =
    (1 : Matrix I I (ZMod 3)) (0,2,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row11 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,2,1) l =
    (1 : Matrix I I (ZMod 3)) (0,2,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row12 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,2,2) l =
    (1 : Matrix I I (ZMod 3)) (0,2,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row13 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,2,3) l =
    (1 : Matrix I I (ZMod 3)) (0,2,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row14 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,2,4) l =
    (1 : Matrix I I (ZMod 3)) (0,2,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row15 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,3,0) l =
    (1 : Matrix I I (ZMod 3)) (0,3,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row16 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,3,1) l =
    (1 : Matrix I I (ZMod 3)) (0,3,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row17 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,3,2) l =
    (1 : Matrix I I (ZMod 3)) (0,3,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row18 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,3,3) l =
    (1 : Matrix I I (ZMod 3)) (0,3,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row19 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (0,3,4) l =
    (1 : Matrix I I (ZMod 3)) (0,3,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row20 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,0,0) l =
    (1 : Matrix I I (ZMod 3)) (1,0,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row21 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,0,1) l =
    (1 : Matrix I I (ZMod 3)) (1,0,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row22 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,0,2) l =
    (1 : Matrix I I (ZMod 3)) (1,0,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row23 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,0,3) l =
    (1 : Matrix I I (ZMod 3)) (1,0,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row24 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,0,4) l =
    (1 : Matrix I I (ZMod 3)) (1,0,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row25 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,1,0) l =
    (1 : Matrix I I (ZMod 3)) (1,1,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row26 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,1,1) l =
    (1 : Matrix I I (ZMod 3)) (1,1,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row27 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,1,2) l =
    (1 : Matrix I I (ZMod 3)) (1,1,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row28 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,1,3) l =
    (1 : Matrix I I (ZMod 3)) (1,1,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row29 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,1,4) l =
    (1 : Matrix I I (ZMod 3)) (1,1,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row30 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,2,0) l =
    (1 : Matrix I I (ZMod 3)) (1,2,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row31 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,2,1) l =
    (1 : Matrix I I (ZMod 3)) (1,2,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row32 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,2,2) l =
    (1 : Matrix I I (ZMod 3)) (1,2,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row33 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,2,3) l =
    (1 : Matrix I I (ZMod 3)) (1,2,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row34 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,2,4) l =
    (1 : Matrix I I (ZMod 3)) (1,2,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row35 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,3,0) l =
    (1 : Matrix I I (ZMod 3)) (1,3,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row36 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,3,1) l =
    (1 : Matrix I I (ZMod 3)) (1,3,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row37 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,3,2) l =
    (1 : Matrix I I (ZMod 3)) (1,3,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row38 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,3,3) l =
    (1 : Matrix I I (ZMod 3)) (1,3,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row39 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (1,3,4) l =
    (1 : Matrix I I (ZMod 3)) (1,3,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row40 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,0,0) l =
    (1 : Matrix I I (ZMod 3)) (2,0,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row41 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,0,1) l =
    (1 : Matrix I I (ZMod 3)) (2,0,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row42 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,0,2) l =
    (1 : Matrix I I (ZMod 3)) (2,0,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row43 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,0,3) l =
    (1 : Matrix I I (ZMod 3)) (2,0,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row44 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,0,4) l =
    (1 : Matrix I I (ZMod 3)) (2,0,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row45 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,1,0) l =
    (1 : Matrix I I (ZMod 3)) (2,1,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row46 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,1,1) l =
    (1 : Matrix I I (ZMod 3)) (2,1,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row47 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,1,2) l =
    (1 : Matrix I I (ZMod 3)) (2,1,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row48 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,1,3) l =
    (1 : Matrix I I (ZMod 3)) (2,1,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row49 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,1,4) l =
    (1 : Matrix I I (ZMod 3)) (2,1,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row50 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,2,0) l =
    (1 : Matrix I I (ZMod 3)) (2,2,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row51 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,2,1) l =
    (1 : Matrix I I (ZMod 3)) (2,2,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row52 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,2,2) l =
    (1 : Matrix I I (ZMod 3)) (2,2,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row53 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,2,3) l =
    (1 : Matrix I I (ZMod 3)) (2,2,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row54 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,2,4) l =
    (1 : Matrix I I (ZMod 3)) (2,2,4) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row55 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,3,0) l =
    (1 : Matrix I I (ZMod 3)) (2,3,0) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row56 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,3,1) l =
    (1 : Matrix I I (ZMod 3)) (2,3,1) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row57 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,3,2) l =
    (1 : Matrix I I (ZMod 3)) (2,3,2) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row58 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,3,3) l =
    (1 : Matrix I I (ZMod 3)) (2,3,3) l := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def row59 : ∀ l : I, (A.map (Int.castRingHom (ZMod 3)) * B) (2,3,4) l =
    (1 : Matrix I I (ZMod 3)) (2,3,4) l := by decide +kernel
end TensorCertificate

open TensorCertificate in
theorem OMA.solution : OMA.R_Arxiv_0805_3777_isGenericRank_of_le_critical_R1_H2_R2_H2_R1.H1 := by
  refine ⟨X, Y, Z, B, ?_⟩
  change A.map (Int.castRingHom (ZMod 3)) * B = 1
  apply Matrix.ext
  rintro ⟨i,j,k⟩ l
  fin_cases i <;> fin_cases j <;> fin_cases k
  · exact row0 l
  · exact row1 l
  · exact row2 l
  · exact row3 l
  · exact row4 l
  · exact row5 l
  · exact row6 l
  · exact row7 l
  · exact row8 l
  · exact row9 l
  · exact row10 l
  · exact row11 l
  · exact row12 l
  · exact row13 l
  · exact row14 l
  · exact row15 l
  · exact row16 l
  · exact row17 l
  · exact row18 l
  · exact row19 l
  · exact row20 l
  · exact row21 l
  · exact row22 l
  · exact row23 l
  · exact row24 l
  · exact row25 l
  · exact row26 l
  · exact row27 l
  · exact row28 l
  · exact row29 l
  · exact row30 l
  · exact row31 l
  · exact row32 l
  · exact row33 l
  · exact row34 l
  · exact row35 l
  · exact row36 l
  · exact row37 l
  · exact row38 l
  · exact row39 l
  · exact row40 l
  · exact row41 l
  · exact row42 l
  · exact row43 l
  · exact row44 l
  · exact row45 l
  · exact row46 l
  · exact row47 l
  · exact row48 l
  · exact row49 l
  · exact row50 l
  · exact row51 l
  · exact row52 l
  · exact row53 l
  · exact row54 l
  · exact row55 l
  · exact row56 l
  · exact row57 l
  · exact row58 l
  · exact row59 l
