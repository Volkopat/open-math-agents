import OMAStatements.S_mo_369021

-- Problem: MathOverflow 369021, a (4, 3) system of mutually orthogonal Latin hypercubes.
-- Identify Fin 4 with GF(4) = {0, 1, w, w^2} (codes 0, 1, 2, 3) and take L_c(x) = sum_a M_(c,a) x_a with
-- M = [[1,1,1],[1,w,w^2],[1,w^2,w]]. Every entry of M is nonzero, so each L_c is a bijection along every
-- axis line, and M is invertible (inverse [[1,1,1],[1,w^2,w],[1,w,w^2]]), so the overlay is a bijection.
-- Both facts are checked by evaluation on the 64 cells.

namespace OMA.MO369021

def gadd (a b : Fin 4) : Fin 4 := ![![0, 1, 2, 3], ![1, 0, 3, 2], ![2, 3, 0, 1], ![3, 2, 1, 0]] a b
def gmul (a b : Fin 4) : Fin 4 := ![![0, 0, 0, 0], ![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2]] a b
def M : Fin 3 → Fin 3 → Fin 4 := ![![1, 1, 1], ![1, 2, 3], ![1, 3, 2]]
def L (c : Fin 3) (x : Fin 3 → Fin 4) : Fin 4 :=
  gadd (gadd (gmul (M c 0) (x 0)) (gmul (M c 1) (x 1))) (gmul (M c 2) (x 2))

def Minv : Fin 3 → Fin 3 → Fin 4 := ![![1, 1, 1], ![1, 3, 2], ![1, 2, 3]]
def Linv (y : Fin 3 → Fin 4) (a : Fin 3) : Fin 4 :=
  gadd (gadd (gmul (Minv a 0) (y 0)) (gmul (Minv a 1) (y 1))) (gmul (Minv a 2) (y 2))

lemma vec_eta (x : Fin 3 → Fin 4) : x = ![x 0, x 1, x 2] := by
  ext i; fin_cases i <;> rfl

lemma inv_triple : ∀ a b c : Fin 4, ∀ i : Fin 3,
    Linv (fun k => L k ![a, b, c]) i = ![a, b, c] i := by decide

lemma ortho : Function.Bijective (fun x : Fin 3 → Fin 4 => fun c : Fin 3 => L c x) := by
  rw [← Finite.injective_iff_bijective]
  refine Function.LeftInverse.injective (g := Linv) fun x => ?_
  rw [vec_eta x]
  funext i
  exact inv_triple _ _ _ i

set_option maxHeartbeats 4000000 in
lemma latin_triple : ∀ c a : Fin 3, ∀ x0 x1 x2 : Fin 4,
    Function.Bijective (fun s : Fin 4 => L c (Function.update ![x0, x1, x2] a s)) := by decide

end OMA.MO369021

theorem OMA.solution : type_of% @OMA.S_mo_369021.main := by
  refine ⟨OMA.MO369021.L, fun c a x => ?_, OMA.MO369021.ortho⟩
  rw [OMA.MO369021.vec_eta x]
  exact OMA.MO369021.latin_triple c a _ _ _
