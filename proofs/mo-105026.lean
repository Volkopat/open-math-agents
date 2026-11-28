import OMAStatements.S_mo_105026
import Mathlib

/-!
MathOverflow 105026: the four-element commutative semiring `{0, 1, a, b}` with `1 + x = 1` for
`x ≠ 0`, `a + b = a`, `x + x = x`, and `xy = 0` for `x, y ∈ {a, b}`. Its only prime ideal is
`{0, a, b}`, which is subtractive; the ideal `{0, a}` is not (`a + b = a`).
-/

namespace OMA.P105026

open OMA.S_mo_105026

/-- A four-element commutative semiring `{0, 1, a, b}`. -/
inductive T : Type
  | z | o | a | b
  deriving DecidableEq

namespace T

def add : T → T → T
  | z, x => x
  | x, z => x
  | o, _ => o
  | _, o => o
  | a, _ => a
  | b, a => a
  | b, b => b

def mul : T → T → T
  | z, _ => z
  | _, z => z
  | o, x => x
  | x, o => x
  | _, _ => z

instance : Fintype T := ⟨{z, o, a, b}, by intro x; cases x <;> simp⟩

instance : Zero T := ⟨z⟩
instance : One T := ⟨o⟩
instance : Add T := ⟨add⟩
instance : Mul T := ⟨mul⟩

instance : CommSemiring T where
  add_assoc x y w := by cases x <;> cases y <;> cases w <;> rfl
  zero_add x := by cases x <;> rfl
  add_zero x := by cases x <;> rfl
  add_comm x y := by cases x <;> cases y <;> rfl
  mul_assoc x y w := by cases x <;> cases y <;> cases w <;> rfl
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  zero_mul x := by cases x <;> rfl
  mul_zero x := by cases x <;> rfl
  left_distrib x y w := by cases x <;> cases y <;> cases w <;> rfl
  right_distrib x y w := by cases x <;> cases y <;> cases w <;> rfl
  mul_comm x y := by cases x <;> cases y <;> rfl
  nsmul := nsmulRec
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  npow := npowRec
  npow_zero _ := rfl
  npow_succ _ _ := rfl

lemma zero_def : (0 : T) = z := rfl
lemma one_def : (1 : T) = o := rfl
lemma add_def (x y : T) : x + y = add x y := rfl
lemma mul_def (x y : T) : x * y = mul x y := rfl

instance : Nontrivial T := ⟨⟨z, o, by decide⟩⟩

lemma prime_subtractive (P : Ideal T) (hP : P.IsPrime) : IsSubtractive P := by
  have hz : z ∈ P := P.zero_mem
  have ho : o ∉ P := fun h => hP.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have ha : a ∈ P := by
    have : a * a ∈ P := by rw [mul_def]; exact hz
    rcases hP.mem_or_mem this with h | h <;> exact h
  have hb : b ∈ P := by
    have : b * b ∈ P := by rw [mul_def]; exact hz
    rcases hP.mem_or_mem this with h | h <;> exact h
  intro x y hxy hx
  cases y with
  | z => exact hz
  | a => exact ha
  | b => exact hb
  | o =>
    exfalso
    cases x <;> exact ho hxy

/-- The ideal `{0, a}`. -/
def I : Ideal T where
  carrier := {x | x = z ∨ x = a}
  add_mem' := by
    intro x y hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      first | exact Or.inl rfl | exact Or.inr rfl
  zero_mem' := Or.inl rfl
  smul_mem' := by
    intro c x hx
    rcases hx with rfl | rfl <;> cases c <;>
      first | exact Or.inl rfl | exact Or.inr rfl

lemma I_not : ¬ IsSubtractive I := by
  intro h
  have := h a b (Or.inr rfl) (Or.inr rfl)
  rcases this with h1 | h1 <;> exact absurd h1 (by decide)

theorem disproof_aux :
    ¬ ∀ (S : Type) [CommSemiring S] [Nontrivial S],
      (∀ P : Ideal S, P.IsPrime → IsSubtractive P) → ∀ I : Ideal S, IsSubtractive I := by
  intro h
  exact I_not (h T prime_subtractive I)

end T

end OMA.P105026

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_105026.main) := OMA.P105026.T.disproof_aux
