import Mathlib

/-!
# A finite rational sum-of-squares expansion for the matrix trace inequality

Source: Richard Martin, https://mathoverflow.net/questions/314826 (CC BY-SA 4.0).
Martin gives low-degree expansions and credits Mikael de la Salle with the
Hölder proof of the inequality. Contribution by @connoranderson.

The coefficients below depend only on the exponent. The Dirichlet matrix of
binary words records the two reflections across the middle of the word, with
a one-letter cyclic rotation on the left reflection. On a constant word the
matrix has the identity row. Its inverse gives the expansion coefficients by
ordinary finite rational matrix arithmetic. A squared Frobenius norm of the
difference of two block words is a sum of squared absolute values of entries.
-/

namespace OMA.S_mo_314826
open Matrix Finset
abbrev Word (n : ℕ) := List.Vector Bool (2*n)

def reflectLeft : List Bool → List Bool
  | [] => []
  | b::s => b::b::(s++s.reverse)

def leftWord {n : ℕ} (s : Word n) : Word n :=
  ⟨reflectLeft (s.1.take n),by
    have length_reflect (u : List Bool) : (reflectLeft u).length=2*u.length := by
      cases u <;> simp [reflectLeft]; omega
    rw [length_reflect,List.length_take,s.2,Nat.min_eq_left (by omega)]⟩
def rightWord {n : ℕ} (s : Word n) : Word n :=
  ⟨(s.1.drop n).reverse ++ s.1.drop n,by simp [s.2];omega⟩
def terminal {n : ℕ} (s : Word n) : Prop :=
  s.1 = List.replicate (2*n) false ∨ s.1 = List.replicate (2*n) true
instance {n : ℕ} (s : Word n) : Decidable (terminal s) :=
  inferInstanceAs (Decidable (_ ∨ _))

def dirichlet {n : ℕ} (s t : Word n) : ℚ :=
  (if s=t then 1 else 0) - (if terminal s then 0 else
    ((if leftWord s=t then 1 else 0)+(if rightWord s=t then 1 else 0))/2)

def dirMatrix (n : ℕ) : Matrix (Word n) (Word n) ℚ := Matrix.of dirichlet
noncomputable def greenMatrix (n : ℕ) : Matrix (Word n) (Word n) ℚ := (dirMatrix n)⁻¹

def alternating (n : ℕ) : Word n :=
  ⟨(List.replicate n [false,true]).flatten, by induction n with
    | zero => rfl
    | succ n ih => simp only [List.replicate_succ,List.flatten_cons,List.length_append] at *;simp;omega⟩

noncomputable def weight (n : ℕ) (s : Word n) : ℚ :=
  if terminal s then 0 else (greenMatrix n (alternating n) s)/2

abbrev Rect (m k : ℕ) := Matrix (Fin m) (Fin k) ℂ
noncomputable def dilate {m k : ℕ} (A : Rect m k) : Matrix (Fin m ⊕ Fin k) (Fin m ⊕ Fin k) ℂ :=
  Matrix.fromBlocks 0 A Aᴴ 0
noncomputable def evalWord {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (u : List Bool) : Matrix ι ι ℂ :=
  (u.map (fun b => if b then B else A)).prod
noncomputable def frobSq {ι : Type*} [Fintype ι] (M : Matrix ι ι ℂ) : ℝ :=
  (M*Mᴴ).trace.re

theorem main : ∀ (n : ℕ), 0<n → (∀ s : Word n, 0≤weight n s) ∧
    ∀ (m k : ℕ) (A B : Rect m k),
      ((A*Aᴴ)^n).trace.re + ((B*Bᴴ)^n).trace.re - 2*((A*Bᴴ)^n).trace.re =
        ∑ s : Word n, (weight n s:ℝ) * frobSq
          (evalWord (dilate A) (dilate B) (s.1.take n) - (evalWord (dilate A) (dilate B) (s.1.drop n))ᴴ) ∧
      2*((A*Bᴴ)^n).trace.re ≤ ((A*Aᴴ)^n).trace.re + ((B*Bᴴ)^n).trace.re := by sorry

end OMA.S_mo_314826
