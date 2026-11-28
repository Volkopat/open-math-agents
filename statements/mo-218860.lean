import Mathlib

/-!
# Injective linear projections of Veronese coordinates

Source: user45183, https://mathoverflow.net/questions/218860 (CC BY-SA 3.0).
Credit: @connoranderson (agent: Codex)

A multiset of coordinate indices represents one commutative monomial. Thus
the bounded nonempty multisets index each monomial of degrees 1 through p
exactly once. In the matrix kernel test, the two trial points are explicit
functions of the linear and quadratic entries of a single kernel vector.
-/

namespace OMA.S_mo_218860

def quadratic (x : ℝ × ℝ) : Fin 5 → ℝ := ![x.1,x.2,x.1^2,x.1*x.2,x.2^2]

abbrev Mono (d p : ℕ) := {s : Multiset (Fin d) // 0 < s.card ∧ s.card ≤ p}

noncomputable instance (d p : ℕ) : Fintype (Mono d p) := by
  let counts (s : Mono d p) (i : Fin d) : Fin (p+1) :=
    ⟨s.1.count i,Nat.lt_succ_of_le ((Multiset.count_le_card i s.1).trans s.2.2)⟩
  refine @Fintype.ofFinite _ (Finite.of_injective counts ?_)
  intro a b h
  apply Subtype.ext
  exact Multiset.ext.mpr fun i => congrArg Fin.val (congrFun h i)

def linIdx {d p : ℕ} (hp : 2 ≤ p) (i : Fin d) : Mono d p := ⟨{i},by simp; omega⟩
def quadIdx {d p : ℕ} (hp : 2 ≤ p) (i j : Fin d) : Mono d p := ⟨i ::ₘ {j},by simpa⟩

def veronese {d p : ℕ} (x : Fin d → ℝ) (s : Mono d p) : ℝ := (s.1.map x).prod

noncomputable def midpointSum {d p : ℕ} (hp : 2 ≤ p) (v : Mono d p → ℝ) (j i : Fin d) : ℝ :=
  (2*v (quadIdx hp i j) - v (linIdx hp i) * (v (quadIdx hp j j)/v (linIdx hp j))) / v (linIdx hp j)

noncomputable def reconstructed {d p : ℕ} (hp : 2 ≤ p) (v : Mono d p → ℝ) (j : Fin d) (sign : ℝ) (i : Fin d) : ℝ :=
  (midpointSum hp v j i + sign * v (linIdx hp i))/2

theorem main :
    (∀ (m : ℕ) (A : Matrix (Fin m) (Fin 5) ℝ),
      Function.Injective (fun x : ℝ × ℝ => A.mulVec (quadratic x)) ↔
      ∀ v, A.mulVec v = 0 → (v 1)^2*v 2 - 2*v 0*v 1*v 3 + (v 0)^2*v 4 = 0 → v 0 = 0 ∧ v 1 = 0) ∧
    (∀ (d m p : ℕ) (hp : 2 ≤ p) (A : Matrix (Fin m) (Mono d p) ℝ),
      Function.Injective (fun x : Fin d → ℝ => A.mulVec (veronese x)) ↔
      ∀ v, A.mulVec v = 0 → ∀ j, v (linIdx hp j) ≠ 0 →
        ∃ s, v s ≠ veronese (reconstructed hp v j 1) s - veronese (reconstructed hp v j (-1)) s) ∧
    (∀ (d m : ℕ) (A : Matrix (Fin m) (Fin d) ℝ), Function.Injective A.mulVec ↔
      ∀ v, A.mulVec v = 0 → v = 0) := by
  sorry

end OMA.S_mo_218860
