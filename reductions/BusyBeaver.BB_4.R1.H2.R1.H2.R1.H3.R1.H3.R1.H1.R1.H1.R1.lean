import OMAReductions.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1
import Mathlib

/-! Split the single-hole FAR search by the missing state `h`. Each batch has
one quarter of the 524288 tables (131072). -/
-- Credit: @pageman
namespace OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1
open Turing Turing.BusyBeaver

private def cert (N : Machine (Fin 2) (Fin 4)) : Prop :=
  ∃ (n m : ℕ) (x : Fin n) (y : Fin m) (L : Fin 2 → Fin n → Fin n)
      (R : Fin 2 → Fin m → Fin m) (S : Fin 4 → Fin 2 → Fin n → Fin m → Bool),
      L 0 x=x ∧ R 0 y=y ∧ S 0 0 x y=true ∧
      ∀ q a s t i j, S q a (L s i) (R t j)=true →
        ∃ r w d, N q a=some (some r,Stmt.write w d) ∧
          (match d with
           | .left => S r s i (R w (R t j))
           | .right => S r t (L w (L s i)) j) = true

private def hole (h : Fin 4) : Prop :=
  ∀ (a b c : Fin 2) (q : Fin 4) (u : Fin 4 → Fin 4 × Stmt (Fin 2)),
    let v : Fin 4 → Fin 4 × Stmt (Fin 2) :=
      ![(1,.write 1 .right),(2,.write a .right),(3,.write b .right),(q,.write c .left)]
    let N : Machine (Fin 2) (Fin 4) := fun r s =>
      if s=0 then some (some (v r).1,(v r).2) else if r=h then none else some (some (u r).1,(u r).2)
    (∃ r T,N.multiStep (Machine.init []) 107 = some ⟨some r,T⟩) → cert N

def H1 : Prop := hole 0
def H2 : Prop := hole 1
def H3 : Prop := hole 2
def H4 : Prop := hole 3

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1.H1 := by
  intro h0 h1 h2 h3 a b c q h u
  fin_cases h
  · exact h0 a b c q u
  · exact h1 a b c q u
  · exact h2 a b c q u
  · exact h3 a b c q u

end OMA.R_BusyBeaver_BB_4_R1_H2_R1_H2_R1_H3_R1_H3_R1_H1_R1_H1_R1
