import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1
import Mathlib

/-! Separation of the planar argument and the finite catalogue of exterior distance words. The fourth label may represent a different distance at every point. -/

open EuclideanGeometry
namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1_H1_R1

/-- Geometry given the six-word bound for each parameter. -/
def H1 : Prop := (∃W:ℝ→Finset ℕ,(∀a,(W a).card≤6)∧ ∀r:Fin 5→Fin 4,∀a b t:ℝ,let h:=fun x y:ℝ=>1+x-y;let v:=fun x y z:ℝ=>2*(x+a-z)-a*h x y;let E:=fun x y z u w q l:ℝ=>(4*a-a^2)*(2*(x+u-l)-h x y*h u w)-v x y z*v u w q;let A:=fun r:Fin 5→Fin 4=>let u:=fun i:Fin 5=>(![a,b,(a-1)^2,t]:Fin 4→ℝ) (r i);a^2*b+b^2-3*a*b-2*b+1=0∧E (u 0) (u 1) (u 2) (u 0) (u 1) (u 2) 0=0∧E (u 0) (u 1) (u 2) ((a-1)^2) a 1 (u 3)=0∧E (u 0) (u 1) (u 2) 1 b b (u 4)=0;0<a→a<1→a≠(a-1)^2→t≠b→t≠(a-1)^2→A r→A ![r 3,r 2,r 1,r 0,r 4]→(256*(r 0).val+64*(r 1).val+16*(r 2).val+4*(r 3).val+(r 4).val)∈W a)→∀A:Finset ℝ²,NonTrilinear (A:Set ℝ²)→∀M:ℝ,0<M→(∀x y:A,dist x.1 y.1≤M)→((∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M)→distanceMultiplicity A M≤5→(distanceSet A).card≤5→A.card≤11) ∧ (∀z:Fin 5→A,Function.Injective z→(∀i,dist (z i).1 (z (i+1)).1=M)→let D:=Finset.univ.image (fun i:Fin 5=>dist (z i).1 (z (i+2)).1); D.card=3→(A.filter fun x=>(Finset.univ.image (fun i:Fin 5=>dist (z i).1 x)\D).card≤1).card≤6)

/-- A catalogue with at most six compatible words at each parameter. -/
def H2 : Prop := ∃W:ℝ→Finset ℕ,(∀a,(W a).card≤6)∧ ∀r:Fin 5→Fin 4,∀a b t:ℝ,let h:=fun x y:ℝ=>1+x-y;let v:=fun x y z:ℝ=>2*(x+a-z)-a*h x y;let E:=fun x y z u w q l:ℝ=>(4*a-a^2)*(2*(x+u-l)-h x y*h u w)-v x y z*v u w q;let A:=fun r:Fin 5→Fin 4=>let u:=fun i:Fin 5=>(![a,b,(a-1)^2,t]:Fin 4→ℝ) (r i);a^2*b+b^2-3*a*b-2*b+1=0∧E (u 0) (u 1) (u 2) (u 0) (u 1) (u 2) 0=0∧E (u 0) (u 1) (u 2) ((a-1)^2) a 1 (u 3)=0∧E (u 0) (u 1) (u 2) 1 b b (u 4)=0;0<a→a<1→a≠(a-1)^2→t≠b→t≠(a-1)^2→A r→A ![r 3,r 2,r 1,r 0,r 4]→(256*(r 0).val+64*(r 1).val+16*(r 2).val+4*(r 3).val+(r 4).val)∈W a

theorem main : H1 → H2 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H1 := by
  intro geometry catalogue
  exact geometry catalogue
end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1_H1_R1
