import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1
import Mathlib

/-! A diameter pentagon has one, three or five distinct short chords. The regular case uses a circle parametrization, the asymmetric case has a unique admissible external word, and the remaining symmetric case has two potentially new lengths. -/

open EuclideanGeometry
namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1_H3_R1

def H1 : Prop := ∀A S:Finset ℝ²,NonTrilinear (A:Set ℝ²)→S⊆A→∀p:Fin 5→ℝ²,(∀i,p i∈A)→(∀i,p i∉S)→Function.Injective p→∀s:ℝ,0<s→∀a:ℝ,0<a→a^2-3*a+1=0→(let w:Fin 5→ℝ:=fun _=>a;∀i j:Fin 5,(if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j)=s*dist (p i) (p j)^2)→∀D:Finset ℝ,D.card≤5→(∀d∈D,0<d∧d<1)→(∀x∈S,∀i,s*dist (p i) x^2∈D)→(∀x∈S,∀y∈S,x≠y→s*dist x y^2∈D)→a∈D→S.card≤8

def H2 : Prop := ∀A S:Finset ℝ²,NonTrilinear (A:Set ℝ²)→∀p:Fin 5→ℝ²,(∀i,p i∈A)→Function.Injective p→∀s:ℝ,0<s→∀w:Fin 5→ℝ,(∀i,0<w i∧w i<1)→Function.Injective w→(∀i j:Fin 5,(if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j)=s*dist (p i) (p j)^2)→(∀x∈S,∀i,∃j,w j=s*dist (p i) x^2)→S.card≤1

def H3 : Prop := ∀A S:Finset ℝ²,NonTrilinear (A:Set ℝ²)→S⊆A→∀p:Fin 5→ℝ²,(∀i,p i∈A)→(∀i,p i∉S)→Function.Injective p→∀s:ℝ,0<s→∀a b:ℝ,0<a→a<1→0<b→b<1→a≠b→a≠(a-1)^2→b≠(a-1)^2→(let w:Fin 5→ℝ:=![a,a,b,(a-1)^2,b];∀i j:Fin 5,(if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j)=s*dist (p i) (p j)^2)→∀D:Finset ℝ,D.card≤5→(∀d∈D,0<d∧d<1)→(∀x∈S,∀i,s*dist (p i) x^2∈D)→a∈D→b∈D→(a-1)^2∈D→S.card≤8

def H4 : Prop := (∀A S:Finset ℝ²,NonTrilinear (A:Set ℝ²)→S⊆A→∀p:Fin 5→ℝ²,(∀i,p i∈A)→(∀i,p i∉S)→Function.Injective p→∀s:ℝ,0<s→∀a:ℝ,0<a→a^2-3*a+1=0→(let w:Fin 5→ℝ:=fun _=>a;∀i j:Fin 5,(if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j)=s*dist (p i) (p j)^2)→∀D:Finset ℝ,D.card≤5→(∀d∈D,0<d∧d<1)→(∀x∈S,∀i,s*dist (p i) x^2∈D)→(∀x∈S,∀y∈S,x≠y→s*dist x y^2∈D)→a∈D→S.card≤8)→(∀A S:Finset ℝ²,NonTrilinear (A:Set ℝ²)→∀p:Fin 5→ℝ²,(∀i,p i∈A)→Function.Injective p→∀s:ℝ,0<s→∀w:Fin 5→ℝ,(∀i,0<w i∧w i<1)→Function.Injective w→(∀i j:Fin 5,(if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j)=s*dist (p i) (p j)^2)→(∀x∈S,∀i,∃j,w j=s*dist (p i) x^2)→S.card≤1)→(∀A S:Finset ℝ²,NonTrilinear (A:Set ℝ²)→S⊆A→∀p:Fin 5→ℝ²,(∀i,p i∈A)→(∀i,p i∉S)→Function.Injective p→∀s:ℝ,0<s→∀a b:ℝ,0<a→a<1→0<b→b<1→a≠b→a≠(a-1)^2→b≠(a-1)^2→(let w:Fin 5→ℝ:=![a,a,b,(a-1)^2,b];∀i j:Fin 5,(if i=j then 0 else if j=i+1 ∨ i=j+1 then 1 else if j=i+2 then w i else w j)=s*dist (p i) (p j)^2)→∀D:Finset ℝ,D.card≤5→(∀d∈D,0<d∧d<1)→(∀x∈S,∀i,s*dist (p i) x^2∈D)→a∈D→b∈D→(a-1)^2∈D→S.card≤8)→∀A:Finset ℝ²,NonTrilinear (A:Set ℝ²)→∀M:ℝ,0<M→(∀x y:A,dist x.1 y.1≤M)→(∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M)→distanceMultiplicity A M≤5→(distanceSet A).card≤6→A.card≤13

theorem main : H1 → H2 → H3 → H4 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H3 := fun a b c h=>h a b c
end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1_H3_R1
