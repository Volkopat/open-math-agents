import OMAReductions.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1
import Mathlib

/-! Isolate the sixteen-point seven-distance case. The residual configurations have at least eight distances and retain the circle, diameter, field and multiplicity hypotheses. -/

open EuclideanGeometry
namespace OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1_H4_R1

def H1 : Prop := ∀A:Finset ℝ²,NonTrilinear (A:Set ℝ²)→∀M:ℝ,0<M→(∀x y:A,dist x.1 y.1≤M)→(∃ a b c d e : A, [a,b,c,d,e].Nodup ∧ dist a.1 b.1=M ∧ dist b.1 c.1=M ∧ dist c.1 d.1=M ∧
      dist d.1 e.1=M ∧ dist e.1 a.1=M)→distanceMultiplicity A M≤5→(distanceSet A).card≤7→A.card≤15

def H2 : Prop := ∀ A:Finset ℝ²,let D:=distinctDistances A;let n:=A.card; NonTrilinear (A:Set ℝ²)→n=2*D+2→8≤D→(∀ (c:ℝ²) (r:ℝ), 3*(A.filter (fun z=>dist z c=r)).card≤4*D+2)→(let k:= fun b:ℝ²×ℝ² => (A.filter fun p=> dist p b.1=dist p b.2).card
    (9*n-30)+(A.offDiag.filter fun b=> k b=0).card≤(A.offDiag.filter fun b=> k b=2).card)→(∀ (T:Finset Circle) (G:Subgroup Circle) (m:ℕ) (P:Finset ℂ) (f:ℂ→ℝ²) (s:ℝ),
      (G:Set Circle)=T→2≤ m→m.Coprime T.card→0<s→(∀ x y, dist (f x) (f y)=s*dist x y)→(∀ z∈T, f (z:ℂ)∈A)→(∀ p∈P, f p∈A)→(∀ p∈P, p≠0∧‖p‖≠1)→Set.InjOn (fun p:ℂ => ‖p‖) (P:Set ℂ)→P.card*T.card+(2*min m 9)*P.card≤2*D+(2*min m 9)*P.card*P.card)→∀ M∈distanceSet A, (∀ d∈distanceSet A, d≤M)→(∃ B⊆A, n/2≤B.card∧∀ x∈B, ∀ y∈B, dist x y<M)→(∃ d∈(distanceSet A).erase M, n+4≤distanceMultiplicity A d)→distanceMultiplicity A M≤5→(∃ a b c d e:A, [a,b,c,d,e].Nodup∧dist a.1 b.1=M∧dist b.1 c.1=M∧dist c.1 d.1=M∧dist d.1 e.1=M∧dist e.1 a.1=M)→(∀c:ℝ²,∀r:ℝ,2*(A.filter fun x => dist x c=r).card≤n+35)→(∀K:Subfield ℝ,(∀d∈distanceSet A,d/M∈K)→IsEmpty (K→+*ℚ_[2])∧Even (Module.finrank ℚ K))→(∀d∈(distanceSet A).erase M,(∀u∈(distanceSet A).erase M,u≤d)→(3-Real.sqrt 5)*M^2≤2*d^2∧distanceMultiplicity A d≤n+10∧((3-Real.sqrt 5)*M^2<2*d^2→distanceMultiplicity A d≤n+7))→(∀z:Fin 5→A,Function.Injective z→(∀i,dist (z i).1 (z (i+1)).1=M)→∀r:ℝ,let g:=fun i=>dist (z i).1 (z (i+2)).1; 3≤(Finset.univ.filter fun i=>g i=r).card→∀i,g i=r)→((∃s:ℝ,0<s∧∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q)→(∀c:ℝ²,∀r:ℝ,(A.filter fun x => dist x c=r).card≤n/2+2))→(∀z:Fin 5→A,Function.Injective z→(∀i,dist (z i).1 (z (i+1)).1=M)→(∃s:ℝ,0<s∧∀x∈A,∀y∈A,∃q:ℚ,dist x y^2=s*q)→Function.Injective (fun i:Fin 5=>dist (z i).1 (z (i+2)).1))→(∀z:Fin 5→A,Function.Injective z→(∀i,dist (z i).1 (z (i+1)).1=M)→let D:=Finset.univ.image (fun i:Fin 5=>dist (z i).1 (z (i+2)).1); D.card=3→(A.filter fun x=>(Finset.univ.image (fun i:Fin 5=>dist (z i).1 x)\D).card≤1).card≤6)→∃ x∈A, ∃ y∈A.erase x, ∃ d∈distanceSet A, d∉distanceSet ((A.erase x).erase y)

theorem main : H1 → H2 → OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1.H4 := by
  classical
  intro seven large A
  try dsimp only
  intro hn nc d7 cir bis orb M mM lim independent many few pent thin fields sec rigid sqcap rational low
  by_cases d8:8≤distinctDistances A
  · exact large A hn nc d8 cir bis orb M mM lim independent many few pent thin fields sec rigid sqcap rational low
  have hm:0<M := by
    obtain ⟨⟨x,y⟩,hp,e⟩:=Finset.mem_image.mp mM
    exact e ▸ dist_pos.mpr (Finset.mem_offDiag.mp hp).2.2
  have bound (x y:A):dist x.1 y.1≤M := by
    by_cases eq:x=y
    · simpa [eq] using hm.le
    · exact lim _ (Finset.mem_image.mpr ⟨(x.1,y.1),Finset.mem_offDiag.mpr ⟨x.2,y.2,Subtype.coe_injective.ne eq⟩,rfl⟩)
  have cap:=seven A hn M hm bound pent few (by change distinctDistances A≤7;omega)
  omega
end OMA.R_Erdos1082_erdos_1082_parts_i_R1_H2_R1_H2_R1_H3_R1_H4_R1
