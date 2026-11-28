import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1
import Mathlib
/- Adapted from openai/math (Apache-2.0) 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
open scoped Classical
open Module Filter

def H1 : Prop :=
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let good := fun (d : ℕ) (q : Q) => haveI : Fact q.val.Prime := ⟨q.2.1⟩; let K := ZMod q.val; ∀(E : Type)[AddCommGroup E][Module K E][Finite E](w : LinearMap.BilinForm K E),w.IsAlt → w.Nondegenerate → 2*d=finrank K E → ∀ L M N : {S : Submodule K E // w.orthogonal S=S},
    let n := fun S : Submodule K E => finrank K S
    let c := n (L.1⊓M.1⊓N.1)
    let b := fun S => (n S-c+1).choose 2
    let a : ℝ := (d+1)*2^d
    (q.val:ℝ)^(3*(d+1).choose 2) ≤ (a*((a*2^d)*(8*(4^d*a^2))))*(q.val:ℝ)^((d+1)*c+(b (L.1⊓M.1)+b (L.1⊓N.1)+b (M.1⊓N.1)))*Nat.card {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,(∀ x y,w (e x) (e y)=w x y) ∧ L.1.map e.toLinearMap=p.1 ∧ M.1.map e.toLinearMap=p.2.1 ∧ N.1.map e.toLinearMap=p.2.2}
  ∀ d, ∀ᶠ q in (Filter.comap (fun q : Q => q.val) Filter.atTop), good d q

def H2 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let good := fun (d : ℕ) (q : Q) => haveI : Fact q.val.Prime := ⟨q.2.1⟩; let K := ZMod q.val; ∀(E : Type)[AddCommGroup E][Module K E][Finite E](w : LinearMap.BilinForm K E),w.IsAlt → w.Nondegenerate → 2*d=finrank K E → ∀ L M N : {S : Submodule K E // w.orthogonal S=S},
    let n := fun S : Submodule K E => finrank K S
    let c := n (L.1⊓M.1⊓N.1)
    let b := fun S => (n S-c+1).choose 2
    let a : ℝ := (d+1)*2^d
    (q.val:ℝ)^(3*(d+1).choose 2) ≤ (a*((a*2^d)*(8*(4^d*a^2))))*(q.val:ℝ)^((d+1)*c+(b (L.1⊓M.1)+b (L.1⊓N.1)+b (M.1⊓N.1)))*Nat.card {p : Submodule K E × Submodule K E × Submodule K E // ∃ e : E ≃ₗ[K] E,(∀ x y,w (e x) (e y)=w x y) ∧ L.1.map e.toLinearMap=p.1 ∧ M.1.map e.toLinearMap=p.2.1 ∧ N.1.map e.toLinearMap=p.2.2}
  let G := fun (d : ℕ) (T : Fin 22 → Finset (Fin 3)) (q : Q) => haveI : Fact q.val.Prime := ⟨q.2.1⟩; let K := ZMod q.val; let V := Fin d → K; let E := V × Module.Dual K V; letI : Finite E := Module.finite_of_finite K; let L := {S : Submodule K E // ∀ x, x ∈ S ↔ ∀ y ∈ S, x.2 y.1 = y.2 x.1}; letI := Fintype.ofFinite L; let n := fun S : Submodule K E => finrank K S; let m := (Nat.card L:ℝ)/Nat.card {Y : L // n ((LinearMap.fst K V (Module.Dual K V)).ker ⊓ Y.1)=d/2}; (∑ X : Fin 13 → L, if ∃ j k, n ((X (t j (sL k))).1 ⊓ (X (t j (sR k))).1)≠0 then ∏ j, ((Nat.card {Y : L // ∀ k ∈ T j,n ((X (t j k)).1 ⊓ Y.1)=d/2}:ℝ)/Nat.card L*m^(T j).card) else 0)/(Nat.card L:ℝ)^13
  ∃ d : ℕ, 4 ∣ d ∧ 12 ≤ d ∧ ∀ T, Tendsto (G d T) ((Filter.comap (fun q : Q => q.val) Filter.atTop) ⊓ Filter.principal {q | good d q}) (nhds 0)

def H3 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let U := fun {A : Type} [Fintype A] (f : A → ℝ) => (∑ a, f a) / (Fintype.card A : ℝ)
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
    let G := fun (d : ℕ) (T : Fin 22 → Finset (Fin 3)) (q : Q) => haveI : Fact q.val.Prime := ⟨q.2.1⟩; let K := ZMod q.val; let V := Fin d → K; let E := V × Module.Dual K V; letI : Finite E := Module.finite_of_finite K; let L := {S : Submodule K E // ∀ x, x ∈ S ↔ ∀ y ∈ S, x.2 y.1 = y.2 x.1}; letI := Fintype.ofFinite L; let n := fun S : Submodule K E => finrank K S; let m := (Nat.card L:ℝ)/Nat.card {Y : L // n ((LinearMap.fst K V (Module.Dual K V)).ker ⊓ Y.1)=d/2}; (∑ X : Fin 13 → L, if ∃ j k, n ((X (t j (sL k))).1 ⊓ (X (t j (sR k))).1)≠0 then ∏ j, ((Nat.card {Y : L // ∀ k ∈ T j,n ((X (t j k)).1 ⊓ Y.1)=d/2}:ℝ)/Nat.card L*m^(T j).card) else 0)/(Nat.card L:ℝ)^13
  let S := fun (d : ℕ) (q : Q) => {A : Matrix (Fin d) (Fin d) (ZMod q.val) // A.IsSymm}
  ∀ d : ℕ, 4 ∣ d → 12 ≤ d → (∀ T, Tendsto (G d T) (Filter.comap (fun q : Q => q.val) Filter.atTop) (nhds 0)) → (∀ T : Fin 22 → Finset (Fin 3), Filter.Tendsto (fun q : Q => haveI : Fact (q.val.Prime) := ⟨q.2.1⟩; haveI : NeZero q.val := ⟨q.2.1.ne_zero⟩; U (fun X : Fin 13 → S d q => if ∃ j k, ((X (t j (sL k))).val-(X (t j (sR k))).val).det=0 then ∏ j, U (fun Y : S d q => ∏ k ∈ T j, if ((X (t j k)).val-Y.val).rank=d/2 then (U (fun Z : S d q => if Z.val.rank=d/2 then (1:ℝ) else 0))⁻¹ else 0) else 0)) (Filter.comap (fun q : Q => q.val) Filter.atTop) (nhds 0))

theorem main : H1 → H2 → H3 → OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1.H2 := by
  intro ha hb hc
  obtain ⟨d,h4,hd,h⟩ := hb
  refine ⟨d,h4,hd,hc d h4 hd (fun T => ?_)⟩
  have ht := h T
  rwa [inf_eq_left.mpr (Filter.le_principal_iff.mpr (ha d))] at ht
end OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
