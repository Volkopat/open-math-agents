import OMAReductions.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1
import Mathlib

/-! Symplectic singular-tail and even-rank matrix limit reduction, adapted under Apache-2.0 from openai/math Sidorenko/Tail.lean and Sidorenko/GlobalMoments.lean. -/

namespace OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R2

open Module Filter

def H1 : Prop :=
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let sep : Fin 33 → ℕ := ![3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,1,1,1,2]
  let tri (x : ℝ) := x*(x+1)/2
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let V D (q : Q) := Fin D → ZMod q.1
  let E D q := V D q × Dual (ZMod q.1) (V D q)
  let rk {D} {q : Q} (U : Submodule (ZMod q.1) (E D q)) := finrank (ZMod q.1) U
  let Lag D (q : Q) := {L : Submodule (ZMod q.1) (E D q) // ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L}
  let ptP D (q : Q) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → Lag D q) :=
    (∀ j, rk (((L (t j 0)).1 ⊓ (L (t j 1)).1) ⊓ (L (t j 2)).1) = c j) ∧
    (∀ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) = h (p j k))
  let pCnt D (q : Q) c h := (Nat.card {L // ptP D q c h L} : ℝ) / (Nat.card (Lag D q) : ℝ)^13
  let pCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :=
    (∑ j, (((D+1)*c j + ∑ k, (h (p j k)-c j+1).choose 2 : ℕ) : ℝ))/2 - (∑ e, (3-(sep e : ℝ))*tri (h e))/6
  ∀ D c h,
    (∀ q, Nonempty {L // ptP D q c h L} → (∀ j, c j ≤ D) ∧ (∀ j k, c j ≤ h (p j k)) ∧ ∀ j, (∑ k, (h (p j k)-c j)) ≤ D-c j) ∧
    ((∀ j, c j ≤ D) → ∃ C₁ ≥ 0, ∀ q, pCnt D q c h ≤ C₁*(q.1 : ℝ)^(-pCost D c h)) ∧
    (33 ≤ D → (∀ e, h e = 0 ∨ h e = 2) → ∃ C₂ ≥ 0, ∀ q, pCnt D q c h ≤ C₂*((q.1 : ℝ)^(-(∑ e, tri (h e))) + (q.1 : ℝ)^(-(D : ℝ)+1575)))

def H2 : Prop :=
 let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
 let sep : Fin 33 → ℕ := ![3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,1,1,1,2]
 let tri (x : ℝ) := x*(x+1)/2
 let pCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :=
  (∑ j, (((D+1)*c j + ∑ k, (h (p j k)-c j+1).choose 2 : ℕ) : ℝ))/2 - (∑ e, (3-(sep e : ℝ))*tri (h e))/6
 let pGain (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
  let δ : ℝ := 2*(u : ℝ)-c; let d : ℝ := (D : ℝ)-c; let P : ℝ := ∑ i, (pv i : ℝ)
  if b then ((d+c)/2+c+1)*((c+δ)/2) - 2*((c+δ)/2)^2 + (∑ i, tri ((pv i : ℝ)+tv i)) -
   δ*P - (∑ i, (pv i : ℝ)^2) - (v : ℝ)*((d-3*δ)/2-P+v) - (∑ i, tri (tv i)) + tri v
  else tri (((Finset.univ.sup fun i => c+(pv i+tv i))/2 : ℕ) : ℝ)
 let feas (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
  let δ : ℝ := 2*(u : ℝ)-c
  c ≤ D ∧ (∑ i, (pv i+tv i)) ≤ D-c ∧ (b = true → u ≤ c ∧ (∀ i, (tv i : ℝ) ≤ pv i+δ) ∧
   (∀ i, (v : ℝ) ≤ pv i+δ) ∧ 0 ≤ ((D : ℝ)-c-3*δ)/2-(∑ i, (pv i : ℝ))+v)
 ∃ D₀ ≥ 1642, ∀ D ≥ D₀, ∀ c h,
  (∀ j, c j ≤ D) → (∀ j k, c j ≤ h (p j k)) → (∀ j, (∑ k, (h (p j k)-c j)) ≤ D-c j) → (∃ e, h e ≠ 0) →
  ∀ (b : Fin 22 → Bool) (m : Fin 22 → ℕ) (w : ∀ j, Fin (m j) → ℝ) (u v : ∀ j, Fin (m j) → ℕ) (pv tv : ∀ j, Fin (m j) → Fin 3 → ℕ),
  (∀ j l, 0 ≤ w j l) → (∀ j l, feas D (c j) (u j l) (v j l) (b j) (pv j l) (tv j l)) →
  (∀ j l k, c j+(pv j l k+tv j l k) = h (p j k)) →
  ∀ (N : {q : ℕ // q.Prime ∧ q ≠ 2} → ℝ) (C₁ C₂ : ℝ), (∀ q, 0 ≤ N q) → (∀ q, N q ≤ C₁*(q.1 : ℝ)^(-pCost D c h)) →
   ((∀ e, h e = 0 ∨ h e = 2) → ∀ q, N q ≤ C₂*((q.1 : ℝ)^(-(∑ e, tri (h e))) + (q.1 : ℝ)^(-(D : ℝ)+1575))) →
   Tendsto (fun q => N q * ∏ j, ∑ l, w j l * (q.1 : ℝ)^pGain D (c j) (u j l) (v j l) (b j) (pv j l) (tv j l))
    (comap Subtype.val atTop) (nhds 0)

def H3 : Prop :=
 let tri (x : ℝ) := x*(x+1)/2
 let nc (A : Type) := (Nat.card A : ℝ)
 let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
 let V D (q : Q) := Fin D → ZMod q.1
 let E D q := V D q × Dual (ZMod q.1) (V D q)
 let rk {D} {q : Q} (U : Submodule (ZMod q.1) (E D q)) := finrank (ZMod q.1) U
 let Lag D (q : Q) := {L : Submodule (ZMod q.1) (E D q) // ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L}
 let afD D r (q : Q) (L : Fin 3 → Lag D q) (T : Finset (Fin 3)) :=
  nc {Y : Lag D q // ∀ i ∈ T, rk ((L i).1 ⊓ Y.1) = r} / nc (Lag D q) *
   (nc (Lag D q) / nc {M : Lag D q // rk (M.1 ⊓ LinearMap.ker (.fst _ _ _)) = r})^T.card
 let pGain (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
  let δ : ℝ := 2*(u : ℝ)-c; let d : ℝ := (D : ℝ)-c; let P : ℝ := ∑ i, (pv i : ℝ)
  if b then ((d+c)/2+c+1)*((c+δ)/2) - 2*((c+δ)/2)^2 + (∑ i, tri ((pv i : ℝ)+tv i)) -
   δ*P - (∑ i, (pv i : ℝ)^2) - (v : ℝ)*((d-3*δ)/2-P+v) - (∑ i, tri (tv i)) + tri v
  else tri (((Finset.univ.sup fun i => c+(pv i+tv i))/2 : ℕ) : ℝ)
 let feas (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
  let δ : ℝ := 2*(u : ℝ)-c
  c ≤ D ∧ (∑ i, (pv i+tv i)) ≤ D-c ∧ (b = true → u ≤ c ∧ (∀ i, (tv i : ℝ) ≤ pv i+δ) ∧
   (∀ i, (v : ℝ) ≤ pv i+δ) ∧ 0 ≤ ((D : ℝ)-c-3*δ)/2-(∑ i, (pv i : ℝ))+v)
 ∀ (r c : ℕ) (s : Fin 3 → ℕ) b, c ≤ 2*r → (∑ i, s i) ≤ 2*r-c →
  ∃ (Q₀ m : ℕ) (w : Fin m → ℝ) (u v : Fin m → ℕ) (pv tv : Fin m → Fin 3 → ℕ),
   (∀ l, 0 ≤ w l) ∧ (∀ l, feas (2*r) c (u l) (v l) b (pv l) (tv l)) ∧ (∀ l k, pv l k+tv l k = s k) ∧
   ∀ q, Q₀ ≤ q.1 → ∀ L T, decide (T = .univ) = b →
    rk (((L 0).1 ⊓ (L 1).1) ⊓ (L 2).1) = c → rk ((L 0).1 ⊓ (L 1).1) = c+s 0 →
    rk ((L 0).1 ⊓ (L 2).1) = c+s 1 → rk ((L 1).1 ⊓ (L 2).1) = c+s 2 →
    afD (2*r) r q L T ≤ ∑ l, w l * (q.1 : ℝ)^pGain (2*r) c (u l) (v l) b (pv l) (tv l)

def H4 : Prop :=
 let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
 let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
 let sL : Fin 3 → Fin 3 := ![0,0,1]; let sR : Fin 3 → Fin 3 := ![1,2,2]
 let uM {A : Type} [Fintype A] (f : A → ℝ) := (∑ a, f a)/(Fintype.card A : ℝ)
 let nc (A : Type) := (Nat.card A : ℝ); let pm (z : ℤ) := z=1 ∨ z= -1
 let Q := {q : ℕ // q.Prime ∧ q ≠ 2}; let lF := comap (Subtype.val : Q → ℕ) atTop
 let Tt := Fin 22 → Finset (Fin 3)
 ∀ r₀ ≥ 3,
  let V (q : Q) := Fin (4*r₀) → ZMod q.1; let E q := V q × Dual (ZMod q.1) (V q)
  let rk {q : Q} (U : Submodule (ZMod q.1) (E q)) := finrank (ZMod q.1) U
  let Lag (q : Q) := {L : Submodule (ZMod q.1) (E q) // ∀ w, (∀ x ∈ L, w.2 x.1-x.2 w.1=0) ↔ w ∈ L}
  let cL q := nc (Lag q)
  (∀ T : Tt, Tendsto (fun q => (∑' L : Fin 13 → Lag q, if ∃ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1)≠0
   then ∏ j, nc {Y : Lag q // ∀ i ∈ T j, rk ((L (t j i)).1 ⊓ Y.1)=2*r₀}/cL q *
    (cL q/nc {M : Lag q // rk (M.1 ⊓ LinearMap.ker (.fst _ _ _))=2*r₀})^(T j).card else 0)/cL q^13) lF (nhds 0)) →
  ∃ (M : Q → Type) (_ : ∀ q, AddCommGroup (M q)) (_ : ∀ q, Fintype (M q)) (R : ∀ q, ℤ → M q → ℝ),
   (∀ q ξ z, 0≤R q ξ z) ∧ (∀ q ξ, pm ξ → uM (R q ξ)=1) ∧ (∀ q ξ z, R q ξ (-z)=R q ξ z) ∧
   ∀ (T : Tt) (ξ : Fin 22 → Fin 3 → ℤ), (∀ j k, pm (ξ j k)) →
    Tendsto (fun q => uM (fun xy : (_ → _)×(_ → _) => ∏ j, ∏ k ∈ T j, R q (ξ j k) (xy.1 (t j k)-xy.2 j)))
     lF (nhds (uM (fun η : _ → Bool => ∏ j, ∏ k,
      if sL k ∈ T j ∧ sR k ∈ T j then 1+(if η (p j k) then 1 else -1)*(ξ j (sL k) : ℝ)*(ξ j (sR k) : ℝ) else 1)))

lemma lag_finite (D : ℕ) (q : {q : ℕ // q.Prime ∧ q ≠ 2}) :
    Finite {L : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) //
      ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L} := by
  have : NeZero q.1 := ⟨q.2.1.ne_zero⟩
  have : Finite (Dual (ZMod q.1) (Fin D → ZMod q.1)) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  have : Finite (Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1))) :=
    Finite.of_injective SetLike.coe SetLike.coe_injective
  exact Subtype.finite

lemma rk_lt (D : ℕ) (q : {q : ℕ // q.Prime ∧ q ≠ 2})
    (U : Submodule (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1))) :
    finrank (ZMod q.1) U < 2 * D + 1 := by
  have : Fact q.1.Prime := ⟨q.2.1⟩
  have hle : finrank (ZMod q.1) U ≤
      finrank (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) :=
    Submodule.finrank_le U
  have hE : finrank (ZMod q.1) ((Fin D → ZMod q.1) × Dual (ZMod q.1) (Fin D → ZMod q.1)) = 2 * D := by
    rw [Module.finrank_prod, Subspace.dual_finrank_eq, Module.finrank_pi, Fintype.card_fin]
    omega
  omega

lemma ep_spec :
    let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
    let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
    let sL : Fin 3 → Fin 3 := ![0,0,1]
    let sR : Fin 3 → Fin 3 := ![1,2,2]
    let eL : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]
    let eR : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]
    (∀ j k, eL (p j k) = t j (sL k) ∧ eR (p j k) = t j (sR k)) ∧
    (∀ e : Fin 33, ∃ j k, p j k = e) := by
  decide

lemma tendsto_tail_zero (h1 : H1) (h3 : H3) (D r : ℕ) (hDr : D = 2 * r) (h33 : 33 ≤ D)
    (T : Fin 22 → Finset (Fin 3))
    (h2D :
      let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
      let sep : Fin 33 → ℕ := ![3,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,1,1,1,1,2,1,1,2,1,1,1,1,1,2]
      let tri (x : ℝ) := x*(x+1)/2
      let pCost (D : ℕ) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) :=
        (∑ j, (((D+1)*c j + ∑ k, (h (p j k)-c j+1).choose 2 : ℕ) : ℝ))/2 - (∑ e, (3-(sep e : ℝ))*tri (h e))/6
      let pGain (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
        let δ : ℝ := 2*(u : ℝ)-c; let d : ℝ := (D : ℝ)-c; let P : ℝ := ∑ i, (pv i : ℝ)
        if b then ((d+c)/2+c+1)*((c+δ)/2) - 2*((c+δ)/2)^2 + (∑ i, tri ((pv i : ℝ)+tv i)) -
         δ*P - (∑ i, (pv i : ℝ)^2) - (v : ℝ)*((d-3*δ)/2-P+v) - (∑ i, tri (tv i)) + tri v
        else tri (((Finset.univ.sup fun i => c+(pv i+tv i))/2 : ℕ) : ℝ)
      let feas (D c u v : ℕ) (b : Bool) (pv tv : Fin 3 → ℕ) :=
        let δ : ℝ := 2*(u : ℝ)-c
        c ≤ D ∧ (∑ i, (pv i+tv i)) ≤ D-c ∧ (b = true → u ≤ c ∧ (∀ i, (tv i : ℝ) ≤ pv i+δ) ∧
         (∀ i, (v : ℝ) ≤ pv i+δ) ∧ 0 ≤ ((D : ℝ)-c-3*δ)/2-(∑ i, (pv i : ℝ))+v)
      ∀ c h,
        (∀ j, c j ≤ D) → (∀ j k, c j ≤ h (p j k)) → (∀ j, (∑ k, (h (p j k)-c j)) ≤ D-c j) → (∃ e, h e ≠ 0) →
        ∀ (b : Fin 22 → Bool) (m : Fin 22 → ℕ) (w : ∀ j, Fin (m j) → ℝ) (u v : ∀ j, Fin (m j) → ℕ) (pv tv : ∀ j, Fin (m j) → Fin 3 → ℕ),
        (∀ j l, 0 ≤ w j l) → (∀ j l, feas D (c j) (u j l) (v j l) (b j) (pv j l) (tv j l)) →
        (∀ j l k, c j+(pv j l k+tv j l k) = h (p j k)) →
        ∀ (N : {q : ℕ // q.Prime ∧ q ≠ 2} → ℝ) (C₁ C₂ : ℝ), (∀ q, 0 ≤ N q) → (∀ q, N q ≤ C₁*(q.1 : ℝ)^(-pCost D c h)) →
         ((∀ e, h e = 0 ∨ h e = 2) → ∀ q, N q ≤ C₂*((q.1 : ℝ)^(-(∑ e, tri (h e))) + (q.1 : ℝ)^(-(D : ℝ)+1575))) →
         Tendsto (fun q => N q * ∏ j, ∑ l, w j l * (q.1 : ℝ)^pGain D (c j) (u j l) (v j l) (b j) (pv j l) (tv j l))
          (comap Subtype.val atTop) (nhds 0)) :
    let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
    let sL : Fin 3 → Fin 3 := ![0,0,1]
    let sR : Fin 3 → Fin 3 := ![1,2,2]
    let nc (A : Type) := (Nat.card A : ℝ)
    let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
    let V (q : Q) := Fin D → ZMod q.1
    let E q := V q × Dual (ZMod q.1) (V q)
    let rk {q : Q} (U : Submodule (ZMod q.1) (E q)) := finrank (ZMod q.1) U
    let Lag (q : Q) := {L : Submodule (ZMod q.1) (E q) // ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L}
    let cL q := nc (Lag q)
    Tendsto (fun q => (∑' L : Fin 13 → Lag q,
      if ∃ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) ≠ 0
      then ∏ j, nc {Y : Lag q // ∀ i ∈ T j, rk ((L (t j i)).1 ⊓ Y.1) = r} / cL q *
        (cL q / nc {M : Lag q // rk (M.1 ⊓ LinearMap.ker (.fst _ _ _)) = r}) ^ (T j).card
      else 0) / cL q ^ 13) (comap Subtype.val atTop) (nhds 0) := by
  subst hDr
  dsimp only
  let t : Fin 22 → Fin 3 → Fin 13 := ![![0,1,3],![0,1,9],![0,2,3],![0,2,9],![1,3,10],![1,7,10],![1,7,12],![1,9,12],![2,3,4],![2,4,9],![3,4,11],![3,10,11],![4,8,9],![4,8,11],![5,6,7],![5,6,11],![5,7,10],![5,10,11],![6,7,12],![6,8,11],![6,8,12],![8,9,12]]
  let p : Fin 22 → Fin 3 → Fin 33 := ![![5,1,6],![5,3,9],![0,1,2],![0,3,4],![6,11,12],![19,11,20],![19,15,23],![9,15,16],![2,7,8],![7,4,10],![8,13,14],![12,13,21],![17,10,18],![17,14,22],![32,25,30],![32,27,29],![25,26,20],![26,27,21],![30,31,23],![28,29,22],![28,31,24],![18,24,16]]
  let sL : Fin 3 → Fin 3 := ![0,0,1]
  let sR : Fin 3 → Fin 3 := ![1,2,2]
  let eL : Fin 33 → Fin 13 := ![0,0,2,0,2,0,1,2,3,1,4,1,3,3,4,1,9,4,8,1,7,10,8,7,8,5,5,5,6,6,6,6,5]
  let eR : Fin 33 → Fin 13 := ![2,3,3,9,9,1,3,4,4,9,9,10,10,11,11,12,12,8,9,7,10,11,11,12,12,7,10,11,8,11,7,12,6]
  have hep : (∀ j k, eL (p j k) = t j (sL k) ∧ eR (p j k) = t j (sR k)) ∧
      (∀ e : Fin 33, ∃ j k, p j k = e) := ep_spec
  let nc (A : Type) := (Nat.card A : ℝ)
  let Q := {q : ℕ // q.Prime ∧ q ≠ 2}
  let V (q : Q) := Fin (2*r) → ZMod q.1
  let E (q : Q) := V q × Dual (ZMod q.1) (V q)
  let rk {q : Q} (U : Submodule (ZMod q.1) (E q)) := finrank (ZMod q.1) U
  let Lag (q : Q) := {L : Submodule (ZMod q.1) (E q) // ∀ w, (∀ x ∈ L, w.2 x.1 - x.2 w.1 = 0) ↔ w ∈ L}
  let cL (q : Q) := nc (Lag q)
  let ptP (q : Q) (c : Fin 22 → ℕ) (h : Fin 33 → ℕ) (L : Fin 13 → Lag q) :=
    (∀ j, rk (((L (t j 0)).1 ⊓ (L (t j 1)).1) ⊓ (L (t j 2)).1) = c j) ∧
    (∀ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) = h (p j k))
  let afD (q : Q) (L : Fin 3 → Lag q) (T : Finset (Fin 3)) :=
    nc {Y : Lag q // ∀ i ∈ T, rk ((L i).1 ⊓ Y.1) = r} / cL q *
      (cL q / nc {M : Lag q // rk (M.1 ⊓ LinearMap.ker (.fst _ _ _)) = r}) ^ T.card
  let Prof := (Fin 22 → Fin (2 * (2 * r) + 1)) × (Fin 33 → Fin (2 * (2 * r) + 1))
  let prof (q : Q) (L : Fin 13 → Lag q) : Prof :=
    (fun j => ⟨rk (((L (t j 0)).1 ⊓ (L (t j 1)).1) ⊓ (L (t j 2)).1), rk_lt (2*r) q _⟩,
     fun e => ⟨rk ((L (eL e)).1 ⊓ (L (eR e)).1), rk_lt (2*r) q _⟩)
  have hprof : ∀ q L pr, prof q L = pr ↔ ptP q (fun j => (pr.1 j).1) (fun e => (pr.2 e).1) L := by
    intro q L pr
    constructor
    · intro h
      refine ⟨fun j => congrArg (fun x => (x.1 j).1) h, fun j k => ?_⟩
      have hk := congrArg (fun x => (x.2 (p j k)).1) h
      dsimp only [prof] at hk
      rw [(hep.1 j k).1, (hep.1 j k).2] at hk
      exact hk
    · intro ⟨h1L, h2L⟩
      apply Prod.ext
      · funext j; apply Fin.ext; exact h1L j
      · funext e; apply Fin.ext
        obtain ⟨j, k, rfl⟩ := hep.2 e
        dsimp only [prof]
        rw [(hep.1 j k).1, (hep.1 j k).2]
        exact h2L j k
  have hsing : ∀ q L,
      (∃ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) ≠ 0) ↔
      (∃ e, ((prof q L).2 e).1 ≠ 0) := by
    intro q L
    constructor
    · rintro ⟨j, k, hjk⟩
      refine ⟨p j k, ?_⟩
      dsimp only [prof]
      rw [(hep.1 j k).1, (hep.1 j k).2]
      exact hjk
    · rintro ⟨e, he⟩
      obtain ⟨j, k, rfl⟩ := hep.2 e
      refine ⟨j, k, ?_⟩
      dsimp only [prof] at he
      rw [(hep.1 j k).1, (hep.1 j k).2] at he
      exact he
  have hfn : (fun q => (∑' L : Fin 13 → Lag q,
      if ∃ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) ≠ 0
      then ∏ j, afD q (fun i => L (t j i)) (T j) else 0) / cL q ^ 13) =
      fun q => ∑ pr : Prof, if ∃ e, (pr.2 e).1 ≠ 0 then
        (∑' L : {L : Fin 13 → Lag q // ptP q (fun j => (pr.1 j).1) (fun e => (pr.2 e).1) L},
          ∏ j, afD q (fun i => L.1 (t j i)) (T j)) / cL q ^ 13 else 0 := by
    funext q
    have : Finite (Lag q) := lag_finite (2 * r) q
    let : Fintype (Fin 13 → Lag q) := Fintype.ofFinite _
    rw [tsum_fintype]
    have hsum1 : (∑ L : Fin 13 → Lag q,
        if ∃ j k, rk ((L (t j (sL k))).1 ⊓ (L (t j (sR k))).1) ≠ 0
        then ∏ j, afD q (fun i => L (t j i)) (T j) else 0) =
        ∑ L : Fin 13 → Lag q,
          if ∃ e, ((prof q L).2 e).1 ≠ 0 then ∏ j, afD q (fun i => L (t j i)) (T j) else 0 := by
      refine Finset.sum_congr rfl fun L _ => ?_
      simp only [hsing]
    rw [hsum1, ← Fintype.sum_fiberwise (prof q), Finset.sum_div]
    refine Finset.sum_congr rfl fun pr _ => ?_
    let : Fintype {L : Fin 13 → Lag q // ptP q (fun j => (pr.1 j).1) (fun e => (pr.2 e).1) L} :=
      Fintype.ofFinite _
    rw [tsum_fintype]
    have hfib : (∑ L : {L : Fin 13 → Lag q // prof q L = pr},
        if ∃ e, ((prof q L.1).2 e).1 ≠ 0 then ∏ j, afD q (fun i => L.1 (t j i)) (T j) else 0) =
        if ∃ e, (pr.2 e).1 ≠ 0 then
          ∑ L : {L : Fin 13 → Lag q // ptP q (fun j => (pr.1 j).1) (fun e => (pr.2 e).1) L},
            ∏ j, afD q (fun i => L.1 (t j i)) (T j) else 0 := by
      let eqv : {L : Fin 13 → Lag q // prof q L = pr} ≃
          {L : Fin 13 → Lag q // ptP q (fun j => (pr.1 j).1) (fun e => (pr.2 e).1) L} :=
        Equiv.subtypeEquivRight (fun L => hprof q L pr)
      have hL : ∀ L : {L : Fin 13 → Lag q // prof q L = pr},
          (if ∃ e, ((prof q L.1).2 e).1 ≠ 0 then ∏ j, afD q (fun i => L.1 (t j i)) (T j) else 0) =
          if ∃ e, (pr.2 e).1 ≠ 0 then ∏ j, afD q (fun i => (eqv L).1 (t j i)) (T j) else 0 := by
        intro L
        rw [L.2]
        rfl
      simp_rw [hL]
      by_cases hne : ∃ e, (pr.2 e).1 ≠ 0
      · simp only [hne, ↓reduceIte]
        exact Equiv.sum_comp eqv (fun L => ∏ j, afD q (fun i => L.1 (t j i)) (T j))
      · simp only [hne, ↓reduceIte, Finset.sum_const_zero]
    rw [hfib]
    split_ifs <;> simp
  rw [hfn, show nhds (0 : ℝ) = nhds (∑ _pr : Prof, (0 : ℝ)) by simp]
  refine tendsto_finsetSum Finset.univ fun pr _ => ?_
  let c : Fin 22 → ℕ := fun j => (pr.1 j).1
  let h : Fin 33 → ℕ := fun e => (pr.2 e).1
  by_cases hne : ∃ e, (pr.2 e).1 ≠ 0
  · simp only [hne, ↓reduceIte]
    by_cases hgeom : (∀ j, c j ≤ 2 * r) ∧ (∀ j k, c j ≤ h (p j k)) ∧ ∀ j, (∑ k, (h (p j k) - c j)) ≤ 2 * r - c j
    · obtain ⟨hc_le, hch_le, hsum_le⟩ := hgeom
      have h3all : ∀ j : Fin 22, ∃ (Q₀ m : ℕ) (w : Fin m → ℝ) (u v : Fin m → ℕ) (pv tv : Fin m → Fin 3 → ℕ),
          (∀ l, 0 ≤ w l) ∧
          (∀ l, let δ : ℝ := 2*(u l : ℝ)-c j; c j ≤ 2*r ∧ (∑ i, (pv l i+tv l i)) ≤ 2*r-c j ∧
            (decide (T j = .univ) = true → u l ≤ c j ∧ (∀ i, (tv l i : ℝ) ≤ pv l i+δ) ∧
            (∀ i, (v l : ℝ) ≤ pv l i+δ) ∧ 0 ≤ (((2*r : ℕ) : ℝ)-c j-3*δ)/2-(∑ i, (pv l i : ℝ))+v l)) ∧
          (∀ l k, pv l k+tv l k = h (p j k) - c j) ∧
          ∀ q, Q₀ ≤ q.1 → ∀ L Tj, decide (Tj = .univ) = decide (T j = .univ) →
            rk (((L 0).1 ⊓ (L 1).1) ⊓ (L 2).1) = c j →
            rk ((L 0).1 ⊓ (L 1).1) = c j + (h (p j 0) - c j) →
            rk ((L 0).1 ⊓ (L 2).1) = c j + (h (p j 1) - c j) →
            rk ((L 1).1 ⊓ (L 2).1) = c j + (h (p j 2) - c j) →
            afD q L Tj ≤ ∑ l, w l * (q.1 : ℝ) ^
              (let δ : ℝ := 2*(u l : ℝ)-c j; let d : ℝ := ((2*r : ℕ) : ℝ)-c j; let P : ℝ := ∑ i, (pv l i : ℝ)
               if decide (T j = .univ) then ((d+c j)/2+c j+1)*((c j+δ)/2) - 2*((c j+δ)/2)^2 +
                 (∑ i, ((pv l i : ℝ)+tv l i)*(((pv l i : ℝ)+tv l i)+1)/2) -
                 δ*P - (∑ i, (pv l i : ℝ)^2) - (v l : ℝ)*((d-3*δ)/2-P+v l) -
                 (∑ i, (tv l i : ℝ)*((tv l i : ℝ)+1)/2) + (v l : ℝ)*((v l : ℝ)+1)/2
               else (((Finset.univ.sup fun i => c j+(pv l i+tv l i))/2 : ℕ) : ℝ) *
                 ((((Finset.univ.sup fun i => c j+(pv l i+tv l i))/2 : ℕ) : ℝ)+1)/2) :=
        fun j => h3 r (c j) (fun k => h (p j k) - c j) (decide (T j = .univ)) (hc_le j) (hsum_le j)
      choose Q₀ m w u v pv tv hw hfeas hsum hbd using h3all
      have hsum_eq : ∀ j l k, c j + (pv j l k + tv j l k) = h (p j k) := by
        intro j l k
        have h1k := hsum j l k
        have h2k := hch_le j k
        omega
      let N : Q → ℝ := fun q => (Nat.card {L : Fin 13 → Lag q // ptP q c h L} : ℝ) / (Nat.card (Lag q) : ℝ) ^ 13
      have hN0 : ∀ q, 0 ≤ N q := fun q => div_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
      obtain ⟨C₁, _, hC₁⟩ := (h1 (2 * r) c h).2.1 hc_le
      have hC₂_ex : ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ((∀ e, h e = 0 ∨ h e = 2) → ∀ q, N q ≤ C₂ * ((q.1 : ℝ)^(-(∑ e, (h e : ℝ)*((h e : ℝ)+1)/2)) + (q.1 : ℝ)^(-((2*r : ℕ) : ℝ)+1575))) := by
        by_cases he2 : ∀ e, h e = 0 ∨ h e = 2
        · obtain ⟨C₂, hC₂0, hC₂⟩ := (h1 (2 * r) c h).2.2 h33 he2
          exact ⟨C₂, hC₂0, fun _ => hC₂⟩
        · exact ⟨0, le_rfl, fun h' => False.elim (he2 h')⟩
      obtain ⟨C₂, _, hC₂⟩ := hC₂_ex
      have hmaj := h2D c h hc_le hch_le hsum_le hne (fun j => decide (T j = .univ)) m w u v pv tv hw
        (fun j l => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hfeas j l)
        hsum_eq N C₁ C₂ hN0 hC₁ hC₂
      refine squeeze_zero' ?_ ?_ hmaj
      · refine Eventually.of_forall fun q => ?_
        have : Finite (Lag q) := lag_finite (2 * r) q
        let : Fintype {L : Fin 13 → Lag q // ptP q c h L} := Fintype.ofFinite _
        rw [tsum_fintype]
        dsimp only [afD, cL, nc]
        refine div_nonneg (Finset.sum_nonneg fun L _ => Finset.prod_nonneg fun j _ => ?_) (pow_nonneg (Nat.cast_nonneg _) _)
        refine mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
      · have hev : ∀ᶠ q : Q in comap Subtype.val atTop, Finset.univ.sup Q₀ ≤ q.1 :=
          tendsto_comap.eventually (eventually_ge_atTop (Finset.univ.sup Q₀))
        refine hev.mono fun q hq => ?_
        have : Finite (Lag q) := lag_finite (2 * r) q
        let : Fintype {L : Fin 13 → Lag q // ptP q c h L} := Fintype.ofFinite _
        rw [tsum_fintype]
        dsimp only [N, cL, nc]
        rw [div_mul_eq_mul_div, mul_comm (Nat.card {L : Fin 13 → Lag q // ptP q c h L} : ℝ)]
        refine div_le_div_of_nonneg_right ?_ (pow_nonneg (Nat.cast_nonneg _) _)
        have hL_le : ∀ L : {L : Fin 13 → Lag q // ptP q c h L},
            (∏ j, afD q (fun i => L.1 (t j i)) (T j)) ≤
            ∏ j, ∑ l, w j l * (q.1 : ℝ) ^
              (let δ : ℝ := 2*(u j l : ℝ)-c j; let d : ℝ := ((2*r : ℕ) : ℝ)-c j; let P : ℝ := ∑ i, (pv j l i : ℝ)
               if decide (T j = .univ) then ((d+c j)/2+c j+1)*((c j+δ)/2) - 2*((c j+δ)/2)^2 +
                 (∑ i, ((pv j l i : ℝ)+tv j l i)*(((pv j l i : ℝ)+tv j l i)+1)/2) -
                 δ*P - (∑ i, (pv j l i : ℝ)^2) - (v j l : ℝ)*((d-3*δ)/2-P+v j l) -
                 (∑ i, (tv j l i : ℝ)*((tv j l i : ℝ)+1)/2) + (v j l : ℝ)*((v j l : ℝ)+1)/2
               else (((Finset.univ.sup fun i => c j+(pv j l i+tv j l i))/2 : ℕ) : ℝ) *
                 ((((Finset.univ.sup fun i => c j+(pv j l i+tv j l i))/2 : ℕ) : ℝ)+1)/2) := by
          intro L
          refine Finset.prod_le_prod (fun j _ => ?_) (fun j _ => ?_)
          · dsimp only [afD, cL, nc]
            exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
              (pow_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)
          · have hQj : Q₀ j ≤ q.1 := (Finset.le_sup (Finset.mem_univ j)).trans hq
            have hc0 : c j + (h (p j 0) - c j) = h (p j 0) := Nat.add_sub_of_le (hch_le j 0)
            have hc1 : c j + (h (p j 1) - c j) = h (p j 1) := Nat.add_sub_of_le (hch_le j 1)
            have hc2 : c j + (h (p j 2) - c j) = h (p j 2) := Nat.add_sub_of_le (hch_le j 2)
            exact hbd j q hQj (fun i => L.1 (t j i)) (T j) rfl (L.2.1 j)
              ((L.2.2 j 0).trans hc0.symm) ((L.2.2 j 1).trans hc1.symm) ((L.2.2 j 2).trans hc2.symm)
        calc (∑ L : {L : Fin 13 → Lag q // ptP q c h L}, ∏ j, afD q (fun i => L.1 (t j i)) (T j))
            ≤ ∑ _L : {L : Fin 13 → Lag q // ptP q c h L},
              ∏ j, ∑ l, w j l * (q.1 : ℝ) ^
                (let δ : ℝ := 2*(u j l : ℝ)-c j; let d : ℝ := ((2*r : ℕ) : ℝ)-c j; let P : ℝ := ∑ i, (pv j l i : ℝ)
                 if decide (T j = .univ) then ((d+c j)/2+c j+1)*((c j+δ)/2) - 2*((c j+δ)/2)^2 +
                   (∑ i, ((pv j l i : ℝ)+tv j l i)*(((pv j l i : ℝ)+tv j l i)+1)/2) -
                   δ*P - (∑ i, (pv j l i : ℝ)^2) - (v j l : ℝ)*((d-3*δ)/2-P+v j l) -
                   (∑ i, (tv j l i : ℝ)*((tv j l i : ℝ)+1)/2) + (v j l : ℝ)*((v j l : ℝ)+1)/2
                 else (((Finset.univ.sup fun i => c j+(pv j l i+tv j l i))/2 : ℕ) : ℝ) *
                   ((((Finset.univ.sup fun i => c j+(pv j l i+tv j l i))/2 : ℕ) : ℝ)+1)/2) :=
              Finset.sum_le_sum fun L _ => hL_le L
          _ = (∏ j, ∑ l, w j l * (q.1 : ℝ) ^
                (let δ : ℝ := 2*(u j l : ℝ)-c j; let d : ℝ := ((2*r : ℕ) : ℝ)-c j; let P : ℝ := ∑ i, (pv j l i : ℝ)
                 if decide (T j = .univ) then ((d+c j)/2+c j+1)*((c j+δ)/2) - 2*((c j+δ)/2)^2 +
                   (∑ i, ((pv j l i : ℝ)+tv j l i)*(((pv j l i : ℝ)+tv j l i)+1)/2) -
                   δ*P - (∑ i, (pv j l i : ℝ)^2) - (v j l : ℝ)*((d-3*δ)/2-P+v j l) -
                   (∑ i, (tv j l i : ℝ)*((tv j l i : ℝ)+1)/2) + (v j l : ℝ)*((v j l : ℝ)+1)/2
                 else (((Finset.univ.sup fun i => c j+(pv j l i+tv j l i))/2 : ℕ) : ℝ) *
                   ((((Finset.univ.sup fun i => c j+(pv j l i+tv j l i))/2 : ℕ) : ℝ)+1)/2)) *
              (Nat.card {L : Fin 13 → Lag q // ptP q c h L} : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm, Nat.card_eq_fintype_card]
    · have hemp : ∀ q : Q, IsEmpty {L : Fin 13 → Lag q // ptP q c h L} := by
        intro q
        rw [← not_nonempty_iff]
        intro hneL
        exact hgeom ((h1 (2 * r) c h).1 q hneL)
      have hz : (fun q : Q => (∑' L : {L : Fin 13 → Lag q // ptP q c h L},
          ∏ j, afD q (fun i => L.1 (t j i)) (T j)) / cL q ^ 13) = fun _ => 0 := by
        funext q
        have := hemp q
        simp
      rw [hz]
      exact tendsto_const_nhds
  · simp only [hne, ↓reduceIte]
    exact tendsto_const_nhds

theorem main : H1 → H2 → H3 → H4 → OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1.H1 := by
  intro h1 h2 h3 h4
  obtain ⟨D₀, hD₀, h2m⟩ := h2
  apply h4 D₀ (by omega)
  intro T
  exact tendsto_tail_zero h1 h3 (4 * D₀) (2 * D₀) (by omega) (by omega) T (h2m (4 * D₀) (by omega))

end OMA.R_SidorenkoConjecture_sidorenko_conjecture_graphon_R1_H1_R1_H1_R1_H1_R2
