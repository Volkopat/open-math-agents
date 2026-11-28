import OMAReductions.R_arxiv_2603_15098_R1_H1_R1
import Mathlib

/-! Adapted from openai/math, Apache-2.0,
commit 3344da59991ed94f9ba711217b29c1d760badfa6
(FiniteJordanImageUniformization, FiniteJordanUniformization).
Licensed under the Apache License, Version 2.0:
https://www.apache.org/licenses/LICENSE-2.0 -/

/-! Geometric cut: independent Jordan cores, then selected metric completions and a common limit. -/
namespace OMA.R_arxiv_2603_15098_R1_H1_R1_H1_R1
open Set OMA.S_arxiv_2603_15098
open Filter
open scoped OnePoint Topology

/-- Finitely many disjoint closed Jordan holes, after any sphere homeomorphism. -/
def H1 : Prop :=
  ∀ (n : ℕ) (H : Fin n → ℂ ≃ₜ ℂ),
    let K := fun i => closure (H i '' Metric.ball (0 : ℂ) 1)
    (∀ ⦃i j⦄, i ≠ j → Disjoint (K i) (K j)) → ∀ e : Sphere ≃ₜ Sphere,
      ∃ V f, IsCircleDomain V ∧ IsConformalEquivalence f (e '' (⋃ i, ((↑) : ℂ → Sphere) '' K i)ᶜ) V

/-- Source geometry only. Every marked source point has a decreasing chain of ends. -/
def H2 : Prop := ∀ U : Set Sphere, IsOpen U → IsConnected U → ∞ ∈ U →
  ∃ (k : ℕ → ℕ) (H : ∀ n, Fin (k n) → ℂ ≃ₜ ℂ),
    let A := fun n i => H n i '' Metric.ball (0 : ℂ) 1
    let K := fun n => (⋃ i, ((↑) : ℂ → Sphere) '' A n i)ᶜ
    (∀ n ⦃i j⦄, i ≠ j → Disjoint (closure (A n i)) (closure (A n j))) ∧
    (∀ n, IsCompact (K n)) ∧ (∀ n, K n ⊆ interior (K (n+1))) ∧ (⋃ n, K n) = U ∧
    ∀ p ∈ Uᶜ, Antitone (fun n => connectedComponentIn (K n)ᶜ p)

/-- Select auxiliary finite completions about prescribed retained cores BEFORE seeing their
uniformizers. On these completions the physical chart need only be conformal on the core.
The normalized finite maps, limiting omitted disks, and outer end bounds use one subsequence. -/
def H3 : Prop := ∀ (U : Set Sphere), IsOpen U → IsConnected U → ∞ ∈ U →
  ∀ (k : ℕ → ℕ) (H : ∀ n, Fin (k n) → ℂ ≃ₜ ℂ),
    let A := fun n i => H n i '' Metric.ball (0 : ℂ) 1
    let K := fun n => (⋃ i, ((↑) : ℂ → Sphere) '' A n i)ᶜ
    (∀ n ⦃i j⦄, i ≠ j → Disjoint (closure (A n i)) (closure (A n j))) →
    (∀ n, IsCompact (K n)) → (∀ n, K n ⊆ interior (K (n+1))) →
  (⋃ n, K n) = U → (∀ p ∈ Uᶜ, Antitone (fun n => connectedComponentIn (K n)ᶜ p)) →
  ∃ (j : ℕ → ℕ) (T : ∀ n, Fin (j n) → ℂ ≃ₜ ℂ) (e : ℕ → Sphere ≃ₜ Sphere),
    let B := fun n i => closure (T n i '' Metric.ball (0 : ℂ) 1)
    let Q := fun n => (⋃ i, ((↑) : ℂ → Sphere) '' B n i)ᶜ
    (∀ n ⦃a b⦄, a ≠ b → Disjoint (B n a) (B n b)) ∧
    (∀ n, K n ⊆ Q n ∧ IsConformalOn (e n) (K n)) ∧
    ∀ (W : ℕ → Set Sphere) (u : ℕ → Sphere → Sphere),
      (∀ n, IsCircleDomain (W n) ∧ IsConformalEquivalence (u n) (e n '' Q n) (W n)) →
      ∃ (s : ℕ → ℕ) (a : ℕ → Mobius) (f : Sphere → Sphere), StrictMono s ∧
        (∀ z ∈ U, ∀ O ∈ 𝓝 (f z), ∃ N ∈ 𝓝 z, ∀ᶠ n in atTop,
          ∀ w ∈ N ∩ U, a n • u (s n) (e (s n) w) ∈ O) ∧
        IsConformalEquivalence f U (f '' U) ∧ IsOpen (f '' U) ∧
        ∀ p ∈ (f '' U)ᶜ, connectedComponentIn (f '' U)ᶜ p ≠ {p} →
          ∃ (b : ℕ → Sphere) (D : Set Sphere),
            let V := fun n => (fun z : Sphere => a n • z) '' W (s n)
            let C := fun n => connectedComponentIn (V n)ᶜ (b n)
            (∀ᶠ n in atTop, b n ∈ (V n)ᶜ) ∧
            (⋂ m, closure (⋃ n ≥ m, C n)) = D ∧ IsRoundClosedDisk D ∧ IsPreconnected D ∧
            p ∈ D ∧ D ⊆ (f '' U)ᶜ ∧ (⋂ n, connectedComponentIn (f '' K n)ᶜ p) ⊆ D

theorem main : H1 → H2 → H3 → OMA.R_arxiv_2603_15098_R1_H1_R1.H1 := by
  classical
  intro hfin hgeom hselect U ho hc hi
  obtain ⟨k,H,hd,hK,hn,hu,hmarks⟩ := hgeom U ho hc hi
  let K := fun n => (⋃ i, ((↑) : ℂ → Sphere) '' (H n i '' Metric.ball (0 : ℂ) 1))ᶜ
  obtain ⟨j,T,e,hdisj,hcore,hsel⟩ := hselect U ho hc hi k H hd hK hn hu hmarks
  choose W u hWu using fun n => hfin (j n) (T n) (hdisj n) (e n)
  obtain ⟨s,a,f,hs,hl,hf,hopen,hend⟩ := hsel W u hWu
  let V := f '' U
  let M := {p ∈ Vᶜ | connectedComponentIn Vᶜ p ≠ {p}}
  let E := fun p => ⋂ n, connectedComponentIn (f '' K n)ᶜ p
  have hsub (n : ℕ) : Vᶜ ⊆ (f '' K n)ᶜ := compl_subset_compl.mpr (image_mono (hu ▸ subset_iUnion K n))
  have hmem (p : Sphere) (hp : p ∈ Vᶜ) : p ∈ E p := mem_iInter.mpr fun n => mem_connectedComponentIn (hsub n hp)
  refine ⟨f,K,M,hf,hopen,hK,hn,hu,fun _ hp => hp.1,?_,?_⟩
  · intro p hp
    obtain ⟨b,D,_,_,hr,hconn,hpD,hDV,hup⟩ := hend p hp.1 hp.2
    have he : E p = D := Subset.antisymm hup (subset_iInter fun n =>
      hconn.subset_connectedComponentIn hpD (hDV.trans (hsub n)))
    change IsRoundClosedDisk (E p) ∧ IsPreconnected (E p)
    rw [he]; exact ⟨hr,hconn⟩
  · intro S hS hconn p hp q hq
    have hpf := hS hp
    have hnot : p ∉ M := fun hm => hpf.2 (mem_iUnion₂.mpr ⟨p,hm,hmem p hpf.1⟩)
    have he : connectedComponentIn Vᶜ p = {p} := by by_contra hn; exact hnot ⟨hpf.1,hn⟩
    have hh := hconn.subset_connectedComponentIn hp (fun x hx => (hS hx).1) hq
    exact (show q ∈ ({p} : Set Sphere) from he ▸ hh).symm

end OMA.R_arxiv_2603_15098_R1_H1_R1_H1_R1
