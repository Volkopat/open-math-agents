import FormalConjectures.GreensOpenProblems.«74»
import Mathlib

-- Reduction Green74.green_74.variants.large.R1 of Ben Green's Open Problem 74 — large
-- Credit: @Burntgogi

/-! Slicing an admissible set along one coordinate bounds the extremal function
in dimension `d + 1` by `N` times its value in dimension `d`. Thus a seed
dimension and extensions to arbitrarily higher dimensions suffice. -/

namespace OMA.R_Green74_green_74_variants_large_R1

open Finset Filter Green74

/-- The dimension reached by the quartic norm graph construction. -/
def H1 : Prop :=
  ∀ᶠ N : ℕ in atTop, N ^ (295 - 100 : ℕ) ≤ maxNoFiveCoplanar 295 N

/-- Every good dimension from 295 onward admits a strictly larger good dimension. -/
def H2 : Prop :=
  ∀ d : ℕ, 295 ≤ d → (∀ᶠ N : ℕ in atTop, N ^ (d - 100) ≤ maxNoFiveCoplanar d N) →
    ∃ m > d, ∀ᶠ N : ℕ in atTop, N ^ (m - 100) ≤ maxNoFiveCoplanar m N

/-- Appending a fixed coordinate sends coplanar sets to coplanar sets. -/
lemma insert_coplanar {d : ℕ} (t : ℕ) (S : Finset (Fin d → ℕ))
    (hc : Coplanar ℝ (embed '' (S : Set (Fin d → ℕ)))) :
    Coplanar ℝ (embed '' (↑(S.image (fun x => Fin.snoc (α := fun _ => ℕ) x t)) : Set (Fin (d + 1) → ℕ))) := by
  classical
  let f : (Fin d → ℝ) →ᵃ[ℝ] (Fin (d+1) → ℝ) :=
    AffineMap.pi (Fin.snoc (fun i : Fin d => (LinearMap.proj i).toAffineMap)
      (AffineMap.const ℝ _ (t : ℝ)))
  have he (x : Fin d → ℕ) : embed (Fin.snoc (α := fun _ => ℕ) x t) = f (embed x) := by
    ext i
    cases i using Fin.lastCases <;> simp [f, embed, AffineMap.pi]
  have hm : Coplanar ℝ (f '' (embed '' (S : Set (Fin d → ℕ)))) := by
    unfold Coplanar
    rw [← f.map_vectorSpan]
    exact (rank_map_le _ _).trans hc
  apply hm.subset
  rintro _ ⟨z,hz,rfl⟩
  obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
  exact ⟨embed x, ⟨x,hx,rfl⟩, (he x).symm⟩

lemma card_bound {d N : ℕ} {A : Finset (Fin d → ℕ)}
    (hA : A ⊆ Fintype.piFinset (fun _ => Icc 1 N)) (ha : NoFiveCoplanar A) :
    A.card ≤ maxNoFiveCoplanar d N := by
  unfold maxNoFiveCoplanar
  apply le_csSup
  rotate_left
  · exact ⟨A,hA,rfl,ha⟩
  refine ⟨N ^ d, ?_⟩
  rintro _ ⟨B,hB,rfl,_⟩
  exact (card_le_card hB).trans (by simp)

/-- Sum the sizes of the slices perpendicular to the last coordinate. -/
lemma slice_bound (d N : ℕ) :
    maxNoFiveCoplanar (d+1) N ≤ N * maxNoFiveCoplanar d N := by
  classical
  apply csSup_le'
  rintro _ ⟨A,hA,rfl,ha⟩
  let last (x : Fin (d+1) → ℕ) := x (Fin.last d)
  have maps : ∀ x ∈ A, last x ∈ Icc 1 N := fun _ hx => Fintype.mem_piFinset.mp (hA hx) _
  rw [card_eq_sum_card_fiberwise maps]
  calc
    _ ≤ ∑ _t ∈ Icc 1 N, maxNoFiveCoplanar d N := by
      apply sum_le_sum
      intro t _
      let F := A.filter (fun x => last x = t)
      have restore (x : Fin (d+1) → ℕ) (hx : x ∈ F) : Fin.snoc (Fin.init x) t = x := by
        rw [← (mem_filter.mp hx).2]
        exact Fin.snoc_init_self x
      have hinj : Set.InjOn (fun x => Fin.init x) (F : Set (Fin (d+1) → ℕ)) := by
        intro x hx y hy he
        change Fin.init x = Fin.init y at he
        rw [← restore x hx, ← restore y hy, he]
      change F.card ≤ _
      rw [← card_image_of_injOn hinj]
      apply card_bound
      · intro y hy
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hy
        exact Fintype.mem_piFinset.mpr fun i =>
          Fintype.mem_piFinset.mp (hA (mem_filter.mp hx).1) i.castSucc
      · intro S hS h5 hc
        apply ha (S.image (fun x => Fin.snoc (α := fun _ => ℕ) x t)) _ _ (insert_coplanar t S hc)
        · intro z hz
          obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
          obtain ⟨x,hx,rfl⟩ := mem_image.mp (hS hy)
          rw [restore x hx]
          exact (mem_filter.mp hx).1
        · rwa [card_image_of_injective _ (Fin.snoc_left_injective (α := fun _ => ℕ) t)]
    _ = _ := by simp

lemma single_bound (d N : ℕ) (hN : 1 ≤ N) : 1 ≤ maxNoFiveCoplanar d N := by
  let A : Finset (Fin d → ℕ) := {fun _ => 1}
  have hA : A ⊆ Fintype.piFinset (fun _ => Icc 1 N) := by
    intro x hx
    obtain rfl := mem_singleton.mp hx
    exact Fintype.mem_piFinset.mpr fun _ => mem_Icc.mpr ⟨le_rfl,hN⟩
  have h := card_bound hA (by
    intro S hS h5
    have hs := card_le_card hS
    simp [A,h5] at hs)
  simpa [A] using h

theorem main : H1 → H2 → type_of% @Green74.green_74.variants.large := by
  intro seed extend d
  let P (k : ℕ) := ∀ᶠ N : ℕ in atTop, N ^ (k - 100) ≤ maxNoFiveCoplanar k N
  have down (k : ℕ) (hk : P (k+1)) : P k := by
    filter_upwards [hk, eventually_ge_atTop 1] with N hn hN
    by_cases h : 100 ≤ k
    · have hh := hn.trans (slice_bound k N)
      rw [show k+1-100 = k-100+1 by omega, pow_succ, mul_comm] at hh
      exact Nat.le_of_mul_le_mul_left hh hN
    · simpa [Nat.sub_eq_zero_of_le (by omega : k ≤ 100)] using single_bound k N hN
  have above (n : ℕ) : ∃ m, 295 ≤ m ∧ n ≤ m ∧ P m := by
    induction n with
    | zero => exact ⟨295,le_rfl,Nat.zero_le _,seed⟩
    | succ n ih =>
      obtain ⟨m,hm,hn,hp⟩ := ih
      obtain ⟨l,hl,hlp⟩ := extend m hm hp
      exact ⟨l,by omega,by omega,hlp⟩
  obtain ⟨m,-,hm,hp⟩ := above d
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction j with
  | zero => exact hp
  | succ j ih => exact ih (down (d+j) hp)

end OMA.R_Green74_green_74_variants_large_R1
