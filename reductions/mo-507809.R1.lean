import OMAStatements.S_mo_507809

/-!
# Canonical backward trajectories for the two-branch Collatz graph

Write an odd vertex as 2u+1. A legal predecessor is indexed by T(3q)=4q,
T(3q+1)=2q, T(3q+2)=2q+1. An orbit reaching a smaller index gives descent.
An orbit repeating a value can be handled by reaching its eventual cycle.
The remaining orbits tend to infinity and require a different backward path.
-/

namespace OMA.R_mo_507809_R1

open OMA.S_mo_507809 Filter

/-- Connect every periodic index of the canonical predecessor to the initial vertex. -/
def H1 : Prop :=
  let T := fun u : ℕ => if u%3 = 0 then 4*(u/3) else 2*(u/3) + u%3/2
  ∀ u : ℕ, (∃ p > 0, T^[p] u = u) → ∃ j, 2*u+1 ∈ layer j

/-- On a canonical orbit escaping without dropping, find a path from a smaller odd vertex. -/
def H2 : Prop :=
  let T := fun u : ℕ => if u%3 = 0 then 4*(u/3) else 2*(u/3) + u%3/2
  ∀ u : ℕ, 0 < u → (∀ i, u ≤ T^[i] u) → Tendsto (fun i => T^[i] u) atTop atTop →
    ∃ v < u, Relation.ReflTransGen (fun x y : ℕ =>
      (3*x+1).divMaxPow 2 = y ∨ (3*x+3).divMaxPow 2 = y) (2*v+1) (2*u+1)

private theorem along_edge {x y : ℕ} (hx : ∃ j, x ∈ layer j)
    (edge : (3*x+1).divMaxPow 2 = y ∨ (3*x+3).divMaxPow 2 = y) :
    ∃ j, y ∈ layer j := by
  obtain ⟨j,hj⟩ := hx
  refine ⟨j+1, ?_⟩
  rcases edge with h|h
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨x,hj,h⟩)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hj,h⟩)

private theorem along_path {x y : ℕ} (hx : ∃ j, x ∈ layer j)
    (path : Relation.ReflTransGen (fun a b : ℕ =>
      (3*a+1).divMaxPow 2 = b ∨ (3*a+3).divMaxPow 2 = b) x y) :
    ∃ j, y ∈ layer j := by
  induction path with
  | refl => exact hx
  | tail _ edge ih => exact along_edge ih edge

private theorem strip {z k u : ℕ} (he : z = 2^k*(2*u+1)) :
    z.divMaxPow 2 = 2*u+1 := by
  have nd : ¬2 ∣ 2*u+1 := by omega
  rw [he, Nat.divMaxPow_base_pow_mul (by decide : 2 ≠ 0)]
  exact congrArg Prod.snd (Nat.maxPowDvdDiv_of_not_dvd nd)

private theorem layer_odd {j y : ℕ} (hy : y ∈ layer j) : Odd y := by
  cases j with
  | zero =>
    have : y = 1 := Finset.mem_singleton.mp hy
    simp [this]
  | succ j =>
    have oddpart (x : ℕ) (hx : x ≠ 0) : Odd (x.divMaxPow 2) := by
      have h := Nat.not_dvd_divMaxPow (p := 2) (by decide) hx
      exact Nat.odd_iff.mpr (by omega)
    rcases Finset.mem_union.mp hy with h|h <;>
      obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp h <;>
      apply oddpart <;> omega

theorem main : H1 → H2 → type_of% @OMA.S_mo_507809.main := by
  intro cycles escape
  let T := fun u : ℕ => if u%3 = 0 then 4*(u/3) else 2*(u/3) + u%3/2
  let R := fun u : ℕ => ∃ j, 2*u+1 ∈ layer j
  have back (u : ℕ) (h : R (T u)) : R u := by
    apply along_edge h
    by_cases h0 : u%3 = 0
    · left; apply strip (k := 2); simp [T,h0]; omega
    by_cases h1 : u%3 = 1
    · right; apply strip (k := 1); simp [T,h1]; omega
    · have h2 : u%3 = 2 := by omega
      left; apply strip (k := 1); simp [T,h2]; omega
  have back_many (u n : ℕ) : R (T^[n] u) → R u := by
    induction n with
    | zero => exact id
    | succ n ih => simpa only [Function.iterate_succ_apply'] using (ih ∘ back (T^[n] u))
  have allR (u : ℕ) : R u := by
    induction u using Nat.strong_induction_on with
    | h u ih =>
      by_cases hu : u = 0
      · subst u; exact ⟨0, by decide⟩
      by_cases drops : ∃ i, T^[i] u < u
      · obtain ⟨i,hi⟩ := drops
        exact back_many u i (ih _ hi)
      have never (i : ℕ) : u ≤ T^[i] u := Nat.le_of_not_gt (fun h => drops ⟨i,h⟩)
      by_cases inj : Function.Injective (fun i : ℕ => T^[i] u)
      · have tends : Tendsto (fun i : ℕ => T^[i] u) atTop atTop := by
          simpa only [Nat.cofinite_eq_atTop] using inj.tendsto_cofinite
        obtain ⟨v,hv,path⟩ := escape u (by omega) never tends
        exact along_path (ih v hv) path
      · simp only [Function.Injective, not_forall] at inj
        obtain ⟨a,b,eqv,ne⟩ := inj
        have repeat_at {i j : ℕ} (hij : i < j) (eqv : T^[i] u = T^[j] u) : R u := by
          apply back_many u i
          apply cycles
          refine ⟨j-i, by omega, ?_⟩
          rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
          exact eqv.symm
        rcases lt_trichotomy a b with hab|hab|hab
        · exact repeat_at hab eqv
        · exact False.elim (ne hab)
        · exact repeat_at hab eqv.symm
  ext y
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j,hj⟩
    have h := layer_odd hj
    exact ⟨by obtain ⟨t,ht⟩ := h; omega, h⟩
  · rintro ⟨_,u,rfl⟩
    exact allR u

end OMA.R_mo_507809_R1
