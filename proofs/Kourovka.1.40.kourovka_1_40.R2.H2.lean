import OMAReductions.R_Kourovka_1_40_kourovka_1_40_R2

/-! A product of a normal nilpotent subgroup and a normal Engel subgroup is Engel.
Repeated commutators descend through the finite lower central series of the first factor. -/

open Kourovka.«1.40» Subgroup OMA.R_Kourovka_1_40_kourovka_1_40_R2
open scoped commutatorElement

namespace OMA.MixedEngel

variable {G : Type*} [Group G]

private theorem iterate_add (x y : G) (m n : ℕ) :
    engelCommutator x y (m+n) = engelCommutator (engelCommutator x y m) y n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun z => ⁅z,y⁆) ih

/-- Normality puts the first commutator in K, where the Engel condition applies. -/
private theorem ambient_engel (K : Subgroup G) [K.Normal] (hK : IsEngelGroup K)
    {k : G} (hk : k ∈ K) : IsEngelElement k := by
  intro x
  have hx : ⁅x,k⁆ ∈ K := commutator_le_right (⊤ : Subgroup G) K
    (commutator_mem_commutator (mem_top x) hk)
  obtain ⟨n,hn⟩ := hK ⟨k,hk⟩ ⟨⁅x,k⁆,hx⟩
  refine ⟨1+n, ?_⟩
  rw [iterate_add]
  exact (engel_map K.subtype ⟨⁅x,k⁆,hx⟩ ⟨k,hk⟩ n).symm.trans
    (by rw [hn, map_one])

private theorem iterate_mem (D : Subgroup G) [D.Normal] {z : G} (hz : z ∈ D) (k : G) :
    ∀ n, engelCommutator z k n ∈ D
  | 0 => hz
  | n+1 => commutator_le_left D (⊤ : Subgroup G)
      (commutator_mem_commutator (iterate_mem D hz k n) (mem_top k))

/-- Modulo N, h centralizes D, so on D iterating with k*h agrees with iterating with k. -/
private theorem descend (D N H : Subgroup G) [D.Normal] [N.Normal] (hDN : ⁅D,H⁆ ≤ N)
    {z k h : G} (hz : z ∈ D) (hh : h ∈ H) (hk : IsEngelElement k) :
    ∃ n, engelCommutator z (k*h) n ∈ N := by
  let q := QuotientGroup.mk' N
  have eqmod (n : ℕ) :
      q (engelCommutator z (k*h) n) = q (engelCommutator z k n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let w := engelCommutator z k n
      have comm : q ⁅w,h⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
        (hDN (commutator_mem_commutator (iterate_mem D hz k n) hh))
      simp only [engelCommutator, map_commutatorElement, ih, map_mul]
      change ⁅q w, q k*q h⁆ = ⁅q w,q k⁆
      rw [map_commutatorElement] at comm
      rw [commutatorElement_mul_right_eq_mul_conj, comm]
      simp [mul_assoc]
  obtain ⟨n,hn⟩ := hk z
  refine ⟨n,(QuotientGroup.eq_one_iff _).mp ?_⟩
  exact (eqmod n).trans (by rw [hn,map_one])

theorem mixed (H K : Subgroup G) [H.Normal] [K.Normal] (hnil : Group.IsNilpotent H)
    (hK : IsEngelGroup K) (hsup : H ⊔ K = ⊤) : IsEngelGroup G := by
  intro y x
  obtain ⟨k,hk,h,hh,rfl⟩ := mem_sup_of_normal_right.mp
    (show y ∈ K ⊔ H by rw [sup_comm,hsup]; exact mem_top _)
  have ke := ambient_engel K hK hk
  have reach (i : ℕ) : ∃ n, engelCommutator x (k*h) n ∈ H.lowerCentralSeries i := by
    induction i with
    | zero => exact descend ⊤ H H (commutator_le_right _ _) (mem_top x) hh ke
    | succ i ih =>
      obtain ⟨m,hm⟩ := ih
      obtain ⟨n,hn⟩ := descend (H.lowerCentralSeries i) (H.lowerCentralSeries (i+1)) H
        le_rfl hm hh ke
      exact ⟨m+n, by rw [iterate_add]; exact hn⟩
  obtain ⟨i,hi⟩ := (isNilpotent_iff_lowerCentralSeries H).mp hnil
  obtain ⟨n,hn⟩ := reach i
  exact ⟨n, by simpa [hi] using hn⟩

end OMA.MixedEngel

theorem OMA.solution : OMA.R_Kourovka_1_40_kourovka_1_40_R2.H2 := by
  intro G _ H K hH hK _ eK hsup hnil _ _
  exact OMA.MixedEngel.mixed H K hnil eK hsup
