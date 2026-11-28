import OMAReductions.R_Erdos360_erdos_360_R1_H4_R1
import Mathlib

/-! Lev, Theorem 4 on consecutive integers in high-multiplicity sumsets, and its Corollary 1.
Reserve a summand of maximum diameter to recover the loss in the critical interval. -/

open scoped BigOperators
namespace OMA.R_Erdos360_erdos_360_R1_H4_R1_H3_R1

/-- Lev's critical odd-family interval theorem, with natural-number translates. -/
def H1 : Prop :=
  ∀ (n D m : ℕ) (S : Fin n → Finset ℕ) (I : Finset (Fin n)),
    2 ≤ D → 3 ≤ m → I.card = 2 * ((D - 2) / (m - 2)) + 1 →
    (∀ i ∈ I, m ≤ (S i).card) →
    (∀ i ∈ I, ∃ x, S i ⊆ Finset.Icc x (x+D)) →
    (∀ i ∈ I, ∀ d : ℕ, 1 < d → ¬ (∀ x ∈ S i, ∀ y ∈ S i, x % d = y % d)) →
    ∃ a w : ℕ, (I.card + 1) * (m - 1) ≤ w + D ∧ D ≤ w + 1 ∧
      ∀ t ∈ Finset.Icc a (a+w), ∃ f : Fin n → ℕ,
        (∀ i ∈ I, f i ∈ S i) ∧ ∑ i ∈ I, f i = t

/-- Adjoin disjoint summands by overlapping their two endpoint translates. -/
def H2 : Prop :=
  ∀ (n : ℕ) (S : Fin n → Finset ℕ) (I T : Finset (Fin n)) (a w D p : ℕ),
    Disjoint I T → D ≤ w + 1 →
    (∀ i ∈ T, ∃ x ∈ S i, ∃ y ∈ S i, x+p ≤ y ∧ y ≤ x+D) →
    (∀ t ∈ Finset.Icc a (a+w), ∃ f : Fin n → ℕ,
        (∀ i ∈ I, f i ∈ S i) ∧ ∑ i ∈ I, f i = t) →
    ∃ b : ℕ, ∀ t ∈ Finset.Icc b (b+(w+T.card*p)), ∃ f : Fin n → ℕ,
      (∀ i ∈ I ∪ T, f i ∈ S i) ∧ ∑ i ∈ I ∪ T, f i = t

theorem main : H1 → H2 → OMA.R_Erdos360_erdos_360_R1_H4_R1.H3 := by
  classical
  intro critical glue ℓ q m hℓ _ hm hq S hcard hbox hprimitive
  have nonemptySet (i : Fin ℓ) : (S i).Nonempty :=
    Finset.card_pos.mp (by have := hcard i; omega)
  let lo (i : Fin ℓ) := (S i).min' (nonemptySet i)
  let hi (i : Fin ℓ) := (S i).max' (nonemptySet i)
  let width (i : Fin ℓ) := hi i - lo i
  have hlo (i) : lo i ∈ S i := Finset.min'_mem _ _
  have hhi (i) : hi i ∈ S i := Finset.max'_mem _ _
  have ordered (i) : lo i ≤ hi i := Finset.min'_le _ _ (hhi i)
  have span (i) : lo i + width i = hi i := by
    dsimp [width]
    have := ordered i
    omega
  have small (i) : m-1 ≤ width i := by
    have sub : S i ⊆ Finset.Icc (lo i) (hi i) := fun x hx ↦
      Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hx, Finset.le_max' _ _ hx⟩
    have hc := Finset.card_le_card sub
    rw [Nat.card_Icc] at hc
    have := hcard i
    have := ordered i
    have := span i
    omega
  have bounded (i) : width i ≤ q := by
    obtain ⟨z,hz⟩ := hbox i
    have h1 := (Finset.mem_Icc.mp (hz (hlo i))).1
    have h2 := (Finset.mem_Icc.mp (hz (hhi i))).2
    have := span i
    omega
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin ℓ)) width
    ⟨⟨0,by omega⟩, Finset.mem_univ _⟩
  let D := width j
  have maxW (i) : width i ≤ D := hj i (Finset.mem_univ _)
  have hD : 2 ≤ D := by have := small j; dsimp [D]; omega
  let r := (D-2)/(m-2)
  have hr : r*(m-2) ≤ D := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have h3r : 3*r ≤ ℓ := by
    apply le_of_mul_le_mul_right (a := m-2) _ (by omega)
    calc
      3*r*(m-2) = 3*(r*(m-2)) := Nat.mul_assoc _ _ _
      _ ≤ 3*D := Nat.mul_le_mul_left _ hr
      _ ≤ 3*q := Nat.mul_le_mul_left _ (bounded j)
      _ ≤ ℓ*(m-2) := hq
  let U := (Finset.univ : Finset (Fin ℓ)).erase j
  have hU : U.card = ℓ-1 := by simp [U]
  obtain ⟨I,hIU,hI⟩ := Finset.exists_subset_card_eq (s := U) (n := 2*r+1) (by omega)
  have hjI : j ∉ I := fun h ↦ (Finset.mem_erase.mp (hIU h)).1 rfl
  have boxes (i : Fin ℓ) : ∃ x, S i ⊆ Finset.Icc x (x+D) := by
    refine ⟨lo i, fun y hy ↦ Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hy, ?_⟩⟩
    have h : y ≤ hi i := Finset.le_max' _ _ hy
    have := span i
    have := maxW i
    omega
  obtain ⟨a,w,hsize,hcover,ha⟩ := critical ℓ D m S I hD hm hI
    (fun i _ ↦ hcard i) (fun i _ ↦ boxes i) (fun i _ ↦ hprimitive i)
  have single : ∀ i ∈ ({j} : Finset (Fin ℓ)), ∃ x ∈ S i, ∃ y ∈ S i, x+D ≤ y ∧ y ≤ x+D := by
    intro i h
    obtain rfl := Finset.mem_singleton.mp h
    exact ⟨lo i,hlo i,hi i,hhi i,(span i).le,(span i).ge⟩
  obtain ⟨b,hb⟩ := glue ℓ S I {j} a w D D (by simpa using hjI) hcover single ha
  let J := I ∪ {j}
  let K := (Finset.univ : Finset (Fin ℓ)) \ J
  have hJ : J.card = I.card + 1 := by simp [J, Finset.union_comm I, hjI]
  have hjoin : J ∪ K = Finset.univ := Finset.union_sdiff_of_subset (Finset.subset_univ J)
  have hd : Disjoint J K := disjoint_sdiff_self_right
  have hcount : J.card + K.card = ℓ := by
    rw [← Finset.card_union_of_disjoint hd, hjoin]
    simp
  have rest : ∀ i ∈ K, ∃ x ∈ S i, ∃ y ∈ S i, x+(m-1) ≤ y ∧ y ≤ x+D := by
    intro i _
    refine ⟨lo i,hlo i,hi i,hhi i,?_,?_⟩ <;>
      have := span i <;> have := small i <;> have := maxW i <;> omega
  obtain ⟨c,hc⟩ := glue ℓ S J K b (w+D) D (m-1) hd (by omega) rest (by simpa [J] using hb)
  have size : ℓ*(m-1) ≤ w+D + K.card*(m-1) := by
    calc
      ℓ*(m-1) = J.card*(m-1) + K.card*(m-1) := by rw [← Nat.add_mul, hcount]
      _ ≤ w+D + K.card*(m-1) := Nat.add_le_add_right (by simpa only [hJ] using hsize) _
  refine ⟨c,c+(w+D+K.card*(m-1)),by omega,?_⟩
  intro t ht
  obtain ⟨f,hf,hs⟩ := hc t ht
  rw [hjoin] at hf hs
  exact ⟨f,fun i ↦ hf i (Finset.mem_univ i),hs⟩

end OMA.R_Erdos360_erdos_360_R1_H4_R1_H3_R1
