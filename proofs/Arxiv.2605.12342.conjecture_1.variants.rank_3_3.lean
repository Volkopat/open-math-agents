import FormalConjectures.Arxiv.«2605.12342».Conjecture1

/-! Verify the six-element dihedral carriers directly. They contain either
two given generators, or an even generator and an odd generator. The original
dihedral proof is credited to @jlgmaarav. -/

namespace OMA.Rank33

open Equiv Equiv.Perm Arxiv.«2605.12342»

abbrev G := Perm (Fin 3) × Perm (Fin 3)
abbrev IsEv (x : G) := sign x.1 = 1 ∧ sign x.2 = 1
abbrev IsOd (x : G) := sign x.1 = -1 ∧ sign x.2 = -1

def entries (r a : G) : List G := [1, a, a * a, r, r * a, r * a * a]

set_option maxRecDepth 4096 in
theorem checked : ∀ r a : G, IsOd r → IsEv a →
    (entries r a).all (fun x => decide (x⁻¹ ∈ entries r a)) = true ∧
    (entries r a).all (fun x => (entries r a).all (fun y => decide (x * y ∈ entries r a))) = true ∧
    ∃ b : G, IsEv b ∧ b ∉ entries r a := by decide +kernel

lemma odd_square : ∀ r : G, IsOd r → r * r = 1 := by decide
lemma odd_exists : ∃ r : G, IsOd r := by decide

lemma mem_gamma {x : G} : x ∈ gammaSubgroup 3 3 ↔ sign x.1 = sign x.2 := by
  simp only [gammaSubgroup, signDiffHom, MonoidHom.mem_ker, MonoidHom.mul_apply,
    MonoidHom.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MonoidHom.inv_apply,
    mul_inv_eq_one]

lemma signs (x : gammaSubgroup 3 3) : IsEv x.val ∨ IsOd x.val := by
  have hx := mem_gamma.mp x.property
  rcases Int.units_eq_one_or (sign x.val.1) with h | h
  · exact Or.inl ⟨h, hx ▸ h⟩
  · exact Or.inr ⟨h, hx ▸ h⟩

def evenPart : Subgroup G where
  carrier := {x | IsEv x}
  one_mem' := by simp [IsEv]
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    simp [IsEv, Equiv.Perm.sign_mul, hx1, hx2, hy1, hy2]
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    simp [IsEv, hx1, hx2]

def dihedral (r a : G) (hr : IsOd r) (ha : IsEv a) : Subgroup G where
  carrier := {x | x ∈ entries r a}
  one_mem' := by simp [entries]
  mul_mem' := fun {x y} hx hy => of_decide_eq_true <|
    List.all_eq_true.mp (List.all_eq_true.mp (checked r a hr ha).2.1 x hx) y hy
  inv_mem' := fun {x} hx => of_decide_eq_true <| List.all_eq_true.mp (checked r a hr ha).1 x hx

lemma proper (L : Subgroup G) (u v : gammaSubgroup 3 3) (hu : u.val ∈ L) (hv : v.val ∈ L)
    (b : gammaSubgroup 3 3) (hb : b.val ∉ L) : Subgroup.closure {u, v} ≠ ⊤ := by
  intro h
  have hle : Subgroup.closure {u, v} ≤ L.comap (gammaSubgroup 3 3).subtype := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hu
    · exact hv
  exact hb (hle (h ▸ Subgroup.mem_top b))

lemma dihedral_case (r a : G) (hr : IsOd r) (ha : IsEv a)
    (u v : gammaSubgroup 3 3) (hu : u.val ∈ entries r a) (hv : v.val ∈ entries r a) :
    Subgroup.closure {u, v} ≠ ⊤ := by
  obtain ⟨b, hb, hn⟩ := (checked r a hr ha).2.2
  exact proper (dihedral r a hr ha) u v hu hv
    ⟨b, mem_gamma.mpr (hb.1.trans hb.2.symm)⟩ hn

end OMA.Rank33

open OMA.Rank33 Equiv.Perm in
theorem OMA.solution : type_of% @Arxiv.«2605.12342».conjecture_1.variants.rank_3_3 := by
  intro u v
  rcases signs u with hue | huo <;> rcases signs v with hve | hvo
  · obtain ⟨b, hb⟩ := odd_exists
    refine proper evenPart u v hue hve ⟨b, mem_gamma.mpr (hb.1.trans hb.2.symm)⟩ ?_
    intro he
    have he' : IsEv b := he
    exact (by decide : (1 : ℤˣ) ≠ -1) (he'.1.symm.trans hb.1)
  · exact dihedral_case v.val u.val hvo hue u v (by simp [entries]) (by simp [entries])
  · exact dihedral_case u.val v.val huo hve u v (by simp [entries]) (by simp [entries])
  · have ha : IsEv (u.val * v.val) := by
      simp [IsEv, Equiv.Perm.sign_mul, huo.1, huo.2, hvo.1, hvo.2]
    have h : u.val * (u.val * v.val) = v.val := by
      rw [← mul_assoc, odd_square _ huo, one_mul]
    exact dihedral_case u.val (u.val * v.val) huo ha u v (by simp [entries]) (by simp [entries, h])
