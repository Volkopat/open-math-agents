import OMAStatements.S_opg_even_vs_odd_latin_squares
import Mathlib

namespace OMA.R_opg_even_vs_odd_latin_squares_R1

open OMA.S_opg_even_vs_odd_latin_squares

lemma latin_sign_of_reindex {n : ℕ} (hn : Even n) (L L' : LatinSquare n)
    (a b : Equiv.Perm (Fin n))
    (h : ∀ i j, L'.val i j = L.val (a i) (b j)) : sign L' = sign L := by
  let row (M : LatinSquare n) (i : Fin n) := Equiv.ofBijective _ (M.2.1 i)
  let col (M : LatinSquare n) (j : Fin n) := Equiv.ofBijective _ (M.2.2 j)
  have hrow (i) : row L' i = b.trans (row L (a i)) := Equiv.ext (h i)
  have hcol (j) : col L' j = a.trans (col L (b j)) := Equiv.ext (fun i => h i j)
  have unit_pow (u : ℤˣ) : u ^ n = 1 := by
    obtain ⟨k, hk⟩ := hn
    rw [hk, pow_add, Int.units_mul_self]
  change (∏ i, Equiv.Perm.sign (row L' i)) * (∏ j, Equiv.Perm.sign (col L' j)) =
    (∏ i, Equiv.Perm.sign (row L i)) * (∏ j, Equiv.Perm.sign (col L j))
  simp_rw [hrow, hcol, Equiv.Perm.sign_trans]
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, unit_pow, mul_one]
  rw [Equiv.prod_comp a (fun i => Equiv.Perm.sign (row L i)),
    Equiv.prod_comp b (fun j => Equiv.Perm.sign (col L j))]

theorem latin_normalize_equiv (n : ℕ) [NeZero n]
    (act : LatinSquare n → Equiv.Perm (Fin n) → Equiv.Perm (Fin n) → LatinSquare n)
    (hact : ∀ L a b i j, (act L a b).val i j = L.val (a i) (b j)) :
    ∃ E : LatinSquare n ≃ Equiv.Perm (Fin n) ×
        {a : Equiv.Perm (Fin n) // a 0 = 0} ×
        {R : LatinSquare n // (∀ j, R.val 0 j = j) ∧ ∀ i, R.val i 0 = i},
      ∀ L, (E L).2.2.val = act L (E L).2.1.val.symm (E L).1.symm := by
  let row (L : LatinSquare n) : Equiv.Perm (Fin n) :=
    Equiv.ofBijective _ (L.property.1 0)
  let col (L : LatinSquare n) : Equiv.Perm (Fin n) :=
    Equiv.ofBijective _ (L.property.2 ((row L).symm 0))
  have hc0 (L : LatinSquare n) : col L 0 = 0 := (row L).apply_symm_apply 0
  have hc0' (L : LatinSquare n) : (col L).symm 0 = 0 :=
    (col L).injective (by rw [Equiv.apply_symm_apply, hc0])
  let reduced (L : LatinSquare n) :
      {R : LatinSquare n // (∀ j, R.val 0 j = j) ∧ ∀ i, R.val i 0 = i} :=
    ⟨act L (col L).symm (row L).symm, by
      constructor
      · intro j
        rw [hact, hc0']
        exact (row L).apply_symm_apply j
      · intro i
        rw [hact]
        exact (col L).apply_symm_apply i⟩
  let E : LatinSquare n ≃ Equiv.Perm (Fin n) ×
      {a : Equiv.Perm (Fin n) // a 0 = 0} ×
      {R : LatinSquare n // (∀ j, R.val 0 j = j) ∧ ∀ i, R.val i 0 = i} := {
    toFun := fun L => ⟨row L, ⟨col L, hc0 L⟩, reduced L⟩
    invFun := fun z => act z.2.2.val z.2.1.val z.1
    left_inv := by
      intro L
      apply Subtype.ext
      funext i j
      change (act (act L (col L).symm (row L).symm) (col L) (row L)).val i j = L.val i j
      simp only [hact, Equiv.symm_apply_apply]
    right_inv := by
      rintro ⟨b, ⟨a,ha⟩, ⟨R,hr,hc⟩⟩
      let L := act R a b
      have hrow : row L = b := by
        apply Equiv.ext
        intro j
        change (act R a b).val 0 j = b j
        rw [hact, ha, hr]
      have hcol : col L = a := by
        apply Equiv.ext
        intro i
        change (act R a b).val i ((row L).symm 0) = a i
        rw [hact, hrow, Equiv.apply_symm_apply, hc]
      apply Prod.ext hrow
      apply Prod.ext (Subtype.ext hcol)
      apply Subtype.ext
      apply Subtype.ext
      funext i j
      change (act (act R a b) (col L).symm (row L).symm).val i j = R.val i j
      simp only [hact, hrow, hcol, Equiv.apply_symm_apply] }
  exact ⟨E, fun _ => rfl⟩

private lemma latin_signed_card {A U V R : Type} (e : A ≃ U × V × R)
    (sA : A → ℤˣ) (sR : R → ℤˣ) (h : ∀ x, sR (e x).2.2 = sA x) (s : ℤˣ) :
    Nat.card {x : A // sA x = s} =
      Nat.card U * (Nat.card V * Nat.card {r : R // sR r = s}) := by
  let F : {x : A // sA x = s} ≃ U × V × {r : R // sR r = s} :=
    { toFun := fun x => ((e x).1, (e x).2.1, ⟨(e x).2.2, (h x).trans x.property⟩)
      invFun := fun ⟨u,v,r⟩ => ⟨e.symm (u,v,r.val), by
        rw [← h, e.apply_symm_apply]
        exact r.property⟩
      left_inv := by intro x; apply Subtype.ext; simp
      right_inv := by rintro ⟨u,v,r⟩; simp }
  simpa [Nat.card_prod] using Nat.card_congr F

def H1 : Prop := ∀ m : ℕ, Even (m+1) → m.Prime →
  let R := {L : LatinSquare (m+1) // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}
  Nat.card {L : R // sign L.val = 1} ≠ Nat.card {L : R // sign L.val = -1}

def H2 : Prop := ∀ m : ℕ, Even (m+1) → (m+2).Prime →
  let R := {L : LatinSquare (m+1) // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}
  Nat.card {L : R // sign L.val = 1} ≠ Nat.card {L : R // sign L.val = -1}

def H3 : Prop := ∀ m : ℕ, Even (m+1) → ¬ m.Prime → ¬ (m+2).Prime →
  let R := {L : LatinSquare (m+1) // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}
  Nat.card {L : R // sign L.val = 1} ≠ Nat.card {L : R // sign L.val = -1}

theorem main : H1 → H2 → H3 → type_of% @OMA.S_opg_even_vs_odd_latin_squares.main := by
  intro hplus hminus hrest n hn he
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let n := m+1
  let R := {L : LatinSquare n // (∀ j, L.val 0 j = j) ∧ ∀ i, L.val i 0 = i}
  let Stab := {b : Equiv.Perm (Fin n) // b 0 = 0}
  have hred : Nat.card {r : R // sign r.val = 1} ≠ Nat.card {r : R // sign r.val = -1} := by
    by_cases h : m.Prime
    · exact hplus m he h
    by_cases h' : (m+2).Prime
    · exact hminus m he h'
    exact hrest m he h h'
  let act (L : LatinSquare n) (a b : Equiv.Perm (Fin n)) : LatinSquare n :=
    ⟨fun i j => L.val (a i) (b j), fun i => (L.2.1 (a i)).comp b.bijective,
      fun j => (L.2.2 (b j)).comp a.bijective⟩
  obtain ⟨E,hE⟩ := latin_normalize_equiv n act (fun _ _ _ _ _ => rfl)
  have hs (L : LatinSquare n) : sign (E L).2.2.val = sign L := by
    rw [hE]
    exact latin_sign_of_reindex he L _ _ _ (fun _ _ => rfl)
  have hc (s : ℤˣ) : Nat.card {L : LatinSquare n // sign L = s} =
      Nat.card (Equiv.Perm (Fin n)) * (Nat.card Stab * Nat.card {r : R // sign r.val = s}) :=
    latin_signed_card E sign (fun r : R => sign r.val) hs s
  have : Nonempty Stab := ⟨⟨Equiv.refl _, rfl⟩⟩
  have hU : 0 < Nat.card (Equiv.Perm (Fin n)) := Nat.card_pos
  have hV : 0 < Nat.card Stab := Nat.card_pos
  intro h
  have heq := (hc 1).symm.trans (h.trans (hc (-1)))
  exact hred (Nat.eq_of_mul_eq_mul_left hV (Nat.eq_of_mul_eq_mul_left hU heq))

end OMA.R_opg_even_vs_odd_latin_squares_R1
