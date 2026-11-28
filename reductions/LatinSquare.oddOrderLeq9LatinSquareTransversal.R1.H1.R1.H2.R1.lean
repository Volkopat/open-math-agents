import OMAReductions.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1
import Mathlib

/-! Seven-row certificates for order-nine Latin transversals, refining the canonical-row reduction in PR 12632. -/
namespace OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1_H2_R1

theorem fill {n : ℕ} (L : LatinSquare n) {a b : Fin n}
    (σ τ : Equiv.Perm (Fin n)) (h : ∀ i : {i : Fin n // i ≠ a ∧ i ≠ b}, L.mat i (σ i) = τ i)
    (ha : L.mat a (σ a) = τ a ∧ L.mat b (σ b) = τ b ∨
          L.mat a (σ b) = τ b ∧ L.mat b (σ a) = τ a) :
    ∃ p, IsTransversal L p := by
  classical
  have finish (s t : Equiv.Perm (Fin n)) (hf : ∀ i, L.mat i (s i) = t i) :
      ∃ p, IsTransversal L p := ⟨s,s.injective,by simpa only [hf] using t.injective⟩
  rcases ha with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · apply finish σ τ
    intro i
    by_cases hia : i = a
    · simpa [hia] using ha
    by_cases hib : i = b
    · simpa [hib] using hb
    exact h ⟨i,hia,hib⟩
  · apply finish ((Equiv.swap a b).trans σ) ((Equiv.swap a b).trans τ)
    intro i
    simp only [Equiv.trans_apply]
    by_cases hia : i = a
    · simpa [hia] using ha
    by_cases hib : i = b
    · simpa [hib] using hb
    simpa [Equiv.swap_apply_of_ne_of_ne hia hib] using h ⟨i,hia,hib⟩

theorem permits {n : ℕ} {a b : Fin n}
    (P : {i : Fin n // i ≠ a ∧ i ≠ b} → Fin n → Fin n) (L : LatinSquare n)
    (rows : ∀ i j, L.mat i.val j = P i j) (no : ¬ ∃ p, IsTransversal L p) :
    ∃ χ : (Fin n × Fin n) → Bool,
      (∀ e f, (∀ i, P i e.1 ≠ e.2) → (∀ i, P i f.1 ≠ f.2) → e ≠ f → (e.1=f.1 ∨ e.2=f.2) → χ e ≠ χ f) ∧
      (∀ e f, (∀ i, P i e.1 ≠ e.2) → (∀ i, P i f.1 ≠ f.2) → (∃ σ τ : Equiv.Perm (Fin n), σ a=e.1 ∧ σ b=f.1 ∧ τ a=e.2 ∧ τ b=f.2 ∧
        ∀ i, P i (σ i) = τ i) → χ e = χ f) := by
  classical
  let χ (e : Fin n × Fin n) := decide (L.mat a e.1 = e.2)
  have yes (e) (h : χ e = true) : L.mat a e.1=e.2 := of_decide_eq_true h
  have other (e : Fin n × Fin n) (hu : (∀ i, P i e.1 ≠ e.2)) (h : χ e = false) : L.mat b e.1=e.2 := by
    have surj := (Finite.injective_iff_surjective).mp (L.col_injective e.1)
    obtain ⟨i,hi⟩ := surj e.2
    change L.mat i e.1=e.2 at hi
    by_cases ia : i=a
    · subst i
      simp [χ,hi] at h
    by_cases ib : i=b
    · rwa [ib] at hi
    · exact False.elim (hu ⟨i,ia,ib⟩ ((rows ⟨i,ia,ib⟩ e.1).symm.trans hi))
  have different {e f : Fin n × Fin n} (hne : e≠f) (incident : e.1=f.1 ∨ e.2=f.2)
      (i : Fin n) (he : L.mat i e.1=e.2) (hf : L.mat i f.1=f.2) : False := by
    apply hne
    rcases incident with h | h
    · exact Prod.ext h (he.symm.trans ((congrArg (L.mat i) h).trans hf))
    · exact Prod.ext (L.row_injective i (he.trans (h.trans hf.symm))) h
  refine ⟨χ,?_,?_⟩
  · intro e f he hf hne inc eqn
    cases hc : χ e with
    | false => exact different hne inc b (other e he hc) (other f hf (eqn ▸ hc))
    | true => exact different hne inc a (yes e hc) (yes f (eqn ▸ hc))
  · intro e f he hf ⟨σ,τ,sa,sb,ta,tb,base⟩
    by_contra neq
    apply no
    apply fill L σ τ (fun i => (rows i _).trans (base i))
    cases ec : χ e <;> cases fc : χ f
    · exact False.elim (neq (ec.trans fc.symm))
    · right
      simpa [sa,sb,ta,tb] using And.intro (yes f fc) (other e he ec)
    · left
      simpa [sa,sb,ta,tb] using And.intro (yes e ec) (other f hf fc)
    · exact False.elim (neq (ec.trans fc.symm))
/-- Seven-row prefixes where the longest cycle of the marked row has length at least five. -/
def H1 : Prop :=
  let rows : Fin 5 → Fin 9 → Fin 9 := ![![1, 2, 3, 4, 5, 6, 7, 8, 0],
      ![1, 2, 3, 4, 5, 6, 0, 8, 7],
      ![1, 2, 3, 4, 5, 0, 7, 8, 6],
      ![1, 2, 3, 4, 0, 6, 7, 8, 5],
      ![1, 2, 3, 4, 0, 6, 5, 8, 7]]
  let R := {i : Fin 9 // i ≠ 7 ∧ i ≠ 8}
  ∀ (P : R → Fin 9 → Fin 9) (u : Fin 5),
    (∀ i, Function.Injective (P i)) → (∀ j, Function.Injective (fun i => P i j)) →
    (∀ j, P ⟨0,by decide⟩ j = j) → (∀ i, P i 0 = i.val) →
    (∀ j, P ⟨1,by decide⟩ j = rows u j) →
    let unused := fun e : Fin 9 × Fin 9 => ∀ i, P i e.1 ≠ e.2
    ¬ ∃ χ : (Fin 9 × Fin 9) → Bool,
      (∀ e f, unused e → unused f → e≠f → (e.1=f.1 ∨ e.2=f.2) → χ e≠χ f) ∧
      (∀ e f, unused e → unused f →
        (∃ σ τ : Equiv.Perm (Fin 9), σ 7=e.1 ∧ σ 8=f.1 ∧ τ 7=e.2 ∧ τ 8=f.2 ∧
          ∀ i : R, P i (σ i) = τ i) → χ e=χ f)

/-- Seven-row prefixes where the longest cycle of the marked row has length at most four. -/
def H2 : Prop :=
  let rows : Fin 3 → Fin 9 → Fin 9 := ![![1, 2, 3, 0, 5, 6, 4, 8, 7],
      ![1, 2, 0, 4, 5, 3, 7, 8, 6],
      ![1, 2, 0, 4, 3, 6, 5, 8, 7]]
  let R := {i : Fin 9 // i ≠ 7 ∧ i ≠ 8}
  ∀ (P : R → Fin 9 → Fin 9) (u : Fin 3),
    (∀ i, Function.Injective (P i)) → (∀ j, Function.Injective (fun i => P i j)) →
    (∀ j, P ⟨0,by decide⟩ j = j) → (∀ i, P i 0 = i.val) →
    (∀ j, P ⟨1,by decide⟩ j = rows u j) →
    let unused := fun e : Fin 9 × Fin 9 => ∀ i, P i e.1 ≠ e.2
    ¬ ∃ χ : (Fin 9 × Fin 9) → Bool,
      (∀ e f, unused e → unused f → e≠f → (e.1=f.1 ∨ e.2=f.2) → χ e≠χ f) ∧
      (∀ e f, unused e → unused f →
        (∃ σ τ : Equiv.Perm (Fin 9), σ 7=e.1 ∧ σ 8=f.1 ∧ τ 7=e.2 ∧ τ 8=f.2 ∧
          ∀ i : R, P i (σ i) = τ i) → χ e=χ f)

theorem main : H1 → H2 → OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1.H2 := by
  intro long short L first col a _ ⟨idx,marked⟩
  let allRows : Fin 8 → Fin 9 → Fin 9 := ![![1, 2, 3, 4, 5, 6, 7, 8, 0],
      ![1, 2, 3, 4, 5, 6, 0, 8, 7],
      ![1, 2, 3, 4, 5, 0, 7, 8, 6],
      ![1, 2, 3, 4, 0, 6, 7, 8, 5],
      ![1, 2, 3, 4, 0, 6, 5, 8, 7],
      ![1, 2, 3, 0, 5, 6, 4, 8, 7],
      ![1, 2, 0, 4, 5, 3, 7, 8, 6],
      ![1, 2, 0, 4, 3, 6, 5, 8, 7]]
  change ∀ j, L.mat a j = allRows idx j at marked
  have starts : ∀ i : Fin 8, allRows i 0 = 1 := by decide
  have a1 : a = 1 := (col a).symm.trans ((marked 0).trans (starts idx))
  subst a
  by_contra no
  let R := {i : Fin 9 // i ≠ 7 ∧ i ≠ 8}
  let P (i : R) (j : Fin 9) := L.mat i.val j
  have rowInj (i : R) : Function.Injective (P i) := L.row_injective i.val
  have colInj (j : Fin 9) : Function.Injective (fun i : R => P i j) :=
    fun _ _ eqn => Subtype.ext (L.col_injective j eqn)
  have colors := permits (a := (7:Fin 9)) (b := (8:Fin 9)) P L (fun _ _ => rfl) no
  have lcase (j : Fin 5) := long P j rowInj colInj first (fun i => col i.val)
  have scase (j : Fin 3) := short P j rowInj colInj first (fun i => col i.val)
  fin_cases idx
  · exact lcase 0 marked colors
  · exact lcase 1 marked colors
  · exact lcase 2 marked colors
  · exact lcase 3 marked colors
  · exact lcase 4 marked colors
  · exact scase 0 marked colors
  · exact scase 1 marked colors
  · exact scase 2 marked colors

end OMA.R_LatinSquare_oddOrderLeq9LatinSquareTransversal_R1_H1_R1_H2_R1
