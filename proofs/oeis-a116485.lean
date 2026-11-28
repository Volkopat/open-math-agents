import OMAStatements.S_oeis_a116485

-- Problem: A116485, a(n) + A158423(n) = n! (Irwin's conjecture), via reverse-complement and inverse symmetry.
-- Credit: @bnb9001

namespace OMA_A116485_Proof

open Equiv Finset OMA.S_oeis_a116485

/-- reverse-complement of a permutation -/
def rc {n : ℕ} (π : Perm (Fin n)) : Perm (Fin n) := Fin.revPerm * π * Fin.revPerm

theorem rc_rc {n : ℕ} (π : Perm (Fin n)) : rc (rc π) = π := by
  ext i; simp [rc]

theorem contains_rc {n k : ℕ} {π : Perm (Fin n)} {σ : Perm (Fin k)} (h : Contains π σ) :
    Contains (rc π) (rc σ) := by
  obtain ⟨f, hf⟩ := h
  have hmono : StrictMono (fun i : Fin k => Fin.rev (f (Fin.rev i))) := by
    intro i j hij
    simp only [Fin.rev_lt_rev]
    exact f.strictMono (Fin.rev_lt_rev.mpr hij)
  refine ⟨OrderEmbedding.ofStrictMono _ hmono, fun i j => ?_⟩
  simp only [OrderEmbedding.coe_ofStrictMono, rc, Perm.coe_mul, Function.comp_apply,
    Fin.revPerm_apply, Fin.rev_rev, Fin.rev_lt_rev]
  exact hf (Fin.rev j) (Fin.rev i)

theorem contains_inv {n k : ℕ} {π : Perm (Fin n)} {σ : Perm (Fin k)} (h : Contains π σ) :
    Contains π⁻¹ σ⁻¹ := by
  obtain ⟨f, hf⟩ := h
  have hmono : StrictMono (fun m : Fin k => π (f (σ⁻¹ m))) := by
    intro m m' hmm
    apply (hf _ _).mpr
    simpa using hmm
  refine ⟨OrderEmbedding.ofStrictMono _ hmono, fun i j => ?_⟩
  simp only [OrderEmbedding.coe_ofStrictMono]
  rw [show ∀ x, π⁻¹ (π x) = x from fun x => by simp,
    show ∀ x, π⁻¹ (π x) = x from fun x => by simp]
  exact f.lt_iff_lt

theorem contains_rc_iff {n k : ℕ} (π : Perm (Fin n)) (σ : Perm (Fin k)) :
    Contains π σ ↔ Contains (rc π) (rc σ) :=
  ⟨contains_rc, fun h => by simpa [rc_rc] using contains_rc h⟩

theorem contains_inv_iff {n k : ℕ} (π : Perm (Fin n)) (σ : Perm (Fin k)) :
    Contains π σ ↔ Contains π⁻¹ σ⁻¹ :=
  ⟨contains_inv, fun h => by simpa using contains_inv h⟩

theorem card_filter_equiv {α : Type*} [Fintype α] (e : α ≃ α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] (h : ∀ x, P x ↔ Q (e x)) :
    (univ.filter P).card = (univ.filter Q).card := by
  apply Finset.card_bij (fun x _ => e x)
  · intro x hx; simp only [mem_filter, mem_univ, true_and] at hx ⊢; exact (h x).mp hx
  · intro x _ y _ hxy; exact e.injective hxy
  · intro y hy
    refine ⟨e.symm y, ?_, by simp⟩
    simp only [mem_filter, mem_univ, true_and] at hy ⊢
    exact (h _).mpr (by simpa using hy)

theorem rc_pat : rc pat12453 = pat23145⁻¹ := by decide

open Classical in
theorem avoid_eq (n : ℕ) :
    (univ.filter fun π : Perm (Fin n) => ¬ Contains π pat12453).card =
      (univ.filter fun π : Perm (Fin n) => ¬ Contains π pat23145).card := by
  classical
  calc (univ.filter fun π : Perm (Fin n) => ¬ Contains π pat12453).card
      = (univ.filter fun π : Perm (Fin n) => ¬ Contains π pat23145⁻¹).card := by
        apply card_filter_equiv ⟨rc, rc, rc_rc, rc_rc⟩
        intro π
        simp only [Equiv.coe_fn_mk]
        rw [contains_rc_iff π pat12453, rc_pat]
    _ = (univ.filter fun π : Perm (Fin n) => ¬ Contains π pat23145).card := by
        apply card_filter_equiv (Equiv.inv _)
        intro π
        simp only [Equiv.inv_apply]
        rw [contains_inv_iff π pat23145⁻¹, inv_inv]

end OMA_A116485_Proof

open Equiv Finset OMA.S_oeis_a116485 OMA_A116485_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a116485.main := by
  intro n _
  classical
  unfold a b
  rw [avoid_eq n]
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Perm (Fin n))))
    (p := fun π => Contains π pat23145)
  rw [add_comm] at this
  rw [this, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
