import OMAStatements.S_mo_262336
import Mathlib

-- Retains @connoranderson’s earlier complement-equivalence proof from statement #24931.
-- The weighted-fiber sum uses the same standard API as @Salofe’s merged proof #29264.

namespace OMA.S_mo_262336
open Finset

private def restrict {n : ℕ} (S : Finset (Fin n)) (σ : Equiv.Perm (Fin n)) : S ↪ Fin n :=
  (Function.Embedding.subtype (· ∈ S)).trans σ.toEmbedding

private lemma extensions {n : ℕ} (S : Finset (Fin n)) (e : S ↪ Fin n) :
    Fintype.card {σ : Equiv.Perm (Fin n) // restrict S σ = e} = (n-S.card).factorial := by
  classical
  let T : Set (Fin n) := Set.range e
  let f : (S : Set (Fin n)) ≃ T := e.toEquivRange
  let b := Equiv.subtypeEquivRight (p := fun σ : Equiv.Perm (Fin n) => restrict S σ = e)
    (q := fun σ : Equiv.Perm (Fin n) => ∀ x : (S : Set (Fin n)), σ x = f x) (fun σ => by
      constructor
      · intro h x
        exact congrArg (fun g : S ↪ Fin n => g x) h
      · intro h
        exact Function.Embedding.ext h)
  rw [Fintype.card_congr (b.trans (Equiv.Set.compl f))]
  let fc : ((S : Set (Fin n))ᶜ : Set (Fin n)) ≃ (Tᶜ : Set (Fin n)) := f.toCompl
  calc
    _ = (Fintype.card ((S : Set (Fin n))ᶜ : Set (Fin n))).factorial := Fintype.card_equiv fc
    _ = _ := by
      rw [Fintype.card_compl_set]
      simp

private lemma rows {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (S : Finset (Fin n)) :
    (∑ σ : Equiv.Perm (Fin n), ∏ i ∈ S, M i (σ i)) = ((n-S.card).factorial:R) * minors M S := by
  classical
  let weight (e : S ↪ Fin n) := ∏ i : S, M i (e i)
  have he (σ : Equiv.Perm (Fin n)) : (∏ i ∈ S, M i (σ i)) = weight (restrict S σ) :=
    (Finset.prod_coe_sort S (fun i => M i (σ i))).symm
  simp_rw [he]
  rw [← Fintype.sum_fiberwise' (restrict S) weight]
  simp only [Finset.sum_const, Finset.card_univ, extensions, nsmul_eq_mul,
    Finset.mul_sum, weight, minors]

lemma translated {R : Type} [CommRing R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (a : R) :
    perm (fun i j => M i j+a) = ∑ S : Finset (Fin n),
      ((n-S.card).factorial : R) * a^(n-S.card) * minors M S := by
  classical
  unfold perm
  simp_rw [Finset.prod_add (fun _ => _) (fun _ => a), Finset.powerset_univ, Finset.prod_const,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  rw [← Finset.sum_mul, rows]
  ring

end OMA.S_mo_262336

namespace OMA.S_mo_262336

private lemma two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    perm M = M 0 0*M 1 1 + M 0 1*M 1 0 := by
  classical
  have hn : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by
    intro he
    have := congrArg (fun σ : Equiv.Perm (Fin 2) => σ 0) he
    simp at this
  have hall : ({1, Equiv.swap (0:Fin 2) 1} : Finset (Equiv.Perm (Fin 2))) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [Fintype.card_perm, hn]
  unfold perm
  rw [← hall]
  simp [hn, Fin.prod_univ_two]

lemma witness (a : ℤ) (ha : a ≠ 0) : ∃ M N : Matrix (Fin 2) (Fin 2) ℤ,
    perm M = perm N ∧ perm (fun i j => M i j+a) ≠ perm (fun i j => N i j+a) := by
  refine ⟨0, !![1,0;0,0], ?_, ?_⟩
  · rw [two,two]; simp
  · let A : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (0 : Matrix (Fin 2) (Fin 2) ℤ) i j+a
    let B : Matrix (Fin 2) (Fin 2) ℤ := fun i j => (!![1,0;0,0] : Matrix (Fin 2) (Fin 2) ℤ) i j+a
    change perm A ≠ perm B
    rw [two A,two B]
    simp [A,B]
    intro h; apply ha; nlinarith

end OMA.S_mo_262336


theorem OMA.solution : type_of% @OMA.S_mo_262336.main := by
  refine ⟨?_, OMA.S_mo_262336.witness⟩
  intro R _ n M a
  exact OMA.S_mo_262336.translated M (a:R)
