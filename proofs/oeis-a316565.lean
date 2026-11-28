import OMAStatements.S_oeis_a316565
import Mathlib

/-
A316565: the largest order of an element of GL(2, Z/p) is (p-1)(p+1) = p^2 - 1 for prime p.

Upper bound. For g in GL(2, Z/p) with matrix M, Cayley-Hamilton gives M^2 = tr(M) M - det(M),
so every power of M lies in the image of (x, y) -> x + y M, a set of at most p^2 matrices that
contains 0. The orderOf g distinct powers of M are nonzero, hence orderOf g <= p^2 - 1.

Attained. The field with p^2 elements is a 2-dimensional algebra over Z/p whose unit group is
cyclic of order p^2 - 1. Its left regular representation in a basis is an injective algebra map
into the 2 x 2 matrices, so the image of a generator is an element of GL(2, Z/p) of order p^2 - 1.
-/

namespace OMA.P316565
open Matrix

lemma psq (p : ℕ) (hp : 0 < p) : p * p - 1 = (p - 1) * (p + 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have : (q + 1) * (q + 1) = q * (q + 1 + 1) + 1 := by ring
  omega

lemma upper (p : ℕ) [hp : Fact p.Prime] (g : GL (Fin 2) (ZMod p)) :
    orderOf g ≤ (p - 1) * (p + 1) := by
  classical
  let M : Matrix (Fin 2) (Fin 2) (ZMod p) := g.val
  let φ : ZMod p × ZMod p → Matrix (Fin 2) (Fin 2) (ZMod p) := fun v => v.1 • 1 + v.2 • M
  have hCH : M * M = M.trace • M - M.det • 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.trace, Matrix.det_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  have hpow : ∀ k : ℕ, ∃ v, φ v = M ^ k := by
    intro k
    induction k with
    | zero => exact ⟨(1, 0), by simp [φ]⟩
    | succ k ih =>
      obtain ⟨⟨x, y⟩, h⟩ := ih
      refine ⟨(-(y * M.det), x + y * M.trace), ?_⟩
      rw [pow_succ, ← h]
      simp only [φ]
      rw [add_mul, smul_mul_assoc, one_mul, smul_mul_assoc, hCH]
      module
  have hinj : Set.InjOn (fun k : ℕ => M ^ k) (Finset.range (orderOf g) : Set ℕ) := by
    intro k hk l hl h
    have h' : g ^ k = g ^ l := Units.ext (by simpa [M] using h)
    exact pow_injOn_Iio_orderOf (by simpa using hk) (by simpa using hl) h'
  have hsub : (Finset.range (orderOf g)).image (fun k : ℕ => M ^ k) ⊆
      (Finset.univ.image φ).erase 0 := by
    intro A hA
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hA
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · have : (M ^ k) = ((g ^ k : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) := by simp [M]
      rw [this]
      exact (g ^ k).ne_zero
    · obtain ⟨v, hv⟩ := hpow k
      exact Finset.mem_image.2 ⟨v, Finset.mem_univ _, hv⟩
  have h0 : (0 : Matrix (Fin 2) (Fin 2) (ZMod p)) ∈ Finset.univ.image φ :=
    Finset.mem_image.2 ⟨(0, 0), Finset.mem_univ _, by simp [φ]⟩
  calc orderOf g = ((Finset.range (orderOf g)).image (fun k : ℕ => M ^ k)).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ ((Finset.univ.image φ).erase 0).card := Finset.card_le_card hsub
    _ = (Finset.univ.image φ).card - 1 := Finset.card_erase_of_mem h0
    _ ≤ p * p - 1 := Nat.sub_le_sub_right (Finset.card_image_le.trans (by simp [ZMod.card])) 1
    _ = (p - 1) * (p + 1) := psq p hp.out.pos

lemma exists_max (p : ℕ) [hp : Fact p.Prime] :
    ∃ g : GL (Fin 2) (ZMod p), orderOf g = (p - 1) * (p + 1) := by
  classical
  have hfr : Module.finrank (ZMod p) (GaloisField p 2) = 2 := GaloisField.finrank p (by norm_num)
  let b : Module.Basis (Fin 2) (ZMod p) (GaloisField p 2) := Module.finBasisOfFinrankEq _ _ hfr
  have : Fintype (GaloisField p 2) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (GaloisField p 2)ˣ)
  have hord : orderOf u = p * p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, GaloisField.card p 2 (by norm_num),
      pow_two]
  let f : GaloisField p 2 →* Matrix (Fin 2) (Fin 2) (ZMod p) := (Algebra.leftMulMatrix b : _ →* _)
  refine ⟨Units.map f u, ?_⟩
  rw [orderOf_injective (Units.map f) (Units.map_injective (Algebra.leftMulMatrix_injective b)) u,
    hord, psq p hp.out.pos]

lemma main' : ∀ p : ℕ, p.Prime →
    sSup (Set.range (fun g : GL (Fin 2) (ZMod p) => orderOf g)) = (p - 1) * (p + 1) := by
  intro p hp
  have := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_max p
  exact IsGreatest.csSup_eq ⟨⟨g, hg⟩, by rintro _ ⟨h, rfl⟩; exact upper p h⟩

end OMA.P316565

theorem OMA.solution : type_of% @OMA.S_oeis_a316565.main := by
  intro p hp
  exact OMA.P316565.main' p hp
