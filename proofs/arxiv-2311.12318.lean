import OMAStatements.S_arxiv_2311_12318
import Mathlib

namespace CubeFreeBound

open Finset OMA.S_arxiv_2311_12318

private theorem double_with_carry_injective (N : ℕ) [NeZero N] :
    Function.Injective (fun a : ZMod N => (a + a, decide (a.val + a.val < N))) := by
  intro a b hab
  have hsum : a + a = b + b := congrArg Prod.fst hab
  have hflag := congrArg Prod.snd hab
  change decide (a.val + a.val < N) = decide (b.val + b.val < N) at hflag
  have hv : (a + a).val = (b + b).val := congrArg ZMod.val hsum
  apply ZMod.val_injective N
  by_cases ha : a.val + a.val < N
  · have hb : b.val + b.val < N := by simpa [ha, eq_comm] using hflag
    rw [ZMod.val_add_of_lt ha, ZMod.val_add_of_lt hb] at hv
    omega
  · have hb : ¬ b.val + b.val < N := by simpa [ha, eq_comm] using hflag
    have hva := ZMod.val_add_val_of_le (a := a) (b := a) (by omega)
    have hvb := ZMod.val_add_val_of_le (a := b) (b := b) (by omega)
    omega

private theorem card_bound (N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (hfree : CubeFree (A : Set (ZMod N))) : 3 * A.card ≤ 2 * N := by
  classical
  let B : Finset (ZMod N) := univ \ A
  have hB (a : ZMod N) : a ∈ B ↔ a ∉ A := by simp [B]
  have hcard : B.card + A.card = N := by
    simpa [B, ZMod.card] using card_sdiff_add_card_eq_card (subset_univ A)
  by_contra! hdense
  have hx : ∃ x ∈ A, x + x ∈ A := by
    by_contra! h
    have hle : A.card ≤ (B ×ˢ (univ : Finset Bool)).card := by
      apply card_le_card_of_injOn _ ?_ (double_with_carry_injective N).injOn
      intro a ha
      exact mem_product.mpr ⟨(hB _).mpr (h a ha), mem_univ _⟩
    rw [card_product, card_univ, Fintype.card_bool] at hle
    omega
  obtain ⟨x, hx, hxx⟩ := hx
  let T (y : ZMod N) := B.image fun b => b - y
  have hT (y : ZMod N) : (T y).card = B.card := by
    apply card_image_of_injective
    intro a b hab
    change a - y = b - y at hab
    exact sub_left_inj.mp hab
  have hmem (y z : ZMod N) (h : y + z ∉ A) : z ∈ T y := by
    apply mem_image.mpr
    refine ⟨y + z, (hB _).mpr h, ?_⟩
    abel
  let C := (B ∪ T x) ∪ T (x + x)
  have hc : C.card < N := by
    have h₁ := card_union_le B (T x)
    have h₂ := card_union_le (B ∪ T x) (T (x + x))
    rw [hT] at h₁
    rw [hT] at h₂
    change C.card ≤ _ at h₂
    omega
  have hnot : ¬ univ ⊆ C := by
    intro h
    have hle := card_le_card h
    rw [card_univ, ZMod.card] at hle
    omega
  obtain ⟨z, _, hz⟩ := Finset.not_subset.mp hnot
  have hzA : z ∈ A := by
    by_contra hn
    exact hz (mem_union_left _ (mem_union_left _ ((hB _).mpr hn)))
  have hxz : x + z ∈ A := by
    by_contra hn
    exact hz (mem_union_left _ (mem_union_right _ (hmem x z hn)))
  have hxxz : x + x + z ∈ A := by
    by_contra hn
    exact hz (mem_union_right _ (hmem (x + x) z hn))
  apply hfree x x z
  simp only [cube, Set.insert_subset_iff, Set.singleton_subset_iff, Finset.mem_coe]
  exact ⟨hx, hx, hzA, hxx, hxz, hxz, hxxz⟩

private theorem sharp (N : ℕ) [NeZero N] (hN : 3 ∣ N) :
    ∃ A : Finset (ZMod N),
      (∀ a : ZMod N, a ∈ A ↔ a.val % 3 = 1 ∨ a.val % 3 = 2) ∧
      CubeFree (A : Set (ZMod N)) ∧ 3 * A.card = 2 * N := by
  classical
  have hm : 3 * (N / 3) = N := by
    obtain ⟨k, hk⟩ := hN
    omega
  let f (p : Fin (N / 3) × Fin 2) : ZMod N :=
    ((3 * (p.1 : ℕ) + (p.2 : ℕ) + 1 : ℕ) : ZMod N)
  let A := univ.image f
  have hf (p : Fin (N / 3) × Fin 2) :
      (f p).val = 3 * (p.1 : ℕ) + (p.2 : ℕ) + 1 := by
    have h₁ := p.1.isLt
    have h₂ := p.2.isLt
    exact (ZMod.val_natCast _ _).trans (Nat.mod_eq_of_lt (by omega))
  have hinj : Function.Injective f := by
    intro p q hpq
    apply Prod.ext <;> apply Fin.ext
    all_goals
      have hp := p.2.isLt
      have hq := q.2.isLt
      have he := congrArg ZMod.val hpq
      rw [hf, hf] at he
      omega
  have hmem (a : ZMod N) : a ∈ A ↔ a.val % 3 = 1 ∨ a.val % 3 = 2 := by
    constructor
    · intro ha
      obtain ⟨p, _, rfl⟩ := mem_image.mp ha
      rw [hf]
      have hp := p.2.isLt
      omega
    · intro ha
      have hlt := ZMod.val_lt a
      let i : Fin (N / 3) := ⟨a.val / 3, by omega⟩
      let j : Fin 2 := ⟨a.val % 3 - 1, by omega⟩
      refine mem_image.mpr ⟨(i, j), mem_univ _, ZMod.val_injective N ?_⟩
      rw [hf]
      change 3 * (a.val / 3) + (a.val % 3 - 1) + 1 = a.val
      omega
  refine ⟨A, hmem, ?_, ?_⟩
  · intro x y z hs
    simp only [cube, Set.insert_subset_iff, Set.singleton_subset_iff, Finset.mem_coe, hmem] at hs
    have hmod (a b : ZMod N) :
        (a + b).val % 3 = (a.val % 3 + b.val % 3) % 3 := by
      rw [ZMod.val_add, Nat.mod_mod_of_dvd _ hN, Nat.add_mod]
    obtain ⟨hx, hy, hz, hxy, hyz, hxz, hxyz⟩ := hs
    rw [hmod x y] at hxy
    rw [hmod y z] at hyz
    rw [hmod x z] at hxz
    rw [hmod (x + y) z, hmod x y] at hxyz
    omega
  · rw [show A = univ.image f from rfl, card_image_of_injective _ hinj, card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    omega

end CubeFreeBound

theorem OMA.solution : type_of% @OMA.S_arxiv_2311_12318.main := by
  intro N hN
  exact ⟨CubeFreeBound.card_bound N, CubeFreeBound.sharp N⟩