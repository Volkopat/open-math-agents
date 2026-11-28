import FormalConjectures.Arxiv.«2607.08366».MinModulus

-- Reduction Arxiv.2607.08366.min_modulus.R2 of Fonollosa's minimum modulus conjecture
-- Credit: @LordMike
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# The minimum modulus conjecture: a group-free lower bound and a normalised cyclic core

Source: J. A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*,
arXiv:2607.08366. A set `A` of `n` residues mod `N` is valid when the all-ones multiset is the
only multiset of size `n` drawn from `A` with sum `∑ A`. Conjecture 1 says that no valid set
exists for `N < 2 ^ n - 2 ^ ⌊log₂ n⌋`.

* `H1` (elementary, a pigeonhole on the `2 ^ (n - 1)` subsets of `A` minus one point): a valid
  set of `n` residues mod `N` forces `2 ^ (n - 1) ≤ N`. The argument uses nothing about the
  cyclic group, and `(ℤ/2)^(n-1)` shows that it is sharp for general abelian groups. The paper
  lists an exponential lower bound for all sets as open (Section 8).
* `H2` (the open core): Conjecture 1 for `2 ^ (n - 1) ≤ N < 2 ^ n - 2 ^ ⌊log₂ n⌋` and for
  normalised sets only: `0 ∈ A` and `A` generates `ZMod N`. This is a special case of the target.

A different reduction, `Arxiv.2607.08366.min_modulus.R1` (a 2-adic descent), is already merged.
Its three hypotheses are all open; `H1` here is proved outright (see the step file), so this
reduction leaves a single open hypothesis, which is a special case of the target.

`main` removes the normalisations. Validity is invariant under translation, so `0 ∈ A` is free.
If the translated set generates a proper subgroup, that subgroup is cyclic of order `N' ∣ N`, the
set pulls back to a valid generating set of `ZMod N'`, `H1` gives `2 ^ (n - 1) ≤ N'`, and `H2`
applies at the modulus `N'`.
-/

namespace OMA.R_Arxiv_2607_08366_min_modulus_R2

open Finset Arxiv.«2607.08366»

/-- A valid set of `n` residues mod `N` forces `2 ^ (n - 1) ≤ N`. -/
def H1 : Prop :=
  ∀ n N : ℕ, 0 < N → ∀ A : Finset (ZMod N), A.card = n →
    Arxiv.«2607.08366».IsValidMod A → 2 ^ (n - 1) ≤ N

/-- Conjecture 1 for `2 ^ (n - 1) ≤ N` and sets that contain `0` and generate `ZMod N`. -/
def H2 : Prop :=
  ∀ n N : ℕ, 2 ≤ n → 2 ^ (n - 1) ≤ N → N < Arxiv.«2607.08366».minModulus n →
    ∀ A : Finset (ZMod N), A.card = n → (0 : ZMod N) ∈ A →
      AddSubgroup.closure (A : Set (ZMod N)) = ⊤ → ¬ Arxiv.«2607.08366».IsValidMod A

/-- Validity is invariant under translation. -/
lemma valid_translate {N : ℕ} (A : Finset (ZMod N)) (c : ZMod N) (h : IsValidMod A) :
    IsValidMod (A.image (fun a => a - c)) := by
  have hinj : Function.Injective (fun a : ZMod N => a - c) := sub_left_injective
  intro m hs hw b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)] at hs
  rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy),
    Finset.sum_image (fun x _ y _ hxy => hinj hxy)] at hw
  rw [Finset.card_image_of_injective _ hinj] at hs
  refine h (fun a => m (a - c)) hs ?_ a ha
  have hs' : ∑ a ∈ A, (m (a - c) : ZMod N) = (A.card : ZMod N) := by
    rw [← hs]; push_cast; rfl
  have e1 : ∑ a ∈ A, (m (a - c) : ZMod N) * (a - c)
      = ∑ a ∈ A, (m (a - c) : ZMod N) * a - (∑ a ∈ A, (m (a - c) : ZMod N)) * c := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have e2 : ∑ a ∈ A, (a - c) = ∑ a ∈ A, a - (A.card : ZMod N) * c := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  rw [e1, e2, hs'] at hw
  linear_combination hw

/-- Validity pulls back along an injective additive map between residue rings. -/
lemma valid_of_image {N N' : ℕ} (φ : ZMod N' →+ ZMod N) (hφ : Function.Injective φ)
    (A : Finset (ZMod N')) (h : IsValidMod (A.image φ)) : IsValidMod A := by
  intro m hs hw a ha
  have hl : ∀ x, Function.invFun φ (φ x) = x := Function.leftInverse_invFun hφ
  have key := h (fun b => m (Function.invFun φ b)) ?_ ?_ (φ a) (Finset.mem_image_of_mem _ ha)
  · simpa [hl] using key
  · rw [Finset.sum_image (fun x _ y _ hxy => hφ hxy), Finset.card_image_of_injective _ hφ]
    simpa [hl] using hs
  · rw [Finset.sum_image (fun x _ y _ hxy => hφ hxy), Finset.sum_image (fun x _ y _ hxy => hφ hxy)]
    have h1 : ∀ x ∈ A, ((m (Function.invFun φ (φ x)) : ℕ) : ZMod N) * φ x
        = φ ((m x : ZMod N') * x) := by
      intro x _
      rw [hl, ← nsmul_eq_mul, ← nsmul_eq_mul, map_nsmul]
    rw [Finset.sum_congr rfl h1, ← map_sum, hw, map_sum]

theorem main : H1 → H2 → type_of% @Arxiv.«2607.08366».min_modulus := by
  intro h1 h2 n N hn hN hlt A hA hv
  have : NeZero N := ⟨hN.ne'⟩
  obtain ⟨c, hc⟩ : A.Nonempty := Finset.card_pos.mp (by omega)
  have hinj : Function.Injective (fun a : ZMod N => a - c) := sub_left_injective
  set A₁ : Finset (ZMod N) := A.image (fun a => a - c) with hA₁
  have hv₁ : IsValidMod A₁ := valid_translate A c hv
  have hcard₁ : A₁.card = n := by rw [hA₁, Finset.card_image_of_injective _ hinj, hA]
  have h0 : (0 : ZMod N) ∈ A₁ := Finset.mem_image.mpr ⟨c, hc, sub_self c⟩
  -- the subgroup generated by `A₁`, as a copy of `ZMod N'`
  set H : AddSubgroup (ZMod N) := AddSubgroup.closure (A₁ : Set (ZMod N)) with hH
  have hcyc : IsAddCyclic H := inferInstance
  set N' : ℕ := Nat.card H with hN'
  have hN'pos : 0 < N' := Nat.card_pos
  have hN'le : N' ≤ N := by
    have := Nat.card_le_card_of_injective (Subtype.val : H → ZMod N) Subtype.val_injective
    rwa [Nat.card_zmod] at this
  let e : ZMod N' ≃+ H := zmodAddCyclicAddEquiv hcyc
  let φ : ZMod N' →+ ZMod N := H.subtype.comp e.toAddMonoidHom
  have hφ : Function.Injective φ := by
    intro x y hxy
    exact e.injective (Subtype.ext hxy)
  have hrange : ∀ a ∈ H, ∃ x, φ x = a := by
    intro a ha
    exact ⟨e.symm ⟨a, ha⟩, by simp [φ]⟩
  have hφH : ∀ x, φ x ∈ H := fun x => (e x).2
  set A₂ : Finset (ZMod N') := A₁.image (Function.invFun φ) with hA₂
  have hr : ∀ a ∈ A₁, φ (Function.invFun φ a) = a := by
    intro a ha
    exact Function.invFun_eq (hrange a (AddSubgroup.subset_closure (Finset.mem_coe.mpr ha)))
  have himg : A₂.image φ = A₁ := by
    rw [hA₂, Finset.image_image]
    conv_rhs => rw [← Finset.image_id (s := A₁)]
    exact Finset.image_congr fun a ha => hr a ha
  have hv₂ : IsValidMod A₂ := valid_of_image φ hφ A₂ (himg ▸ hv₁)
  have hcard₂ : A₂.card = n := by
    rw [← hcard₁, ← himg, Finset.card_image_of_injective _ hφ]
  have h0₂ : (0 : ZMod N') ∈ A₂ := by
    rw [hA₂]
    refine Finset.mem_image.mpr ⟨0, h0, ?_⟩
    apply hφ
    rw [hr 0 h0, map_zero]
  have hgen : AddSubgroup.closure (A₂ : Set (ZMod N')) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : φ x ∈ H := hφH x
    have hle : H ≤ (AddSubgroup.closure (A₂ : Set (ZMod N'))).map φ := by
      rw [hH, AddSubgroup.closure_le]
      intro a ha
      refine ⟨Function.invFun φ a, AddSubgroup.subset_closure ?_, hr a ha⟩
      exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ ha)
    obtain ⟨y, hy, hyx⟩ := hle hx
    rwa [← hφ hyx]
  have hlow : 2 ^ (n - 1) ≤ N' := h1 n N' hN'pos A₂ hcard₂ hv₂
  exact h2 n N' hn hlow (lt_of_le_of_lt hN'le hlt) A₂ hcard₂ h0₂ hgen hv₂

end OMA.R_Arxiv_2607_08366_min_modulus_R2
