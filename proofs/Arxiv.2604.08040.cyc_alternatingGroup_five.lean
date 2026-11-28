import FormalConjectures.Arxiv.«2604.08040».Conjecture5_5

/-! Count cyclic subgroups by canonical finite sets of powers.
The original finite certificate is credited to @ldy985. -/

namespace OMA.P15

abbrev A5 := alternatingGroup (Fin 5)

def P5 (g : A5) : Finset A5 := (Finset.range 5).image (g ^ ·)

def small_order : ∀ g : A5, ∃ n : Fin 5, g ^ (n.val + 1) = 1 := by decide +kernel

def card_image : (Finset.univ.image P5).card = 32 := by decide +kernel

theorem main : Arxiv.«2604.08040».cyc A5 = 32 := by
  classical
  let encode (H : Subgroup A5) := (H : Set A5).toFinite.toFinset
  have hinj : Function.Injective encode := by
    intro H K h
    ext g
    simpa [encode] using Finset.ext_iff.mp h g
  have hz (g : A5) : encode (Subgroup.zpowers g) = P5 g := by
    ext h
    simp only [encode, Set.Finite.mem_toFinset, SetLike.mem_coe, P5, Finset.mem_image,
      Finset.mem_range]
    constructor
    · intro hh
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hh)
      obtain ⟨n, hn⟩ := small_order g
      exact ⟨k, (Finset.mem_range.mp hk).trans_le
        ((orderOf_le_of_pow_eq_one (Nat.succ_pos _) hn).trans n.isLt), rfl⟩
    · rintro ⟨k, _, rfl⟩
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hc : {H : Subgroup A5 | IsCyclic H} = Set.range Subgroup.zpowers := by
    ext H
    exact H.isCyclic_iff_exists_zpowers_eq_top
  change ({H : Subgroup A5 | IsCyclic H} : Set (Subgroup A5)).ncard = 32
  have he : encode ∘ Subgroup.zpowers = P5 := funext hz
  rw [hc, ← Set.ncard_image_of_injective _ hinj, ← Set.range_comp, he]
  have hf := Set.ncard_coe_finset (Finset.univ.image P5)
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hf
  exact hf.trans card_image

end OMA.P15

theorem OMA.solution : type_of% @Arxiv.«2604.08040».cyc_alternatingGroup_five :=
  OMA.P15.main
