import FormalConjectures.Wikipedia.LeinsterGroup

/-!
# Dihedral Leinster Groups

Proof that `DihedralGroup n` (`n ≠ 0`) is a Leinster group if and only if `n` is an odd perfect
number (Leinster 2001): every subgroup of the rotation subgroup `C_n` is normal, for odd `n` the
only additional normal subgroup is `⊤` (giving sum `2n + σ(n)`), while for even `n` two extra
index-2 normal subgroups push the sum of normal subgroup orders to at least `5n > 4n`.
-/

-- Problem: Leinster Groups — dihedral is leinster iff odd perfect
-- Upstream: formal-conjectures FormalConjectures/Wikipedia/LeinsterGroup.lean:114 (declaration LeinsterGroup.dihedral_is_leinster_iff_odd_perfect)
-- Credit: @TheWaler (the owner of the agent is credited as the solver)
-- Original proof: @TheWaler (#346); subgroup transport uses Mathlib APIs.

open scoped Classical

private def rotHom (n : ℕ) : Multiplicative (ZMod n) →* DihedralGroup n where
  toFun x := DihedralGroup.r (Multiplicative.toAdd x)
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma rotHom_injective (n : ℕ) : Function.Injective (rotHom n) := by
  intro x y h
  exact Multiplicative.toAdd.injective (DihedralGroup.r.inj h)

private lemma mem_rotHom_range_iff {n : ℕ} {g : DihedralGroup n} :
    g ∈ (rotHom n).range ↔ ∃ i : ZMod n, g = DihedralGroup.r i := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨Multiplicative.toAdd x, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Multiplicative.ofAdd i, rfl⟩

private lemma sr_notMem_rotHom_range (n : ℕ) (i : ZMod n) :
    DihedralGroup.sr i ∉ (rotHom n).range := by
  rw [mem_rotHom_range_iff]
  rintro ⟨j, h⟩
  cases h

private lemma normal_of_le_rotHom_range {n : ℕ} {H : Subgroup (DihedralGroup n)}
    (hH : H ≤ (rotHom n).range) : H.Normal where
  conj_mem x hx g := by
    obtain ⟨i, rfl⟩ := mem_rotHom_range_iff.mp (hH hx)
    cases g with
    | r j =>
      have h : DihedralGroup.r j * DihedralGroup.r i * (DihedralGroup.r j)⁻¹ =
          DihedralGroup.r i := by
        simp [add_comm]
      rw [h]
      exact hx
    | sr j =>
      have h : DihedralGroup.sr j * DihedralGroup.r i * (DihedralGroup.sr j)⁻¹ =
          (DihedralGroup.r i)⁻¹ := by
        simp
      rw [h]
      exact H.inv_mem hx

private lemma card_map_rotHom {n : ℕ} (K : Subgroup (Multiplicative (ZMod n))) :
    Nat.card (K.map (rotHom n)) = Nat.card K :=
  Subgroup.card_map_of_injective (rotHom_injective n)

private lemma sum_subgroup_of_isCyclic (G : Type*) [CommGroup G] [Fintype G] [IsCyclic G] :
    (∑ H : Subgroup G, Nat.card H) = ∑ d ∈ (Fintype.card G).divisors, d := by
  have hker : ∀ H : Subgroup G, H = (powMonoidHom (α := G) (Nat.card H)).ker := by
    intro H
    have hle : H ≤ (powMonoidHom (α := G) (Nat.card H)).ker := by
      intro x hx
      rw [MonoidHom.mem_ker, powMonoidHom_apply]
      have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := by
        rw [Nat.card_eq_fintype_card]
        exact pow_card_eq_one
      exact congrArg Subtype.val h1
    have hcard : Nat.card H = Nat.card (powMonoidHom (α := G) (Nat.card H)).ker := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Subgroup.card_subgroup_dvd_card H)]
    exact Subgroup.eq_of_le_of_card_ge hle hcard.ge
  refine Finset.sum_bij (fun H _ => Nat.card H) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro H _
    rw [Nat.mem_divisors]
    exact ⟨by simpa [Nat.card_eq_fintype_card] using Subgroup.card_subgroup_dvd_card H,
      Fintype.card_ne_zero⟩
  · intro H₁ _ H₂ _ h
    rw [hker H₁, hker H₂, h]
  · intro d hd
    rw [Nat.mem_divisors] at hd
    refine ⟨(powMonoidHom (α := G) d).ker, Finset.mem_univ _, ?_⟩
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Nat.gcd_eq_right hd.1]

private lemma normal_eq_top_of_odd_not_le_rot {n : ℕ} (hodd : Odd n)
    {H : Subgroup (DihedralGroup n)} [hN : H.Normal] (hnot : ¬ H ≤ (rotHom n).range) :
    H = ⊤ := by
  have hsr : ∃ i : ZMod n, DihedralGroup.sr i ∈ H := by
    by_contra hno
    push Not at hno
    apply hnot
    intro g hg
    cases g with
    | r i => exact mem_rotHom_range_iff.mpr ⟨i, rfl⟩
    | sr i => exact (hno i hg).elim
  obtain ⟨i, hi⟩ := hsr
  have hr2 : ∀ k : ZMod n, DihedralGroup.r (2 * k) ∈ H := by
    intro k
    have hconj : DihedralGroup.r (-k) * DihedralGroup.sr i * (DihedralGroup.r (-k))⁻¹ ∈ H :=
      hN.conj_mem _ hi _
    have hprod : (DihedralGroup.sr i)⁻¹ *
        (DihedralGroup.r (-k) * DihedralGroup.sr i * (DihedralGroup.r (-k))⁻¹) ∈ H :=
      H.mul_mem (H.inv_mem hi) hconj
    have heq : (DihedralGroup.sr i)⁻¹ *
        (DihedralGroup.r (-k) * DihedralGroup.sr i * (DihedralGroup.r (-k))⁻¹) =
        DihedralGroup.r (2 * k) := by
      simp only [DihedralGroup.inv_sr, DihedralGroup.inv_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
      congr 1
      ring
    rwa [heq] at hprod
  obtain ⟨m, rfl⟩ := hodd
  have h2inv : (2 : ZMod (2 * m + 1)) * ((m : ZMod (2 * m + 1)) + 1) = 1 := by
    have h0 : ((2 * m + 1 : ℕ) : ZMod (2 * m + 1)) = 0 := ZMod.natCast_self (2 * m + 1)
    push_cast at h0
    linear_combination h0
  have hr_all : ∀ a : ZMod (2 * m + 1), DihedralGroup.r a ∈ H := by
    intro a
    have ha : 2 * (((m : ZMod (2 * m + 1)) + 1) * a) = a := by
      rw [← mul_assoc, h2inv, one_mul]
    rw [← ha]
    exact hr2 _
  rw [eq_top_iff]
  intro g _
  cases g with
  | r a => exact hr_all a
  | sr a =>
    have hmul : DihedralGroup.sr i * DihedralGroup.r (a - i) = DihedralGroup.sr a := by
      simp
    rw [← hmul]
    exact H.mul_mem hi (hr_all (a - i))

private lemma zmod2_sub_eq_add (a b : ZMod 2) : b - a = a + b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma not_isLeinster_of_even {n : ℕ} [NeZero n] (heven : Even n) :
    ¬ LeinsterGroup.IsLeinster (DihedralGroup n) := by
  have h2 : 2 ∣ n := even_iff_two_dvd.mp heven
  let φ : ZMod n →+ ZMod 2 := (ZMod.castHom h2 (ZMod 2)).toAddMonoidHom
  let f₁ : DihedralGroup n →* Multiplicative (ZMod 2) :=
    { toFun := fun
        | DihedralGroup.r i => Multiplicative.ofAdd (φ i)
        | DihedralGroup.sr i => Multiplicative.ofAdd (φ i)
      map_one' := by
        change Multiplicative.ofAdd (φ 0) = 1
        simp
      map_mul' := by
        rintro (i | i) (j | j)
        · simp [DihedralGroup.r_mul_r, map_add, ofAdd_add]
        · simp only [DihedralGroup.r_mul_sr, map_sub, zmod2_sub_eq_add, ofAdd_add]
        · simp [DihedralGroup.sr_mul_r, map_add, ofAdd_add]
        · simp only [DihedralGroup.sr_mul_sr, map_sub, zmod2_sub_eq_add, ofAdd_add] }
  let f₂ : DihedralGroup n →* Multiplicative (ZMod 2) :=
    { toFun := fun
        | DihedralGroup.r i => Multiplicative.ofAdd (φ i)
        | DihedralGroup.sr i => Multiplicative.ofAdd (φ i + 1)
      map_one' := by
        change Multiplicative.ofAdd (φ 0) = 1
        simp
      map_mul' := by
        rintro (i | i) (j | j)
        · simp only [DihedralGroup.r_mul_r, map_add, ofAdd_add]
        · change Multiplicative.ofAdd (φ (j - i) + 1) =
              Multiplicative.ofAdd (φ i) * Multiplicative.ofAdd (φ j + 1)
          rw [← ofAdd_add]
          congr 1
          rw [map_sub, zmod2_sub_eq_add]
          ring
        · change Multiplicative.ofAdd (φ (i + j) + 1) =
              Multiplicative.ofAdd (φ i + 1) * Multiplicative.ofAdd (φ j)
          rw [← ofAdd_add]
          congr 1
          rw [map_add]
          ring
        · change Multiplicative.ofAdd (φ (j - i)) =
              Multiplicative.ofAdd (φ i + 1) * Multiplicative.ofAdd (φ j + 1)
          rw [← ofAdd_add]
          congr 1
          rw [map_sub, zmod2_sub_eq_add]
          have h11 : (1 : ZMod 2) + 1 = 0 := by decide
          linear_combination -h11 }
  have hφ1 : φ 1 = 1 := map_one (ZMod.castHom h2 (ZMod 2))
  have hf₁_surj : Function.Surjective f₁ := by
    intro y
    obtain ⟨i, hi⟩ := ZMod.castHom_surjective h2 (Multiplicative.toAdd y)
    refine ⟨DihedralGroup.r i, ?_⟩
    change Multiplicative.ofAdd (φ i) = y
    rw [show φ i = Multiplicative.toAdd y from hi]
    rfl
  have hf₂_surj : Function.Surjective f₂ := by
    intro y
    obtain ⟨i, hi⟩ := ZMod.castHom_surjective h2 (Multiplicative.toAdd y)
    refine ⟨DihedralGroup.r i, ?_⟩
    change Multiplicative.ofAdd (φ i) = y
    rw [show φ i = Multiplicative.toAdd y from hi]
    rfl
  let Htop : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨⊤, inferInstance⟩
  let Hrot : {H : Subgroup (DihedralGroup n) // H.Normal} :=
    ⟨(rotHom n).range, normal_of_le_rotHom_range le_rfl⟩
  let HN₁ : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨f₁.ker, f₁.normal_ker⟩
  let HN₂ : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨f₂.ker, f₂.normal_ker⟩
  have hcard_top : Nat.card Htop.1 = 2 * n := by
    change Nat.card (⊤ : Subgroup (DihedralGroup n)) = 2 * n
    rw [Subgroup.card_top, DihedralGroup.nat_card]
  have hcard_rot : Nat.card Hrot.1 = n := by
    have htop : (⊤ : Subgroup (Multiplicative (ZMod n))).map (rotHom n) = (rotHom n).range := by
      simp [MonoidHom.range_eq_map]
    rw [show Hrot.1 = (⊤ : Subgroup (Multiplicative (ZMod n))).map (rotHom n) from htop.symm,
      card_map_rotHom, Subgroup.card_top]
    simp
  have hcard_ker : ∀ (f : DihedralGroup n →* Multiplicative (ZMod 2)),
      Function.Surjective f → Nat.card f.ker = n := by
    intro f hf
    have hmul := Subgroup.card_mul_index f.ker
    have hidx : f.ker.index = 2 := by
      rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top]
      simp
    rw [hidx, DihedralGroup.nat_card] at hmul
    omega
  have hcard_N₁ : Nat.card HN₁.1 = n := hcard_ker f₁ hf₁_surj
  have hcard_N₂ : Nat.card HN₂.1 = n := hcard_ker f₂ hf₂_surj
  have hne_top_rot : Htop ≠ Hrot := by
    intro h
    have h1 : DihedralGroup.sr (0 : ZMod n) ∈ Hrot.1 := by rw [← h]; exact Subgroup.mem_top _
    exact sr_notMem_rotHom_range n 0 h1
  have hne_top_N₁ : Htop ≠ HN₁ := by
    intro h
    have h1 : DihedralGroup.r (1 : ZMod n) ∈ HN₁.1 := by rw [← h]; exact Subgroup.mem_top _
    change f₁ (DihedralGroup.r 1) = 1 at h1
    simp [f₁, hφ1] at h1
  have hne_top_N₂ : Htop ≠ HN₂ := by
    intro h
    have h1 : DihedralGroup.r (1 : ZMod n) ∈ HN₂.1 := by rw [← h]; exact Subgroup.mem_top _
    change f₂ (DihedralGroup.r 1) = 1 at h1
    simp [f₂, hφ1] at h1
  have hne_rot_N₁ : Hrot ≠ HN₁ := by
    intro h
    have h1 : DihedralGroup.sr (0 : ZMod n) ∈ HN₁.1 := by
      change f₁ (DihedralGroup.sr 0) = 1
      simp [f₁]
    rw [← h] at h1
    exact sr_notMem_rotHom_range n 0 h1
  have hne_rot_N₂ : Hrot ≠ HN₂ := by
    intro h
    have h1 : DihedralGroup.sr (1 : ZMod n) ∈ HN₂.1 := by
      change Multiplicative.ofAdd (φ 1 + 1) = 1
      rw [hφ1]
      decide
    rw [← h] at h1
    exact sr_notMem_rotHom_range n 1 h1
  have hne_N₁_N₂ : HN₁ ≠ HN₂ := by
    intro h
    have h1 : DihedralGroup.sr (0 : ZMod n) ∈ HN₁.1 := by
      change f₁ (DihedralGroup.sr 0) = 1
      simp [f₁]
    rw [h] at h1
    change f₂ (DihedralGroup.sr 0) = 1 at h1
    simp [f₂] at h1
  let S : Finset {H : Subgroup (DihedralGroup n) // H.Normal} := {Htop, Hrot, HN₁, HN₂}
  have hle : ∑ H ∈ S, Nat.card H.1 ≤
      ∑ H : {H : Subgroup (DihedralGroup n) // H.Normal}, Nat.card H.1 :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => Nat.zero_le _)
  have hS : ∑ H ∈ S, Nat.card H.1 = 5 * n := by
    simp only [S, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      hne_top_rot, hne_top_N₁, hne_top_N₂, hne_rot_N₁, hne_rot_N₂, hne_N₁_N₂, or_self,
      not_false_eq_true, hcard_top, hcard_rot, hcard_N₁, hcard_N₂]
    ring
  intro hL
  unfold LeinsterGroup.IsLeinster at hL
  rw [DihedralGroup.card] at hL
  have hn_pos : 0 < n := NeZero.pos n
  omega

theorem OMA.solution : type_of% @LeinsterGroup.dihedral_is_leinster_iff_odd_perfect := by
  intro n _
  by_cases hodd : Odd n
  · let toNorm : Subgroup (Multiplicative (ZMod n)) →
        {H : Subgroup (DihedralGroup n) // H.Normal} := fun K =>
      ⟨K.map (rotHom n), normal_of_le_rotHom_range (by
        rintro _ ⟨x, _, rfl⟩
        exact ⟨x, rfl⟩)⟩
    have htoNorm_inj : Function.Injective toNorm := fun _ _ h =>
      Subgroup.map_injective (rotHom_injective n) (congrArg Subtype.val h)
    let Htop : {H : Subgroup (DihedralGroup n) // H.Normal} := ⟨⊤, inferInstance⟩
    have htop_notMem : Htop ∉ Finset.univ.image toNorm := by
      simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
      intro K hK
      have hsr : DihedralGroup.sr (0 : ZMod n) ∈ K.map (rotHom n) := by
        have hval : K.map (rotHom n) = ⊤ := congrArg Subtype.val hK
        rw [hval]
        exact Subgroup.mem_top _
      obtain ⟨x, _, hx⟩ := hsr
      exact sr_notMem_rotHom_range n 0 ⟨x, hx⟩
    have huniv : (Finset.univ : Finset {H : Subgroup (DihedralGroup n) // H.Normal}) =
        insert Htop (Finset.univ.image toNorm) := by
      ext ⟨H, hN⟩
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_and, true_iff]
      by_cases hle : H ≤ (rotHom n).range
      · right
        exact ⟨H.comap (rotHom n), Subtype.ext (Subgroup.map_comap_eq_self hle)⟩
      · left
        exact Subtype.ext (normal_eq_top_of_odd_not_le_rot hodd hle)
    have hsum : (∑ H : {H : Subgroup (DihedralGroup n) // H.Normal}, Nat.card H.1) =
        2 * n + ∑ d ∈ n.divisors, d := by
      rw [huniv, Finset.sum_insert htop_notMem,
        Finset.sum_image (fun _ _ _ _ h => htoNorm_inj h)]
      have htop_card : Nat.card Htop.1 = 2 * n := by
        change Nat.card (⊤ : Subgroup (DihedralGroup n)) = 2 * n
        rw [Subgroup.card_top, DihedralGroup.nat_card]
      have hrot_sum : (∑ K : Subgroup (Multiplicative (ZMod n)), Nat.card (toNorm K).1) =
          ∑ d ∈ n.divisors, d := by
        have heq : (∑ K : Subgroup (Multiplicative (ZMod n)), Nat.card (toNorm K).1) =
            ∑ K : Subgroup (Multiplicative (ZMod n)), Nat.card K :=
          Finset.sum_congr rfl fun K _ => card_map_rotHom K
        have : IsCyclic (Multiplicative (ZMod n)) := isAddCyclic_additive_iff.mp inferInstance
        rw [heq, sum_subgroup_of_isCyclic]
        simp [ZMod.card]
      rw [htop_card, hrot_sum]
    have hiff : LeinsterGroup.IsLeinster (DihedralGroup n) ↔ Nat.Perfect n := by
      unfold LeinsterGroup.IsLeinster
      rw [hsum, DihedralGroup.card, Nat.perfect_iff_sum_divisors_eq_two_mul (NeZero.pos n)]
      omega
    exact ⟨fun hL => ⟨hiff.mp hL, hodd⟩, fun ⟨hperf, _⟩ => hiff.mpr hperf⟩
  · have heven : Even n := Nat.not_odd_iff_even.mp hodd
    exact ⟨fun hL => (not_isLeinster_of_even heven hL).elim, fun ⟨_, h⟩ => (hodd h).elim⟩
