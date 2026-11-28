import FormalConjectures.ErdosProblems.«591»
import Mathlib

/-!
# Erdős 591: separate local extraction from global fiber selection

The positive Schipperus--Darby argument has two independent combinatorial parts.
First, inside a sufficiently large finite rank block one extracts a smaller red block.
Second, a global height-two construction supplies infinitely many such blocks with no
blue edges between distinct blocks.  Once these are available, the union of the extracted
red pieces is cofinal in `ω ^ (ω ^ 2)`, and the endpoint partition relation follows by
ordinal arithmetic.  This file isolates exactly those two pieces.

The hypotheses are stated for the canonical realization in `Ordinal.{0}`.  The reduction
includes the universe transfer needed to apply them to the universe-polymorphic host type
in the catalogue statement.
-/

open Cardinal Ordinal Set Function Order

universe u

namespace OMA.R_Erdos591_erdos_591_R1


/-- Local extraction: a triangle-free blue graph on a block of order type at least
`(ω^ω)^((n+1)*2)` contains a red block of exact type `(ω^ω)^(n+1)`. -/
def H1 : Prop :=
  ∀ n : ℕ, ∀ blue : SimpleGraph ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType),
    blue.CliqueFree 3 →
    ∀ S : Set ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType),
      ((ω ^ ω : Ordinal.{0}) ^ ((n + 1) * 2)) ≤ typeLT S →
      ∃ T : Set ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType),
        T ⊆ S ∧ blueᶜ.IsClique T ∧
          typeLT T = (ω ^ ω : Ordinal.{0}) ^ (n + 1)

/-- Global fiber selection: a triangle-free blue graph admits arbitrarily large finite-rank
fibers with no blue edges between distinct fibers. -/
def H2 : Prop :=
  ∀ blue : SimpleGraph ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType),
    blue.CliqueFree 3 →
    ∃ S : ℕ → Set ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType),
      (∀ n : ℕ, ((ω ^ ω : Ordinal.{0}) ^ ((n + 1) * 2)) ≤ typeLT (S n)) ∧
      ∀ i j : ℕ, i ≠ j →
        ∀ x ∈ S i, ∀ y ∈ S j, ¬ blue.Adj x y

theorem thetaOmega_eq0 : (ω ^ ω : Ordinal.{0}) ^ ω = ω ^ (ω ^ 2) := by
  rw [← Ordinal.opow_mul]
  congr 1
  rw [pow_two]

theorem iSup_opow_lift_Iio (a b : Ordinal.{0}) :
    (⨆ x : Iio b, (lift.{u,0} a) ^ (lift.{u,0} x.1)) =
      ⨆ y : Iio (lift.{u,0} b), (lift.{u,0} a) ^ y.1 := by
  let e : Iio b ≃ Iio (lift.{u,0} b) :=
    { toFun x := ⟨lift.{u,0} x.1, (Ordinal.lift_lt).2 x.2⟩
      invFun y :=
        let x := Classical.choose (mem_range_lift_of_le y.2.le)
        ⟨x, by
          have hx : lift.{u,0} x = y.1 := Classical.choose_spec (mem_range_lift_of_le y.2.le)
          have hlt : lift.{u,0} x < lift.{u,0} b := hx ▸ y.2
          exact (Ordinal.lift_lt).1 hlt⟩
      left_inv x := by
        apply Subtype.ext
        apply (Ordinal.lift_inj).1
        dsimp
        exact Classical.choose_spec (mem_range_lift_of_le (b := lift.{u,0} x.1) (a := b) ((Ordinal.lift_lt).2 x.2).le)
      right_inv y := by
        apply Subtype.ext
        dsimp
        exact Classical.choose_spec (mem_range_lift_of_le y.2.le) }
  exact e.iSup_comp (g := fun y => (lift.{u,0} a) ^ y.1)

theorem lift_opow_of_ne_zero (a b : Ordinal.{0}) (ha : a ≠ 0) :
    lift.{u,0} (a ^ b) = (lift.{u,0} a) ^ (lift.{u,0} b) := by
  induction b using limitRecOn with
  | zero => simp
  | add_one b ih =>
      rw [opow_add_one, Ordinal.lift_mul, ih, Ordinal.lift_add_one, ← opow_add_one]
  | limit b hb ih =>
      have hlb : IsSuccLimit (lift.{u,0} b) := (isSuccLimit_lift).2 hb
      have hla : lift.{u,0} a ≠ 0 := by
        intro h
        apply ha
        rw [← (Ordinal.lift_zero.{0,u} : lift.{u,0} (0 : Ordinal.{0}) = (0 : Ordinal.{u}))] at h
        exact (Ordinal.lift_inj).1 h
      haveI : Nonempty (Iio b) := ⟨⟨(0 : Ordinal.{0}), hb.pos⟩⟩
      calc
        lift.{u,0} (a ^ b) = lift.{u,0} (⨆ x : Iio b, a ^ x.1) := by
          rw [opow_limit ha hb]
        _ = ⨆ x : Iio b, lift.{u,0} (a ^ x.1) := by
          simpa using (Ordinal.liftInitialSeg.{u,0}.isNormal.map_iSup (g := fun x : Iio b => a ^ x.1) bddAbove_of_small)
        _ = ⨆ x : Iio b, (lift.{u,0} a) ^ (lift.{u,0} x.1) := by
          apply iSup_congr
          intro x
          exact ih x.1 x.2
        _ = ⨆ y : Iio (lift.{u,0} b), (lift.{u,0} a) ^ y.1 := by
          exact iSup_opow_lift_Iio a b
        _ = (lift.{u,0} a) ^ (lift.{u,0} b) := by
          rw [opow_limit hla hlb]

theorem lift_omega_pow_omega_sq :
    lift.{u,0} ((ω ^ (ω ^ 2) : Ordinal.{0})) = (ω ^ (ω ^ 2) : Ordinal.{u}) := by
  have h2 : lift.{u,0} ((ω ^ 2 : Ordinal.{0})) = (ω ^ 2 : Ordinal.{u}) := by
    rw [pow_two, pow_two, Ordinal.lift_mul, Ordinal.lift_omega0]
  rw [lift_opow_of_ne_zero (ω : Ordinal.{0}) ((ω ^ 2 : Ordinal.{0})) Ordinal.omega0_ne_zero]
  rw [h2]
  simp

theorem hostRelIso :
    Nonempty (((· < ·) : ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType) → ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType) → Prop) ≃r ((· < ·) : ((ω ^ (ω ^ 2) : Ordinal.{u}).ToType) → ((ω ^ (ω ^ 2) : Ordinal.{u}).ToType) → Prop)) := by
  have h0 : lift.{u,0} (typeLT ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType)) = typeLT (((ω ^ (ω ^ 2) : Ordinal.{u}).ToType)) := by
    rw [Ordinal.type_toType, Ordinal.type_toType]
    exact lift_omega_pow_omega_sq
  have hid : lift.{0,u} (typeLT (((ω ^ (ω ^ 2) : Ordinal.{u}).ToType))) = typeLT (((ω ^ (ω ^ 2) : Ordinal.{u}).ToType)) := Ordinal.lift_uzero _
  rw [← hid] at h0
  exact (Ordinal.lift_type_eq.{0,u,0}).1 h0

theorem assembled0 (hlocal : H1) (hfiber : H2) (blue : SimpleGraph ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType)) :
    (∃ s, blueᶜ.IsClique s ∧ typeLT s = (ω ^ (ω ^ 2) : Ordinal.{0})) ∨
      ∃ s, blue.IsClique s ∧ #s = (3 : Cardinal.{0}) := by
  by_cases hfree : blue.CliqueFree 3
  · obtain ⟨F, hlarge, hcross⟩ := hfiber blue hfree
    have hpieces (n : ℕ) :
        ∃ T : Set ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType),
          T ⊆ F n ∧ blueᶜ.IsClique T ∧
            typeLT T = (ω ^ ω : Ordinal.{0}) ^ (n + 1) :=
      hlocal n blue hfree (F n) (hlarge n)
    choose T hsub hclique htype using hpieces
    let U : Set ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType) := ⋃ n, T n
    refine Or.inl ⟨U, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
      by_cases hij : i = j
      · subst j
        exact hclique i hi hj hxy
      · apply (blue.compl_adj x y).mpr
        exact ⟨hxy, hcross i j hij x (hsub i hi) y (hsub j hj)⟩
    · apply le_antisymm
      · exact (Ordinal.type_set_le U).trans_eq
          (Ordinal.type_toType ((ω ^ (ω ^ 2) : Ordinal.{0})))
      · have hcof : ((ω ^ ω : Ordinal.{0}) ^ ω) ≤ typeLT U := by
          rw [← Ordinal.iSup_pow_natCast (Ordinal.opow_pos _ Ordinal.omega0_pos)]
          apply Ordinal.iSup_le
          intro n
          have hn : typeLT (T n) ≤ typeLT U :=
            Ordinal.type_mono (Set.subset_iUnion T n)
          rw [htype n] at hn
          calc
            (ω ^ ω : Ordinal.{0}) ^ n ≤ (ω ^ ω) ^ n * (ω ^ ω) :=
              Ordinal.le_mul_left _ (Ordinal.opow_pos _ Ordinal.omega0_pos)
            _ = (ω ^ ω : Ordinal.{0}) ^ (n + 1) := (pow_succ _ _).symm
            _ ≤ typeLT U := hn
        simpa [thetaOmega_eq0] using hcof
  · obtain ⟨s, hs⟩ := not_forall.mp hfree
    have hclique : blue.IsNClique 3 s := not_not.mp hs
    refine Or.inr ⟨(s : Set ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType)), hclique.isClique, ?_⟩
    simp only [Finset.coe_sort_coe, Cardinal.mk_coe_finset, hclique.card_eq, Nat.cast_ofNat]

theorem main : H1 → H2 → type_of% @Erdos591.erdos_591 := by
  intro h1 h2 red blue hcompl
  obtain ⟨e⟩ := hostRelIso
  let blue0 : SimpleGraph ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType) := blue.comap e
  rcases assembled0 h1 h2 blue0 with ⟨s, hscl, hstype⟩ | ⟨s, hscl, hscard⟩
  · let t : Set _ := e '' s
    refine Or.inl ⟨t, ?_, ?_⟩
    · rw [hcompl.eq_compl]
      rintro x ⟨x0, hx0, rfl⟩ y ⟨y0, hy0, rfl⟩ hxy
      have hne0 : x0 ≠ y0 := fun h => hxy (congrArg e h)
      have hc := hscl hx0 hy0 hne0
      exact ⟨hxy, hc.2⟩
    · let er : ((· < ·) : s → s → Prop) ≃r ((· < ·) : t → t → Prop) :=
        ⟨Equiv.Set.image e.toEquiv s e.injective, by
          intro x y
          exact e.map_rel_iff⟩
      have ht := er.ordinal_lift_type_eq
      rw [hstype, lift_omega_pow_omega_sq, Ordinal.lift_uzero] at ht
      exact ht.symm
  · let t : Set _ := e '' s
    refine Or.inr ⟨t, ?_, ?_⟩
    · rintro x ⟨x0, hx0, rfl⟩ y ⟨y0, hy0, rfl⟩ hxy
      have hne0 : x0 ≠ y0 := fun h => hxy (congrArg e h)
      exact hscl hx0 hy0 hne0
    · have hc := Cardinal.mk_image_eq_lift (fun x : ((ω ^ (ω ^ 2) : Ordinal.{0}).ToType) => e x) s e.injective
      simpa [hscard] using hc

end OMA.R_Erdos591_erdos_591_R1