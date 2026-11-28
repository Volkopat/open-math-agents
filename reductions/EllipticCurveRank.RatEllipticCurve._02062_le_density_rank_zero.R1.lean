import FormalConjectures.Wikipedia.EllipticCurveRank
import Mathlib

/-! Finite counting argument for Theorem 5 of Bhargava and Shankar,
arXiv:1312.7859. The pointwise inequality and slack constants follow the
suggestion of @MechaNuggan. The two remaining inputs concern the selected
Selmer family and divisibility of a finitely generated group, respectively. -/

open EllipticCurveRank EllipticCurveRank.RatEllipticCurve Finset Filter

namespace OMA.R_EllipticCurveRank_RatEllipticCurve__02062_le_density_rank_zero_R1

def H1 : Prop := ∀ᶠ H : ℕ in atTop,
  ∃ (U F : Finset RatEllipticCurve) (s : RatEllipticCurve → ℕ),
    (U : Set RatEllipticCurve) = heightLE H ∧ U.Nonempty ∧ F ⊆ U ∧
    54999 * U.card ≤ 100000 * F.card ∧
    49999 * F.card ≤ 100000 * (F.filter fun E => Even (s E)).card ∧
    100000 * (∑ E ∈ F, 5 ^ s E) ≤ 600001 * F.card ∧
    ∀ E ∈ F, s E = 0 → Function.Surjective (fun P : E.toWeierstrass.Point => 5 • P)

def H2 : Prop := ∀ E : RatEllipticCurve,
  Function.Surjective (fun P : E.toWeierstrass.Point => 5 • P) → E.rank = 0

lemma weight (k : ℕ) :
    5 + (if Even k then 20 else 0) ≤ 5^k + (if k=0 then 24 else 0) := by
  rcases k with _ | k
  · decide
  rcases k with _ | k
  · decide
  have h := Nat.pow_le_pow_right (by decide : 0 < 5) (show 2 ≤ k+2 by omega)
  change 5 + (if Even (k+2) then 20 else 0) ≤ 5^(k+2) + (if k+2=0 then 24 else 0)
  rw [if_neg (by omega : k+2 ≠ 0), add_zero]
  split <;> omega

lemma tally {α : Type*} (F : Finset α) (s : α → ℕ) :
    5*F.card + 20*(F.filter fun E => Even (s E)).card ≤
      (∑ E ∈ F, 5^s E) + 24*(F.filter fun E => s E=0).card := by
  have h := Finset.sum_le_sum (s := F) (fun E _ => weight (s E))
  simpa [Finset.sum_add_distrib, ← Finset.sum_filter, Nat.mul_comm] using h

theorem main : H1 → H2 → type_of% @EllipticCurveRank.RatEllipticCurve._02062_le_density_rank_zero := by
  classical
  intro data descend
  have bounds : ∀ᶠ H : ℕ in atTop,
      let d := ({E ∈ heightLE H | E.rank = 0}.ncard / (heightLE H).ncard : ℝ)
      0.2062 ≤ d ∧ d ≤ 1 := by
    filter_upwards [data] with H h
    obtain ⟨U,F,s,hU,hpos,hFU,hsize,heven,hmoment,hfive⟩ := h
    let Z := F.filter fun E => s E=0
    let R := {E ∈ heightLE H | E.rank=0}
    have hsub : (Z : Set RatEllipticCurve) ⊆ R := by
      intro E hE
      obtain ⟨hf,hz⟩ := mem_filter.mp hE
      exact ⟨hU ▸ hFU hf, descend E (hfive E hf hz)⟩
    have hRU : R ⊆ (U : Set RatEllipticCurve) := fun E hE => hU ▸ hE.1
    have rf := U.finite_toSet.subset hRU
    have hZR : Z.card ≤ R.ncard := by simpa using Set.ncard_le_ncard hsub rf
    have hRUc : R.ncard ≤ U.card := by simpa using Set.ncard_le_ncard hRU U.finite_toSet
    have t := tally F s
    change _ ≤ _ + 24*Z.card at t
    have key : 2062*U.card ≤ 10000*R.ncard := by
      linarith only [hsize,heven,hmoment,t,hZR]
    have hu : (0:ℝ) < U.card := by exact_mod_cast card_pos.mpr hpos
    change 0.2062 ≤ (R.ncard:ℝ) / (heightLE H).ncard ∧ (R.ncard:ℝ) / (heightLE H).ncard ≤ 1
    rw [← hU, Set.ncard_coe_finset]
    constructor
    · apply (le_div_iff₀ hu).mpr
      have keyR : (2062:ℝ)*U.card ≤ 10000*R.ncard := by exact_mod_cast key
      linarith
    · apply (div_le_iff₀ hu).mpr
      simpa using (show (R.ncard:ℝ) ≤ U.card by exact_mod_cast hRUc)
  exact le_liminf_of_le (isCoboundedUnder_ge_of_eventually_le atTop (x := 1) (bounds.mono fun _ h => h.2))
    (bounds.mono fun _ h => h.1)

end OMA.R_EllipticCurveRank_RatEllipticCurve__02062_le_density_rank_zero_R1
