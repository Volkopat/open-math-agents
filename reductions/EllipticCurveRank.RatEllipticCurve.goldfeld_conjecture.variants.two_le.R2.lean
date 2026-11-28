import FormalConjectures.Wikipedia.EllipticCurveRank
import Mathlib

/-! Pass from squarefree twists to all nonzero indices. For a fixed cutoff K,
the square factors up to K contribute at most K times the squarefree
exceptional count. The remaining square factors have density at most 1/K
by telescoping a bound for the reciprocal squares. -/
open EllipticCurveRank Filter Finset Set
open scoped Topology BigOperators
namespace OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R2

/-- The squarefree exceptional density implied by Smith's Selmer-distribution theorem. -/
def H1 : Prop := ∀ E : RatEllipticCurve, Tendsto
  (fun H : ℕ ↦ ({d ∈ RatEllipticCurve.twistIndexLE H |
    Squarefree d ∧ 2 ≤ E.twistRank d}.ncard : ℝ) / (2 * H)) atTop (𝓝 0)

/-- Changing the twist index by a nonzero square leaves the rational rank unchanged. -/
def H2 : Prop := ∀ (E : RatEllipticCurve) (a : ℤ) (b : ℕ), a ≠ 0 → 0 < b →
  E.twistRank ((b : ℤ)^2 * a) = E.twistRank a

theorem signed_squarefree {d : ℤ} (hd : d ≠ 0) :
    ∃ (a : ℤ) (b : ℕ), a ≠ 0 ∧ 0 < b ∧ (b : ℤ)^2*a=d ∧ Squarefree a := by
  obtain ⟨a,b,ha,hb,hex,hs⟩ := Nat.sq_mul_squarefree_of_pos (Int.natAbs_pos.mpr hd)
  have ha' : (a:ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hab : (b:ℤ)^2*(a:ℤ)=(d.natAbs:ℤ) := by exact_mod_cast hex
  rw [Int.natCast_natAbs] at hab
  by_cases h : 0 ≤ d
  · exact ⟨a,b,ha',hb,by simpa [abs_of_nonneg h] using hab,Int.squarefree_natCast.mpr hs⟩
  · refine ⟨-(a:ℤ),b,neg_ne_zero.mpr ha',hb,?_,?_⟩
    · rw [mul_neg, hab, abs_of_neg (lt_of_not_ge h), neg_neg]
    · apply Int.squarefree_natAbs.mp
      simpa using hs

theorem index_finite (H : ℕ) : (RatEllipticCurve.twistIndexLE H).Finite :=
  (Set.finite_Icc (-(H:ℤ)) H).subset (fun _ h ↦ abs_le.mp h.2)

theorem reciprocal_tail {K H : ℕ} (hK : 0 < K) (hKH : K ≤ H) :
    (∑ i ∈ Finset.Ico K H, (1:ℝ) / ((i:ℝ)+1)^2) ≤ 1/(K:ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.Ico K H, (-(1/((i+1:ℕ):ℝ)) - (-(1/(i:ℝ)))) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi0 : (0:ℝ)<(i:ℝ) := by exact_mod_cast hK.trans_le (Finset.mem_Ico.mp hi).1
      push_cast
      calc
        _ ≤ 1 / ((i:ℝ)*((i:ℝ)+1)) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        _ = _ := by field_simp <;> ring
    _ = -(1/(H:ℝ)) - (-(1/(K:ℝ))) :=
      Finset.sum_Ico_sub (fun i : ℕ ↦ -(1/(i:ℝ))) hKH
    _ ≤ _ := by linarith [show (0:ℝ) ≤ 1/(H:ℝ) by positivity]

theorem count_bound (E : RatEllipticCurve) (h : H2) {r K H : ℕ} (hr : 2 ≤ r)
    (hK : 0 < K) (hKH : K ≤ H) :
    ({d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r}.ncard : ℝ) ≤
      (K:ℝ) * ({d ∈ RatEllipticCurve.twistIndexLE H |
        Squarefree d ∧ 2 ≤ E.twistRank d}.ncard : ℝ) + (2*(H:ℝ))*(1/(K:ℝ)) := by
  classical
  let S : Set ℤ := {d ∈ RatEllipticCurve.twistIndexLE H | Squarefree d ∧ 2 ≤ E.twistRank d}
  let small (b : ℕ) : Set ℤ := (fun a : ℤ ↦ (b:ℤ)^2 * a) '' S
  let large (i : ℕ) : Set ℤ := (fun a : ℤ ↦ ((i+1:ℕ):ℤ)^2 * a) ''
    RatEllipticCurve.twistIndexLE (H/(i+1)^2)
  let U : Set ℤ := ⋃ b ∈ (↑(Finset.Icc 1 K) : Set ℕ), small b
  let V : Set ℤ := ⋃ i ∈ (↑(Finset.Ico K H) : Set ℕ), large i
  have fS : S.Finite := (index_finite H).subset (fun _ hS ↦ hS.1)
  have fU : U.Finite := (Finset.Icc 1 K).finite_toSet.biUnion (fun b _ ↦ fS.image _)
  have fV : V.Finite := (Finset.Ico K H).finite_toSet.biUnion (fun i _ ↦ (index_finite _).image _)
  have cover : {d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r} ⊆ U ∪ V := by
    intro d hd
    obtain ⟨a,b,ha,hb,hab,hs⟩ := signed_squarefree hd.1.1
    have dabs : d.natAbs ≤ H := by
      have bd := hd.1.2
      rw [← Int.natCast_natAbs] at bd
      exact_mod_cast bd
    have eqAbs : d.natAbs = b^2 * a.natAbs := by
      rw [← hab, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    rw [eqAbs] at dabs
    have ha0 : 0 < a.natAbs := Int.natAbs_pos.mpr ha
    have hb0 : 0 < b^2 := pow_pos hb _
    have aH : a.natAbs ≤ H := (Nat.le_mul_of_pos_left _ hb0).trans dabs
    have bH : b ≤ H := (Nat.le_self_pow (by decide : 2 ≠ 0) b).trans
      ((Nat.le_mul_of_pos_right _ ha0).trans dabs)
    by_cases hbk : b ≤ K
    · left
      refine Set.mem_iUnion.mpr ⟨b,Set.mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hb,hbk⟩,a,?_,hab⟩⟩
      refine ⟨⟨ha,?_⟩,hs,?_⟩
      · rw [← Int.natCast_natAbs]
        exact_mod_cast aH
      · rw [← h E a b ha hb, hab, hd.2]
        exact hr
    · right
      have his : b-1+1=b := by omega
      refine Set.mem_iUnion.mpr ⟨b-1,Set.mem_iUnion.mpr
        ⟨Finset.mem_Ico.mpr ⟨by omega,by omega⟩,a,?_,by simpa only [his] using hab⟩⟩
      refine ⟨ha,?_⟩
      rw [his, ← Int.natCast_natAbs]
      exact_mod_cast (Nat.le_div_iff_mul_le hb0).mpr (by simpa [Nat.mul_comm] using dabs)
  have smallBound : U.ncard ≤ K*S.ncard := by
    calc
      _ ≤ ∑ b ∈ Finset.Icc 1 K, (small b).ncard := (Finset.Icc 1 K).set_ncard_biUnion_le small
      _ ≤ ∑ _b ∈ Finset.Icc 1 K, S.ncard := Finset.sum_le_sum (fun b _ ↦ Set.ncard_image_le fS)
      _ = _ := by simp
  have largeBound : (V.ncard : ℝ) ≤ (2*(H:ℝ))*(1/(K:ℝ)) := by
    calc
      _ ≤ ∑ i ∈ Finset.Ico K H, ((large i).ncard : ℝ) := by
        exact_mod_cast (Finset.Ico K H).set_ncard_biUnion_le large
      _ ≤ ∑ i ∈ Finset.Ico K H, (2*(H:ℝ)) * ((1:ℝ)/((i:ℝ)+1)^2) := by
        apply Finset.sum_le_sum
        intro i hi
        have bd : (large i).ncard ≤ 2*(H/(i+1)^2) :=
          (Set.ncard_image_le (index_finite _)).trans_eq (RatEllipticCurve.ncard_twistIndexLE _)
        have divBound : ((H/(i+1)^2:ℕ):ℝ) ≤ (H:ℝ)/((i:ℝ)+1)^2 := by
          apply (le_div_iff₀ (by positivity)).mpr
          have v := Nat.div_mul_le_self H ((i+1)^2)
          push_cast
          exact_mod_cast v
        have hb : ((large i).ncard:ℝ) ≤ 2*((H/(i+1)^2:ℕ):ℝ) := by exact_mod_cast bd
        calc
          _ ≤ 2 * ((H/(i+1)^2:ℕ):ℝ) := hb
          _ ≤ 2 * ((H:ℝ)/((i:ℝ)+1)^2) := mul_le_mul_of_nonneg_left divBound (by norm_num)
          _ = _ := by ring
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (reciprocal_tail hK hKH) (by positivity)
  have hcard := (Set.ncard_le_ncard cover (fU.union fV)).trans (Set.ncard_union_le U V)
  have hcast : ({d ∈ RatEllipticCurve.twistIndexLE H | E.twistRank d = r}.ncard:ℝ) ≤
      (U.ncard:ℝ)+(V.ncard:ℝ) := by exact_mod_cast hcard
  have hcastSmall : (U.ncard:ℝ) ≤ (K:ℝ)*(S.ncard:ℝ) := by exact_mod_cast smallBound
  exact hcast.trans (add_le_add hcastSmall largeBound)

theorem main : H1 → H2 →
    type_of% @EllipticCurveRank.RatEllipticCurve.goldfeld_conjecture.variants.two_le := by
  intro hz hi E r hr
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun H ↦ lt_of_lt_of_le ha (by positivity))
  · intro a ha
    obtain ⟨K,hK⟩ := exists_nat_gt (2/a)
    have hKpos : 0 < K := by
      have h : (0:ℝ)<(K:ℝ) := (show 0 < 2/a by positivity).trans hK
      exact_mod_cast h
    have hm : 1/(K:ℝ) < a/2 := by
      apply (div_lt_iff₀ (by exact_mod_cast hKpos)).mpr
      have h := (div_lt_iff₀ ha).mp hK
      nlinarith
    have hs := (hz E).const_mul (K:ℝ)
    rw [mul_zero] at hs
    have ht := (tendsto_order.mp hs).2 (a/2) (by positivity)
    filter_upwards [ht,eventually_ge_atTop K] with H hH hKH
    have Hpos : (0:ℝ)<(H:ℝ) := by exact_mod_cast hKpos.trans_le hKH
    have hpos : (0:ℝ)<2*(H:ℝ) := by positivity
    rw [RatEllipticCurve.ncard_twistIndexLE]
    push_cast
    calc
      _ ≤ ((K:ℝ) * ({d ∈ RatEllipticCurve.twistIndexLE H |
          Squarefree d ∧ 2 ≤ E.twistRank d}.ncard : ℝ) + (2*(H:ℝ))*(1/(K:ℝ))) /
          (2*(H:ℝ)) := div_le_div_of_nonneg_right (count_bound E hi hr hKpos hKH) hpos.le
      _ = (K:ℝ) * (({d ∈ RatEllipticCurve.twistIndexLE H |
          Squarefree d ∧ 2 ≤ E.twistRank d}.ncard : ℝ) / (2*(H:ℝ))) + 1/(K:ℝ) := by
        field_simp [hpos.ne']
      _ < a := by linarith [hH,hm]

end OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R2
