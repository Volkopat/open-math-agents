import FormalConjectures.Paper.CasasAlvero

/-!
Translate every root by the centroid, which is itself a root. For a multiset
of centered roots s, the coefficient of order i about z is the coefficient
of X^i in the product of X + (z - r) over r in s, with multiplicities.
Testing at zero first discards every order outside the support of the
centered polynomial. The first step concerns configurations with at least
two distinct nonzero locations. The second handles the remaining split
polynomials by their vanishing next-to-leading coefficient.
-/

namespace OMA.R_CasasAlvero_casas_alvero_conjecture_R1

open Polynomial CasasAlvero

/-- Find a supported, nonleading order whose translated coefficients never vanish
at the nonzero root locations of this centered configuration. -/
def H1 : Prop := ∀ {K : Type} [Field K] [CharZero K] (s : Multiset K),
    s.sum = 0 → 0 ∈ s →
    (∃ a ∈ s, ∃ b ∈ s, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b) →
    ∃ i < s.card, ((s.map (fun r => X - C r)).prod : K[X]).coeff i ≠ 0 ∧
      ∀ z ∈ s, z ≠ 0 → ((s.map (fun r => X + C (z - r))).prod : K[X]).coeff i ≠ 0

/-- A monic split polynomial with next coefficient zero and at most one
nonzero root location must be a power of X. -/
def H2 : Prop := ∀ {K : Type} [Field K] [CharZero K] (Q : K[X]),
    Q.Monic → Q.Splits → Q.nextCoeff = 0 →
    (∀ a ∈ Q.roots, ∀ b ∈ Q.roots, a ≠ 0 → b ≠ 0 → a = b) →
    Q = X ^ Q.natDegree

variable {K : Type*} [Field K] {P : K[X]}

theorem penultimate_hasse (hm : P.Monic) {k : ℕ} (hd : P.natDegree = k + 1) :
    P.hasseDeriv k = C (↑(k + 1) : K) * X + C P.nextCoeff := by
  have hlin : (P.hasseDeriv k).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le P k).trans (by omega)
  have hc : P.coeff (k + 1) = 1 := hd ▸ hm.coeff_natDegree
  rw [eq_X_add_C_of_natDegree_le_one hlin]
  simp only [hasseDeriv_coeff, Nat.add_comm 1 k, Nat.choose_succ_self_right, hc,
    mul_one, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  rw [nextCoeff_of_natDegree_pos (by omega), hd, Nat.add_sub_cancel]


theorem translate_product (s : Multiset K) (z : K) :
    taylor z (s.map (fun r => X - C r)).prod =
      (s.map (fun r => X + C (z - r))).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, taylor_mul, ih,
      map_sub, taylor_X, taylor_C]
    ring

theorem small_field (hcfg : H1) (hsingle : H2) {K : Type} [Field K] [CharZero K]
    (P : K[X]) (hm : P.Monic) (hca : HasCasasAlveroProp P) :
    ∃ c : K, P = (X - C c) ^ P.natDegree := by
  classical
  by_cases hzero : P.natDegree = 0
  · exact ⟨0, by simp [hm.natDegree_eq_zero.mp hzero]⟩
  let L := AlgebraicClosure K
  let f := algebraMap K L
  let A := P.map f
  let c : K := -P.nextCoeff / P.natDegree
  let u := f c
  let Q := taylor u A
  have hA : A.Monic := hm.map _
  have hdeg : A.natDegree = P.natDegree := natDegree_map _
  have hQdeg : Q.natDegree = P.natDegree := (natDegree_taylor _ _).trans hdeg
  have hQ : Q.Monic := by simpa [Q, Monic] using hA
  have hroots : HasCasasAlveroPropᵣ A :=
    hasCasasAlveroProp_iffᵣ.mp (HasCasasAlveroProp.map_iff.mpr hca)
  have hk : A.natDegree = (A.natDegree - 1) + 1 := by omega
  have hlin := penultimate_hasse hA hk
  rw [← hk] at hlin
  have hu : u = -A.nextCoeff / A.natDegree := by
    simp [u, c, A, nextCoeff_map f.injective, f]
  have hdegNZ : (A.natDegree : L) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have base_value (v : L) : (A.hasseDeriv (A.natDegree - 1)).eval v = 0 ↔ v = u := by
    rw [hlin, hu, eq_div_iff hdegNZ]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    constructor <;> intro he <;> linear_combination he
  obtain ⟨v, hv, hvd⟩ := hroots (A.natDegree - 1) (Finset.mem_range.mpr (by omega))
  have hAu : A.IsRoot u := (base_value v |>.mp hvd) ▸ hv
  have hQc : Q.nextCoeff = 0 := by
    rw [nextCoeff_of_natDegree_pos (by omega), hQdeg, ← hdeg]
    simpa only [Q, taylor_coeff] using (base_value u).mpr rfl
  have hQ0 : Q.IsRoot 0 := by simpa [IsRoot, Q, taylor_eval] using hAu
  have hs := IsAlgClosed.splits Q
  have hprod := hs.eq_prod_roots_of_monic hQ
  have hpure : Q = X ^ Q.natDegree := by
    apply hsingle Q hQ hs hQc
    intro a ha b hb ha0 hb0
    by_contra hab
    have hsum : Q.roots.sum = 0 := by
      simpa [hs.nextCoeff_eq_neg_sum_roots_of_monic hQ] using hQc
    obtain ⟨i, hi, hi0, wall⟩ := hcfg Q.roots hsum ((mem_roots hQ.ne_zero).mpr hQ0)
      ⟨a, ha, b, hb, ha0, hb0, hab⟩
    rw [← hs.natDegree_eq_card_roots, hQdeg, ← hdeg] at hi
    obtain ⟨y, hy, hyd⟩ := hroots i (Finset.mem_range.mpr hi)
    let z := y - u
    have hzu : z + u = y := sub_add_cancel _ _
    have hz : Q.IsRoot z := by simpa [Q, IsRoot, taylor_eval, hzu] using hy
    have hshift : (taylor z Q).coeff i = 0 := by
      simpa only [Q, taylor_taylor, hzu, taylor_coeff, IsRoot] using hyd
    by_cases hz0 : z = 0
    · rw [hz0, taylor_zero, hprod] at hshift
      exact hi0 hshift
    · have hzmem := (mem_roots hQ.ne_zero).mpr hz
      rw [hprod, translate_product] at hshift
      exact wall z hzmem hz0 hshift
  refine ⟨c, map_injective f f.injective ?_⟩
  change A = _
  rw [Polynomial.map_pow, Polynomial.map_sub, map_X, map_C]
  change A = (X - C u) ^ P.natDegree
  apply (taylor_injective u)
  change taylor u A = taylor u ((X - C u) ^ P.natDegree)
  rw [taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  exact hQdeg ▸ hpure

theorem main : H1 → H2 → type_of% @CasasAlvero.casas_alvero_conjecture := by
  intro hcfg hsingle K _ _ P hm hca
  classical
  let S := Subfield.closure (Set.range P.coeff)
  have : Countable (Set.range P.coeff) := (Set.countable_range _).to_subtype
  have : Countable S := Cardinal.mk_le_aleph0_iff.mp <|
    (Subfield.cardinalMk_closure_le_max _).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  let k := Shrink.{0} S
  let e := Shrink.ringEquiv.{0} S
  let f : k →+* K := S.subtype.comp e.toRingHom
  have : CharZero k := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have hlift : P ∈ lifts f := by
    apply (lifts_iff_coeff_lifts P).mpr
    intro i
    let c : S := ⟨P.coeff i, Subfield.subset_closure ⟨i, rfl⟩⟩
    exact ⟨e.symm c, by simp [f, c]⟩
  obtain ⟨B, hB⟩ := (mem_lifts _).mp hlift
  obtain ⟨a, ha⟩ := small_field hcfg hsingle B (monic_map_iff.mp (hB ▸ hm))
    (HasCasasAlveroProp.map_iff.mp (hB ▸ hca))
  refine ⟨f a, ?_⟩
  simpa only [← hB, natDegree_map, Polynomial.map_pow, Polynomial.map_sub,
    map_X, map_C] using congrArg (Polynomial.map f) ha

end OMA.R_CasasAlvero_casas_alvero_conjecture_R1
