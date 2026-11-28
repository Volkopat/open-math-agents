import FormalConjectures.ErdosProblems.«724»
import Mathlib

/-!
# Beth's lower bound for mutually orthogonal Latin squares

We prove the interval sieve needed for the finite-field, direct-product and
truncated transversal-design constructions. The sieve uses a finite
Selberg upper bound, alternating Buchstab inequalities, and a two-dimensional
Mertens bound. At level 63999/15000 an explicit rational profile gives a
positive lower main term. The strict inequality 63999/15000 < 64/15 absorbs
the errors from counting residue classes in intervals. Credits for the
existing construction and Selberg lemmas appear next to their proofs.
-/

section

namespace OMABeth.Buchstab

open Finset

/-- 指定したすべての素数の除外条件を同時に満たす整数 -/
def hits (bad : ℕ → ℕ → Prop) (d : Finset ℕ) (x : ℕ) : Prop :=
  ∀ q ∈ d, bad q x

noncomputable def count (A : Finset ℕ) (pred : ℕ → Prop) : ℝ := by
  classical
  exact ((A.filter pred).card : ℝ)

/- CRTによる1周期の計数と区間端の誤差の2補題は@green-notesによるWilson構成から引用
https://github.com/lefttosolve2/open-math-agents/pull/4718 (96b8ff3ae79468ec26ec864761a0f4c43ca48069)
-/

private lemma card_bad_period (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)]
    (hper : ∀ p y, bad p y ↔ bad p (y % p)) :
    ∀ (d : List ℕ) (A : ℕ), d.Nodup → (∀ p ∈ d, p.Prime) →
      ((Finset.Ico A (A + d.prod)).filter (fun y => ∀ p ∈ d, bad p y)).card =
        (d.map fun p => ((Finset.range p).filter (fun r => bad p r)).card).prod := by
  intro d A hd_nd hd_pr
  have hQ_pos : 0 < d.prod := List.prod_pos fun p hp => (hd_pr p hp).pos
  have h_ico_range : ((Finset.Ico A (A + d.prod)).filter (fun y => ∀ p ∈ d, bad p y)).card =
      ((Finset.range d.prod).filter (fun r => ∀ p ∈ d, bad p r)).card := by
    apply Finset.card_bij (fun y _ => y % d.prod)
    · intro y hy
      rw [Finset.mem_filter, Finset.mem_Ico] at hy
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨Nat.mod_lt y hQ_pos, fun p hp => ?_⟩
      have hpd : p ∣ d.prod := List.dvd_prod hp
      rw [hper p (y % d.prod), Nat.mod_mod_of_dvd y hpd, ← hper p y]
      exact hy.2 p hp
    · intro y₁ hy₁ y₂ hy₂ heq
      rw [Finset.mem_filter, Finset.mem_Ico] at hy₁ hy₂
      wlog hle : y₁ ≤ y₂ generalizing y₁ y₂
      · exact (this y₂ hy₂ y₁ hy₁ heq.symm (le_of_not_ge hle)).symm
      have hdvd : d.prod ∣ y₂ - y₁ := by
        have h1 : y₁ % d.prod = y₂ % d.prod := heq
        have h2 := Nat.div_add_mod y₂ d.prod
        have h3 := Nat.div_add_mod y₁ d.prod
        have hdiv : d.prod * (y₁ / d.prod) ≤ d.prod * (y₂ / d.prod) :=
          Nat.mul_le_mul_left d.prod (Nat.div_le_div_right hle)
        refine ⟨y₂ / d.prod - y₁ / d.prod, ?_⟩
        rw [Nat.mul_sub_left_distrib]
        omega
      by_contra hne
      have hpos_diff : 0 < y₂ - y₁ := by omega
      have hle_Q := Nat.le_of_dvd hpos_diff hdvd
      omega
    · intro r hr
      rw [Finset.mem_filter, Finset.mem_range] at hr
      let k := (A + d.prod - 1 - r) / d.prod
      have hrQ : r < d.prod := hr.1
      let y := r + ((A + d.prod - 1 - r) / d.prod) * d.prod
      have hy_ge : A ≤ y := by
        have hmod : (A + d.prod - 1 - r) / d.prod * d.prod + (A + d.prod - 1 - r) % d.prod = A + d.prod - 1 - r :=
          Nat.div_add_mod' _ _
        have hlt : (A + d.prod - 1 - r) % d.prod < d.prod := Nat.mod_lt _ hQ_pos
        dsimp only [y]; omega
      have hy_lt : y < A + d.prod := by
        have hle : (A + d.prod - 1 - r) / d.prod * d.prod ≤ A + d.prod - 1 - r := Nat.div_mul_le_self _ _
        dsimp only [y]; omega
      refine ⟨y, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Ico]
        refine ⟨⟨hy_ge, hy_lt⟩, fun p hp => ?_⟩
        have hpd : p ∣ d.prod := List.dvd_prod hp
        have hym : y % d.prod = r := by
          dsimp only [y]
          rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrQ]
        rw [hper p y, ← Nat.mod_mod_of_dvd y hpd, hym, ← hper p r]
        exact hr.2 p hp
      · dsimp only [y]; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrQ]
  rw [h_ico_range]
  clear h_ico_range hQ_pos
  induction d with
  | nil => simp
  | cons p rest ih =>
    have hp_nd := List.nodup_cons.mp hd_nd
    have hp_pr := hd_pr p List.mem_cons_self
    have hrest_pr : ∀ q ∈ rest, q.Prime := fun q hq => hd_pr q (List.mem_cons_of_mem _ hq)
    have hrest_pos : 0 < rest.prod := List.prod_pos fun q hq => (hrest_pr q hq).pos
    have hcop : Nat.Coprime p rest.prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro q hq
      exact (Nat.coprime_primes hp_pr (hrest_pr q hq)).mpr (fun h => hp_nd.1 (h ▸ hq))
    have hprod_eq : ((Finset.range (p :: rest).prod).filter (fun r => ∀ q ∈ p :: rest, bad q r)).card =
        ((Finset.range p).filter (fun r => bad p r)).card *
        ((Finset.range rest.prod).filter (fun r => ∀ q ∈ rest, bad q r)).card := by
      rw [← Finset.card_product]
      apply Finset.card_bij (fun r _ => (r % p, r % rest.prod))
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_range] at hr
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt r hp_pr.pos, ?_⟩, ⟨Nat.mod_lt r hrest_pos, fun q hq => ?_⟩⟩
        · rw [← hper p r]; exact hr.2 p List.mem_cons_self
        · rw [hper q (r % rest.prod), Nat.mod_mod_of_dvd r (List.dvd_prod hq), ← hper q r]
          exact hr.2 q (List.mem_cons_of_mem _ hq)
      · intro r₁ hr₁ r₂ hr₂ heq
        rw [Finset.mem_filter, Finset.mem_range, List.prod_cons] at hr₁ hr₂
        wlog hle : r₁ ≤ r₂ generalizing r₁ r₂
        · exact (this r₂ hr₂ r₁ hr₁ heq.symm (le_of_not_ge hle)).symm
        have hp_eq : r₁ % p = r₂ % p := congrArg Prod.fst heq
        have hR_eq : r₁ % rest.prod = r₂ % rest.prod := congrArg Prod.snd heq
        have hd_p : p ∣ r₂ - r₁ := by
          have hdiv : p * (r₁ / p) ≤ p * (r₂ / p) := Nat.mul_le_mul_left p (Nat.div_le_div_right hle)
          have := Nat.div_add_mod r₁ p
          have := Nat.div_add_mod r₂ p
          refine ⟨r₂ / p - r₁ / p, ?_⟩
          rw [Nat.mul_sub_left_distrib]; omega
        have hd_R : rest.prod ∣ r₂ - r₁ := by
          have hdiv : rest.prod * (r₁ / rest.prod) ≤ rest.prod * (r₂ / rest.prod) :=
            Nat.mul_le_mul_left rest.prod (Nat.div_le_div_right hle)
          have := Nat.div_add_mod r₁ rest.prod
          have := Nat.div_add_mod r₂ rest.prod
          refine ⟨r₂ / rest.prod - r₁ / rest.prod, ?_⟩
          rw [Nat.mul_sub_left_distrib]; omega
        have hd_both := hcop.mul_dvd_of_dvd_of_dvd hd_p hd_R
        by_contra hne
        have hpos_d : 0 < r₂ - r₁ := by omega
        have := Nat.le_of_dvd hpos_d hd_both
        omega
      · intro ⟨r₁, r₂⟩ hpair
        rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter, Finset.mem_range, Finset.mem_range] at hpair
        obtain ⟨k, hkp, hkR⟩ := Nat.chineseRemainder hcop r₁ r₂
        -- Wait: we only need surjectivity onto Finset.range (p * rest.prod)!
        refine ⟨k % (p * rest.prod), ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_range, List.prod_cons]
          refine ⟨Nat.mod_lt k (mul_pos hp_pr.pos hrest_pos), fun q hq => ?_⟩
          rcases List.mem_cons.mp hq with hqp | hq_rest
          · rw [hqp, hper p (k % (p * rest.prod)), Nat.mod_mod_of_dvd k (dvd_mul_right p rest.prod)]
            have hkm : k % p = r₁ := by
              have : k ≡ r₁ [MOD p] := hkp
              simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.1.1] using this
            rw [hkm]; exact hpair.1.2
          · rw [hper q (k % (p * rest.prod)),
                Nat.mod_mod_of_dvd k (dvd_mul_of_dvd_right (List.dvd_prod hq_rest) p)]
            have hkm : k % rest.prod = r₂ := by
              have : k ≡ r₂ [MOD rest.prod] := hkR
              simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.2.1] using this
            rw [← Nat.mod_mod_of_dvd k (List.dvd_prod hq_rest), hkm, ← hper q r₂]
            exact hpair.2.2 q hq_rest
        · ext
          · rw [Nat.mod_mod_of_dvd k (dvd_mul_right p rest.prod)]
            have : k ≡ r₁ [MOD p] := hkp
            simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.1.1] using this
          · rw [Nat.mod_mod_of_dvd k (dvd_mul_left rest.prod p)]
            have : k ≡ r₂ [MOD rest.prod] := hkR
            simpa [Nat.ModEq, Nat.mod_eq_of_lt hpair.2.1] using this
    rw [hprod_eq, List.map_cons, List.prod_cons, ih hp_nd.2 hrest_pr]

private lemma card_bad_Ico_error (bad : ℕ → ℕ → Prop) [∀ p y, Decidable (bad p y)]
    (hper : ∀ p y, bad p y ↔ bad p (y % p))
    (w : ℕ → ℝ) (e : List ℕ) (he_nd : e.Nodup) (he_pr : ∀ p ∈ e, p.Prime)
    (hle2 : ∀ p ∈ e, ((Finset.range p).filter (fun r => bad p r)).card ≤ 2)
    (hw : ∀ p ∈ e, w p = (((Finset.range p).filter (fun r => bad p r)).card : ℝ) / p)
    (Y0 M : ℕ) :
    |(M : ℝ) * (e.map w).prod -
      (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card : ℝ)| ≤ (2 : ℝ) ^ e.length := by
  let Q := e.prod
  have hQ_pos : 0 < Q := List.prod_pos fun p hp => (he_pr p hp).pos
  let q := M / Q
  let r := M % Q
  have hM_eq : M = q * Q + r := (Nat.div_add_mod' M Q).symm
  have hr_lt : r < Q := Nat.mod_lt M hQ_pos
  let N_full := (e.map fun p => ((Finset.range p).filter (fun x => bad p x)).card).prod
  have hw_eq : (e.map w).prod = (N_full : ℝ) / (Q : ℝ) := by
    clear hM_eq hr_lt hQ_pos
    induction e with
    | nil => simp [N_full, Q]
    | cons p t ih =>
      simp only [List.map_cons, List.prod_cons, N_full, Q] at *
      rw [ih (List.nodup_cons.mp he_nd).2 (fun q hq => he_pr q (List.mem_cons_of_mem _ hq))
          (fun q hq => hle2 q (List.mem_cons_of_mem _ hq)) (fun q hq => hw q (List.mem_cons_of_mem _ hq))]
      rw [hw p List.mem_cons_self]
      push_cast; ring
  have hN_le : N_full ≤ 2 ^ e.length := by
    clear hw_eq hM_eq hr_lt hQ_pos
    induction e with
    | nil => simp [N_full]
    | cons p t ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ', N_full] at *
      exact Nat.mul_le_mul (hle2 p List.mem_cons_self)
        (ih (List.nodup_cons.mp he_nd).2 (fun q hq => he_pr q (List.mem_cons_of_mem _ hq))
          (fun q hq => hle2 q (List.mem_cons_of_mem _ hq)) (fun q hq => hw q (List.mem_cons_of_mem _ hq)))
  have hblock : ∀ A : ℕ, ((Finset.Ico A (A + Q)).filter (fun y => ∀ p ∈ e, bad p y)).card = N_full :=
    fun A => card_bad_period bad hper e A he_nd he_pr
  have hblocks : ∀ m : ℕ,
      ((Finset.Ico Y0 (Y0 + m * Q)).filter (fun y => ∀ p ∈ e, bad p y)).card = m * N_full := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hmQ : (m + 1) * Q = m * Q + Q := Nat.succ_mul m Q
      have hsplit : Finset.Ico Y0 (Y0 + (m + 1) * Q) =
          Finset.Ico Y0 (Y0 + m * Q) ∪ Finset.Ico (Y0 + m * Q) (Y0 + m * Q + Q) := by
        rw [hmQ]; ext x; simp only [Finset.mem_union, Finset.mem_Ico]; constructor <;> intro h <;> omega
      have hdisj : Disjoint (Finset.Ico Y0 (Y0 + m * Q)) (Finset.Ico (Y0 + m * Q) (Y0 + m * Q + Q)) := by
        rw [Finset.disjoint_left]; intro x hx1 hx2; simp only [Finset.mem_Ico] at hx1 hx2; omega
      rw [hsplit, Finset.filter_union,
          Finset.card_union_of_disjoint (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
          ih, hblock (Y0 + m * Q), Nat.add_mul, one_mul]
  have hlow : q * N_full ≤ ((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card := by
    rw [← hblocks q]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro y hy; simp only [Finset.mem_Ico] at hy ⊢; omega
  have hup : ((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card ≤ (q + 1) * N_full := by
    have hqQ : (q + 1) * Q = q * Q + Q := Nat.succ_mul q Q
    rw [← hblocks (q + 1)]
    apply Finset.card_le_card
    apply Finset.filter_subset_filter
    intro y hy; simp only [Finset.mem_Ico] at hy ⊢; rw [hqQ]; omega
  have hMW : (M : ℝ) * (e.map w).prod = (q : ℝ) * N_full + (r : ℝ) / Q * N_full := by
    rw [hw_eq, hM_eq]; push_cast; field_simp
  have hrQ0 : 0 ≤ (r : ℝ) / Q := by positivity
  have hrQ1 : (r : ℝ) / Q ≤ 1 := (div_le_one (by exact_mod_cast hQ_pos)).mpr (by exact_mod_cast hr_lt.le)
  have hN_nn : (0 : ℝ) ≤ N_full := Nat.cast_nonneg _
  have hMW_lo : (q : ℝ) * N_full ≤ (M : ℝ) * (e.map w).prod := by nlinarith
  have hMW_hi : (M : ℝ) * (e.map w).prod ≤ (q : ℝ) * N_full + N_full := by nlinarith
  have hcard_lo : (q : ℝ) * N_full ≤ (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card : ℝ) := by
    exact_mod_cast hlow
  have hcard_hi : (((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card : ℝ) ≤
      (q : ℝ) * N_full + N_full := by
    have : ((Finset.Ico Y0 (Y0 + M)).filter (fun y => ∀ p ∈ e, bad p y)).card ≤ q * N_full + N_full := by
      linarith [hup]
    exact_mod_cast this
  have hN_R : (N_full : ℝ) ≤ (2 : ℝ) ^ e.length := by exact_mod_cast hN_le
  rw [abs_le]
  constructor <;> linarith

/-- pに関して悪い剰余類の数 -/
noncomputable def numResidues (bad : ℕ → ℕ → Prop) (p : ℕ) : ℕ := by
  classical
  exact ((range p).filter (bad p)).card

/-- 有限集合に含まれる全素数に関する合同条件の密度 -/
noncomputable def residueDensity (bad : ℕ → ℕ → Prop) (f : Finset ℕ) : ℝ :=
  ∏ p ∈ f, ((numResidues bad p : ℝ) / p)

/-- 各素数で除く剰余類が高々2個なら、CRTの区間端での誤差は2^{#f}以下になる -/
theorem interval_discrepancy (bad : ℕ → ℕ → Prop) (f : Finset ℕ)
    (hper : ∀ p x, bad p x ↔ bad p (x % p)) (hprime : ∀ p ∈ f, p.Prime)
    (hsize : ∀ p ∈ f, numResidues bad p ≤ 2) (X L : ℕ) :
    |count (Ico X (X + L)) (hits bad f) - L * residueDensity bad f| ≤ (2 : ℝ) ^ f.card := by
  classical
  let ρ : ℕ → ℝ := fun p => (numResidues bad p : ℝ) / p
  have hprod : (f.toList.map ρ).prod = ∏ p ∈ f, ρ p := by
    rw [← List.prod_toFinset ρ f.nodup_toList, Finset.toList_toFinset]
  have h := card_bad_Ico_error bad hper ρ f.toList f.nodup_toList
    (fun p hp => hprime p (Finset.mem_toList.mp hp))
    (fun p hp => hsize p (Finset.mem_toList.mp hp))
    (fun _ _ => rfl) X L
  have hc : count (Ico X (X + L)) (hits bad f) =
      (((Ico X (X + L)).filter (fun x => ∀ p ∈ f, bad p x)).card : ℝ) := by
    unfold count
    apply congrArg (fun d : Finset ℕ => (d.card : ℝ))
    ext x
    simp [hits]
  rw [hc, abs_sub_comm]
  simpa [residueDensity, hprod, ρ] using h

end OMABeth.Buchstab

end

section

namespace OMABeth

open Finset

/-- 上側または下側の篩を与える係数と、使っている法の上限 -/
structure Cert (upper : Bool) (P : Finset ℕ) (D : ℝ) where
  coeff : Finset ℕ → ℝ
  coeff_bound : ∀ d ⊆ P, |coeff d| ≤ (3 : ℝ) ^ d.card
  level : ∀ d ⊆ P, D < (∏ q ∈ d, (q : ℝ)) → coeff d = 0
  bound : ∀ X ⊆ P, if upper then
    (if X = ∅ then (1 : ℝ) else 0) ≤ ∑ d ∈ X.powerset, coeff d
    else (∑ d ∈ X.powerset, coeff d) ≤ if X = ∅ then (1 : ℝ) else 0

namespace Cert

/-- 各素数の局所密度から得られる篩の主項 -/
noncomputable def main {upper P D} (c : Cert upper P D) (w : ℕ → ℝ) : ℝ :=
  ∑ d ∈ P.powerset, c.coeff d * ∏ q ∈ d, w q

/-- pより小さい篩の素数 -/
def below (P : Finset ℕ) (p : ℕ) := P.filter (· < p)

/-- 自明な下界0は任意の水準で使える。 -/
noncomputable def zeroLower (P : Finset ℕ) (D : ℝ) : Cert false P D where
  coeff _ := 0
  coeff_bound _ _ := by simp
  level _ _ _ := rfl
  bound X _ := by by_cases h : X = ∅ <;> simp [h]

@[simp] theorem main_zeroLower (P : Finset ℕ) (D : ℝ) (w : ℕ → ℝ) :
    (zeroLower P D).main w = 0 := by simp [main, zeroLower]


/-- 非空な素数集合を、その最大素数によって重複なく分類する。 -/
private theorem sum_powerset_max (X : Finset ℕ) (f : Finset ℕ → ℝ) :
    ∑ d ∈ X.powerset, f d =
      f ∅ + ∑ p ∈ X, ∑ d ∈ (below X p).powerset, f (insert p d) := by
  classical
  induction X using Finset.induction_on_max with
  | empty => simp
  | insert p X hlt ih =>
    have hp : p ∉ X := fun h => lt_irrefl _ (hlt _ h)
    have hself : below (insert p X) p = X := by
      ext q
      constructor
      · intro h
        obtain ⟨hm, hqp⟩ := mem_filter.mp h
        exact (mem_insert.mp hm).resolve_left (ne_of_lt hqp)
      · intro h
        exact mem_filter.mpr ⟨mem_insert_of_mem h, hlt _ h⟩
    have hprev (q) (hq : q ∈ X) : below (insert p X) q = below X q := by
      ext r
      constructor
      · intro h
        obtain ⟨hm, hr⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨(mem_insert.mp hm).resolve_left (ne_of_lt (hr.trans (hlt q hq))), hr⟩
      · intro h
        obtain ⟨hm, hr⟩ := mem_filter.mp h
        exact mem_filter.mpr ⟨mem_insert_of_mem hm, hr⟩
    rw [Finset.sum_powerset_insert hp, ih, Finset.sum_insert hp, hself]
    have hsum := Finset.sum_congr (s₁ := X) rfl (fun q hq =>
      congrArg (fun S : Finset ℕ => ∑ d ∈ S.powerset, f (insert q d)) (hprev q hq))
    rw [hsum]
    ring

private noncomputable def assemble (g : ℕ → Finset ℕ → ℝ) (d : Finset ℕ) : ℝ :=
  if hd : d.Nonempty then -g (d.max' hd) (d.erase (d.max' hd)) else 1

@[simp] private theorem assemble_empty (g : ℕ → Finset ℕ → ℝ) : assemble g ∅ = 1 := by
  simp [assemble]

private theorem assemble_insert (g : ℕ → Finset ℕ → ℝ) (p : ℕ) (d : Finset ℕ)
    (h : ∀ q ∈ d, q < p) : assemble g (insert p d) = -g p d := by
  have hp : p ∉ d := fun hp => lt_irrefl _ (h _ hp)
  have hm : (insert p d).max' (Finset.insert_nonempty p d) = p := by
    apply le_antisymm
    · apply Finset.max'_le
      intro q hq
      rcases mem_insert.mp hq with rfl | hq
      · rfl
      · exact (h q hq).le
    · exact le_max' _ _ (mem_insert_self _ _)
  simp [assemble, Finset.insert_nonempty, hm, hp]

private theorem assemble_weighted (X : Finset ℕ) (g : ℕ → Finset ℕ → ℝ) (w : ℕ → ℝ) :
    ∑ d ∈ X.powerset, assemble g d * ∏ q ∈ d, w q =
      1 - ∑ p ∈ X, w p * ∑ d ∈ (below X p).powerset, g p d * ∏ q ∈ d, w q := by
  classical
  rw [sum_powerset_max]
  simp only [assemble_empty, prod_empty, mul_one]
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  apply congrArg (1 + ·)
  apply sum_congr rfl
  intro p _
  rw [mul_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro d hd
  have hlt (q) (hq : q ∈ d) : q < p := (mem_filter.mp (mem_powerset.mp hd hq)).2
  rw [assemble_insert g p d hlt, prod_insert (fun hp => lt_irrefl _ (hlt _ hp))]
  ring

private theorem indicator (X : Finset ℕ) :
    (if X = ∅ then (1 : ℝ) else 0) =
      1 - ∑ p ∈ X, if below X p = ∅ then (1 : ℝ) else 0 := by
  classical
  by_cases hx : X.Nonempty
  · let p := X.min' hx
    have hp : p ∈ X := min'_mem X hx
    have hm : below X p = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨hq, hlt⟩ := mem_filter.mp hq
      exact (not_lt_of_ge (min'_le X q hq)) hlt
    rw [if_neg hx.ne_empty, sum_eq_single_of_mem p hp, if_pos hm]
    · norm_num
    · intro q hq hne
      apply if_neg
      intro h
      have hpq : p ∈ below X q := mem_filter.mpr
        ⟨hp, lt_of_le_of_ne (min'_le X q hq) hne.symm⟩
      simp [h] at hpq
  · simp [Finset.not_nonempty_iff_eq_empty.mp hx]



private noncomputable def branchCoeff {upper : Bool} {P : Finset ℕ} {D : ℝ}
    (child : ∀ p ∈ P, Cert (!upper) (below P p) (D / p)) (p : ℕ) (d : Finset ℕ) : ℝ :=
  if hp : p ∈ P then (child p hp).coeff d else 0

private theorem erase_subset_below {d P : Finset ℕ} (hs : d ⊆ P) (hne : d.Nonempty) :
    d.erase (d.max' hne) ⊆ below P (d.max' hne) := by
  intro q hq
  exact mem_filter.mpr ⟨hs (mem_of_mem_erase hq), d.lt_max'_of_mem_erase_max' hne hq⟩

private theorem reverse_sum (upper : Bool) (X : Finset ℕ) (trueValue approx : ℕ → ℝ)
    (h : ∀ p ∈ X, if !upper then trueValue p ≤ approx p else approx p ≤ trueValue p) :
    if upper then (1 - ∑ p ∈ X, trueValue p) ≤ 1 - ∑ p ∈ X, approx p
    else (1 - ∑ p ∈ X, approx p) ≤ 1 - ∑ p ∈ X, trueValue p := by
  cases upper <;> exact sub_le_sub_left (sum_le_sum h) 1

/-- 各pの枝で反対側の篩を使って係数を合成する。非空なdの最大素数が枝を一意に決める。 -/
noncomputable def buchstab {upper : Bool} {P : Finset ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hpos : ∀ p ∈ P, 0 < p) (child : ∀ p ∈ P, Cert (!upper) (below P p) (D / p)) :
    Cert upper P D where
  coeff := assemble (branchCoeff child)
  coeff_bound d hd := by
    by_cases hne : d.Nonempty
    · let p := d.max' hne
      have hp : p ∈ P := hd (d.max'_mem hne)
      rw [assemble, dif_pos hne, abs_neg, branchCoeff, dif_pos hp]
      exact ((child p hp).coeff_bound _ (erase_subset_below hd hne)).trans
        (pow_le_pow_right₀ (by norm_num) Finset.card_erase_le)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hne]
  level d hd hlevel := by
    by_cases hne : d.Nonempty
    · let p := d.max' hne
      have hp : p ∈ P := hd (d.max'_mem hne)
      have hp' : p ∈ d := d.max'_mem hne
      have hlt : D / p < (∏ q ∈ d.erase p, (q : ℝ)) := by
        apply (div_lt_iff₀ (Nat.cast_pos.mpr (hpos p hp))).mpr
        rw [mul_comm, Finset.mul_prod_erase _ _ hp']
        exact hlevel
      rw [assemble, dif_pos hne, branchCoeff, dif_pos hp,
        (child p hp).level _ (erase_subset_below hd hne) hlt, neg_zero]
    · have h : d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      simp [h] at hlevel
      exact (not_lt_of_ge hD hlevel).elim
  bound X hX := by
    have h := assemble_weighted X (branchCoeff child) (fun _ => 1)
    simp only [prod_const_one, mul_one, one_mul] at h
    rw [h, indicator X]
    apply reverse_sum
    intro p hp
    have hsub : below X p ⊆ below P p := by
      intro q hq
      exact mem_filter.mpr ⟨hX (mem_filter.mp hq).1, (mem_filter.mp hq).2⟩
    simpa only [branchCoeff, dif_pos (hX hp)] using (child p (hX hp)).bound (below X p) hsub

/-- 子の主項を密度w(p)で重み付けした和が、合成した篩の主項を与える。 -/
theorem main_buchstab {upper : Bool} {P : Finset ℕ} {D : ℝ} (hD : 1 ≤ D)
    (hpos : ∀ p ∈ P, 0 < p) (child : ∀ p ∈ P, Cert (!upper) (below P p) (D / p))
    (w : ℕ → ℝ) :
    (buchstab hD hpos child).main w =
      1 - ∑ p ∈ P.attach, w p.val * (child p.val p.property).main w := by
  change ∑ d ∈ P.powerset, assemble (branchCoeff child) d * ∏ q ∈ d, w q = _
  rw [assemble_weighted, ← Finset.sum_attach P]
  apply congrArg (1 - ·)
  apply sum_congr rfl
  intro p _
  simp [branchCoeff, p.property, main]


end Cert
end OMABeth

end

section

/- 有限篩の係数をCRTで区間上の整数個数に移し、全ての法の誤差をまとめる。 -/

namespace OMABeth.Cert

open Finset Buchstab

/-- xが満たす除外条件の素数集合 -/
private noncomputable def badSet (P : Finset ℕ) (bad : ℕ → ℕ → Prop) (x : ℕ) : Finset ℕ := by
  classical
  exact P.filter (fun p => bad p x)

private theorem badSet_empty (P : Finset ℕ) (bad : ℕ → ℕ → Prop) (x : ℕ) :
    badSet P bad x = ∅ ↔ ∀ p ∈ P, ¬ bad p x := by
  classical
  simp [badSet, filter_eq_empty_iff]

private theorem polynomial_sum (A P : Finset ℕ) (bad : ℕ → ℕ → Prop) (f : Finset ℕ → ℝ) :
    ∑ x ∈ A, ∑ d ∈ (badSet P bad x).powerset, f d =
      ∑ d ∈ P.powerset, f d * count A (hits bad d) := by
  classical
  have extract (x) :
      ∑ d ∈ (badSet P bad x).powerset, f d =
        ∑ d ∈ P.powerset, if hits bad d x then f d else 0 := by
    rw [← sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [mem_powerset, mem_filter]
    constructor
    · intro h
      exact ⟨fun q hq => (mem_filter.mp (h hq)).1,
        fun q hq => (mem_filter.mp (h hq)).2⟩
    · rintro ⟨hs, hb⟩ q hq
      exact mem_filter.mpr ⟨hs hq, hb q hq⟩
  simp_rw [extract]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [← sum_filter]
  simp [Buchstab.count, nsmul_eq_mul, mul_comm]

/-- 係数の絶対値・法の上限・CRT誤差を、自然数の素因数だけの和にまとめる。 -/
theorem weighted_error {upper P D} (c : Cert upper P D) (hp : ∀ p ∈ P, p.Prime)
    (E : Finset ℕ → ℝ) (hE : ∀ d ⊆ P, |E d| ≤ (2 : ℝ) ^ d.card) :
    |∑ d ∈ P.powerset, c.coeff d * E d| ≤
      ∑ n ∈ Icc 1 ⌊D⌋₊, (8 : ℝ) ^ n.primeFactors.card := by
  classical
  let N := fun d : Finset ℕ => ∏ q ∈ d, q
  let T := P.powerset.filter fun d => N d ≤ ⌊D⌋₊
  have restrict : ∑ d ∈ T, c.coeff d * E d = ∑ d ∈ P.powerset, c.coeff d * E d := by
    apply sum_subset (Finset.filter_subset _ _)
    intro d hd hn
    have hD : D < (N d : ℝ) := by
      by_contra! h
      exact hn (mem_filter.mpr ⟨hd, Nat.le_floor h⟩)
    have h0 := c.level d (mem_powerset.mp hd) (by simpa [N, Nat.cast_prod] using hD)
    simp [h0]
  have hfac (d) (hd : d ∈ T) : (N d).primeFactors = d :=
    Nat.primeFactors_prod fun p h => hp p (mem_powerset.mp (mem_filter.mp hd).1 h)
  have hcode : Set.InjOn N (T : Set (Finset ℕ)) := by
    intro d hd e he h
    rw [← hfac d hd, ← hfac e he, h]
  have hsub : T.image N ⊆ Icc 1 ⌊D⌋₊ := by
    intro n hn
    obtain ⟨d, hd, rfl⟩ := mem_image.mp hn
    exact mem_Icc.mpr ⟨Finset.prod_pos (fun q hq => (hp q (mem_powerset.mp (mem_filter.mp hd).1 hq)).pos),
      (mem_filter.mp hd).2⟩
  rw [← restrict]
  calc
    _ ≤ ∑ d ∈ T, |c.coeff d * E d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ T, (8 : ℝ) ^ (N d).primeFactors.card := by
      apply sum_le_sum
      intro d hd
      have hdP := mem_powerset.mp (mem_filter.mp hd).1
      rw [hfac d hd, abs_mul]
      calc _ ≤ (3 : ℝ) ^ d.card * 2 ^ d.card :=
              mul_le_mul (c.coeff_bound d hdP) (hE d hdP) (abs_nonneg _) (by positivity)
           _ ≤ 8 ^ d.card := by rw [← mul_pow]; gcongr; norm_num
    _ = ∑ n ∈ T.image N, (8 : ℝ) ^ n.primeFactors.card := by rw [sum_image hcode]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)

/-- 任意の下側の篩を、各素数で高々2類を除く実際の整数区間に適用する。 -/
theorem lower_count {P D} (c : Cert false P D) (bad : ℕ → ℕ → Prop) (X L : ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hper : ∀ p x, bad p x ↔ bad p (x % p))
    (hsize : ∀ p ∈ P, numResidues bad p ≤ 2) :
    (L : ℝ) * c.main (fun p => (numResidues bad p : ℝ) / p) -
      (∑ n ∈ Icc 1 ⌊D⌋₊, (8 : ℝ) ^ n.primeFactors.card) ≤
      count (Ico X (X + L)) (fun x => ∀ p ∈ P, ¬ bad p x) := by
  classical
  let A := Ico X (X + L)
  let E := fun d => count A (hits bad d) - (L : ℝ) * residueDensity bad d
  have herr := weighted_error c hp E (fun d hd =>
    interval_discrepancy bad d hper (fun p h => hp p (hd h)) (fun p h => hsize p (hd h)) X L)
  have herr_eq : ∑ d ∈ P.powerset, c.coeff d * E d =
      ∑ d ∈ P.powerset, c.coeff d * count A (hits bad d) -
        (L : ℝ) * c.main (fun p => (numResidues bad p : ℝ) / p) := by
    simp only [main, E, mul_sub, sum_sub_distrib, mul_sum, residueDensity]
    congr 1
    apply sum_congr rfl
    intro d _
    ring
  have hsum : ∑ d ∈ P.powerset, c.coeff d * count A (hits bad d) ≤
        count A (fun x => ∀ p ∈ P, ¬ bad p x) := by
    rw [← polynomial_sum]
    have hpoint (x) (_hx : x ∈ A) := c.bound (badSet P bad x) (filter_subset _ _)
    have h := Finset.sum_le_sum hpoint
    change ∑ x ∈ A, ∑ d ∈ (badSet P bad x).powerset, c.coeff d ≤
        ∑ x ∈ A, (if badSet P bad x = ∅ then (1 : ℝ) else 0) at h
    refine h.trans_eq ?_
    simp only [Finset.sum_boole, count, Nat.cast_inj]
    apply congrArg Finset.card
    ext x
    simp [badSet_empty]
  rw [herr_eq, abs_le] at herr
  change _ ≤ count A _
  linarith [herr.1]


/-- 除外する剰余類が1個以下の素数も、2個ちょうどに拡大して一様な密度2/pを使う。 -/
theorem exists_of_uniform_main {P D} (c : Cert false P D) (bad : ℕ → ℕ → Prop) (X L : ℕ)
    (hp : ∀ p ∈ P, p.Prime) (hper : ∀ p x, bad p x ↔ bad p (x % p))
    (hsize : ∀ p ∈ P, numResidues bad p ≤ 2)
    (hgap : (∑ n ∈ Icc 1 ⌊D⌋₊, (8 : ℝ) ^ n.primeFactors.card) <
       (L : ℝ) * c.main (fun p => 2 / (p : ℝ))) :
    ∃ y ∈ Ico X (X + L), ∀ p ∈ P, ¬ bad p y := by
  classical
  let old := fun p => (range p).filter (bad p)
  have choose_set : ∀ p, ∃ S : Finset ℕ, p ∈ P → old p ⊆ S ∧ S ⊆ range p ∧ S.card = 2 := by
    intro p
    by_cases hm : p ∈ P
    · obtain ⟨S, hs, hr, hc⟩ := exists_subsuperset_card_eq (filter_subset (bad p) (range p))
          (hsize p hm) (by simpa using (hp p hm).two_le : 2 ≤ (range p).card)
      exact ⟨S, fun _ => ⟨hs, hr, hc⟩⟩
    · exact ⟨∅, fun h => (hm h).elim⟩
  choose S hS using choose_set
  let bad' := fun p y => y % p ∈ S p
  have hsize' (p) (hm : p ∈ P) : numResidues bad' p = 2 := by
    unfold numResidues
    have heq : (range p).filter (bad' p) = S p := by
      ext q
      constructor
      · intro h
        obtain ⟨hq, hb⟩ := mem_filter.mp h
        simpa only [bad', Nat.mod_eq_of_lt (mem_range.mp hq)] using hb
      · intro h
        have hq := (hS p hm).2.1 h
        exact mem_filter.mpr ⟨hq, by simpa only [bad', Nat.mod_eq_of_lt (mem_range.mp hq)] using h⟩
    refine Eq.trans ?_ (hS p hm).2.2
    apply congrArg Finset.card
    ext q
    simpa only [mem_filter] using Finset.ext_iff.mp heq q
  have hmain : c.main (fun p => (numResidues bad' p : ℝ) / p) = c.main (fun p => 2 / (p : ℝ)) := by
    unfold main
    apply sum_congr rfl
    intro d hd
    congr 1
    apply prod_congr rfl
    intro p hm
    change (numResidues bad' p : ℝ) / p = 2 / p
    simp [hsize' p (mem_powerset.mp hd hm)]
  have h := lower_count c bad' X L hp (fun p x => by simp [bad'])
    (fun p hm => (hsize' p hm).le)
  rw [hmain] at h
  have hc : 0 < count (Ico X (X + L)) (fun x => ∀ p ∈ P, ¬ bad' p x) :=
    (sub_pos.mpr hgap).trans_le h
  unfold count at hc
  obtain ⟨y, hy⟩ := card_pos.mp (Nat.cast_pos.mp hc)
  simp only [mem_filter] at hy
  obtain ⟨hy, hgood⟩ := hy
  refine ⟨y, hy, fun p hm hb => hgood p hm ?_⟩
  exact (hS p hm).1 (mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ (hp p hm).pos), (hper p y).mp hb⟩)


end OMABeth.Cert

end

section

/-
Bethの元の命題を、長さがC z^{64/15}以上の区間で成立する2次元篩の定理H4から導く。
最後の定理 `OMABeth.beth_of_interval_sieve` の引数が、残る解析的な仮定である。

組合せ構成と指数の計算には次のLean証明を使用した。

* 有限体上の構成 — @ivillar, https://github.com/lefttosolve2/open-math-agents/pull/3737
* 直積構成 — @ivillar, https://github.com/lefttosolve2/open-math-agents/pull/3765
* Wilsonの構成 — @marcusbuffett, https://github.com/lefttosolve2/open-math-agents/pull/3823
  4列の構成は@ptc-prover-botによる https://github.com/lefttosolve2/open-math-agents/pull/3230
* Bethの指数を得る計算 — @PianothShaveck, https://github.com/lefttosolve2/open-math-agents/pull/29344
  コミット68cdcf9ce257d857b13e4dd323d175651a76ca02にある@green-notesのWilson還元の改変
-/

-- Step Erdos724.erdos_724.variants.wilson.R1.H1: hypothesis H1 of reduction Erdos724.erdos_724.variants.wilson.R1
-- Credit: @ivillar
-- Over a finite field F with q elements the q - 1 squares (i, j) -> c i + j, c nonzero, are
-- Latin and pairwise orthogonal; GaloisField p k has p^k elements.

open Finset

namespace O2W

variable {F : Type*} [Field F]

/-- The square `(i, j) ↦ c * i + j` over a finite field, transported to `Fin n`. -/
def sq {n : ℕ} (e : Fin n ≃ F) (c : F) (hc : c ≠ 0) : LatinSquare n where
  mat := fun i j => e.symm (c * e i + e j)
  row_injective := by
    intro i a b h
    have h' := e.symm.injective h
    exact e.injective (add_left_cancel h')
  col_injective := by
    intro j a b h
    have h' := e.symm.injective h
    have h'' : c * e a = c * e b := add_right_cancel h'
    exact e.injective (mul_left_cancel₀ hc h'')

theorem field_bound [Fintype F] [DecidableEq F] (n : ℕ) (hn : Fintype.card F = n) :
    n - 1 ≤ Erdos724.maxMOLS n := by
  classical
  let e : Fin n ≃ F := (Fintype.equivFinOfCardEq hn).symm
  let f : Fˣ → LatinSquare n := fun u => sq e (u : F) u.ne_zero
  have finj : Function.Injective f := by
    intro u v h
    have h1 := congrArg (fun L : LatinSquare n => e (L.mat (e.symm 1) (e.symm 0))) h
    simp only [f, sq, Equiv.apply_symm_apply, mul_one, add_zero] at h1
    exact Units.ext h1
  have hcard : (univ.image f).card = n - 1 := by
    rw [card_image_of_injective _ finj, card_univ, Fintype.card_units, hn]
  refine le_csSup ⟨Fintype.card (LatinSquare n), ?_⟩ ⟨univ.image f, hcard, ?_⟩
  · rintro k ⟨S, rfl, -⟩
    exact card_le_univ S
  · intro L hL M hM hLM
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hL hM
    obtain ⟨u, rfl⟩ := hL
    obtain ⟨v, rfl⟩ := hM
    have huv : (u : F) ≠ v := fun h => hLM (by rw [Units.ext h])
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [f, sq, Prod.mk.injEq] at h
    have h1 := e.symm.injective h.1
    have h2 := e.symm.injective h.2
    have h3 : ((u : F) - v) * (e i - e i') = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) huv
    · have hii : i = i' := e.injective (sub_eq_zero.mp h4)
      subst hii
      have hjj : e j = e j' := add_left_cancel h1
      rw [e.injective hjj]

theorem prime_power_bound (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
    p ^ k - 1 ≤ Erdos724.maxMOLS (p ^ k) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let _ : Fintype (GaloisField p k) := Fintype.ofFinite _
  exact field_bound (F := GaloisField p k) (p ^ k)
    (by rw [Fintype.card_eq_nat_card]; exact GaloisField.card p k (by omega))

end O2W

-- Step Erdos724.erdos_724.variants.wilson.R1.H2: hypothesis H2 of reduction Erdos724.erdos_724.variants.wilson.R1
-- Credit: @ivillar
-- MacNeish's product construction: the direct products of m mutually orthogonal squares of
-- order a with m of order b are m mutually orthogonal squares of order ab.

open Finset

namespace O2W2

open Erdos724

/-- The direct product of a square of order `a` and a square of order `b`. -/
def prodSq {a b : ℕ} (L : LatinSquare a) (M : LatinSquare b) : LatinSquare (a * b) where
  mat := fun x y => finProdFinEquiv
    (L.mat (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm y).1,
     M.mat (finProdFinEquiv.symm x).2 (finProdFinEquiv.symm y).2)
  row_injective := by
    intro x y y' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 := L.row_injective _ h'.1
    have h2 := M.row_injective _ h'.2
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)
  col_injective := by
    intro y x x' h
    have h' := finProdFinEquiv.injective h
    simp only [Prod.mk.injEq] at h'
    have h1 := L.col_injective _ h'.1
    have h2 := M.col_injective _ h'.2
    exact finProdFinEquiv.symm.injective (Prod.ext h1 h2)

lemma prodSq_orth {a b : ℕ} {L L' : LatinSquare a} {M M' : LatinSquare b}
    (hL : IsOrthogonal L L') (hM : IsOrthogonal M M') :
    IsOrthogonal (prodSq L M) (prodSq L' M') := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  simp only [prodSq, Prod.mk.injEq] at h
  have h1 := finProdFinEquiv.injective h.1
  have h2 := finProdFinEquiv.injective h.2
  simp only [Prod.mk.injEq] at h1 h2
  have e1 := hL (a₁ := ((finProdFinEquiv.symm x).1, (finProdFinEquiv.symm y).1))
    (a₂ := ((finProdFinEquiv.symm x').1, (finProdFinEquiv.symm y').1))
    (Prod.ext h1.1 h2.1)
  have e2 := hM (a₁ := ((finProdFinEquiv.symm x).2, (finProdFinEquiv.symm y).2))
    (a₂ := ((finProdFinEquiv.symm x').2, (finProdFinEquiv.symm y').2))
    (Prod.ext h1.2 h2.2)
  simp only [Prod.mk.injEq] at e1 e2
  have hx : x = x' := finProdFinEquiv.symm.injective (Prod.ext e1.1 e2.1)
  have hy : y = y' := finProdFinEquiv.symm.injective (Prod.ext e1.2 e2.2)
  rw [hx, hy]

lemma prodSq_left {a b : ℕ} (hb : 0 < b) {L L' : LatinSquare a} {M M' : LatinSquare b}
    (h : prodSq L M = prodSq L' M') : L = L' := by
  have hm : ∀ u v : Fin a, L.mat u v = L'.mat u v := by
    intro u v
    have := congrArg (fun P : LatinSquare (a * b) =>
      (finProdFinEquiv.symm (P.mat (finProdFinEquiv (u, ⟨0, hb⟩))
        (finProdFinEquiv (v, ⟨0, hb⟩)))).1) h
    simp only [prodSq, Equiv.symm_apply_apply] at this
    exact this
  cases L; cases L'
  simp only [LatinSquare.mk.injEq]
  funext u v
  exact hm u v

lemma bdd (n : ℕ) : BddAbove {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal} := by
  classical
  refine ⟨Fintype.card (LatinSquare n), ?_⟩
  rintro k ⟨S, rfl, -⟩
  exact card_le_univ S

lemma attain (n : ℕ) : ∃ S : Finset (LatinSquare n), #S = maxMOLS n ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal := by
  have h := Nat.sSup_mem (s := {k : ℕ | ∃ S : Finset (LatinSquare n), #S = k ∧
    (S : Set (LatinSquare n)).Pairwise IsOrthogonal}) ⟨0, ∅, by simp, by simp⟩ (bdd n)
  exact h

theorem macNeish (a b : ℕ) (_ha : 1 ≤ a) (hb : 1 ≤ b) :
    min (maxMOLS a) (maxMOLS b) ≤ maxMOLS (a * b) := by
  classical
  set m := min (maxMOLS a) (maxMOLS b)
  obtain ⟨Sa, hSa, hpa⟩ := attain a
  obtain ⟨Sb, hSb, hpb⟩ := attain b
  obtain ⟨Ta, hTa, hTac⟩ := exists_subset_card_eq (show m ≤ #Sa by rw [hSa]; exact min_le_left _ _)
  obtain ⟨Tb, hTb, hTbc⟩ := exists_subset_card_eq (show m ≤ #Sb by rw [hSb]; exact min_le_right _ _)
  have hpa' := hpa.mono (coe_subset.mpr hTa)
  have hpb' := hpb.mono (coe_subset.mpr hTb)
  let fa : Fin m → LatinSquare a := fun i => (Ta.equivFinOfCardEq hTac).symm i
  let fb : Fin m → LatinSquare b := fun i => (Tb.equivFinOfCardEq hTbc).symm i
  have fa_mem : ∀ i, fa i ∈ Ta := fun i => ((Ta.equivFinOfCardEq hTac).symm i).2
  have fb_mem : ∀ i, fb i ∈ Tb := fun i => ((Tb.equivFinOfCardEq hTbc).symm i).2
  have fa_inj : Function.Injective fa := by
    intro i j h
    exact (Ta.equivFinOfCardEq hTac).symm.injective (Subtype.ext h)
  have fb_inj : Function.Injective fb := by
    intro i j h
    exact (Tb.equivFinOfCardEq hTbc).symm.injective (Subtype.ext h)
  let g : Fin m → LatinSquare (a * b) := fun i => prodSq (fa i) (fb i)
  have g_inj : Function.Injective g := fun i j h => fa_inj (prodSq_left (by omega) h)
  refine le_csSup (bdd (a * b)) ⟨univ.image g, ?_, ?_⟩
  · rw [card_image_of_injective _ g_inj, card_univ, Fintype.card_fin]
  · intro P hP Q hQ hPQ
    simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range] at hP hQ
    obtain ⟨i, rfl⟩ := hP
    obtain ⟨j, rfl⟩ := hQ
    have hij : i ≠ j := fun h => hPQ (by rw [h])
    exact prodSq_orth (hpa' (fa_mem i) (fa_mem j) (fun h => hij (fa_inj h)))
      (hpb' (fb_mem i) (fb_mem j) (fun h => hij (fb_inj h)))

end O2W2

/-
Wilson’s truncated transversal design recursion. The array gluing argument generalizes the four-column construction of @ptc-prover-bot in merged PR 3230, commit 02c8589. The arbitrary-size Latin square family and its conversion to and from an orthogonal array are supplied here.
-/
/- Generalized from @ptc-prover-bot, merged PR 3230, commit 02c8589. -/
namespace W724
def IsOA {α : Type*} (k : ℕ) (S : Set (Fin k → α)) : Prop :=
  ∀ a b : Fin k, a ≠ b → Set.BijOn (fun r => (r a, r b)) S Set.univ

variable {T U M : Type*} {d : ℕ}

def rowA (β : Fin (d+1) → T) (r : Fin d → M) : Fin d → (T × M) ⊕ U :=
  fun g => Sum.inl (β g.castSucc, r g)

def rowB (β : Fin (d+1) → T) (k : U) (r : Fin d → Option M) : Fin d → (T × M) ⊕ U :=
  fun g => match r g with
    | none => Sum.inr k
    | some s => Sum.inl (β g.castSucc, s)

def rowC (r : Fin d → U) : Fin d → (T × M) ⊕ U := fun g => Sum.inr (r g)

def W (S5 : Set (Fin (d+1) → T)) (S3 : Set (Fin d → M)) (S4 : Set (Fin d → Option M))
    (SU : Set (Fin d → U)) (ι : U → T) : Set (Fin d → (T × M) ⊕ U) :=
  {x | ∃ β ∈ S5, (∀ k, ι k ≠ β (Fin.last d)) ∧ ∃ r ∈ S3, x = rowA β r} ∪
  {x | ∃ β ∈ S5, ∃ k, ι k = β (Fin.last d) ∧ ∃ r ∈ S4, r ≠ (fun _ => none) ∧ x = rowB β k r} ∪
  {x | ∃ r ∈ SU, x = rowC r}

lemma rowB_eq_inl {β : Fin (d+1) → T} {k : U} {r : Fin d → Option M} {g : Fin d} {p : T × M} :
    rowB β k r g = Sum.inl p ↔ ∃ s, r g = some s ∧ p = (β g.castSucc, s) := by
  unfold rowB
  cases r g <;> simp [eq_comm]

lemma rowB_eq_inr {β : Fin (d+1) → T} {k : U} {r : Fin d → Option M} {g : Fin d} {k' : U} :
    rowB β k r g = Sum.inr k' ↔ r g = none ∧ k = k' := by
  unfold rowB
  cases r g <;> simp

lemma inj_of {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S) {a b : Fin k} (hab : a ≠ b)
    {r r' : Fin k → α} (hr : r ∈ S) (hr' : r' ∈ S) (h1 : r a = r' a) (h2 : r b = r' b) : r = r' :=
  (h a b hab).injOn hr hr' (Prod.ext h1 h2)

lemma ex_of {α : Type*} {k : ℕ} {S : Set (Fin k → α)} (h : IsOA k S) {a b : Fin k} (hab : a ≠ b)
    (x y : α) : ∃ r ∈ S, r a = x ∧ r b = y := by
  obtain ⟨r, hr, he⟩ := (h a b hab).surjOn (Set.mem_univ (x, y))
  exact ⟨r, hr, (Prod.ext_iff.mp he).1, (Prod.ext_iff.mp he).2⟩

theorem wilson_OA {S5 : Set (Fin (d+1) → T)} {S3 : Set (Fin d → M)}
    {S4 : Set (Fin d → Option M)} {SU : Set (Fin d → U)} {ι : U → T}
    (h5 : IsOA (d+1) S5) (h3 : IsOA d S3) (h4 : IsOA d S4) (hnone : (fun _ => none) ∈ S4)
    (hU : IsOA d SU) (hι : Function.Injective ι) : IsOA d (W S5 S3 S4 SU ι) := by
  classical
  intro a b hab
  have hab' : a.castSucc ≠ b.castSucc := fun h => hab (Fin.castSucc_injective _ h)
  have ha4 : a.castSucc ≠ Fin.last d := Fin.castSucc_ne_last a
  have hb4 : b.castSucc ≠ Fin.last d := Fin.castSucc_ne_last b
  -- a row of S4 with two `none` entries at a, b is the all-none row
  have allnone : ∀ r ∈ S4, r a = none → r b = none → r = fun _ => none := fun r hr h1 h2 =>
    inj_of h4 hab hr hnone h1 h2
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · -- injectivity
    rintro x hx y hy hxy
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨hxa, hxb⟩ := hxy
    rcases hx with (⟨β, hβ, hβι, r, hr, rfl⟩ | ⟨β, hβ, k, hk, r, hr, hrn, rfl⟩) | ⟨r, hr, rfl⟩ <;>
    rcases hy with (⟨γ, hγ, hγι, s, hs, rfl⟩ | ⟨γ, hγ, k', hk', s, hs, hsn, rfl⟩) | ⟨s, hs, rfl⟩
    -- A A
    · simp only [rowA, Sum.inl.injEq, Prod.mk.injEq] at hxa hxb
      rw [inj_of h5 hab' hβ hγ hxa.1 hxb.1, inj_of h3 hab hr hs hxa.2 hxb.2]
    -- A B
    · exfalso
      obtain ⟨s1, hs1, e1⟩ := rowB_eq_inl.mp hxa.symm
      obtain ⟨s2, hs2, e2⟩ := rowB_eq_inl.mp hxb.symm
      simp only [rowA, Prod.mk.injEq] at e1 e2
      have := inj_of h5 hab' hβ hγ e1.1 e2.1
      exact hβι k' (this ▸ hk')
    -- A C
    · simp [rowA, rowC] at hxa
    -- B A
    · exfalso
      obtain ⟨s1, hs1, e1⟩ := rowB_eq_inl.mp hxa
      obtain ⟨s2, hs2, e2⟩ := rowB_eq_inl.mp hxb
      simp only [rowA, Prod.mk.injEq] at e1 e2
      have := inj_of h5 hab' hβ hγ e1.1.symm e2.1.symm
      exact hγι k (this ▸ hk)
    -- B B
    · cases hra : r a with
      | none =>
        cases hrb : r b with
        | none => exact absurd (allnone r hr hra hrb) hrn
        | some v =>
          have xa : rowB β k r a = Sum.inr k := by simp [rowB, hra]
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v) := by simp [rowB, hrb]
          rw [xa] at hxa; rw [xb] at hxb
          obtain ⟨hsa, rfl⟩ := rowB_eq_inr.mp hxa.symm
          obtain ⟨w, hsb, e⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e
          have hβγ : β = γ := inj_of h5 hb4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [inj_of h4 hab hr hs (hra.trans hsa.symm) (hrb.trans (by rw [hsb, e.2]))]
      | some v =>
        have xa : rowB β k r a = Sum.inl (β a.castSucc, v) := by simp [rowB, hra]
        rw [xa] at hxa
        obtain ⟨w, hsa, e⟩ := rowB_eq_inl.mp hxa.symm
        simp only [Prod.mk.injEq] at e
        cases hrb : r b with
        | none =>
          have xb : rowB β k r b = Sum.inr k := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨hsb, rfl⟩ := rowB_eq_inr.mp hxb.symm
          have hβγ : β = γ := inj_of h5 ha4 hβ hγ e.1 (hk.symm.trans hk')
          subst hβγ
          rw [inj_of h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans hsb.symm)]
        | some v' =>
          have xb : rowB β k r b = Sum.inl (β b.castSucc, v') := by simp [rowB, hrb]
          rw [xb] at hxb
          obtain ⟨w', hsb, e'⟩ := rowB_eq_inl.mp hxb.symm
          simp only [Prod.mk.injEq] at e'
          have hβγ : β = γ := inj_of h5 hab' hβ hγ e.1 e'.1
          subst hβγ
          have hkk : k = k' := hι (hk.trans hk'.symm)
          subst hkk
          rw [inj_of h4 hab hr hs (hra.trans (by rw [hsa, e.2])) (hrb.trans (by rw [hsb, e'.2]))]
    -- B C
    · exfalso
      obtain ⟨h1, -⟩ := rowB_eq_inr.mp hxa
      obtain ⟨h2, -⟩ := rowB_eq_inr.mp hxb
      exact hrn (allnone r hr h1 h2)
    -- C A
    · simp [rowA, rowC] at hxa
    -- C B
    · exfalso
      obtain ⟨h1, -⟩ := rowB_eq_inr.mp hxa.symm
      obtain ⟨h2, -⟩ := rowB_eq_inr.mp hxb.symm
      exact hsn (allnone s hs h1 h2)
    -- C C
    · simp only [rowC, Sum.inr.injEq] at hxa hxb
      rw [inj_of hU hab hr hs hxa hxb]
  · -- surjectivity
    rintro ⟨P, Q⟩ -
    rcases P with ⟨p, α⟩ | k <;> rcases Q with ⟨q, α'⟩ | k'
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 hab' p q
      by_cases hι' : ∃ k, ι k = β (Fin.last d)
      · obtain ⟨k, hk⟩ := hι'
        obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab (some α) (some α')
        refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, hk, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
        simp [rowB, r1, r2, e1, e2]
      · push_neg at hι'
        obtain ⟨r, hr, r1, r2⟩ := ex_of h3 hab α α'
        exact ⟨rowA β r, Or.inl (Or.inl ⟨β, hβ, hι', r, hr, rfl⟩), by simp [rowA, r1, r2, e1, e2]⟩
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 ha4 p (ι k')
      obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab (some α) none
      refine ⟨rowB β k' r, Or.inl (Or.inr ⟨β, hβ, k', e2.symm, r, hr, fun h => by simp [h] at r1, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨β, hβ, e1, e2⟩ := ex_of h5 hb4 q (ι k)
      obtain ⟨r, hr, r1, r2⟩ := ex_of h4 hab none (some α')
      refine ⟨rowB β k r, Or.inl (Or.inr ⟨β, hβ, k, e2.symm, r, hr, fun h => by simp [h] at r2, rfl⟩), ?_⟩
      simp [rowB, r1, r2, e1]
    · obtain ⟨r, hr, r1, r2⟩ := ex_of hU hab k k'
      exact ⟨rowC r, Or.inr ⟨r, hr, rfl⟩, by simp [rowC, r1, r2]⟩


lemma oa_of_range {ι α : Type*} [Fintype ι] [Fintype α] {k : ℕ} (f : ι → Fin k → α)
    (hcard : Fintype.card ι = Fintype.card α * Fintype.card α)
    (h : ∀ a b : Fin k, a ≠ b → Function.Injective fun i => (f i a, f i b)) :
    IsOA k (Set.range f) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
    rw [h a b hab hij]
  · intro xy _
    have hb : Function.Bijective fun i => (f i a, f i b) :=
      (Fintype.bijective_iff_injective_and_card _).mpr ⟨h a b hab, by rw [hcard, Fintype.card_prod]⟩
    obtain ⟨i, hi⟩ := hb.2 xy
    exact ⟨f i, ⟨i, rfl⟩, hi⟩


end W724

namespace W724
open Finset Erdos724

private def sizes (n : ℕ) : Set ℕ := {k | ∃ S : Finset (LatinSquare n), S.card=k ∧ (S:Set (LatinSquare n)).Pairwise IsOrthogonal}
lemma sizes_bdd (n : ℕ) : BddAbove (sizes n) := by
  refine ⟨Fintype.card (LatinSquare n),?_⟩
  rintro _ ⟨S,rfl,_⟩; exact card_le_univ S

lemma getFamily {s n : ℕ} (h : s ≤ maxMOLS n) : ∃ L : Fin s → LatinSquare n,
    ∀ i j, i≠j → IsOrthogonal (L i) (L j) := by
  classical
  have h0 : 0∈sizes n := ⟨∅,rfl,by simp⟩
  obtain ⟨S,hS,hp⟩ := Nat.sSup_mem ⟨0,h0⟩ (sizes_bdd n)
  have hle : s≤S.card := by rw [hS]; exact h
  let E : Fin s ↪ S := (Fin.castLEEmb hle).trans (Fintype.equivFinOfCardEq (α:=S) (by simp : Fintype.card S = S.card)).symm.toEmbedding
  exact ⟨fun i => E i,fun i j hij => hp (E i).2 (E j).2 (fun eq => hij (E.injective (Subtype.ext eq)))⟩

def fullRow {s n : ℕ} (L : Fin s → LatinSquare n) (p : Fin n × Fin n) : Fin (s+2) → Fin n :=
  Fin.cases p.1 (Fin.cases p.2 (fun v => (L v).mat p.1 p.2))

lemma input {s n : ℕ} (h : s ≤ maxMOLS n) : ∃ S, @IsOA (Fin n) (s+2) S := by
  classical
  obtain ⟨L,hL⟩ := getFamily h
  refine ⟨Set.range (fullRow L),oa_of_range _ (by simp) ?_⟩
  intro c d hcd
  rintro ⟨i,j⟩ ⟨i',j'⟩ eq
  obtain ⟨hx,hy⟩ := Prod.mk.inj eq
  rcases Fin.eq_zero_or_eq_succ c with rfl|⟨c,rfl⟩
  · rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact (hcd rfl).elim
    rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact Prod.ext hx hy
    change i=i' at hx
    subst i'
    exact Prod.ext rfl ((L d).row_injective i hy)
  rcases Fin.eq_zero_or_eq_succ c with rfl|⟨c,rfl⟩
  · rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact Prod.ext hy hx
    rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
    · exact (hcd rfl).elim
    change j=j' at hx
    subst j'
    exact Prod.ext ((L d).col_injective j hy) rfl
  rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
  · change i=i' at hy
    subst i'
    exact Prod.ext rfl ((L c).row_injective i hx)
  rcases Fin.eq_zero_or_eq_succ d with rfl|⟨d,rfl⟩
  · change j=j' at hy
    subst j'
    exact Prod.ext ((L c).col_injective j hx) rfl
  exact hL c d (fun E => hcd (E ▸ rfl)) (Prod.ext hx hy)

lemma relabel {α β : Type*} {d : ℕ} {S : Set (Fin d → α)} (hS : IsOA d S) (e : Fin d → α ≃ β) :
    IsOA d ((fun (r : Fin d → α) i => e i (r i)) '' S) := by
  intro a b hab
  refine ⟨fun _ _ => Set.mem_univ _,?_,?_⟩
  · rintro _ ⟨r,hr,rfl⟩ _ ⟨s,hs,rfl⟩ eq
    have := inj_of hS hab hr hs ((e a).injective (Prod.mk.inj eq).1) ((e b).injective (Prod.mk.inj eq).2)
    rw [this]
  · rintro ⟨x,y⟩ -
    obtain ⟨r,hr,hx,hy⟩ := ex_of hS hab ((e a).symm x) ((e b).symm y)
    exact ⟨_,⟨r,hr,rfl⟩,by simp [hx,hy]⟩

lemma withNone {s m : ℕ} (h : s ≤ maxMOLS (m+1)) : ∃ S, @IsOA (Option (Fin m)) (s+2) S ∧ (fun _ => none) ∈ S := by
  classical
  obtain ⟨A,hA⟩ := input h
  obtain ⟨r,hr,_,_⟩ := ex_of hA (show (0:Fin (s+2))≠1 by exact Fin.zero_ne_one) 0 0
  let e : Fin (m+1) ≃ Option (Fin m) := (Fintype.equivFinOfCardEq (by simp)).symm
  let E (i : Fin (s+2)) := e.trans (Equiv.swap (e (r i)) none)
  refine ⟨_,relabel hA E, r,hr,?_⟩
  funext i
  simp [E]
end W724


namespace W724
open Finset Erdos724

-- The two axes and the remaining columns of an array give the required family.
theorem output {s n : ℕ} (hn : 2≤n) {α : Type*} (e : α ≃ Fin n)
    {S : Set (Fin (s+2) → α)} (h : IsOA (s+2) S) : s ≤ maxMOLS n := by
  classical
  let a : Fin (s+2) := 0
  let b : Fin (s+2) := (0:Fin (s+1)).succ
  let c (i : Fin s) := i.succ.succ
  have hab : a ≠ b := Ne.symm (Fin.succ_ne_zero _)
  have hac (i : Fin s) : a ≠ c i := Ne.symm (Fin.succ_ne_zero _)
  have hbc (i : Fin s) : b ≠ c i := fun eq => Fin.succ_ne_zero i (Fin.succ_injective _ eq).symm
  let row (p : Fin n × Fin n) := (ex_of h hab (e.symm p.1) (e.symm p.2)).choose
  have hr (p : Fin n × Fin n) : row p∈S ∧ row p a=e.symm p.1 ∧ row p b=e.symm p.2 :=
    (ex_of h hab _ _).choose_spec
  have key {u v : Fin (s+2)} (huv : u≠v) {p q : Fin n × Fin n}
      (hu : row p u=row q u) (hv : row p v=row q v) : p=q := by
    have eq := inj_of h huv (hr p).1 (hr q).1 hu hv
    exact Prod.ext (e.symm.injective ((hr p).2.1.symm.trans ((congrFun eq a).trans (hr q).2.1)))
      (e.symm.injective ((hr p).2.2.symm.trans ((congrFun eq b).trans (hr q).2.2)))
  let L (i : Fin s) : LatinSquare n := {
    mat := fun x y => e (row (x,y) (c i))
    row_injective := fun x y z eq => congrArg Prod.snd (key (hac i)
      ((hr (x,y)).2.1.trans (hr (x,z)).2.1.symm) (e.injective eq))
    col_injective := fun y x z eq => congrArg Prod.fst (key (hbc i)
      ((hr (x,y)).2.2.trans (hr (z,y)).2.2.symm) (e.injective eq)) }
  have horth {i j : Fin s} (hij : i≠j) : IsOrthogonal (L i) (L j) := by
    intro p q eq
    exact key (show c i ≠ c j from fun E => hij (Fin.succ_injective _ (Fin.succ_injective _ E)))
      (e.injective (Prod.mk.inj eq).1) (e.injective (Prod.mk.inj eq).2)
  have hinj : Function.Injective L := by
    intro i j E
    by_contra hij
    have hh := horth hij; rw [E] at hh
    let z : Fin n := ⟨0,by omega⟩
    let o : Fin n := ⟨1,by omega⟩
    obtain ⟨k,hk⟩ := (Finite.injective_iff_surjective.mp ((L j).row_injective o)) ((L j).mat z z)
    have eq : (o,k)=(z,z) := hh (Prod.ext hk hk)
    have := congrArg (fun p : Fin n × Fin n => p.1.val) eq
    contradiction
  apply le_csSup (sizes_bdd n)
  refine ⟨univ.image L,by rw [card_image_of_injective _ hinj]; simp,?_⟩
  rintro _ h1 _ h2 hne
  obtain ⟨i,_,rfl⟩ := mem_image.mp h1
  obtain ⟨j,_,rfl⟩ := mem_image.mp h2
  exact horth (fun eq => hne (congrArg L eq))

theorem wilson (m t u s : ℕ) (hm : 1 ≤ m) (hu : 1≤u) (hut : u≤t)
    (h1 : s ≤ maxMOLS m) (h2 : s ≤ maxMOLS (m+1)) (h3 : s+1 ≤ maxMOLS t)
    (h4 : s ≤ maxMOLS u) : s ≤ maxMOLS (m*t+u) := by
  classical
  obtain ⟨A,hA⟩ := input h3
  obtain ⟨B,hB⟩ := input h1
  obtain ⟨C,hC,h0⟩ := withNone h2
  obtain ⟨D,hD⟩ := input h4
  have hOA := wilson_OA hA hB hC h0 hD (Fin.castLEEmb hut).injective
  let e : ((Fin t × Fin m) ⊕ Fin u) ≃ Fin (m*t+u) := Fintype.equivFinOfCardEq (by simp [Nat.mul_comm])
  exact output (by nlinarith) e hOA
end W724

/-
Beth's lower bound follows from the finite-field, product, and truncated
transversal-design constructions together with a dimension-two interval sieve
at exponent 64/15. The first sieve call produces two consecutive orders
of size O(z^(79/15)); the second uses an interval of length comparable to
n/z^(158/15). The sum of the exponents is 74/5.

The construction and arithmetic follow the Wilson reduction by @green-notes.
-/

-- Reduction Erdos724.erdos_724.variants.beth.R1 of Erdős Problem 724
-- Credit: @PianothShaveck

namespace OMA.R_Erdos724_erdos_724_variants_beth_R1

open Filter Erdos724

def H1 : Prop :=
  ∀ p k : ℕ, p.Prime → 1 ≤ k → p ^ k - 1 ≤ Erdos724.maxMOLS (p ^ k)

def H2 : Prop :=
  ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    min (Erdos724.maxMOLS a) (Erdos724.maxMOLS b) ≤ Erdos724.maxMOLS (a * b)

def H3 : Prop :=
  ∀ m t u s : ℕ, 1 ≤ m → 1 ≤ u → u ≤ t →
    s ≤ Erdos724.maxMOLS m → s ≤ Erdos724.maxMOLS (m + 1) →
    s + 1 ≤ Erdos724.maxMOLS t → s ≤ Erdos724.maxMOLS u →
    s ≤ Erdos724.maxMOLS (m * t + u)

def H4 : Prop :=
  ∃ C : ℝ, 3 ≤ C ∧ ∀ (z : ℝ) (X L : ℕ) (a b : ℤ),
    C ≤ z → C * z ^ ((64 : ℝ) / 15) ≤ (L : ℝ) →
    (∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ ((p : ℤ) ∣ a)) →
    ∃ x ∈ Finset.Ico X (X + L),
      ¬ 2 ∣ x ∧
      ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z →
        ¬ ((p : ℤ) ∣ (x : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x : ℤ) + b)

section Helpers

private lemma macneish (h1 : H1) (h2 : H2) :
    ∀ n : ℕ, 2 ≤ n → ∀ s : ℕ,
      (∀ p ∈ n.primeFactors, s + 1 ≤ p ^ (n.factorization p)) → s ≤ Erdos724.maxMOLS n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn s hs
    let p := n.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    have hpn : p ∣ n := Nat.minFac_dvd n
    have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
    have hk : 1 ≤ n.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpn
    let q := p ^ (n.factorization p)
    have hqn : q ∣ n := Nat.ordProj_dvd n p
    let r := n / q
    have hqr : q * r = n := Nat.mul_div_cancel' hqn
    have hq_pos : 1 ≤ q := Nat.one_le_pow _ _ hp.pos
    have hr_pos : 1 ≤ r := Nat.pos_of_ne_zero fun hr0 => by
      rw [hr0, mul_zero] at hqr
      omega
    have hq_ge : s ≤ Erdos724.maxMOLS q := by
      have h1q := h1 p (n.factorization p) hp hk
      have hsq : s + 1 ≤ q := hs p hpmem
      dsimp only [q]
      omega
    by_cases hr1 : r = 1
    · rw [← hqr, hr1, mul_one]
      exact hq_ge
    · have hr2 : 2 ≤ r := by omega
      have hq2 : 2 ≤ q := by
        have hp2 : 2 ≤ p := hp.two_le
        have hpow : p ≤ p ^ (n.factorization p) := by
          simpa using Nat.pow_le_pow_right hp.pos hk
        simpa [q] using hp2.trans hpow
      have hrlt : r < n := by
        calc r = 1 * r := (one_mul r).symm
          _ < q * r := Nat.mul_lt_mul_of_pos_right (by omega) hr_pos
          _ = n := hqr
      have hpnr : ¬ p ∣ r := Nat.not_dvd_ordCompl hp (by omega)
      have hsr : s ≤ Erdos724.maxMOLS r := by
        refine ih r hrlt hr2 s fun p' hp' => ?_
        have hp'_prime : p'.Prime := (Nat.mem_primeFactors.mp hp').1
        have hp'_dvd_r : p' ∣ r := (Nat.mem_primeFactors.mp hp').2.1
        have hp'_ne : p' ≠ p := by
          rintro rfl
          exact hpnr hp'_dvd_r
        have hp'_dvd_n : p' ∣ n := hp'_dvd_r.trans ⟨q, by rw [← hqr, mul_comm]⟩
        have hp'_mem : p' ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hp'_prime, hp'_dvd_n, by omega⟩
        have hq_not : ¬ p' ∣ q := fun hd => by
          have := (Nat.dvd_prime hp).mp (hp'_prime.dvd_of_dvd_pow hd)
          rcases this with h1' | hpeq
          · exact hp'_prime.ne_one h1'
          · exact hp'_ne hpeq
        have hfac : r.factorization p' = n.factorization p' := by
          have h := congrArg (fun x => Nat.factorization x p') hqr.symm
          rw [Nat.factorization_mul (by omega) (by omega), Finsupp.add_apply,
            Nat.factorization_eq_zero_of_not_dvd hq_not, zero_add] at h
          exact h.symm
        rw [hfac]
        exact hs p' hp'_mem
      calc s ≤ min (Erdos724.maxMOLS q) (Erdos724.maxMOLS r) := le_min hq_ge hsr
        _ ≤ Erdos724.maxMOLS (q * r) := h2 q r hq_pos hr_pos
        _ = Erdos724.maxMOLS n := by rw [hqr]

private lemma exists_pow_two_near {z : ℝ} (hz : 3 ≤ z) :
    ∃ k : ℕ, 2 ≤ k ∧ z < ((2 ^ k : ℕ) : ℝ) ∧ ((2 ^ k : ℕ) : ℝ) ≤ 2 * z := by
  let f : ℕ := ⌊z⌋₊
  have hf3 : 3 ≤ f := Nat.le_floor (by exact_mod_cast hz)
  have hlog : 1 ≤ Nat.log 2 f := Nat.le_log_of_pow_le (by omega) (by omega)
  refine ⟨Nat.log 2 f + 1, by omega, ?_, ?_⟩
  · have hlt : f < 2 ^ (Nat.log 2 f + 1) := Nat.lt_pow_succ_log_self (by omega) f
    have hle : f + 1 ≤ 2 ^ (Nat.log 2 f + 1) := hlt
    have hz1 : z < (f : ℝ) + 1 := Nat.lt_floor_add_one z
    have hleR : (f : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 f + 1) : ℕ) : ℝ) := by exact_mod_cast hle
    exact hz1.trans_le hleR
  · have hpow : 2 ^ Nat.log 2 f ≤ f := Nat.pow_log_le_self 2 (by omega)
    have hpow2 : 2 ^ (Nat.log 2 f + 1) ≤ 2 * f := by
      rw [pow_succ']
      omega
    have hfR : (f : ℝ) ≤ z := Nat.floor_le (by linarith)
    have hpowR : ((2 ^ (Nat.log 2 f + 1) : ℕ) : ℝ) ≤ 2 * (f : ℝ) := by exact_mod_cast hpow2
    linarith

end Helpers

set_option maxHeartbeats 800000 in
theorem main : H1 → H2 → H3 → H4 → type_of% @Erdos724.erdos_724.variants.beth := by
  intro h1 h2 h3 h4
  obtain ⟨C, hC3, hsieve⟩ := h4
  let c : ℝ := 1 / (40 * C ^ (3 : ℕ))
  have hc_pos : 0 < c := by positivity
  have hc_half : 0 < c / 2 := by positivity
  refine ⟨c / 2, hc_half, ?_⟩
  have hpow_atTop : Tendsto (fun n : ℕ => c * (n : ℝ) ^ ((1 : ℝ) / 14.8)) atTop atTop :=
    Tendsto.const_mul_atTop hc_pos
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 14.8)).comp tendsto_natCast_atTop_atTop)
  have h_ev1 : ∀ᶠ n : ℕ in atTop, C ≤ c * (n : ℝ) ^ ((1 : ℝ) / 14.8) :=
    hpow_atTop.eventually (eventually_ge_atTop C)
  have h_ev2 : ∀ᶠ n : ℕ in atTop, (6 : ℝ) ≤ c * (n : ℝ) ^ ((1 : ℝ) / 14.8) :=
    hpow_atTop.eventually (eventually_ge_atTop 6)
  have h_ev3 : ∀ᶠ n : ℕ in atTop, 2 ≤ n := eventually_ge_atTop 2
  filter_upwards [h_ev1, h_ev2, h_ev3] with n hzC hz6 hn2
  set z : ℝ := c * (n : ℝ) ^ ((1 : ℝ) / 14.8)
  have hz3 : 3 ≤ z := by linarith
  have hz_pos : 0 < z := by linarith
  have hz_times : z * z ^ ((64 : ℝ) / 15) = z ^ ((79 : ℝ) / 15) := by
    calc z * z ^ ((64 : ℝ) / 15) = z ^ ((1 : ℝ) + 64 / 15) := by
          rw [Real.rpow_add hz_pos, Real.rpow_one]
      _ = _ := by norm_num
  have hz_square : z ^ ((79 : ℝ) / 15) * z ^ ((79 : ℝ) / 15) = z ^ ((158 : ℝ) / 15) := by
    rw [← Real.rpow_add hz_pos]
    norm_num
  have hz_combined : z ^ ((64 : ℝ) / 15) * z ^ ((158 : ℝ) / 15) = z ^ ((74 : ℝ) / 5) := by
    rw [← Real.rpow_add hz_pos]
    norm_num
  obtain ⟨k, hk2, hzA, hA2z⟩ := exists_pow_two_near hz3
  let A : ℕ := 2 ^ k
  have hA_ge : 4 ≤ A := by
    have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk2
    simpa [A] using this
  have hA_odd : ∀ p : ℕ, p.Prime → 3 ≤ p → ¬ ((p : ℤ) ∣ (A : ℤ)) := by
    intro p hp hp3 hdiv
    have hdivN : p ∣ 2 ^ k := Int.natCast_dvd_natCast.mp hdiv
    have hp2 := hp.eq_two_or_odd
    have hdvd2 := hp.dvd_of_dvd_pow hdivN
    have := Nat.dvd_prime Nat.prime_two |>.mp hdvd2
    omega
  let Lq : ℕ := ⌈C * z ^ ((64 : ℝ) / 15)⌉₊
  have hLq : C * z ^ ((64 : ℝ) / 15) ≤ (Lq : ℝ) := Nat.le_ceil _
  let bq : ℤ := if Even n then -1 else 1
  obtain ⟨q, hq_mem, hq_odd, hq_sieve⟩ :=
    hsieve z 1 Lq (A : ℤ) bq hzC hLq (fun p hp hp3 _ => hA_odd p hp hp3)
  have hq_ge : 1 ≤ q := (Finset.mem_Ico.mp hq_mem).1
  have hq_lt : q < 1 + Lq := (Finset.mem_Ico.mp hq_mem).2
  have hLq_lt : (Lq : ℝ) < C * z ^ ((64 : ℝ) / 15) + 1 := Nat.ceil_lt_add_one (by positivity)
  have hq_leR : (q : ℝ) ≤ 2 * C * z ^ ((64 : ℝ) / 15) := by
    have hqR : (q : ℝ) < 1 + (Lq : ℝ) := by exact_mod_cast hq_lt
    have hz5 : (1 : ℝ) ≤ z ^ ((64 : ℝ) / 15) := Real.one_le_rpow (by linarith) (by norm_num)
    have hCz5 : (2 : ℝ) ≤ C * z ^ ((64 : ℝ) / 15) := by nlinarith
    linarith
  let m : ℕ := if Even n then A * q - 1 else A * q
  have hAq4 : 4 ≤ A * q := Nat.mul_le_mul hA_ge hq_ge
  have hm_ge3 : 3 ≤ m := by
    dsimp only [m]
    split_ifs <;> omega
  have hm_leR : (m : ℝ) ≤ 4 * C * z ^ ((79 : ℝ) / 15) := by
    have hAqR : ((A * q : ℕ) : ℝ) ≤ 4 * C * z ^ ((79 : ℝ) / 15) := by
      calc ((A * q : ℕ) : ℝ) = (A : ℝ) * (q : ℝ) := by push_cast; ring
        _ ≤ (2 * z) * (2 * C * z ^ ((64 : ℝ) / 15)) := by gcongr
        _ = 4 * C * (z * z ^ ((64 : ℝ) / 15)) := by ring
        _ = 4 * C * z ^ ((79 : ℝ) / 15) := by rw [hz_times]
    dsimp only [m]
    split_ifs with he
    · have hsub : ((A * q - 1 : ℕ) : ℝ) ≤ ((A * q : ℕ) : ℝ) := by
        exact_mod_cast Nat.sub_le (A * q) 1
      linarith
    · exact hAqR
  have hAq_pos : 1 ≤ A * q := by nlinarith
  have hm_nodvd : ∀ p : ℕ, p.Prime → 3 ≤ p → (p : ℝ) ≤ z → ¬ p ∣ m := by
    intro p hp hp3 hpz hpm
    have hps := hq_sieve p hp hp3 hpz
    dsimp only [m] at hpm
    split_ifs at hpm with he
    · have hpmZ : (p : ℤ) ∣ (A : ℤ) * (q : ℤ) + bq := by
        have hcast : ((A * q - 1 : ℕ) : ℤ) = (A : ℤ) * (q : ℤ) + bq := by
          simp [bq, he]
          omega
        rw [← hcast]
        exact Int.natCast_dvd_natCast.mpr hpm
      exact hps.2 hpmZ
    · rcases hp.dvd_mul.mp hpm with hpA | hpq
      · exact hA_odd p hp hp3 (Int.natCast_dvd_natCast.mpr hpA)
      · exact hps.1 (Int.natCast_dvd_natCast.mpr hpq)
  have hm_fac : ∀ p ∈ m.primeFactors, z < ((p ^ (m.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      by_cases he : Even n
      · have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        have hodd_m : ¬ 2 ∣ m := by
          dsimp only [m]
          rw [if_pos he]
          omega
        exact False.elim (hodd_m hpm)
      · have hm_eq : m = A * q := by simp [m, he]
        have hpow_dvd : 2 ^ k ∣ m := by
          rw [hm_eq]
          exact dvd_mul_right A q
        have hk_le : k ≤ m.factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
        have h2le : A ≤ 2 ^ m.factorization 2 := Nat.pow_le_pow_right (by omega) hk_le
        have h2leR : (A : ℝ) ≤ ((2 ^ m.factorization 2 : ℕ) : ℝ) := by exact_mod_cast h2le
        exact hzA.trans_le h2leR
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        exact hm_nodvd p hp hp3 hle hpm
      have hk1 : 1 ≤ m.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm
      have hpp : p ≤ p ^ m.factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ m.factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  have hm1_fac : ∀ p ∈ (m + 1).primeFactors, z < ((p ^ ((m + 1).factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpm1 := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      by_cases he : Even n
      · have hm1_eq : m + 1 = A * q := by
          dsimp only [m]
          rw [if_pos he]
          omega
        have hpow_dvd : 2 ^ k ∣ m + 1 := by
          rw [hm1_eq]
          exact dvd_mul_right A q
        have hk_le : k ≤ (m + 1).factorization 2 :=
          (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp hpow_dvd
        have h2le : A ≤ 2 ^ (m + 1).factorization 2 := Nat.pow_le_pow_right (by omega) hk_le
        have h2leR : (A : ℝ) ≤ ((2 ^ (m + 1).factorization 2 : ℕ) : ℝ) := by exact_mod_cast h2le
        exact hzA.trans_le h2leR
      · have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        have hodd_m1 : ¬ 2 ∣ m + 1 := by
          dsimp only [m]
          rw [if_neg he]
          omega
        exact False.elim (hodd_m1 hpm1)
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        have hps := hq_sieve p hp hp3 hle
        dsimp only [m] at hpm1
        split_ifs at hpm1 with he
        · have hsub1 : A * q - 1 + 1 = A * q := Nat.sub_add_cancel hAq_pos
          have hpAq : p ∣ A * q := by rwa [hsub1] at hpm1
          rcases hp.dvd_mul.mp hpAq with hpA | hpq
          · exact hA_odd p hp hp3 (Int.natCast_dvd_natCast.mpr hpA)
          · exact hps.1 (Int.natCast_dvd_natCast.mpr hpq)
        · have hpmZ : (p : ℤ) ∣ (A : ℤ) * (q : ℤ) + bq := by
            have hcast : ((A * q + 1 : ℕ) : ℤ) = (A : ℤ) * (q : ℤ) + bq := by
              simp [bq, he]
            rw [← hcast]
            exact Int.natCast_dvd_natCast.mpr hpm1
          exact hps.2 hpmZ
      have hk1 : 1 ≤ (m + 1).factorization p :=
        Nat.Prime.factorization_pos_of_dvd hp (by omega) hpm1
      have hpp : p ≤ p ^ (m + 1).factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ (m + 1).factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  let Xt : ℕ := ⌈(n : ℝ) / ((m : ℝ) + 1)⌉₊
  let Yt : ℕ := (n - 2) / m + 1
  have hn_scale : (n : ℝ) = z ^ ((74 : ℝ) / 5) / c ^ ((74 : ℝ) / 5) := by
    have hz_pow : z ^ ((74 : ℝ) / 5) = c ^ ((74 : ℝ) / 5) * (n : ℝ) := by
      dsimp only [z]
      rw [Real.mul_rpow hc_pos.le (by positivity), ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hz_pow]
    field_simp [hc_pos.ne']
  have hmm1_le : (m : ℝ) * ((m : ℝ) + 1) ≤ 20 * C ^ (2 : ℕ) * z ^ ((158 : ℝ) / 15) := by
    have hm1_le : (m : ℝ) + 1 ≤ 5 * C * z ^ ((79 : ℝ) / 15) := by
      have h1Cz6 : (1 : ℝ) ≤ C * z ^ ((79 : ℝ) / 15) := by
        have : (1 : ℝ) ≤ C := by linarith
        have : (1 : ℝ) ≤ z ^ ((79 : ℝ) / 15) := Real.one_le_rpow (by linarith) (by norm_num)
        nlinarith
      linarith
    calc (m : ℝ) * ((m : ℝ) + 1) ≤ (4 * C * z ^ ((79 : ℝ) / 15)) * (5 * C * z ^ ((79 : ℝ) / 15)) := by gcongr
      _ = 20 * C ^ (2 : ℕ) * (z ^ ((79 : ℝ) / 15) * z ^ ((79 : ℝ) / 15)) := by ring
      _ = 20 * C ^ (2 : ℕ) * z ^ ((158 : ℝ) / 15) := by rw [hz_square]
  have hc_coefficient : 20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5) ≤ 1 / (2 * C) := by
    have h40 : (1 : ℝ) ≤ 40 * C ^ (3 : ℕ) := by nlinarith
    have hc_le1 : c ≤ 1 := by
      dsimp only [c]
      rw [div_le_one (by positivity)]
      exact h40
    have hc_power_le : c ^ ((74 : ℝ) / 5) ≤ c := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
        hc_pos hc_le1 (by norm_num : (1 : ℝ) ≤ 74 / 5)
    calc 20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5) ≤ 20 * C ^ (2 : ℕ) * c := by gcongr
      _ = 1 / (2 * C) := by
        dsimp only [c]
        field_simp
        ring
  have hdiff_ge : C * z ^ ((64 : ℝ) / 15) ≤ (Yt : ℝ) - (Xt : ℝ) := by
    have hYt_gt : ((n : ℝ) - 2) / (m : ℝ) < (Yt : ℝ) := by
      have hm_pos : 0 < m := by omega
      have hdiv : n - 2 < m * ((n - 2) / m + 1) := by
        have := Nat.lt_div_mul_add hm_pos (a := n - 2)
        linarith
      have hdivR : ((n - 2 : ℕ) : ℝ) < (m : ℝ) * (((n - 2) / m + 1 : ℕ) : ℝ) := by
        exact_mod_cast hdiv
      have hn2R : (n : ℝ) - 2 = ((n - 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hn2]
        norm_num
      rw [hn2R]
      exact (div_lt_iff₀' (by positivity)).mpr (by simpa [Yt] using hdivR)
    have hXt_lt : (Xt : ℝ) < (n : ℝ) / ((m : ℝ) + 1) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have hn_gap : 2 * C * z ^ ((64 : ℝ) / 15) ≤ (n : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      rw [hn_scale, div_div]
      have hden_pos : 0 < c ^ ((74 : ℝ) / 5) * ((m : ℝ) * ((m : ℝ) + 1)) := by positivity
      rw [le_div_iff₀ hden_pos]
      calc 2 * C * z ^ ((64 : ℝ) / 15) * (c ^ ((74 : ℝ) / 5) * ((m : ℝ) * ((m : ℝ) + 1)))
          ≤ 2 * C * z ^ ((64 : ℝ) / 15) * (c ^ ((74 : ℝ) / 5) * (20 * C ^ (2 : ℕ) * z ^ ((158 : ℝ) / 15))) := by
            gcongr
        _ = 2 * C * (20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5)) *
            (z ^ ((64 : ℝ) / 15) * z ^ ((158 : ℝ) / 15)) := by ring
        _ = 2 * C * (20 * C ^ (2 : ℕ) * c ^ ((74 : ℝ) / 5)) * z ^ ((74 : ℝ) / 5) := by
          rw [hz_combined]
        _ ≤ 2 * C * (1 / (2 * C)) * z ^ ((74 : ℝ) / 5) := by gcongr
        _ = z ^ ((74 : ℝ) / 5) := by
          field_simp
    have hsub_id : (n : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1) =
        (n : ℝ) / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      have hm10 : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    have h2m : 2 / (m : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by positivity)]
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
      linarith
    have hCz5_ge3 : 3 ≤ C * z ^ ((64 : ℝ) / 15) := by
      have hz5 : 1 ≤ z ^ ((64 : ℝ) / 15) := Real.one_le_rpow (by linarith) (by norm_num)
      nlinarith
    have hpart : ((n : ℝ) - 2) / (m : ℝ) - ((n : ℝ) / ((m : ℝ) + 1) + 1) =
        ((n : ℝ) / (m : ℝ) - (n : ℝ) / ((m : ℝ) + 1)) - 2 / (m : ℝ) - 1 := by ring
    linarith
  have hXY_le : Xt ≤ Yt := by
    have hpos : (0 : ℝ) ≤ (Yt : ℝ) - (Xt : ℝ) := by
      have : 0 ≤ C * z ^ ((64 : ℝ) / 15) := by positivity
      linarith
    exact_mod_cast (sub_nonneg.mp hpos)
  let Lt : ℕ := Yt - Xt
  have hLt_eq : Xt + Lt = Yt := Nat.add_sub_cancel' hXY_le
  have hLtR : C * z ^ ((64 : ℝ) / 15) ≤ (Lt : ℝ) := by
    have : (Lt : ℝ) = (Yt : ℝ) - (Xt : ℝ) := by
      dsimp only [Lt]
      rw [Nat.cast_sub hXY_le]
    linarith
  obtain ⟨t, ht_mem, ht_odd, ht_sieve⟩ :=
    hsieve z Xt Lt (-(m : ℤ)) (n : ℤ) hzC hLtR fun p hp hp3 hpz hdiv => by
      have hpm : p ∣ m := Int.natCast_dvd_natCast.mp (dvd_neg.mp hdiv)
      exact hm_nodvd p hp hp3 hpz hpm
  have ht_ge : Xt ≤ t := (Finset.mem_Ico.mp ht_mem).1
  have ht_lt : t < Yt := by
    rw [← hLt_eq]
    exact (Finset.mem_Ico.mp ht_mem).2
  have hut : n - m * t ≤ t := by
    have h1' : (n : ℝ) / ((m : ℝ) + 1) ≤ (Xt : ℝ) := Nat.le_ceil _
    have h2' : (Xt : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_ge
    have h3' : (n : ℝ) ≤ (t : ℝ) * ((m : ℝ) + 1) := (div_le_iff₀ (by positivity)).mp (h1'.trans h2')
    have h3N : n ≤ (m + 1) * t := by exact_mod_cast (by linarith : (n : ℝ) ≤ ((m : ℝ) + 1) * (t : ℝ))
    have h3N' : n ≤ m * t + t := by linarith
    omega
  have hmt_le : m * t ≤ n - 2 := by
    have htle : t ≤ (n - 2) / m := by omega
    calc m * t ≤ m * ((n - 2) / m) := Nat.mul_le_mul_left m htle
      _ ≤ n - 2 := Nat.mul_div_le (n - 2) m
  let u : ℕ := n - m * t
  have hu2 : 2 ≤ u := by omega
  have ht2 : 2 ≤ t := by omega
  have hn_eq : n = m * t + u := by omega
  have ht_fac : ∀ p ∈ t.primeFactors, z < ((p ^ (t.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpt := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      exact False.elim (ht_odd hpt)
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        exact (ht_sieve p hp hp3 hle).1 (Int.natCast_dvd_natCast.mpr hpt)
      have hk1 : 1 ≤ t.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpt
      have hpp : p ≤ p ^ t.factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ t.factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  have hu_odd : ¬ 2 ∣ u := by
    by_cases he : Even n
    · have hm_odd : ¬ 2 ∣ m := by
        have h2A : 2 ∣ A := dvd_pow_self 2 (by omega)
        have h2Aq : 2 ∣ A * q := dvd_mul_of_dvd_left h2A q
        dsimp only [m]
        rw [if_pos he]
        omega
      obtain ⟨r, hr⟩ := he
      intro h2u
      have h2mt : 2 ∣ m * t := by omega
      rcases Nat.Prime.dvd_mul Nat.prime_two |>.mp h2mt with h2m | h2t
      · exact hm_odd h2m
      · exact ht_odd h2t
    · have hm_even : 2 ∣ m := by
        dsimp only [m]
        rw [if_neg he]
        exact dvd_mul_of_dvd_left (dvd_pow_self 2 (by omega)) q
      intro h2u
      have h2mt : 2 ∣ m * t := dvd_mul_of_dvd_left hm_even t
      have h2n : 2 ∣ n := by
        rw [hn_eq]
        exact dvd_add h2mt h2u
      exact he (even_iff_two_dvd.mpr h2n)
  have hu_fac : ∀ p ∈ u.primeFactors, z < ((p ^ (u.factorization p) : ℕ) : ℝ) := by
    intro p hp_mem
    have hp := (Nat.mem_primeFactors.mp hp_mem).1
    have hpu := (Nat.mem_primeFactors.mp hp_mem).2.1
    by_cases hp2 : p = 2
    · subst hp2
      exact False.elim (hu_odd hpu)
    · have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hzp : z < (p : ℝ) := by
        by_contra hle
        push Not at hle
        have hpuZ : (p : ℤ) ∣ -(m : ℤ) * (t : ℤ) + (n : ℤ) := by
          have hcast : (u : ℤ) = -(m : ℤ) * (t : ℤ) + (n : ℤ) := by
            dsimp only [u]
            zify [show m * t ≤ n by omega]
            ring
          rw [← hcast]
          exact Int.natCast_dvd_natCast.mpr hpu
        exact (ht_sieve p hp hp3 hle).2 hpuZ
      have hk1 : 1 ≤ u.factorization p := Nat.Prime.factorization_pos_of_dvd hp (by omega) hpu
      have hpp : p ≤ p ^ u.factorization p := Nat.le_self_pow (by omega) p
      have hppR : (p : ℝ) ≤ ((p ^ u.factorization p : ℕ) : ℝ) := by exact_mod_cast hpp
      exact hzp.trans_le hppR
  let s : ℕ := ⌊z⌋₊ - 2
  have hs_le_z : (s : ℝ) + 2 ≤ z := by
    have hfl6 : 6 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz6)
    have hs2 : s + 2 = ⌊z⌋₊ := by omega
    have hs2R : (s : ℝ) + 2 = (⌊z⌋₊ : ℝ) := by exact_mod_cast hs2
    rw [hs2R]
    exact Nat.floor_le (by linarith)
  have hmac := macneish h1 h2
  have hsm : s ≤ Erdos724.maxMOLS m := by
    refine hmac m (by omega) s fun p hp => ?_
    have hz_lt := hm_fac p hp
    have hltR : (s : ℝ) + 1 < ((p ^ m.factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 1 < p ^ m.factorization p := by exact_mod_cast hltR
    omega
  have hsm1 : s ≤ Erdos724.maxMOLS (m + 1) := by
    refine hmac (m + 1) (by omega) s fun p hp => ?_
    have hz_lt := hm1_fac p hp
    have hltR : (s : ℝ) + 1 < ((p ^ (m + 1).factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 1 < p ^ (m + 1).factorization p := by exact_mod_cast hltR
    omega
  have hst : s + 1 ≤ Erdos724.maxMOLS t := by
    refine hmac t ht2 (s + 1) fun p hp => ?_
    have hz_lt := ht_fac p hp
    have hltR : (s : ℝ) + 2 < ((p ^ t.factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 2 < p ^ t.factorization p := by exact_mod_cast hltR
    omega
  have hsu : s ≤ Erdos724.maxMOLS u := by
    refine hmac u hu2 s fun p hp => ?_
    have hz_lt := hu_fac p hp
    have hltR : (s : ℝ) + 1 < ((p ^ u.factorization p : ℕ) : ℝ) := by linarith
    have hltN : s + 1 < p ^ u.factorization p := by exact_mod_cast hltR
    omega
  have hs_n : s ≤ Erdos724.maxMOLS n := by
    rw [hn_eq]
    exact h3 m t u s (by omega) (by omega) hut hsm hsm1 hst hsu
  have hs_lower : c / 2 * (n : ℝ) ^ ((1 : ℝ) / 14.8) ≤ (s : ℝ) := by
    have hfl6 : 6 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz6)
    have hs2 : s + 2 = ⌊z⌋₊ := by omega
    have hs2R : (s : ℝ) + 2 = (⌊z⌋₊ : ℝ) := by exact_mod_cast hs2
    have hfl_gt : z - 1 < (⌊z⌋₊ : ℝ) := Nat.sub_one_lt_floor z
    have h1' : z - 3 < (s : ℝ) := by linarith
    have h2' : c / 2 * (n : ℝ) ^ ((1 : ℝ) / 14.8) = z / 2 := by
      dsimp only [z]
      ring
    linarith
  have hs_nR : (s : ℝ) ≤ (Erdos724.maxMOLS n : ℝ) := by exact_mod_cast hs_n
  exact hs_lower.trans hs_nR

end OMA.R_Erdos724_erdos_724_variants_beth_R1

namespace OMABeth

open OMA.R_Erdos724_erdos_724_variants_beth_R1

theorem beth_of_interval_sieve (hsieve : H4) : type_of% @Erdos724.erdos_724.variants.beth :=
  main O2W.prime_power_bound O2W2.macNeish W724.wilson hsieve

end OMABeth

end

section

/-
Mertensの初等的評価はgreen-notesによるWilson H4の第2節を再利用した。
https://github.com/lefttosolve2/open-math-agents/pull/4718
区間のオイラー積では、下端に依存する誤差を残して任意のεを選べるようにする。
-/

namespace BethMertens

open Finset Filter
/- ## Section 2: Elementary Mertens First Theorem and Prime Product Bound -/

private lemma log_two_ge_half : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.add_one_le_exp (-1 / 2 : ℝ)
  have h1 : (1 / 2 : ℝ) ≤ (Real.exp (1 / 2))⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.exp_neg] at h
    linarith
  have h2 : Real.exp (1 / 2) ≤ 2 := by
    calc Real.exp (1 / 2) = ((Real.exp (1 / 2))⁻¹)⁻¹ := (inv_inv _).symm
      _ ≤ (1 / 2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h1
      _ = 2 := by norm_num
  calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
    _ ≤ Real.log 2 := Real.log_le_log (Real.exp_pos _) h2

private lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

private lemma log_factorial_bounds : ∀ n : ℕ, 1 ≤ n →
    (n : ℝ) * Real.log n - n ≤ Real.log (Nat.factorial n : ℝ) ∧
    Real.log (Nat.factorial n : ℝ) ≤ (n + 1 : ℝ) * Real.log (n + 1) - n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [Nat.factorial_one, Nat.cast_one, Real.log_one, one_mul, zero_sub]
    constructor
    · linarith
    · have := log_two_ge_half
      norm_num
      linarith
  | succ n hn ih =>
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1_pos : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have hn2_pos : (0 : ℝ) < (n : ℝ) + 2 := by linarith
    have hfac : Real.log (Nat.factorial (n + 1) : ℝ) = Real.log (n + 1 : ℝ) + Real.log (Nat.factorial n : ℝ) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul]
      · push_cast; rfl
      · positivity
      · exact_mod_cast (Nat.factorial_pos n).ne'
    have h_ub_step : (n : ℝ) * (Real.log (n + 1) - Real.log n) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div hn1_pos.ne' hn_pos.ne'] at h
      have : (((n : ℝ) + 1) / n - 1) * n = 1 := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right h hn_pos.le]
    have h_lb_step : 1 ≤ ((n : ℝ) + 2) * (Real.log (n + 2) - Real.log (n + 1)) := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < ((n : ℝ) + 2) / (n + 1) by positivity)
      rw [Real.log_div hn2_pos.ne' hn1_pos.ne', inv_div] at h
      have : (1 - ((n : ℝ) + 1) / (n + 2)) * ((n : ℝ) + 2) = 1 := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right h hn2_pos.le]
    rw [hfac]
    push_cast
    rw [show ((n : ℝ) + 1 + 1) = (n : ℝ) + 2 by ring]
    constructor <;> linarith [ih.1, ih.2]

private lemma inv_sqrt_sub_ge (m : ℕ) (hm : 2 ≤ m) :
    (1 : ℝ) / (2 * (m : ℝ) * Real.sqrt m) ≤
      1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ) := by
  have hm1_pos : (0 : ℝ) < ((m - 1 : ℕ) : ℝ) := by
    have : 1 ≤ m - 1 := by omega
    exact_mod_cast this
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  set u := Real.sqrt ((m - 1 : ℕ) : ℝ)
  set v := Real.sqrt (m : ℝ)
  have hu_pos : 0 < u := Real.sqrt_pos.mpr hm1_pos
  have hv_pos : 0 < v := Real.sqrt_pos.mpr hm_pos
  have huv_sq : v ^ 2 - u ^ 2 = 1 := by
    rw [Real.sq_sqrt hm_pos.le, Real.sq_sqrt hm1_pos.le]
    have : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
    linarith
  have hle : u ≤ v := Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le m 1)
  have hsub : v - u = 1 / (v + u) := by
    have hvup : v + u ≠ 0 := by linarith
    field_simp
    linarith
  have h1 : 1 / u - 1 / v = 1 / (u * v * (v + u)) := by
    rw [div_sub_div _ _ hu_pos.ne' hv_pos.ne', one_mul, mul_one, hsub]
    field_simp
  rw [h1]
  have hden : u * v * (v + u) ≤ 2 * (m : ℝ) * v := by
    have hvu : v + u ≤ 2 * v := by linarith
    calc u * v * (v + u) ≤ v * v * (2 * v) := by gcongr
      _ = 2 * v ^ 2 * v := by ring
      _ = 2 * (m : ℝ) * v := by rw [Real.sq_sqrt hm_pos.le]
  exact one_div_le_one_div_of_le (by positivity) hden

private lemma sum_log_prime_div_mul_sub_one_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1)) ≤ 8 := by
  have hterm : ∀ p ∈ Nat.primesLE n,
      Real.log p / ((p : ℝ) * (p - 1)) ≤
        8 * (1 / Real.sqrt ((p - 1 : ℕ) : ℝ) - 1 / Real.sqrt (p : ℝ)) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hp2 : 2 ≤ p := hp_prime.two_le
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hsqrt_pos : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp_pos
    have hlog : Real.log p ≤ 2 * Real.sqrt p := by
      have h := Real.log_le_sub_one_of_pos hsqrt_pos
      have hsq : Real.log p = 2 * Real.log (Real.sqrt p) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ← Real.log_pow, Real.sq_sqrt hp_pos.le]
      linarith
    have hden : (p : ℝ) ^ 2 / 2 ≤ (p : ℝ) * (p - 1) := by
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      nlinarith
    calc Real.log p / ((p : ℝ) * (p - 1))
        ≤ (2 * Real.sqrt p) / ((p : ℝ) ^ 2 / 2) := by
          apply div_le_div₀ (by positivity) hlog (by positivity) hden
      _ = 4 / ((p : ℝ) * Real.sqrt p) := by
          have : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp_pos.le
          field_simp
          nlinarith
      _ = 8 * (1 / (2 * (p : ℝ) * Real.sqrt p)) := by ring
      _ ≤ 8 * (1 / Real.sqrt ((p - 1 : ℕ) : ℝ) - 1 / Real.sqrt (p : ℝ)) := by
          gcongr
          exact inv_sqrt_sub_ge p hp2
  have hsub : Nat.primesLE n ⊆ Finset.Icc 2 n := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesLE hp).two_le, Nat.le_of_mem_primesLE hp⟩
  have hnonneg : ∀ m ∈ Finset.Icc 2 n,
      0 ≤ 8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) := by
    intro m hm
    have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hm).1
    have h1 := inv_sqrt_sub_ge m hm2
    have h2 : (0 : ℝ) ≤ 1 / (2 * (m : ℝ) * Real.sqrt m) := by positivity
    linarith
  calc ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1))
      ≤ ∑ p ∈ Nat.primesLE n, 8 * (1 / Real.sqrt ((p - 1 : ℕ) : ℝ) - 1 / Real.sqrt (p : ℝ)) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ m ∈ Finset.Icc 2 n, 8 * (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun m hm _ => hnonneg m hm
    _ = 8 * ∑ m ∈ Finset.Icc 2 n, (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ 8 * 1 := by
        gcongr
        cases n with
        | zero => simp
        | succ n' =>
          cases n' with
          | zero => simp
          | succ m' =>
            have htel : ∀ k : ℕ, 1 ≤ k →
                ∑ m ∈ Finset.Icc 2 (k + 1),
                  (1 / Real.sqrt ((m - 1 : ℕ) : ℝ) - 1 / Real.sqrt (m : ℝ)) =
                1 - 1 / Real.sqrt ((k + 1 : ℕ) : ℝ) := by
              intro k hk
              induction k, hk using Nat.le_induction with
              | base => simp
              | succ k hk ih =>
                rw [Finset.sum_Icc_succ_top (by omega), ih]
                simp only [Nat.add_sub_cancel]
                ring
            rw [htel (m' + 1) (by omega)]
            have : (0 : ℝ) ≤ 1 / Real.sqrt (((m' + 1 + 1 : ℕ) : ℝ)) := by positivity
            linarith
    _ = 8 := by ring

lemma mertens_first (n : ℕ) (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ) - Real.log n| ≤ 9 := by
  have hfac_log : Real.log (Nat.factorial n : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((Nat.factorial n).factorization p : ℝ) * Real.log p := by
    have hpos : Nat.factorial n ≠ 0 := Nat.factorial_ne_zero n
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hpos]
    rw [Finsupp.prod, Nat.cast_prod, Real.log_prod]
    · have hpf : (Nat.factorial n).factorization.support = Nat.primesLE n := by
        ext p
        rw [Nat.support_factorization, Nat.mem_primeFactors, Nat.mem_primesLE]
        refine ⟨fun ⟨hp, hd, _⟩ => ⟨hp.dvd_factorial.mp hd, hp⟩,
               fun ⟨hle, hp⟩ => ⟨hp, hp.dvd_factorial.mpr hle, hpos⟩⟩
      rw [hpf]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Nat.cast_pow, Real.log_pow]
    · intro p hp
      have hp_prime := (Nat.mem_primeFactors.mp (by rwa [← Nat.support_factorization])).1
      exact_mod_cast pow_ne_zero _ hp_prime.ne_zero
  have hsum_k : ∀ p ∈ Nat.primesLE n,
      ((Nat.factorial n).factorization p : ℝ) =
        (n / p : ℕ) + ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) := by
    intro p hp
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hlog : Nat.log p n < n + 1 := Nat.lt_succ_of_le (Nat.log_le_self p n)
    rw [Nat.factorization_factorial hp_prime hlog]
    have hsplit : ∑ i ∈ Finset.Ico 1 (n + 1), n / p ^ i =
        n / p + ∑ i ∈ Finset.Icc 2 (n + 1), n / p ^ i := by
      have h1 : Finset.Ico 1 (n + 1) = insert 1 (Finset.Ico 2 (n + 1)) := by
        ext x; simp; omega
      have h3 : ∑ i ∈ Finset.Icc 2 (n + 1), n / p ^ i =
          ∑ i ∈ Finset.Ico 2 (n + 1), n / p ^ i + n / p ^ (n + 1) := by
        have : Finset.Icc 2 (n + 1) = insert (n + 1) (Finset.Ico 2 (n + 1)) := by
          ext x; simp; omega
        rw [this, Finset.sum_insert (by simp), add_comm]
      have hzero : n / p ^ (n + 1) = 0 := by
        apply Nat.div_eq_of_lt
        have : 2 ≤ p := hp_prime.two_le
        calc n < 2 ^ (n + 1) := (Nat.lt_pow_succ_log_self (by norm_num) n).trans_le
              (Nat.pow_le_pow_right (by norm_num) (by have := Nat.log_le_self 2 n; omega))
          _ ≤ p ^ (n + 1) := Nat.pow_le_pow_left this _
      rw [h1, Finset.sum_insert (by simp), pow_one, h3, hzero, add_zero]
    rw [hsplit]
    push_cast
    rfl
  set S : ℝ := ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)
  have hS_lower : (n : ℝ) * S - Chebyshev.theta n ≤ Real.log (Nat.factorial n : ℝ) := by
    rw [hfac_log, Chebyshev.theta_eq_sum_primesLE_log, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp_prime := Nat.prime_of_mem_primesLE hp
    have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
    have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
    have hdiv : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
      have hmod : (n / p : ℕ) * p + n % p = n := Nat.div_add_mod' n p
      have hmod_lt : ((n % p : ℕ) : ℝ) < p := by exact_mod_cast Nat.mod_lt n hp_prime.pos
      have hmodR : ((n / p : ℕ) : ℝ) * p + ((n % p : ℕ) : ℝ) = n := by exact_mod_cast hmod
      have heq : (n : ℝ) / p = ((n / p : ℕ) : ℝ) + ((n % p : ℕ) : ℝ) / p := by field_simp; linarith
      have hlt1 : ((n % p : ℕ) : ℝ) / p < 1 := (div_lt_one hp_pos).mpr hmod_lt
      linarith
    have hfac_ge : ((n / p : ℕ) : ℝ) ≤ ((Nat.factorial n).factorization p : ℝ) := by
      rw [hsum_k p hp]
      have : 0 ≤ ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) :=
        Finset.sum_nonneg fun _ _ => by positivity
      linarith
    have := mul_le_mul_of_nonneg_right (hdiv.trans hfac_ge) hlog_nn
    linarith [show (n : ℝ) * (Real.log p / p) = ((n : ℝ) / p) * Real.log p by ring]
  have hS_upper : Real.log (Nat.factorial n : ℝ) ≤ (n : ℝ) * S + 8 * n := by
    have h1 : Real.log (Nat.factorial n : ℝ) ≤ (n : ℝ) * S +
        (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * (p - 1)) := by
      rw [hfac_log, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun p hp => ?_
      have hp_prime := Nat.prime_of_mem_primesLE hp
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp_prime.pos
      have hp1_pos : (0 : ℝ) < (p : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p := by exact_mod_cast hp_prime.two_le
        linarith
      have hlog_nn : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp_prime.one_le)
      rw [hsum_k p hp, add_mul]
      have hterm1 : ((n / p : ℕ) : ℝ) * Real.log p ≤ (n : ℝ) * (Real.log p / p) := by
        have hdiv : ((n / p : ℕ) : ℝ) ≤ (n : ℝ) / p := by
          rw [le_div_iff₀ hp_pos]
          exact_mod_cast Nat.div_mul_le_self n p
        calc ((n / p : ℕ) : ℝ) * Real.log p ≤ ((n : ℝ) / p) * Real.log p :=
              mul_le_mul_of_nonneg_right hdiv hlog_nn
          _ = (n : ℝ) * (Real.log p / p) := by ring
      have hterm2 : (∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ)) * Real.log p ≤
          (n : ℝ) * (Real.log p / ((p : ℝ) * (p - 1))) := by
        have hgeom : ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) ≤
            (n : ℝ) / ((p : ℝ) * (p - 1)) := by
          have hsub : ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ) ≤
              (n : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_le_sum fun k _ => ?_
            rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hp_pos k)]
            exact_mod_cast Nat.div_mul_le_self n (p ^ k)
          have hgeom_sum : ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k ≤
              1 / ((p : ℝ) * (p - 1)) := by
            have hshift : ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k =
                (1 / (p : ℝ)) ^ 2 * ∑ j ∈ Finset.range n, (1 / (p : ℝ)) ^ j := by
              rw [Finset.mul_sum]
              refine Finset.sum_bij (fun k _ => k - 2) ?_ ?_ ?_ ?_
              · intro k hk; rw [Finset.mem_Icc] at hk; rw [Finset.mem_range]; omega
              · intro a ha b hb hab; rw [Finset.mem_Icc] at ha hb; omega
              · intro j hj; rw [Finset.mem_range] at hj
                refine ⟨j + 2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
              · intro k hk
                rw [Finset.mem_Icc] at hk
                rw [← pow_add, show 2 + (k - 2) = k by omega]
            rw [hshift]
            have hr_lt : (1 / (p : ℝ)) < 1 := by
              rw [div_lt_one hp_pos]
              exact_mod_cast hp_prime.one_lt
            have hg2 : ∑ j ∈ Finset.range n, (1 / (p : ℝ)) ^ j ≤ 1 / (1 - 1 / (p : ℝ)) := by
              rw [geom_sum_eq hr_lt.ne]
              have hnum : 0 ≤ (1 / (p : ℝ)) ^ n := by positivity
              have h1m : 0 < 1 - 1 / (p : ℝ) := by linarith
              have hs1 : (1 / (p : ℝ)) ^ n - 1 = -(1 - (1 / (p : ℝ)) ^ n) := by ring
              have hs2 : 1 / (p : ℝ) - 1 = -(1 - 1 / (p : ℝ)) := by ring
              rw [hs1, hs2, neg_div_neg_eq]
              exact div_le_div_of_nonneg_right (by linarith) h1m.le
            calc (1 / (p : ℝ)) ^ 2 * ∑ j ∈ Finset.range n, (1 / (p : ℝ)) ^ j
                ≤ (1 / (p : ℝ)) ^ 2 * (1 / (1 - 1 / (p : ℝ))) := by gcongr
              _ = 1 / ((p : ℝ) * (p - 1)) := by field_simp
          calc ∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ)
              ≤ (n : ℝ) * ∑ k ∈ Finset.Icc 2 (n + 1), (1 / (p : ℝ)) ^ k := hsub
            _ ≤ (n : ℝ) * (1 / ((p : ℝ) * (p - 1))) := by gcongr
            _ = (n : ℝ) / ((p : ℝ) * (p - 1)) := by ring
        calc (∑ k ∈ Finset.Icc 2 (n + 1), ((n / p ^ k : ℕ) : ℝ)) * Real.log p
            ≤ ((n : ℝ) / ((p : ℝ) * (p - 1))) * Real.log p :=
              mul_le_mul_of_nonneg_right hgeom hlog_nn
          _ = (n : ℝ) * (Real.log p / ((p : ℝ) * (p - 1))) := by ring
      linarith
    have h2 := sum_log_prime_div_mul_sub_one_le n
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hfac_b := log_factorial_bounds n hn
  have hth := Chebyshev.theta_le_log4_mul_x (show (0 : ℝ) ≤ n by positivity)
  have hth2 : Chebyshev.theta n ≤ 2 * (n : ℝ) := by
    have := log_four_le_two
    nlinarith [show (0 : ℝ) ≤ n by positivity]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlow : (n : ℝ) * Real.log n - 9 * n ≤ (n : ℝ) * S := by linarith
  have hup : (n : ℝ) * S ≤ (n : ℝ) * Real.log n + 4 * n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h_diff : ((n : ℝ) + 1) * Real.log (n + 1) - n ≤ (n : ℝ) * Real.log n + 1 + Real.log (n + 1) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      rw [Real.log_div (by linarith) hn_pos.ne'] at h
      have : (((n : ℝ) + 1) / n - 1) * n = 1 := by field_simp; ring
      nlinarith [mul_le_mul_of_nonneg_right h hn_pos.le]
    have hlog_n1 : Real.log ((n : ℝ) + 1) ≤ (n : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < n + 1)
      linarith
    linarith
  rw [abs_le]
  constructor <;> nlinarith

private lemma sum_Icc_by_parts (A B : ℕ) (hAB : A + 1 ≤ B) (S f : ℕ → ℝ) :
    ∑ n ∈ Finset.Icc (A + 1) B, (S n - S (n - 1)) * f n =
      S B * f B - S A * f (A + 1) +
        ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (f n - f (n + 1)) := by
  induction B, hAB using Nat.le_induction with
  | base =>
    have h2 : A + 1 - 1 < A + 1 := by omega
    rw [Finset.Icc_self, Finset.sum_singleton, Finset.Icc_eq_empty_of_lt h2, Finset.sum_empty]
    simp only [Nat.add_sub_cancel]
    ring
  | succ B hAB ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have hB1 : (B + 1 - 1 : ℕ) = B := by omega
    have hsumB : ∑ n ∈ Finset.Icc (A + 1) B, S n * (f n - f (n + 1)) =
        ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (f n - f (n + 1)) +
          S B * (f B - f (B + 1)) := by
      have hB_eq : B = (B - 1) + 1 := by omega
      conv_lhs => rw [hB_eq, Finset.sum_Icc_succ_top (by omega)]
      rw [show (B - 1) + 1 = B by omega]
    rw [hB1, hsumB]
    ring

private lemma sum_inv_prime_Icc_le (A B : ℕ) (hA : 3 ≤ A) (hAB : A ≤ B) :
    ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, (1 : ℝ) / p ≤
      Real.log (Real.log B / Real.log A) + 19 / Real.log A := by
  rcases eq_or_lt_of_le hAB with rfl | hlt
  · have hlogB : Real.log (A : ℝ) > 0 := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
    have : Finset.Icc (A + 1) A = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
    rw [this, Finset.filter_empty, Finset.sum_empty, div_self hlogB.ne', Real.log_one, zero_add]
    positivity
  set S : ℕ → ℝ := fun n => ∑ p ∈ Nat.primesLE n, Real.log p / (p : ℝ)
  have hdiff : ∀ n : ℕ, 2 ≤ n →
      S n - S (n - 1) = if n.Prime then Real.log n / (n : ℝ) else 0 := by
    intro n hn
    have hsub : Nat.primesLE n =
        if n.Prime then insert n (Nat.primesLE (n - 1)) else Nat.primesLE (n - 1) := by
      ext p
      simp only [Nat.mem_primesLE]
      split_ifs with hnp
      · rw [Finset.mem_insert, Nat.mem_primesLE]
        constructor
        · rintro ⟨hle, hp⟩
          rcases eq_or_lt_of_le hle with rfl | hlt'
          · exact Or.inl rfl
          · exact Or.inr ⟨by omega, hp⟩
        · rintro (rfl | ⟨hle, hp⟩)
          · exact ⟨le_rfl, hnp⟩
          · exact ⟨by omega, hp⟩
      · constructor
        · rintro ⟨hle, hp⟩
          rw [Nat.mem_primesLE]
          refine ⟨?_, hp⟩
          by_contra hnot
          have : p = n := by omega
          subst this
          exact hnp hp
        · intro h
          rw [Nat.mem_primesLE] at h
          exact ⟨by omega, h.2⟩
    dsimp only [S]
    rw [hsub]
    split_ifs with hnp
    · rw [Finset.sum_insert]
      · simp
      · simp [Nat.mem_primesLE]; omega
    · simp
  have hsum_eq : ∑ p ∈ (Finset.Icc (A + 1) B).filter Nat.Prime, (1 : ℝ) / p =
      ∑ n ∈ Finset.Icc (A + 1) B, (S n - S (n - 1)) * (1 / Real.log n) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn2 : 2 ≤ n := by rw [Finset.mem_Icc] at hn; omega
    rw [hdiff n hn2]
    split_ifs with hnp
    · have hlog_ne : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast hnp.one_lt)).ne'
      field_simp
    · simp
  rw [hsum_eq, sum_Icc_by_parts A B (by omega) S (fun n => 1 / Real.log n)]
  have hlogA_pos : 0 < Real.log (A : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < A))
  have hlogA1_pos : 0 < Real.log ((A + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < A + 1))
  have hlogB_pos : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < B))
  have hlogA_le_A1 : Real.log (A : ℝ) ≤ Real.log ((A + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast (by omega : A ≤ A + 1))
  have hSB : S B * (1 / Real.log B) ≤ 1 + 9 / Real.log B := by
    have hm := (abs_le.mp (mertens_first B (by omega))).2
    have h1 := div_le_div_of_nonneg_right (by linarith : S B ≤ Real.log B + 9) hlogB_pos.le
    rw [add_div, div_self hlogB_pos.ne'] at h1
    linarith [show S B * (1 / Real.log B) = S B / Real.log B by ring]
  have hSA : - (S A * (1 / Real.log ((A + 1 : ℕ) : ℝ))) ≤
      - Real.log A / Real.log ((A + 1 : ℕ) : ℝ) + 9 / Real.log ((A + 1 : ℕ) : ℝ) := by
    have hm := (abs_le.mp (mertens_first A (by omega))).1
    have h1 := div_le_div_of_nonneg_right (by linarith : Real.log A - 9 ≤ S A) hlogA1_pos.le
    rw [sub_div] at h1
    rw [neg_div]
    linarith [show S A * (1 / Real.log ((A + 1 : ℕ) : ℝ)) = S A / Real.log ((A + 1 : ℕ) : ℝ) by ring]
  have hmid : ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) +
        9 * (1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log B) := by
    have hterm : ∀ n ∈ Finset.Icc (A + 1) (B - 1),
        S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) +
            9 * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) := by
      intro n hn
      have hn3 : 3 ≤ n := by rw [Finset.mem_Icc] at hn; omega
      have hlogn_pos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have hlogn1_pos : 0 < Real.log ((n + 1 : ℕ) : ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < n + 1))
      have hdiff_nn : 0 ≤ 1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ) := by
        apply sub_nonneg.mpr
        apply one_div_le_one_div_of_le hlogn_pos
        exact Real.log_le_log (by positivity) (by push_cast; linarith)
      have hm := (abs_le.mp (mertens_first n (by omega))).2
      have h1 : S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          (Real.log n + 9) * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by linarith) hdiff_nn
      have h2 : Real.log n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) ≤
          Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ)) := by
        have h_log := Real.one_sub_inv_le_log_of_pos
          (show 0 < Real.log ((n + 1 : ℕ) : ℝ) / Real.log n by positivity)
        rw [Real.log_div hlogn1_pos.ne' hlogn_pos.ne', inv_div] at h_log
        have h_eq : Real.log n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
            1 - Real.log n / Real.log ((n + 1 : ℕ) : ℝ) := by
          field_simp
        linarith
      linarith
    have htel_log : ∑ n ∈ Finset.Icc (A + 1) (B - 1),
        (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) =
        Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) := by
      rw [Real.log_div hlogB_pos.ne' hlogA1_pos.ne']
      rcases eq_or_lt_of_le (show A + 1 ≤ B by omega) with h_eq | h_lt
      · have : B - 1 < A + 1 := by omega
        rw [Finset.Icc_eq_empty_of_lt this, Finset.sum_empty, h_eq, sub_self]
      · have hB_eq : B - 1 + 1 = B := by omega
        have hind : ∀ k : ℕ, A + 1 ≤ k →
            ∑ n ∈ Finset.Icc (A + 1) k,
              (Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) =
            Real.log (Real.log ((k + 1 : ℕ) : ℝ)) - Real.log (Real.log ((A + 1 : ℕ) : ℝ)) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ k hk ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            ring
        rw [hind (B - 1) (by omega), hB_eq]
    have htel_inv : ∑ n ∈ Finset.Icc (A + 1) (B - 1), (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
        1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log B := by
      rcases eq_or_lt_of_le (show A + 1 ≤ B by omega) with h_eq | h_lt
      · have : B - 1 < A + 1 := by omega
        rw [Finset.Icc_eq_empty_of_lt this, Finset.sum_empty, h_eq, sub_self]
      · have hB_eq : B - 1 + 1 = B := by omega
        have hind : ∀ k : ℕ, A + 1 ≤ k →
            ∑ n ∈ Finset.Icc (A + 1) k, (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ)) =
            1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log ((k + 1 : ℕ) : ℝ) := by
          intro k hk
          induction k, hk using Nat.le_induction with
          | base => simp
          | succ k hk ih =>
            rw [Finset.sum_Icc_succ_top (by omega), ih]
            ring
        rw [hind (B - 1) (by omega)]
        congr 1; simp [hB_eq]
    calc ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ))
        ≤ ∑ n ∈ Finset.Icc (A + 1) (B - 1),
            ((Real.log (Real.log ((n + 1 : ℕ) : ℝ)) - Real.log (Real.log (n : ℝ))) +
              9 * (1 / Real.log n - 1 / Real.log ((n + 1 : ℕ) : ℝ))) := Finset.sum_le_sum hterm
      _ = Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) +
            9 * (1 / Real.log ((A + 1 : ℕ) : ℝ) - 1 / Real.log B) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, htel_log, htel_inv]
  have hlog_mono : Real.log (Real.log B / Real.log ((A + 1 : ℕ) : ℝ)) ≤
      Real.log (Real.log B / Real.log A) := by
    apply Real.log_le_log (by positivity)
    exact div_le_div_of_nonneg_left hlogB_pos.le hlogA_pos hlogA_le_A1
  have h_end : 1 - Real.log A / Real.log ((A + 1 : ℕ) : ℝ) ≤ 1 / Real.log A := by
    have hlog1 : Real.log ((A + 1 : ℕ) : ℝ) - Real.log A ≤ 1 / (A : ℝ) := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((A : ℝ) + 1) / A by positivity)
      rw [Real.log_div (by positivity) (by positivity)] at h
      push_cast
      linarith [show (((A : ℝ) + 1) / A - 1) = 1 / A by field_simp; ring]
    have h1 : 1 - Real.log A / Real.log ((A + 1 : ℕ) : ℝ) =
        (Real.log ((A + 1 : ℕ) : ℝ) - Real.log A) / Real.log ((A + 1 : ℕ) : ℝ) := by
      field_simp
    rw [h1]
    calc (Real.log ((A + 1 : ℕ) : ℝ) - Real.log A) / Real.log ((A + 1 : ℕ) : ℝ)
        ≤ (1 / (A : ℝ)) / Real.log A :=
          div_le_div₀ (by positivity) hlog1 hlogA_pos hlogA_le_A1
      _ ≤ 1 / Real.log A := by
          apply div_le_div_of_nonneg_right _ hlogA_pos.le
          have : (1 : ℝ) ≤ A := by exact_mod_cast (by omega : 1 ≤ A)
          rw [div_le_one (by positivity)]; exact this
  have h18 : 18 / Real.log ((A + 1 : ℕ) : ℝ) ≤ 18 / Real.log A :=
    div_le_div_of_nonneg_left (by norm_num) hlogA_pos hlogA_le_A1
  rw [mul_sub, mul_one_div, mul_one_div] at hmid
  have h9 : 9 / Real.log ((A + 1 : ℕ) : ℝ) + 9 / Real.log ((A + 1 : ℕ) : ℝ) =
      18 / Real.log ((A + 1 : ℕ) : ℝ) := by ring
  rw [neg_div] at hSA
  have h19 : 1 / Real.log (A : ℝ) + 18 / Real.log (A : ℝ) = 19 / Real.log (A : ℝ) := by ring
  have hsum_cast : (∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n + 1 : ℕ) : ℝ))) =
      ∑ n ∈ Finset.Icc (A + 1) (B - 1), S n * (1 / Real.log (n : ℝ) - 1 / Real.log ((n : ℝ) + 1)) := by
    refine Finset.sum_congr rfl fun n _ => by push_cast; rfl
  linarith

private lemma neg_log_one_sub_le {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    -Real.log (1 - t) ≤ t + 2 * t ^ 2 := by
  have h1t_pos : 0 < 1 - t := by linarith
  have h := Real.one_sub_inv_le_log_of_pos h1t_pos
  have h2 : t / (1 - t) ≤ t + 2 * t ^ 2 := by
    rw [div_le_iff₀ h1t_pos]
    nlinarith [sq_nonneg t]
  have h3 : -Real.log (1 - t) ≤ t / (1 - t) := by
    have : 1 - (1 - t)⁻¹ = -(t / (1 - t)) := by field_simp; ring
    linarith
  linarith

theorem prod_two_div_interval_explicit {x y : ℝ} (hx : 4 ≤ x) (hxy : x ≤ y) :
    ∏ p ∈ (Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 - 2 / (p : ℝ))⁻¹ ≤
      Real.exp (48 / Real.log (⌊x⌋₊ : ℝ)) * (Real.log y / Real.log x) ^ 2 := by
  have hx_pos : 0 < x := by linarith
  have hy_pos : 0 < y := by linarith
  have hA_ge_4 : 4 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hA_le_B : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hA_pos : 0 < (⌊x⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊x⌋₊)
  have hB_pos : 0 < (⌊y⌋₊ : ℝ) := by exact_mod_cast (by omega : 0 < ⌊y⌋₊)
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogy_pos : 0 < Real.log y := Real.log_pos (by linarith)
  have hlogA_pos : 0 < Real.log (⌊x⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊x⌋₊))
  have hlogB_pos : 0 < Real.log (⌊y⌋₊ : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊y⌋₊))
  have hpos_fac : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
      0 < 1 - 2 / (p : ℝ) := by
    intro p hp
    have hp4 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
    have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp4
    have : 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    linarith
  rw [← Real.exp_log (Finset.prod_pos fun p hp => inv_pos.mpr (hpos_fac p hp))]
  rw [Real.log_prod fun p hp => (inv_pos.mpr (hpos_fac p hp)).ne']
  have hlog_sum : ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, Real.log (1 - 2 / (p : ℝ))⁻¹ ≤
      2 * Real.log (Real.log y / Real.log x) + 48 / Real.log (⌊x⌋₊ : ℝ) := by
    have hterm : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
        Real.log (1 - 2 / (p : ℝ))⁻¹ ≤ 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 := by
      intro p hp
      rw [Real.log_inv]
      have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
      have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
      have ht : 2 / (p : ℝ) ≤ 1 / 2 := by
        calc 2 / (p : ℝ) ≤ 2 / 5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
          _ ≤ 1 / 2 := by norm_num
      have hnl := neg_log_one_sub_le (by positivity) ht
      linarith [show 2 / (p : ℝ) + 2 * (2 / (p : ℝ)) ^ 2 = 2 / (p : ℝ) + 8 / (p : ℝ) ^ 2 by ring]
    have hsum1 := sum_inv_prime_Icc_le ⌊x⌋₊ ⌊y⌋₊ (by omega) hA_le_B
    have hsum2 : ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (8 : ℝ) / (p : ℝ) ^ 2 ≤
        8 / (⌊x⌋₊ : ℝ) := by
      have htel : ∀ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
          (8 : ℝ) / (p : ℝ) ^ 2 ≤ 8 * (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := by
        intro p hp
        have hp5 : 5 ≤ p := by rw [Finset.mem_filter, Finset.mem_Icc] at hp; omega
        have hpR : (5 : ℝ) ≤ p := by exact_mod_cast hp5
        have hp1R : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
        rw [hp1R, div_sub_div _ _ (by linarith) (by linarith)]
        have : 1 / ((p : ℝ) ^ 2) ≤ 1 / (((p : ℝ) - 1) * p) :=
          one_div_le_one_div_of_le (by nlinarith) (by nlinarith)
        have hsimp : (1 * (p : ℝ) - ((p : ℝ) - 1) * 1) / (((p : ℝ) - 1) * p) =
            1 / (((p : ℝ) - 1) * p) := by ring
        have h8 : 8 / (p : ℝ) ^ 2 ≤ 8 * (1 / (((p : ℝ) - 1) * p)) := by
          rw [← mul_one_div (8 : ℝ)]
          exact mul_le_mul_of_nonneg_left this (by norm_num)
        rw [hsimp]
        exact h8
      calc ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (8 : ℝ) / (p : ℝ) ^ 2
          ≤ ∑ p ∈ (Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
              8 * (1 / ((p - 1 : ℕ) : ℝ) - 1 / (p : ℝ)) := Finset.sum_le_sum htel
        _ ≤ ∑ m ∈ Finset.Icc (⌊x⌋₊ + 1) ⌊y⌋₊,
              8 * (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
            intro m hm _
            have hm5 : 5 ≤ m := by rw [Finset.mem_Icc] at hm; omega
            have hm1R : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by exact_mod_cast Nat.cast_sub (by omega)
            rw [hm1R]
            have hmR : (5 : ℝ) ≤ m := by exact_mod_cast hm5
            have : (1 : ℝ) / (m : ℝ) ≤ 1 / ((m : ℝ) - 1) :=
              one_div_le_one_div_of_le (by linarith) (by linarith)
            linarith
        _ ≤ 8 / (⌊x⌋₊ : ℝ) := by
            rw [← Finset.mul_sum]
            rcases eq_or_lt_of_le hA_le_B with h_eq | h_lt
            · have : ⌊y⌋₊ < ⌊x⌋₊ + 1 := by omega
              rw [Finset.Icc_eq_empty_of_lt this, Finset.sum_empty, mul_zero]
              positivity
            · have hind : ∀ k : ℕ, ⌊x⌋₊ + 1 ≤ k →
                  ∑ m ∈ Finset.Icc (⌊x⌋₊ + 1) k, (1 / ((m - 1 : ℕ) : ℝ) - 1 / (m : ℝ)) =
                  1 / (⌊x⌋₊ : ℝ) - 1 / (k : ℝ) := by
                intro k hk
                induction k, hk using Nat.le_induction with
                | base => simp
                | succ k hk ih =>
                  rw [Finset.sum_Icc_succ_top (by omega), ih]
                  simp only [Nat.add_sub_cancel]
                  push_cast; ring
              rw [hind ⌊y⌋₊ (by omega), mul_sub]
              have h_eq : 8 * (1 / (⌊x⌋₊ : ℝ)) = 8 / (⌊x⌋₊ : ℝ) := by ring
              have h_nn : (0 : ℝ) ≤ 8 * (1 / (⌊y⌋₊ : ℝ)) := by positivity
              linarith

    have hlogA : Real.log x ≤ Real.log (⌊x⌋₊ : ℝ) + 1 := by
      have hxA : x ≤ 2 * (⌊x⌋₊ : ℝ) := by
        have := Nat.lt_floor_add_one x
        have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊x⌋₊)
        linarith
      have h := Real.log_le_log hx_pos hxA
      rw [Real.log_mul (by norm_num) hA_pos.ne'] at h
      linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hrit : Real.log (Real.log x / Real.log (⌊x⌋₊ : ℝ)) ≤ 1 / Real.log (⌊x⌋₊ : ℝ) := by
      apply (Real.log_le_sub_one_of_pos (div_pos hlogx_pos hlogA_pos)).trans
      rw [div_sub_one hlogA_pos.ne', div_le_div_iff_of_pos_right hlogA_pos]
      linarith
    have hlog_comp : Real.log (Real.log (⌊y⌋₊ : ℝ) / Real.log (⌊x⌋₊ : ℝ)) ≤
        Real.log (Real.log y / Real.log x) + 1 / Real.log (⌊x⌋₊ : ℝ) := by
      calc _ ≤ Real.log (Real.log y / Real.log (⌊x⌋₊ : ℝ)) := by
             apply Real.log_le_log (div_pos hlogB_pos hlogA_pos)
             exact div_le_div_of_nonneg_right (Real.log_le_log hB_pos (Nat.floor_le hy_pos.le)) hlogA_pos.le
           _ = Real.log (Real.log y / Real.log x) + Real.log (Real.log x / Real.log (⌊x⌋₊ : ℝ)) := by
             rw [Real.log_div hlogy_pos.ne' hlogA_pos.ne', Real.log_div hlogy_pos.ne' hlogx_pos.ne',
               Real.log_div hlogx_pos.ne' hlogA_pos.ne']
             ring
           _ ≤ _ := by linarith
    have hsq : 8 / (⌊x⌋₊ : ℝ) ≤ 8 / Real.log (⌊x⌋₊ : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) hlogA_pos (by linarith [Real.log_le_sub_one_of_pos hA_pos])
    calc _ ≤ ∑ p ∈ (Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime,
               (2 / (p : ℝ) + 8 / (p : ℝ) ^ 2) := sum_le_sum hterm
         _ = 2 * ∑ p ∈ (Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (1 : ℝ) / p +
               ∑ p ∈ (Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime, (8 : ℝ) / (p : ℝ) ^ 2 := by
             rw [sum_add_distrib, mul_sum]
             congr 1; refine sum_congr rfl fun p _ ↦ by ring
         _ ≤ 2 * (Real.log (Real.log y / Real.log x) + 1 / Real.log (⌊x⌋₊ : ℝ) +
               19 / Real.log (⌊x⌋₊ : ℝ)) + 8 / Real.log (⌊x⌋₊ : ℝ) :=
             add_le_add (mul_le_mul_of_nonneg_left (hsum1.trans (add_le_add hlog_comp le_rfl))
               (by norm_num)) (hsum2.trans hsq)
         _ = _ := by ring
  calc Real.exp _ ≤ Real.exp (2 * Real.log (Real.log y / Real.log x) + 48 / Real.log (⌊x⌋₊ : ℝ)) :=
         Real.exp_le_exp.mpr hlog_sum
       _ = _ := by rw [Real.exp_add, two_mul, Real.exp_add, Real.exp_log (div_pos hlogy_pos hlogx_pos)]; ring

/-- 小さな素数での値を含めず、3以上の素数について篩密度の積を取る。 -/
noncomputable def sieveProduct (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∏ p ∈ (Icc 3 ⌊x⌋₊).filter Nat.Prime, (1 - w p)

theorem ratio_le {ε : ℝ} (hε : 0 < ε) :
    ∃ y₀ : ℕ, 4 ≤ y₀ ∧ ∀ {x y : ℝ}, y₀ ≤ x → x ≤ y →
      ∀ w : ℕ → ℝ, (∀ p : ℕ, p.Prime → 3 ≤ p → w p ≤ 2 / (p : ℝ)) →
        sieveProduct w x / sieveProduct w y ≤ (1 + ε) * (Real.log y / Real.log x) ^ 2 := by
  have hlogε : 0 < Real.log (1 + ε) := Real.log_pos (by linarith)
  let y₀ := max 4 ⌈Real.exp (48 / Real.log (1 + ε))⌉₊
  refine ⟨y₀, le_max_left _ _, ?_⟩
  intro x y hx hxy w hw
  have h4 : 4 ≤ y₀ := le_max_left _ _
  have hx4 : (4 : ℝ) ≤ x := (show (4 : ℝ) ≤ y₀ by exact_mod_cast h4).trans hx
  have hAB : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
  have hAx : y₀ ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hA4 : 4 ≤ ⌊x⌋₊ := h4.trans hAx
  have hExp : Real.exp (48 / Real.log (1 + ε)) ≤ (⌊x⌋₊ : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right 4 _).trans hAx)
  have hlogx : 0 < Real.log (⌊x⌋₊ : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < ⌊x⌋₊))
  have herr : Real.exp (48 / Real.log (⌊x⌋₊ : ℝ)) ≤ 1 + ε := by
    apply (Real.le_log_iff_exp_le (by linarith : 0 < 1 + ε)).mp
    have hlog := (Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) hExp)).mpr hExp
    rw [div_le_iff₀ hlogε] at hlog
    rw [div_le_iff₀ hlogx, mul_comm]
    exact hlog
  let P := (Icc 3 ⌊x⌋₊).filter Nat.Prime
  let Q := (Icc (⌊x⌋₊ + 1) ⌊y⌋₊).filter Nat.Prime
  have hu : (Icc 3 ⌊y⌋₊).filter Nat.Prime = P ∪ Q := by
    ext p
    simp only [P, Q, mem_filter, mem_Icc, mem_union]
    by_cases h : p.Prime
    · simp [h]; omega
    · simp [h]
  have hd : Disjoint P Q := by
    apply disjoint_left.2
    intro p hp hq
    simp only [P, Q, mem_filter, mem_Icc] at hp hq
    omega
  have hfac {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) : 0 < 1 - w p := by
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have ht : 2 / (p : ℝ) ≤ 2 / 3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hpR
    linarith [hw p hp hp3]
  have hP : 0 < ∏ p ∈ P, (1 - w p) := prod_pos fun p hp ↦
    hfac (mem_filter.1 hp).2 (mem_Icc.1 (mem_filter.1 hp).1).1
  have hr : sieveProduct w x / sieveProduct w y = ∏ p ∈ Q, (1 - w p)⁻¹ := by
    unfold sieveProduct
    rw [hu, prod_union hd, prod_inv_distrib]
    change (∏ p ∈ P, (1 - w p)) / ((∏ p ∈ P, (1-w p)) * ∏ p ∈ Q, (1-w p)) = _
    rw [div_mul_eq_div_div, div_self hP.ne', one_div]
  calc _ = _ := hr
       _ ≤ ∏ p ∈ Q, (1 - 2 / (p : ℝ))⁻¹ := by
         apply Finset.prod_le_prod
         · intro p hp
           obtain ⟨hm, hprime⟩ := mem_filter.1 hp
           have hpA := (mem_Icc.1 hm).1
           exact (inv_pos.mpr (hfac hprime (by omega))).le
         · intro p hp
           obtain ⟨hm, hprime⟩ := mem_filter.1 hp
           have hpA := (mem_Icc.1 hm).1
           have hpR : (5 : ℝ) ≤ p := by exact_mod_cast (by omega : 5 ≤ p)
           apply inv_anti₀
           · have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 5) hpR
             linarith
           · linarith [hw p hprime (by omega)]
       _ ≤ _ := (prod_two_div_interval_explicit hx4 hxy).trans
         (mul_le_mul_of_nonneg_right herr (sq_nonneg _))

end BethMertens

end

section

namespace BethRemainder

open Filter Finset

/-- εを固定すると、p^εが8未満の素数pは有限個に限られる。 -/
private lemma primeFactorWeight_le {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 0 < n →
      (8 : ℝ) ^ n.primeFactors.card ≤ A * (n : ℝ) ^ ε := by
  obtain ⟨K, hK⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hε).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ ↦ (p : ℝ)) atTop atTop)
      |>.eventually_ge_atTop 8)
  refine ⟨(8 : ℝ) ^ K, by positivity, ?_⟩
  intro n hn
  let s := n.primeFactors
  let small := s.filter (fun p ↦ p < K)
  have hsmall : small.card ≤ K := by
    calc small.card ≤ (range K).card := card_le_card fun p hp ↦
           mem_range.2 (mem_filter.1 hp).2
         _ = K := card_range K
  have hprod : ∏ p ∈ s, (p : ℝ) ≤ (n : ℝ) := by
    have h : (∏ p ∈ n.primeFactors, p) ≤ n := Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
    simpa [s, Nat.cast_prod] using (Nat.cast_le (α := ℝ)).2 h
  have hpow : ∏ p ∈ s, (p : ℝ) ^ ε ≤ (n : ℝ) ^ ε := by
    rw [Real.finsetProd_rpow _ _ (by intros; positivity)]
    exact Real.rpow_le_rpow (by positivity) hprod hε.le
  calc (8 : ℝ) ^ n.primeFactors.card = ∏ _p ∈ s, (8 : ℝ) := by simp [s]
       _ ≤ ∏ p ∈ s, (if p < K then (8 : ℝ) else 1) * (p : ℝ) ^ ε := by
         apply prod_le_prod (by intros; norm_num)
         intro p hp
         by_cases h : p < K
         · have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
           simpa [h] using mul_le_mul_of_nonneg_left (Real.one_le_rpow hp1 hε.le) (by norm_num : (0:ℝ) ≤ 8)
         · simpa [h] using hK p (le_of_not_gt h)
       _ = (8 : ℝ) ^ small.card * (∏ p ∈ s, (p : ℝ) ^ ε) := by
         rw [prod_mul_distrib, ← prod_filter]
         simp [small]
       _ ≤ (8 : ℝ) ^ K * (n : ℝ) ^ ε := by
         gcongr
         norm_num

theorem sum_primeFactorWeight_le {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ D : ℝ, 1 ≤ D →
      (∑ n ∈ Icc 1 ⌊D⌋₊, (8 : ℝ) ^ n.primeFactors.card) ≤ A * D ^ (1 + ε) := by
  obtain ⟨A, hA, h⟩ := primeFactorWeight_le hε
  refine ⟨A, hA, ?_⟩
  intro D hD
  have floor_le := Nat.floor_le (by linarith : (0 : ℝ) ≤ D)
  calc (∑ n ∈ Icc 1 ⌊D⌋₊, (8 : ℝ) ^ n.primeFactors.card)
       ≤ ∑ _n ∈ Icc 1 ⌊D⌋₊, A * D ^ ε := by
         apply sum_le_sum
         intro n hn
         obtain ⟨hn1, hnD⟩ := mem_Icc.1 hn
         exact (h n hn1).trans (mul_le_mul_of_nonneg_left
           (Real.rpow_le_rpow (Nat.cast_nonneg n) ((Nat.cast_le.mpr hnD).trans floor_le) hε.le) hA.le)
       _ = (⌊D⌋₊ : ℝ) * (A * D ^ ε) := by simp [Nat.card_Icc, nsmul_eq_mul]
       _ ≤ D * (A * D ^ ε) := by gcongr
       _ = A * D ^ (1 + ε) := by rw [Real.rpow_add (by linarith : 0 < D), Real.rpow_one]; ring

/-- α < βなら、z^αまでの剰余の和に対数の任意の固定べき乗を掛けてもz^βで抑えられる。 -/
theorem weightedRemainder {α β c : ℝ} (hα : 0 < α) (hab : α < β) (hc : 0 < c)
    (k : ℕ) :
    ∀ᶠ z : ℝ in atTop, (∑ n ∈ Icc 1 ⌊z ^ α⌋₊, (8 : ℝ) ^ n.primeFactors.card) *
      (Real.log z) ^ k ≤ c * z ^ β := by
  let δ := (β - α) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  obtain ⟨A, hA, hsum⟩ := sum_primeFactorWeight_le (div_pos hδ hα)
  have hlog := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hδ).bound (div_pos hc hA)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog] with z hz hlog
  have hz0 : 0 < z := by linarith
  have hlog0 : 0 ≤ Real.log z := Real.log_nonneg hz
  have hlog' : Real.log z ^ k ≤ (c / A) * z ^ δ := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlog0 k), abs_of_nonneg (Real.rpow_nonneg hz0.le δ)] using hlog
  have hexp : α * (1 + δ / α) + δ = β := by
    dsimp [δ]
    field_simp
    ring
  calc (∑ n ∈ Icc 1 ⌊z ^ α⌋₊, (8 : ℝ) ^ n.primeFactors.card) * Real.log z ^ k
       ≤ (A * (z ^ α) ^ (1 + δ / α)) * ((c / A) * z ^ δ) :=
         mul_le_mul (hsum _ (Real.one_le_rpow hz hα.le)) hlog' (pow_nonneg hlog0 k) (by positivity)
       _ = c * (z ^ (α * (1 + δ / α)) * z ^ δ) := by
         rw [← Real.rpow_mul hz0.le]
         field_simp
       _ = c * z ^ β := by rw [← Real.rpow_add hz0, hexp]

end BethRemainder

end

section

/-
Bethの2次元篩を有限係数の主項の正値性に帰着する。
小さい素数の合同条件、一次形式の周期性と剰余類の数、元の区間に戻す部分は
@green-notesによるWilson H4の証明から移植した。
https://github.com/lefttosolve2/open-math-agents/pull/4718 (96b8ff3ae79468ec26ec864761a0f4c43ca48069)
-/

namespace OMABeth.Application

open Finset Filter

/-- 小素数の合同条件を処理した後の素数集合 -/
noncomputable def largePrimes (y0 : ℕ) (z : ℝ) := (Icc (y0 + 1) ⌊z⌋₊).filter Nat.Prime

private lemma crt_const_exists (y0 : ℕ) (a b : ℤ)
    (ha : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ y0 → ¬ ((p : ℤ) ∣ a)) :
    let Q0 := 2 * ∏ p ∈ (Finset.Icc 3 y0).filter Nat.Prime, p
    ∃ x0 < Q0, ¬ 2 ∣ x0 ∧
      ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ y0 →
        ¬ ((p : ℤ) ∣ (x0 : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x0 : ℤ) + b) := by
  intro Q0
  have hgen : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ 3 ≤ p ∧ ¬ ((p : ℤ) ∣ a)) →
      ∃ x0 < 2 * ∏ p ∈ T, p, ¬ 2 ∣ x0 ∧
        ∀ p ∈ T, ¬ ((p : ℤ) ∣ (x0 : ℤ)) ∧ ¬ ((p : ℤ) ∣ a * (x0 : ℤ) + b) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, by norm_num, by omega, by simp⟩
    | @insert p T hpT ih =>
      intro hT
      have hp_sp := hT p (Finset.mem_insert_self p T)
      have hT_sub : ∀ q ∈ T, q.Prime ∧ 3 ≤ q ∧ ¬ ((q : ℤ) ∣ a) :=
        fun q hq => hT q (Finset.mem_insert_of_mem hq)
      obtain ⟨x', hx'_lt, hx'_odd, hx'_good⟩ := ih hT_sub
      let QT := 2 * ∏ q ∈ T, q
      have hQT_pos : 0 < QT := by
        refine mul_pos (by norm_num) (Finset.prod_pos fun q hq => (hT_sub q hq).1.pos)
      have hcop_prod : Nat.Coprime p (∏ q ∈ T, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact (Nat.coprime_primes hp_sp.1 (hT_sub q hq).1).mpr (fun h => hpT (h ▸ hq))
      have hcop_2 : Nat.Coprime p 2 :=
        (Nat.coprime_primes hp_sp.1 Nat.prime_two).mpr (by omega)
      have hcop_QT : Nat.Coprime p QT := hcop_2.mul_right hcop_prod
      have hp_ndvd_QT : ¬ p ∣ QT := hp_sp.1.coprime_iff_not_dvd.mp hcop_QT
      have hp_int_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_sp.1
      have h_inj_x : ∀ k₁ k₂ : ℕ, k₁ < k₂ → k₂ ≤ 2 →
          (p : ℤ) ∣ ((x' + k₁ * QT : ℕ) : ℤ) → ¬ ((p : ℤ) ∣ ((x' + k₂ * QT : ℕ) : ℤ)) := by
        intro k₁ k₂ h12 h2 hd1 hd2
        have hsub : (p : ℤ) ∣ ((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ) := by
          have : ((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ) = ((x' + k₂ * QT : ℕ) : ℤ) - ((x' + k₁ * QT : ℕ) : ℤ) := by
            push_cast [Nat.cast_sub h12.le]; ring
          rw [this]; exact dvd_sub hd2 hd1
        have hnat : p ∣ (k₂ - k₁) * QT := Int.natCast_dvd_natCast.mp (by exact_mod_cast hsub)
        rcases hp_sp.1.dvd_mul.mp hnat with hd_k | hd_Q
        · have : p ≤ k₂ - k₁ := Nat.le_of_dvd (by omega) hd_k
          omega
        · exact hp_ndvd_QT hd_Q
      have h_inj_ax : ∀ k₁ k₂ : ℕ, k₁ < k₂ → k₂ ≤ 2 →
          (p : ℤ) ∣ a * ((x' + k₁ * QT : ℕ) : ℤ) + b →
          ¬ ((p : ℤ) ∣ a * ((x' + k₂ * QT : ℕ) : ℤ) + b) := by
        intro k₁ k₂ h12 h2 hd1 hd2
        have hsub : (p : ℤ) ∣ a * (((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ)) := by
          have : a * (((k₂ - k₁ : ℕ) : ℤ) * (QT : ℤ)) =
              (a * ((x' + k₂ * QT : ℕ) : ℤ) + b) - (a * ((x' + k₁ * QT : ℕ) : ℤ) + b) := by
            push_cast [Nat.cast_sub h12.le]; ring
          rw [this]; exact dvd_sub hd2 hd1
        rcases hp_int_prime.dvd_or_dvd hsub with hda | hd_mul
        · exact hp_sp.2.2 hda
        · have hnat : p ∣ (k₂ - k₁) * QT := Int.natCast_dvd_natCast.mp (by exact_mod_cast hd_mul)
          rcases hp_sp.1.dvd_mul.mp hnat with hd_k | hd_Q
          · have : p ≤ k₂ - k₁ := Nat.le_of_dvd (by omega) hd_k
            omega
          · exact hp_ndvd_QT hd_Q
      have hex_k : ∃ k ≤ 2,
          ¬ ((p : ℤ) ∣ ((x' + k * QT : ℕ) : ℤ)) ∧
          ¬ ((p : ℤ) ∣ a * ((x' + k * QT : ℕ) : ℤ) + b) := by
        by_cases h0x : (p : ℤ) ∣ ((x' + 0 * QT : ℕ) : ℤ)
        · have h1x := h_inj_x 0 1 (by omega) (by omega) h0x
          have h2x := h_inj_x 0 2 (by omega) (by omega) h0x
          by_cases h1a : (p : ℤ) ∣ a * ((x' + 1 * QT : ℕ) : ℤ) + b
          · exact ⟨2, by omega, h2x, h_inj_ax 1 2 (by omega) (by omega) h1a⟩
          · exact ⟨1, by omega, h1x, h1a⟩
        · by_cases h0a : (p : ℤ) ∣ a * ((x' + 0 * QT : ℕ) : ℤ) + b
          · have h1a := h_inj_ax 0 1 (by omega) (by omega) h0a
            have h2a := h_inj_ax 0 2 (by omega) (by omega) h0a
            by_cases h1x : (p : ℤ) ∣ ((x' + 1 * QT : ℕ) : ℤ)
            · exact ⟨2, by omega, h_inj_x 1 2 (by omega) (by omega) h1x, h2a⟩
            · exact ⟨1, by omega, h1x, h1a⟩
          · exact ⟨0, by omega, h0x, h0a⟩
      obtain ⟨k, hk2, hkx, hka⟩ := hex_k
      refine ⟨x' + k * QT, ?_, ?_, ?_⟩
      · have hx'_Q : x' < QT := hx'_lt
        calc x' + k * QT < QT + 2 * QT := by nlinarith
          _ = 3 * QT := by ring
          _ ≤ p * QT := Nat.mul_le_mul_right QT hp_sp.2.1
          _ = 2 * ∏ q ∈ insert p T, q := by rw [Finset.prod_insert hpT]; dsimp only [QT]; ring
      · intro h2dvd
        have h2QT : 2 ∣ k * QT := dvd_mul_of_dvd_right (dvd_mul_right 2 _) k
        exact hx'_odd ((Nat.dvd_add_left h2QT).mp h2dvd)
      · intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hqT
        · exact ⟨hkx, hka⟩
        · have hq_dvd_QT : q ∣ QT := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hqT) 2
          have hqZ_dvd : (q : ℤ) ∣ (k * QT : ℕ) := Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_right hq_dvd_QT k)
          have hxg := hx'_good q hqT
          refine ⟨fun hd => hxg.1 ?_, fun hd => hxg.2 ?_⟩
          · have : ((x' : ℕ) : ℤ) = ((x' + k * QT : ℕ) : ℤ) - ((k * QT : ℕ) : ℤ) := by push_cast; ring
            rw [this]; exact dvd_sub hd hqZ_dvd
          · have : a * (x' : ℤ) + b = (a * ((x' + k * QT : ℕ) : ℤ) + b) - a * ((k * QT : ℕ) : ℤ) := by
              push_cast; ring
            rw [this]; exact dvd_sub hd (dvd_mul_of_dvd_right hqZ_dvd a)
  obtain ⟨x0, hx0_lt, hx0_odd, hx0_good⟩ := hgen ((Finset.Icc 3 y0).filter Nat.Prime)
    (fun p hp => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hp
      exact ⟨hp.2, hp.1.1, ha p hp.2 hp.1.1 hp.1.2⟩)
  exact ⟨x0, hx0_lt, hx0_odd, fun p hp hp3 hpy =>
    hx0_good p (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp3, hpy⟩, hp⟩)⟩

/-- 大素数の篩の主項が一様に対数の逆2乗より大きければ、Bethで必要な区間が得られる。 -/
theorem h4_of_cert_log (y0 : ℕ) (hy0 : 4 ≤ y0) {α k : ℝ} (hα : 0 < α)
    (hab : α < (64 : ℝ) / 15) (hk : 0 < k)
    (hcert : ∀ᶠ z : ℝ in atTop, ∃ c : Cert false (largePrimes y0 z) (z ^ α),
      k / (Real.log z)^2 ≤ c.main (fun p => 2 / (p : ℝ))) :
    OMA.R_Erdos724_erdos_724_variants_beth_R1.H4 := by
  let Q0 : ℕ := 2 * ∏ p ∈ (Finset.Icc 3 y0).filter Nat.Prime, p
  have hQ0_pos : 0 < Q0 := mul_pos (by norm_num) (Finset.prod_pos fun p hp =>
    (Finset.mem_filter.mp hp).2.pos)
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp (hcert.and <|
    BethRemainder.weightedRemainder hα hab (half_pos hk) 2)
  let C := max (max (y0 : ℝ) Z) (3 * (Q0 : ℝ))
  have hy0R : (4 : ℝ) ≤ y0 := by exact_mod_cast hy0
  have hCy : (y0 : ℝ) ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCZ : Z ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hCQ : 3 * (Q0 : ℝ) ≤ C := le_max_right _ _
  have hC3 : 3 ≤ C := by linarith
  refine ⟨C, hC3, ?_⟩
  intro z X L a b hzC hLC ha
  have hz_ge_y0 := hCy.trans hzC
  have hz3 := hC3.trans hzC
  have hz_pos : 0 < z := by linarith
  have hlog : 0 < Real.log z := Real.log_pos (by linarith)
  let R := z ^ ((64 : ℝ) / 15)
  have hR : 1 ≤ R := Real.one_le_rpow (by linarith) (by norm_num)
  have hRpos : 0 < R := by linarith
  have ha_y0 : ∀ p : ℕ, p.Prime → 3 ≤ p → p ≤ y0 → ¬ ((p : ℤ) ∣ a) := by
    intro p hp hp3 hpy
    exact ha p hp hp3 ((by exact_mod_cast hpy : (p : ℝ) ≤ y0).trans hz_ge_y0)
  obtain ⟨x0, hx0_lt, hx0_odd, hx0_good⟩ := crt_const_exists y0 a b ha_y0
  let M : ℕ := ⌊R⌋₊ + 1
  let Y0 : ℕ := X / Q0 + 1
  have hM : R ≤ (M : ℝ) := by simpa only [M, Nat.cast_add_one] using (Nat.lt_floor_add_one R).le
  have hM' : (M : ℝ) ≤ R + 1 := by simpa [M] using add_le_add_right (Nat.floor_le hRpos.le) 1
  have hQM_le_L : Q0 * (M + 1) ≤ L := by
    have hQ : (0 : ℝ) ≤ Q0 := Nat.cast_nonneg _
    have h : (Q0 : ℝ) * ((M : ℝ) + 1) ≤ (L : ℝ) := calc
      _ ≤ (Q0 : ℝ) * (R + 2) := mul_le_mul_of_nonneg_left (by linarith) hQ
      _ ≤ 3 * (Q0 : ℝ) * R := by nlinarith [mul_nonneg hQ (sub_nonneg.mpr hR)]
      _ ≤ C * R := mul_le_mul_of_nonneg_right hCQ hRpos.le
      _ ≤ (L : ℝ) := hLC
    exact_mod_cast h
  let bad : ℕ → ℕ → Prop := fun p y =>
    (p : ℤ) ∣ ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) ∨
      (p : ℤ) ∣ a * ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) + b
  have hper : ∀ p y, bad p y ↔ bad p (y % p) := by
    intro p y
    have hym : (p : ℤ) ∣ ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by
      refine ⟨((y / p : ℕ) : ℤ), ?_⟩
      have hdivZ : (p : ℤ) * ((y / p : ℕ) : ℤ) + ((y % p : ℕ) : ℤ) = (y : ℤ) := by
        exact_mod_cast Nat.div_add_mod y p
      linarith
    dsimp only [bad]
    constructor <;> rintro (h | h)
    · left
      have : (x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ) =
          ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) - (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_sub h (dvd_mul_of_dvd_right hym _)
    · right
      have : a * ((x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ)) + b =
          (a * ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) + b) - a * (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_sub h (dvd_mul_of_dvd_right hym _)
    · left
      have : (x0 : ℤ) + (Q0 : ℤ) * (y : ℤ) =
          ((x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ)) + (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_add h (dvd_mul_of_dvd_right hym _)
    · right
      have : a * ((x0 : ℤ) + (Q0 : ℤ) * (y : ℤ)) + b =
          (a * ((x0 : ℤ) + (Q0 : ℤ) * ((y % p : ℕ) : ℤ)) + b) + a * (Q0 : ℤ) * ((y : ℤ) - ((y % p : ℕ) : ℤ)) := by ring
      rw [this]; exact dvd_add h (dvd_mul_of_dvd_right hym _)
  let S_ps := largePrimes y0 z
  have hps_spec {p : ℕ} (hm : p ∈ S_ps) : p.Prime ∧ y0 < p ∧ (p : ℝ) ≤ z := by
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    have hb := Finset.mem_Icc.mp hm
    exact ⟨hp, by omega, (Nat.le_floor_iff hz_pos.le).mp hb.2⟩
  have hps_ndvd : ∀ p : ℕ, p.Prime → y0 < p → (p : ℝ) ≤ z → ¬ (p ∣ Q0) ∧ ¬ ((p : ℤ) ∣ a) := by
    intro p hp hpy hpz
    refine ⟨?_, ha p hp (by omega) hpz⟩
    intro hdvd
    rcases hp.dvd_mul.mp hdvd with hd2 | hd_prod
    · have := ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left hp.ne_one
      omega
    · obtain ⟨q, hq, hqp⟩ := (hp.prime.dvd_finsetProd_iff id).mp hd_prod
      rw [Finset.mem_filter, Finset.mem_Icc] at hq
      have := ((Nat.dvd_prime hq.2).mp hqp).resolve_left hp.ne_one
      omega
  have hbad_le2 : ∀ p : ℕ, p.Prime → y0 < p → (p : ℝ) ≤ z →
      ((Finset.range p).filter (fun r => bad p r)).card ≤ 2 := by
    intro p hp hpy hpz
    obtain ⟨hpQ0, hpa⟩ := hps_ndvd p hp hpy hpz
    have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hsub : (Finset.range p).filter (fun (r : ℕ) => bad p r) ⊆
        (Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ))) ∪
        (Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ a * ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ)) + b) := by
      intro r hr
      rw [Finset.mem_filter] at hr
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      rcases hr.2 with h1 | h2
      · exact Or.inl ⟨hr.1, h1⟩
      · exact Or.inr ⟨hr.1, h2⟩
    have hc1 : ((Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ)))).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro r₁ hr₁ r₂ hr₂
      rw [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
      wlog hle : r₁ ≤ r₂ generalizing r₁ r₂
      · exact (this r₂ hr₂ r₁ hr₁ (le_of_not_ge hle)).symm
      have hsub_dvd : (p : ℤ) ∣ (Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ) := by
        have : (Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ) =
            ((x0 : ℤ) + (Q0 : ℤ) * (r₂ : ℤ)) - ((x0 : ℤ) + (Q0 : ℤ) * (r₁ : ℤ)) := by
          rw [Nat.cast_sub hle]; ring
        rw [this]; exact dvd_sub hr₂.2 hr₁.2
      have hnat : p ∣ Q0 * (r₂ - r₁) := Int.natCast_dvd_natCast.mp (by exact_mod_cast hsub_dvd)
      rcases hp.dvd_mul.mp hnat with hq | hr
      · exact absurd hq hpQ0
      · by_contra hne
        have := Nat.le_of_dvd (by omega) hr
        omega
    have hc2 : ((Finset.range p).filter (fun (r : ℕ) => (p : ℤ) ∣ a * ((x0 : ℤ) + (Q0 : ℤ) * (r : ℤ)) + b)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro r₁ hr₁ r₂ hr₂
      rw [Finset.mem_filter, Finset.mem_range] at hr₁ hr₂
      wlog hle : r₁ ≤ r₂ generalizing r₁ r₂
      · exact (this r₂ hr₂ r₁ hr₁ (le_of_not_ge hle)).symm
      have hsub_dvd : (p : ℤ) ∣ a * ((Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ)) := by
        have : a * ((Q0 : ℤ) * ((r₂ - r₁ : ℕ) : ℤ)) =
            (a * ((x0 : ℤ) + (Q0 : ℤ) * (r₂ : ℤ)) + b) - (a * ((x0 : ℤ) + (Q0 : ℤ) * (r₁ : ℤ)) + b) := by
          rw [Nat.cast_sub hle]; ring
        rw [this]; exact dvd_sub hr₂.2 hr₁.2
      rcases hp_int.dvd_or_dvd hsub_dvd with ha_dvd | hmul
      · exact absurd ha_dvd hpa
      · have hnat : p ∣ Q0 * (r₂ - r₁) := Int.natCast_dvd_natCast.mp (by exact_mod_cast hmul)
        rcases hp.dvd_mul.mp hnat with hq | hr
        · exact absurd hq hpQ0
        · by_contra hne
          have := Nat.le_of_dvd (by omega) hr
          omega
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans (by omega))
  obtain ⟨⟨c, hc⟩, herr⟩ := hZ z (hCZ.trans hzC)
  have hkmain := (div_le_iff₀ (sq_pos_of_pos hlog)).mp hc
  have hgap : (∑ n ∈ Icc 1 ⌊z ^ α⌋₊, (8 : ℝ) ^ n.primeFactors.card) <
      (M : ℝ) * c.main (fun p => 2 / (p : ℝ)) := by
    apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hlog)).mp
    calc _ ≤ (k / 2) * R := herr
         _ < R * k := by nlinarith [mul_pos hk hRpos]
         _ ≤ (M : ℝ) * (c.main (fun p => 2 / (p : ℝ)) * (Real.log z)^2) :=
           mul_le_mul hM hkmain hk.le (Nat.cast_nonneg _)
         _ = _ := by ring
  have hcard (p) (hm : p ∈ S_ps) : Buchstab.numResidues bad p ≤ 2 := by
    have h := hbad_le2 p (hps_spec hm).1 (hps_spec hm).2.1 (hps_spec hm).2.2
    apply le_trans _ h
    apply Finset.card_le_card
    intro r hr
    simpa only [Finset.mem_filter] using hr
  have hex_y := Cert.exists_of_uniform_main c bad Y0 M (fun _ h => (hps_spec h).1) hper hcard hgap
  obtain ⟨y, hy_mem, hy_good⟩ := hex_y
  rw [Finset.mem_Ico] at hy_mem
  let x := x0 + Q0 * y
  refine ⟨x, Finset.mem_Ico.mpr ⟨?_, ?_⟩, ?_, ?_⟩
  · have hmod : (X / Q0 : ℕ) * Q0 + X % Q0 = X := Nat.div_add_mod' X Q0
    have hmod_lt : X % Q0 < Q0 := Nat.mod_lt X hQ0_pos
    have hQy : Q0 * (X / Q0 + 1) ≤ Q0 * y := Nat.mul_le_mul_left Q0 hy_mem.1
    exact Nat.le_of_lt (calc X = (X / Q0 : ℕ) * Q0 + X % Q0 := hmod.symm
      _ < (X / Q0 : ℕ) * Q0 + Q0 := Nat.add_lt_add_left hmod_lt _
      _ = Q0 * (X / Q0 + 1) := by ring
      _ ≤ Q0 * y := hQy
      _ ≤ x0 + Q0 * y := Nat.le_add_left _ _)
  · have hmul : (X / Q0 : ℕ) * Q0 ≤ X := Nat.div_mul_le_self X Q0
    have hx0_Q : x0 < Q0 := hx0_lt
    have hy1 : y + 1 ≤ X / Q0 + (M + 1) := by
      have h1 : y + 1 ≤ Y0 + M := Nat.succ_le_of_lt hy_mem.2
      change y + 1 ≤ (X / Q0 + 1) + M at h1
      linarith
    have hQy1 : Q0 * (y + 1) ≤ Q0 * (X / Q0 + (M + 1)) := Nat.mul_le_mul_left Q0 hy1
    calc x0 + Q0 * y < Q0 + Q0 * y := Nat.add_lt_add_right hx0_Q _
      _ = Q0 * (y + 1) := by ring
      _ ≤ Q0 * (X / Q0 + (M + 1)) := hQy1
      _ = (X / Q0 : ℕ) * Q0 + Q0 * (M + 1) := by ring
      _ ≤ X + L := Nat.add_le_add hmul hQM_le_L
  · intro h2x
    have h2Q : 2 ∣ Q0 * y := dvd_mul_of_dvd_left (dvd_mul_right 2 _) y
    exact hx0_odd ((Nat.dvd_add_left h2Q).mp h2x)
  · intro p hp hp3 hpz
    by_cases hpy : p ≤ y0
    · obtain ⟨hx0_p, hx0_ap⟩ := hx0_good p hp hp3 hpy
      have hp_dvd_Q0 : p ∣ Q0 := by
        refine dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ ?_) 2
        rw [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hp3, hpy⟩, hp⟩
      have hpZ : (p : ℤ) ∣ ((Q0 * y : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (dvd_mul_of_dvd_left hp_dvd_Q0 y)
      refine ⟨fun hd => hx0_p ?_, fun hd => hx0_ap ?_⟩
      · have : (x0 : ℤ) = (x : ℤ) - ((Q0 * y : ℕ) : ℤ) := by dsimp only [x]; push_cast; ring
        rw [this]; exact dvd_sub hd hpZ
      · have : a * (x0 : ℤ) + b = (a * (x : ℤ) + b) - a * ((Q0 * y : ℕ) : ℤ) := by
          dsimp only [x]; push_cast; ring
        rw [this]; exact dvd_sub hd (dvd_mul_of_dvd_right hpZ a)
    · have hpy_gt : y0 + 1 ≤ p := by omega
      have hp_le_fl : p ≤ ⌊z⌋₊ := Nat.le_floor hpz
      have hp_mem : p ∈ S_ps :=
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpy_gt, hp_le_fl⟩, hp⟩
      have hy_nb := hy_good p hp_mem
      dsimp only [bad] at hy_nb
      push Not at hy_nb
      exact ⟨by simpa [x] using hy_nb.1, by simpa [x] using hy_nb.2⟩


/-- 相対主項が正の定数δ以上なら元のBethの篩が成立する。 -/
theorem h4_of_cert (y0 : ℕ) (hy0 : 4 ≤ y0) {α δ : ℝ} (hα : 0 < α)
    (hab : α < (64 : ℝ) / 15) (hδ : 0 < δ)
    (hcert : ∀ᶠ z : ℝ in atTop, ∃ c : Cert false (largePrimes y0 z) (z ^ α),
      (∏ p ∈ largePrimes y0 z, (1 - 2 / (p : ℝ))) * δ ≤ c.main (fun p => 2 / (p : ℝ))) :
    OMA.R_Erdos724_erdos_724_variants_beth_R1.H4 := by
  have hy0R : (4 : ℝ) ≤ y0 := by exact_mod_cast hy0
  have hlog0 : 0 < Real.log (y0 : ℝ) := Real.log_pos (by linarith)
  let k := δ * (Real.log (y0 : ℝ))^2 / Real.exp (48 / Real.log (y0 : ℝ))
  have hk : 0 < k := by dsimp [k]; positivity
  apply h4_of_cert_log y0 hy0 hα hab hk
  filter_upwards [hcert, eventually_ge_atTop (y0 : ℝ)] with z hc hz
  obtain ⟨c, hc⟩ := hc
  refine ⟨c, le_trans ?_ hc⟩
  have hlog : 0 < Real.log z := Real.log_pos (by linarith)
  let V := ∏ p ∈ largePrimes y0 z, (1 - 2 / (p : ℝ))
  have hV : 0 < V := by
    apply Finset.prod_pos
    intro p hp
    have hlo := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpR : (2 : ℝ) < p := by exact_mod_cast (by omega : 2 < p)
    exact sub_pos.mpr ((div_lt_one (by linarith)).mpr hpR)
  have hinv : V⁻¹ ≤ Real.exp (48 / Real.log (y0 : ℝ)) *
      (Real.log z / Real.log (y0 : ℝ))^2 := by
    simpa [V, largePrimes, Finset.prod_inv_distrib] using
      BethMertens.prod_two_div_interval_explicit hy0R hz
  have hrec := inv_anti₀ (inv_pos.mpr hV) hinv
  rw [inv_inv] at hrec
  change k / (Real.log z)^2 ≤ V * δ
  calc _ = (Real.exp (48 / Real.log (y0 : ℝ)) *
        (Real.log z / Real.log (y0 : ℝ))^2)⁻¹ * δ := by
           dsimp [k]
           field_simp [hlog0.ne', hlog.ne', Real.exp_ne_zero]
       _ ≤ _ := mul_le_mul_of_nonneg_right hrec hδ.le

end OMABeth.Application

end

section

open Finset

namespace BethSelberg

noncomputable def volume (s : BoundingSieve) : ℝ :=
  ∏ p ∈ s.prodPrimes.primeFactors, (1 - s.nu p)

noncomputable def divisorMass (s : BoundingSieve) (d : ℕ) : ℝ :=
  (∏ p ∈ d.primeFactors, s.nu p) *
    ∏ p ∈ s.prodPrimes.primeFactors \ d.primeFactors, (1 - s.nu p)

theorem volume_pos (s : BoundingSieve) : 0 < volume s :=
  Finset.prod_pos fun p hp ↦ sub_pos.mpr
    (s.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp))

theorem selbergTerms_mul_volume (s : BoundingSieve) {d : ℕ} (hd : d ∣ s.prodPrimes) :
    s.selbergTerms d * volume s = divisorMass s d := by
  have hsub := Nat.primeFactors_mono hd s.prodPrimes_ne_zero
  have hunit : (∏ p ∈ d.primeFactors, (1 - s.nu p)) ≠ 0 :=
    (Finset.prod_pos fun p hp ↦ sub_pos.mpr (s.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hp) ((Nat.dvd_of_mem_primeFactors hp).trans hd))).ne'
  rw [BoundingSieve.selbergTerms_apply, ← s.prod_primeFactors_nu hd,
    Finset.prod_inv_distrib, volume, divisorMass, ← Finset.prod_sdiff hsub]
  field_simp

theorem selberg_truncated_mass (s : BoundingSieve) (D : ℝ) :
    (∑ l ∈ s.prodPrimes.divisors, if (l : ℝ)^2 ≤ D then s.selbergTerms l else 0) * volume s =
      ∑ l ∈ s.prodPrimes.divisors, if (l : ℝ)^2 ≤ D then divisorMass s l else 0 := by
  rw [sum_mul]
  apply sum_congr rfl
  intro l hl
  split_ifs <;> simp [selbergTerms_mul_volume s (Nat.dvd_of_mem_divisors hl)]

theorem selberg_reciprocal_as_mass (s : BoundingSieve) (D : ℝ) :
    (∑ l ∈ s.prodPrimes.divisors, if (l : ℝ)^2 ≤ D then s.selbergTerms l else 0)⁻¹ =
      volume s / (∑ l ∈ s.prodPrimes.divisors, if (l : ℝ)^2 ≤ D then divisorMass s l else 0) := by
  rw [← selberg_truncated_mass, div_eq_mul_inv, mul_inv, mul_left_comm,
    mul_inv_cancel₀ (volume_pos s).ne', mul_one]

noncomputable def volumeOn (w : ℕ → ℝ) (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1 - w p)

noncomputable def cdf (w : ℕ → ℝ) (P : Finset ℕ) (Y : ℝ) : ℝ :=
  ∑ S ∈ P.powerset, if ((∏ p ∈ S, p : ℕ) : ℝ) ≤ Y then
    (∏ p ∈ S, w p) * volumeOn w (P \ S) else 0

theorem cdf_insert (w : ℕ → ℝ) (P : Finset ℕ) {p : ℕ} (hp : p ∉ P) (hp0 : 0 < p) (Y : ℝ) :
    cdf w (insert p P) Y = (1 - w p) * cdf w P Y + w p * cdf w P (Y / p) := by
  classical
  simp only [cdf, Finset.sum_powerset_insert hp, mul_sum]
  congr 1
  · refine sum_congr rfl fun S hS ↦ ?_
    have hpS : p ∉ S := fun h ↦ hp (mem_powerset.mp hS h)
    rw [insert_sdiff_of_notMem _ hpS, volumeOn, prod_insert (fun h ↦ hp (mem_sdiff.mp h).1)]
    split_ifs <;> simp [volumeOn]
    ring
  · refine sum_congr rfl fun S hS ↦ ?_
    have hpS : p ∉ S := fun h ↦ hp (mem_powerset.mp hS h)
    have hpR : 0 < (p : ℝ) := by exact_mod_cast hp0
    rw [prod_insert hpS, prod_insert hpS, Nat.cast_mul, insert_sdiff_insert,
      sdiff_insert_of_notMem hp]
    simp only [le_div_iff₀ hpR, mul_comm (p : ℝ) ((∏ i ∈ S, i : ℕ) : ℝ)]
    split_ifs <;> ring

theorem cdf_eq_sum_max (w : ℕ → ℝ) (P : Finset ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (hP : ∀ p ∈ P, 0 < p) :
    cdf w P Y = volumeOn w P + ∑ p ∈ P,
      w p * volumeOn w (P.filter (p < ·)) * cdf w (P.filter (· < p)) (Y / p) := by
  classical
  induction P using Finset.induction_on_max with
  | empty => simp [cdf, volumeOn, hY]
  | insert m P hlt ih =>
    have hm : m ∉ P := fun h ↦ (hlt _ h).false
    have hm0 := hP m (mem_insert_self m P)
    have hP' : ∀ p ∈ P, 0 < p := fun p hp ↦ hP p (mem_insert_of_mem hp)
    have hSm : (insert m P).filter (· < m) = P := by
      rw [filter_insert, if_neg (lt_irrefl _), filter_true_of_mem hlt]
    have hLm : (insert m P).filter (m < ·) = ∅ :=
      filter_false_of_mem ((forall_mem_insert _ _ _).mpr ⟨lt_irrefl _, fun p hp ↦ (hlt _ hp).not_gt⟩)
    have hrest (p : ℕ) (hp : p ∈ P) :
        w p * volumeOn w ((insert m P).filter (p < ·)) * cdf w ((insert m P).filter (· < p)) (Y / p) =
          (1 - w m) * (w p * volumeOn w (P.filter (p < ·)) * cdf w (P.filter (· < p)) (Y / p)) := by
      rw [filter_insert, if_pos (hlt p hp), filter_insert, if_neg (hlt p hp).not_gt]
      simp only [volumeOn, prod_insert (fun h ↦ hm (mem_filter.mp h).1)]
      ring
    rw [cdf_insert w P hm hm0, ih hP', sum_insert hm, hSm, hLm, sum_congr rfl hrest, ← mul_sum]
    simp only [volumeOn, prod_empty, mul_one, prod_insert hm]
    ring

theorem cdf_eq_divisorMass (s : BoundingSieve) (Y : ℝ) :
    cdf (fun p ↦ s.nu p) s.prodPrimes.primeFactors Y =
      ∑ l ∈ s.prodPrimes.divisors, if (l : ℝ) ≤ Y then divisorMass s l else 0 := by
  classical
  rw [← Nat.divisors_filter_squarefree_of_squarefree s.prodPrimes_squarefree,
    Nat.sum_divisors_filter_squarefree s.prodPrimes_ne_zero, Nat.factors_eq]
  unfold cdf
  refine sum_congr rfl fun t ht ↦ ?_
  have ht' : ∀ p ∈ t, Nat.Prime p := fun p hp ↦ Nat.prime_of_mem_primeFactors (mem_powerset.mp ht hp)
  rw [t.prod_val, Function.id_def, divisorMass, Nat.primeFactors_prod ht']
  rfl

theorem cdf_nonneg (w : ℕ → ℝ) (P : Finset ℕ) (Y : ℝ)
    (hw : ∀ p ∈ P, w p ∈ Set.Icc 0 1) : 0 ≤ cdf w P Y := by
  refine sum_nonneg fun S hS ↦ ?_
  split_ifs
  · exact mul_nonneg (prod_nonneg fun p hp ↦ (hw p (mem_powerset.mp hS hp)).1)
      (prod_nonneg fun p hp ↦ sub_nonneg.mpr (hw p (mem_sdiff.mp hp).1).2)
  · exact le_rfl

theorem cdf_mono (w : ℕ → ℝ) (P : Finset ℕ) (hw : ∀ p ∈ P, w p ∈ Set.Icc 0 1) :
    Monotone (cdf w P) := by
  intro X Y hXY
  refine sum_le_sum fun S hS ↦ ?_
  split_ifs with hX hY
  · exact le_rfl
  · exact False.elim (hY (hX.trans hXY))
  · exact mul_nonneg (prod_nonneg fun p hp ↦ (hw p (mem_powerset.mp hS hp)).1)
      (prod_nonneg fun p hp ↦ sub_nonneg.mpr (hw p (mem_sdiff.mp hp).1).2)
  · exact le_rfl

theorem selberg_reciprocal_as_cdf (s : BoundingSieve) {D : ℝ} (hD : 0 ≤ D) :
    (∑ l ∈ s.prodPrimes.divisors, if (l : ℝ)^2 ≤ D then s.selbergTerms l else 0)⁻¹ =
      volume s / cdf (fun p ↦ s.nu p) s.prodPrimes.primeFactors (Real.sqrt D) := by
  rw [selberg_reciprocal_as_mass, cdf_eq_divisorMass]
  congr 1
  exact sum_congr rfl fun l hl ↦ by simp only [Real.le_sqrt (Nat.cast_nonneg l) hD]

theorem cdf_compl_le_moment (w : ℕ → ℝ) (P : Finset ℕ) (r : ℝ) (hr : 0 ≤ r)
    (hP : ∀ p ∈ P, 0 < p) (hw : ∀ p ∈ P, w p ∈ Set.Icc 0 1)
    (Y : ℝ) (hY : 0 < Y) :
    1 - cdf w P Y ≤ (∏ p ∈ P, (1 - w p + w p * (p : ℝ) ^ r)) / Y ^ r := by
  classical
  induction P using Finset.induction_on generalizing Y with
  | empty =>
    by_cases h1 : 1 ≤ Y
    · simp [cdf, volumeOn, h1, (Real.rpow_pos_of_pos hY r).le]
    · simpa [cdf, volumeOn, h1] using
        (one_le_div₀ (Real.rpow_pos_of_pos hY r)).mpr (Real.rpow_le_one hY.le (le_of_not_ge h1) hr)
  | insert p P hp ih =>
    have hp0 := hP p (mem_insert_self p P)
    have hp0' : 0 < (p : ℝ) := by exact_mod_cast hp0
    have hP' : ∀ q ∈ P, 0 < q := fun q hq ↦ hP q (mem_insert_of_mem hq)
    have hw' : ∀ q ∈ P, w q ∈ Set.Icc 0 1 := fun q hq ↦ hw q (mem_insert_of_mem hq)
    have hwp := hw p (mem_insert_self p P)
    rw [cdf_insert w P hp hp0, prod_insert hp]
    calc
      _ = (1 - w p) * (1 - cdf w P Y) + w p * (1 - cdf w P (Y / p)) := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (ih hP' hw' Y hY) (sub_nonneg.mpr hwp.2))
        (mul_le_mul_of_nonneg_left (ih hP' hw' (Y / p) (div_pos hY hp0')) hwp.1)
      _ = _ := by rw [Real.div_rpow hY.le hp0'.le, div_div_eq_mul_div]; ring

private theorem exp_two_mul_le_chord {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp (2*x) ≤ 1 + (Real.exp 2 - 1) * x := by
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (2 : ℝ))
    (sub_nonneg.mpr hx1) hx (sub_add_cancel 1 x)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_comm x 2] using
    h.trans_eq (by simp [smul_eq_mul]; ring)

private theorem chernoff_constant : Real.exp ((Real.exp 2 - 1) * (2001 / 1000)) ≤ 400000 := by
  have h1 : Real.exp 1 ≤ 2.72 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have h2 : Real.exp 2 ≤ (2.72 : ℝ)^2 := by
    simpa only [Real.exp_one_pow, Nat.cast_ofNat] using (pow_le_pow_left₀ (Real.exp_nonneg 1) h1 2)
  have h13 : Real.exp 13 ≤ (2.72 : ℝ)^13 := by
    simpa only [Real.exp_one_pow, Nat.cast_ofNat] using (pow_le_pow_left₀ (Real.exp_nonneg 1) h1 13)
  calc
    _ ≤ Real.exp (13 - 1/6) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 13 / Real.exp (1/6) := Real.exp_sub _ _
    _ ≤ 400000 := by
      rw [div_le_iff₀ (Real.exp_pos _)]
      linarith [Real.add_one_le_exp (1/6)]

theorem cdf_compl_le_chernoff (w : ℕ → ℝ) (P : Finset ℕ) {z : ℝ} (hz : 1 < z)
    (hP : ∀ p ∈ P, 0 < p ∧ (p : ℝ) ≤ z) (hw : ∀ p ∈ P, w p ∈ Set.Icc 0 1)
    (hmean : ∑ p ∈ P, w p * (Real.log p / Real.log z) ≤ 2001 / 1000) (s : ℝ) :
    1 - cdf w P (z ^ (s/2)) ≤ 400000 * Real.exp (-s) := by
  have hz0 : 0 < z := zero_lt_one.trans hz
  have hlog := Real.log_pos hz
  have he2 : 0 ≤ Real.exp 2 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  let r := 2 / Real.log z
  let x (p : ℕ) := Real.log p / Real.log z
  have hx (p : ℕ) (hp : p ∈ P) : 0 ≤ x p ∧ x p ≤ 1 := by
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hP p hp).1
    exact ⟨div_nonneg (Real.log_nonneg hp1) hlog.le,
      (div_le_one hlog).mpr (Real.log_le_log (zero_lt_one.trans_le hp1) (hP p hp).2)⟩
  have hm := cdf_compl_le_moment w P r (div_nonneg (by norm_num) hlog.le)
    (fun p hp ↦ (hP p hp).1) hw (z^(s/2)) (Real.rpow_pos_of_pos hz0 _)
  have hprod : (∏ p ∈ P, (1 - w p + w p * (p : ℝ) ^ r)) ≤
      Real.exp ((Real.exp 2 - 1) * (2001/1000)) := by
    calc
      _ ≤ ∏ p ∈ P, Real.exp ((Real.exp 2 - 1) * (w p * x p)) := by
        apply Finset.prod_le_prod
        · intro p hp
          exact add_nonneg (sub_nonneg.mpr (hw p hp).2)
            (mul_nonneg (hw p hp).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        · intro p hp
          have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p hp).1
          have heq : (p : ℝ)^r = Real.exp (2*x p) := by
            rw [Real.rpow_def_of_pos hp0]
            dsimp [r, x]
            ring_nf
          have ha := mul_le_mul_of_nonneg_left (exp_two_mul_le_chord (hx p hp).1 (hx p hp).2) (hw p hp).1
          rw [heq]
          linarith only [ha, Real.add_one_le_exp ((Real.exp 2 - 1) * (w p * x p))]
      _ = Real.exp ((Real.exp 2 - 1) * ∑ p ∈ P, w p * x p) := by rw [mul_sum, Real.exp_sum]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmean he2)
  have hbase : (z ^ (s/2)) ^ r = Real.exp s := by
    rw [← Real.rpow_mul hz0.le, Real.rpow_def_of_pos hz0]
    congr 1
    dsimp [r]
    field_simp [hlog.ne']
  calc
    _ ≤ _ := hm
    _ ≤ Real.exp ((Real.exp 2 - 1) * (2001/1000)) / Real.exp s := by
      rw [hbase]
      exact div_le_div_of_nonneg_right hprod (Real.exp_pos _).le
    _ ≤ 400000 * Real.exp (-s) := by
      rw [Real.exp_neg, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right chernoff_constant (Real.exp_pos _).le

end BethSelberg

end

section

open Finset

namespace BethGrid

open BethSelberg

-- 質量を最大素数で分け、しきい値qまでの分を足し戻す
theorem mass_le_cut (w : ℕ → ℝ) (P : Finset ℕ) (q : ℕ) :
    volumeOn w P + ∑ p ∈ P, (if p ≤ q then w p * volumeOn w (P.filter (p < ·)) else 0) =
      volumeOn w (P.filter (q < ·)) := by
  classical
  induction P using Finset.induction_on_min with
  | empty => simp
  | insert m P hlt ih =>
    have hm : m ∉ P := fun h => (hlt m h).false
    have hfilter (p : ℕ) (hp : p ∈ P) :
        (insert m P).filter (p < ·) = P.filter (p < ·) := by
      rw [filter_insert, if_neg (hlt p hp).not_gt]
    have htop : (insert m P).filter (m < ·) = P := by
      rw [filter_insert, if_neg (lt_irrefl _), filter_true_of_mem hlt]
    have hexp : volumeOn w (insert m P) = (1 - w m) * volumeOn w P := by
      simp [volumeOn, hm]
    rw [hexp, sum_insert hm, htop]
    have hsum : (∑ p ∈ P, if p ≤ q then w p * volumeOn w ((insert m P).filter (p < ·)) else 0) =
        ∑ p ∈ P, if p ≤ q then w p * volumeOn w (P.filter (p < ·)) else 0 :=
      sum_congr rfl fun p hp => by rw [hfilter p hp]
    rw [hsum, filter_insert]
    by_cases hmq : m ≤ q
    · rw [if_pos hmq, if_neg (not_lt.mpr hmq)]
      linarith
    · have hqm : q < m := lt_of_not_ge hmq
      have hall : ∀ p ∈ P, q < p := fun p hp => hqm.trans (hlt p hp)
      rw [if_neg hmq, if_pos hqm, filter_true_of_mem hall]
      have hzero : (∑ p ∈ P, if p ≤ q then w p * volumeOn w (P.filter (p < ·)) else 0) = 0 :=
        sum_eq_zero fun p hp => if_neg (not_le.mpr (hall p hp))
      rw [hzero, add_zero, add_zero, hexp]

-- 小さい素数から除くときに使う逆方向の和
theorem mass_gt_cut (w : ℕ → ℝ) (P : Finset ℕ) (q : ℕ) :
    volumeOn w P + ∑ p ∈ P, (if q < p then w p * volumeOn w (P.filter (· < p)) else 0) =
      volumeOn w (P.filter (· ≤ q)) := by
  classical
  induction P using Finset.induction_on_max with
  | empty => simp
  | insert m P hlt ih =>
    have hm : m ∉ P := fun h => (hlt m h).false
    have hfilter (p : ℕ) (hp : p ∈ P) :
        (insert m P).filter (· < p) = P.filter (· < p) := by
      rw [filter_insert, if_neg (hlt p hp).not_gt]
    have htop : (insert m P).filter (· < m) = P := by
      rw [filter_insert, if_neg (lt_irrefl _), filter_true_of_mem hlt]
    have hexp : volumeOn w (insert m P) = (1 - w m) * volumeOn w P := by
      simp [volumeOn, hm]
    rw [hexp, sum_insert hm, htop]
    have hsum : (∑ p ∈ P, if q < p then w p * volumeOn w ((insert m P).filter (· < p)) else 0) =
        ∑ p ∈ P, if q < p then w p * volumeOn w (P.filter (· < p)) else 0 :=
      sum_congr rfl fun p hp => by rw [hfilter p hp]
    rw [hsum, filter_insert]
    by_cases hqm : q < m
    · rw [if_pos hqm, if_neg (not_le.mpr hqm)]
      linarith
    · have hmq : m ≤ q := le_of_not_gt hqm
      have hall : ∀ p ∈ P, p ≤ q := fun p hp => (hlt p hp).le.trans hmq
      rw [if_neg hqm, if_pos hmq, filter_true_of_mem hall]
      have hzero : (∑ p ∈ P, if q < p then w p * volumeOn w (P.filter (· < p)) else 0) = 0 :=
        sum_eq_zero fun p hp => if_neg (not_lt.mpr (hall p hp))
      rw [hzero, add_zero, add_zero, hexp]

theorem lower_cdf_layers (w : ℕ → ℝ) (P I : Finset ℕ) (Y : ℝ)
    (hY : 1 ≤ Y) (hp : ∀ p ∈ P, 0 < p) (hw : ∀ p ∈ P, w p ∈ Set.Icc 0 1)
    (cut : ℕ → ℕ) (inc lb : ℕ → ℝ)
    (hi : ∀ j ∈ I, 0 ≤ inc j) (hi_sum : ∑ j ∈ I, inc j ≤ 1)
    (hcut : ∀ j ∈ I, lb j ≤ volumeOn w (P.filter (cut j < ·)))
    (hchild : ∀ p ∈ P, (∑ j ∈ I, if p ≤ cut j then inc j else 0) ≤
      cdf w (P.filter (· < p)) (Y / p)) :
    (∑ j ∈ I, inc j * lb j) ≤ cdf w P Y := by
  classical
  let mass (p : ℕ) := w p * volumeOn w (P.filter (p < ·))
  have hvol : 0 ≤ volumeOn w P := prod_nonneg fun p h => sub_nonneg.mpr (hw p h).2
  have hmass (p : ℕ) (h : p ∈ P) : 0 ≤ mass p :=
    mul_nonneg (hw p h).1 (prod_nonneg fun q hq => sub_nonneg.mpr (hw q (mem_filter.mp hq).1).2)
  calc
    (∑ j ∈ I, inc j * lb j) ≤ ∑ j ∈ I, inc j * volumeOn w (P.filter (cut j < ·)) :=
      sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hcut j hj) (hi j hj)
    _ = (∑ j ∈ I, inc j) * volumeOn w P +
        ∑ p ∈ P, mass p * ∑ j ∈ I, if p ≤ cut j then inc j else 0 := by
      have hexp (j : ℕ) : volumeOn w (P.filter (cut j < ·)) = volumeOn w P +
          ∑ p ∈ P, if p ≤ cut j then mass p else 0 := (mass_le_cut w P (cut j)).symm
      calc
        _ = ∑ j ∈ I, inc j * (volumeOn w P + ∑ p ∈ P, if p ≤ cut j then mass p else 0) :=
          sum_congr rfl fun j _ => by rw [hexp j]
        _ = _ := by
          simp_rw [mul_add, mul_sum, mul_ite, mul_zero]
          rw [sum_add_distrib, sum_mul]
          congr 1
          rw [sum_comm]
          refine sum_congr rfl fun p _ => sum_congr rfl fun j _ => ?_
          split_ifs <;> ring
    _ ≤ volumeOn w P + ∑ p ∈ P, mass p * cdf w (P.filter (· < p)) (Y / p) := by
      apply add_le_add
      · simpa using mul_le_mul_of_nonneg_right hi_sum hvol
      · exact sum_le_sum fun p h => mul_le_mul_of_nonneg_left (hchild p h) (hmass p h)
    _ = cdf w P Y := (cdf_eq_sum_max w P Y hY hp).symm


-- 前からの累積質量をすべて抑えられれば、非負で減少する係数を掛けて足した和も抑えられる
theorem weighted_range_le (n : ℕ) (a b f : ℕ → ℝ)
    (hprefix : ∀ k ≤ n, ∑ i ∈ range k, a i ≤ ∑ i ∈ range k, b i)
    (hf : Antitone f) (hpos : ∀ i < n, 0 ≤ f i) :
    ∑ i ∈ range n, a i * f i ≤ ∑ i ∈ range n, b i * f i := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have hdiff := ih (fun i => f i - f n)
      (fun k hk => hprefix k (Nat.le_succ_of_le hk))
      (fun x y hxy => sub_le_sub_right (hf hxy) _)
      (fun i hi => sub_nonneg.mpr (hf hi.le))
    have hc := mul_le_mul_of_nonneg_right (hprefix (n+1) le_rfl) (hpos n (Nat.lt_succ_self n))
    simp only [mul_sub, sum_sub_distrib, ← sum_mul] at hdiff
    rw [sum_range_succ, sum_range_succ, add_mul, add_mul] at hc
    rw [sum_range_succ, sum_range_succ]
    linarith

-- 各素数を指数の区間番号に振り分けた有限和をまとめる
theorem group_bins (P : Finset ℕ) (n : ℕ) (bin : ℕ → ℕ) (a f : ℕ → ℝ) :
    ∑ j ∈ range n, (∑ p ∈ P, if bin p = j then a p else 0) * f j =
      ∑ p ∈ P, if bin p < n then a p * f (bin p) else 0 := by
  classical
  simp_rw [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  simp

theorem upper_grid_sum (P : Finset ℕ) (j n : ℕ) (hj : 0 < j)
    (bin : ℕ → ℕ) (a f : ℕ → ℝ) (K : ℝ) (hK : 1 ≤ K)
    (hprefix : ∀ k ≤ n,
      (∑ p ∈ P, if bin p < k then a p else 0) ≤ K * ((j + k : ℕ) : ℝ)^2 / (j : ℝ)^2 - 1)
    (hf : Antitone f) (hf0 : ∀ k, 0 ≤ f k) :
    (∑ p ∈ P, if bin p < n then a p * f (bin p) else 0) ≤
      (K - 1) * f 0 + K / (j : ℝ)^2 *
        ∑ k ∈ range n, (2 * ((j + k : ℕ) : ℝ) + 1) * f k := by
  classical
  let A (i : ℕ) := ∑ p ∈ P, if bin p = i then a p else 0
  let d (i : ℕ) := K / (j : ℝ)^2 * (2 * ((j + i : ℕ) : ℝ) + 1)
  let b (i : ℕ) := (if i = 0 then K - 1 else 0) + d i
  have hj0 : (j : ℝ) ≠ 0 := by positivity
  have hd (k : ℕ) : ∑ i ∈ range k, d i =
      K * ((j + k : ℕ) : ℝ)^2 / (j : ℝ)^2 - K := by
    induction k with
    | zero => simp; field_simp; ring
    | succ k ih =>
      rw [sum_range_succ, ih]
      simp only [d, Nat.cast_add, Nat.cast_succ]
      ring
  have hb (k : ℕ) (hk : 0 < k) :
      ∑ i ∈ range k, b i = K * ((j + k : ℕ) : ℝ)^2 / (j : ℝ)^2 - 1 := by
    simp only [b, sum_add_distrib, hd]
    rw [sum_ite_eq', if_pos (mem_range.mpr hk)]
    ring
  have hcomp (k : ℕ) (hk : k ≤ n) : ∑ i ∈ range k, A i ≤ ∑ i ∈ range k, b i := by
    by_cases h : k = 0
    · simp [h]
    · rw [hb k (Nat.pos_of_ne_zero h)]
      have hgroup := group_bins P k bin a (fun _ => 1)
      simpa only [mul_one, A] using (le_of_eq_of_le (by simpa only [mul_one] using hgroup) (hprefix k hk))
  rw [← group_bins P n bin a f]
  calc
    _ ≤ ∑ i ∈ range n, b i * f i := weighted_range_le n A b f hcomp hf (fun k _ => hf0 k)
    _ ≤ _ := by
      simp_rw [b, add_mul, ite_mul, zero_mul, d, mul_assoc]
      rw [sum_add_distrib, ← mul_sum, sum_ite_eq']
      split_ifs with h
      · simp only [add_mul, mul_assoc]
        exact le_rfl
      · simp only [mem_range] at h
        have hzero : n = 0 := by omega
        subst n
        simpa using mul_nonneg (sub_nonneg.mpr hK) (hf0 0)

end BethGrid

end

section

open Finset

namespace BethUpperGrid

open BethSelberg

noncomputable def mass (w : ℕ → ℝ) (P : Finset ℕ) (p : ℕ) : ℝ :=
  w p * volumeOn w (P.filter (· < p)) / volumeOn w P

theorem volume_split (w : ℕ → ℝ) (P : Finset ℕ) (q : ℕ) :
    volumeOn w (P.filter (· ≤ q)) * volumeOn w (P.filter (q < ·)) = volumeOn w P := by
  classical
  unfold volumeOn
  simpa only [not_le] using
    (prod_filter_mul_prod_filter_not P (fun p => p ≤ q) (fun p => 1 - w p))

theorem mass_gt (w : ℕ → ℝ) (P : Finset ℕ) (q : ℕ)
    (hw : ∀ p ∈ P, w p < 1) :
    (∑ p ∈ P, if q < p then mass w P p else 0) = (volumeOn w (P.filter (q < ·)))⁻¹ - 1 := by
  classical
  have hv : 0 < volumeOn w P := prod_pos fun p hp => sub_pos.mpr (hw p hp)
  have hhi : 0 < volumeOn w (P.filter (q < ·)) :=
    prod_pos fun p hp => sub_pos.mpr (hw p (mem_filter.mp hp).1)
  have hc := BethGrid.mass_gt_cut w P q
  have hvsplit := volume_split w P q
  have hraw : (∑ p ∈ P, if q < p then w p * volumeOn w (P.filter (· < p)) else 0) =
      volumeOn w (P.filter (· ≤ q)) - volumeOn w P := by linarith
  calc
    _ = (∑ p ∈ P, if q < p then w p * volumeOn w (P.filter (· < p)) else 0) / volumeOn w P := by
      rw [sum_div]
      refine sum_congr rfl fun p _ => ?_
      split_ifs <;> simp [mass]
    _ = _ := by
      rw [hraw, sub_div, div_self hv.ne', ← hvsplit, div_mul_eq_div_div,
        div_self (show volumeOn w (P.filter (· ≤ q)) ≠ 0 from
          (prod_pos fun p hp => sub_pos.mpr (hw p (mem_filter.mp hp).1)).ne'), one_div]

-- pの区間番号についての上限を、実数によるp自身の下限へ換算する
theorem normalized_cumulative {s x z D K : ℝ} (hs : 0 < s) (hsx : s ≤ x)
    (hz : 1 < z) (hK : 0 < K) (hscale : s * Real.log z ≤ Real.log D)
    (w : ℕ → ℝ) (P : Finset ℕ) (hp : ∀ p ∈ P, 1 < p) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p < 1)
    (hcut : (s/x)^2 / K ≤ volumeOn w (P.filter (⌊z ^ (s/x)⌋₊ < ·))) :
    (∑ p ∈ P, if Real.log D / Real.log p < x then mass w P p else 0) ≤ K * (x/s)^2 - 1 := by
  classical
  let q := ⌊z ^ (s/x)⌋₊
  have hv : 0 < volumeOn w P := prod_pos fun p hp => sub_pos.mpr (hw p hp).2
  have hmass (p : ℕ) (h : p ∈ P) : 0 ≤ mass w P p :=
    div_nonneg (mul_nonneg (hw p h).1 (prod_nonneg fun a ha =>
      (sub_pos.mpr (hw a (mem_filter.mp ha).1).2).le)) hv.le
  have hx := hs.trans_le hsx
  have hl : 0 < (s / x)^2 / K := by positivity
  calc
    _ ≤ ∑ p ∈ P, if q < p then mass w P p else 0 := by
      apply sum_le_sum
      intro p h
      have hp' : (1 : ℝ) < p := by exact_mod_cast hp p h
      split_ifs with hux hqp hqp
      · exact le_rfl
      · have hlog : Real.log z * (s/x) < Real.log p := by
          rw [← mul_div_assoc, div_lt_iff₀ hx, mul_comm (Real.log z), mul_comm (Real.log p)]
          exact hscale.trans_lt ((div_lt_iff₀ (Real.log_pos hp')).mp hux)
        have hz0 := zero_lt_one.trans hz
        have hlt : z ^ (s/x) < (p:ℝ) := by
          rw [Real.rpow_def_of_pos hz0, ← Real.exp_log (zero_lt_one.trans hp'), Real.exp_lt_exp]
          exact hlog
        exact False.elim (hqp (by exact_mod_cast ((Nat.floor_le (Real.rpow_nonneg hz0.le _)).trans_lt hlt)))
      · exact hmass p h
      · exact le_rfl
    _ = _ := mass_gt w P q (fun p h => (hw p h).2)
    _ ≤ ((s/x)^2 / K)⁻¹ - 1 := sub_le_sub_right (inv_anti₀ hl hcut) _
    _ = _ := by field_simp

end BethUpperGrid

end

section

open Finset

namespace BethTail

private theorem exp_small {b : ℝ} (hb : 26 ≤ b) :
    Real.exp (-(b/2)) ≤ 1/128 := by
  have h : 128 ≤ Real.exp (b/2) := by
    calc (128 : ℝ) = (2 : ℝ)^7 := by norm_num
         _ ≤ (Real.exp 1)^7 := by gcongr; exact Real.exp_one_gt_two.le
         _ = Real.exp (7 * 1) := by rw [show (7:ℝ) = ((7:ℕ):ℝ) by norm_num, Real.exp_nat_mul]
         _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h

private theorem decay_bin (k : ℕ) {b u : ℝ} (hb : 26 ≤ b) (hu : b + b / 2 * k ≤ u) :
    Real.exp (1-u) ≤ Real.exp (1-b) * (1/128 : ℝ)^k := by
  calc Real.exp (1-u) ≤ Real.exp ((1-b) + k * (-(b/2))) := Real.exp_le_exp.mpr (by linarith)
       _ = Real.exp (1-b) * (Real.exp (-(b/2)))^k := by rw [Real.exp_add, Real.exp_nat_mul]
       _ ≤ _ := by gcongr; exact exp_small hb

private theorem bin_growth (k : ℕ) : ((k : ℝ) + 3)^2 ≤ 9 * (4:ℝ)^k := by
  have h : (k : ℝ) + 3 ≤ 3 * (2:ℝ)^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [Nat.cast_succ, pow_succ]
      linarith [show (0:ℝ) ≤ k by positivity]
  calc ((k : ℝ)+3)^2 ≤ (3*2^k)^2 := by gcongr
       _ = 9 * (4:ℝ)^k := by
         rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]; norm_num

/-- 対数比がb以上の素数を幅b/2の区間に分け、指数関数の残りを合計する -/
theorem exp_tail (P : Finset ℕ) (u m : ℕ → ℝ) (s b K : ℝ)
    (hs : 0 < s) (_hsb : s ≤ b) (hb : 26 ≤ b) (hK : 0 ≤ K)
    (hm : ∀ p ∈ P, 0 ≤ m p)
    (hcum : ∀ x : ℝ, b ≤ x → (∑ p ∈ P, if u p < x then m p else 0) ≤ K * (x/s)^2) :
    (∑ p ∈ P.filter (fun p => b ≤ u p), m p * Real.exp (1 - u p)) ≤
      (5/2 : ℝ) * K * (b/s)^2 * Real.exp (1-b) := by
  classical
  let Q := P.filter fun p => b ≤ u p
  let idx (p : ℕ) := ⌊2*(u p / b - 1)⌋₊
  let M := Q.sup idx + 1
  let c (k : ℕ) := Real.exp (1-b) * (1/128 : ℝ)^k
  have hb0 : 0 < b := by linarith
  have hQ (p : ℕ) (hp : p ∈ Q) := mem_filter.mp hp
  have hi (p : ℕ) (hp : p ∈ Q) : idx p < M := Nat.lt_succ_of_le (le_sup hp)
  have hbins (p : ℕ) (hp : p ∈ Q) :
      b + b/2 * idx p ≤ u p ∧ u p < b * ((idx p : ℝ) + 3) / 2 := by
    have h1 : 1 ≤ u p / b := (le_div_iff₀ hb0).mpr (by simpa using (hQ p hp).2)
    have hl : (idx p : ℝ) ≤ 2*(u p / b - 1) := Nat.floor_le (by linarith)
    have hh : 2*(u p / b - 1) < (idx p : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlo := mul_le_mul_of_nonneg_right hl hb0.le
    have hhi := mul_lt_mul_of_pos_right hh hb0
    field_simp at hlo hhi
    constructor <;> nlinarith
  have hmass (k : ℕ) : (∑ p ∈ Q, if idx p = k then m p else 0) ≤
      K * ((b/s)^2 /4 * (9 * (4:ℝ)^k)) := by
    let x := b * ((k:ℝ)+3)/2
    have hbx : b ≤ x := by dsimp [x]; nlinarith [show 0 ≤ b * (k : ℝ) by positivity]
    calc
      _ ≤ ∑ p ∈ Q, if u p < x then m p else 0 := by
        refine sum_le_sum fun p hp => ?_
        by_cases hk : idx p = k
        · rw [if_pos hk, if_pos (show u p < x by simpa [x,hk] using (hbins p hp).2)]
        · rw [if_neg hk]; split_ifs <;> simp [hm p (hQ p hp).1]
      _ ≤ ∑ p ∈ P, if u p < x then m p else 0 := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro p hp _; split_ifs <;> simp [hm p hp]
      _ ≤ K * (x/s)^2 := hcum x hbx
      _ = K * ((b/s)^2 /4 * ((k:ℝ)+3)^2) := by dsimp [x]; ring
      _ ≤ _ := by gcongr; exact bin_growth k
  have hgeo : (∑ k ∈ range M, (1/32:ℝ)^k) ≤ 10/9 := by
    rw [geom_sum_eq (by norm_num : (1/32:ℝ) ≠ 1)]
    rw [div_le_iff_of_neg (by norm_num)]
    nlinarith [show 0 ≤ (1/32:ℝ)^M by positivity]
  let C := K * (b/s)^2 * Real.exp (1-b) * (9/4)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ ∑ p ∈ Q, if idx p < M then m p * c (idx p) else 0 := by
      refine sum_le_sum fun p hp => ?_
      rw [if_pos (hi p hp)]
      exact mul_le_mul_of_nonneg_left (decay_bin (idx p) hb (hbins p hp).1) (hm p (hQ p hp).1)
    _ = ∑ k ∈ range M, (∑ p ∈ Q, if idx p = k then m p else 0) * c k :=
      (BethGrid.group_bins Q M idx m c).symm
    _ ≤ ∑ k ∈ range M, C * (1/32:ℝ)^k := by
      apply sum_le_sum
      intro k _
      calc _ ≤ K * ((b/s)^2 /4 * (9 * (4:ℝ)^k)) * c k :=
                 mul_le_mul_of_nonneg_right (hmass k) (by dsimp [c]; positivity)
           _ = C * ((4:ℝ)*(1/128))^k := by dsimp [C,c]; rw [mul_pow]; ring
           _ = _ := by norm_num
    _ = C * (∑ k ∈ range M, (1/32:ℝ)^k) := (mul_sum ..).symm
    _ ≤ C * (10/9) := mul_le_mul_of_nonneg_left hgeo hC
    _ = _ := by dsimp [C]; ring


private theorem tail_at_forty :
    (5 / 2 : ℝ) * 3000000 * 40^2 * Real.exp (1 - 40) ≤ 1 / 1000000 := by
  have hbase : (2.7 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hpow := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) hbase 39
  rw [Real.exp_one_pow] at hpow
  norm_num at hpow
  rw [show (1 - 40 : ℝ) = -39 by norm_num, Real.exp_neg]
  rw [mul_inv_le_iff₀ (Real.exp_pos _)]
  linarith

noncomputable def tableStep (K : ℝ) (N j M : ℕ) (F : ℕ → ℝ) : ℝ :=
  (K-1) * F (j-N) + K / (j : ℝ)^2 *
    ((N:ℝ)^2 / 1000000 +
      ∑ k ∈ range (M-j), (2*((j+k : ℕ):ℝ)+1) * F (j+k-N))

theorem table_step_bound (P : Finset ℕ) (m u e : ℕ → ℝ) (F : ℕ → ℝ)
    (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (hjM : j ≤ 40*N) (K : ℝ) (hK : 1 ≤ K)
    (hF : Antitone F) (hF0 : ∀ a, 0 ≤ F a) (hm : ∀ p ∈ P, 0 ≤ m p)
    (hu : ∀ p ∈ P, (j:ℝ)/N ≤ u p)
    (hcum : ∀ x : ℝ, (j:ℝ)/N ≤ x →
      (∑ p ∈ P, if u p < x then m p else 0) ≤ K*(x/((j:ℝ)/N))^2 - 1)
    (hnear : ∀ p ∈ P, ⌊(N:ℝ)*u p⌋₊ < 40*N → e p ≤ F (⌊(N:ℝ)*u p⌋₊ - N))
    (hfar : ∀ p ∈ P, 40 ≤ u p → e p ≤ 3000000 * Real.exp (1-u p)) :
    (∑ p ∈ P, m p * e p) ≤ tableStep K N j (40*N) F := by
  classical
  let s := (j:ℝ) / N
  let M := 40*N
  let bin (p : ℕ) := ⌊(N:ℝ)*u p⌋₊ - j
  have hN0 : (0:ℝ) < N := by positivity
  have hj0 : (0:ℝ) < j := by positivity
  have hs : 0 < s := by dsimp [s]; positivity
  have hs40 : s ≤ 40 := by
    rw [div_le_iff₀ hN0]
    exact_mod_cast hjM
  have hjfloor (p : ℕ) (hp : p ∈ P) : j ≤ ⌊(N:ℝ)*u p⌋₊ := by
    apply Nat.le_floor
    have h := (div_le_iff₀ hN0).mp (hu p hp)
    linarith
  have hfbin (p : ℕ) (hp : p ∈ P) : j + bin p = ⌊(N:ℝ)*u p⌋₊ :=
    Nat.add_sub_of_le (hjfloor p hp)
  have hprefix (k : ℕ) (hk : k ≤ M - j) :
      (∑ p ∈ P, if bin p < k then m p else 0) ≤ K * ((j+k:ℕ):ℝ)^2 / (j:ℝ)^2 - 1 := by
    let x := ((j+k:ℕ):ℝ)/N
    have hsx : s ≤ x := by dsimp [s,x]; gcongr; omega
    calc _ ≤ ∑ p ∈ P, if u p < x then m p else 0 := by
           apply sum_le_sum
           intro p hp
           by_cases H : bin p < k
           · have hn : ⌊(N:ℝ)*u p⌋₊ < j+k := by rw [← hfbin p hp]; omega
             have hr : (N:ℝ)*u p < ((j+k:ℕ):ℝ) :=
               (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hn)
             rw [if_pos H, if_pos (show u p < x by
               change u p < ((j+k:ℕ):ℝ)/N; rw [lt_div_iff₀ hN0]; linarith)]
           · rw [if_neg H]; split_ifs <;> simp [hm p hp]
         _ ≤ _ := (hcum x hsx).trans_eq (by dsimp [x]; field_simp)
  have hnearSum := BethGrid.upper_grid_sum P j (M-j) hj bin m
    (fun k => F (j+k-N)) K hK hprefix (fun a b hab => hF (by omega)) (fun k => hF0 _)
  have htail := exp_tail P u m s 40 K hs hs40 (by norm_num) (by linarith) hm (fun x hx =>
    (hcum x (hs40.trans hx)).trans (by dsimp [s]; linarith))
  have splitBound : (∑ p ∈ P, m p * e p) ≤
      (∑ p ∈ P, if bin p < M-j then m p * F (j+bin p-N) else 0) +
      3000000 * ∑ p ∈ P.filter (fun p => 40 ≤ u p), m p * Real.exp (1-u p) := by
    rw [mul_sum, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun p hp => ?_
    by_cases h : bin p < M-j
    · have hn : ⌊(N:ℝ)*u p⌋₊ < 40*N := by rw [← hfbin p hp]; dsimp [M] at h; omega
      have hpos : ¬ 40 ≤ u p := by
        intro h40
        have : 40*N ≤ ⌊(N:ℝ)*u p⌋₊ := Nat.le_floor (by push_cast; nlinarith)
        omega
      rw [if_pos h, if_neg hpos, add_zero, hfbin p hp]
      exact mul_le_mul_of_nonneg_left (hnear p hp hn) (hm p hp)
    · have hh : 40*N ≤ ⌊(N:ℝ)*u p⌋₊ := by rw [← hfbin p hp]; dsimp [M] at h; omega
      have hf : (⌊(N:ℝ)*u p⌋₊ : ℝ) ≤ (N:ℝ)*u p := Nat.floor_le (mul_nonneg hN0.le (hs.le.trans (hu p hp)))
      have hr : (40:ℝ)*N ≤ (⌊(N:ℝ)*u p⌋₊:ℝ) := by exact_mod_cast hh
      have h40 : 40 ≤ u p := by nlinarith
      rw [if_neg h, if_pos h40, zero_add]
      nlinarith [mul_le_mul_of_nonneg_left (hfar p hp h40) (hm p hp)]
  have htailScaled : 3000000 * (∑ p ∈ P.filter (fun p => 40 ≤ u p), m p * Real.exp (1-u p))
      ≤ K / (j:ℝ)^2 * ((N:ℝ)^2/1000000) := by
    calc
      _ ≤ 3000000 * ((5/2) * K * (40/s)^2 * Real.exp (1-40)) :=
        mul_le_mul_of_nonneg_left htail (by norm_num)
      _ = K * ((N:ℝ)^2 / (j:ℝ)^2) * ((5/2) * 3000000 * 40^2 * Real.exp (1-40)) := by
        dsimp [s]; field_simp <;> ring
      _ ≤ K * ((N:ℝ)^2 / (j:ℝ)^2) * (1/1000000) :=
        mul_le_mul_of_nonneg_left tail_at_forty (by positivity)
      _ = _ := by ring
  exact splitBound.trans ((add_le_add hnearSum htailScaled).trans_eq (by simp only [tableStep,M,Nat.add_zero]; ring))

end BethTail

end

section

open Finset

namespace BethIteration

open OMABeth BethSelberg BethUpperGrid

def HasBound (upper : Bool) (P : Finset ℕ) (D : ℝ) (w : ℕ → ℝ) (e : ℝ) : Prop :=
  ∃ c : Cert upper P D, if upper then c.main w ≤ volumeOn w P * (1+e)
    else volumeOn w P * (1-e) ≤ c.main w

theorem weaken {upper P D w a b} (h : HasBound upper P D w a) (hab : a ≤ b)
    (hv : 0 ≤ volumeOn w P) : HasBound upper P D w b := by
  obtain ⟨c,hc⟩ := h
  refine ⟨c, ?_⟩
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] at hc ⊢
  · exact (mul_le_mul_of_nonneg_left (by linarith) hv).trans hc
  · exact hc.trans (mul_le_mul_of_nonneg_left (by linarith) hv)

theorem zero_lower (P : Finset ℕ) (D : ℝ) (w : ℕ → ℝ) : HasBound false P D w 1 := by
  exact ⟨Cert.zeroLower P D, by simp⟩

theorem alternating_step {upper : Bool} (P : Finset ℕ) (D : ℝ) (w E : ℕ → ℝ) (e : ℝ)
    (hD : 1 ≤ D) (hp : ∀ p ∈ P, 0 < p) (hw : ∀ p ∈ P, 0 ≤ w p ∧ w p < 1)
    (child : ∀ p ∈ P, HasBound (!upper) (Cert.below P p) (D/p) w (E p))
    (estimate : (∑ p ∈ P, mass w P p * E p) ≤ e) : HasBound upper P D w e := by
  classical
  choose c hc using child
  have hv : 0 < volumeOn w P := prod_pos fun p hm => sub_pos.mpr (hw p hm).2
  have hm := BethGrid.mass_gt_cut w P 0
  have hempty : P.filter (· ≤ 0) = ∅ := filter_false_of_mem fun p h => not_le.mpr (hp p h)
  rw [hempty] at hm
  have hsum : ∑ p ∈ P, w p * volumeOn w (Cert.below P p) = 1 - volumeOn w P := by
    have h : (∑ p ∈ P, if 0 < p then w p * volumeOn w (P.filter (· < p)) else 0) =
        ∑ p ∈ P, w p * volumeOn w (Cert.below P p) :=
      sum_congr rfl fun p h => if_pos (hp p h)
    rw [h] at hm
    simpa [volumeOn] using (eq_sub_of_add_eq' hm)
  have herr : (∑ p ∈ P, w p * volumeOn w (Cert.below P p) * E p) ≤ volumeOn w P * e := by
    calc
      _ = (∑ p ∈ P, mass w P p * E p) * volumeOn w P := by
        rw [sum_mul]; refine sum_congr rfl fun p _ => ?_
        dsimp [mass, Cert.below]; field_simp
      _ ≤ _ := (mul_le_mul_of_nonneg_right estimate hv.le).trans_eq (mul_comm _ _)
  have htotal (t : ℝ) : (∑ p ∈ P.attach,
        w p.val * (volumeOn w (Cert.below P p.val) * (1 + t * E p.val))) =
      (1 - volumeOn w P) + t * ∑ p ∈ P, w p * volumeOn w (Cert.below P p) * E p := by
    rw [Finset.sum_attach P (fun p => w p * (volumeOn w (Cert.below P p) * (1+t*E p)))]
    simp_rw [mul_add, mul_one]
    rw [sum_add_distrib, hsum, mul_sum]
    congr 1; refine sum_congr rfl fun p _ => ?_; ring
  refine ⟨Cert.buchstab hD hp c, ?_⟩
  rw [Cert.main_buchstab]
  cases upper with
  | false =>
    simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false] at hc ⊢
    have H : (∑ p ∈ P.attach, w p.val * (c p.val p.property).main w) ≤
        ∑ p ∈ P.attach, w p.val * (volumeOn w (Cert.below P p.val) * (1+1*E p.val)) :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (by simpa using hc p.val p.property) (hw p.val p.property).1
    rw [htotal 1, one_mul] at H
    linarith
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true] at hc ⊢
    have H : (∑ p ∈ P.attach, w p.val * (volumeOn w (Cert.below P p.val) * (1+(-1)*E p.val))) ≤
        ∑ p ∈ P.attach, w p.val * (c p.val p.property).main w :=
      sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (by simpa [sub_eq_add_neg] using hc p.val p.property) (hw p.val p.property).1
    rw [htotal (-1), neg_one_mul] at H
    linarith

end BethIteration

end

section

/-
Selbergの最適化した篩係数とその平方和を利用する。
以下のメビウス反転、対角化、係数の評価はLeft to SolveのErdos1204.erdos_1204.variants.A_lowerから採った。
Arend MellendijkのPrimeNumberTheoremAnd(55270df80721)、AuxResults・Basic・Selbergの形式化に基づく。
-/


/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module aux_results
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius ArithmeticFunction.omega

open Nat ArithmeticFunction Finset

namespace Aux
theorem sum_over_dvd_ite {α : Type _} [Ring α] {P : ℕ} (hP : P ≠ 0) {n : ℕ} (hn : n ∣ P)
    {f : ℕ → α} : ∑ d ∈ n.divisors, f d = ∑ d ∈ P.divisors, if d ∣ n then f d else 0 :=
  by
  rw [←Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hP hn]

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d:ℤ) else 0) = if l = m then (μ l:ℤ) else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    {n | Squarefree n} (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  rw [sum_divisorsAntidiagonal' (f:= fun x y => μ x • if l=y then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ←isMultiplicative_moebius.map_mul_of_coprime,
        hmul]

      apply coprime_of_squarefree_mul; rw [hmul]; exact hm
    · intro d _ hdl; rw [if_neg hdl.symm, smul_zero]
    · intro h; rw[mem_divisors] at h; exfalso; exact h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩
  · rw [if_neg hl, sum_eq_zero]; intro d hd
    rw [if_neg, smul_zero]
    by_contra h; rw [←h] at hd; exact hl (dvd_of_mem_divisors hd)

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then μ d else 0) = if l = m then μ l else 0 := by
  rw [←moebius_inv_dvd_lower_bound _ _ (Squarefree.squarefree_of_dvd hm hP),
    sum_over_dvd_ite hP.ne_zero hm]
  simp_rw[ite_and, ←sum_filter, filter_comm]

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  norm_cast
  apply moebius_inv_dvd_lower_bound' hP l m hm
end Aux
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module sieve
-/
section
noncomputable section

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

open Finset Real Nat Aux BoundingSieve

namespace SelbergSieve

variable (s : BoundingSieve)

abbrev selbergTerms := BoundingSieve.selbergTerms (s := s)

section SieveLemmas

theorem selbergTerms_pos (l : ℕ) (hl : l ∣ s.prodPrimes) : 0 < (SelbergSieve.selbergTerms s) l := by
  exact BoundingSieve.selbergTerms_pos hl
theorem selbergTerms_mult : ArithmeticFunction.IsMultiplicative (SelbergSieve.selbergTerms s) := by
  exact BoundingSieve.selbergTerms_isMultiplicative
theorem conv_selbergTerms_eq_selbergTerms_mul_nu {d : ℕ} (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes, if l ∣ d then (SelbergSieve.selbergTerms s) l else 0) = (SelbergSieve.selbergTerms s) d * (s.nu d)⁻¹ := by
  exact BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hd

end SieveLemmas

section LambdaSquared

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ (d : ℕ), ¬d ^ 2 ≤ y → w d = 0)
    {d : ℕ} (hd : ¬↑d ≤ y) (d1 : ℕ) (d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2, mul_zero]
  by_contra hyp; apply hd
  apply le_trans _ hyp
  norm_cast
  calc _ ≤ (d1.lcm d2) := by rw [h]
      _ ≤ (d1*d2) := Nat.div_le_self _ _
      _ ≤ _       := ?_
  · rw [sq]; gcongr

theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬d ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬d ≤ y) :
    lambdaSquared w d = 0 := by
  dsimp only [lambdaSquared]
  by_cases hy : 0 ≤ y
  swap
  · push Not at hd hy
    have : ∀ d' : ℕ, w d' = 0 := by
      intro d'; apply hw
      have : (0:ℝ) ≤ (d') ^ 2 := by norm_num
      linarith
    apply sum_eq_zero; intro d1 _
    apply sum_eq_zero; intro d2 _
    rw [this d1, this d2]
    simp only [mul_zero, ite_self]
  apply sum_eq_zero; intro d1 _
  apply sum_eq_zero; intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · apply lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    apply lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
      (Nat.lcm_comm d1 d2 ▸ h) hle

theorem lambdaSquared_mainSum_eq_diag_quad_form (w : ℕ → ℝ) :
    mainSum (s := s) (lambdaSquared w) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms s) l * (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * w d else 0) ^ 2 :=
  by simpa only [selbergTerms, one_div] using BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq (s := s) w
end LambdaSquared

end SelbergSieve
end
end

/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Arend Mellendijk

! This file was ported from Lean 3 source module selberg
-/
section
noncomputable section

open scoped BigOperators Classical SelbergSieve ArithmeticFunction.Moebius ArithmeticFunction.omega

open Finset Real Nat ArithmeticFunction SelbergSieve BoundingSieve

namespace SelbergSieve

variable (s : SelbergSieve)

@[simp]
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0

theorem selbergBoundingSum_pos :
    0 < (SelbergSieve.selbergBoundingSum s) := by
  dsimp only [selbergBoundingSum]
  rw [← sum_filter]
  apply sum_pos;
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    · apply selbergTerms_pos _ _ (hl.1.1)
  · simp_rw [Finset.Nonempty, mem_filter]; use 1
    constructor
    · apply one_mem_divisors.mpr prodPrimes_ne_zero
    rw [cast_one, one_pow]
    exact s.one_le_level

theorem selbergBoundingSum_ne_zero : (SelbergSieve.selbergBoundingSum s) ≠ 0 := by
  apply _root_.ne_of_gt
  exact s.selbergBoundingSum_pos

theorem selbergBoundingSum_nonneg : 0 ≤ (SelbergSieve.selbergBoundingSum s) := _root_.le_of_lt s.selbergBoundingSum_pos

def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d * (SelbergSieve.selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬ d ∣ s.prodPrimes) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬d ^ 2 ≤ s.level) :
    (SelbergSieve.selbergWeights s) d = 0 := by
  dsimp only [selbergWeights]
  split_ifs with h
  · rw [mul_eq_zero_of_right _]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg ?_
    intro hyp
    have : (d^2:ℝ) ≤ (d*m)^2 := by
      norm_cast;
      refine Nat.pow_le_pow_left ?h 2
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_mem_divisors hm)
    linarith [hyp.1]
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ (SelbergSieve.selbergWeights s) d * μ d := by
  dsimp only [selbergWeights]
  rw [if_pos hdP, mul_assoc]
  trans ((μ d :ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (SelbergSieve.selbergBoundingSum s)⁻¹ * ∑ m ∈ divisors s.prodPrimes,
          if (d * m) ^ 2 ≤ s.level ∧ Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0)
  swap
  · apply le_of_eq; ring
  refine mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_) ?_
  · apply sq_nonneg
  · rw [inv_nonneg]
    exact le_of_lt <| nu_pos_of_dvd_prodPrimes hdP
  · exact le_of_lt <| selbergTerms_pos _ d hdP
  · exact s.selbergBoundingSum_nonneg
  apply sum_nonneg; intro m hm
  split_ifs with h
  · exact le_of_lt <| selbergTerms_pos _ m (dvd_of_mem_divisors hm)
  · rfl

theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬ k ∣ l → f l = 0) :
      ∑ l ∈ n.divisors, f l
    = ∑ m ∈ n.divisors, if k*m ∣ n then f (k*m) else 0 := by
  by_cases hn: n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [sum_eq_zero, sum_eq_zero]
    · rintro m _
      rw [if_neg]
      rintro h
      apply hkn
      exact (Nat.dvd_mul_right k m).trans h
    · intro l hl; apply h l (dvd_of_mem_divisors hl)
      apply fun hkl => hkn <| hkl.trans (dvd_of_mem_divisors hl)
  trans (∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l=k*m then f l else 0)
  · rw [sum_congr rfl]; intro l hl
    by_cases hkl : k ∣ l
    swap
    · rw [h l (dvd_of_mem_divisors hl) hkl, sum_eq_zero];
      intro m _; rw [ite_id]
    rw [sum_eq_single (l/k)]
    · rw[if_pos]; rw [Nat.mul_div_cancel' hkl]
    · intro m _ hmlk
      apply if_neg; revert hmlk; contrapose!; intro hlkm
      rw [hlkm, mul_comm, Nat.mul_div_cancel];
      apply Nat.pos_of_dvd_of_pos hkn (Nat.pos_of_ne_zero hn)
    · contrapose!; intro _
      rw [mem_divisors]
      exact ⟨Trans.trans (Nat.div_dvd_of_dvd hkl) (dvd_of_mem_divisors hl), hn⟩
  · rw [sum_comm, sum_congr rfl]; intro m _
    split_ifs with hdvd
    · rw [sum_ite_eq_of_mem']
      simp only [mem_divisors, hdvd, ne_eq, hn, not_false_eq_true, and_self]
    · apply sum_eq_zero; intro l hl
      apply if_neg;
      rintro rfl
      simp only [mem_divisors, ne_eq] at hl
      exact hdvd hl.1

theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * (SelbergSieve.selbergWeights s) d =
      (SelbergSieve.selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes, if d ∣ l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · dsimp only [selbergWeights]; rw [if_neg h_dvd]
    rw [sum_eq_zero]
    · ring
    intro l hl; rw [mem_divisors] at hl
    rw [if_neg]; push Not; intro h
    exfalso; exact h_dvd (dvd_trans h hl.left)
  dsimp only [selbergWeights]
  rw [if_pos h_dvd]
  repeat rw [mul_sum]
  
  apply symm
  rw [sum_mul_subst d s.prodPrimes]
  · apply sum_congr rfl
    intro m hm
    rw [mul_ite_zero, ←ite_and, mul_ite_zero, mul_ite_zero]
    apply if_ctx_congr _ _ fun _ => rfl
    · rw [coprime_comm]
      constructor
      · intro h
        push_cast at h
        exact ⟨h.2.2, coprime_of_squarefree_mul
          <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree⟩
      · intro h
        push_cast
        exact ⟨ Coprime.mul_dvd_of_dvd_of_dvd h.2 h_dvd (dvd_of_mem_divisors hm),
          Nat.dvd_mul_right d m, h.1⟩
    · intro h
      trans ((s.nu d)⁻¹ * (s.nu d) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * μ d / (SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) m)
      · rw [inv_mul_cancel₀ (nu_ne_zero h_dvd),
          (selbergTerms_mult _).map_mul_of_coprime <| coprime_comm.mp h.2]
        ring
      ring
  · intro l _ hdl
    rw [if_neg, mul_zero]
    push Not; intro h; contradiction

theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
      if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) =
        ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ k ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ) else 0 := by
      apply sum_congr rfl; intro d _
      rw [selbergWeights_eq_dvds_sum, ← boole_mul, mul_sum, mul_sum]
      apply sum_congr rfl; intro k _
      rw [mul_ite_zero, ite_zero_mul_ite_zero]
      apply if_ctx_congr Iff.rfl _ (fun _ => rfl);
      intro _; ring
    _ = ∑ k ∈ divisors s.prodPrimes, if k ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d:ℝ) else 0) * (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * (SelbergSieve.selbergBoundingSum s)⁻¹
          else 0 := by
      rw [sum_comm]; apply sum_congr rfl; intro k _
      apply symm
      rw [← boole_mul, sum_mul, sum_mul, mul_sum, sum_congr rfl]
      intro d _
      rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ←ite_and]
      apply if_ctx_congr _ _ (fun _ => rfl)
      · tauto
      intro _; ring
    _ = if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0 := by
      rw [← sum_ite_eq_of_mem' (divisors s.prodPrimes) l (fun _ => if l^2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * μ l * (SelbergSieve.selbergBoundingSum s)⁻¹ else 0) hl]
      apply sum_congr rfl; intro k hk
      rw [Aux.moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l _ (dvd_of_mem_divisors hk),
        ←ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]; apply and_congr_right
        intro heq; rw [heq]
      · intro h; rw [h.1]; ring

def selbergMuPlus : ℕ → ℝ :=
  lambdaSquared (SelbergSieve.selbergWeights s)

theorem weight_one_of_selberg : (SelbergSieve.selbergWeights s) 1 = 1 := by
  dsimp only [selbergWeights]
  rw [if_pos (one_dvd s.prodPrimes), s.nu_mult.left, (selbergTerms_mult _).map_one]
  simp only [inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, _root_.pow_zero, Int.cast_one, selbergBoundingSum, one_mul,
    coprime_one_right_eq_true, and_true, cast_one]
  rw [inv_mul_cancel₀]
  convert! s.selbergBoundingSum_ne_zero

theorem selbergμPlus_eq_zero (d : ℕ) (hd : ¬d ≤ s.level) : (SelbergSieve.selbergMuPlus s) d = 0 := by
  apply lambdaSquared_eq_zero_of_support _ s.level _ d hd
  apply s.selbergWeights_eq_zero
theorem mainSum_eq_diag_quad_form :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) =
      ∑ l ∈ divisors s.prodPrimes,
        1 / (SelbergSieve.selbergTerms (s.toBoundingSieve)) l *
          (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * (SelbergSieve.selbergWeights s) d else 0) ^ 2 :=
  by apply lambdaSquared_mainSum_eq_diag_quad_form

theorem selberg_bound_simple_mainSum :
    mainSum (s := s.toBoundingSieve) (SelbergSieve.selbergMuPlus s) = (SelbergSieve.selbergBoundingSum s)⁻¹ := by
  rw [mainSum_eq_diag_quad_form]
  trans (∑ l ∈ divisors s.prodPrimes, (if l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2 else 0))
  · apply sum_congr rfl; intro l hl
    rw [s.selbergWeights_diagonalisation l hl, ite_pow, zero_pow two_ne_zero, mul_ite_zero]
    apply if_congr Iff.rfl _ rfl
    trans (1/(SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (SelbergSieve.selbergTerms (s.toBoundingSieve)) l * (μ l:ℝ)^2  * ((SelbergSieve.selbergBoundingSum s)⁻¹) ^ 2)
    · ring
    norm_cast; rw [moebius_sq_eq_one_of_squarefree <| squarefree_of_mem_divisors_prodPrimes hl]
    rw [one_div_mul_cancel <| _root_.ne_of_gt <| selbergTerms_pos _ l <| dvd_of_mem_divisors hl]
    ring
  conv => {lhs; congr; {skip}; {ext i; rw [← ite_zero_mul]}}
  dsimp only [selbergBoundingSum]
  rw [←sum_mul, sq, ←mul_assoc, mul_inv_cancel₀]
  · ring
  · apply _root_.ne_of_gt; apply selbergBoundingSum_pos

theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k*m) := by
  obtain ⟨r, hr⟩ := hkd
  have hrdvd : r ∣ d := by use k; rw [mul_comm]; exact hr
  apply symm; rw [hr, Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  apply Coprime.coprime_dvd_right hrdvd hmd

private theorem _helper {k m d : ℕ} (hkd : k ∣ d) (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧ (k * m) ^ 2 ≤ s.level ↔
    (k * m) ^ 2 ≤ s.level ∧ Coprime m d := by
  constructor
  · intro h
    constructor
    · exact h.2.2
    · obtain ⟨r, hr⟩ := hkd
      rw [hr, Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk ⊢)] at h
      rw [hr, coprime_comm]; apply Coprime.mul_left
      · apply coprime_of_squarefree_mul <| Squarefree.squarefree_of_dvd h.1 s.prodPrimes_squarefree
      · exact h.2.1
  · intro h
    constructor
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · rw [coprime_comm]; exact Coprime.coprime_dvd_right hkd h.2
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    constructor
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk ⊢)
    · exact h.1

theorem selbergBoundingSum_ge {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    (SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
  calc
  _ = (∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes, if k = d.gcd l ∧ l ^ 2 ≤ s.level then (SelbergSieve.selbergTerms (s.toBoundingSieve)) l else 0) := by
    dsimp only [selbergBoundingSum]
    rw [sum_comm, sum_congr rfl]; intro l _
    simp_rw [ite_and]
    rw [sum_ite_eq_of_mem']
    · rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans (hdP), prodPrimes_ne_zero⟩
  _ = (∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (k * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0) := by
    apply sum_congr rfl; intro k hk
    rw [mul_sum]
    split_ifs with hkd
    swap
    · rw [sum_eq_zero]; intro l _
      rw [if_neg]
      push Not; intro h; exfalso
      rw [h] at hkd
      exact hkd <| Nat.gcd_dvd_left d l
    rw [sum_mul_subst k s.prodPrimes, sum_congr rfl]
    · intro m hm
      rw [mul_ite_zero, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · exact_mod_cast s._helper hkd hk hm
      · intro h
        apply (selbergTerms_mult _).map_mul_of_coprime
        rw [gcd_comm]; apply h.2.coprime_dvd_right hkd
    · intro l _ hkl; apply if_neg
      push Not; intro h; exfalso
      rw [h] at hkl; exact hkl (Nat.gcd_dvd_right d l)
  _ ≥ (∑ k ∈ divisors s.prodPrimes, if k ∣ d
          then (SelbergSieve.selbergTerms (s.toBoundingSieve)) k * ∑ m ∈ divisors s.prodPrimes, if (d * m) ^ 2 ≤ s.level ∧ m.Coprime d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0
          else 0 ) := by
    apply sum_le_sum; intro k _
    split_ifs with hkd
    swap
    · rfl
    apply mul_le_mul le_rfl _ _ (le_of_lt <| selbergTerms_pos _ k <| hkd.trans hdP)
    · apply sum_le_sum; intro m hm
      split_ifs with h h' h'
      · rfl
      · exfalso; apply h'
        refine ⟨?_, h.2⟩
        · trans ((d*m)^2:ℝ)
          · norm_cast; gcongr
            refine Nat.le_of_dvd ?_ hkd
            apply Nat.pos_of_ne_zero; apply ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
          exact h.1
      · refine le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
      · rfl
    apply sum_nonneg; intro m hm
    split_ifs
    · apply le_of_lt <| selbergTerms_pos _ m <| dvd_of_mem_divisors hm
    · rfl
  _ = _ := by
    conv => enter [1, 2, k]; rw [← ite_zero_mul]
    rw [←sum_mul, conv_selbergTerms_eq_selbergTerms_mul_nu _ hdP]
    trans ((SelbergSieve.selbergBoundingSum s) * (SelbergSieve.selbergBoundingSum s)⁻¹ * (μ d:ℝ)^2 * (s.nu d)⁻¹ * (SelbergSieve.selbergTerms (s.toBoundingSieve)) d * (∑ m ∈ divisors s.prodPrimes, if (d*m) ^ 2 ≤ s.level ∧
      Coprime m d then (SelbergSieve.selbergTerms (s.toBoundingSieve)) m else 0))
    · rw [mul_inv_cancel₀, ←Int.cast_pow, moebius_sq_eq_one_of_squarefree]
      · ring
      · exact Squarefree.squarefree_of_dvd hdP s.prodPrimes_squarefree
      · exact _root_.ne_of_gt <| s.selbergBoundingSum_pos
    dsimp only [selbergWeights]; rw [if_pos hdP]
    ring

theorem selberg_bound_weights (d : ℕ) : |(SelbergSieve.selbergWeights s) d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [s.selbergWeights_eq_zero_of_not_dvd hdP]; simp only [zero_le_one, abs_zero]
  have : 1*(SelbergSieve.selbergBoundingSum s) ≥ (SelbergSieve.selbergWeights s) d * ↑(μ d) * (SelbergSieve.selbergBoundingSum s) := by
    rw[one_mul]
    exact s.selbergBoundingSum_ge hdP
  replace this : (SelbergSieve.selbergWeights s) d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right this (s.selbergBoundingSum_pos)
  convert this using 1
  rw [← abs_of_nonneg <| s.selbergWeights_mul_mu_nonneg d hdP,
    abs_mul, ←Int.cast_abs, abs_moebius_eq_one_of_squarefree <|
    (s.prodPrimes_squarefree.squarefree_of_dvd hdP), Int.cast_one, mul_one]

theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |(SelbergSieve.selbergMuPlus s) n| ≤ (3:ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z : ℕ => if n = x.lcm z then 1 else 0
  dsimp only [selbergMuPlus, lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| ≤
        ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, |if n = d1.lcm d2 then (SelbergSieve.selbergWeights s) d1 * (SelbergSieve.selbergWeights s) d2 else 0| := ?_
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := ?_
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.fst p.snd := ?_
    _ = Finset.card ((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.fst.lcm p.snd) := ?_
    _ = (3:ℕ) ^ ω n := ?_
    _ = (3:ℝ) ^ ω n := ?_
  · apply abs_sum_le_sum_abs
  · gcongr; apply abs_sum_le_sum_abs
  · gcongr with d1 _ d2
    rw [apply_ite abs, abs_zero, abs_mul]
    simp only [f]
    by_cases h : n = d1.lcm d2
    · rw [if_pos h, if_pos h]
      apply mul_le_one₀ (s.selberg_bound_weights d1) (abs_nonneg <| (SelbergSieve.selbergWeights s) d2)
        (s.selberg_bound_weights d2)
    rw [if_neg h, if_neg h]
  · rw [← Finset.sum_product']
  · rw [← sum_filter, Finset.sum_const, smul_one_eq_cast]
  · norm_cast
    simp [← card_pair_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn), eq_comm]
  norm_num
end SelbergSieve
end
end

namespace OMABeth

open Finset BethSelberg
open scoped ArithmeticFunction.omega

private theorem primeProduct_squarefree (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) :
    Squarefree (∏ p ∈ P, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime _ fun p h ↦ (hp p h).squarefree
  exact fun p hpP q hqP hpq ↦ Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp p hpP) (hp q hqP)).mpr hpq)

private theorem primeProduct_mem {P : Finset ℕ} (hP : ∀ p ∈ P, Nat.Prime p) {p : ℕ}
    (hp : Nat.Prime p) (hd : p ∣ ∏ q ∈ P, q) : p ∈ P := by
  rw [← Nat.primeFactors_prod hP]
  exact Nat.mem_primeFactors.mpr ⟨hp, hd, (primeProduct_squarefree P hP).ne_zero⟩

private theorem primeWeight_apply (w : ℕ → ℝ) {p : ℕ} (hp : Nat.Prime p) :
    ArithmeticFunction.prodPrimeFactors w p = w p := by
  simp [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors]

/-- 平方因子のない法の局所密度だけをSelbergの平方和に渡す。 -/
noncomputable def finiteSelbergSieve (w : ℕ → ℝ) (P : Finset ℕ) (D : ℝ)
    (hp : ∀ p ∈ P, Nat.Prime p) (hw : ∀ p ∈ P, w p ∈ Set.Ioo 0 1) (hD : 1 ≤ D) : SelbergSieve where
  support := ∅
  weights := fun _ ↦ 0
  weights_nonneg := fun _ ↦ le_rfl
  totalMass := 0
  prodPrimes := ∏ p ∈ P, p
  prodPrimes_squarefree := primeProduct_squarefree P hp
  nu := ArithmeticFunction.prodPrimeFactors w
  nu_mult := ArithmeticFunction.IsMultiplicative.prodPrimeFactors w
  nu_pos_of_prime p h hdiv := by rw [primeWeight_apply w h]; exact (hw p (primeProduct_mem hp h hdiv)).1
  nu_lt_one_of_prime p h hdiv := by rw [primeWeight_apply w h]; exact (hw p (primeProduct_mem hp h hdiv)).2
  level := D
  one_le_level := hD

private theorem sum_divisor_primeProduct (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p)
    (f : ℕ → ℝ) :
    (∑ n ∈ (∏ p ∈ P, p : ℕ).divisors, f n) = ∑ T ∈ P.powerset, f (∏ q ∈ T, q) := by
  have hsf := primeProduct_squarefree P hp
  rw [← Nat.divisors_filter_squarefree_of_squarefree hsf, Nat.sum_divisors_filter_squarefree hsf.ne_zero,
    Nat.factors_eq]
  change (∑ t ∈ (∏ p ∈ P, p : ℕ).primeFactors.powerset, f t.val.prod) = _
  rw [Nat.primeFactors_prod hp]
  exact sum_congr rfl fun t _ ↦ by rw [t.prod_val, Function.id_def]

private theorem primeProduct_dvd {T P : Finset ℕ} (h : T ⊆ P) :
    (∏ p ∈ T, p) ∣ ∏ p ∈ P, p := by
  rw [← prod_sdiff h]
  exact dvd_mul_left _ _

private theorem cardDistinct_primeProduct (P : Finset ℕ) (hp : ∀ p ∈ P, Nat.Prime p) :
    ω (∏ p ∈ P, p) = P.card := by
  calc
    _ = (∏ p ∈ P, p : ℕ).primeFactors.card := by
      rw [ArithmeticFunction.cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
    _ = _ := congrArg Finset.card (Nat.primeFactors_prod hp)

/-- Selbergのエルシーエム係数を素数の部分集合に添字付けした上側の篩 -/
noncomputable def selbergCert (w : ℕ → ℝ) (P : Finset ℕ) (D : ℝ)
    (hp : ∀ p ∈ P, Nat.Prime p) (hw : ∀ p ∈ P, w p ∈ Set.Ioo 0 1) (hD : 1 ≤ D) : Cert true P D := by
  let s := finiteSelbergSieve w P D hp hw hD
  refine ⟨fun d ↦ s.selbergMuPlus (∏ p ∈ d, p), ?_, ?_, ?_⟩
  · intro d hd
    have hdP : (∏ p ∈ d, p) ∈ s.prodPrimes.divisors :=
      Nat.mem_divisors.mpr ⟨primeProduct_dvd hd, s.prodPrimes_ne_zero⟩
    rw [← cardDistinct_primeProduct d (fun p h ↦ hp p (hd h))]
    exact s.selberg_bound_muPlus _ hdP
  · intro d _ h
    apply s.selbergμPlus_eq_zero
    change ¬ ((∏ p ∈ d, p : ℕ) : ℝ) ≤ D
    simpa only [Nat.cast_prod] using (not_le.mpr h)
  · intro X hX
    have hpX (p : ℕ) (h : p ∈ X) := hp p (hX h)
    have hiff : (∏ p ∈ X, p) = 1 ↔ X = ∅ := by
      refine ⟨fun he ↦ ?_, fun he ↦ by simp [he]⟩
      rw [← Nat.primeFactors_prod hpX, he, Nat.primeFactors_one]
    have h := BoundingSieve.upperMoebius_lambdaSquared s.selbergWeights s.weight_one_of_selberg (∏ p ∈ X, p)
    change (if (∏ p ∈ X, p) = 1 then (1 : ℝ) else 0) ≤ ∑ d ∈ (∏ p ∈ X, p : ℕ).divisors, s.selbergMuPlus d at h
    change (if X = ∅ then (1 : ℝ) else 0) ≤ ∑ d ∈ X.powerset, s.selbergMuPlus (∏ p ∈ d, p)
    simpa only [hiff, sum_divisor_primeProduct X hpX] using h

private theorem cdf_congr_on (w v : ℕ → ℝ) (P : Finset ℕ) (Y : ℝ) (h : ∀ p ∈ P, w p = v p) :
    cdf w P Y = cdf v P Y := by
  apply sum_congr rfl
  intro t ht
  split_ifs
  · exact congrArg₂ (· * ·) (prod_congr rfl fun p hp ↦ h p (mem_powerset.mp ht hp))
      (prod_congr rfl fun p hp ↦ congrArg (1 - ·) (h p (mem_sdiff.mp hp).1))
  · rfl

theorem main_selbergCert (w : ℕ → ℝ) (P : Finset ℕ) (D : ℝ)
    (hp : ∀ p ∈ P, Nat.Prime p) (hw : ∀ p ∈ P, w p ∈ Set.Ioo 0 1) (hD : 1 ≤ D) :
    (selbergCert w P D hp hw hD).main w = volumeOn w P / cdf w P (Real.sqrt D) := by
  let s := finiteSelbergSieve w P D hp hw hD
  have hnu {p : ℕ} (hp' : p ∈ P) : s.nu p = w p := primeWeight_apply w (hp p hp')
  have pf : s.prodPrimes.primeFactors = P := Nat.primeFactors_prod hp
  calc
    _ = s.toBoundingSieve.mainSum s.selbergMuPlus := by
      change (∑ d ∈ P.powerset, s.selbergMuPlus (∏ p ∈ d, p) * ∏ p ∈ d, w p) =
        ∑ d ∈ (∏ p ∈ P, p : ℕ).divisors, s.selbergMuPlus d * s.nu d
      rw [sum_divisor_primeProduct P hp]
      refine sum_congr rfl fun d hd ↦ ?_
      have hpd (p : ℕ) (h : p ∈ d) := hp p (mem_powerset.mp hd h)
      have hn : (∏ p ∈ d, p : ℕ) ≠ 0 := (primeProduct_squarefree d hpd).ne_zero
      change _ = _ * ArithmeticFunction.prodPrimeFactors w (∏ p ∈ d, p)
      rw [ArithmeticFunction.prodPrimeFactors_apply hn, Nat.primeFactors_prod hpd]
    _ = s.selbergBoundingSum⁻¹ := s.selberg_bound_simple_mainSum
    _ = volume s.toBoundingSieve / cdf (fun p ↦ s.nu p) s.prodPrimes.primeFactors (Real.sqrt D) :=
      selberg_reciprocal_as_cdf s.toBoundingSieve (zero_le_one.trans hD)
    _ = _ := by
      rw [volume, pf, cdf_congr_on _ w P _ (fun _ h ↦ hnu h)]
      exact congrArg (· / cdf w P (Real.sqrt D)) (prod_congr rfl fun p h ↦ congrArg (1 - ·) (hnu h))

end OMABeth

end

section

open Finset

namespace BethCdfGrid

open BethSelberg

def increment (F : ℕ → ℝ) : ℕ → ℝ
  | 0 => F 0
  | t+1 => F (t+1) - F t

theorem sum_increment (F : ℕ → ℝ) (n : ℕ) :
    ∑ t ∈ range (n+1), increment F t = F n := by
  induction n with
  | zero => simp [increment]
  | succ n ih => rw [sum_range_succ, ih, increment]; ring

theorem sum_increment_mul (F B : ℕ → ℝ) (n : ℕ) :
    (∑ t ∈ range (n+1), increment F t * B t) =
      F n * B n + ∑ t ∈ range n, F t * (B t - B (t+1)) := by
  induction n with
  | zero => simp [increment]
  | succ n ih => rw [sum_range_succ, ih, sum_range_succ, increment]; ring

noncomputable def cut (N : ℕ) (z : ℝ) (j t : ℕ) : ℕ :=
  ⌊z ^ ((j : ℝ) / ((t : ℝ) + 2 * N))⌋₊

noncomputable def cutBound (N : ℕ) (K : ℝ) (j t : ℕ) : ℝ :=
  min 1 (((j : ℝ) / ((t : ℝ) + 2 * N)) ^ 2) / K

noncomputable def kernel (N t : ℕ) : ℝ :=
  let k : ℝ := t + 2*N
  (2*k + 1) / (k^2 * (k+1)^2)

private theorem cutBound_eq (N : ℕ) (hN : 0 < N) (K : ℝ) (j t : ℕ) (hj : j ≤ t + 2*N) :
    cutBound N K j t = ((j : ℝ)^2 / K) / ((t : ℝ) + 2*N)^2 := by
  have hkN : 0 < (N : ℝ) := by exact_mod_cast hN
  have hk : 0 < (t : ℝ) + 2*N := by positivity
  have hu : (j : ℝ)/((t : ℝ) + 2*N) ≤ 1 := (div_le_one hk).mpr (by exact_mod_cast hj)
  rw [cutBound, min_eq_right (pow_le_one₀ (by positivity) hu), div_pow]
  ring

private theorem cutBound_eq_one_div (N : ℕ) (hN : 0 < N) (K : ℝ) (j t : ℕ) (hj : t + 2*N ≤ j) :
    cutBound N K j t = 1 / K := by
  have hkN : 0 < (N : ℝ) := by exact_mod_cast hN
  have hk : 0 < (t : ℝ) + 2*N := by positivity
  have hu : 1 ≤ (j : ℝ)/((t : ℝ) + 2*N) := (one_le_div₀ hk).mpr (by exact_mod_cast hj)
  rw [cutBound, min_eq_left (one_le_pow₀ hu)]

theorem cutBound_diff (N : ℕ) (hN : 0 < N) (K : ℝ) (j t : ℕ) :
    cutBound N K j t - cutBound N K j (t+1) =
      if j ≤ t+2*N then ((j : ℝ)^2 / K) * kernel N t else 0 := by
  split_ifs with h
  · rw [cutBound_eq N hN K j t h, cutBound_eq N hN K j (t+1) (by omega)]
    let k : ℝ := t+2*N
    have hkN : 0 < (N : ℝ) := by exact_mod_cast hN
    have hk : 0 < k := by dsimp [k]; positivity
    have hs : ((t+1 : ℕ) : ℝ) + 2*N = k+1 := by push_cast; dsimp [k]; ring
    rw [hs]
    change _ / k^2 - _ / (k+1)^2 = _ * ((2*k+1)/(k^2*(k+1)^2))
    field_simp [hk.ne', (by positivity : 0 < k+1).ne']
    ring
  · rw [cutBound_eq_one_div N hN K j t (by omega), cutBound_eq_one_div N hN K j (t+1) (by omega)]
    ring

/-- 有限表のソフトウェアで使う各区間の有理数係数に、しきい値の差分和を変換する。 -/
theorem abel_update (F : ℕ → ℝ) (N cap : ℕ) (hN : 0 < N) (K : ℝ) (j : ℕ) (hj : j ≤ cap + 2*N) :
    (∑ t ∈ range (cap+1), increment F t * cutBound N K j t) =
      ((j : ℝ)^2 / K) * (F cap / ((cap : ℝ) + 2*N)^2 +
        ∑ t ∈ range cap, if j ≤ t+2*N then F t * kernel N t else 0) := by
  rw [sum_increment_mul, cutBound_eq N hN K j cap hj, mul_add, mul_sum]
  congr 1
  · ring
  · refine sum_congr rfl fun t ht ↦ ?_
    rw [cutBound_diff N hN K j t]
    split_ifs <;> ring

/-- 対数比がMertensの評価区間を外れる両端も含めて、最大素数の分布を下から抑える。 -/
theorem cutBound_le_volume (w : ℕ → ℝ) (P : Finset ℕ) {K lo z a : ℝ}
    (hK : 1 ≤ K) (hlo : 1 < lo) (hz : lo ≤ z) (ha : 0 ≤ a)
    (hP : ∀ p ∈ P, lo < (p : ℝ) ∧ (p : ℝ) ≤ z)
    (hM : ∀ x : ℝ, lo ≤ x → x ≤ z →
      (Real.log x / Real.log z)^2 / K ≤ volumeOn w (P.filter (⌊x⌋₊ < ·))) :
    min 1 (a^2) / K ≤ volumeOn w (P.filter (⌊z^a⌋₊ < ·)) := by
  have hz1 := hlo.trans_le hz
  have hz0 := zero_lt_one.trans hz1
  have hlo0 := zero_lt_one.trans hlo
  have hK0 := zero_lt_one.trans_le hK
  have hza := Real.rpow_pos_of_pos hz0 a
  have hlog := Real.log_pos hz1
  by_cases ha1 : 1 ≤ a
  · have hge : z ≤ z^a := by
      calc z = z^(1:ℝ) := (Real.rpow_one z).symm
           _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hz1.le ha1
    have he : P.filter (⌊z ^ a⌋₊ < ·) = ∅ :=
      filter_false_of_mem fun p hp ↦ Nat.not_lt.mpr (Nat.le_floor ((hP p hp).2.trans hge))
    rw [he, volumeOn, prod_empty, div_le_one hK0]
    exact (min_le_left _ _).trans hK
  · have hsz : z^a ≤ z := by
      calc _ ≤ z^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hz1.le (le_of_not_ge ha1)
           _ = _ := Real.rpow_one z
    have hmin : min 1 (a^2) / K ≤ a^2 / K :=
      div_le_div_of_nonneg_right (min_le_right _ _) hK0.le
    by_cases hah : lo ≤ z^a
    · have h := hM (z^a) hah hsz
      rw [Real.log_rpow hz0, mul_div_cancel_right₀ _ hlog.ne'] at h
      exact hmin.trans h
    · have hlt := lt_of_not_ge hah
      have hPlo : ∀ p ∈ P, ⌊lo⌋₊ < p := fun p hp ↦ (Nat.floor_lt hlo0.le).mpr (hP p hp).1
      have hPza : ∀ p ∈ P, ⌊z^a⌋₊ < p :=
        fun p hp ↦ (Nat.floor_lt hza.le).mpr (hlt.trans (hP p hp).1)
      have h := hM lo le_rfl hz
      rw [filter_true_of_mem hPlo] at h
      rw [filter_true_of_mem hPza]
      have halog : a ≤ Real.log lo / Real.log z := by
        rw [le_div_iff₀ hlog, ← Real.log_rpow hz0]
        exact Real.log_le_log hza hlt.le
      exact hmin.trans ((div_le_div_of_nonneg_right (pow_le_pow_left₀ ha halog 2) hK0.le).trans h)

theorem child_threshold (N : ℕ) (hN : 0 < N) {z : ℝ} (hz : 0 < z)
    (j t p : ℕ) (hp : 0 < p) (hcut : p ≤ cut N z j t) :
    (p : ℝ) ^ ((t : ℝ)/(2*N)) ≤ z ^ ((j : ℝ)/(2*N)) / p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hk : 0 < (t : ℝ) + 2*N := by positivity
  have hnum : (p : ℝ) ≤ z ^ ((j : ℝ) / ((t : ℝ) + 2 * N)) :=
    (show (p : ℝ) ≤ cut N z j t by exact_mod_cast hcut).trans
      (Nat.floor_le (Real.rpow_pos_of_pos hz _).le)
  have hlog := Real.log_le_log hp0 hnum
  rw [Real.log_rpow hz] at hlog
  have hh : Real.log p * ((t : ℝ) + 2*N) ≤ j * Real.log z := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk] at hlog
    exact hlog
  rw [le_div_iff₀ hp0, ← Real.rpow_add_one hp0.ne', Real.rpow_def_of_pos hp0,
    Real.rpow_def_of_pos hz, Real.exp_le_exp]
  field_simp
  nlinarith

private theorem inc_nonneg (F : ℕ → ℝ) {cap t : ℕ} (ht : t ≤ cap)
    (hmono : ∀ {a b : ℕ}, a ≤ b → b ≤ cap → F a ≤ F b) (hF0 : 0 ≤ F 0) :
    0 ≤ increment F t := by
  cases t with
  | zero => exact hF0
  | succ t => exact sub_nonneg.mpr (hmono (Nat.le_succ t) ht)

private theorem selected_sum_le (F : ℕ → ℝ) (cap : ℕ) (C : ℕ → Prop) [DecidablePred C]
    (hmono : ∀ {a b : ℕ}, a ≤ b → b ≤ cap → F a ≤ F b) (hF0 : 0 ≤ F 0)
    {b : ℝ} (hb : 0 ≤ b) (hsel : ∀ t ≤ cap, C t → F t ≤ b) :
    (∑ t ∈ range (cap+1), if C t then increment F t else 0) ≤ b := by
  classical
  let A := (range (cap+1)).filter C
  rw [← sum_filter]
  change (∑ t ∈ A, increment F t) ≤ b
  by_cases h : A.Nonempty
  · let m := A.max' h
    have hm : m ∈ A := max'_mem A h
    have hmC := (mem_filter.mp hm).2
    have hmcap : m ≤ cap := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hm).1)
    have hsub : A ⊆ range (m+1) := fun t ht ↦ mem_range.mpr (Nat.lt_succ_of_le (le_max' _ _ ht))
    calc
      _ ≤ ∑ t ∈ range (m+1), increment F t :=
        sum_le_sum_of_subset_of_nonneg hsub fun t ht _ ↦
          inc_nonneg F ((Nat.lt_succ_iff.mp (mem_range.mp ht)).trans hmcap) hmono hF0
      _ = F m := sum_increment F m
      _ ≤ b := hsel m hmcap hmC
  · rw [not_nonempty_iff_eq_empty.mp h, sum_empty]
    exact hb

/-- 最大の選択素数を取り除くたびに素数集合の要素数が減ることを用い、
各しきい値での積の下界と、指数モーメントから有限表の全項を同時に下から評価する。 -/
theorem cdf_ge_table (w : ℕ → ℝ) (P₀ : Finset ℕ) (N cap : ℕ) (hN : 0 < N)
    (F : ℕ → ℝ) (K lo : ℝ) (hlo : 1 < lo)
    (hpr : ∀ p ∈ P₀, lo < (p : ℝ)) (hw : ∀ p ∈ P₀, w p ∈ Set.Icc 0 1)
    (hmono : ∀ {a b : ℕ}, a ≤ b → b ≤ cap → F a ≤ F b) (hF0 : 0 ≤ F 0) (hFcap : F cap ≤ 1)
    (hstep : ∀ j ≤ cap, F j ≤ max (max 0 (1 - 400000 * Real.exp (-((j : ℝ)/N))))
      (∑ t ∈ range (cap+1), increment F t * cutBound N K j t))
    (hmean : ∀ Q ⊆ P₀, ∀ z : ℝ, lo ≤ z → (∀ p ∈ Q, (p : ℝ) ≤ z) →
      (∑ p ∈ Q, w p * (Real.log p / Real.log z)) ≤ 2001/1000)
    (hcut : ∀ Q ⊆ P₀, ∀ z : ℝ, lo ≤ z → (∀ p ∈ Q, (p : ℝ) ≤ z) →
      ∀ j ≤ cap, ∀ t ≤ cap, cutBound N K j t ≤ volumeOn w (Q.filter (cut N z j t < ·)))
    (P : Finset ℕ) (hP : P ⊆ P₀) (z : ℝ) (hz : lo ≤ z) (hPz : ∀ p ∈ P, (p : ℝ) ≤ z)
    (j : ℕ) (hj : j ≤ cap) :
    F j ≤ cdf w P (z ^ ((j : ℝ)/(2*N))) := by
  classical
  induction P using Finset.strongInductionOn generalizing z j with
  | _ P ih =>
    have hwP (p : ℕ) (hp : p ∈ P) := hw p (hP hp)
    have hpos (p : ℕ) (hp : p ∈ P) : 0 < p := by
      exact_mod_cast (zero_lt_one.trans (hlo.trans (hpr p (hP hp))))
    have hz1 := hlo.trans_le hz
    have hY : 1 ≤ z ^ ((j : ℝ) / (2*N)) := Real.one_le_rpow hz1.le (by positivity)
    refine (hstep j hj).trans (max_le ?_ ?_)
    · refine max_le (cdf_nonneg w P _ hwP) ?_
      have hch := cdf_compl_le_chernoff w P hz1 (fun p hp ↦ ⟨hpos p hp, hPz p hp⟩)
        hwP (hmean P hP z hz hPz) ((j : ℝ)/N)
      have hexp : ((j : ℝ)/N)/2 = (j : ℝ)/(2*N) := by ring
      rw [hexp] at hch
      linarith
    · apply BethGrid.lower_cdf_layers w P (range (cap+1)) _ hY hpos hwP
        (cut N z j) (increment F) (cutBound N K j)
      · exact fun t ht ↦ inc_nonneg F (Nat.lt_succ_iff.mp (mem_range.mp ht)) hmono hF0
      · rw [sum_increment]
        exact hFcap
      · exact fun t ht ↦ hcut P hP z hz hPz j hj t (Nat.lt_succ_iff.mp (mem_range.mp ht))
      · intro p hp
        let Q := P.filter (· < p)
        have hs : Q ⊂ P := filter_ssubset.mpr ⟨p, hp, lt_irrefl _⟩
        have hQ : Q ⊆ P₀ := Subset.trans (filter_subset _ _) hP
        have hQp (q : ℕ) (hq : q ∈ Q) : (q : ℝ) ≤ p := by
          exact_mod_cast (mem_filter.mp hq).2.le
        have hwQ (q : ℕ) (hq : q ∈ Q) := hw q (hQ hq)
        apply selected_sum_le F cap (fun t ↦ p ≤ cut N z j t) hmono hF0 (cdf_nonneg w Q _ hwQ)
        intro t ht hpc
        have hc := ih Q hs hQ (p : ℝ) (hpr p (hP hp)).le hQp t ht
        exact hc.trans (cdf_mono w Q hwQ (child_threshold N hN (zero_lt_one.trans hz1) j t p (hpos p hp) hpc))

theorem weighted_log_mean (w : ℕ → ℝ) (P : Finset ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hlog : 18000 ≤ Real.log z) (hP : ∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ z)
    (hw : ∀ p ∈ P, w p ≤ 2/(p : ℝ)) :
    ∑ p ∈ P, w p * (Real.log p / Real.log z) ≤ 2001/1000 := by
  have hf : 1 ≤ ⌊z⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hz)
  have hpos : 0 < Real.log z := by linarith
  have hsub : P ⊆ Nat.primesLE ⌊z⌋₊ :=
    fun p hp ↦ Nat.mem_primesLE.mpr ⟨Nat.le_floor (hP p hp).2, (hP p hp).1⟩
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ ↦ Real.log p / (p : ℝ)) hsub
    (fun p hp _ ↦ div_nonneg (Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)) (Nat.cast_nonneg _))
  have hsd := (abs_le.mp (BethMertens.mertens_first ⌊z⌋₊ hf)).2
  have hfloorpos : 0 < (⌊z⌋₊ : ℝ) := by exact_mod_cast hf
  have hf_log := Real.log_le_log hfloorpos (Nat.floor_le (zero_le_one.trans hz))
  have hbase : (∑ p ∈ P, Real.log p / (p : ℝ)) ≤ Real.log z + 9 := by linarith
  calc
    _ ≤ ∑ p ∈ P, (2/(p : ℝ)) * (Real.log p / Real.log z) :=
      sum_le_sum fun p hp ↦ mul_le_mul_of_nonneg_right (hw p hp) (div_nonneg
        (Real.log_nonneg (by exact_mod_cast (hP p hp).1.one_le)) hpos.le)
    _ = 2 * (∑ p ∈ P, Real.log p / (p : ℝ)) / Real.log z := by
      rw [mul_sum, Finset.sum_div]
      exact sum_congr rfl fun p _ ↦ by ring
    _ ≤ _ := by rw [div_le_iff₀ hpos]; linarith

private theorem masked_product (w : ℕ → ℝ) (P : Finset ℕ)
    (hp : ∀ p ∈ P, p.Prime ∧ 3 ≤ p) (x : ℝ) :
    BethMertens.sieveProduct (fun p ↦ if p ∈ P then w p else 0) x =
      volumeOn w (P.filter (· ≤ ⌊x⌋₊)) := by
  classical
  let T := (Icc 3 ⌊x⌋₊).filter Nat.Prime
  have he : T.filter (· ∈ P) = P.filter (· ≤ ⌊x⌋₊) := by
    ext p
    simp only [T, mem_filter, mem_Icc]
    exact ⟨fun h ↦ ⟨h.2, h.1.1.2⟩, fun h ↦ ⟨⟨⟨(hp p h.1).2, h.2⟩, (hp p h.1).1⟩, h.1⟩⟩
  calc
    _ = ∏ p ∈ T, (if p ∈ P then 1 - w p else 1) := by
      refine prod_congr rfl fun p hp ↦ ?_
      by_cases h : p ∈ P <;> simp [h]
    _ = _ := by rw [← prod_filter, he]; rfl

theorem volume_lower_of_ratio (w : ℕ → ℝ) (P : Finset ℕ) {x z K : ℝ}
    (hK : 0 < K) (hx : 1 < x) (hxz : x ≤ z)
    (hp : ∀ p ∈ P, p.Prime ∧ 3 ≤ p ∧ (p : ℝ) ≤ z)
    (hw : ∀ p ∈ P, w p ≤ 2/(p : ℝ))
    (hratio : ∀ v : ℕ → ℝ, (∀ p : ℕ, p.Prime → 3 ≤ p → v p ≤ 2 / (p : ℝ)) →
      BethMertens.sieveProduct v x / BethMertens.sieveProduct v z ≤ K*(Real.log z / Real.log x)^2) :
    (Real.log x / Real.log z)^2 / K ≤ volumeOn w (P.filter (⌊x⌋₊ < ·)) := by
  classical
  let v (p : ℕ) := if p ∈ P then w p else 0
  have hP (p : ℕ) (h : p ∈ P) : p.Prime ∧ 3 ≤ p := ⟨(hp p h).1, (hp p h).2.1⟩
  have hfac (p : ℕ) (h : p ∈ P) : 0 < 1 - w p := by
    have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (hP p h).2
    have hdiv : 2/(p : ℝ) ≤ 2/3 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp3
    linarith [hw p h]
  have hv (p : ℕ) (_ : p.Prime) (_ : 3 ≤ p) : v p ≤ 2/(p : ℝ) := by
    dsimp [v]
    split_ifs with h
    · exact hw p h
    · positivity
  have h := hratio v hv
  have hl : 0 < volumeOn w (P.filter (· ≤ ⌊x⌋₊)) := prod_pos fun p hp ↦ hfac p (mem_filter.mp hp).1
  have hh : 0 < volumeOn w (P.filter (⌊x⌋₊ < ·)) := prod_pos fun p hp ↦ hfac p (mem_filter.mp hp).1
  have hmul : volumeOn w P = volumeOn w (P.filter (· ≤ ⌊x⌋₊)) * volumeOn w (P.filter (⌊x⌋₊ < ·)) := by
    simpa [volumeOn, not_le] using (prod_filter_mul_prod_filter_not P (· ≤ ⌊x⌋₊) (fun p ↦ 1-w p)).symm
  have hzP : P.filter (· ≤ ⌊z⌋₊) = P :=
    filter_true_of_mem fun p h ↦ Nat.le_floor (hp p h).2.2
  rw [show BethMertens.sieveProduct v x = _ from masked_product w P hP x,
    show BethMertens.sieveProduct v z = _ from masked_product w P hP z, hzP, hmul,
    div_mul_eq_div_div, div_self hl.ne', one_div] at h
  have hinv := inv_anti₀ (inv_pos.mpr hh) h
  rw [inv_inv] at hinv
  have hlx := Real.log_pos hx
  have hlz := Real.log_pos (hx.trans_le hxz)
  calc
    _ = (K * (Real.log z / Real.log x)^2)⁻¹ := by field_simp
    _ ≤ _ := hinv

/-- 素数集合や局所密度が変化しても、同じ下端から一次モーメントと全cutの評価を適用できる。 -/
theorem uniform_mertens_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ lo : ℕ, 4 ≤ lo ∧ ∀ (w : ℕ → ℝ) (P : Finset ℕ) {z : ℝ}, ↑lo ≤ z →
      (∀ p ∈ P, p.Prime ∧ lo < p ∧ (p : ℝ) ≤ z) → (∀ p ∈ P, w p ≤ 2/(p : ℝ)) →
      (∑ p ∈ P, w p * (Real.log p / Real.log z) ≤ 2001/1000) ∧
        ∀ a : ℝ, 0 ≤ a → min 1 (a^2)/(1+ε) ≤ volumeOn w (P.filter (⌊z^a⌋₊ < ·)) := by
  obtain ⟨B, hB, hR⟩ := BethMertens.ratio_le hε
  let lo := max B ⌈Real.exp 18000⌉₊
  have hBlo : B ≤ lo := le_max_left _ _
  have hlo : 4 ≤ lo := hB.trans hBlo
  have hloR : (1 : ℝ) < lo := by exact_mod_cast (by omega : 1 < lo)
  refine ⟨lo, hlo, ?_⟩
  intro w P z hz hp hw
  have hz1 := hloR.trans_le hz
  have hlog : 18000 ≤ Real.log z :=
    (Real.le_log_iff_exp_le (zero_lt_one.trans hz1)).mpr ((Nat.le_ceil _).trans
      ((show (⌈Real.exp 18000⌉₊ : ℝ) ≤ lo by exact_mod_cast (le_max_right B ⌈Real.exp 18000⌉₊)).trans hz))
  refine ⟨weighted_log_mean w P hz1.le hlog (fun p h ↦ ⟨(hp p h).1, (hp p h).2.2⟩) hw, ?_⟩
  intro a ha
  apply cutBound_le_volume w P (by linarith) hloR hz ha
  · exact fun p h ↦ ⟨by exact_mod_cast (hp p h).2.1, (hp p h).2.2⟩
  intro x hx hxz
  refine volume_lower_of_ratio w P (by linarith) (hloR.trans_le hx) hxz ?_ hw ?_
  · intro p h
    have hs := (hp p h).2.1
    exact ⟨(hp p h).1, by omega, (hp p h).2.2⟩
  · exact hR ((show (B : ℝ) ≤ lo by exact_mod_cast hBlo).trans hx) hxz

end BethCdfGrid

end

section

open Finset

namespace BethMainSieve

open OMABeth BethIteration BethSelberg BethUpperGrid

structure Conditions (P₀ : Finset ℕ) (w : ℕ → ℝ) (lo K : ℝ) : Prop where
  lo_gt : 1 < lo
  distortion : 1 ≤ K
  distortion_le : K ≤ 1001/1000
  prime : ∀ p ∈ P₀, Nat.Prime p
  large : ∀ p ∈ P₀, lo < (p : ℝ)
  weight : ∀ p ∈ P₀, w p ∈ Set.Ioo 0 1
  mean : ∀ Q ⊆ P₀, ∀ z : ℝ, lo ≤ z → (∀ p ∈ Q, (p : ℝ) ≤ z) →
    ∑ p ∈ Q, w p * (Real.log p / Real.log z) ≤ 2001/1000
  cut : ∀ Q ⊆ P₀, ∀ z : ℝ, lo ≤ z → (∀ p ∈ Q, (p : ℝ) ≤ z) →
    ∀ a : ℝ, 0 ≤ a → min 1 (a^2) / K ≤ volumeOn w (Q.filter (⌊z^a⌋₊ < ·))

theorem mass_nonneg {w : ℕ → ℝ} {P : Finset ℕ} (hw : ∀ p ∈ P, w p ∈ Set.Ioo 0 1)
    (p : ℕ) (hp : p ∈ P) : 0 ≤ mass w P p :=
  div_nonneg (mul_nonneg (hw p hp).1.le (Finset.prod_nonneg fun a ha =>
    (sub_pos.mpr (hw a (Finset.mem_filter.mp ha).1).2).le))
    (Finset.prod_nonneg fun q h => (sub_pos.mpr (hw q h).2).le)

theorem scale_log {z s D : ℝ} (hz : 1 < z) (h : z^s ≤ D) :
    s * Real.log z ≤ Real.log D := by
  have t := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hz) _) h
  rw [Real.log_rpow (zero_lt_one.trans hz)] at t
  exact t

theorem prime_parameter_ge {z D s : ℝ} {p : ℕ} (hp : 1 < p) (hpz : (p:ℝ) ≤ z)
    (hs : 0 ≤ s) (hz : 1 < z) (hD : z^s ≤ D) : s ≤ Real.log D / Real.log p := by
  have h1 : (1:ℝ) < p := by exact_mod_cast hp
  rw [le_div_iff₀ (Real.log_pos h1)]
  exact (mul_le_mul_of_nonneg_left (Real.log_le_log (zero_lt_one.trans h1) hpz) hs).trans (scale_log hz hD)

theorem child_level {p : ℕ} {D : ℝ} (hp : 1 < p) (hD : 0 < D) :
    (p:ℝ) ^ (Real.log D / Real.log p - 1) = D / p := by
  have h1 : (1:ℝ) < p := by exact_mod_cast hp
  have hp0 := zero_lt_one.trans h1
  have hlog := (Real.log_pos h1).ne'
  rw [Real.rpow_def_of_pos hp0, ← Real.exp_log (div_pos hD hp0), Real.log_div hD.ne' hp0.ne']
  congr 1; field_simp

theorem sqrt_level {z s D : ℝ} (hz : 0 < z) (hD : z^s ≤ D) :
    z^(s/2) ≤ Real.sqrt D := by
  rw [Real.le_sqrt (Real.rpow_nonneg hz.le _) ((Real.rpow_pos_of_pos hz _).le.trans hD)]
  calc (z^(s/2))^2 = (z^(s/2))^((2:ℕ):ℝ) := (Real.rpow_natCast ..).symm
       _ = z^s := by rw [← Real.rpow_mul hz.le]; congr 1; ring
       _ ≤ _ := hD

theorem from_selberg {P : Finset ℕ} {w : ℕ → ℝ} {D t : ℝ} (hp : ∀ p ∈ P, Nat.Prime p)
    (hw : ∀ p ∈ P, w p ∈ Set.Ioo 0 1) (hD : 1 ≤ D) (ht : 0 < t) (hc : t ≤ cdf w P (Real.sqrt D)) :
    HasBound true P D w ((1-t)/t) := by
  refine ⟨selbergCert w P D hp hw hD, ?_⟩
  simp only [if_true, main_selbergCert]
  have hv : 0 ≤ volumeOn w P := prod_nonneg fun p h => (sub_pos.mpr (hw p h).2).le
  calc volumeOn w P / cdf w P (Real.sqrt D) ≤ volumeOn w P / t :=
         div_le_div_of_nonneg_left hv ht hc
       _ = _ := by field_simp; ring

theorem large_upper {P₀ P : Finset ℕ} {w lo K z D s} (c : Conditions P₀ w lo K)
    (hP : P ⊆ P₀) (hz : lo ≤ z) (hPz : ∀ p ∈ P, (p:ℝ) ≤ z)
    (hs : 25 ≤ s) (hD : z^s ≤ D) : HasBound true P D w (410000 * Real.exp (-s)) := by
  have hz1 := c.lo_gt.trans_le hz
  have h₀ : 0 < z := zero_lt_one.trans hz1
  have hw (p : ℕ) (h : p ∈ P) := c.weight p (hP h)
  have hvol : 0 ≤ volumeOn w P := prod_nonneg fun p h => (sub_pos.mpr (hw p h).2).le
  have e0 := Real.exp_pos (-s)
  have h25 : (2:ℝ)^25 ≤ Real.exp s := by
    calc (2:ℝ)^25 ≤ (Real.exp 1)^25 := by gcongr; exact Real.exp_one_gt_two.le
         _ = Real.exp 25 := Real.exp_one_pow _
         _ ≤ _ := Real.exp_le_exp.mpr hs
  have hsmall : 400000 * Real.exp (-s) ≤ 1/41 := by
    rw [Real.exp_neg, mul_inv_le_iff₀ (Real.exp_pos _)]
    norm_num at h25
    linarith
  have hwI (p : ℕ) (h : p ∈ P) := Set.Ioo_subset_Icc_self (hw p h)
  have ch := cdf_compl_le_chernoff w P hz1 (fun p h => ⟨(c.prime p (hP h)).pos, hPz p h⟩)
    hwI (c.mean P hP z hz hPz) s
  let t := 1 - 400000*Real.exp (-s)
  have ht : 40/41 ≤ t := by dsimp [t]; linarith
  have ht0 : 0 < t := by linarith
  have hlev : 1 ≤ D := (Real.one_le_rpow hz1.le (by linarith : 0 ≤ s)).trans hD
  apply weaken (from_selberg (fun p h => c.prime p (hP h)) hw hlev ht0
    ((show t ≤ cdf w P (z^(s/2)) by dsimp [t]; linarith).trans (cdf_mono w P hwI (sqrt_level h₀ hD)))) _ hvol
  rw [div_le_iff₀ ht0]
  have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 410000 * Real.exp (-s) by positivity)
  dsimp [t] at *
  linarith

theorem cumulative {P₀ P : Finset ℕ} {w lo K z D s} (c : Conditions P₀ w lo K)
    (hP : P ⊆ P₀) (hz : lo ≤ z) (hPz : ∀ p ∈ P, (p:ℝ) ≤ z) (hs : 0 < s) (hD : z^s ≤ D)
    (x : ℝ) (hsx : s ≤ x) :
    (∑ p ∈ P, if Real.log D / Real.log p < x then mass w P p else 0) ≤ K * (x/s)^2 - 1 := by
  have hx := hs.trans_le hsx
  have hc := c.cut P hP z hz hPz (s/x) (by positivity)
  have hratio : s/x ≤ 1 := (div_le_one hx).mpr hsx
  rw [min_eq_right (show (s/x)^2 ≤ 1 from pow_le_one₀ (by positivity) hratio)] at hc
  exact normalized_cumulative hs hsx (c.lo_gt.trans_le hz) (zero_lt_one.trans_le c.distortion)
    (scale_log (c.lo_gt.trans_le hz) hD) w P (fun p h => (c.prime p (hP h)).one_lt)
    (fun p h => ⟨(c.weight p (hP h)).1.le,(c.weight p (hP h)).2⟩) hc

theorem large_either {P₀ P : Finset ℕ} {w lo K z D s} (c : Conditions P₀ w lo K)
    (hP : P ⊆ P₀) (hz : lo ≤ z) (hPz : ∀ p ∈ P, (p:ℝ) ≤ z)
    (hs : 26 ≤ s) (hD : z^s ≤ D) (side : Bool) :
    HasBound side P D w (3000000 * Real.exp (-s)) := by
  have hz1 := c.lo_gt.trans_le hz
  have hD1 : 1 ≤ D := (Real.one_le_rpow hz1.le (by linarith : 0 ≤ s)).trans hD
  have hvol : 0 ≤ volumeOn w P := prod_nonneg fun p h => (sub_pos.mpr (c.weight p (hP h)).2).le
  cases side with
  | true => exact weaken (large_upper c hP hz hPz (by linarith) hD) (by linarith [Real.exp_pos (-s)]) hvol
  | false =>
    let u := fun p : ℕ => Real.log D / Real.log p
    have hu (p : ℕ) (h : p ∈ P) : s ≤ u p :=
      prime_parameter_ge (c.prime p (hP h)).one_lt (hPz p h) (by linarith) hz1 hD
    have hw (p : ℕ) (h : p ∈ P) := c.weight p (hP h)
    apply alternating_step P D w (fun p => 410000 * Real.exp (1-u p)) _ hD1
      (fun p h => (c.prime p (hP h)).pos) (fun p h => ⟨(hw p h).1.le, (hw p h).2⟩)
    · intro p h
      have hp' := (c.prime p (hP h)).one_lt
      have hside := large_upper (P := Cert.below P p) c (Subset.trans (filter_subset _ _) hP) (c.large p (hP h)).le
        (fun q hq => (show (q:ℝ) ≤ p by exact_mod_cast (show q < p from (mem_filter.mp hq).2).le))
        (show 25 ≤ u p - 1 by linarith [hu p h])
        (child_level hp' (zero_lt_one.trans_le hD1)).le
      simpa [u, sub_eq_add_neg, add_comm] using hside
    · have hm (p : ℕ) (h : p ∈ P) := mass_nonneg hw p h
      have H := BethTail.exp_tail P u (mass w P) s s K (by linarith) le_rfl hs
        (zero_lt_one.trans_le c.distortion).le hm
        (fun x hx => (cumulative c hP hz hPz (by linarith) hD x hx).trans (by linarith))
      rw [filter_true_of_mem hu] at H
      have hc : 410000 * (5/2:ℝ) * K * Real.exp 1 ≤ 3000000 := by
        have h := mul_le_mul c.distortion_le Real.exp_one_lt_d9.le (Real.exp_pos _).le (by norm_num)
        linarith
      calc
        _ = 410000 * ∑ p ∈ P, mass w P p * Real.exp (1-u p) := by
          rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
        _ ≤ 410000 * (5/2 * K * (s/s)^2 * Real.exp (1-s)) := mul_le_mul_of_nonneg_left H (by norm_num)
        _ = (410000*(5/2)*K*Real.exp 1) * Real.exp (-s) := by
          rw [div_self (show s ≠ 0 by linarith), sub_eq_add_neg, Real.exp_add]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le

end BethMainSieve

end

section

open Finset

namespace BethEnvironment

open BethMainSieve

noncomputable def distortion : ℝ := 1 + 1/1000000000

/-- しきい値を変えながら素数集合を小さくしても、同じMertens評価を利用する。 -/
theorem exists_conditions :
    ∃ lo : ℕ, 4 ≤ lo ∧ ∀ (w : ℕ → ℝ) (P₀ : Finset ℕ),
      (∀ p ∈ P₀, p.Prime ∧ lo < p) →
      (∀ p ∈ P₀, w p ∈ Set.Ioo 0 1) → (∀ p ∈ P₀, w p ≤ 2/(p : ℝ)) →
      Conditions P₀ w lo distortion := by
  obtain ⟨lo, hlo, hlocal⟩ := BethCdfGrid.uniform_mertens_bounds (ε := 1/1000000000) (by norm_num)
  refine ⟨lo, hlo, ?_⟩
  intro w P₀ hp hw h2
  refine ⟨by exact_mod_cast (by omega : 1 < lo), by norm_num [distortion], by norm_num [distortion],
    fun p h ↦ (hp p h).1, fun p h ↦ by exact_mod_cast (hp p h).2, hw, ?_, ?_⟩
  · intro Q hQ z hz hQz
    exact (hlocal w Q hz (fun p h ↦ ⟨(hp p (hQ h)).1, (hp p (hQ h)).2, hQz p h⟩)
      (fun p h ↦ h2 p (hQ h))).1
  · intro Q hQ z hz hQz
    exact (hlocal w Q hz (fun p h ↦ ⟨(hp p (hQ h)).1, (hp p (hQ h)).2, hQz p h⟩)
      (fun p h ↦ h2 p (hQ h))).2

theorem exists_prime_interval_conditions :
    ∃ lo : ℕ, 4 ≤ lo ∧ ∀ {z : ℝ}, lo ≤ z →
      Conditions ((Icc (lo+1) ⌊z⌋₊).filter Nat.Prime) (fun p : ℕ ↦ 2/(p : ℝ)) lo distortion := by
  obtain ⟨lo, hlo, H⟩ := exists_conditions
  refine ⟨lo, hlo, ?_⟩
  intro z _
  let P := (Icc (lo+1) ⌊z⌋₊).filter Nat.Prime
  have hp (p : ℕ) (h : p ∈ P) : p.Prime ∧ lo < p :=
    ⟨(mem_filter.mp h).2, (mem_Icc.mp (mem_filter.mp h).1).1⟩
  apply H _ P hp _ (fun p h ↦ le_rfl)
  intro p h
  have hloP := (hp p h).2
  have htwo : (2 : ℝ) < p := by exact_mod_cast (by omega : 2 < p)
  have hp0 : 0 < (p:ℝ) := lt_trans (by norm_num) htwo
  exact ⟨div_pos (by norm_num) hp0, (div_lt_one hp0).mpr htwo⟩

end BethEnvironment

end

section

namespace BethProfile

open Finset

structure Profile (N : ℕ) (K : ℝ) where
  F : ℕ → ℝ
  e : Bool → ℕ → ℝ
  F_mono : ∀ {a b : ℕ}, a ≤ b → b ≤ 40*N → F a ≤ F b
  F_zero : 0 ≤ F 0
  F_cap : F (40*N) ≤ 1
  cdf_step : ∀ j ≤ 40*N, F j ≤ max (max 0 (1 - 400000 * Real.exp (-((j:ℝ)/N))))
    (∑ t ∈ range (40*N+1), BethCdfGrid.increment F t * BethCdfGrid.cutBound N K j t)
  e_anti : ∀ side, Antitone (e side)
  e_nonneg : ∀ side j, 0 ≤ e side j
  lower_branch : ∀ j < 40*N,
    1 ≤ e false j ∨
    (26*N ≤ j ∧ 3000000*Real.exp (-((j:ℝ)/N)) ≤ e false j) ∨
    (4*N ≤ j ∧ BethTail.tableStep K N j (40*N) (e true) ≤ e false j)
  upper_branch : ∀ j < 40*N, 3*N ≤ j →
    (0 < F j ∧ (1-F j)/(F j) ≤ e true j) ∨
    (26*N ≤ j ∧ 3000000*Real.exp (-((j:ℝ)/N)) ≤ e true j) ∨
    BethTail.tableStep K N j (40*N) (e false) ≤ e true j

end BethProfile

end

section

open Finset

namespace BethMainSieve

open BethSelberg BethIteration BethUpperGrid BethCdfGrid OMABeth BethProfile

theorem of_profile {P₀ : Finset ℕ} {w lo K} (c : Conditions P₀ w lo K)
    {N : ℕ} (hN : 0 < N) (t : Profile N K)
    (P : Finset ℕ) (hP : P ⊆ P₀) (z D : ℝ) (hz : lo ≤ z) (hPz : ∀ p ∈ P, (p:ℝ) ≤ z)
    (j : ℕ) (hj : j < 40*N) (hD : z^((j:ℝ)/N) ≤ D)
    (side : Bool) (hup : side = true → 3*N ≤ j) :
    HasBound side P D w (t.e side j) := by
  classical
  induction P using Finset.strongInductionOn generalizing z D j side with
  | _ P ih =>
    have hz1 := c.lo_gt.trans_le hz
    have hz0 := zero_lt_one.trans hz1
    have hN0 : (0:ℝ) < N := by exact_mod_cast hN
    have hs : 0 ≤ (j:ℝ)/N := by positivity
    have hD1 : 1 ≤ D := (Real.one_le_rpow hz1.le hs).trans hD
    have hw (p : ℕ) (h : p ∈ P) := c.weight p (hP h)
    have hvol : 0 ≤ volumeOn w P := prod_nonneg fun p h => (sub_pos.mpr (hw p h).2).le
    have hlarge (b : Bool) (hj26 : 26*N ≤ j) (h : 3000000*Real.exp (-((j:ℝ)/N)) ≤ t.e b j) :
        HasBound b P D w (t.e b j) := by
      have h26 : (26:ℝ) ≤ (j:ℝ)/N := (le_div_iff₀ hN0).mpr (by exact_mod_cast hj26)
      exact weaken (large_either c hP hz hPz h26 hD b) h hvol
    have hstep (b : Bool) (start : (if b then 3 else 4)*N ≤ j)
        (h : BethTail.tableStep K N j (40*N) (t.e (!b)) ≤ t.e b j) :
        HasBound b P D w (t.e b j) := by
      let u (p : ℕ) := Real.log D / Real.log p
      let idx (p : ℕ) := ⌊(N:ℝ)*u p⌋₊
      let E (p : ℕ) := if idx p < 40*N then t.e (!b) (idx p-N) else
          3000000*Real.exp (1-u p)
      have jlarge : 3*N ≤ j := by cases b <;> simp only [Bool.false_eq_true, if_false, if_true] at start <;> omega
      have hjpos : 0 < j := by omega
      have hspos : 0 < (j:ℝ)/N := by positivity
      have hu (p : ℕ) (hp : p ∈ P) : (j:ℝ)/N ≤ u p :=
        prime_parameter_ge (c.prime p (hP hp)).one_lt (hPz p hp) hs hz1 hD
      have hidx (p : ℕ) (hp : p ∈ P) : j ≤ idx p := by
        apply Nat.le_floor; rw [mul_comm]; exact (div_le_iff₀ hN0).mp (hu p hp)
      have hfar (p : ℕ) (hp : p ∈ P) : 40 ≤ u p ↔ 40*N ≤ idx p := by
        constructor
        · intro hh; apply Nat.le_floor; push_cast; nlinarith
        · intro hh
          have : (40:ℝ)*N ≤ (idx p:ℝ) := by exact_mod_cast hh
          have hf : (idx p:ℝ) ≤ (N:ℝ)*u p := Nat.floor_le (mul_nonneg hN0.le (hs.trans (hu p hp)))
          nlinarith
      apply weaken _ h hvol
      apply alternating_step P D w E _ hD1 (fun p hp => (c.prime p (hP hp)).pos)
        (fun p hp => ⟨(hw p hp).1.le, (hw p hp).2⟩)
      · intro p hp
        let Q := Cert.below P p
        have hQ : Q ⊂ P := filter_ssubset.mpr ⟨p,hp,lt_irrefl _⟩
        have hQ0 : Q ⊆ P₀ := Subset.trans (filter_subset _ _) hP
        have hQp : ∀ q ∈ Q, (q:ℝ) ≤ p := fun q hq =>
          by exact_mod_cast (show q < p from (mem_filter.mp hq).2).le
        have p1 := (c.prime p (hP hp)).one_lt
        have p1R : (1:ℝ) < p := by exact_mod_cast p1
        have hD' : (p:ℝ)^(u p-1) = D/p := child_level p1 (zero_lt_one.trans_le hD1)
        by_cases hn : idx p < 40*N
        · have hNi : N ≤ idx p := by have := hidx p hp; omega
          have hpow : (p:ℝ) ^ (((idx p - N : ℕ):ℝ)/N) ≤ D/p := by
            rw [← hD']; apply Real.rpow_le_rpow_of_exponent_le p1R.le
            rw [div_le_iff₀ hN0, Nat.cast_sub hNi]
            have hfl : (idx p:ℝ) ≤ (N:ℝ)*u p := Nat.floor_le (mul_nonneg hN0.le (hs.trans (hu p hp)))
            linarith
          have hh := ih Q hQ hQ0 (p:ℝ) (D/p) (c.large p (hP hp)).le hQp (idx p-N)
            (by omega) hpow (!b) (by
              intro Hb
              have hji := hidx p hp
              cases b <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false, if_true] at start Hb <;> omega)
          simpa only [E, if_pos hn] using hh
        · have h40 := (hfar p hp).mpr (le_of_not_gt hn)
          have hh := large_either c hQ0 (c.large p (hP hp)).le hQp
            (show 26 ≤ u p-1 by linarith) hD'.le (!b)
          simpa only [E, if_neg hn, neg_sub] using hh
      · apply BethTail.table_step_bound P (mass w P) u E (t.e (!b)) N j hN hjpos hj.le K c.distortion
          (t.e_anti _) (t.e_nonneg _) (fun p hp => mass_nonneg hw p hp) hu
          (cumulative c hP hz hPz hspos hD)
        · exact fun p _ hn => by simp [E, idx, hn]
        · exact fun p hp h40 => by rw [show E p = _ from if_neg (not_lt.mpr ((hfar p hp).mp h40))]
    cases side with
    | false =>
      rcases t.lower_branch j hj with h | ⟨h26,h⟩ | ⟨h4,h⟩
      · exact weaken (zero_lower P D w) h hvol
      · exact hlarge false h26 h
      · exact hstep false h4 h
    | true =>
      have h3 := hup rfl
      rcases t.upper_branch j hj h3 with ⟨hF,h⟩ | ⟨h26,h⟩ | h
      · have hcdf := BethCdfGrid.cdf_ge_table w P₀ N (40*N) hN t.F K lo c.lo_gt c.large
            (fun p hp => Set.Ioo_subset_Icc_self (c.weight p hp))
            t.F_mono t.F_zero t.F_cap t.cdf_step c.mean (by
              intro Q hQ z hz hQz k hk a ha
              exact c.cut Q hQ z hz hQz _ (by positivity))
            P hP z hz hPz j hj.le
        have hsqr := sqrt_level hz0 hD
        have heq : ((j:ℝ)/N)/2 = (j:ℝ)/(2*N) := by ring
        rw [heq] at hsqr
        exact weaken (from_selberg (fun p hp => c.prime p (hP hp)) hw hD1 hF
          (hcdf.trans (cdf_mono w P (fun p hp => Set.Ioo_subset_Icc_self (hw p hp)) hsqr))) h hvol
      · exact hlarge true h26 h
      · exact hstep true h3 h

end BethMainSieve

end

section

/- Beth's lower bound from the finite two-dimensional sieve profile. -/

open Finset Filter

namespace BethGoal

theorem of_profile (t : BethProfile.Profile 15000 BethEnvironment.distortion)
    (hmargin : t.e false 63999 ≤ 1 - 1/100000) :
    type_of% @Erdos724.erdos_724.variants.beth := by
  obtain ⟨lo,hlo,hcond⟩ := BethEnvironment.exists_prime_interval_conditions
  apply OMABeth.beth_of_interval_sieve
  apply OMABeth.Application.h4_of_cert lo hlo (α := 21333/5000) (δ := 1/100000)
    (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [eventually_ge_atTop (lo:ℝ)] with z hz
  let P := OMABeth.Application.largePrimes lo z
  let w := fun p : ℕ => (2:ℝ) / p
  have hpz (p : ℕ) (h : p ∈ P) : (p:ℝ) ≤ z :=
    (show (p:ℝ) ≤ ⌊z⌋₊ by exact_mod_cast (mem_Icc.mp (mem_filter.mp h).1).2).trans
      (Nat.floor_le ((Nat.cast_nonneg lo).trans hz))
  have hcond' : BethMainSieve.Conditions P w lo BethEnvironment.distortion := hcond hz
  obtain ⟨cert,hcert⟩ := BethMainSieve.of_profile hcond' (by norm_num : 0 < 15000) t P
    (Subset.rfl) z (z^((21333:ℝ)/5000)) hz hpz 63999 (by norm_num) (by norm_num)
    false (by simp)
  refine ⟨cert, ?_⟩
  simp only [Bool.false_eq_true,if_false] at hcert
  have hvol : 0 ≤ BethSelberg.volumeOn w P :=
    prod_nonneg fun p hp => (sub_pos.mpr (hcond'.weight p hp).2).le
  exact (mul_le_mul_of_nonneg_left (by linarith : (1:ℝ)/100000 ≤ 1 - t.e false 63999) hvol).trans hcert

end BethGoal

end

section

open Finset

namespace BethBernstein

/-- 単項式を区間[0,1]のBernstein基底で展開するとき、k番目の係数が全次数に寄与する和 -/
private theorem sum_row (d k : ℕ) (hk : k ≤ d) (v t : ℝ) :
    (∑ i ∈ range (d+1), if k ≤ i then
        v * ((d-k).choose (i-k) : ℝ) * t^i * (1-t)^(d-i) else 0) = v*t^k := by
  rw [← sum_filter]
  have hI : (range (d+1)).filter (k ≤ ·) = Ico k (d+1) := by
    ext i; simp [and_comm]
  rw [hI, sum_Ico_eq_sum_range, show d+1-k = d-k+1 by omega]
  calc
    _ = ∑ n ∈ range (d-k+1), (v*t^k) * (t^n * (1-t)^(d-k-n) * ((d-k).choose n : ℝ)) := by
      refine sum_congr rfl fun n hn ↦ ?_
      rw [Nat.add_sub_cancel_left, pow_add, show d-(k+n) = d-k-n by omega]
      ring
    _ = (v*t^k) * (t+(1-t))^(d-k) := by rw [add_pow, mul_sum]
    _ = v*t^k := by simp

theorem expansion (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (∑ k ∈ range (d+1), c k * t^k) =
      ∑ i ∈ range (d+1), (∑ k ∈ range (i+1), c k * ((d-k).choose (i-k) : ℝ)) *
        t^i * (1-t)^(d-i) := by
  calc
    _ = ∑ k ∈ range (d+1), ∑ i ∈ range (d+1), if k ≤ i then
          c k * ((d-k).choose (i-k) : ℝ) * t^i * (1-t)^(d-i) else 0 :=
      sum_congr rfl fun k hk ↦ (sum_row d k (Nat.lt_succ_iff.mp (mem_range.mp hk)) (c k) t).symm
    _ = _ := by
      rw [sum_comm]
      refine sum_congr rfl fun i hi ↦ ?_
      rw [← sum_filter]
      have hI : (range (d+1)).filter (· ≤ i) = range (i+1) := by
        ext k
        simp only [mem_filter, mem_range] at hi ⊢
        omega
      rw [hI, sum_mul, sum_mul]

/-- 非負性をカーネルで計算するための整数係数。通常のBernstein係数と同符号になる。 -/
def coeff (d L : ℕ) (c : ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ k ∈ range (i+1), c k * (L : ℤ)^k * ((d-k).choose (i-k) : ℤ)

theorem nonneg_of_coeff (d L : ℕ) (c : ℕ → ℤ) (hc : ∀ i ≤ d, 0 ≤ coeff d L c i)
    {x : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) :
    0 ≤ ∑ k ∈ range (d+1), (c k : ℝ) * x^k := by
  let t := x/(L:ℝ)
  have ht : 0 ≤ t := div_nonneg hx (Nat.cast_nonneg L)
  have hts : t ≤ 1 := by
    by_cases h : L = 0
    · simp [t,h]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).mpr hL
  have hxt : x = (L:ℝ)*t := by
    by_cases h : L = 0
    · have hx' : x = 0 := le_antisymm (by simpa [h] using hL) hx
      simp [hx', t]
    · dsimp [t]; field_simp
  calc
    0 ≤ ∑ i ∈ range (d+1),
        (∑ k ∈ range (i+1), ((c k : ℝ) * (L:ℝ)^k) * ((d-k).choose (i-k) : ℝ)) *
          t^i * (1-t)^(d-i) := by
      refine sum_nonneg fun i hi ↦ mul_nonneg (mul_nonneg ?_ (pow_nonneg ht _)) (pow_nonneg (sub_nonneg.mpr hts) _)
      have H := hc i (Nat.lt_succ_iff.mp (mem_range.mp hi))
      unfold coeff at H
      exact_mod_cast H
    _ = ∑ k ∈ range (d+1), ((c k : ℝ) * (L:ℝ)^k) * t^k := (expansion _ _ _).symm
    _ = _ := by
      refine sum_congr rfl fun k hk ↦ ?_
      rw [hxt, mul_pow, mul_assoc]

/-- 次数順の整数係数を受け取り、区間での非負性に十分な有限個の符号を判定する。 -/
def check (d L : ℕ) (c : ℕ → ℤ) : Bool :=
  (List.range (d+1)).all fun i ↦ decide (0 ≤ coeff d L c i)

theorem nonneg_of_check (d L : ℕ) (c : ℕ → ℤ) (h : check d L c = true)
    {x : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) :
    0 ≤ ∑ k ∈ range (d+1), (c k : ℝ) * x^k := by
  apply nonneg_of_coeff d L c _ hx hL
  simpa only [check, List.all_eq_true, List.mem_range, Nat.lt_succ_iff, decide_eq_true_eq] using h

noncomputable def horner : List ℤ → ℝ → ℝ
  | [], _ => 0
  | a :: c, x => a + x * horner c x

theorem horner_eq_sum (c : List ℤ) (x : ℝ) :
    horner c x = ∑ k ∈ range c.length, (c.getD k 0 : ℝ) * x^k := by
  induction c with
  | nil => simp [horner]
  | cons a c ih =>
    rw [horner, ih, mul_sum, List.length_cons, sum_range_succ', add_comm]
    congr 1
    · exact sum_congr rfl fun k hk ↦ by simp [List.getD, pow_succ]; ring
    · simp [List.getD]

def checkList (L : ℕ) (c : List ℤ) : Bool :=
  check (c.length - 1) L (fun k ↦ c.getD k 0)

theorem nonneg_horner_of_check (L : ℕ) (c : List ℤ) (h : checkList L c = true)
    {x : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) : 0 ≤ horner c x := by
  cases c with
  | nil => simp [horner]
  | cons a c =>
    rw [horner_eq_sum]
    simpa using (nonneg_of_check ((a::c).length - 1) L (fun k ↦ (a::c).getD k 0) h hx hL)

end BethBernstein

end

section

namespace BethNumericPoly

open BethBernstein

namespace Coeff

def add : List ℤ → List ℤ → List ℤ
  | [], b => b
  | a, [] => a
  | a::as, b::bs => (a+b)::add as bs

def scale (z : ℤ) (a : List ℤ) : List ℤ :=
  a.map (z * ·)

def mul : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a::as, bs => add (scale a bs) (0::mul as bs)

def shift (z : ℤ) : List ℤ → List ℤ
  | [] => []
  | a::as =>
    let p := shift z as
    add [a] (add (scale z p) (0::p))

theorem eval_add (a b : List ℤ) (x : ℝ) :
    horner (add a b) x = horner a x + horner b x := by
  induction a generalizing b with
  | nil => simp [add,horner]
  | cons a as ih =>
    cases b with
    | nil => simp [add,horner]
    | cons b bs => simp [add,horner,ih]; ring

theorem eval_scale (z : ℤ) (a : List ℤ) (x : ℝ) :
    horner (scale z a) x = z * horner a x := by
  induction a with
  | nil => simp [horner,scale]
  | cons a as ih =>
    simp only [scale,List.map_cons,horner,Int.cast_mul] at ih ⊢
    rw [ih]; ring

theorem eval_mul (a b : List ℤ) (x : ℝ) :
    horner (mul a b) x = horner a x * horner b x := by
  induction a with
  | nil => simp [mul,horner]
  | cons a as ih => simp only [mul,eval_add,eval_scale,horner,Int.cast_zero,ih]; ring

theorem eval_shift (z : ℤ) (a : List ℤ) (x : ℝ) :
    horner (shift z a) x = horner a (z+x) := by
  induction a with
  | nil => simp [shift,horner]
  | cons a as ih => simp only [shift,eval_add,eval_scale,horner,Int.cast_zero,ih]; ring

end Coeff

/-- 整数係数と一つの正の分母で有理係数多項式を表す -/
structure Poly where
  c : List ℤ
  d : ℕ+
deriving Inhabited

namespace Poly

noncomputable def eval (p : Poly) (x : ℝ) : ℝ := horner p.c x / (p.d : ℕ)

def scalar (z : ℤ) (d : ℕ+ := 1) : Poly := ⟨[z],d⟩

def var (z : ℤ) : Poly := ⟨[z,1],1⟩

def add (p q : Poly) : Poly :=
  if p.d = q.d then ⟨Coeff.add p.c q.c,p.d⟩
  else ⟨Coeff.add (Coeff.scale (q.d : ℕ) p.c) (Coeff.scale (p.d : ℕ) q.c),p.d*q.d⟩

def scale (p : Poly) (z : ℤ) : Poly := ⟨Coeff.scale z p.c,p.d⟩

def sub (p q : Poly) : Poly := p.add (q.scale (-1))

def mul (p q : Poly) : Poly := ⟨Coeff.mul p.c q.c,p.d*q.d⟩

def shift (p : Poly) (k : ℤ) : Poly := ⟨Coeff.shift k p.c,p.d⟩

theorem eval_scalar (z : ℤ) (d : ℕ+) (x : ℝ) :
    (scalar z d).eval x = z / (d : ℕ) := by simp [eval,scalar,horner]

theorem eval_var (z : ℤ) (x : ℝ) : (var z).eval x = z+x := by simp [eval,var,horner]

theorem eval_add (p q : Poly) (x : ℝ) : (p.add q).eval x = p.eval x + q.eval x := by
  have hp : 0 < ((p.d : ℕ) : ℝ) := by exact_mod_cast p.d.property
  have hq : 0 < ((q.d : ℕ) : ℝ) := by exact_mod_cast q.d.property
  unfold add
  split <;> rename_i h
  · simp [eval,Coeff.eval_add,h,add_div]
  · simp only [eval,Coeff.eval_add,Coeff.eval_scale,Int.cast_natCast,PNat.mul_coe,Nat.cast_mul]
    field_simp

theorem eval_scale (p : Poly) (z : ℤ) (x : ℝ) : (p.scale z).eval x = z*p.eval x := by
  simp only [scale,eval,Coeff.eval_scale]; ring

theorem eval_sub (p q : Poly) (x : ℝ) : (p.sub q).eval x = p.eval x - q.eval x := by
  simp [sub,eval_add,eval_scale,sub_eq_add_neg]

theorem eval_mul (p q : Poly) (x : ℝ) : (p.mul q).eval x = p.eval x * q.eval x := by
  simp [mul,eval,Coeff.eval_mul,PNat.mul_coe,div_mul_div_comm]

theorem eval_shift (p : Poly) (z : ℤ) (x : ℝ) : (p.shift z).eval x = p.eval (z+x) := by
  simp [shift,eval,Coeff.eval_shift]

def cubic (w : ℕ+) (a b c d : ℤ) (s : ℕ+) : Poly :=
  let h : ℤ := (w : ℕ)
  ⟨[a*h^3,3*(b-a)*h^2,3*(c-2*b+a)*h,d-3*c+3*b-a],w^3*s⟩

theorem eval_cubic (w : ℕ+) (a b c d : ℤ) (s : ℕ+) (x : ℝ) :
    (cubic w a b c d s).eval x =
    (a*((w:ℕ)-x)^3+3*b*x*((w:ℕ)-x)^2+3*c*x^2*((w:ℕ)-x)+d*x^3)/
      (((w:ℕ):ℝ)^3*(s:ℕ)) := by
  simp only [cubic,eval,horner,PNat.mul_coe,PNat.pow_coe,Nat.cast_mul,Nat.cast_pow,
    Int.cast_mul,Int.cast_pow,Int.cast_sub,Int.cast_add,Int.cast_ofNat,Int.cast_natCast]
  ring

/-- 重み付き3次式の有限和。差分を取ると元の4次式に戻る -/
def antiderivative4 (p : Poly) : Poly :=
  let a := p.c.getD 0 0
  let b := p.c.getD 1 0
  let c := p.c.getD 2 0
  let d := p.c.getD 3 0
  let e := p.c.getD 4 0
  ⟨[0,60*a-30*b+10*c-2*e,30*b-30*c+15*d,20*c-30*d+20*e,15*d-30*e,12*e],60*p.d⟩

private theorem eval_take5 (c : List ℤ) (hc : c.length ≤ 5) (x : ℝ) :
    horner c x = (c.getD 0 0 : ℤ) + (c.getD 1 0 : ℤ)*x + (c.getD 2 0 : ℤ)*x^2 +
      (c.getD 3 0 : ℤ)*x^3 + (c.getD 4 0 : ℤ)*x^4 := by
  obtain _ | ⟨a,c⟩ := c
  · simp [horner]
  obtain _ | ⟨b,c⟩ := c
  · simp [horner]
  obtain _ | ⟨d,c⟩ := c
  · simp [horner]; ring
  obtain _ | ⟨e,c⟩ := c
  · simp [horner]; ring
  obtain _ | ⟨f,c⟩ := c
  · simp [horner]; ring
  have hz : c.length = 0 := by simp only [List.length_cons] at hc; omega
  have cz : c = [] := List.length_eq_zero_iff.mp hz
  subst c
  simp [horner]; ring

theorem eval_antiderivative4_diff (p : Poly) (h : p.c.length ≤ 5) (x : ℝ) :
    p.antiderivative4.eval (x+1) - p.antiderivative4.eval x = p.eval x := by
  simp only [antiderivative4,eval,horner,PNat.mul_coe,Nat.cast_mul,PNat.val_ofNat,
    Nat.cast_ofNat,Int.cast_zero,Int.cast_mul,Int.cast_sub,Int.cast_add,Int.cast_ofNat]
  rw [eval_take5 p.c h x]
  ring

def valueAtInt (p : Poly) (x : ℤ) : ℤ :=
  p.c.foldr (fun a b ↦ a+x*b) 0

theorem cast_valueAtInt (p : Poly) (x : ℤ) :
    (p.valueAtInt x : ℝ) = horner p.c x := by
  unfold valueAtInt
  induction p.c with
  | nil => simp [horner]
  | cons a as ih => simp [horner,ih]

def atInt (p : Poly) (x : ℤ) : Poly := scalar (p.valueAtInt x) p.d

theorem eval_atInt (p : Poly) (x : ℤ) (y : ℝ) : (p.atInt x).eval y = p.eval x := by
  rw [atInt,eval_scalar,cast_valueAtInt,eval]

def test (p : Poly) (L : ℕ) : Bool := checkList L p.c

theorem test_sound (p : Poly) (L : ℕ) (h : p.test L = true) {x : ℝ} (hx : 0 ≤ x) (hL : x ≤ L) :
    0 ≤ p.eval x :=
  div_nonneg (nonneg_horner_of_check L p.c h hx hL) (Nat.cast_nonneg _)

end Poly
end BethNumericPoly

end

section

/- Bernstein形の3次数表は、制御点の順序と両端の値を保つ。 -/

namespace BethCubicOrder

open BethNumericPoly

theorem left (w s : ℕ+) (a b c d : ℤ) :
    (Poly.cubic w a b c d s).eval 0 = (a : ℝ) / (s : ℕ) := by
  rw [Poly.eval_cubic]
  have hw : ((w : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr w.property).ne'
  simp
  field_simp [hw]

theorem right (w s : ℕ+) (a b c d : ℤ) :
    (Poly.cubic w a b c d s).eval (w : ℕ) = (d : ℝ) / (s : ℕ) := by
  rw [Poly.eval_cubic]
  have hw : ((w : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr w.property).ne'
  simp
  field_simp [hw]

private def blend (w x a b : ℝ) := (w-x)*a + x*b

private lemma blend_args {w x a b c d : ℝ} (hx : 0 ≤ x) (hw : x ≤ w)
    (hac : a ≤ c) (hbd : b ≤ d) : blend w x a b ≤ blend w x c d :=
  add_le_add (mul_le_mul_of_nonneg_left hac (sub_nonneg.mpr hw)) (mul_le_mul_of_nonneg_left hbd hx)

private lemma blend_arg {w x y a b : ℝ} (hxy : x ≤ y) (hab : a ≤ b) :
    blend w x a b ≤ blend w y a b := by
  dsimp [blend]
  nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hab)]

private def quad (w x a b c : ℝ) :=
  blend w x (blend w x a b) (blend w x b c)

private lemma quad_arg {w x y a b c : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ w)
    (hab : a ≤ b) (hbc : b ≤ c) : quad w x a b c ≤ quad w y a b c :=
  (blend_arg hxy (blend_args hx (hxy.trans hy) hab hbc)).trans
    (blend_args (hx.trans hxy) hy (blend_arg hxy hab) (blend_arg hxy hbc))

private lemma quad_args {w x a b c d : ℝ} (hx : 0 ≤ x) (hw : x ≤ w)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : quad w x a b c ≤ quad w x b c d :=
  blend_args hx hw (blend_args hx hw hab hbc) (blend_args hx hw hbc hcd)

/-- どちら向きの単調性も、符号を付けた4つの制御点の順序から従う。 -/
theorem monotone_signed (w s : ℕ+) (a b c d sign : ℤ)
    (hab : sign*a ≤ sign*b) (hbc : sign*b ≤ sign*c) (hcd : sign*c ≤ sign*d)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ (w : ℕ)) :
    (sign : ℝ) * (Poly.cubic w a b c d s).eval x ≤
      (sign : ℝ) * (Poly.cubic w a b c d s).eval y := by
  let A := (sign : ℝ)*a
  let B := (sign : ℝ)*b
  let C := (sign : ℝ)*c
  let E := (sign : ℝ)*d
  have hAB : A ≤ B := by dsimp [A,B]; exact_mod_cast hab
  have hBC : B ≤ C := by dsimp [B,C]; exact_mod_cast hbc
  have hCE : C ≤ E := by dsimp [C,E]; exact_mod_cast hcd
  have heq (t : ℝ) : (sign : ℝ) * (Poly.cubic w a b c d s).eval t =
      blend (w : ℕ) t (quad (w : ℕ) t A B C) (quad (w : ℕ) t B C E) /
        (((w : ℕ) : ℝ)^3*(s : ℕ)) := by
    rw [Poly.eval_cubic]
    dsimp [quad, blend, A, B, C, E]
    ring
  rw [heq, heq]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (blend_arg hxy (quad_args hx (hxy.trans hy) hAB hBC hCE)).trans
    (blend_args (hx.trans hxy) hy (quad_arg hx hxy hy hAB hBC) (quad_arg hx hxy hy hBC hCE))

end BethCubicOrder

end

section

/- Evaluation and monotonicity of the piecewise cubic functions in the certificate. -/

namespace BethNumericMesh

open BethNumericPoly

structure Knot where
  start : ℕ
  y : ℤ
  b : ℤ
  c : ℤ
deriving Inhabited

structure Mesh where
  size : ℕ
  lookup : ℕ → Knot
  scale : ℕ+
deriving Inhabited

namespace Mesh

def row (m : Mesh) (i : ℕ) : Knot := m.lookup i

def last (m : Mesh) : ℕ := m.size - 2

def width (m : Mesh) (i : ℕ) : ℕ+ :=
  ⟨((m.row (i+1)).start - (m.row i).start - 1) + 1, Nat.succ_pos _⟩

def piece (m : Mesh) (i : ℕ) : Poly :=
  Poly.cubic (m.width i) (m.row i).y (m.row i).b (m.row i).c (m.row (i+1)).y m.scale

def index (m : Mesh) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun i ↦ (m.row i).start ≤ j) m.last

def offset (m : Mesh) (i j : ℕ) : ℕ :=
  min j (m.row (i+1)).start - (m.row i).start

noncomputable def evalUsing (m : Mesh) (pieces : ℕ → Poly) (j : ℕ) : ℝ :=
  (pieces (m.index j)).eval (m.offset (m.index j) j)

noncomputable def eval (m : Mesh) (j : ℕ) : ℝ := m.evalUsing m.piece j

def Starts (m : Mesh) : Prop := ∀ i ≤ m.last, (m.row i).start < (m.row (i+1)).start

def Controls (m : Mesh) (sign : ℤ) : Prop :=
  ∀ i ≤ m.last, sign * (m.row i).y ≤ sign * (m.row i).b ∧
    sign * (m.row i).b ≤ sign * (m.row i).c ∧ sign * (m.row i).c ≤ sign * (m.row (i+1)).y

def checkStarts (m : Mesh) : Bool :=
  (List.range (m.last+1)).all fun i ↦ decide ((m.row i).start < (m.row (i+1)).start)

def checkControls (m : Mesh) (sign : ℤ) : Bool :=
  (List.range (m.last+1)).all fun i ↦ decide (sign * (m.row i).y ≤ sign * (m.row i).b ∧
    sign * (m.row i).b ≤ sign * (m.row i).c ∧ sign * (m.row i).c ≤ sign * (m.row (i+1)).y)

theorem starts_of_check {m : Mesh} (h : m.checkStarts) : m.Starts := by
  simpa only [checkStarts, Starts, List.all_eq_true, List.mem_range, Nat.lt_succ_iff,
    decide_eq_true_eq] using h

theorem controls_of_check {m : Mesh} {s : ℤ} (h : m.checkControls s) : m.Controls s := by
  simpa only [checkControls, Controls, List.all_eq_true, List.mem_range, Nat.lt_succ_iff,
    decide_eq_true_eq] using h

private theorem chain {α : Type*} [Preorder α] {f : ℕ → α} {M : ℕ}
    (h : ∀ i ≤ M, f i ≤ f (i+1)) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ M+1) : f i ≤ f j := by
  induction hij with
  | refl => exact le_rfl
  | @step j _ ih => exact (ih (by omega)).trans (h j (by omega))

theorem width_eq {m : Mesh} (h : m.Starts) {i : ℕ} (hi : i ≤ m.last) :
    (m.width i : ℕ) = (m.row (i+1)).start - (m.row i).start := by
  have hlt := h i hi
  change (_ - _ - 1) + 1 = _
  omega

theorem index_eq {m : Mesh} (h : m.Starts) {i j : ℕ} (hi : i ≤ m.last)
    (ha : (m.row i).start ≤ j) (hb : j < (m.row (i+1)).start) : m.index j = i := by
  apply Nat.findGreatest_eq_iff.mpr
  refine ⟨hi, fun _ ↦ ha, fun k hk hkl ↦ ?_⟩
  exact not_le.mpr (hb.trans_le (chain (f := fun k ↦ (m.row k).start)
    (fun t ht ↦ (h t ht).le) hk (by omega)))

theorem evalUsing_piece_lt {m : Mesh} (h : m.Starts) (pieces : ℕ → Poly) {i j : ℕ}
    (hi : i ≤ m.last) (ha : (m.row i).start ≤ j) (hb : j < (m.row (i+1)).start) :
    m.evalUsing pieces j = (pieces i).eval (j - (m.row i).start : ℕ) := by
  simp only [evalUsing, index_eq h hi ha hb, offset, min_eq_left hb.le]

theorem evalUsing_piece {m : Mesh} (h : m.Starts) (pieces : ℕ → Poly)
    (hl : ∀ i ≤ m.last, (pieces i).eval 0 = ((m.row i).y : ℝ)/(m.scale : ℕ))
    (hr : ∀ i ≤ m.last, (pieces i).eval (m.width i : ℕ) = ((m.row (i+1)).y : ℝ)/(m.scale : ℕ))
    {i j : ℕ} (hi : i ≤ m.last) (ha : (m.row i).start ≤ j) (hb : j ≤ (m.row (i+1)).start) :
    m.evalUsing pieces j = (pieces i).eval (j - (m.row i).start : ℕ) := by
  rcases lt_or_eq_of_le hb with hlt | rfl
  · exact evalUsing_piece_lt h pieces hi ha hlt
  by_cases hn : i+1 ≤ m.last
  · rw [evalUsing_piece_lt h pieces hn le_rfl (h (i+1) hn), Nat.sub_self, Nat.cast_zero,
      ← width_eq h hi, hl _ hn, hr _ hi]
  · have he : i = m.last := by omega
    have hidx : m.index (m.row (i+1)).start = i := by
      rw [he]
      exact Nat.findGreatest_eq (P := fun k ↦ (m.row k).start ≤ (m.row (m.last+1)).start)
        (h _ le_rfl).le
    simp [evalUsing, hidx, offset]

theorem eval_piece {m : Mesh} (h : m.Starts) {i j : ℕ} (hi : i ≤ m.last)
    (ha : (m.row i).start ≤ j) (hb : j ≤ (m.row (i+1)).start) :
    m.eval j = (m.piece i).eval (j - (m.row i).start : ℕ) := by
  exact evalUsing_piece h m.piece (fun _ _ ↦ BethCubicOrder.left ..)
    (fun _ _ ↦ BethCubicOrder.right ..) hi ha hb

theorem eval_shift {m : Mesh} (h : m.Starts) {i a j : ℕ} (hi : i ≤ m.last)
    (ha : (m.row i).start ≤ a) (haj : a ≤ j) (hb : j ≤ (m.row (i+1)).start) :
    ((m.piece i).shift ((a - (m.row i).start : ℕ) : ℤ)).eval (j-a : ℕ) = m.eval j := by
  rw [Poly.eval_shift, eval_piece h hi (ha.trans haj) hb, Int.cast_natCast, ← Nat.cast_add]
  congr 2
  omega

theorem eval_left {m : Mesh} (h : m.Starts) {j : ℕ} (hj : j ≤ (m.row 0).start) :
    m.eval j = ((m.row 0).y : ℝ)/(m.scale : ℕ) := by
  have hi : m.index j = 0 := by
    apply Nat.findGreatest_eq_zero_iff.mpr
    intro k hk hkl
    exact not_le.mpr (hj.trans_lt ((h 0 (Nat.zero_le _)).trans_le
      (chain (f := fun k ↦ (m.row k).start) (fun i hi ↦ (h i hi).le) hk (by omega))))
  have hoff : m.offset 0 j = 0 := Nat.sub_eq_zero_of_le ((min_le_left ..).trans hj)
  rw [eval, evalUsing, hi, hoff, Nat.cast_zero]
  exact BethCubicOrder.left ..

theorem eval_right {m : Mesh} (h : m.Starts) {j : ℕ} (hj : (m.row (m.last+1)).start ≤ j) :
    m.eval j = ((m.row (m.last+1)).y : ℝ)/(m.scale : ℕ) := by
  have hi : m.index j = m.last := Nat.findGreatest_eq (P := fun i ↦ (m.row i).start ≤ j)
    ((h _ le_rfl).le.trans hj)
  rw [eval, evalUsing, hi, offset, min_eq_right hj, ← width_eq h le_rfl]
  exact BethCubicOrder.right ..

private theorem offset_le_width {m : Mesh} (h : m.Starts) {i : ℕ} (hi : i ≤ m.last) (j : ℕ) :
    m.offset i j ≤ (m.width i : ℕ) := by
  rw [width_eq h hi]
  exact Nat.sub_le_sub_right (min_le_right ..) _

theorem monotone_signed {m : Mesh} {s : ℤ} (h : m.Starts) (hc : m.Controls s) :
    Monotone (fun j ↦ (s : ℝ) * m.eval j) := by
  intro a b hab
  let i := m.index a
  let k := m.index b
  have hi : i ≤ m.last := Nat.findGreatest_le _
  have hk : k ≤ m.last := Nat.findGreatest_le _
  have hik : i ≤ k := Nat.findGreatest_mono_left
    (P := fun n ↦ (m.row n).start ≤ a) (Q := fun n ↦ (m.row n).start ≤ b)
    (fun _ hn ↦ hn.trans hab) _
  have loc (t : ℕ) (ht : t ≤ m.last) {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ (m.width t : ℕ)) :
      (s : ℝ) * (m.piece t).eval x ≤ s * (m.piece t).eval y := by
    obtain ⟨h1,h2,h3⟩ := hc t ht
    exact BethCubicOrder.monotone_signed _ _ _ _ _ _ _ h1 h2 h3 (Nat.cast_nonneg _)
      (by exact_mod_cast hxy) (by exact_mod_cast hy)
  change (s : ℝ) * (m.piece i).eval (m.offset i a) ≤ s * (m.piece k).eval (m.offset k b)
  rcases lt_or_eq_of_le hik with hlt | heq
  · have bound := loc i hi (offset_le_width h hi a) le_rfl
    have bound' := loc k hk (Nat.zero_le (m.offset k b)) (offset_le_width h hk b)
    have ri : (m.piece i).eval (m.width i : ℕ) = ((m.row (i+1)).y : ℝ)/(m.scale : ℕ) :=
      BethCubicOrder.right ..
    have lk : (m.piece k).eval 0 = ((m.row k).y : ℝ)/(m.scale : ℕ) :=
      BethCubicOrder.left ..
    rw [ri] at bound
    rw [Nat.cast_zero, lk] at bound'
    apply bound.trans (le_trans ?_ bound')
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have hy := chain (f := fun q ↦ s * (m.row q).y)
      (fun q hq ↦ (hc q hq).1.trans ((hc q hq).2.1.trans (hc q hq).2.2)) hlt (by omega)
    exact_mod_cast hy
  · rw [heq]
    exact loc k hk (Nat.sub_le_sub_right (min_le_min_right _ hab) _) (offset_le_width h hk b)

theorem monotone_eval {m : Mesh} (h : m.Starts) (hc : m.Controls 1) : Monotone m.eval := by
  simpa using monotone_signed h hc

theorem antitone_eval {m : Mesh} (h : m.Starts) (hc : m.Controls (-1)) : Antitone m.eval := by
  intro a b hab
  simpa using monotone_signed h hc hab

end Mesh
end BethNumericMesh

end

section

/- The tabulated cubic segments are close to a cubic on each block.
Store their exact integer differences from that prediction. Every lookup
reads four bit fields in its block and performs integer arithmetic. -/

namespace BethNumericPacking

open BethNumericMesh

structure Lane where
  bits : ℕ
  data : ℕ

def Lane.read (s : Lane) (i : ℕ) : ℕ :=
  (s.data >>> (i*s.bits)) % (1 <<< s.bits)

private def signed (z : ℕ) : ℤ :=
  if z%2 = 0 then (z/2 : ℕ) else -(((z/2+1 : ℕ) : ℤ))

/-- Each block has its own cubic predictor. The last three lanes store the
exact residuals in the left value and first two control-point differences. -/
def cubicRow (count span start : ℕ) (v p q r : ℤ)
    (offsets values slopes bends : Lane) (i : ℕ) : Knot :=
  let u := offsets.read i
  let h : ℤ := (if i+1=count then span else offsets.read (i+1)) - (u : ℤ)
  let w : ℤ := span
  let x : ℤ := u
  let a := 3*p*w^2
  let b := 3*(q-p)*w
  let c := r-2*q+p
  let den := w^3
  let y := v + x*(a+x*(b+x*c))/den + signed (values.read i)
  let d := h*(a+2*b*x+3*c*x*x)/(3*den) + signed (slopes.read i)
  let e := h*h*(b+3*c*x)/(3*den) + signed (bends.read i)
  ⟨start+u,y,y+d,y+2*d+e⟩

/-- For a suffix sum only its endpoint value and the source segment index
are needed. The interior is constructed by exact discrete integration. -/
def suffixRow (first span start : ℕ) (v p q r : ℤ) (offsets values source : Lane) (i : ℕ) : Knot :=
  let u := offsets.read i
  let x : ℤ := u
  let w : ℤ := span
  let a := 3*p*w^2
  let b := 3*(q-p)*w
  let c := r-2*q+p
  let y := v + x*(a+x*(b+x*c))/w^3 + signed (values.read i)
  ⟨start+u, y, ((first+i : ℕ) : ℤ) + signed (source.read i), 0⟩

end BethNumericPacking

end

section

/- Exact control points for the six functions in the sieve certificate. -/

namespace BethNumericData

open BethNumericMesh BethNumericPacking

private def fRow (i : ℕ) : Knot :=
  if i < 360 then
    if i < 172 then
      if i < 84 then
        if i < 4 then
          cubicRow 4 24576 0 0 0 35257244078277 70514488156584 ⟨15,0x9000c000c000000⟩ ⟨4,0x6820⟩ ⟨3,2144⟩ ⟨4,0xba02⟩ i
        else
          if i < 36 then
            cubicRow 32 46080 24576 105771732234861 132214665293580 266024738886127 168378965543070 ⟨16,0xae00a800a2009c00960090008a0084007e00780072006c00660060005a0054004e00480042003c00360030002a00240021001e001b001800150012000c000000⟩ ⟨43,0x3e1cba69481c58ce60b6073edf90b51174fc5f8e9a41a25d3b2a0a9982cb03819ca33a77d53c05abead5886f2fd4228526e44a750c274b4d86cd951edcd4a0dca748dc0da1d4eabacbac2a8fe81fa2b94ea280e92c6935ffc68d490d1f2981971dcd6e516a632e9e60bb74530d03584247f52224acf0b25c7bd3680d789548842130b726961c17ffad0719817fda9ac1a009f60728040209eb407a2077c8df74140ea36ec6c280000000000⟩ ⟨38,0x4f1c8f05562423d1457afd92eb147175f01299cd81df2e9f26352fcc5bcef0d0766a9715a7bb92d5bbc555dc715480557f5663aacd8c5fd26b12ad7685dc46b1e81b435e372f31163ba118dc79b31281725c0c04964af9a9c85d30878ca0b0cd174d47733bc5f1182c5f693dc62c12916dc05006519ad917c0823c039bc206618ad1078afa1a607852682a9119ad211bef1b254000000000⟩ ⟨37,0x43ff5270717e4a546807716db7c01c4924a20011b457fb048d441a0c40e7e8c522a7fe535319d30cb338ed30b2ccc82b9cb18245c0c5ddd242f1a99692464f9e948fa686896446aa281b1f5d27fe08da6566b9c57b4ad4a61e4abaa0506d903f23818bca3f783b40ac47c38f284274090ff7f97058daa4268352e6f6ec1f4634fb41222491ad06dfe850305c3f5ed9146764b453⟩ (i-4)
          else
            cubicRow 48 75264 70656 672390101957638 275019891214439 30947286510939 13100432191196 ⟨17,0x90004680228010e00840040801f800f60078003a801c800de006c00348019800c60060002e8016800ae00540028801380096004800228010800780039001b000cc0060002d00150009c00480021000f0006c0030001500090003c0018000900030000c000000⟩ ⟨43,0xab0c48caa04e4044d6ec1406543640840613056950b49fba85ba1cf2f00d984457d3288cf89e3558e8b315817253f062cd0adbabe4596c17e1368aa020e09491305f55837e1f427ed8cd42c39c577ea82a88070c91018c964c26012f206dcdc0497198c3700e0c525a1de2689cea2400630d1bcedc8f3829a6eb72432c3ea95e53deef592b8be2744bc4e9a720f76fda3e5f3b1fc5284875b8c1e115c26486b323e585dfa15493ac6582cc935655ed41524312a8333a3aa0b5d20f447fb5145ee8129e46e914ee8d2fc6ce9ae252268e72f1df4b20f64fc01f5a0048121cb78690c511565c511146ca88258153ef2c8294149864b0d500b343ecd3000000000000⟩ ⟨38,0xda33294c05ec5a9ce41e6500753087eec9f4022b589f588835317fac1c9dbf4790595b123f80e47eea74812ebaa4f6060547af6c46b28eb491dee7e422ca9f7d4db9370e73805d0d51364454f0579aefd67699c017638ecd4185af89000a57298b9cf15ddecd6a4d7a5859dc1dec14d9a1d795e1985d5d51df44cb6eaf1039e6cf1f3ca734bc7488874ed51abbdd28bc607e1c5108f576901c1c4e8b8637e46af2308c0d4a6920782b2025ecf745461cf27c2f8486288bbed253db309dc9f2f6c5be28eebbf70ca16e11db425c201ead4833090e8a991d7390883949d682f8000000000⟩ ⟨36,0x17937040310a1818f70a28b9c7f042dc2eeb014adea74063cd825a0aa415cf20e7cd2b8811c3ab1321475b14b6169086814181276f1818fa9ad401948fca4818fec5812181e70f1616ac093b014ad623a61229be51e0f295bd480bb599b5407d91a026039fe6cd200e8644cd05b06b5810aa6dd1dd0fb83749f6761463251ea4203d123281a4352739dc4e32ab1a6c972d62a80572f1a4a10f2f9dddd692eb173e372c218f58927d6a865521b2f83eb19963f2130f5d8cf1302e2f84170c02b466c1d80587de31c6e87ea490be85666389f7e52818174de8⟩ (i-36)
      else
        if i < 140 then
          if i < 108 then
            cubicRow 24 34944 145920 991457711874212 6082294096606 901107068892 700036637937 ⟨16,0x870084007e00780072006c00660060005a0054004e00480042003c00360030002a0024001e00180012000c0006000000⟩ ⟨38,0x68839edc0e235c0c511c034628ca10365be94465c854bd8ee957ca583fdf7a9ce8ca1308f3bf6d60b24f5d08d2ca9e9617c2be7d3428a5cdf8e50e6c27d52696849ea0492c64f5df5271cfbe82ca974e81487c8897e9d10bced6e443ff2339de483aa472fb5885507fe1657dc000000000⟩ ⟨34,0x45036bf0618e34206456d313225460b52a0af256e2aded93e8aad6d0fca7fe075608c2d69849c3763aa24f8973a28a73594e40162705e89f810f0d50041f2bdd3c725af946fe592eb0877c2fb986cde5ee7e1e98faaaa8934622a76e3350dc2f86c00000000⟩ ⟨32,0x860ce3b1d894527580c1ca73bcfe4292196ad910989086f0c2e05f81f60f2362fdf9a4e3d7739c847f25f124f18e4c652afefde5279f2f04e36b85245a3740c387adfc2267562c00f49477e0d54fce32fb26f67581d1b1586e385f1bc543e3d⟩ (i-84)
          else
            cubicRow 32 8832 180864 999141149677647 176932336992 125736634938 97050138117 ⟨13,0xfc066032fb97acba65a32a1920c606002d013806c035f5af4d746b43541a40cc06002a00f001800be85e82e81680a80480180000⟩ ⟨29,0x112c4c6b3a711e59e21aa6cf6f5a168160dfb469203da921922da5724372ccc9abeba701640b550353994f1a22f7f7d113160e88406d743c758da1899a2d06857f67d307c737f5c29944e9fac0c22bb54f4d4760aa8c7b04f3cee8270814c12ef21a08e5a1103e6ea981740154054ea420000000⟩ ⟨26,0x53ff24b9a8a6a009b58001f7dc00fb6e007d37603e1af81e8b460ec01f06d3eb82d09508b46f7e8e97d04006401003afac01dc1500f252407d615042cf04255215162bf64dc9ac77fa1125d556a7010161c00c7d900629cc02ffad016a2ec09e9810371ca4000000⟩ ⟨26,0x1e9be44ef2d02008396400004200003f00003f600040a80041ae0043dc804846e0511a2062c0f4860ea30025e1f000026000021e000222000217a002067801e400019eea8114c4400076122827d103a3c400000a90000a84000aad000af7c00b87300ca77c0ee6cb⟩ (i-108)
        else
          if i < 148 then
            cubicRow 8 765 189696 999540868787694 8406177043 8184014098 7973527935 ⟨10,0xbeaf4ba2d0a824060000⟩ ⟨6,0x862948b6c00⟩ ⟨4,0x113e2⟩ ⟨6,0x810c20c24e2⟩ (i-140)
          else
            cubicRow 24 7683 190461 999565432506770 80112351748 59072258702 46677670745 ⟨13,0xc01e002ffb7f7bf5df4ef47743b41d40e406c036002ff57eebeb5e9ae8d686a83481980c006000⟩ ⟨28,0x381f6d3385b2273888ec538e476b399b6473b089dd3de05c14383a074e8e17963593e384fc51b9214c819218e17920c98591f3ad391c074f915488390671a58e38cbb88a5627795b55b4ffa04f00000a70000000⟩ ⟨25,0xda6ec8004f9a801e86001e81601e78a01e66281e3e541de1bc1cf5671a503191d35f4befdd5000ac7001074c010c4601160f012979814f79c19832621c7d72f0837bc651ae28f6f2000000⟩ ⟨25,0xc1ddc00536e400000c00002600004500009980014f40032800087370196d0854f371324d1e00c31380001400002880004e00009a20012b7802343803dc480587e5024d2b1e6ffaa01c6db⟩ (i-148)
    else
      if i < 248 then
        if i < 212 then
          if i < 204 then
            cubicRow 32 7680 198144 999751294787965 46659444410 34052003424 26913456640 ⟨13,0xefef7ebbe9de8ee87683a81c80d8060024011fd8fd47d23d11d08d04502100f006001800bfa5fa2fa17a0ba05a02a01200600000⟩ ⟨25,0x12fc10150f68160aa0166b4616620715eb8714d18ad29b380e7deb17ad16f037489a1d85010f626b8850c344c7326300f1921adf49a1f03d59a40f1db12bcf902fc5f8cfe302f0f178de98b3c7cc5121761f99ef06736d79323eb194354d43f6a000000⟩ ⟨24,0xca1900f65d01e98503c6390759710de9c118c5c7260cc323dee52b2936b1d16200a028006a8c00d46a01a6360341f20659fa0c0c121575f4204f02158816865953001156002df5005cb100bc5501841f0332ab06f3ef0f4a8d1d6149000000⟩ ⟨23,0x1968e0001ac000d18006670032d2018e4c0bf9485820d246502a873c667a7300f07b000020000150000a800053e0029fc0150280a8fb0555362b821969959808df180001a0000d00005d8002c6001416007c9801a58816cb4af5d11⟩ (i-172)
          else
            cubicRow 8 3060 205824 999858919692439 10689010254 9501193087 8543762505 ⟨12,0xbe8bd0ba0b40a80900600000⟩ ⟨6,0x1062948b2c00⟩ ⟨4,0x42211182⟩ ⟨6,0x1411440400e6⟩ (i-204)
        else
          if i < 224 then
            cubicRow 12 3078 208884 999887653658285 8594020188 7621655767 6844857426 ⟨12,0xc00bf4bdcbacb4ca8c90c60c00c009006000⟩ ⟨21,0x1580056400dfe01f1d03fc887a6f4d4b3f1cfa5039730002e8000a400000⟩ ⟨21,0xe0002580053400ad6015290267483b8742f86cc109c8098180003c00000⟩ ⟨21,0x28000b40015a002c7004e680784c0606a180c6c078c02a964000100001c⟩ (i-212)
          else
            cubicRow 24 6150 211962 999910714191666 13676374100 10558990550 8659530050 ⟨13,0xc01e002ff57eebeb5e9ae8d686a83481980cc036002fe97dcbd65d32d1950c9063030018006000⟩ ⟨25,0x93b200a3df00ab9200aea3a0ae9ed0ab89e0a3fc6094b79678394a48c302109c5348422c841d92f20b48690227a87da0403b6e641a78d48a437002ae1b00277418017d0000001c000000⟩ ⟨22,0x18914077d703b93c1d7210e60e46d9933185dd3c9e75876a462e1aea1f5803fea0095c804aa60251101248a08e508433fc1dcfe8b499226938941407007ef000000⟩ ⟨21,0x31698000b40016a002b70057680ac2414b322629f3f5e5cae91f97b30076cb000030000680010400202003ef007be80efe81beb82f9ac3e424011d2600002⟩ (i-224)
      else
        if i < 288 then
          if i < 256 then
            cubicRow 8 3060 218112 999943609086366 4292017690 3798195484 3403823385 ⟨12,0xbe8bd0ba0b40a80900600000⟩ ⟨9,0x40687072654ca2800⟩ ⟨6,0x32d34d1a82⟩ ⟨8,0x3010a080f0b09ba⟩ (i-248)
          else
            cubicRow 32 12252 221172 999955103122925 13628638804 7564139862 5294813089 ⟨14,0xbeb2f4cba32d0ca83240c603180960198005fd17dc5eb174c5a3150c4830c0c3024c063000bf42f70bac2d30a8c243060c00300090018000⟩ ⟨27,0x92a200a33cc06cb6383baa091cef2eebec41aefe60ecdf4cd77be9e3cf7d4e5e6fae1a5df6c1c1bf0d4d77e9b7defcac36de38e9fae03dbee7b11bdceeb83b9cbc857350dbae5863f5c69997b7b41196ada086c3098753980f294c08f3000615c0000ce40000b68000000⟩ ⟨24,0x30c6011fde0513de144d7247dc74c213ec07c58102a6dd000c12001790002cc4005022007ae600624e017a430b7717352fcfc5230d004f2d005e3300bcaf017a8102f97506039b0c425319349733430b5ac06f0cffb1001170000079000000⟩ ⟨25,0xc1a801765c02bb4a04af4f06422980126ef1a29300c260000000e00001300002640004b000094f00124900234c40418f806ef0508d2d5000867a00000e0000110000228000458000810000d810010ef80069e60af1e73e5cab8014704000032000075⟩ (i-256)
        else
          if i < 336 then
            cubicRow 48 24576 233424 999981590714680 10620740608 1907064624 1512232448 ⟨15,0xbfa17dc2f585d30b46150c2418482d9055209240c48008fa11dc235845308460f0c1818302d6054c09180c30005fa0bdc17582d30546090c0c18182d30546090c0c18002fa05dc0b581530246030c0018002d0054009000c0000⟩ ⟨29,0x2e0d800ce134022a74e04daf5f09de1dc924e9d05cc925b2e6813cb7355b0eb9bfe9fdcf50472e8f8d6d75cc941bc355255f67439b0faac559b6700aded2d43f8d354ebc6b6f7be35ee05f1b2ce8f8dcb96fc719675e3bd43af20920af9230627c984c5de252ccbe9670dd63e1f8bf1f0711d8f6ebdcc7a28ffe3bc719b1c9538d8cfa758c5298fde13a9c6af383f47629c1049a9bf05c005598800060c50002a2a8000f81400037360000000⟩ ⟨26,0xf548016cc601a21681afee419d379960973adbbcf50012afa003831001c16a00e09600702c8037f7181bdaca0dc96c86ba4c2325dcf941e6f21c6f0000096ea000907000478a0023160010dd6007c18003349400efee802ec530b6dd44ec6691ea25884002e79003776401bc1b00de79c06fa5903839841c7e9b0e977dc7909333e66ad5c3f0d117e846c0104aa0000ff40006db00024bc000000⟩ ⟨26,0x7a0c0077ff0073b6c06b2c105a14c437e6ab0c75610014dcd000001000000e00000f80000f80000fe80010f200130e80175aa01fef0031189a536be300203cd0000058000056000056000056600056800055d2005493005228e04d520843a5b4304c9580314a70000048000036000037000033c0003288002f480028dd801bf6e0022a60316edd98a13d404a85d000009c0000950000914000937⟩ (i-288)
          else
            cubicRow 24 12288 258000 999995630752360 756116480 407242730 292044544 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨23,0xa6600b9b407bc6843fe521092edae97785d20f11b93e244ebc4c05f8a568f17e19e3b81fc9d84f99358f29b97d5be5724972c045dd00028100046200067c0005d800000⟩ ⟨20,0x3760147c05c8e17286523a4e08ce15034020740024800482008cc0109c01d6c02be801e7c095673db87db52fd3c4b02f6e00019000290003d00000⟩ ⟨21,0xd9801a9c031da055c5073cc808c6769bcc0879b000060000480003c00082000f5001d78037ac062cc092bd05a07a79d020d5e30000000000c000120003f⟩ (i-336)
  else
    if i < 560 then
      if i < 456 then
        if i < 408 then
          if i < 384 then
            cubicRow 24 12288 270288 999997086156114 292044288 165211732 124419840 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨22,0x7cc011890176a419bd919056d4bbbdab1226aea93abb4d6af26fabf2b6b1055acd18eb6f9daed0b6b8265a260edbd27300df30000e50003240009300010400000⟩ ⟨19,0x2a801f00118508c503e4b15474844d400cae001c8006f801b00066001698043b00608037b52ea4b4cb5e8b0a812e40000e00034000880000⟩ ⟨20,0xad00281009710207d057c500deba51dc035110000300001000080002c000bc002d200aa20257e06f9808a347785d0553300000000030000900017⟩ (i-360)
          else
            cubicRow 24 12288 282576 999997667831974 124419072 79161063 64717056 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨21,0x5b8019d4044da09743125fc9e73cdf717efc7237e40ebf2835f9bb2fd5257f143bfe23e0248b000ed7781fa8ff6c02b10000450001d8000a40001e00000⟩ ⟨17,0x3e00b7019c033825b7a7d0c86b9404ce0028002900284025e0218019380938142f445afa487c75a074400008000c000a0000⟩ ⟨18,0xe400ef00ddc0be7080d4054ff1f80141b00030000600008001200130010a00f880dd60a4883350aeeec20bd000000003000000001⟩ (i-384)
        else
          if i < 432 then
            cubicRow 24 12288 294864 999997936129165 64717312 48613421 43284992 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨19,0x76008f40613835b71a2b6adc0ecf1cda377b47a769216d2f1da887b5abf6d566df61db901ab0c6eb1e403f6000210003a00054000480000⟩ ⟨16,0x2e00fe049812584140b29614c001c20024003e007400de0188024a01b6070d309baea3af8902b40004000000000000⟩ ⟨17,0xe8012c028e044105c3807e6b118075b00058000000080002000b0018802d804ea076104a69effe0c2300058000400020000⟩ (i-408)
          else
            cubicRow 24 12288 307152 999998092744890 43284480 37357805 35131904 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨17,0xa80334088612b92462bc50fe65ff50ffa97fd5b7ebcff6d1fc3ffed1ffd1ffc93ed84d19b405ec000100000000800040000⟩ ⟨14,0x4005a066065e5a93df61d380a0003801400a004e02280cc02782714377ca9f3cc10200000000004000⟩ ⟨15,0xa0064034817107ea02bfbb7029f000a001000200020010009003901bc0a401a0ab138479000400040030004⟩ (i-432)
      else
        if i < 504 then
          if i < 480 then
            cubicRow 24 12288 319440 999998208519079 35130880 32698081 31529984 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨16,0xb00530191068f18e951a1a773a815a81fa835a85ba8a9a937aa1fab29aa599ebd6c3b0118001400120010000a0000⟩ ⟨13,0x500901282323d553303ec034000002801401a01701100600df2e3d1f6626054001000800c000⟩ ⟨14,0xc00b00ac07f054c02ba1700d700200030030002001000c009809a06f0214788c1790008004001c00a⟩ (i-456)
          else
            cubicRow 24 65592 331728 999998307878024 168303606 140610998 130768584 ⟨17,0x80103ffc1fe60fc307818360c18060a83048181e0c0c06048301818060c02ee016b00a98048c01860003000150009000300000⟩ ⟨21,0x3800094002f60132308643966d4d850cb300e3c4b19ee45e75e993656d5725bf9469449b0f24974f20bec8c99fc3170a000520000680001c0000200000⟩ ⟨18,0x100010002b8091a1fac9f30c94bba27185f8a86f3a37e462eebc481ecc170573c15910a7344d051d6f40abb000780000000000000⟩ ⟨16,0x4000000410323284954d90bcf375871d69df0b1fa9dde44c88b8f005d002700b103af156f8ae1008b000400030002⟩ (i-480)
        else
          if i < 528 then
            cubicRow 24 480 397320 999998747561212 957040 22453091 12970820 ⟨9,0xe466270783b9d8ea723618090301509c4c25120602e160a8481800⟩ ⟨23,0x4024c3fa791fbcd44eb680866e9d0b897a140a641182c7a4bf4c686d098c4b081de5190dc238cdfc74d458dd10b1a16da13f0642351b840b230760460adf2409b91800000⟩ ⟨22,0x5301465d1341d5eeaee9002783c09d1f0270b408944062d9047a542a0d786bd8e04f6f007e70010f3c042830104dc24fa100bfc402e9500b4dc04c97019c4c00000⟩ ⟨23,0x12dd005a5f00f54dc42efd1ab4ac08b50011b4800106f006e26021c8c046e3033804007c48004390099e40000a300014a01858c00055802e0c005c180018cc00ca38068fb⟩ (i-504)
          else
            cubicRow 32 13800 397800 999998783942163 372911650 209783737 148719437 ⟨14,0xd6e3558d263318c062a187861e157849e0c7801de876e1d587261b1860612181860615184860c18005e816e0558126031800600120030000⟩ ⟨22,0x6a400efd0141041623715aee525393a5ab86981a1a6150698c75a66ae69b6a9a7b0c6a4e03abb5a6ba17dac426e399031f178c786e71e0214773cd1d69b4727ff1b119c602b5125f542392f0003640005100008c00000⟩ ⟨20,0x11e006a401e180791a1b39e4d9c42e4ae007960013a00262004b60092e0115401e9402d3a01e680970b399b59c49b014fb0021d0043b0086f010bd020e703f47072ff0abbb00e0f000290000d00000⟩ ⟨19,0x116008ac041681c5d09fd20cb8fcd3a01ca90000e00038000a00028001180081003eb01cd00c0e03a7d08b3a854ee000000001000018000f0008e0054403238211d18976001a8000100007⟩ (i-528)
    else
      if i < 664 then
        if i < 608 then
          if i < 584 then
            cubicRow 24 12288 411600 999999515356987 132424704 80217426 58372096 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨20,0x950051701af9076411caf55ee1fc2475c2d9dc2e53c2fbbc327dc37c9c416dc5115c6247c4fdbb74a97cc9900c600004b000410002f0001500000⟩ ⟨17,0x32009081420283c4754611e030cc030c0020001d801d801b60183011c8055c112f3607de9e6b5fa043a00008001400060000⟩ ⟨18,0xb400c300abc094b064240309bf2b00ca1000000008000000016000b800c000c080a9407d4025108b814130d000100004000040005⟩ (i-560)
          else
            cubicRow 24 12288 423888 999999786371213 58372096 35359889 25730048 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨19,0x860091c05fc8344919522a75c6ad04d5e0fabcc357bfeb01ad6289acd8f5b6aeba9cd6d09a189adbe4c02bc0001b0003200044000280000⟩ ⟨16,0x2c00fe047611c03eecab300a960156001e0038006400c0015201f2013207972fa7a6d9988d01de0004000200050000⟩ ⟨17,0x7801340262041305888051ea21c058d0000800040014000c000e00168029004ac06e504161ec7e086100048001c00140001⟩ (i-584)
        else
          if i < 632 then
            cubicRow 24 12288 436176 999999905833246 25730048 15586793 11341568 ⟨14,0xbf42f70bac2d30a8c243060c182d60a982460618005f417705ac153048c0c3000c002d00a80240060000⟩ ⟨18,0x8401090156c17351662d276196f7e5da79772e5e1197a665f9f985f6648199f4664258e5ad835f009b800070001c0003000000000⟩ ⟨15,0x2c01d00fd07da377d2dd0244009800180060016005601340368042035b2a0f262e17b80d2000800100010000⟩ ⟨16,0x30021008301cb04d3008f949202730002000000020004000600280094020e061207286cb703af0001000700010000⟩ (i-608)
          else
            cubicRow 32 17712 448464 999999958491655 16347438 7399543 5016255 ⟨15,0x8460f0c1818302d6054c09180c30005fa0bdc17582d30546090c0c18182d30546090c0c18002fa05dc0b581530246030c0018002d0054009000c0000⟩ ⟨18,0x5ad4b017a268e8a97a2c2e8bf7a372e9173a62c6a6f1b0a16f5d1d317fb3c7d0087408fd01173fafcfa073c1dcdcff2d1bc5d5ee6619cd256c9d004380007000140001000080000⟩ ⟨16,0xea444ce906a00520028004e00a00138026804b208fc103c192811f0768d00260013002f005f00c7019f0379078f116b294f57e11f3d005a0004000100000000⟩ ⟨15,0xd1635b578f00b90004000800380020010004001d00e60794450aace01130006000c001800500060080023010c04bc1107fb38199000600180008004⟩ (i-632)
      else
        if i < 760 then
          if i < 696 then
            cubicRow 32 13053 466176 999999987254891 3696752 2160814 1548956 ⟨14,0xcbeb2f4cba32d0ca83240c603000b4027006c01afd6be9af46ba1ad06a81a4066018005400f000c002fd0be82f40ba02d00a802400600000⟩ ⟨15,0x40004002800f005201d40b184831deeb7d6ef3de23bc4f78cef26de79bd977d7700ee02db6a30bfc19d838907020ddc1af832f05aa08a40828000⟩ ⟨13,0x400400000500880c814e2232d1050c018000000801801000c00b805804714da93e0ba01c000800001200f00d80cc096002⟩ ⟨13,0x1002000400e000802c02203b05680268c40550050028002004004000803004c07606294b60790010014018006000800c03205f⟩ (i-664)
          else
            cubicRow 64 36867 479229 999999994661413 4460907 (-122320) 0 ⟨15,0xf007b00f5a1ea83d207980f181e183c187818f025e048c08b80ff019e003c00580070005ffdbfef7faefe9dfa3be877a0ee81da03a807200e3fbc7eb8fa71e8e3a1c6838a07080de01b0035ffabfdd7f5afd35f46bd0d741ad035406900cc0198002ffa5fdcbf597d32f465d0cb4195032406300c0018000⟩ ⟨18,0x16a218b1e6a0d1c59e7fcd2678ead9a2d020b6352dc0eb72fadd36b782adfb4b8c2af072bc2eaf078bc0daef6cbb77aeac0b9212d818afd5a8e3a8b6c973a6077d2017980cfe04f98219e0f3f87306371d9a4e6c2efd31dfb87fee23fb891ee247b891ee207b83dedc3fb227e7acf54c79482651d59461e50ed93ede4d4b921c63ea78ab5602516bbbd07c7000000000⟩ ⟨16,0x7511979b09e509c112c51f47148d06c5026700ef003300450045008d011b047b00150015001500480084010a02140424083a10481fcc3c6c6ab6928c009c009801280246047408a6101e1b92248e010300060000000200040003001d0087022d088b1fbb6957000d001b002d006500c9019b034506a90dab1c1b36193a810000⟩ ⟨16,0x8f9e392e0036000900830437067701e3007f0021000b000e00020002000200060002008c008c0003000a000200020002000800160064019a077c24f40013000300030000001600220098025c094c25000011000000040009000200060026008e020606aa0f6a0029000a0003000400090005000600140028003402b9268b003b⟩ (i-696)
        else
          if i < 776 then
            cubicRow 16 83904 516096 999999999000000 0 0 0 ⟨17,0xa380510027001200084003c001b000c000540024000f000600024000c00030000000⟩ ⟨0,0⟩ ⟨0,0⟩ ⟨0,0⟩ (i-760)
          else
            ⟨600000,999999999000000,0,0⟩

def f : Mesh := ⟨777, fRow, 1000000000000000⟩

private def lRow (i : ℕ) : Knot :=
  if i < 188 then
    if i < 44 then
      if i < 16 then
        cubicRow 16 8448 0 1010010000000000 (-11263202816162) 2442491009089 (-493937712180) ⟨13,0xf006c030015009003c01b00c005402400f006002400c00300000⟩ ⟨41,0x11f7b0d5751ee8e113aa1d45f1502b154e338abe4d220ea7914715cd1c41838141d648f5ac748f665ec48636e16255de415e7f233ee848124d43a5dc50045e51e9b20121f295fff82a23a3e3bc0000000000⟩ ⟨38,0x5909582bf6296e29f63966cf96ea6031f293614e84b32aec1c51e5fcf109b1f656894bef384839061b75d92ade1b07a5886310051811574afa5f3a3da5b947cc30dc83410f17798000000000⟩ ⟨36,0x8954a6b163be72df7e0bb270da74af899d857e30fa0c39fb5f4c27294c69d21291157f452655ddfa7208090abb16ce9d96108474da410c54a7c0a28a1858424eb6dbf268150dda38⟩ i
      else
        if i < 40 then
          cubicRow 24 55550 8448 1000695350480747 (-3246821097196) 2561939268991 0 ⟨16,0xd8fdd8fcd8f0d8c0d800d500cf00b7009f0087006f0057004b003f003300270021001b0015000f000900060003000000⟩ ⟨41,0x94c70000009e83000003c38e00001675cae000a133fc6004d1cb93f80e832b7d4049108135505ae21371b14b785344dab244f3372adc3fe50bec8e075f67aaa69bad3ca512e757c3887d268f1862727b876ce36930b5f5f92a917adbd2f045560e3a04e1295a9f2c8048ff2b45880a1c5b63500000000000⟩ ⟨38,0x33dc0000019ef00003370bc000a8015b00276f8ffc097e29c3d0b47db9c35ed64e6b9b9f859da89e674af0a596abbe58c8c4ec1b140712c32bbbb0cc858d04c55c14713b1dd750405642ccd8ed29202e7c49a49f29d2bd9187189eee386f69f94857820680e0cca5d3030000000002⟩ ⟨36,0x10f99000010f9f00003a5dc0003a333a00398aaa0036e8636c0c69033ae7259696ac1e59976823520acccb872baf481d4c93eb193d76604ff43faccf7d4670360233fc638edd0cf116e33080b093bd006f020760eecd814e27d1f4ba60efed11fc1553ea6861dcdf451e⟩ (i-16)
        else
          cubicRow 4 34 63998 1000010468652542 0 (-1731607621884) (-889355536587) ⟨4,0xa410⟩ ⟨40,0xa3dcea92435b5dd6dd630aedb92ff10000000000⟩ ⟨38,0x7d1a754a66ab522b4b1822f12d8ac000000000⟩ ⟨40,0xe26a25377a14bcd90a320601fd19420c4b0d228d⟩ (i-40)
    else
      if i < 76 then
        cubicRow 32 21984 64032 997389505494071 (-575046824054638) (-144444790041416) (-110132740041063) ⟨15,0xa5c13f8267049e08dc10f820703de075c0df81a7031e05dc0af8147025e045c07f80e7019e02dc04f808700de015c01f8033004e006c007800300000⟩ ⟨45,0x2a34ae117204f742de3c2853e8a3b8f3c45d02e365b432e44d064f12212cfddf39957ba2954b9ccf1c196a08078609cbd8a543e895d041fa55690443335410e5c847d4a8f55aceb4c572ad6e14132c1b85510b495e3662bf338aa522d95cd4511166ca669a5ae6b39107110c56cca718778bd9ca75d326402f7ddb94349bf48e2479245dcc18e291e38a12b40be0e32bf8f0414d6a340441402635e5ac0505a5d00e900cfabc6d0c0004585293e000000000000⟩ ⟨40,0x369ae826e16361dd106386b4343fd7a0f9eca863b2a2a317a7bc2631a47dbe055d2cf1b8ca922565ad0ab218679b65f34cf38488d42717692d23eecb4a1b22c3af282aba98930444d4059d209afdad06456453fd1268efe2c7ba89fd4205f4a7307ad200bf0f4f0520cffe32d9dcd83ceed176d5e2dec57cc6dac181e6a8de0a804249bcdfd3043cb4fb3ac22d28388c221ae7eea2f405c343df2e0000000000⟩ ⟨37,0xc663a15724fe40ad541eaf769f40aec46a32e35d4cd8960b1bf231f01d3dca0a24532207c73b797530ca8e0beb4bd94f839f46eb6f7cf9f82f2739e6c6567e2ad64a8251be728fd22c5791ef60f7bc5499dd9c5f80443f32d78b03e1d5361bbc629a2516d80c379454dd240ee493565785c3efe4c0ae81c70bd005560871f16b96443673daa1274a530a216a27e1fa80bb760842⟩ (i-44)
      else
        if i < 140 then
          cubicRow 64 27264 86016 167765151356954 (-136583353074792) (-15822106574615) (-8490963508359) ⟨15,0xd2019e033006480c60186030005e80ba016e02d005880ae015602a005280a2013e027004c809601260240046808a010e0210040807e00f601e003a807200de01b0034806600c6018002e805a00ae0150028804e0096012602490490891e1230240042007800d8018002a0048007800c00120018001800000⟩ ⟨40,0x1edb9b9da075ee385ce0fd256d7a41acb0717e627d02df320366d799c6646333d1a8e56b6a2b8966791e0b2f27864703cf288d346fa6c9889130bdea73679cbe4b492595facc05a0d3c4cca51b5c61cd244832fe2d80503c266db6d75b6b8dc601ccfaedac79be19ed697527998cfcbbed83cc66ae4768eba84b74f00ac338c27249b9c8e1a8e88f039aab6746add9b0c5e5521e4e847049512922edc405588164d42b06602288c6df119f5f2bb45307ba066c7450974c33556ddb9d25f65245636876ef5f507b1735723032b71376083d1677027a8b754c3e6077137dce93d2b0f4c3da7a709d59821b010a8013a741264b30c68142026709017918af37c250dcfd03880b4ad0084c089d2c1c6e6680efae8f4b12399ceee56b41ed2d6e3ddcf3eb287894a6a861f84fa345744793d7e2c56c8b2ea0c8c70b7640000000000⟩ ⟨37,0xa0e0b9c7895f4728ec68703b6fe40636eaf7250b2a9a5945a44c1acace9e237e59544b5032d114e4a9963f22f074abfff1ed6514c0ba5d2580a0a4690d05f325474602d49a2ff1eddfd1256bcdf98622b7196c1767ecb0a01ab850ac07b2fd0c00752f392c05656a153438d0a0f222302cacb614a46817b0bc73636d068c01a7ee38f2362f61e58d61c78fded1892882548d1ca4198488ac204e95a6a8f83bf30a47383c60e0338804b431598b7f69882300067826c6847a8038057d0f07ab13f51495714125a7da2029975bf60b93ebe882b225d1e60ef2c224f8fa0ed049ff9db5824e0affbc24925e15e46b3f37dbce96cdd12c3532caf5d11608ea9e123f541a52976e926e28e2729989b81c42184f8b6f69007abf22ec43385b14610fbccad5b0000000002⟩ ⟨35,0x12b925a9420105d09035b45545057463254087c381300c50d85c80fb9be0100e7ad74c0033ac47e0432e74d40f82ec2f82c419ffd070e80f4e10e46936c26c7448d8565e3ad90bbe75f0a1910510b4349c5afd86ccb1a550ddd1ae6a1be066674374226a986bdf12650cefe688a1854475dc2ca026e784f374d730863f41ce0d386ed9c123278a98118f695f00773e6a006e4e26e01b0d8eab0536fe3c80e7652e8c25c162ed85ec661fc0e76e08f0229a204205177d3908bd6250201b3aed9fe3e19c58988c954d9584aa556620097824e8001d1ecce00139a144009c8e738137aa34d94d9d0f0315fb71b05f9497611b754255f55bcc628fa8b0f571a4ae7bf98986e9560491421e447875113fe5196c4f6924af8de5bc⟩ (i-76)
        else
          cubicRow 48 18432 113280 6868728199188 (-5740360309008) (-226553029402) (-439622250048) ⟨15,0x8d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨39,0xf4dfe4940760ead7e01ffc2562906d70ddaf8148c746a7c38d4695b789463a5af11735cf526c3836f3d66884a262f89932497ee582b6a2f1bf660f2fd5320d598313809d0fecb3333e98099fa28581e4b1a51a387c0e7a4fa1d7f6d4ce91103069ec72d6625456fe3526a965d4046d53ad660c06a7faa7019d4ee3f9378a96fb84a1351714043c29ee13eaedd3385b2f3024e4a2f8b3462f995d22843b72e124f67bc24781c604af001339222d6565c4a93b4c8a23836f9111716d214c1d3c9da3642f6dc677fc49bfbd39706c46dfda00925b778920adb4729cc0a2bda5b78055aec4520000000000⟩ ⟨33,0x2813f9d5a5e64b1e5ad0ab12b0d21b4f19dd32a03d8939139f02af774799043cd5d4cc655fecd7855876d415a07b3b1379bd572548be7251fbaf123dfd7b70e778b3aa2b259dccf3cc2361f60dfdee85bbe755f1b6108a46ad21fcc64ee646331de5030102f90d8be90b9c0c2be5d9092a4741e6173eefc3c65e2e4a3c373bbd47d5f7a0b710fd1064150fcc35b74a029c59a58faeb996cb0786e942bbc8bdce01de46127ce7461c0d6d11120fb1ceeae155c242fdc8e1f71d8336c14ab8deab5fe800000000⟩ ⟨30,0x977fd442190727a756b74d994096e2550c4e29163db9e36922f40a06d7921a322540337843e002715b82fa9a99174d99e487e4a072be344fcd4065cf3d4ae13d1363d334ba893c546c3f0156ea07156d2cea95ecbc3258589b7d6305a97d8eadeff6349831d8753b895f42776d6e198cb56947515417fbf748db8bc4ffe5c9d35ab387ca7875551c8d9e6c3678fc102fd5128555b4982980c7b8fe3a00c57941e51c69a87c8ddbf3d2b12bbaecd0b6b93c0d92e4⟩ (i-140)
  else
    if i < 300 then
      if i < 236 then
        cubicRow 48 18432 131712 462192610730 (-439620887952) 24661163278 (-24006718512) ⟨15,0x8d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨36,0xccfc4140318725e406b9aa8060b88aec98115e5682e181451e4c1f8536822278c8c5983006db9cc38d1bb32241cbdffc84ad52cf1053cec40aa5c9b18210651dffb2a6d3cc8aca74de4d3f07beb09c9c824d33f3887f0d2f628cc3d934e90b63f2a693ba1fc2a95c3d632e96ca1d62696c630fbe95b3f03ac9392028da9061fe2628c28908e086eda960680bca742879a48735871b8166bc690e26b7e5fc1c5c0855f2771bc4bc4717904160df04436f6212e42cb81806422e06d59c19aee3c9a1169aa0e00a5db29ee04df10046014956056000000000⟩ ⟨30,0x2196b454ff04f555a8f0d0dc8430cd8657f3965ddcd11a5822b4ec236719b8af79cef7fbc81c094832702282c1bdfada4ee40f219b1c3482ea165f399ce851fe3e4e4bf8081045dbf61fb95dc40acd29bff71360b1a54831ac030ad6bd642e37aac222d7ca8e32c2824f26599193eee407a03cfc237cdb16a07b529ac5200bec00182f3312c7e0d5c32e5b700b286de9d8c8374850fcd715a4e32fefe00bb4ec2a29205ae886ffdbe188b85c23567d1900000000⟩ ⟨27,0x7f72c34e3bf06192336f2bbf4a04ab88f07c7de38c8586e13214dc1ac953c1f5e98013e7a802a89750f2c0ce3120de485dee494ed7f531b2f3a71efc44fe86d6a2d3f0f4b017329f49f2d4e21ffab50c5558e51eeb48f34d6af34cad1bf2b58ab54aac11bed49063ba6a2cab47046667ed8fa4d9adf695f703d1fdfbe224565140ae6c7874633821c02e06df7ec1396e0933fe05083fc47144f938b0e7ca573c3e6e⟩ (i-188)
      else
        if i < 268 then
          cubicRow 32 12288 150144 23226167544 (-16004408928) (-2322982788) (-1993229536) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨30,0x25e797823e183613105c707fc0ee82ee96bd0fd55d3650967cb9885f504734e8a820ee835892e4ceea8193e4eabdd2b32d3f506abb832ce2fcef4ccc00401daf725b18b88bbbeac176be6a5664d625f889468824a4b1da6600c63c62c79412dbfa3ce70860a9d5a3019f38e583203c10036189a00000000⟩ ⟨25,0x312d74ad29e3deeef1f2b686ba890d6da5567ee983b3742ff9b43b25d49e3ae66543f0b8ba76e57bea9ee31cdbba3e30657707a84313f44b11f2330ccee4083149b4e5a492c96f0185fee4cd84c2685fd832dc87d7895d2a1e4cd3d62b09156f88000000⟩ ⟨23,0x5a2ef894cb68ecd541653a81ec5dc23386014d8003301d1119ee35d0ac8ef4d95c43532392e6f7becf00eb9f7b39408116811984fc0549de30536bf1a5fa1749b7388de1f30e644e02c9404ef141464e440b678b75b81e77574dbad2⟩ (i-236)
        else
          cubicRow 32 12288 162432 2905546292 (-1993219264) (-239971778) (-235565248) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨27,0x296d18139dea0536c48117aa48335fb3c8ac9e096162d235cc34e7e8bd59214b91a859385582a27abd0caed8e69d433a0cbd695ef94d3bd005a2d54532f136b616f55cb6e1781501cfca5b019e41b67506ea6908b23d3490e9bdc179a32a1ce0b201bda3e80f13a70000000⟩ ⟨22,0x35c2858b4738779be90331b8e28f19639ccd44732fd5c68c3eead2fa9bae650a3f7a92ed765953ddb2c7052906fe18aa4624dcc91bf1f68f8d6ab0592c44acb5c04ce2fc439ba86e1629b439c6b3dfd2226944d48f000000⟩ ⟨20,0x62aba518c6410ce3138e2219413ba8062c206865124d71d19126d752f77f36e833d12d41e2f4541b4715f4745f45b534246b3cde53557d2b8e11f5e910a2100d2e153102ca32475e065998878d6ad768⟩ (i-268)
    else
      if i < 356 then
        if i < 332 then
          cubicRow 32 28032 174720 436790002 (-537380375) 192276932 (-18676448) ⟨15,0xcf018602dc055809f0126021c040807b00ea01bc034806300ba015c028804b008a00fc01c8033005a009c010801b002a003c0060009000c000c00000⟩ ⟨27,0x726bbc34c0d38d9813b2bf66467be5a153e98a1afd3c2d669c8b4d9574f5c6c6a0bac7482782616cf2c061de4a6d9bbba8d1743b3f0def8d95a50599b0ce55458abe089d32fd50e7a919c02a0c2c2a85a4103568565c96860a21008177a0098693808db9d004a1bf0000000⟩ ⟨23,0x494bb701aab69bcf2de0e01c0e9db6c56ae73c9aa2d6293b56de5f348c8a6d48a421905856e145220691dd1546063aa28894541162cdb32dfb670bbd8f202d1f740f3f267a797bfcdc7c016d289139d4a1f92742d1ec0304ee000000⟩ ⟨21,0x80af02eba40ec0a03333c06695924c1d0158e26667162378c67dc6cb563a61d1eccf8ff8548232a4114d1fd458f277c6f71e30b51139fd86c0241719a078dc0f6dd0ebce0b90a81c068109c409b75059fb0339ea⟩ (i-300)
        else
          cubicRow 24 110592 202752 73010111 (-73677672) 14888721 (-4929048) ⟨17,0xcc0060002d00150009c00480021000f0006c0030001500090003c0018000a80048001e000c000480018000900030000c000000⟩ ⟨24,0x67c6817f492317a5850352c716694926fdcb0d91eca5a20dce5b8e6b81ee669c6db0830c4388aa26d3c8ddb3877477c5f392e4676ae2e292c181b620ec19207283801f542000000⟩ ⟨20,0x428377535f987d3acd7fb2df1ab4d3970897728b4d0d91a6b71e9625b35897d36cf62a7373c7cecc83052841d27d9f86b4182db6622c9c13f1e00000⟩ ⟨17,0xea0655bc9bad0682a03e59c5bda6072b0bbb6fece2fb9ebed7dee71e7184adaa40c9105e83cc8b160cd4424cf1943910d8b68e⟩ (i-332)
      else
        if i < 416 then
          cubicRow 60 286656 313344 9292112 (-12775415) 3581781 (-83608) ⟨19,0x8be01170022800438008400102001f8003d80078000ea001c800378006d800da401b3c0367686ceb8d9d59b3a8367206cd80d9801b0003480066000c90018c00300005d000b40015c002a000510009c0012c00240004500084000fc001e000390006c000cc00180002d000540009c0012000210003c0006c000c00015000240003c0006000090000c0000c0000000⟩ ⟨22,0x30001260051a808238054490288e410e6e0680be263a50db1104d8899b5e2082348a200308b00b22cc508b49922d56e8b5a622db5a8b94222f8628e4bfa5f74ca12d4a96d30aa47e2cd476bbec630fef0cb651b483b4d7e01b73062e09d138d788e4f203951f4e450d38802ede4e2364caad2ab5b2ae62c162cadac84aab80a7631c8f4e7a0099e7046d17fb824f6838fc4682f58c88309a13eca8264e40296d800000⟩ ⟨18,0x24009f029543483157247adb29cd4dffd4b4f59ac98e9d7274f78df47e85102fc040700804010100184019100cec06730cdccc9d530bfc601318b44bc8f2c884a567259cc85751c9945d8511b342e7505264068808b303ffe177707c16269b8b87435758f20e4326124e64e8d94bc4562995fca57fb957ac5157126e83e898bc561a8c00002⟩ ⟨16,0xa004803de1004113c13dc1896203e2ce040aa5f0a8dc42bce02e200ce0007000d0000004c002100080006001702c5041d002b007004b105bb06e7080908fd0a150adb0bbd0c870d4b0ddb0e590ec10f0b0f210f230ed30e710db90cb70b7d09cd07b5051d020101da066c0bd412841a4e23802e903b8e⟩ (i-356)
        else
          ⟨600000,14870,0,0⟩

def l : Mesh := ⟨417, lRow, 1000000000000000⟩

private def uRow (i : ℕ) : Knot :=
  if i < 256 then
    if i < 160 then
      if i < 64 then
        cubicRow 64 39552 45000 1916562483889330 (-1512595077743158) 58397411764690 (-263739257697762) ⟨16,0x99009780960094809300918090008e808d008b808ac08a608a308a2a8a278a248a188a008700840081007e007b007800750072006f006c0069006600630060005d005a005700540051004e004b004800450042003f003c0039003600330030002d002a002700240021001e001b001800150012000f000c000900060003000000⟩ ⟨47,0xd7eebd9e7406bfd29d04901e61fc2d84d06c1547f9ebe151fce97865c3ce3951ee020a5ebc066fa81b1f08263c7044be7fd225ecaa0039c8f349772ae46eb23312d5e9a401a64ad758f9ac8c9f09aae3c4193da49b0b9b327914836da464e09d1777ecc97c0046e55986c5d6d08d4307b2ea328266250fec49b98cb0d2110de09a9751b381bc384e321a6a7a780c4b63521500ed23c4e81a2698511818849b385dc115e9d8724feea894fab3228abdac88d1da20dd5e2168f3907ac608bad865859e97096abe5b5f8f5017d656fd649ae5cc6e68319812651d88ea3a811e3c36f9bcbb827a1337cb1d86f60f9d995225ed06de1819dbd5c5845fd59796652343638ee8c533c0441d157b3d1a8a384af2e79d106c093d931654cd6c7a702ef9829a4c84092acf3d00d701c528acc4967fe954bc9cf7f65094e0f862711cd9c1340f0e30eb77cbab78504e8c1060f07e66d68cc968bbe91549a5210143cd1a01e1355ba1a8c64125bcc1c989809cc6b43e58000000000000⟩ ⟨42,0x11fed9d6094900670ca41360c83258ed20903adb1f5a4cf2258bdb23059c51f7ee69d05b0e45878a331da40381e9046db455d67c36025657429cc50c76cba718edd2a7ca40c7bae8b47001266c3dd800bc04cfcc00ba4f3e4d005b7301e6a13bdd7118580ef087118f18bdf6cee34ad479f5bb53b82df0642d2571f1e7ef54eb22d113d78f0125ffd655d329c8eda976accea16d4d6a7a045b8f5ee5ac96d400b036f5a9a1e76ef365cb722e1157dfbf11299579a94d2add38dd0f9e77436fb47ced4dd81317fd32a27442367c6f92fa9c010cbadf9fde40cc87e87f413bbde2ce6092e71585643600de08af11d7aa5846c58988096a49a5ba088df4799b3b23b6a234c7630ea96c3df3431a8c4f1df600ad60e88f3d2d501067a5eba3cc776272ef59404154b9805dbabaaca831738d2a68e2e92ef252397dc4007bd45e0de996df949da2032932bfc9980000000002⟩ ⟨39,0x47fedfc22c902d41d44920fff84af243ddf949a48cab5f8a0925b7d64a12697020a42519d715024ad886a678972aabbae84bfefd67a0261ad998c0131467b1400098aa3681027fac95000036bc5e0006d5004000367f4de98b864cec82c768ca0e64f205b4a388afbcb1e88f021de337196180a44629b0a6b11441a9864e1860cbb4d6b07e77d359807ad035594005d30d44c1efcb8126877fe1b10b15eb0b29ce38f6c1ff7c8aab1883894396f4add2dccef2dba6563b93c9cdc68b09a79d7f031ca33e553bc91e822e9e1ed50cee02e7ca25c70cb474584abd2768ae038972d11980cff7a128f3a5df3f1c6acb5e7557df36fcd390d360b96d304edd924cef7d7123471c171b436e648ec7806eda3dcc11c0cc2f884a527f0778ed5bde3b02a487e6ff871264efb6122dda8c30ad731938616f55f7e676⟩ i
      else
        if i < 112 then
          cubicRow 48 18432 84552 198625560213100 (-122907494738352) (-29472847191756) (-19873524360672) ⟨15,0x8d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨43,0xbcf97759005b1ffac1d018b1b1b1cc05484b44e140fdfdcee78c2beb5f4018072ba6888ab11f4270d0882b81ae608e066b5b50f668ed54eb64e721a9c6698ce4b39f027dd0a5dbe891679695a99fd7b30ae504f49467ea184f814dbd5de07b19cd330a4e3b3bff7f473f27bf2ee49f8cfe379f6630a05bb9bbb104171c96890c8373623648d0634548de72075876cffb3fd3f27a4d67c92b7930d8f138ed2a451cf372035c0371919f1edc67d841e3e30c1a3324133164cc82f96a288a911a3a448936d1b39c7f9af938400db9a7a64d217030e511cc255766cedd83a14812e030554bbf0c9f073536c87aa088e9a28ea40804e508fd0043923951e00000000000⟩ ⟨37,0x1eee83a349d42963c2d4b619675acffb7a2e17a0b8e6f5c48c8580b654f90a79b3d285927da534b11b7d49d5998b6ab086b7bf53cfbfee7a6ca1551ad0c3fa42066907a89632233453c38632178b6bcd7cee1b5aedfcfe3ab8e4a41a34c077915d9d50e20ff4a1b4e6eea2b2f3ca930250876aa889b4829e89328cfedc7069bcb0e4b3ee2d9c2ed72ab0a9bd1bc3c88ff93fa50c8ef6326a34e43ce643aa0ddf5d1d637855392b8c8ed7665e86ef452af8df00b0177dfae17eb5dbc0c6755cea4282a7348e09311228542466ff85485d2887aa9670af93e31c0000000000⟩ ⟨34,0x74f54b8399ef4b4f45ad9b38c139381156421d65e70d92d017a2adb1f4a87f42cbd8152fd25802bf1f220013adac782042f79710e1ca77464ce6055210141a4ca116b7152efb8c3fcd4754e913aa53e8acfe35240943cf2d6bd1d91873b4a461425531b49eab4dd230b3d39b5c61f4e36d61953497c1494b31f38852146c0cd447b8ef24fe96307f39c531ef4cb3e4e892ab94723c85d97a5916fa6078c2ce1043501dda54b841566730203e8d9f0c6a0921244a2be35964fe00426f905f7121ea0b252a19a9e4eaf5f1781e⟩ (i-64)
        else
          cubicRow 48 18048 102984 26371693922320 (-19459474641121) (-2615921446197) (-1997820233419) ⟨15,0x8a010e0210040807e00f601e003a807200de01b0034806600c6018002e805a00ae0150028804e009601200228042007e00f001d4039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨40,0x120847a4a04532edda609531f56ea0fdd8d31ee17b1e08ab82091cd40da2a416f3d283487681bae3f2cfe4b9e49fe3db8da54ca1a132c5f6292c8e4699cd8cb2c735176342a7c5c77e810849d994b888bf8722bcc9254a6f5d2979e1b5c0e9bc5278b7e9ebed01376a08500a484a116c9cdcca078a1e2029eb4a92f8e9bdaf1ba029801caa5b895be2e22129345f9a0768dbf06c7de8771a946f08063b1f2cc789efba51670318fd3b4672dcc866e5daa8bbdbc53c34c58ba49985c8b6c3f4f05f4de3511bb673e2b10487332218002ca5a189bfd8bac10a53e8f6e09e2f5c75a04a2b6cab80138b4a4e00000000000⟩ ⟨34,0x2f1a10a356187d0f77c0278cc668a50f89b3062c6971b2d584bd5ad4e4d77f8caacbe5a6a8f2f9cd1421be4cb95f8f7abc0089d5244f4bf21d2995fb8ecb61869b73ab8f92999caa5f1ed056f64dea24e53094509f32b4b204c63e26e51009ec94a8666e2dc43181e5ac91f3fc7c65bfd58668ca34518636c67be69f8f1adf48e9569f6a791f03a0acfbc3f1ae95aae06c5fa771033e17370cd693ddcd36af0e9aedb92b886b629d272ad185d64ab16d8516cb4bb5f0227852295a813bb64e176987d8632c3ed62000000000⟩ ⟨31,0xb09815ad3342a0020d735d936e99d66590d75a88a29e650c7ce55a0fd9ddc80e60470803f6b7b4454cc268fcd50f92cc479de7185b34d0e1cc36a6811a235523d28eb7b659e5845a219b261a28766cdcfb2ce432de596a3ef8b126a1b75cf68852ab1754252fc8edb88c3ce631072fa9a84c1717d01ca9db9e95f8f53880734e64c70a7cab2019790d02af316de4d5a14e6773c0ec083b09cdd02c255fb6f4721afba13adadb23336eb48804609e538a67e42eaa8b526db02ee2⟩ (i-112)
    else
      if i < 192 then
        cubicRow 32 12288 121032 2298477601583 (-1360214877472) (-347042360520) (-231223279520) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨36,0x20d6a9aa07c1145a8107156ea01b7c0e24a2846f4836364003df244dddabe253a02664c621011e2e6fc0ba5a27c4fa8c088765515d890b5994e89800625849d121d5329fc4638989ffe975829db68c6d498f13806e91c36992a88528c18a7cd570dd26f9523b3860edc9748514f891da413f801ec3158c2632224d66ac414e79fda80a0ae3caa02b520748000000000⟩ ⟨31,0x2a8e7bbe9bcbd355a94ca56c0141bd78fbb01e332cb2afe7619449ce400cb396ba8ec719448cf5faa41c3b6a3032158f62b268478a5f4a68664f87dad1a90af10fe04b69a9c0ffc1f1d2c7b7bd67012f845090d176a562ac53512775d0a9f8cc295746f10a997cab64c9855788310c148c5d743a0de8144200000000⟩ ⟨28,0x9b7d21c7f340ba642b3164a71fb2321885a1b2fb4a05c92f80e0887520320e9309f21f3f3a7fd4bedeb956a21b75f3ea7765aa03f69c96e36b80df56ab2f896740fb5610aabb57ee4894bc873f3c741ab29ca66913a2a91062dca223d3a68457dcae6b5d4fc95a5bc4c48d0b6f84bd84⟩ (i-160)
      else
        if i < 224 then
          cubicRow 32 12288 133320 359997084071 (-231222571616) (-45574132806) (-33625374048) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨34,0x1c6477e81ad84e3c0e3ee48485f586c6622f7501c8bc92c4ae3be762c29233f9fa055768fd5985efa7bc6c8940681d94467d47e8fc2f72142f7a568996ff5023038ffba8c5ad985229cafa3886593d3ea007ea5d077e60e929b76fa6f06240ecaf95597274a47ad09b80e62faaa62b8b4aa18792270d41276e6f08237f4ed40264c599000000000⟩ ⟨29,0x24d078ca1bf3e157117b42dece8af7d26c0ec2e649de269495f1202a0784369e7bdcfca2dbe6fda2c12231f4eea2e89d8c513c96515121db6c3b088dc2e100e0600dcf5fe89ab1cd461cd73639f9349a0c5af4d1d0162c956d6d94b88496a4a4f2350e2c8ee73ac5772baf6920c4aa5fc0000000⟩ ⟨26,0x86c0101baa102578b07905dc062c7ba0062a4d406110302cea771b267a4a67853368bd350763514b6cf7d4cbae3590426d7352df5e8699577fb095b20df5573d6f4deb20d0d4edf35e731c9607c711feb7c1325e41eff6d0f3371a5e6154a0fa374ad955ab6e683c⟩ (i-192)
        else
          cubicRow 32 12288 145608 49575005601 (-33625238080) (-5352177681) (-4347948704) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨31,0x25b7b5c11d858184bd21770fdf2df82e9b54687dcac6b93ffd31a30aa963a725d0b35052eea22464079c4f6f4806aa26ddd16634cfa2e5e29bf5e88029cbdbec26576e7ccaad8c10475703bce4a3212d092b7438aa1895b9a3a67013c6237d6b09e030710ef9733414dea4f019802624188ff7180d4720000000000⟩ ⟨26,0x30ecddd673dad7af2a6e529e59a744306cc8eb9b8a6de6e0d1c5b23955e9ca447977e2f60eea4d6c6801d4861f93566d2c5bdc310888f70a183fa47cdcb1980250821e3ba6cfac4b06c1d302889ccacd1cb372418c860bb2e533b49f33161e29152441c540000000⟩ ⟨24,0x59a94649dc083aabd42c22761e4a34112db604d88a06a925114a971afe3723b58b2b618b31f1fb3755e33b7b333e4ee73fbcd73fafc73e10c53ac85b35bd152ed46f25f1f51af7cb0dc68f01c33213c9022870223fdfdc5a424e77c36e989206⟩ (i-224)
  else
    if i < 352 then
      if i < 288 then
        cubicRow 32 12288 157896 6249641136 (-4347927680) (-551673847) (-516975808) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨28,0x2bfa2c0a692481621f4e25178de367fff2499a7f25db00807213fde8624df0994cfecab03522bacc3dec83a7d0d2f00deda9f344df0b86ae00b0dadd87770d77f584ce07892c14c8ecb19421a9f3ec788ac987c74cfbae5e0cf4c475f0ce31c84561e719440ead0f003f879e0000000⟩ ⟨23,0x3910cad1bd0e3eeb5d6ff2dc407afa4770f6415eec6c17d22e038b1226cdd21ce4233815672c5255503b098e90c50802245b4d814b98a3b65cc9852956ccbb33f7ac71c1c0f006e5e80cdbb825a6e3faebdbef12007f945b97000000⟩ ⟨21,0x68b532b3e5113bc868312240610a6170197800e351139608f82eca559664e9f3a4dca0663d1766292bab4b3eca5b15526ac28bf574031e9c168cb725641bdd114508097d05aaf45ec404b84035a4da3bb296d54c⟩ (i-256)
      else
        if i < 320 then
          cubicRow 32 18432 170184 833063801 (-775459488) 106681542 (-41063184) ⟨15,0x8a010801f803c007200d80198030005a00a801380240042007800d8018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨27,0x3a4c6c1b3fd7872316417886f043e1f00b3875b9be30c3421317096940014be623ac5ff505c4d1ccbacad816f91872be00e0510d1a2999badd200a46a15c3663cff5c86dd4b48c23e5c95045a9237303a39df7c85a9145085d5190b616100d98a300cd2b7806cbf50000000⟩ ⟨22,0x4b2dbe1d0b5b4b33f501d5e5da6fab7e9e3e447474cdb5ba96433bf647204c8e41040d28f1394742cdaa3d12609ac9af0ce75b619f8d4a84fdd2272488c4b4230cd2892a6a0b52c78cf31aac285808d1017e62334e800000⟩ ⟨20,0x870ae694424c77830d101674c02697198f92ec2741b17520d35f78b698176faff717296e2a5651c9176a1153a5129390f6c70bbb3077770296702f0c092c81024c17e9c208902a0f6348d8401424cb5a⟩ (i-288)
        else
          cubicRow 32 108288 188616 123222671 (-241237746) 136433664 (-6554015) ⟨17,0xc7805dc02be014700978045c01fe00e70067802dc013e0087003d801bc00c60057002580114007e00390019800b4004e0021000d80054001e000c0004800180006000000⟩ ⟨27,0x52b168268d990a0f66e20ff43c5e7e260f76fe025ebf9d583a60cc422b85a1cecab541dfa67744f6c78ef5d7a4c49abe4a854f63be68acffc0ff63579cf822233b73c05a74e209a2e438fe172419017a424e8150315b1a837d35b04b50b40595f34053db6802c49b0000000⟩ ⟨23,0x35435abebdddf9a12c93d239bb5bf3486e639585bc16ed581b925d12240fe791f4b122f3f107fc72943e9931108272b1fc7a6d390319921f256466368900b9121eb323ab78440b707bb560cf2530b39301242ec1a6eb81cb85000000⟩ ⟨20,0xbeaae9231c661883a75e0f6481af8d447676cd2b93c55b8d73db487f997f4163f43c1344f4f443f54047f0efc50d8470b6fd08889048cf00df608362121a21f5ea311b60f23c12546160481a4321f290⟩ (i-320)
    else
      if i < 400 then
        cubicRow 48 206904 296904 11864574 (-12521969) 3717738 (-2017314) ⟨18,0xca0b32820c9f032700c90032100c83d320eec83a320d0c82832040c7e031e00c60030000ba002d000ae002a000a200270009600240008a00210007e001e00072001b0006600180005a00150004e001200042000f00036000c0002a00090001e0006000120003000060000000⟩ ⟨21,0x18c001b6004a48062e40b4dd0a2b9051f44291fe148d80a38f850f3c27a6a1301908b2082cf88111d1154148dcd2c715ce306550fe488210dc29948360682d10b1ff5514bd18cb3067747c43beb256f6d4330caaaa1584f2accc7164690ad8d7529eda65935148b6784cc320b7939e88711e823bf208e86013f0c00000⟩ ⟨16,0x107013f0a2714d35beb64eb018f00cb001c01280236046208ae11103ef0abfc64442478136f439f6c458d65a743ba05c5edcb2bc9efc2adb5a7a33d8bed703350a52de308b71e0645426be49072b16accf2e0d2ea64e6bad230a87e64740002⟩ ⟨14,0x40c002004003811684a400140080158031000800a006002c0a8a5e68781df4680962649e8eb42c70794110810c08cc5211fb4a8d3384eeb42a52114c2d3a94e75307466cf5330a47d107745943c01ab4a543b2a⟩ (i-352)
      else
        if i < 445 then
          cubicRow 45 96192 503808 1043029 (-8016) (-980063) (-40080) ⟨17,0x177a8bba45d722df9157c89fe449f221f90f7c86fe431f215f9097c83fe41fda0feb87f563fa81fce0fe107e483e641e720e79067c827e4127208d9045482244110a087f043c81be407f2027900dc8056401f2003900048001e000c000300000⟩ ⟨19,0x11000c20081c076989c75342cabddd6387ddd4f5db2dfc6b07075daf1036b4acdefb1c01238242703f8e02c1bf0c373d86bf20cdff1768226922369b866dd8c8ff18e16318ac62e10c43b1850216fc41f2646f0b8ff6121716402642ab68005f0003400050000500000⟩ ⟨18,0x60008800a601778451219b507ac01f7786b820f3601895291c57e55b27140b390058c00b300060006c00380036801ad00cfa0603827b209dd8070e00b38013800240004a0041801280fc304e46066d8095200c280a39191a41fb70008c0002000180000⟩ ⟨16,0xa0003000b018913ff0dbb062f031c0f3c1f7235ea55d483f4c75e0009000b0002001600080005000e0014003800ec04701604016c005c00140004000300260000058219dc06f801ca014e0766322a0386002a000400000006⟩ (i-400)
        else
          ⟨600000,14870,0,0⟩

def u : Mesh := ⟨446, uRow, 1000000000000000⟩

private def cfRow (i : ℕ) : Knot :=
  if i < 368 then
    if i < 192 then
      if i < 80 then
        if i < 32 then
          cubicRow 32 120 30000 394030763240724417661881 0 19863082059404 (-16473586152739320) ⟨7,0xe5b3360b55274884f1cb666c16aa4e9109e3660a921e304860608080⟩ ⟨45,0x4da40c621f08b6acee70f88bec44bdb686e2ea91322e4ba85b8bf0c2f736486ac99bd77336bc78f7d68c0001683bfe47ad6b432fa52f198216ab8747aa507405e1d1cc80470a228293dd64017d0c9d78b551ab00de03095c2aa672542be0712f37fed0904154237a3bfd4963894c998e40dbe3314931b3f448f7790b1016cd67d844c572716a0192c441802208746f95fcd827a6c483550090a4b091b60116ed3886f0039360d81900050bcb079c00000000000⟩ ⟨40,0x6213251b15a53e537721ccdd056299dc5c3aa4a9d72a7427b1c0b78819059c74ad62b36dd4814cb7384b2ed0fd00b1dbadaa0eafb9efa21cd23dd8522a8557b4043791672b7c43beceda244ed5ee69ee589efae3ea60e23811566767d506ca6bf7fa7cc06e5ac0a9d46e583d9e2c6bb86882e066433b677c5dc0aba7d851f882fa2042b2b69a2c2fb6f5d87618cd11629c0f3b10ecde032a54df840000000000⟩ ⟨38,0xa378c5c7c9a3ce139c83546b2dd3021d4ed8641d7db80cb4f23dd628f54bd0d903d98118d60970622a2d5dcf4dbbd071c9ac1eb446fcd450291add38ebfc655dbd6af17627589bc53f94c6bf122a77b59c3b9bab8150b33d28bdc1c43e5d83027e2a4e540a10e063007f6fb49383766f1da0142c559f586bbfbfd4a22235348b8a71e29d1e31dbd710b2e1832514f2720733d240a46f5bb3⟩ i
        else
          cubicRow 48 468 30120 394030746787001346981965 (-64246975400425350) (-325118547727924082) (-1482677525072167944) ⟨9,0xe46f361a4cc6330174b4572a1449c4b24114843f1e0e46c33180b45427120843c1b0cc602d1509c48210f06c30150903c18090300c00⟩ ⟨52,0x23c0fc9667a8087aeba23e35612132433873861e6463229155c2cd7727f2acb03cde4434c447a4df3f984e3d865f9cea83fb4c67166ad9f98e3e82e81f2a59ca693c168edf0a16a39c09c20e942b22add2d5da0ebf2a230a3376eca5f87311ff04d39a292d54746dab2a3f2fd37edf8b15a01c206e20f2742bce66e23414a3e8de0dff8b41d33674db657e6f63898d48c96a41169acb89d1f5a57b0c082bfbe5d03eb3a6b167dd668a52ec26b679f8955de0516be748480d2bbef16e72ee4373bcfe069feb6104eccc6106c682099285814153837a2c4f34e24abdde646780dbb182623ded17b392a0635a420cd2a26a2dadea4d6e4ce261bd6697ba1e1effe88822fba186cc582ecba21275b3e96812c0d2e9c421642008ac094df27b80503284a359060249c93285b1800965f04331f40000000000000⟩ ⟨47,0x2e6ea319c2b6ab3eabbf4425d7c4ca51679c7e2b5948507a37d813a69cb62f68acbeb0ee88362c71b8dee855fc4b83bced808790e36fb4d06080a6bbeb165fb35d1592661a825936502ff073302ee7ea052d5b536aacbef1aba6a024c6bb3fdb4dd7105a4ebae775a7fc38e696058928594eae58c14246663f107c87a2a2d1fee79533aacc02383595c5702b347fc3c9ebee81245e4f89dce288143a39613576e4964d1ecb84c7300baad7bd630207cd17e54026d2772fd36dd964065f2409c5f1f0bc0bc4e48dc97116eab9e752cee7250b59a56c4afb4e3c8a5ecd1402be139ad662c837248e64b981da4303fd16a0bc78346bdc91a8d162ccd553815dc586f057822336885cc142f8421b4ad3031777675fe0000000000000⟩ ⟨44,0xaada6835b168e9cf1a080073e3a7674da5aafc46b384430288a91e62cdd2ded8e41840f5da232052f214fba40c570bf02d11c505040dff2abb6962da137970feb96742e1fe1827d4c9aec27f3554c09144cdf5b51a5cc385604cdd5b6f163b0ee21d8d657c8bd6d2165ae6407e2164452d45abf613f94bd27d5c9c49b68835659fa5c56f4e7751e082744f2fd1aed339cba5e909d2cfff5f2ec51e8e918e2c10e76269e4b1016a9b93f9700dac9e0ec0033acc42f8a05b5749666c084acdc15840afae5052dc0dc5c462e6c10ab76cf55a13ac047435a16c77d7666019fde738d321d4f526333620bbc4601b624434de25ea27e5f5c55c82ba3c6aa1142f7ccfeae26337119d9010⟩ (i-32)
      else
        if i < 128 then
          cubicRow 48 1020 30588 394028874743953146464589 (-3231476494198993175) (-8882682997577950892) (-21925500751957630153) ⟨10,0xf93cced39ce136cd533cc930cbd2dcb12aca527c9924c8d21c811ec751bc6918c5d15c5112c450fc390cc2d09c210781b060150480f0300901803000⟩ ⟨57,0x1149f7e63126a020f970f5c51ab82354ddf5e192281ddf8cd10c465a162b6a8b2baa030f241f11c835fa09c27af064f3120606f681ec2d3b8399c73a35dc47c2183546df89ad013121e71401833caa6f740e467f225dadf0e0c4b19732c42f94a724911b2a01578f1ec0ce5e353747498fa784dde5685be363e5483ab3ca31f9ffcd8475b0ab7d04420d1d9dae2a8329f75900763441850f2527ab55207055ec345cb30fea6ef89a3b75a7bc8511def19f23b95dd997ffd839c6366394ccde2cd603be2afb3bfe63a09b45bfcc542dc2fd2255f5e994b493b939c289c9354317f15b48c40360b01e6a9231b5189a371c4880b48981ee3c98fc47d2d39f3b29ac1b31f5b165c2e40b8d04ffdddad584ce88356ed1f101f3558dc6cddc40c44654b906dcd04a025386a9f3401a5e866dd6f73808a7eef9547cae027f1ff3627c4b00919b232d3e118012a7578d54d5400000000000000⟩ ⟨51,0x2d057db55ad3aa765acd52ecddd1442878b499c795774fc6603a48bd3242e65f697f022dd106f0048f341796be368633c42f19c9485abf02bdf8f8d677a9b9cf0a6827071fe0dd088a097c91dae7b09d886c7b404f45cb978de3d9c623e70d3be4513410f6b967e20ba12d3aaa38115bfa8ebce9dfb05ef208912d7e77a3a7d09bd11b5cbb861e1bf3806c8389ec704b2a1dd1fecab7b821e6572f435b7f7dcdabb06ddbf702083620fd26b54a741af5bd55aa595e2ba33295677cac323fdbafc231f19dc35638def6590080cb9db092a14f198677feb1470b220bf0e7ec196017e01769dd4b2ddd117f4f20aa3799baebf11405f37e6d071252e5953d219a43e49d3e51bb07953568e0df38d297d601f3ec15e9c7edd012e222c897354c1c2f55d919f25083122fa38265f0000000000000⟩ ⟨48,0xa718de8f886c8e470f1c21fa769fa5013120602483f89fdc4ad79326cd4e36babd34dc6c23cfef54fe3412191a8b83b20198324888400db0d23351411bbff80b989f2893423834133428af55b7eb3e7e3b07a6ad4791dd80f6994f618bc16df555eb3759c7915b2cce0d76b75f243af6a69961cf64b99141632c2f29da7763387a78e16d61f223138ed55f57019471975b64ebfa09795619b387b92d4f7326857497476f0f1078013e0b344cafa3334558af0f43271b3bd0382b198a98ca45150a9127340d0505d364e4d41417a55c2acc8c2ae711e183223f9ade7d222412a7304033ae1577eae388cc186012e166c81b5fbafb321c1e76f69f27b021a5d8bcf90024ec74d50466284ade308d2a2bc1280c550a2f4f6628446832f5abdab390⟩ (i-80)
        else
          cubicRow 64 2712 31608 393994835083709411890369 (-58296034645228201324) (-155676121561757653421) (-328816230689260775781) ⟨12,0xa68a38a089d89a89789489188e88b88888588287f87c87987687387086d86a86786486185e85b85885585284f84c84984684384083d83a83783483182e82b82882582281f81c81981681501381201080f00d80c00a8090078060048030018000⟩ ⟨61,0x124d5dc41c4bbe023620eaf63c1d0826738734834a78c20fe2146ebdedf218dcebe2c09e88c11412cbae7f666f8b4f435cd9560c2071b91ff73f7bd464532432817e6c372908b48776c037617d3ca7641f04578d98533d78fe1be27a44c0266c428f543d84e19b6aca812538cb3b851fd48d4376edb92170c18ae1a8abecfbccbd5cf1c619314b2d0313eee1aed8d30e99e94da09c97502cd8b92ee26de2d057099d8970e8e7c7ba29f71a1bc0362dde0bab21776e9d2f4400564793fdd87c258fdaf1bc3663ec78ab696a452c9f9650e6191a4ad8fd03f6c060c94bb7e085278068f4f7be764b95b86315f5ecc1514bc9a5474f1acaaab8c918e675e2aa38a10a7ec392d55dcd361e765b913fde6f8943e4d3533866ea142b86491cdff9f9e12c2f841d53f29e49e16463981dadc6fe0a5a26cf39efa5774c3ff958a085f56a2bab3c3c6745838fa0ca83dd9a851e6ef8bd91437ddc530759d14357703394c27d529f4cad048b084165c67a7d4388bfe43be20534192acea7358b2ad0b15ba7de9e464ac4d2e1af34801e04211d63f439f74030df8be5fa98db0685c6c6af762ef5e825446962592466c0e8ef58d28fbd1a0574de6656aae7881eec7b1ad4ae9080a17ca07fa20fac02e50e95327b87700a7e834da8050380156569b9062ce8000000000000000⟩ ⟨56,0x17fe159ff3fa4f2d8f38d5fc5ef140c580c1f3e8fb51b396227e9fed606c5e5de6ef536d02fc43241a47778ad0cd72b85580177bea9043c986bcdd435100e38b8f1506d2cbef8ea284b900c261900bd0032015658fdfdd873529d38e33d7b691e80b8b1d2dab0451f186b19402bb4175810705bf8834a17a33c52854bc15724e5caecd10a7696d9fd6c1175f5fa8ac2199ae0b5516e9fc08825b49d00db05688833dec185a788c6d318358dfd44c5324ae6ceac648a3178641e95e24ad0a24160efd5235035e86a5dc2c1610e7b162bb057a1e5d33745be2be2ba481369c7f9038a2b900e7a62a453ca20e2da9765156ab6152ad765cd4eaa6b9b194679b1b10445352718c9c2eb6d9627a8c70c6dec84a827d3da159032489414858a0c98c8eba762095456492ca4a8b1a5a809551e6482b89ec963205e106ef62954b006f925cd8927cc650e217d88da6dfd372d3d286a86be01e272e4127a9e6a423ce3eafec4fea363c3beabd6b1bc9e638d5fc9a8d1404356f85ced80de031b531813948d62da4d4ad80bde4293c40ccdad13e247943cf6132bc1f59a816e6c03819db34709e326c13fbac0f9765940db8ce863db944071057c1193dbc00000000000000⟩ ⟨52,0xb616fb7af5d28a2f5ee302b4da906935a13befa7e72b40d8d8f26d1451ae145525c4ffcd0de6e24c27a9eaf16883c9d53ad5dc622db2fb1d35f461f6aa79b0bc8811c667094feb204c84dde06f4e078d88cea4f871338fb23dd60d1e37e073e42ff2888092590a5b32273e99b3b4b3b13431cccc7f4349d1bd605c54ac89e426df19518d550e172bf57959b099f89b5cdf0d8048b0d61674204e0541652bc6677a45f682a2090ea9c56a5fce5f7256b6bca459bd53bf6c66f3cb9a64d6c333e2d672e76b2c817c4a26f695011e747a23669b3af8fea77630b3f6a555175e9d59002bd07594eb8821ecab531c858cd16ad4c03de7033b914401d81e829d13b137dea710a33135d19236c912665cafad14591aa0581a7c3530de25cdd3acf70028b2f3ca96f0e8fd64952bd21e4a7a06bb12e2f0a7dfdf0aa640d332c3f282a128c169f7e16a14ef24f88c81217632a807c3c819e842b171c101c7e8931a19ee1f2619cf397cc21df108c3a92624a9899606ac82785a14db842c2a73743b9bf602d731f1d908623084bed8dbbbc33a8708f1485436de5185d1ab03a267f399aaea⟩ (i-128)
    else
      if i < 288 then
        if i < 240 then
          cubicRow 48 4320 34320 393452046696813165259843 (-523778050019223560610) (-966328678420254898742) (-1468209580429390901325) ⟨13,0x8404081f80f607803a81c80de06c03481980c606002e81680ae0540288138096048022810807e03c01c80d806603001680a804e024010807803601800a804801e00c004801e00c00480180060000⟩ ⟨63,0x11a3bd1270ac04408770063be78b0582484da57fcc68c207c57f210560e512173abc09f1fa52483fe954e10a9af788a5fda8a7e763b2f19d20981f7489b503e2e45356e6d74f491d8763300084ad14ebb6d5b7f945ca2f24e5bbcd53ccae689382f34692d864e4cabd5d6d1fc2d9ee6ed3d0332e025420af4f31649b7f28bb684729b86f91d24c68789f0c3442a6014d4fd0e05ec04e44657d255ac4ba9fddf2d1a069269d43f05bfd3f990fa28b3aa51849309c4512e2ade153e6b80a0a002229c4703593b38e9c96f925a7a65621ad611797a449ef9ee9fc6e8cec8d3fe9f98685d4a90b1c81ee9744e391f389f0198ae8cc839acbae7eee3ef8a6914c93121aa6154bc75e182e63121714bdd9c76b2ea28123bd63ff99f8b40e3bfaf2236b08546c61665411ff22d2e89790f62278081f90dea54275c98a70c12d0b93c3d94de401655716860c32b501fd95181b9fa103029d87ee33c0caba0304f404cc856fb002c0e1af66a2c59001697b1205bf1f00000000000000000⟩ ⟨57,0x2e158b32ad870dab441c64d470bade616daa9fd4ebb2e7ba4599185bfafe1ac8c916f3ce1d1e18935397174adfddba0d9ce3baa73090b3470be3ad6a043b6b14f2fed7e01f357cf91f8d22573af0bbed4a99722fd77d6ff07fd25c059e5bd7543aca8baef4791fb8eda09758564a71d7b6b998e54b9c267986c1c929b482025f5b1e6bd052e82e6a7c96f287718d73a1eb663f9a9948fba79abd6516f410db006953f9062e94f5ebbf74de32bb31c6a5c3d326e2d39e4752591a0477e1dd9dad5028b243cf6a99699041b60132583577736eaef0c6b30a8c0c5a002a2da77b988c2cc612e1d8223074fa7676445a7da188083cd8dedb25043fdebf343880e54cef3d97821b17f377647303ce29e9f37e82f03e4d57f5992bb0ed3f5794b2efdc14b127414916d9110849b30fdef6f92006e3c69c9dc05d83b5e2948fba793ff330e4faf6228b24e83b7d548221e2d400000000000000⟩ ⟨54,0xace110dcc2f06a5ab7c149df0fa813764e08b7db1b20ab7dcf4b2e58952b42fb059115d175d09ce1a3325e710019c8086be35136aadc111738c27706d0058bda7cfad460d6706c9abf10c6d019b9c118a72822a9feeafeacd01ca0ecd16ab3ee710a607692522eda095f0d6f517d086fd8cbdd64927bd3f7c5b5faaabc99c1cd5941e01e71f39b69333ee9ecc5e5b09760698b7896dd70af3cfaf65b8f98c0791ba16d5337242a5455ac32a0f62367d67619fd169de0d89233a8a476695bb8ab3797bda54e9dc1b267f614a0b1bdff69a34fb65b1a93072b3207e0800d7cd48e2ed2289feb51359e132aaf92c059c66a71f9fd1258362a784e489fbfadff76ce23f6c2e9657f3796365d274cb62e744481be7311ca46e9aca0e997e2859aac684ffd0b1722a4c1d5863081ca95e7cd00d3276b1b4a4a439352c81af88f0f710ca1defed8⟩ (i-192)
        else
          cubicRow 48 14016 38640 390493730387944295899166 (-4763524283870713066418) (-10082232919941631429878) (-12943931828462467238350) ⟨14,0xd5033c0c9030c0bd02dc0b102ac0a5027c099024c08d020407501bc069018c05d015c051012c048011404200fc03c00e403600cc03000b402a009c024008401e006c0180054012003c00c0024006000c00180000⟩ ⟨65,0xb85f13c7653da0017f2138d9ccf8d701bc978a8814fe2a8194e58e467e8356814214e9447d13dad0eabff574d10b52c0a0d64f7e68f5ea9869303549a0188e024252035a9315fa552895747beb2c733d18381c94a75d27858e24ea0df5622de0081ac5c9b15560cd851026c7f352368be2fb9d3378be78f9c59623e6c4d1482fced53497ed4f861a7b6e78d37bd773494d387cb1cbd4edf8969c7d788148e0d0062e29dc671e9f549c06eed7173d72bef7ab68935abafc0f4265ab140a78cb375e00d00b4322f250904a64d5a15e9e44c3cb309baf4324529d95574b939311f218248b17e2a690839726e53ef9e9991df9ce4a7639ab512c7232e5253a786d3dc30154872063bc240717983d97fb279f7482959bb9e9ce2607fb134c4ce0db83d82bc9c55d1c48089e3419724a7f9a33f35f5a28f43949d97301a4d0627d329b5cf00b162617c6773f40cf720deb39ad8c6c0d6284af4add79d0f885416298fd36d005b26052ccf7c8980fbdc00aded9dfe761ba3001646d739a8c3ae40000000000000000⟩ ⟨61,0x7d899c056d84ab8842573cc68e85a466e3bb044c157364654df11e107da92c9076332a66c059ad26b3352a68c0cf89163b2132adfe8b9e58d052eae934c6960cf7f70457a8ddb74f745aa795564b2b6f787ea56af851226b3c53d958240c9df5547f7d3074b7dbe3fddae2d06c548bd203fa779c8a24098f00d2ffa076936d29699121c154a29873b44b631b4c87c29f603f07730d7f4a75100dac11bdcc811116a4a94573d688858b4076ae09d1ac35e0ff98ac6ecf81faab97d50d915a1228a7c29bfe0290a3640d0483545a85a6b57bef1a5554315a2ae857f716f1a9c301debb2bdb8e30475ff21c5e3877c831eb165ec543e8fdfb0ae3eb612058e393339dcca908d778366bb19b4860db90d9497c90430e1382a0f97452119adaec77253b9017406988f766087adf6c07066f46c394e763094a98f419ed3c7ffdbf4010b3cc6171320ec2c48eb746e668798a1a3db85987d33c607122382c6ba4d900eabe07770b1e8c000000000000000⟩ ⟨58,0x215a1221bae5dd0904a1f4b55687c259b453dcf7a0e097f16298a00d06253f364fa2564688dbb6c390b72122097f1f88c634187323f61e6a1bc4181284774332dc84a1d0b0012e59e0c3c5f0fa78dc28152694b05643fa02363a45c6e716d24c68abd79e9bd8cc167294da5fccad962d8a1ec215333c09bc7200734e9e5b6661db7ab40df9a1fd47c1bd18a7cbec2d55514a0cbf24283b5ed30d1f1ac1361851317164f13c15f44c17df38a9dac312cd1018d954d5c49a3ded3fa6f3f11d61c5929d7a7c4442fbab0a9bad1014f163d1541143b7a52755ca4190d6955ffada29cc2ec2b4501a5d6d09afd8f857510bc1d8776cb590ebb04c18162e2119ac0725253c416a11018c893340b68d81517effe4f2b2a09695f8c1bd599037f549fe2298441308c574dc4f368624bfbc4ff12e41ea39f8c967a278950a9943d302a62c7875539d6b3e8d1375a2a9856ae0e210b6b6b674383cd9518306571c⟩ (i-240)
      else
        if i < 336 then
          cubicRow 48 21120 52656 362704041355669484164520 (-19504556225562818984585) (-25792873203370597019557) (-25751605172575830676865) ⟨15,0xa2013e027004c809601260240046808a010e0210040807e00f601e003a807200de01a4031805700a2012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨65,0x1da99109d611c4b837f682dd5b806aec3b4e8a12b8bdb04a31971cdc307f3e8324647a336ef8c6909893d253772209834faa643308d860d769913b5aa9635aea95a7302567096c230b40d20d3061a9b435d4fd741a2c88386f0358ad462c11b7f98d3514847926578ecbdb8a1bee7211f0e84644d521c95fe6752952decce654845b04360f80cd5b74bdb01799230995833ef7df1ead65307133835011e612ef6d07bfa2bc3cd7d6ddafddfc331cd86c224d6df485308d6dcb9eb6b8eac49adc34309b3d0acbcb3fe1c80d8f61892ca353f026c02c6ae2cb565cb75c1e9b7adaf34ab1abc8b644fbf323b9d47a7ed155a66b9c695438376073a909f414d0439954611699ace78e526386f5ac9d7fdbfe1074563e2d04183c2befdf5b030cfe0a243f903f769458a48383988db546d7963fd06fd4576938d1bd0e15592a037608f31b3689942433dbf65e740ea9a3e15ee9336becfc9cda681e435591fa35e44e2014812db5103dea4ebf8968a683dc32747f09f544c083da9c62bb90eea0000000000000000⟩ ⟨60,0x26681f5fe3986404634fa46a8b05865fdede1e50c595a73e097b667a118a82b3056848913c08ccf5fce12c2aa292ac4bf9b51edea94bfc011b8c331a937c8187fc7cc2a8f54b72647fadd888b67d3be833430800e039f2176db275c29a0ac59804c6a39961af7ed21c5dd24e9743f9c2050e87a29031d5b443d0b065121f1d236dbb0070e2cc923ce1def098087861332c81ee1f439842bfd7da3b5a2152b200c786b4a5972c2dc26e10b0c111562a7c297b77b314819b510764b3f13f53f8e27139071453e60bbc6e993164e86c30393bbb1ab3cb56e509ae32213fdf2d61d64f2bfbb107b4a2c4d37d526c05a8e515450544e5796e63552ef43d18f4949160f4c85af7f07b76e76018d519c58d7ad1ca281da7e798565ce473b764a38d8eb595d36557f92a8527539f9d45940dd68a4720805911a0d2de2426e389279c489dc92777b914c2d081c1bb67b25711ec408a74ce6c0dba8e9df92a8bb7f3ea53157000000000000000⟩ ⟨57,0x8be8e560d869f1b935e4d49a32d656b56d61759578a8a4cc06ba2f4e5315b3d5868f93c8fbad81d2c9e31c3d947200e89b8e024abdf57723210b50730c2ade640aff7a578a4f5b87bf6ad128aaef04cac180725892e2c14faad0dbf63182152fb8a76ff8cbfeaaee1c697068b984fa39fc3a346ee9d93a7a0419a2ff8cb4b6fb2e2a4465bf2ef812b115320198db6f21b37a240ab09094d42ab431384027e523b653bc0e0753afbd7cd1bb0369b18f8db3a3808335e265de9940fa883191254e417adf702bfb0e2173a45a8cdd8831195fce2c65e290b09e9b7a149d906574b51f49c56e36dd31f0f79ba61c44d3288b65018dee685320ec01c68cf14fd68e6822e8e576ea848cb1314ce77ee91d406cd68852f8ce881b5ee9b3ad948a026aff52100e488a8d6c7f0ec85cca98097c15d8e9284738befa69e535ca54b1dbd1635bccf6b7e394b07e6483d3e050d86b7648e2256e87ab⟩ (i-288)
        else
          cubicRow 32 12288 73776 291655006754160237483513 (-14982752744385876191712) (-14973058451009727111152) (-14249659262930644126464) ⟨14,0xba02d00ae02a00a20270096024008a021007e01e007201b0066018005a015004e012004200f003600c002a009001e0060012003000600000⟩ ⟨64,0x3222c2e491d479d0bc5346b9a415ed718d00a87dd9edb05293aaf87aebc16633c0e759a2361c14f50664f97eb12eda7656f208e09da48857a67ff11b36c6e6d8ea276344abdbe15a182d5364f0ba8a7b2807ed80ae12675c1262a8fe2bec61dcd12228b5f3ab003d5f691bbbd612a87db99d0e99b17733bddd6a36a56338785dc9c6f8cdc756605d7ef8874c0c0b859cfe9763047f5da47c4b92ab51138b9d1b6a331314526f605a601f041c406880b9345e951155051c37ef5e18dd3e7963769af036c11c76f0d542514926731a60b3f22a781aa3066412b8932cc490666891a511e8a6171af7f0c89e7c959e9a853035a3dcf8f2893c10000000000000000⟩ ⟨59,0x40c76d94a2eac58eb04a80604b0baa7b862efcc6efc25ece6c9a95d60aad26e3a8c3595009bc2799ff305472b853737d817074b6e701c180e5369ed1912395cead7b58055bf428756feaa5e6cbd125a4fc4726d26d6b783686f78a56b5da3dec9ba1c7aaedf5478a8b906f514981302b62743c63c0a61f97d1bd259090e87f998abdeda1cd9b80165cc9917cc3adb2ceb2de9bba487be23e1c64e77af3c7acf28726f4517f29b9714a6ef7e86c282f34efe5afbaf8ba06897c8d616f0eba2e2f68f0c49b4b863fe316e84941fff53a74b2d33318cae2f93911cab36e3b514adffee4986f2800000000000000⟩ ⟨57,0x7525558088b25aaedcc5f0aa1abcd1ee061b3e9b1de66503063aa4a6f20101d6a75b582873c483856cc25c0671e071e0e154204f894135a4c01d22c015f2767f144268248f57fb0c931dceff3cfe074e50a909480e040f08a53249e7b22deee88c3e0ec123676bf7bfe8fc947b18cbba895e49e2dc95756ef223e0a2207dfcf410f654ef55082d47c491a06c08f98369d80a6f7f198169e06b373c9e508809a1a25a121429d5ccaf63409605f1205ffe715a057923d0396cf9c76eb8d185f4ea264da271057964f490bb1efc62f1fb0ce6dae768eba5f0649bf0245997310616db47b117⟩ (i-336)
  else
    if i < 608 then
      if i < 480 then
        if i < 416 then
          cubicRow 48 24576 86064 247449536295833990054185 (-28499319442615901472384) (-25377136499937182156214) (-20977825967746643421536) ⟨15,0xba016802b805400a201380258048008a010801f803c007200d80198030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨67,0x31a1aa561aa8435a17686fa9ff4162a6c6321abc35b8c523094ae6eaae890631ff3c8472283bf59f5bea2beddd6851036f759c70a30c367ab21cbe7bdb14d72b84269923ea4dbeb738469f4c9b674b1755e74a6e24a3ebc9b3e0e57e4464a653c193ad4fd5cd90314067345cfbff509f8424a37c079b31c625f6f096a4f5088a68d05e05897ea5493faf2fd4b0afd3576524507f3ebb7a05958cd000b65d9f2caea783cd9199cbe22cf96e412e70c47bbc014300e72c324f62d340c2745a678fe9594dfd9c1cf1213cbe24812661c86653889c8071572f3aab6f00a1fbda6a3e6b3d9865ed7ab5e751f1a97c1d1b176a41ff73ec30a333bed5987e533df66b47cb8b6ac4ed1cb7f42cf94317e9796dcdf959a70ee63e491eb5f6491d59e28986c6e6f45bdadf9c9f0088ca7a2d507819585414bce828a6c30b62ea5b71bce936b37b89f3cac897f054c84250c148b2612a21d35eecb84e3a11e697e7c8d3eb453ab309a04883f8386f09b0fb406edbcf08171d11e4df739960772b16683d07fe5c03dad855b8d57e1c80000000000000000⟩ ⟨62,0x4046c3c2c88083a9d59ea68daf02cde9fddf339d18f423300b867063586a70d6e325226432120b923e824bb32fec2e9ccfdd581aee61b9cf274a2a2bc266dd8711fd64016c133574fb87a752876b777751c0ecc77ba725a93cc4dbc30c7d835012968c22316c3b38bd66c98403612082fe08a84383dbb424b7916110021b68071cedb3b42fdf4b90f5e2cdd15cdc275eeb7a0dc7e36b3e5842e9d72927fc4def540bd4ca32774cd6d4b553bab7b447fb5ab9511d06b98cd249df4cd6037b64c13e1d5300f47c2299d095c21dbb8efdc5ab58ba649a532c6c676906267829a7b94db9977b29e9b540372f72302c22dd995daa000ad83000d77966ad520e46b97dec839b1cfc861f97bc4a59f9c17a50decfe4d06ff6035f797fa2eb60a7d805d9c9558b149173772057ecbe688d0b5b09a350d47c3fb564c2acc58cbf97956f1a5c1d22f995b511ebed156e3e45d12dca92ae48fe0f367b97405459ee1c995d267bbc2386b14353e20ad72fef4000000000000000⟩ ⟨59,0xea5196cadd840437d4b483d83b368e53f1f90998bedbb6b97501c4e16334823748af4d122a4a5948785ec024412a96eb5b2ace18ca19c36102a66e347f124b00d886c99cf1c60175f861897b3aa1bc418b3a61014cae1608083f2e155482b1dd1f9bb15ff2447e260d32fec96820c4e8200b620f1f3e2770b6fb191ce384ee9802260650009cf06a0986f19f1362ad6f3f0dc8a260f5258604c6bc4a2ffc7e53b54b88f814bb913ffd51133760b0ef862420aaac34167184c3d530d833aa4f0871934d89063f9c0ceda051a56f168170bd00d1e79e6827e8ea005fea148425c1b9b5d920a06792b7fd70605a0905982bc6f189c099d96934aeb5c00141af067ff375023b3eadf4e4e9d098673a9242fe621dc2ac4701f7094520e9ece1a48358d38a2833eba8eb20ab0f2818a22424e65bcd9202de94b825b56939225d9a9831901f672873ca9505f04eedaa88ec4ca64b4bd3d325e4f41ad7998aa87a9b202ccdfd⟩ (i-368)
        else
          cubicRow 64 56064 110640 172595254385534263004051 (-47855671000797923050895) (-26075351970577455872042) (-17883478231102689759909) ⟨16,0xd800d500d200cf00cc00c900c600c300c000bd00ba00b700b400b100ae00ab00a800a500a2009f009c0099009600930090008d008a008700840081007e007b0075006f00690063005d00570051004b00450042003f003c0039003600330030002d002a002700240021001e001b001800150012000f000c000900060003000000⟩ ⟨66,0x1746dce99519264016445f002c1cf0d80bf81ded8dc676200513f86e2c8e47c221e430b7e2a638cc30a6023e3733b160fe35bbb259958f706e90ab02f3899c0adb6500d89c6178df56d97681c622ca8dcd366b296045196e0d189e1c529e196d88a4685457a2fa8b8ff77a45de30488056bc7a9cdd6b24b7f81629a9d452cc33fbe72beb0b1a1bfef17f74d2e384764f5ee8296ebfc69c8dc031afe9b15347fa5f22dd5a2c963bec124ef26c5b2ff65aed27093a8ccd11badadf094cb6b326c813fc24ff896ca988940b0d88232b1c31b585a6fb8676c1fce04f57ca593c2edcdd5ff4d7bb50cb37d21b7c6717f992a8a86762445b7fda9f8daef6a7907b2024ef89e0a1601c0fe78eca95e52d6b06616a71e2684b69445639d7f9f6a3f4726d05f17d450fba6a0e40a5e8da539f7d0bacad3dd115e27b248149c5e46197e2ff2ad92172334d051ac1f7a6a9e751583208360ce584b6891d757d8a759be4385d0726e401f9ed5814eec5593dd3f3c4ab1bfaa6579e3dc694656b6b961e4e33a9c67f49e51fc5b5e4dd19479910e4c3895dd185ee2f5f011d5b36cf9f84ef6200463b1f15df1c7bc33ebc04c777285aaf8b56dbf81d9d6c6cf77decc8e35b2dca049c97918553914446e24fc82cd40f4ed9e2bfcbca5cce7b71f9955efdbd26b2c02bf4ac3f0bc6abf3e22bae8c26d10258e5d8b194f3141ed33dd4e68f41650210c085d401ff5040000000000000000⟩ ⟨62,0xf2d5eb459215fc4716cb9dec40d005279fa8ed160e5dacc44632123effcc538c7ba0a15fd7aecfb6492e128c9583435cda17586c0b5d19a7c3775bbc8d5481790cf76ee33dd21f3818ed35bf0d47b10c92e87b6455172cd4f5e03bf8d42e274d2d8e81fbcfc372de048c158f3a642670e1659c74d3f128275d5ee732eecd8a80ea714d4a130ee09a3be6292130a9381a41748c66c035b7b7325ab11e00ec758a19a442757d6232a54b3501a6b0c9ebc1081c1a650ee57a8cb980ed5db823cd8dd605bee516679c79701ef773add6cfda009adc89c88d576be2e28ec3855d35228d4ef6f44ba544b03bdfbc64fa1683b10814dae5c6b9b729939e7785408b98aa4cdf34cfa0fc8eb34dc777b8c9574adc18ae2f03598b4b40829f3f7c1f41aa8ccd7aef221cb899a0db682bf9bfaa0aae55eede21cda65f59390c5164d60ab799aaf68864b222397b1a345c98d8648bd02686d51460fb3a41324ebcbe0181e098eab7d17403c25a2be5a595f4361dcbba7ecbfbb1721f23125fa294c81a16c7c69db06b292d9f87dafd9914c503488880e4093386d4ba332f0cea4f9e90591572d80f432af0eb18c919cd18f85e027db7ebf476e23674a52ff9519c27a9012aca6942f6687d4a964cf4f2ac4bc7c746a6b333526201c69ebac98d5bd905195807154750a1e0376d7c000000000000000⟩ ⟨58,0x713e07f1d2999598661e0a7d0aec652a890df1b4c4d111bc5ae607265e36ed0e37b50b030a88be3f4465f301e1198b6fe5cd684ae48b0524fe84081a0c2e637f730072f2f9e90211f0af847a3201e5444dafa363aba21f1b26f448f8b53ec88a96031f930212876c7b14a81b14b836a5fb7114e332f02cb966dea34dc80f0d720efb93a9f907402986a4f5c295f21e41a33f95cb03adcf31d04486bc0eb16cd41e88a5367bd90d0873772c4db69b41b2bf960b7d67502babeea41cdc13f1521069938a54f3ad876d5e7def3a36c2830a8ee9cdbf5cf90677a633345ba316127f7cbc5af8db7da28d9642311eae5bb6da6940d2e270f0b38451b66f23b6b40df380b99a0d57332c68500376099a7fae3d6bd08789f106b418d8b22340fb31a7aa5f52fb2e73ab98001090cd014c03c5096471ed7e79ce77f1293ad37fa86aec4cabf2db8b449793873af48240b6c4e882ac7706b6613747c6104008764bdf15f33570989224726c92f60c243cd7281d42b340f5c90c1dfea72035624cb74268710adef16c3d1758a1f9e509ceaab45046948238491b84016d12cec7140c844c74423a7c22f265d91df701d37cf905ed1a6be3a1590691e9e519e0ddb6e5ad4658d0397ec9d4b91e0c86f1afd7f1615473⟩ (i-416)
      else
        if i < 544 then
          cubicRow 64 49152 166704 80780753183056194321205 (-15678664911815000337728) (-9489412810667016410125) (-7326180868106484692736) ⟨16,0xbd00ba00b700b400b100ae00ab00a800a500a2009f009c0099009600930090008d008a008700840081007e007b007800750072006f006c0069006600630060005d005a005700540051004e004b004800450042003f003c0039003600330030002d002a002700240021001e001b001800150012000f000c000900060003000000⟩ ⟨67,0xd18cd85c73164c0065ce0df895147ed81bce6596d82768a105ff627447d9a6b4a122e8285ce6a87c4c32c470895c9d215e885e89b8bb81a0f04152bb6d347ba4950c33dc0ed3ec2df514c7bd5e7d2506aa9af1219fc7f200b9e3c5299be716d7ea0a6e65e404229f61384c30d2d00186aa01ffcc1d25aea69fdab038c3fda916e09d6b99a68aacf4107e427c0ed2ad1e9fe48244e4b27f53f690553acdeb54eefe1c741959684b371fa4fe03c141ed79004403fdfdc53fb13e30cbc11f8bfb56666ac67fc2652806d3f08e5b1fc599961b4ac8a73ea550850b7fce693f7c6c056d725f75c91a5a6b2dce8afddb025ffaf699d77ec3961592856cbb79eecf6125114b1779242b8f49a7f93eef72b9c633e050d9ddda16afbc580b8e83b4f8feff3433e07c755e47d0221b29d66e74e523557416cd29c5ef616ae6fbcfccb76f95a780620a8ad6bd4bbf10f1151d98d0c1d71ed2c2bbc91922397a999e1f5bf302952292eadf29ae5bc4f0c712d3008d0adced22db33b50d2d470a07f4f1fb5fe0262fc51fc2a6826b546c8adc6df72f1dfc8211f16c92626b6ccecb169efd5782cc99a9fd46e179ac01322f50a2f53de43f3a252dbe87466e1a80708e9cdd8fe9e506910f067cab334e5c6d518b0bbf86b53e018a2749f1fa26cf046c03bf492709cfb22ab8566d81bf8779ef54072c0ceed0534cab2085d5c2bc374a4e6c07b42e6c9900fe00803fd22621d4febf000000000000000000⟩ ⟨61,0x226d4cb67e76159a0f32600c85ae20d79eee6739346d8af07def4f56168b78f41b6d30d33406d1cb02f7d74fee96d539185bb2737f788fa63f02b7f897d135e1778799394edc5e3983fe375778e4ad362b155717d2bdb51084ad50bed04cab5df4829bf74cbca1bd206dbfb8c8fef0081a31fd7c9b83b0b6770de7c7755ca8d62a9f0f84cf1ec67c05769dd11834cf4547a2e5b3dff8aa1c9c6fb2f3859f0e20dd94431ca89670a6b84e4ee6741951b3faaf959b7f09a79087dbfa2b3abc1c0225fb703f553a5bc9ab7752f7bd3eba91472de85ded54ac618e856db3b39bdd7f00ab053f44910f077ada3401620fa9b2492648b9037af467c2190070bc38ec622dcd1c8ae230e2fcd120487ec1fcd5ed7334e52f06047194e3df330b7e22a84ab3b9e2d1777a69aeb41154f215c662f24a9bcf1740c5e4087560479eb807bcb02ecca7acc214e1e992521fc7fc6ec2cd5c8b50e0df913c7076be2a17e3b153a9cb265ed9c2b49e467052c0be0826f80a039d3a6337e7de81679fb58f413f57d5c09904feb9f920c2374bf81daf93ba51cabfeeea799c83d8119fc743a97fad97ff6e589bd0e851773f09fccf8581c110e7ba05e9859bf9ab4eeaa9d79a8c4641ad651bc7ab099b7779c7095b40fd2635b227a435432605c258a73fd3d8c7ae3e0000000000000000⟩ ⟨58,0x83bb1aaf0134c31e029e1fe45df9c6c9e99e1437e6d185e366d10b25ce569a95c39be6f9930152f282c6a4241ba19603896410deea58a311b9c82e08273c4dce1289290f3849263c21b9056f3869c7d84b37c73ea3dcf80a5e9a6f4f8c3e0090f65386b35920580b7663736f8c33b60c6b3a913b1400e265115b3bc6ae4d2d06bc8212114c567d6517f49c47a07722f0572caedb1aab9f31cc7a799b3dd9e1536c13b6dd2b34f4eccc5be113cffb3f3d9dc2065e4650b7c07a96ddfbf46155be795c3a5d237b4ed204c6374b39760b514ff75348d85f47a504f4e9a97ae8b20f9d3e74baa41c0c8950291dc9b11129540f1ce7fd4bfd14fd51e3b65e8e853bc497bccda12d4d8e70a800631e52eac07bd6209f14944b8ef28b85a51966584debfd5b42e7735e928faecfbb14025eca7fb3a6602c9d1b912cd54a2f4ca9191d2fafc0aebff365ca5ee93fe02570322b40f8cc6ce1a46d5c28a3074cc913626f9212599b42b514b6a69a54901aa95ca22b624c20729f77123d30128379d30ece6e0762ebf2286cad029374f07610d958d62049971db14a427fec58e83d1294081f82c80a1b45e6ba23016dc499b58b6bb7e38e6e7d07e5b71b1860a35707f0bec63869e6123259e105bac0608684c84a88⟩ (i-480)
        else
          cubicRow 64 49152 215856 48286494592467692880616 (-7326180522587917839488) (-4961058967791893423586) (-3961396417844359602176) ⟨16,0xbd00ba00b700b400b100ae00ab00a800a500a2009f009c0099009600930090008d008a008700840081007e007b007800750072006f006c0069006600630060005d005a005700540051004e004b004800450042003f003c0039003600330030002d002a002700240021001e001b001800150012000f000c000900060003000000⟩ ⟨66,0x816eca785cf2a6807dc796d29c8bc8c044b7e1c047a874a01da5f2ef1f47e3f00b3c8a66eb15d09b83ec26bea8a5d89f614b2285a37384c69868b8d3427fe51c2220124d7ec9bd8c9f09932335b6a8cd0d42ccb9d13ff0c40240cdfaeab48d24d1963a55b7164a92210d10503ed7620fd538048318ae3a80eb7c513c64188188fe9e4a55e9ad723107c1b617259900c784d663c6312b2bc10da4ece9a54b2d10afba308e6f4b8b0c5850c3041d3c9f9cb112e84107a3de3f612972bd01fc92bdd4051967d4839e8d7ab7f5875c21e8f9a9a31ddf7ec8b2de324b8af973ea38d9b8cf287b142890b839b714d5758c24abb07a3078348a29416511e1fded061253b00e62dd9bd908952dcb6496b53712a5369d16c7bff799893f1a839727bf9e8a49cfcb0d906cf10e9062c5f39b23115223701f95814af6c968a906777519e9b71a1b5b0181175be53c8298c01df8f5dbfd9f77269ecf50c0b1678a984d0813556fa9cc1eeb795f48136c6d0083b43ebadaf719a78db42d944cffe5fec41593ec25546963dcad6c66f932c251cc9d1727dd4a3a929ed9242f8a5e79443137b35c4217a828ee982e333d378cec344576eca1f63e418b4156e083b7b698e25fa9a707403ba4e07ced77d1246de5be18df1f8c9d3d4fdd84bfaba01f581ce4c0db436801d4d89638246d190aecb844a00550d628181c2f57809cd3d174025eda600a292916a6fc35600000000000000000⟩ ⟨60,0x15440cfbe37d56928b701c338806c53a632e212601e854a53474fa4cc75558922e012cfe2e3652af45442a84af7028deaf0fe0987799764cabcceb5d818232c5261424b87f52a391c9d3678cfc5f679af705b90a41fd6fd1591b92f8f159905852f94079335ffb0f9593dcfe9ec3799d7928668f206ae783901143c82ceb38f8c8b3fb2c92620f88024becd6077a58284990013008357c20989e100618d74e500e4417d4516ce0cbba610ddad642339f2ce3bfe35abbd2db52a32fd50ba6823a291a29462f14cf85e65713b2a40ec90104d12fbca0c2c666cb723f73981756318b17eb5fa3e3d7d770baabb5c754214500b8b8b8be016900d2ca9f6e8dbe3e199e7002f9f571825fb0783f03e330322f1413dd8924a3e26d97941aad2049ce3ee490233ae5510c89c848b18e5fd99ac163a59aa6a13711dbe8336473a8a38f6f97bfc7c831e6e7695e7a848c665c200b2c28bad8e5c89c378891cf3dba7a8c11096d9a6e35fc38469ab48c894eac8669d4735a655edd3a9e78753c941207e9e2e9f53e016e989c4f8fc566baa9898c09bb69a1e58c93669bac74c7e9a8c25de46aabb9cc82e2311e8ad23f2777ecf30be5400669de6dd41c2c94c59e32cbae65facc476ea164bf127fa3261c1d40ee28ca1a9cf516da9581a000000000000000⟩ ⟨56,0xa2c6759afbe03e9465db9dcc1f408659fea271b2ca78a47eec2ceb986b46c8f7cf17965e426ae0ea8b765198fb04916696454c1833cafb1c395d69e70dd5342dcea0734bbd7822a1415cbb821417d73a05739f480d724243d402ee03742eff8ad0c0062130947c5d350f4bf833f71bd9180a3a15e1136d2059f8fc61b075283940b84b30e52fa603feffb469369e2b40b7094b3d1f8d19db90ab43280d984c190748b572bb08ba014dc57774840a3d5255c21025cce356640bfb56907d59edea81c687c75cf0e7173aadfd5f6a73289293bd61581a98126af362b73db1e9538f6385301f3eef7763bf2978b04df96362852ab5bb9d626c69e518d1f360d9f0f02b29255ea812ad0847db5bd3f73909e1f3585a86bace5e7554389b3ba893f34f6ae8107470a549ee5f562e2f3143bfa57053e6913cdb5008f6cccf353dc71fef03712ce3c46613c8c923c9a2fa65324719ebaece986f2f0f45fdd16b320703d50f463a0415086b10b7129b04157e65708c9912236932349cf470322f3394f1e8a641d4b26551be68525e06c516916463cfd4d287e8f6762e1588838076897d6caf0bd39e9dc28ccdbf4734b30282bd37cac6c941835aa19a40e08493613c3b68⟩ (i-544)
    else
      if i < 736 then
        if i < 672 then
          cubicRow 64 90624 265008 32037858684243522015366 (-7303824448472612234524) (-3921587993400693446591) (-3022255735368231708928) ⟨17,0xae0055802a0014a00a2004f8027001320096004980240011a008a0043802100102007e003d801e000ea00720037801b000d2006600318018000ba005a002b8015000a2004e002580120008a0042001f800f0007200360019800c0005a002a0013800900042001e000d80060002a00120007800360018000a80048001e000c0004800180006000000⟩ ⟨67,0xbe3ec58a2b74e1405c57df7f68b42e40193291ce0be26fb2056de27924f1bdcce1070acedbd47abdc42dd948d2ef320bec078c6cff45d5f6bb5131155013bd36ca962ea31fedb527e77146f2effa107ebd66390394282979a153282538ed93a48c913825424f1eecfc439c68bbcc6b4a09c72a1199e79f1fd26551a76389bc9277bf7768147a9c3f63d36db8cb907709f50b868b50a231e267e84165b0134a6583e01843857129c9e9cc330ce732fd47c6fe8ead9786d4aaa2c01b37069ea8b5843d26c68763da66b5cd2da92e1239c9974a1436e23d39092af8215ca731815df76075feaf6f9473be0c2f4a729a02fbe0ad8839aadc1da859db3118208671ec0178f61de95c045ab7e388c231e01f2cdfeb04d7f7e95925eeddcc62f19efd10c39bfa7c5c17a3ac42e3c3066b31bb059cca6afc715a69325940526aaea9a0e03321d4463894f89eaae3c214ce6896f303c438d36c21d1c610fc1b12d55a321377f52c1729ef443d8798610c7a2b99e70da323ce366ac8c4ccaecf4f9bc7496216e868147f8aca5de286b148fb9c13f0b24614e17e8b18042d87700a254235cbd1b8c4f6fadd99798ba713baa388e1f97fc7a1e51f5dc3204501e42c03bd8a4d49fbe6848e1273ba8e66f93075b1be39de0c3fc60b8251474816a786c1146e91358ce9b8381882d93ae9e297db0200b168a1ca5630a024cfeb948e1c94500216901dd619887880110dce3746c662900000000000000000⟩ ⟨61,0x1f3de0b648bfb5f9ddbdb5d642d6c3555ef89c6479e5d6d932d4738ca431b811fbac4d2767d0c98f5523f01e60168a99ef217a7cbab5f8fc51369ba2b5ba9405974c6f33ce18e41b96db1b5b725cdd78476a520f9b56ebbe7262cf5cfd79fb758c0dd5e805cba0fed2aa07396e3122c94883f95b87e376d6f403c5a30548ca720cadf62e745277cae2ed96ca766942c05758f495862d554efa13b0eda7a39592ca5b01bc70b6e7c61c11ae729ee4c26f0808c41094d57b6884540e3d166d4abf60fa99205488d1a500642ca1e27a693256c98ca8dc12219abbf68546d2879a3be016d6e22c0fda3582ca44eb42e8d137db1ce7fa2a99a44728e89e11ee67db937725bf942f2705c763ca00c686ee7faf2209a753b584e996eeea433e6cff51b5939a5b7d6f03bb8db194c71eb3635765a8b45e6cc181192cc6091933bbb1a7f4b31646f17421f565aba195bfebd9bb4dd592a09b8585c7715fcbe575abfc03973f3353e8c4b79cca794797fb14eee413ca8e12569046f6b174b9f7b321b597db58cf45dc2994e3fca4784e000bace485a5b8081453994534d57d632137a3e2b4b2e05948f5a375391f0a7840e0f9108b9705b1cc00782c64414d8c617241022f9e7c51daf95836e8b221fb26c7e1570d3d0ae7e2f7b030b8e82d02842a354c2bc000000000000000⟩ ⟨57,0xeec100a06a233e6c6c286ad64c58b0d9902495c6a355cdbebc82ecc4899f2afdf66e49e42fbe3cad341861ca02c3fc6c8e7cbf21f7ec9bc6304d2c5520f90c1f1dab438dc07cf18a84dee227045d032ce78753721340955f435449a27030e076f417882453a96de21089764620b59e3e8d4730894fc37334b49ea82a8463f8f9d25816eecbe057ea968536ceb96575f46588169a02eb488a970f4851a5c83d4d0ad3321af474c35ee1fb65818c52e28c6213c3ff627daf8efce362c76d8e9db5724550fe2b2b3c795d5f322048dcacc430758e5a7d2e68cd20595ff85b35ab8f6cdc862b9a657144503458cc6cee7b2c2c8f658a9568010864f249ba97270bc498d3b047fe0313dc3741adbbe94ccdfd2d78299dfe52ecb425a7baab6d6c098e93914d96b027507f04552a54c76b8b5ef8baa88d54f337a1e9934291784d0de29912603d65dc81c43b18091d0d5cea0cedef8c1a21d81d7959005f11411b281810513e901442c8e2c68f810db74fea95048ae8c6f0d5c829850569d2bd14a22b18be9888e3c5a5f0682cd7f2a442a038aa761e1d28561eb16ec093cebd90900e25d795b148e866930758c264c6c700f7bf6d828de4a4dab091295cd13d299d5b7cb9a8a1606512a0⟩ (i-608)
        else
          cubicRow 64 98304 355632 17790190507001984625323 (-3278378809266781371200) (-2016107289749694945334) (-1576443619178855108480) ⟨17,0xbd005d002dc016800b10057002ac015000a500510027c01380099004b0024c0120008d00450021c01080081003f001ec00f000750039001bc00d8006900330018c00c0005d002d0015c00a8005100270012c009000450021000fc00780039001b000cc0060002d00150009c00480021000f0006c0030001500090003c0018000900030000c000000⟩ ⟨65,0xb756ee92438036016490baef328b458185def75f08f77f8150a4a46f40a72640ff58259829d3ab40b26510b5ceb0ff8075bcfffa4f2418f84a8590bc51df80b02dad5bdffd6f01b81b4ae9ab6bed77dd8ff8f0e7f3518c30c92ff033b41318bb85352264d1ffb4ecd2ea2c979975dfe4d19d11d591b6639418e27498d31232d02c7b136c3fde57d0e9425e82cee0089210a3894b52286d792792e75abb9a20fce189fedda51ec42688d541781c302f3a9682bfc035f3a815a3ed6e47598429b3d876bdbd93ee620030a761d93ca941fcb47fb23e0731d739d62619b0a9b4ab6c6c042d151f0e407a8750f6a2b83b17bbe0dc835a3ad175a7d2fbd5afe88813af06bd46d8843266cd9d365a6c1e191b3c96462bb5c6cd0a93ee50855aa42dc80a7c4c51ed25063537e72a69d6755757071e43e4bb28d4e40cedbd6a1189e9cd4cfd374c00bef0f9f56183e9ee5c18f7813e0aa1032c30702bc1bacb9815157e3a245fe11949ffd969bb46615a64b62af24f5a0252da344e7442a605d8b905f4acb0135809c8788d473f5e14a2e836f0f8b70b9b2be098c3e98d055abbd68b05f23f80b187af44d5cc8127d5d1f1f215a276253c2c2498e154af65a290c9cc5cc0e2d0118f339424f94b0f82f677340e2285c8df004289051aceb5836dbdbc01b2b48ad12ae4ea007f065fbd75d779401d4ffb59d893800003cd872b300835680000000000000000⟩ ⟨59,0x1e21fedc7cd300a737fcd4055581e54b9b95cf421fd1b4d25714937281f7e073c2526bbb0f2039aa68a0e4cb67fd02d04c51f25d6cddf2680a4d9fb9231e36ef2cd878533599d4c97d47283cfeca739d92e7ca0148413c20fd33879125fe97a7aa1b0277aecc71f549155bca69048e9c74782fc8d5b9d05e2868ef508cb974c3cbe7f976e715e376d218da2bdef4bae448b949db50b79a741eeceb55e5e806d6be9067ed183bb11d754c9b258646f9038f86194b44684150aefd02506d3eb80da39d992d8aefcaac9713a8fe5264748d3baa3339387e6fe01a43928561c9a6e5c8bd375238a77b0131ccc691030502aa545d6da1e129fbf6fd31a084832c098e119d1993018892bc7ea44fce8d4a6c3f5cad118a28954a9119eb0cff0508d413c24902eb39618c8840bec9962bbdd2ee71109092576a9704d93991463f59845d815056938bf283e0adaf0c4193fa2b47e0942234d8f03cf4c75b66d9bf0f6fcc2598e154370535512b5cb252950b5997739f2f7a22613c7073ec005337b4bd2e58de82468ee889c186f7b81bb189b653652d0ad9b69677ffada2b8f16cc1ad43d54fa048d624dfb1294839e274f5c7f003279a42dfdc02451879e6a7ba4ca058048c967b84270cd70f89f451114258b7b000000000000000⟩ ⟨56,0x737210a3462fa2697b4a276e0c1a5fbabf3eccde2456318f1412a1104ce0df46ce62cc43c9dce3e0418e3aedbc53c1ee6e324db9b6f3505c29eb182922cdec21c72331883d0619e32e90c7ec1c124096bb239f640ae0bf9818e9e003c516ac6ba8260310ed4dbd8001099fcbc0c4eaaf0fe5fca3b941cf15dd23c22e72331b8e00a045af9d20effe8215f86d2602b1a3d99edd2ac45a536907a52f332d4eb049cf334d536bf8bba13710e93f45f76f3a7bfebce232033d8c96d83f65ff4040a72002e989429617568c647b448ac106fece21461c6f16612f674748dd513f1ba5480db7f55672e548689b36f0d0df485712c2032fcf47d699371342b346e497a3ba585b457e64f564e8f343a14568518b6d414a69f0960d413e76ef9eb84c2d3b23defcefb52f374e2b689d68b132f2b26456c3f72e0e3ae52046a5289d749700c10b229cf71c83e0351c0941465799f914deb84549a2010d19a6d1784c7d04b63c4bdc1261044f742987b6360dfb749917d8261851ed357ed5982357255b5776322f0f849ddcdece3b7f93d89acc2648abfe55d9910c569992f93aeee2654d45782edb5c74cc2f950210e2851b927976afde9640d810eefe86a84194755d356e⟩ (i-672)
      else
        if i < 784 then
          cubicRow 48 73728 453936 10919260788806653200309 (-1182332663493145677312) (-903131325960128882381) (-752750890541200580352) ⟨17,0x8d00450021c01080081003f001ec00f000750039001bc00d8006900330018c00c0005d002d0015c00a8005100270012c009000450021000fc00780039001b000cc0060002d00150009c00480021000f0006c0030001500090003c0018000900030000c000000⟩ ⟨62,0x106fea37986a3700fccece18f3531608890c9b7855d0303a3b59764447c9415cd1213db5da5d0783963663904698271f6d044f256d28c33d10320cbe78e3aef10aac58f2a51154934af254d73a4fcec5fbf19b54f168f291b01ae5b26647679b060b60ef1b965286fcba9acc77c49898a6ef5e7a0269c97a725795c88bf7aebca6cd9d2406be0f64fa310c9696df4deacd312a707f835726125aaa0a57656a73a62329067bdb2a82e60ca6727f6b567fca2a9e9d2d1b3cb05a0a7b377cb6bd6492a9a54e09684b40baa44ddcbc24fc82828387897ae014cf89c5901cb8289795a5af8fe34df55caa901ffc341bd7a5ba224013b3062a9708023a47690e4af69dbced1f231ea1c06d1caf529f12b9d18afb086b63c3ee457fddf54c3b5c9c93407476644bac2441f6504795f97238dc2c4384ee599342c73dde196277f8889a2a926df393f01925a729506bf21043ad659f4fcfc6e09feb010379e210812a46c8b002b80a0138a2ef76906550000000000000000⟩ ⟨56,0x2af9ce0dc2248b50e605a85259a371ef365926d68f8e417c7706ba21a609bd133ab001b975aa27108ed7c8b3c6d94207a9d3f36bdf855e9fdb64cbf8aaca1bdf38f8849bbe8fdfa1e6363e4629dcd271e58a932bd6fe657bf3bb17ce5a7d0315ad5bc31c6bcf26bd07b57ae1cea6c231a5ad90f5c93d1393ed32d1a8fb1d80738e38c418ff6b7b7d272809a35540f2b707a42d3e0101483fc48f25f9e0c5da66050d6af51fc143410b6b2b1fba55f22446b006086d1c3ce4894d23c68855005f30b250d26c548b2a2fe522829a10680c010a9788942a480072aad655cfb5b38ebc3826d0cc4840cb6162639f453ad803e50c54cf02e1d003c7c1d9cce87483305cdff8eb9e8e32fc3ecaeaf9acbd7caee8e62fb9e71a86b4dce8da29cd39c8cecb710690f170bb7c16bb886992a29d8d43f85cc083d0b58ff255b85eb483f04ecdc032e5f4bd6813ac00000000000000⟩ ⟨53,0xa19f99e91502146ddff47e0b729ea1d1bccc1b38d0091b7ce56625636fe18d32d92290ea092e4ad8d321741f9e2144a5bf01e3e1301656165a3c23904221dd9ca1dc01410044dc18be22fdeb5452bd31d28e3d53fe7c93fefc70058accc7e9348a9350a7633c6f5f215f4358a8db4f1fea55939d189e39d448c0c66ca126ad4bfdacb24095b36f64afca97af68affea29e9585c263d796e6ac61fc8284a99763aa699a50087b19d9b1daec97d86f4ea00e9202be569404cd6475b801b02cf996ab5b229dd89145432104f67a0769360cf192569f4168f04ef327b9bf5f8e58c4134b4cd7f0443102427214c49574d13f69e309d8f382b2d100f5f0d42a022684852e037855769df2242e67b285602e5213b5b2f030e895fdbe85e98e54dddfd91c773c4876927d70bd7450b53a7ef27b4af3ef31969d05db44aaf253f1cc⟩ (i-736)
        else
          if i < 825 then
            cubicRow 41 102336 527664 8081045908812178060264 (-1044833889744929199336) (-753377259677967116427) (-613900524695404193481) ⟨17,0x18f00c60060002e8016800ae005400288013800960048002280108007e003c001c800d8006600300016800a8004e002400108007800360018000a800480021000f0006c0030001500090003c0018000900030000c000000⟩ ⟨62,0xc16fb0da0a98004a896f8b28e608136e34c039d62480e3c14dbd85b8c106e0f1c7426c75362bd5fe7639666370f9888ddc09102b052640a1fdc829cd99c914a594d4e3e07bf8cd4c2abdd15a41138af688728dea379feecac96d73ad4600302f05f7f4c4adad7495ffd8a34764a0f670f1598dc486e5a0338e8a38ee75ed65a69654e7fc9c56f5a21383a3c57b2658888aae68abbbb63ec485383377c1df252fa8d7d31e6a56514b532f1a687a5b9e50cbce8e3a4ff6094c2ae3eabf4746248298267297eb7443420cbd2944f7920106d4391c0ab023fc95c5308db2accd304c22724932df6e2905b502ffb7cb038371282e6485eb6a0b4c4e2282b1e0a423ea134b11a9db986d7df841b86752c13b5a4a3c456dc483449edcc1b6fc02079dc779833acfb80e04995ef64c14e00e81693dba0c238000000000000000⟩ ⟨57,0x80bd09e87af504ed323d61acafa601df78bb20045e9a0bc33f2a0e33eb80f0cac75dbbb5df79582ce94e77840b2dbcc52f6a6872ee425defbdcab607c48d63dc610cdbbfb5a7e9d03491917e81714ecd6b231492b639be339becc6399fa018fc81076bf32eecaffc452d7ef5048fad7f7e7d62ba108078e51bf90b8394ec3b83d77cb26bfae40ae0f7cf5eedc2c9d79000da255a270892484de64f14809a1edbefc35ab1f50154c938c189c44260c9ea50d855494cf184b472f11548dcd866bb22fd77ef1c9f1d69a8ecb84af4873b034dcc94d293845627bca099a9b08e7064dfc620ccd19c2c311d6e5f48200046588c2b57834946c1c19322a926058a7a0818f9294b7b83e3352eeb1e21396120c1bb230af5004c0db57cb4e4c000000000000002⟩ ⟨54,0x400a62f6eb560f5b4c7d04909b339daad36db4ca62b30b0da10020588b5b4d53565e9b68b4a95cd8f799c8a2852d01f5366c356ff280bcbda6a6c0f4172995196c232cbbc14ec02f463444eb676a5ae855cc60720f78d76784c5d1d5363dd4cf5bfcbd8178029460b65943e213b5ec17c8b38d8d7bf001885e3f3513c667fbb8ef55d6daf92a62baffa884f60d839665c7a9e955e363240bd65ef6a964bc81a554562c3caa9f58494309968fc5317ca5ff5cf5b3eb30bf20d37979e0c570b14631dda20a22d566635c383c18a62cc73741430924ec400e8668d1e6464b5e1f5f879388f9b8959a5b36496f82bb9c02b21c1e8c96955c39e13e3949aefff371290224b759ef610481a37fca101213ff8ee8bdfaa8⟩ (i-784)
          else
            ⟨630000,5668934234693877551020,0,0⟩

def cf : Mesh := ⟨826, cfRow, 10000000000000000000000000⟩

private def alRow (i : ℕ) : Knot :=
  if i < 256 then
    if i < 96 then
      suffixRow 0 51840 60000 219626166184256828161947225 (-173747156594723499212918640) (-31738333334427904553458027) (-9502458493464321518506995) ⟨16,0xc900c780c600c480c300c180c000be80bd00bb80ba00b880b700b580b400b280b100af80ae00ac80ab00a980a800a680a500a380a200a0809f009d809c009a8099009780960094809300918090008e808d008b808ac08a608a308a2a8a278a248a188a008700840081007e007b007800750072006f006c0069006600630060005d005a005700540051004e004b004800450042003f003c0039003600330030002d002a002700240021001e001b001800150012000f000c000900060003000000⟩ ⟨84,0x1921ed9d6c672978c05002c2a29e299c154826230039155e71277494af8b7003fd092f781ccf953797004038add136f011838ad003a19f034e558f7feaf9002d2f6dc38aba1ed87710019227f4b1bc526ee293000275cf73b0faba87d0e002615572e87025be5adc00524b71ddd2dc4b3c8fe0087bb9d22ea72c07273000c71e2280e92808f35d6011140c5a39f92ec6b3b001670778f290b97daf39201c96d18b0a2abb10ed060239842cec021c307b8b402b877b284a621406b5bc03478beb92fbb7da06b4e03e81f377b8cc99def24c049baaf3008e13340f5e60563c460a6df48cf1acec06421d99c877d337483a607388688b285123f92e380848edec32026e5aee8f209756264f651a55f140060ac0138d365bdd89e8b940c2b531b0a0a410aea84e0db9960def73b4335bb940f6d75e7f8fc6a1dd37e41149b1f327d2ed4a2b322135130937cbe9abeb778a158700a65018b8640f7f417ee5aef890ebc5abcc2c1a8aa39553ffcdb99428c1d5f6baaffe367ac28094207072cbb33f69ee61f4623c1a8c5b2451b8ab503227572f56f947c045cdb9a2b355bfbf8e381d69802a2f60b9d14bece86eea12633de0b894a9cef280d4be363cfc6502f1505ad36443774ce6fae461bae6fd5a3812d7013c0b31d5403123826b1bf7d03eb18413063830a011e618fff38a3a8383a8dd6a5503a030b23a38623f609c03a5ceaf50a38b187dec8620daa3549842509ac21713d3043b99e4b5cfdec73580a46c823c53d23a9a46fbf5e63cc545bac3337355b496fad37262e7277dcd719581432c0697fb8d806716d6ccb1826f72ef03caef395c36d2c74be3cfefc1311e6ce95c795f863e724874a4b62127d5524339822f9cf391d4809dec244cc1f9339837283393558c2e051c4b1b148526dfa30e3ce7d98148486675a43fed21639e5ef286fbab30c47ac03e2273086e576bc99294d5550378862707a955bcfa020ecec84c357a156673d8d6387482be181c66893e46efe66801bbbb085dc5a375c2187ce17fce2c5ceb957e2a2791576e62f6dc77fb085e74be92f57d294d04e1af86fe4b07072c79cfacf9806a90a18482fad2209639464cc39a30c1764422bb645ea2594437276aa1f64b4581efa5e1e20bda602c80514f40f134a378b424b344a41902fbb5e68b3061e24305a1b62a170897cd7703bac9e8b9cbb49c43a8de34493a14ce289bd2d50322cefcf28ba5b9f225691625b67f7a97ff555f4c7721eb5559200d30f97b8abe1806698fcc190a99ac0aa11c60904582ce31ef62880c12e222d229fd14cfdb8070e32a47c80b20a951e202dbfab70dd06a78efaf6005ccba5fcc91f77477ab0271f067d588de8caff350335cbeb50fd7020d71ef0276f7927b4600dccea63000000000000000000000⟩ ⟨0,0⟩ i
    else
      if i < 192 then
        suffixRow 96 36480 111840 4638217761641102877063563 (-6426377174210772378625179) 1878412252790530497959209 (-59412460826606898098884) ⟨16,0x8d008b808a008880870085808400828081007f807e007c807b0079807800768075007380720070806f006d806c006a8069006780660064806300618060005e805d005b805a005880570055805400528051004f804e004c804b0049804800468045004380420040803f003d803c003a80390037803600354034803300318030002e802d002b802a002880270025802400228021001f801e001c801b0019801800168015001380120010800f000d800c000a800900078006000480030001800000⟩ ⟨80,0x448b3c3bbcc0aa8ca20119084de4792d089cc4027660495feb7849285c045585887fdaa8ce03cc06af741d02a01baff2c8097d32481172192255aa0cb7d0f6f33c262217cc10586c452cd787860b0014582c044a50577dbb6018b044498f422fb84f981d59f601cf2fd98d721c224e8f8bb1a45507f03427876d58a8c77c5835ce2cfdfa94e46f9c9c2a3432abb1d68eac391ac06a388a1dd4a2ab9bcd57fe3e92da25b201486d135a44bf9406f085bcd2a16a4b0a0b2be29f80de7110516c12970e3912f1dfc457df917c12d5fad0fdf05e5e842b91c05c46a9ae64e2fd095430945ecb486b67258d22388cc2e3b071e53f4ec2712c307dc87857a51da00624eadbde7eb8cc249a679a2dce588503451a87fe1efd606a8b31bd7ffb873dfdc7aa913f00eae27f3fc474849725fa6099eaa5956aec9ce1b5bf1e057f4c913aa26d61360158c8867c72a7c44ecfdf6d0a62cfe6ace1f60d081254290feab1c1f59028de9d57dee4b66014ddc412b3d3c8a4bab8462f4db0b97191a2bec6a85ad1ed795fa302c28788d0130aafd7b3e8c5f765ac17e800ae4086c912efe430aae7acc18ccbd70d89834ccf784140ce40dc263f3ab6d6d366d04db335a50410f83550d1fb26b81da9b3a14d9ed34709e4aca4f6bfecccd42f71f917cce6ebed70d4b2b92a316067561fd0d4cf81b5c25f888eb8dcd484b917a64ff2421600d3d19b63bd5e3d5e6f62d2b5b6c66edcc8520c0ad130ef2d8c1a8aa7ae4ecf43821b7af07d7d6bd4ccee0aa6a7d93686dcb6ca3185a75952c244eef4c70f56161984626b8224c389499d08098dc88a9ec1a17f26e9cfba517a6ebfa19d5cbf09d477796ebb5aff20e83366ca07aeb6b87c35831f64c4052eb1bd77834cd9cb74fae2ac6dab86fd78792764c4a6cd2ce4b4c2b88921c8a0e06d0fd321b63bd7789aac3d07f056fa38f52c9435d02ba88d9aaf60de8d82bf21ff77ec6adaa886990adb2078bdf19bdc7f7f1fa94a76b47ca12c783bd872bdc83929e1c070d681fd8b1dfc9cda066956de562acbdc18298661c52851cccdacba6c7e5a2a172d5b5075a6fc18528ee24a334abcccdad84afd4509a0d29f013a20437f82c8378b604cbb243c206afa2a904d81485634eb5d69d2c5154b0b462dec4e999eb95136e8f4272fcc4ab38d040f863a20c3022993b3bf372e801ab3bea22dfcc9fe814c151077dcc5a7cb7f92dc0fe850e533326613950c0b4b1efe0d35e57d420c07496f2158ea60d122ee03f48bb072e820f1ceaa015e8254f27f849d23e80065d5eba34c9ec4d8270144d66770ed6644ab6b012a025120e097f5182b00000000000000000000⟩ ⟨0,0⟩ (i-96)
      else
        suffixRow 192 24576 148320 30840379394254098298709 (-37783985694842068365526) 8499246623727357350902 (-812209728583482700224) ⟨15,0xbd017402dc05a00b1015c02ac05400a50144027c04e0099012c024c048008d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨73,0x5bb3c11e302d04b200c2b3abd4f34d7c8680db6bf3c9875c0bf640c0a8d31ce3bd8c8d6093d0bc49a186465800683042ce960afc0fd84545c351d93fbd0ca82c214f8bf34d950dde1b35409d6c74d7abd71058814c40a87fb27b099d7af7f07faa58fb058ec69a0c1ee18c8ea32a4537619d78399f21c797f9be5d7f3d4938fd54d2e626994d71ec8b7c73ee1f9277aea24c21a299b2d413adb02939aa4680fe56c69a1629e335634ee6adf40bd65c95ab34786dbfc648a56e9d82da1fb8d3511a2d7ae590c51d71bdce01d8ee2c4ebe44e8e294cc17ebf188407913610bacf926662d3ea881b77db56c0de1a0487e6359d59b35d8d08fd387db03b2c7172875fdd8aa3a0b3a74044dfa8b954ab8ccc67a2e5cdceb9c13147ef119c50668a75d94dcd48d9ce91205068c0d3946e17368121ec916142354740d246740801f9188fb5e2fc9135d01a8aa42b72bca2fbacb34433712f847b506d37a1644ab5bfe1051c3a9044a92f7f80acbce007e26ac49ba3590f7e23cccfda70e474bcf129d214a92c776b1b9cc0dddf169f313cf9593e68e1e254538f9dd72d31333cf5a96277049e16e24e43fcda5b15874a8af743b43a50c66624ce162e0d4ab37686a229bbedfdfac5aadbb0f5b5501497ad7d54e06b3092b33605e8a1182dcff877e884e175a913172894fe88784f6507b3ede71060b33d5bc2fa64a2b9c1c4126d4115a4a249ab985873005c4d926b73e3da83681a23a53fba0d0020100505441fedb6a4324c005b20c9eb9c2a829b80ef7133218571597fc074dfddd2016b1afc2000000000000000000⟩ ⟨0,0⟩ (i-192)
  else
    if i < 368 then
      if i < 320 then
        suffixRow 256 30720 172896 743430594555904583861 (-953272496239524898667) 364075805180391261688 (-23285457648300466214) ⟨15,0xea01c8037806c00d20198031806000ba016802b805400a201380258048008d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨68,0x136b6d8d083edd9804cb6c505acb480040a7a9d241acac65de1201434f34d47ede01b1ce83ee1dea1c48258bb99cf9084e6ea310ca115f642392ee3d5f5f76a73ed5bf24a44ababaab0b53ca577e561147e4a60d464cf70bd938fb8aca71fc7d6d8e106ac9c7ecba1d4eeb5058808b04e331a63d3825e96726a1aea16c3488a0e0cfa75a72585c2a5a905dc859936978aa1f7524b8be82ca4ae3e894f50dc0c24cb200e7e0f8f5e09ceb56173f7e3f810832b85b526f48d3671eabae9ee4963b942c5cbd08fd635355492c6beb4857750fecb806bfe8e172d8e561a66c0a2c725990906bb4c0df4d4f0dfa399b8c09bf210b42a731f0bfd6a1cb62703fc44be8dbe6e66317b5ecbcc0273ef5b79b094ba6d412198f36cecab794ff6b465ef3da2b437ed440decb18fab05737a41e5e57f7aabf4b7f5c0c281516a712ff64bddb106daa1b562e6f9cfadfe49be00809b7b90f5549597f28ecbe449b828ee312e68619cc97487c85596ef0f733a6804fb396ca068fca0788243b3551ec559c706a4d0ae9242919068135ab0f7eac752a5f8a508a6e17f4a9656dd8174fc99eb7584e1cc6cd8a12edd004559996a94fd42ed83ca72c1ecc27cb312341a87db40c18e5b42bcaa98a201ef488223d0a1b9df381a08a1c47b634479a36952154d859d0a9b0d2600f022d362e55e9770098870e9486c767160505e5b59a305e67601a31ea7a6f48326800742383498806bb50110bfe5fcf8958f900000000000000000⟩ ⟨0,0⟩ (i-256)
      else
        suffixRow 320 206592 203616 130948445848470480668 (-150769901869897758599) 49365481490166253061 (-8560692067688017557) ⟨18,0xc3c02f700b7c02c700abc0297009fc02670093c02370087c0207007bc01d7006fc01a70063c01770057c0147004bc0117003fc00e70033c00b70027c0087001ec006f0018c00570012c0045000fc0039000cc002d0009c00210006c00150003c000c0002400060000c000000⟩ ⟨66,0x104f780732ea48b810bbcfeef36be9be093b4ed7108dd22703f9fb96bfee707de17f3560523683b3208472e7a07675c0882b2413f544d52fbc8d728f5cedda886c840d10b1eb32f8a2912fedba8bb5cad570570d9ce181dfbf0698734e841647059e66c018e0d4cdd3a219d5cf01e0c1ce230a7def1fe8c72a843ea1505d5ecc61346208b3b67d9b09f0c0723ec3c2b29713bf749279e8b22e4039d0a4dcabf092c9b84da927cf7256cda73d723e02dbc47e4fc2468a6d589bf497090520cec9808e57cb52e79ed1068703a70cd1ba4bb6be1b71d868614c657d5aff4841949342703fd134b404a3f22bcf6a9ca2d1078bc8f8a693ed8039487d1ffc3c393c0c20f9e5b3809edac27af458c9400658f88d25b65330e1bc8e1eedb0007c8f9f9d86a8adc8dd7e672bc16709a1333827d9f849851f8465dd7a420e811533a8b33fbc82b7ddd107ca0addc078ffb0ce010b27e012ae2bdade3e5c8802521c8bffdfb2b800597de0308bdd77400ace648ec6cfaa6000b7efa2363f2c6a000eb72ddcb722d7c0000000000000000⟩ ⟨0,0⟩ (i-320)
    else
      if i < 439 then
        suffixRow 368 189792 410208 20983333401050957573 (-7458120960135952089) (-3376202510049141334) (-149009930865864150) ⟨18,0x2d000ae002a000a200270009600240008a00227a089e52278e89e22277089d0226808940222008700210007e001f2007bc01ed807b301ec607b0c1ec0078001c8006f001b6006cc01b0006a801a8806a1d1a8686a141a8386a0b1a82069f01a70069001a100683d1a0ee683a1a0d068281a04067e019e006600180005a00150004e001200042000f00036000c0002a00090001e0006000120003000060000000⟩ ⟨59,0xe55137a6d1e8fc6b0f688f4dd8119bf9bc0a4c5f5175a9e751f9a905f6f928dc9001f0f26522a47bb286928ca4bc8a33a5f54367f1cd11a9e5a4ecd7ccfb625b8ecd9a5e9c0ba3c509b3421fc61cb47fd6670d664848873acc46707fe77a37596206bc7977269b18ea08af906c4f5e4f43cf07fd3cea9a427d18406cb50949758193f3f48f9cbef09b023bf1f81c53e6ea7d885b54e9677e9a290d215017fafe5ea1bf22bed41d28ba3990526da90a9b474cad7c92512820eb3ea4915e11b21d9cc7836de3eea52d5c4c37d0325ce227de9a8f296d9deb13ca2bef1713c6a5d91c73aa1678dfc34aaba6ae0f12f0847e344161de9289b8daa0f83bbe63a20d32f10777be2453ac53f0eef5f07d1f97ee9dde44b91a1dd933bbb8b37722bb7677761b85678e7b4eeea6ac42f62d49ddc3eac0c676fc3bbc388808dc062787084a07ce2d98f5abce7353148f1eb8a04853ce2643d746b95075ecda7aef3038d9ba984f6111f216284929ececd6d368c5933dd0102e79299d47c6870200ad03d0fbe5f96759dbe320f32f79d2c63324b28705c18af180a16bed8c5908e414b6686cedcef07a8f28240452bd0e4e312d5c0319a40903e8722a8f5e0500656127d6e1751b4990b1b0ad6b72c0af9ba88f8f044215aa3321e1e4c58a57d68686b930605a73c8793d5b0364ba220bcce5c060a957c6f5645a196bbc683747eb42d7d47d5bd684c800000000000000⟩ ⟨0,0⟩ (i-368)
      else
        ⟨600000,10000000000000000000,0,0⟩

def al : Mesh := ⟨440, alRow, 10000000000000000000000000⟩

private def auRow (i : ℕ) : Knot :=
  if i < 192 then
    if i < 64 then
      suffixRow 27 65364 45000 283124764924540058297577109 (-87851243773220629028815943) (-175800186354245688334841172) (-13974120487793632108731711) ⟨16,0xff48ff30fed0fbd0f8d0f5d0f2d0efd0ecd0e9d0e6d0e3d0e0d0ddd0dad0d7d0d4d0d1d0ced0cbd0c8d0c5d0c2d0bfd0bcd0b9d0b6d0b3d0b0d0add0aad0a7d0a4d0a1d09ed09bd098d095d092d08fd08cd08b5089d0885086d0855084f084d884d284cf84ce84cd84cc84c0849083d080d07ad062d04ad032d01ad002d00000⟩ ⟨85,0xe30e7fbb895b0322800032c7cad78c4f2ab8a400134ddf69298e85471ba01ab32222c8c53d9ae17d02d018ad9481d22a46bdf82f2afb97004b1839eab542818b5ed048490e18a9f61e45e4130211221743fa7152bc783f679fefcbfbd98e0837997be2fcde084f1c8f0132fa0d7fa0df494fa5854c2cd3d107616552ad353d46f1921617f8affb19f739525675455acccd07d245717336d052513dcc62a76cb66085b994a4ab61d5eb5ad18fe80016543f36b4fffc1dac5cc836b80de5d603b042f4e049ffe573f02474628a455a80acbb3b8cd29a7e9915572755b66cc3bd4bb54802fbd6dfefe8fefdebb70136c46867535e8fe6c40b4e5a8222319ba4346a576198da898696e26a660198184d2dbdd9973b8a093b33482e952194fb0a2ff4d1f01296f317fbe105e3912d68482f84facf4716413ddf6ee15bb1a77bf28c8e59d0260bde51bfeb3a009bae88fcd03a77dfa3ad86159959c3ade25efec10a1cc797eac0372daffd3eb0c8bc0173981ce3ffefe40bc959ec9d0e44edfdea5fd6cb272e2c12279fd34d705573bcf3924cac7d34e1783c4d8a91421abbd9f8f4ed9f74c1fca2ff7e2b7153f3c73f9eed84eeee4e1a2618b31f408ba4a7574ec515270b41e6a1ecb9cae737ce7546c87e0c1fc620533795e199839156ade942cd58ff88d9b378eb6eb2d940d9ecb54d8810d7746461e0198114a5dab49ba0bc45e49f1cd5671642dcfc44ac5682270cddb73ee7c87fc91ccb2f95be34773d76d5968a99986d7dd3b9e54d87f41c393022d0bdccc34e75869510ed41d16e1964d7e81f7f5a2aa0cf674b70020b8053313dc29a15befd75fce83e93db63c00ac0a23340c323bfe6bc8920de31b34d251eb803e11fe3185208f5bfb67b1a12396ce4fd3bc29dbe9b404efe62c1951b7d3f5b6a001ad589339e462679d0e4000000000000000000000⟩ ⟨0,0⟩ i
    else
      if i < 128 then
        suffixRow 91 23676 110364 5499214309280108825188283 (-5055075119437239455149042) 108908559469431420878929 (-296331305443184774996346) ⟨15,0xb5f965f2bfe567ca9f94df28fe507c9df935f25fe4a7c91f91df22fe447c85f905f1ffe3e7c79f8edf1cfe387c6df8d5f19fe327c61f8bdf16fe2c7c55f8a5f13fe267c49f88df10fe207c3df875f0dfe1a7c31f85df0afe147c25f845f07fe0e7c19f82df04fe087c0df815f01fe027c01f800f00060000⟩ ⟨79,0x403180130aa5b31e28032663b7435f2647cde80f89732d479093471ce038bb545be659a0323060b1c73521cd4710e52c81fb7e5cab51daf5ae0585503314fe4f56b0a1e80d9b26e878d08149595a21a834b3970df6a698dc5105633b633a14fdf440bec9b3241c260f09d1f1b92453eedf6977b36f23ec6afb40746a141af648d0e0dc08730cb4f6c71395113bdec068c5ab6b2b0ed738ef2dc1480a105dd31cf7ab3ec8534fe0caca0943330ec6a91f71b311e79bf902923b3c239f19bc9e45e2217a1fc7ab3a50096067c78a8e10251b90e5f772cdd8e521cdac8d79429a927dbb4668dd6223ec18e9bbae91ef52cbf469f285208d2d0b4c904efcde27ca526a2ee17c17f711136884efcb5bbccff8261c658a0c7899fab035be9fbf545df9a89760576fde1ea91b3a90e5d9e70a1a66529d4ba90a458c6a6194a55597c6b33b91dad17549778b84365e6a81bd1a8db072fa0a2f0f8409150b36244a51a7dda948a9ead1cab483a69f8563136839088dcc1f66ee3c25ca2e97ec4b1781c0d24933a16226f49221988e8d041b49cad244a565950e0eeb68991b3fd8639201ec287c7f06558d8793cb512fdce1bc39ce64871e1bbaad1b710397650d3e0e5717a3581491401869ae3005abf89f5ac32c8b697f10e3c4b8f6fc5054f09e40f40b81e5488eee7b8ae565e4df1aa0fa57dd98fe1b2e1652c1ae5bff306e04a5c6bd82d34749d3fbc3f527dbc49df8877efc11e5532b8747b18776d59d1d32240af2a94bd80b46df3eb60f69dc4a3ea3b8d3260013ab150ce4db40a47b281551533d3dda7261883010a8fc37badd3e403060049d9d4a54444ad56800000504c79b3dd08fd50000373835fc563bdd7f80000000000000000000⟩ ⟨0,0⟩ (i-64)
      else
        suffixRow 155 24576 134040 256716443869116015921824 (-291942462029847850383574) 49613894867947296923609 (-8204505425305559039062) ⟨15,0xbd017402dc05a00b1015c02ac05400a50144027c04e0099012c024c048008d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨75,0x8da2f7811ef409c8804e9bd52a253061bb48166c2a878d69e1347904f2e4a9f10df6e07240f3b0c2d740ff0068042b022fc5b674cffd880727a23c41fde3d28d2123d2c2d6ac33bce1322cfbe0a3d0e8c4d91146c15c61709f6fa6fb20fe3e3431c1bc90b8f524b93f10f9a789b7d44539ccdd8a525c2cc528bbf024596caf7229d41a1b998e8a2b2c9e1f0397538a16dc5897aea87d576e0e9b92f81c0c50f4265532f8fd0235a246d0e21762c00b4b8e4dbed28246c8341baa6a4eb526c4135e4c83c15bd7b2a293e3ec25612d9ba69d821f6435ca25f31e4946a1fbcc3716c5bc7625bbc5ff151a998d536051cab4e10383498498afdd6eb9407f6bca03bd6674f004630dbf83d6906892cd784dbf07c5dc7b3d88c4e0b88b8f82fc1efd913bf71f7e7891c35134a236e4c260a607c12ee6cf5c9423125061e2631c938e2225be06b8b89d8c70bb6293e1993c52d3ade6b7069f3e2fa5f86db4cfae20556b4484d9b55bc062889067b841f67c2e5ab88ba4dcf07cc8b2fa9cb2c9890d4b981feb1d372c70ddde7ae1d734cac655b8178e5791bb8c88d9f1b8136a517cb8d12eeae46bed34c965b7825238f74a23c7aa0ee9146e479ca41ae6d7550ff578d1d07739506f164d0d0efc4d5a2097abec3f5c08b979101f636a1283dc0d28dacdfe16c50ad91fa454c54d766749b343f072646fde168ed66f5e8b653789b25c26fb3c21152cb4170032dc11b818998a2bcfb264b67001f53c380a7b1bbafec8204fb0086ab4736d53010ca2f51c365d8bbc801fffbcd2e5a09f210a07da4337f8d8a83efc40d7a9235726dcf124f8000000000000000000⟩ ⟨0,0⟩ (i-128)
  else
    if i < 304 then
      if i < 256 then
        suffixRow 219 24576 158616 6183371281909903422797 (-7720662897954465588416) 1956360492641069903736 (-155755414525274043990) ⟨15,0xbd017402dc05a00b1015c02ac05400a50144027c04e0099012c024c048008d0114021c042008100fc01ec03c007500e401bc036006900cc018c030005d00b4015c02a0051009c012c0240045008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨70,0xa6c11043c21eb9c80ae0974ece0f01bd4061985b6cfc16c56202ac1c19532858fd6c1062b16e58da0c25105c595091f765845601eb1a7b993494f2ed89c6d0e75596175da6303a0c2158248a5fd8e7d4dd9a64995955a44345298fe0087cf593b7d1df7a4da3a5de59de625a2f602833a1946960d51573a0270707c4d7e90a53e0af1efb7746d5c7c9d5fe87591fe2ff1fca3b5a4aa2d24212348442a9dc7c82fe0032abd7aa2887c3b15a2f5cc0b3241e3898e85f272af4eb561654cc3a0c6c6d40a46401e5b065b3f790a4edb268e65cd848d14f70e4074203800f8b6f44fa22906e7008a99501bc2936bb4c344cc4500e1f30f287c3c7b6216fe20bdbe60feaacf7b52dafa7b58fc53c4a47383f40f065bdb5ebc796fe8a874fffe594da63fc234ab7680787884fe7940b345a321ee7bf35fe688abc2e921cfa22c917b3ef5b006bd964de4e8c728917af17ca57d216b4d37f3ae419ee3b761f17fae499e5e4f365194c837282e93b1ba1a28acd3aed3bb57c531e67b2742645d91f25327cbf150f2931c6b576b2ce380174b23f285cca75026c898c2a8c24a69cd61f9c09276cac8d12b65420863e0fa9fd3374d4c3668891271441a26521e49c0998c7a84669eaacc53c5506c6b89bb25dc1691cacf51ff85796fa039bf54ce09a60571d0b3ecfa8c22e3ad0da211c5498409f6950b859958f863e7e0b5d80d1efbf138c51074f0165f05df831d6d8c60024c5bbda231492780b7876051d59f0a01030de555b5214f87a400000000000000000⟩ ⟨0,0⟩ (i-192)
      else
        suffixRow 283 33024 183192 263313462071233694127 (-197416217115080955696) 59136437861501386439 (-16428296593522221639) ⟨15,0xf601d4037806900c6017402d005700a80144027004b00900114021003f007800e401b0033006000b401500270048008400fc01e0039006c00cc018002d0054009c0120021003c006c00c00150024003c0060009000c000c00000⟩ ⟨66,0x32bca31c8cab8c60318b4de0524b7d661a52a0cd0471000c0aeb49c14d5be07be3f2a2cd5d54fb1e914e24762a2d5bd4665dabc9e9393250ae19e4dbcfedbe61d50711b525c9ebe25131e87f2bc08a854db2827e6bb4325aaab0a2858c1762607f26090c7b2366a8a13eaa59d591114c0b175e9b03d8128e1bb5222796831492b90b0cea061c6bab9222b0aa841fea94c79eac26a03d3e43ac687a62a77d94209851940009a2cb1a9386a50622537d4631130bb92a8e13562996fa794ba1753f817d155c3627c38a20eb2104afd9c56f6cd6e92c5be06b81684bc31cd0de1959b423aa57c01dc5f12fd727ee0cabf16236ce6f8461f17e51dfa1b4ce1dd0fd12c49c0e2781195544430d24b75db6f9c0f51a5ea606aa422a3660bfc5d57a33df8be3638910fbd42f228dca009b35015400897c0e483a51bdc41c27504661c14d4385927052554cc2e6210dc51317d56f5b402fdb5ebe3662e71607b3291c48008040810b4e01f975569f8018338ee724eaf0f800a8df2682b692cd00b7ed6b6d4553ec40000000000000000⟩ ⟨0,0⟩ (i-256)
    else
      if i < 385 then
        suffixRow 331 383784 216216 108605386224131903231 (-184035855841051628239) 85694379857572372906 (-263910240652647898) ⟨19,0x5d600b7c0169802c70057600abc0151802970052200a3e01476028eb451d5ca3aad475428e9051cc0a3801458027f004e6009b401338025b0049e0090c011b8022b0043e0084c0103801fb003de0078c00eb801cb0037e006cc00d38019b0031e0060c00bb8016b002be0054c00a38013b0025e0048c008b8010b001fe003cc0073800db0019e0030c005b800ab0013e0024c00438007b000de0018c002b8004b0007e000cc001680027000420006c000a8000f00018000240003000030000000⟩ ⟨66,0x1592a85451346200ae9ea362767ccb808f464029672aace04a7c81bfe8d9a3501fa33e752bb9b4220bff113e2853d585843c1f96cc373776416cd8ae5b0cef583868769f7fca424d261afcbfdf4bc1a86906db81bb2fb7266281b75254b83beef9986de2d3adf54c2f4a1b7a7cd7a6464dc786df113486da782d21b8a85cce0c4e7cc06e9c375014deeb5c1be0361f5346fb28076b7d97c07b20b622530bee1a6b2ff7e8b48554a5180378a6313e0ab98789e5788d5c2896d3923917e3e111f29cf3f4e9091bd32656d9d04fc8500d4e89591611ee96531c4a70097091662a40c4c80f3f3229b01852f9578cf18875649b8362e1295a9fac741435f4b6b5287e00428b79b290aa4386b306c6cb824699a967b06502a51ea88a7f88797d49088aa566922661e83202c887594a263b920cb97fad20c68a025cb018e51d447781c74c6c1796db7d87c77b323659de50723ca0d1bc7bcf13c692513590c616d9e6a8d6cda16c48f183b5b2eb74b5385c68dac558df7d05433490f687383f3312bd57b8c4ee1a428874d88228b385ad5a5c4a16da62e04b60eb04bc2756378f8e6b9aece1e5adb3ed8f76472fe4e35d257f0bb130887ad25b3fabeef43c1d331cda75855ec1ce8c5928556fd02e7be2f6ecbc2e904b4804b4f244339b1e3c79aacfcec6c5484e964a0ac8b3f2d27604e25520a7dfdfa07f5289241ebc1855da439f15cd65fe22316826efdd6890fd5b4f1984ec29ed888401605339ba91e9397283914b8e3fc6962244e37582a5b2ea173e28a813cd963ce6e1ce1d92f3f5dc97d9c285f46953e83d564e41276373f345f9c7c0364f6cbf21347f6809408540ab2ac5bc016575bacd9c0b7ec02b2a21258a36d028065de9236347745000bd75fc1a41ec03800ad4fad738971780016fbe5a752380a40000000000000000⟩ ⟨0,0⟩ (i-304)
      else
        ⟨600000,10000000000000000000,0,0⟩

def au : Mesh := ⟨386, auRow, 10000000000000000000000000⟩

end BethNumericData

end

section

/- Bethの有限篩で実際に使う有理数表の境界、単調性、および主項の余裕 -/

namespace BethNumericFacts

open BethNumericData BethNumericMesh BethNumericPoly

set_option maxRecDepth 15000 in
theorem f_starts : f.Starts := Mesh.starts_of_check (by decide +kernel)

set_option maxRecDepth 15000 in
theorem l_starts : l.Starts := Mesh.starts_of_check (by decide +kernel)

set_option maxRecDepth 15000 in
theorem u_starts : u.Starts := Mesh.starts_of_check (by decide +kernel)

set_option maxRecDepth 15000 in
theorem cf_starts : cf.Starts := Mesh.starts_of_check (by decide +kernel)

set_option maxRecDepth 15000 in
theorem al_starts : al.Starts := Mesh.starts_of_check (by decide +kernel)

set_option maxRecDepth 15000 in
theorem au_starts : au.Starts := Mesh.starts_of_check (by decide +kernel)

set_option maxRecDepth 15000 in
theorem f_controls : f.Controls 1 := Mesh.controls_of_check (by decide +kernel)
set_option maxRecDepth 15000 in
theorem l_controls : l.Controls (-1) := Mesh.controls_of_check (by decide +kernel)
set_option maxRecDepth 15000 in
theorem u_controls : u.Controls (-1) := Mesh.controls_of_check (by decide +kernel)

theorem f_mono : Monotone f.eval := Mesh.monotone_eval f_starts f_controls
theorem l_anti : Antitone l.eval := Mesh.antitone_eval l_starts l_controls
theorem u_anti : Antitone u.eval := Mesh.antitone_eval u_starts u_controls

theorem F_zero : 0 ≤ f.eval 0 := by
  rw [Mesh.eval_left f_starts (Nat.zero_le _), show (f.row 0).y = 0 by decide +kernel]
  simp

theorem f_cap_value : f.eval 600000 = 999999999000000 / (1000000000000000 : ℝ) := by
  rw [Mesh.eval_right f_starts (by decide +kernel)]
  rw [show (f.row (f.last+1)).y = 999999999000000 by decide +kernel]
  norm_num [show (f.scale : ℕ) = 1000000000000000 by decide +kernel]

theorem F_cap : f.eval (40*15000) ≤ 1 := by
  change f.eval 600000 ≤ 1
  rw [f_cap_value]
  norm_num

private theorem nonneg_of_end (m : Mesh) (h : m.Starts) (hanti : Antitone m.eval)
    (hval : 0 ≤ (m.row (m.last+1)).y) (j : ℕ) : 0 ≤ m.eval j := by
  let t := max j (m.row (m.last+1)).start
  have he := Mesh.eval_right h (le_max_right j (m.row (m.last+1)).start)
  have ht : 0 ≤ m.eval t := by
    rw [show m.eval t = _ from he]
    exact div_nonneg (by exact_mod_cast hval) (Nat.cast_nonneg _)
  exact ht.trans (hanti (le_max_left ..))

theorem l_nonneg (j : ℕ) : 0 ≤ l.eval j := nonneg_of_end l l_starts l_anti (by decide +kernel) j
theorem u_nonneg (j : ℕ) : 0 ≤ u.eval j := nonneg_of_end u u_starts u_anti (by decide +kernel) j

theorem e_nonneg (side : Bool) (j : ℕ) : 0 ≤ (if side then u.eval else l.eval) j := by
  cases side
  · exact l_nonneg j
  · exact u_nonneg j

theorem cdf_end : cf.eval (42*15000) * (((42*15000 : ℕ) : ℝ))^2 ≤
    f.eval (40*15000) * (15000 : ℝ)^2 := by
  change cf.eval 630000 * (630000 : ℝ)^2 ≤ f.eval 600000 * (15000 : ℝ)^2
  rw [Mesh.eval_right cf_starts (by decide +kernel), f_cap_value,
    show (cf.row (cf.last+1)).y = 5668934234693877551020 by decide +kernel,
    show (cf.scale : ℕ) = 10000000000000000000000000 by decide +kernel]
  norm_num

theorem margin : l.eval 63999 ≤ 1 - 1 / 100000 := by
  have he : l.eval 63999 = (l.piece 41).eval 0 := by
    have hh := Mesh.eval_piece l_starts (i := 41) (j := 63999) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
    rwa [show (l.row 41).start = 63999 by decide +kernel, Nat.sub_self, Nat.cast_zero] at hh
  rw [he, Mesh.piece, BethCubicOrder.left, show (l.row 41).y = 999982571342290 by decide +kernel,
    show (l.scale : ℕ) = 1000000000000000 by decide +kernel]
  norm_num

private theorem tail_end (m : Mesh) (h : m.Starts) (pieces : ℕ → Poly)
    (hl : ∀ i ≤ m.last, (pieces i).eval 0 = ((m.row i).y : ℝ)/(m.scale : ℕ))
    (hr : ∀ i ≤ m.last, (pieces i).eval (m.width i : ℕ) = ((m.row (i+1)).y : ℝ)/(m.scale : ℕ))
    (hj : (m.row (m.last+1)).start = 600000) (hv : (m.row (m.last+1)).y = 10000000000000000000)
    (hs : (m.scale : ℕ) = 10000000000000000000000000) :
    1/1000000 ≤ m.evalUsing pieces (40*15000) := by
  change _ ≤ m.evalUsing pieces 600000
  rw [← hj, Mesh.evalUsing_piece h pieces hl hr le_rfl (h _ le_rfl).le le_rfl,
    ← Mesh.width_eq h le_rfl, hr _ le_rfl, hv, hs]
  norm_num

theorem al_end (pieces : ℕ → Poly)
    (hl : ∀ i ≤ al.last, (pieces i).eval 0 = ((al.row i).y : ℝ)/(al.scale : ℕ))
    (hr : ∀ i ≤ al.last, (pieces i).eval (al.width i : ℕ) = ((al.row (i+1)).y : ℝ)/(al.scale : ℕ)) :
    1/1000000 ≤ al.evalUsing pieces (40*15000) :=
  tail_end al al_starts pieces hl hr (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem au_end (pieces : ℕ → Poly)
    (hl : ∀ i ≤ au.last, (pieces i).eval 0 = ((au.row i).y : ℝ)/(au.scale : ℕ))
    (hr : ∀ i ≤ au.last, (pieces i).eval (au.width i : ℕ) = ((au.row (i+1)).y : ℝ)/(au.scale : ℕ)) :
    1/1000000 ≤ au.evalUsing pieces (40*15000) :=
  tail_end au au_starts pieces hl hr (by decide +kernel) (by decide +kernel) (by decide +kernel)

end BethNumericFacts

end

section

/- Buchstabの接尾和を区間ごとの補間多項式で表し、各格子点で差分の向きを保つ。 -/

namespace BethNumericPot

open BethNumericPoly BethBernstein

private def linear (n : ℕ+) (a : ℕ) : Poly := ⟨[2*(a:ℤ)+1,2], n^2⟩

/-- (2(a+x)+1)/n²にsourceを掛けた、接尾和の1格子分 -/
def weighted (n : ℕ+) (a : ℕ) (source : Poly) := (linear n a).mul source

private def slope (w : ℕ+) : Poly := ⟨[0,1],w⟩

/-- LとRを整数の分子として、同一の分母sで指定した接尾和の補間 -/
def piece (n w s : ℕ+) (a : ℕ) (L R : ℤ) (source : Poly) : Poly :=
  let S := (weighted n a source).antiderivative4
  let adjust := (Poly.scalar (R-L) s).add (S.atInt (w : ℕ))
  ((Poly.scalar L s).sub S).add (adjust.mul (slope w))

private lemma length_add (u v : List ℤ) : (Coeff.add u v).length = max u.length v.length := by
  induction u generalizing v with
  | nil => simp [Coeff.add]
  | cons a u ih =>
    cases v with
    | nil => simp [Coeff.add]
    | cons b v => simp [Coeff.add,ih]

theorem length_shift (p : Poly) (k : ℤ) : (p.shift k).c.length = p.c.length := by
  change (Coeff.shift k p.c).length = p.c.length
  induction p.c with
  | nil => rfl
  | cons a u ih => simp [Coeff.shift, length_add, Coeff.scale, ih]

theorem weighted_degree (n : ℕ+) (a : ℕ) (source : Poly) (h : source.c.length ≤ 4) :
    (weighted n a source).c.length ≤ 5 := by
  simp [weighted,linear,Poly.mul,Coeff.mul,length_add,Coeff.scale]
  omega

theorem weighted_eval (n : ℕ+) (a : ℕ) (source : Poly) (x : ℝ) :
    (weighted n a source).eval x = ((2*((a:ℝ)+x)+1)*source.eval x) / ((n : ℕ) : ℝ)^2 := by
  rw [weighted, Poly.eval_mul]
  simp [linear,Poly.eval,horner]
  ring

private lemma eval_slope (w : ℕ+) (x : ℝ) : (slope w).eval x = x / (w : ℕ) := by
  simp [slope,Poly.eval,horner]

private lemma anti_zero (p : Poly) : p.antiderivative4.eval 0 = 0 := by
  simp [Poly.antiderivative4,Poly.eval,horner]

/-- 補正に使った線形項と離散原始関数の評価式 -/
theorem eval_piece (n w s : ℕ+) (a : ℕ) (L R : ℤ) (source : Poly) (x : ℝ) :
    (piece n w s a L R source).eval x =
      (L : ℝ) / (s : ℕ) - (weighted n a source).antiderivative4.eval x +
      ((R : ℝ) / (s : ℕ) - (L : ℝ) / (s : ℕ) +
        (weighted n a source).antiderivative4.eval (w : ℕ)) * (x / (w : ℕ)) := by
  simp only [piece, Poly.eval_add, Poly.eval_sub, Poly.eval_mul, Poly.eval_scalar, Poly.eval_atInt,
    eval_slope, Int.cast_sub, Int.cast_natCast, sub_div]

theorem first (n w s : ℕ+) (a : ℕ) (L R : ℤ) (source : Poly) :
    (piece n w s a L R source).eval 0 = (L : ℝ) / (s : ℕ) := by
  simp [eval_piece, anti_zero]

theorem last (n w s : ℕ+) (a : ℕ) (L R : ℤ) (source : Poly) :
    (piece n w s a L R source).eval (w : ℕ) = (R : ℝ) / (s : ℕ) := by
  have hw : ((w : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr w.property).ne'
  rw [eval_piece, div_self hw, mul_one]
  ring

/-- 右端から計算した和を左端で上に丸めると、補間の後も各格子差分が元の項以上になる。 -/
theorem step (n w s : ℕ+) (a : ℕ) (L R : ℤ) (source : Poly)
    (hdeg : source.c.length ≤ 4)
    (hslack : (R : ℝ) / (s : ℕ) - (L : ℝ) / (s : ℕ) +
      (weighted n a source).antiderivative4.eval (w : ℕ) ≤ 0) (x : ℝ) :
    (weighted n a source).eval x ≤
      (piece n w s a L R source).eval x - (piece n w s a L R source).eval (x+1) := by
  let A := (R : ℝ) / (s : ℕ) - (L : ℝ) / (s : ℕ) +
    (weighted n a source).antiderivative4.eval (w : ℕ)
  have had := Poly.eval_antiderivative4_diff (weighted n a source) (weighted_degree n a source hdeg) x
  have hcoef : A / (w : ℕ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hslack (Nat.cast_nonneg _)
  rw [eval_piece, eval_piece]
  change _ ≤ _ + A * (x / (w : ℕ)) - (_ + A * ((x+1) / (w : ℕ)))
  rw [add_div, mul_add, mul_one_div]
  linarith

end BethNumericPot

end

section

/- 接尾和の表の各行を補間多項式に変換し、閉区間の全格子点で同じ値を得る。 -/

namespace BethNumericPotView

open BethNumericPoly BethNumericMesh

/-- 行のb欄に記録された元の曲線を、格子をNだけずらして取り出す。 -/
def sourcePiece (N : ℕ+) (m src : Mesh) (i : ℕ) : Poly :=
  let k := (m.row i).b.toNat
  (src.piece k).shift (((m.row i).start - N - (src.row k).start : ℕ) : ℤ)

/-- 接尾和を表す表の1行 -/
def potPiece (N : ℕ+) (m src : Mesh) (i : ℕ) : Poly :=
  BethNumericPot.piece N (m.width i) m.scale (m.row i).start
    (m.row i).y (m.row (i+1)).y (sourcePiece N m src i)

theorem left (N : ℕ+) (m src : Mesh) (i : ℕ) :
    (potPiece N m src i).eval 0 = ((m.row i).y : ℝ) / (m.scale : ℕ) :=
  BethNumericPot.first ..

theorem right (N : ℕ+) (m src : Mesh) (i : ℕ) :
    (potPiece N m src i).eval (m.width i : ℕ) = ((m.row (i+1)).y : ℝ) / (m.scale : ℕ) :=
  BethNumericPot.last ..

theorem source_degree (N : ℕ+) (m src : Mesh) (i : ℕ) :
    (sourcePiece N m src i).c.length ≤ 4 := by
  rw [sourcePiece, BethNumericPot.length_shift]
  rfl

theorem eval_piece (N : ℕ+) {m : Mesh} (src : Mesh) (h : m.Starts) {i j : ℕ}
    (hi : i ≤ m.last) (ha : (m.row i).start ≤ j) (hb : j ≤ (m.row (i+1)).start) :
    m.evalUsing (potPiece N m src) j = (potPiece N m src i).eval (j - (m.row i).start : ℕ) :=
  Mesh.evalUsing_piece h _ (fun _ _ => left ..) (fun _ _ => right ..) hi ha hb

theorem source_eval (N : ℕ+) (m : Mesh) {src : Mesh} (h : src.Starts) (i j : ℕ)
    (hi : (m.row i).b.toNat ≤ src.last) (hN : (N : ℕ) ≤ (m.row i).start)
    (ha : (src.row (m.row i).b.toNat).start ≤ (m.row i).start - N)
    (haj : (m.row i).start ≤ j) (hb : j - N ≤ (src.row ((m.row i).b.toNat + 1)).start) :
    (sourcePiece N m src i).eval (j-(m.row i).start : ℕ) = src.eval (j - N) := by
  have hh := Mesh.eval_shift h hi ha (Nat.sub_le_sub_right haj (N : ℕ)) hb
  simpa only [sourcePiece, show j - N - ((m.row i).start - N) = j - (m.row i).start by omega] using hh

private def anti (N : ℕ+) (m src : Mesh) (i : ℕ) : Poly :=
  (BethNumericPot.weighted N (m.row i).start (sourcePiece N m src i)).antiderivative4

/-- 接尾和の端点を上に丸めるときの符号を整数の不等式で検査する。 -/
def checkSlack (N : ℕ+) (m src : Mesh) (i : ℕ) : Bool :=
  let S := anti N m src i
  decide (((m.row (i+1)).y - (m.row i).y) * (S.d : ℕ) +
    (S.valueAtInt (m.width i : ℕ)) * (m.scale : ℕ) ≤ 0)

theorem slack_of_check (N : ℕ+) (m src : Mesh) (i : ℕ) (hc : checkSlack N m src i) :
    ((m.row (i+1)).y : ℝ) / (m.scale : ℕ) - ((m.row i).y : ℝ) / (m.scale : ℕ) +
    (BethNumericPot.weighted N (m.row i).start (sourcePiece N m src i)).antiderivative4.eval
      (m.width i : ℕ) ≤ 0 := by
  let S := anti N m src i
  have hz : ((m.row (i+1)).y - (m.row i).y) * (S.d : ℕ) +
      (S.valueAtInt (m.width i : ℕ)) * (m.scale : ℕ) ≤ (0 : ℤ) := of_decide_eq_true hc
  have hR : (((m.row (i+1)).y : ℝ) - (m.row i).y) * (S.d : ℕ) +
      (S.valueAtInt (m.width i : ℕ) : ℝ) * (m.scale : ℕ) ≤ 0 := by exact_mod_cast hz
  have hcS : (S.valueAtInt (m.width i : ℕ) : ℝ) =
      S.eval (m.width i : ℕ) * (S.d : ℕ) := by
    rw [Poly.cast_valueAtInt, Int.cast_natCast, Poly.eval, div_mul_cancel₀]
    exact (Nat.cast_pos.mpr S.d.property).ne'
  rw [hcS] at hR
  have hs : (0 : ℝ) < (m.scale : ℕ) := Nat.cast_pos.mpr m.scale.property
  have hsd : (0 : ℝ) < (S.d : ℕ) := Nat.cast_pos.mpr S.d.property
  change _ + S.eval (m.width i : ℕ) ≤ 0
  have hn : (((m.row (i+1)).y : ℝ) - (m.row i).y) + S.eval (m.width i : ℕ)*(m.scale : ℕ) ≤ 0 := by
    by_contra! hpos
    nlinarith only [hR, mul_pos hpos hsd]
  calc _ = ((((m.row (i+1)).y : ℝ) - (m.row i).y) +
              S.eval (m.width i : ℕ)*(m.scale : ℕ)) / (m.scale : ℕ) := by field_simp
       _ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hn hs.le


/-- 元の曲線が、接尾和片の全ての格子点に対応していることを整数で調べる。 -/
def checkSource (N : ℕ+) (m src : Mesh) (i : ℕ) : Bool :=
  let k := (m.row i).b.toNat
  decide (k ≤ src.last ∧ (N : ℕ) ≤ (m.row i).start ∧
    (src.row k).start ≤ (m.row i).start - N ∧
    (m.row (i+1)).start - N ≤ (src.row (k+1)).start)

/-- 区間をまたぐ最後の格子差分にも端点の一致を使い、全表で接尾和を抑える。 -/
theorem mass_diff (N : ℕ+) {m src : Mesh} (hm : m.Starts) (hs : src.Starts)
    (hsource : ∀ i ≤ m.last, checkSource N m src i)
    (hslack : ∀ i ≤ m.last, checkSlack N m src i)
    (k : ℕ) (hlo : (m.row 0).start ≤ k) (hhi : k < (m.row (m.last+1)).start) :
    (2*(k:ℝ)+1)*src.eval (k-N) ≤
      (m.evalUsing (potPiece N m src) k - m.evalUsing (potPiece N m src) (k+1))*((N : ℕ) : ℝ)^2 := by
  let i := m.index k
  have hi : i ≤ m.last := Nat.findGreatest_le _
  have ha : (m.row i).start ≤ k := Nat.findGreatest_spec
    (P := fun u => (m.row u).start ≤ k) (Nat.zero_le m.last) hlo
  have hb : k < (m.row (i+1)).start := by
    by_cases he : i = m.last
    · rwa [he]
    · apply lt_of_not_ge
      exact Nat.findGreatest_is_greatest (P := fun u => (m.row u).start ≤ k)
        (n := m.last) (k := i+1) (Nat.lt_succ_self i) (by omega)
  let a := (m.row i).start
  let t := k - a
  have hrow := of_decide_eq_true (hsource i hi)
  obtain ⟨hiS, hNa, haS, hbS⟩ := hrow
  have hh := BethNumericPot.step N (m.width i) m.scale a (m.row i).y (m.row (i+1)).y
    (sourcePiece N m src i) (source_degree N m src i) (slack_of_check N m src i (hslack i hi)) (t : ℝ)
  rw [BethNumericPot.weighted_eval] at hh
  have heS := source_eval N m hs i k hiS hNa haS ha
    ((Nat.sub_le_sub_right hb.le (N:ℕ)).trans hbS)
  have hat : (a : ℝ) + t = k := by exact_mod_cast Nat.add_sub_of_le ha
  have hnext : (((k+1-(m.row i).start : ℕ)) : ℝ) = (t : ℝ)+1 := by
    exact_mod_cast (show k+1-(m.row i).start = t+1 by dsimp [t,a]; omega)
  have zero := eval_piece N src hm hi ha hb.le
  have one := eval_piece N src hm hi (ha.trans (Nat.le_succ _)) (Nat.succ_le_of_lt hb)
  rw [hnext] at one
  rw [hat, heS] at hh
  rw [zero, one]
  exact (div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.mpr N.property))).mp hh


end BethNumericPotView

end

section

/- 格子上で使う指数関数の有理数下界と、Buchstabの初期値への変換 -/

namespace BethNumericSeed

open Finset

/-- exp(x)の次数n-1のTaylor多項式 -/
def taylorSum (n : ℕ) (x : ℚ) : ℚ := ∑ i ∈ range n, x ^ i / (i.factorial : ℚ)

/-- aを左端とする区間のoff番目における指数関数の有理数下界 -/
def expLower (N a off : ℕ) : ℚ :=
  (taylorSum 16 1) ^ (a / N) * taylorSum 10 (((a % N + off : ℕ) : ℚ) / N)

/-- 多項式の実数での評価から、同じ有理数の格子値へ移すための式 -/
theorem cast_expLower (N a off : ℕ) :
    (expLower N a off : ℝ) =
      (∑ i ∈ range 16, (1 : ℝ) / i.factorial) ^ (a / N) *
        ∑ i ∈ range 10, ((((a % N + off : ℕ) : ℝ) / N)^i / i.factorial) := by
  simp [expLower, taylorSum]

private lemma taylor_nonneg {x : ℚ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ taylorSum n x :=
  sum_nonneg fun _ _ => div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)

private lemma taylor_le {x : ℚ} (hx : 0 ≤ x) (n : ℕ) :
    (taylorSum n x : ℝ) ≤ Real.exp (x : ℝ) := by
  simpa [taylorSum] using Real.sum_le_exp_of_nonneg (x := (x : ℝ)) (by exact_mod_cast hx) n

theorem expLower_nonneg (N a off : ℕ) : 0 ≤ expLower N a off :=
  mul_nonneg (pow_nonneg (taylor_nonneg (by norm_num) _) _)
    (taylor_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _)

theorem expLower_le {N : ℕ} (hN : 0 < N) (a off : ℕ) :
    (expLower N a off : ℝ) ≤ Real.exp (((a + off : ℕ) : ℝ) / N) := by
  let x : ℚ := ((a % N + off : ℕ) : ℚ) / N
  have hx : 0 ≤ x := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hN' : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have he : (((a / N : ℕ) : ℝ) + (x : ℝ)) = ((a + off : ℕ) : ℝ) / N := by
    apply (eq_div_iff hN').mpr
    simp only [x, Rat.cast_div, Rat.cast_natCast, add_mul, div_mul_cancel₀ _ hN']
    exact_mod_cast (show (a / N) * N + (a % N + off) = a + off by
      rw [← Nat.add_assoc, Nat.div_add_mod'])
  simp only [expLower, Rat.cast_mul, Rat.cast_pow]
  calc _ ≤ (Real.exp 1) ^ (a / N) * Real.exp (x : ℝ) := by
            apply mul_le_mul
            · exact pow_le_pow_left₀ (by exact_mod_cast taylor_nonneg (by norm_num : (0:ℚ) ≤ 1) 16)
                (by simpa using taylor_le (by norm_num : (0:ℚ) ≤ 1) 16) _
            · exact taylor_le hx 10
            · exact_mod_cast taylor_nonneg hx 10
            · positivity
       _ = Real.exp (((a / N : ℕ) : ℝ) + (x : ℝ)) := by
             rw [← Real.exp_nat_mul, mul_one, Real.exp_add]
       _ = _ := by rw [he]

private lemma scaled_exp_seed {t E y A : ℝ} (hA : 0 < A) (hE0 : 0 ≤ E)
    (hE : E ≤ Real.exp t) (h : A ≤ E * y) : A * Real.exp (-t) ≤ y := by
  have hy : 0 ≤ y := by
    by_contra! hneg
    exact hA.not_ge (h.trans (mul_nonpos_of_nonneg_of_nonpos hE0 hneg.le))
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  exact h.trans ((mul_le_mul_of_nonneg_right hE hy).trans_eq (mul_comm _ _))

/-- 表が有理数で確認した候補E(1-F)≥400000をCDFの初期下界に移す。 -/
theorem cdf_seed {N a off : ℕ} (hN : 0 < N) {F : ℝ}
    (h : 400000 ≤ (expLower N a off : ℝ) * (1 - F)) :
    F ≤ 1 - 400000 * Real.exp (-(((a + off : ℕ) : ℝ) / N)) := by
  have h0 : (0 : ℝ) ≤ (expLower N a off : ℝ) := by exact_mod_cast expLower_nonneg N a off
  have hh := scaled_exp_seed (by norm_num : (0:ℝ) < 400000) h0 (expLower_le hN a off) h
  linarith

/-- 表が有理数で確認した候補EY≥3000000を両側のBuchstab打切りへ移す。 -/
theorem tail_seed {N a off : ℕ} (hN : 0 < N) {Y : ℝ}
    (h : 3000000 ≤ (expLower N a off : ℝ) * Y) :
    3000000 * Real.exp (-(((a + off : ℕ) : ℝ) / N)) ≤ Y := by
  have h0 : (0 : ℝ) ≤ (expLower N a off : ℝ) := by exact_mod_cast expLower_nonneg N a off
  exact scaled_exp_seed (by norm_num) h0 (expLower_le hN a off) h

end BethNumericSeed

end

section

/- 区間ごとのTaylor下界を、共通分母を持つ整数係数多項式で評価する。 -/

namespace BethNumericPolySeed

open Finset BethNumericPoly BethBernstein BethNumericSeed

private def numerator (n : ℤ) : List ℤ :=
  [362880*n^9, 362880*n^8, 181440*n^7, 60480*n^6, 15120*n^5,
    3024*n^4, 504*n^3, 72*n^2, 9*n, 1]

private def remainderPoly (n : ℕ+) : Poly :=
  ⟨numerator (n : ℕ), ⟨362880 * (n : ℕ)^9, Nat.mul_pos (by decide) (pow_pos n.property _)⟩⟩

/-- 15次と9次のTaylor和を合わせた、区間の左端aで平行移動した多項式 -/
def expLowerPoly (n : ℕ+) (a : ℕ) : Poly :=
  (Poly.scalar ((888656868019 : ℤ) ^ (a / n))
      ⟨326918592000 ^ (a / n), pow_pos (by decide) _⟩).mul
    ((remainderPoly n).shift ((a % (n : ℕ) : ℕ) : ℤ))

private theorem base_const :
    (∑ i ∈ range 16, (1 : ℝ) / i.factorial) = (888656868019 : ℝ) / 326918592000 := by
  norm_num [sum_range_succ, Nat.factorial]

private theorem remainder_eval (n : ℕ+) (x : ℝ) :
    (remainderPoly n).eval x = ∑ i ∈ range 10, (x / (n : ℕ)) ^ i / i.factorial := by
  have hn : ((n : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr n.property).ne'
  norm_num [Poly.eval, remainderPoly, numerator, horner, sum_range_succ, Nat.factorial]
  field_simp [hn]
  ring

/-- 整数格子点でのHorner評価と、指数関数を抑える有理数は一致する。 -/
theorem eval_expLowerPoly (n : ℕ+) (a off : ℕ) :
    (expLowerPoly n a).eval off = (expLower n a off : ℝ) := by
  simp only [expLowerPoly, Poly.eval_mul, Poly.eval_shift, remainder_eval, cast_expLower,
    base_const, div_pow, Int.cast_natCast, Nat.cast_add]
  congr 1
  norm_num [Poly.scalar, Poly.eval, horner]

end BethNumericPolySeed

end

section

namespace BethNumericRows

open BethNumericPoly BethNumericPolySeed BethNumericSeed

inductive Kind where
  | cdfMass | cdfZero | cdfSeed | cdfStep | lowerOne | upperGap | tail | buchStep | buchMass
deriving DecidableEq, Inhabited

noncomputable def distortion : ℝ := 1+1/1000000000

def residual (kind : Kind) (n : ℕ+) (a : ℕ) (X Y A : Poly) : Poly :=
  let j := Poly.var a
  let jp := Poly.var (a+1)
  let j2 := j.mul j
  let w := (Poly.var (2*a+1)).add (Poly.var 0)
  let n2 : ℤ := ((n:ℕ):ℤ)^2
  match kind with
  | .cdfMass => ((X.mul w).scale n2).sub (((Y.sub A).mul j2).mul (jp.mul jp))
  | .cdfZero => X.scale (-1)
  | .cdfSeed => ((expLowerPoly n a).mul ((Poly.scalar 1).sub X)).sub (Poly.scalar 400000)
  | .cdfStep => ((j2.mul Y).scale 1000000000).sub (X.scale (1000000001*n2))
  | .lowerOne => X.sub (Poly.scalar 1)
  | .upperGap => (Y.mul ((Poly.scalar 1).add X)).sub (Poly.scalar 1)
  | .tail => ((expLowerPoly n a).mul X).sub (Poly.scalar 3000000)
  | .buchStep => (((X.scale 1000000000).sub Y).mul j2).sub (A.scale (1000000001*n2))
  | .buchMass => ((Y.sub A).scale n2).sub (w.mul X)

def Statement (kind : Kind) (n j : ℕ) (X Y A : ℝ) : Prop :=
  match kind with
  | .cdfMass => (Y-A)*(j:ℝ)^2*((j:ℝ)+1)^2 ≤ X*(n:ℝ)^2*(2*(j:ℝ)+1)
  | .cdfZero => X ≤ 0
  | .cdfSeed => X ≤ 1-400000*Real.exp (-((j:ℝ)/n))
  | .cdfStep => X*(distortion*(n:ℝ)^2) ≤ (j:ℝ)^2*Y
  | .lowerOne => 1 ≤ X
  | .upperGap => 1 ≤ Y*(1+X)
  | .tail => 3000000*Real.exp (-((j:ℝ)/n)) ≤ X
  | .buchStep => distortion*(n:ℝ)^2*A ≤ (X-(distortion-1)*Y)*(j:ℝ)^2
  | .buchMass => (2*(j:ℝ)+1)*X ≤ (Y-A)*(n:ℝ)^2

theorem residual_sound (kind : Kind) (n : ℕ+) (a off : ℕ) (X Y A : Poly)
    (h : 0 ≤ (residual kind n a X Y A).eval off) :
    Statement kind n (a+off) (X.eval off) (Y.eval off) (A.eval off) := by
  cases kind <;> simp only [residual,Poly.eval_sub,Poly.eval_scale,Poly.eval_mul,
    Poly.eval_var,Poly.eval_add,Poly.eval_scalar,eval_expLowerPoly,Int.cast_mul,Int.cast_pow,
    Int.cast_neg,Int.cast_natCast,Int.cast_one,Int.cast_ofNat,Int.cast_add,Int.cast_zero,PNat.val_ofNat,Nat.cast_one,
    Nat.cast_add,div_one,Statement,distortion] at h ⊢
  · linarith only [h]
  · linarith only [h]
  · convert cdf_seed (a:=a) (off:=off) (F:=X.eval off) n.property (sub_nonneg.mp h) using 1 <;> push_cast <;> congr 2
  · linarith only [h]
  · linarith only [h]
  · linarith only [h]
  · convert tail_seed (a:=a) (off:=off) (Y:=X.eval off) n.property (sub_nonneg.mp h) using 1 <;> push_cast <;> congr 2
  · linarith only [h]
  · linarith only [h]

theorem test_sound (kind : Kind) (n : ℕ+) (a L off : ℕ) (X Y A : Poly) (ho : off ≤ L)
    (h : (residual kind n a X Y A).test L = true) :
    Statement kind n (a+off) (X.eval off) (Y.eval off) (A.eval off) :=
  residual_sound kind n a off X Y A ((residual kind n a X Y A).test_sound L h (Nat.cast_nonneg _) (by exact_mod_cast ho))

end BethNumericRows

end

section

namespace BethNumericView

open BethNumericMesh BethNumericPoly

structure Curve where
  m : Mesh
  pieces : ℕ → Poly
  starts : m.Starts
  left : ∀ i ≤ m.last, (pieces i).eval 0 = ((m.row i).y : ℝ)/(m.scale : ℕ)
  right : ∀ i ≤ m.last, (pieces i).eval (m.width i : ℕ) = ((m.row (i+1)).y : ℝ)/(m.scale : ℕ)

inductive Ref where
  | moving (piece start : ℕ)
  | fixed (piece start : ℕ)
deriving Inhabited, DecidableEq

def Ref.indexAt : Ref → ℕ → ℕ
  | .moving _ a, off => a+off
  | .fixed _ a, _ => a

namespace Curve

def cubic (m : Mesh) (h : m.Starts) : Curve :=
  ⟨m, m.piece, h, fun _ _ ↦ BethCubicOrder.left .., fun _ _ ↦ BethCubicOrder.right ..⟩

noncomputable def eval (c : Curve) (j : ℕ) : ℝ := c.m.evalUsing c.pieces j

def shifted (c : Curve) (i a : ℕ) : Poly :=
  (c.pieces i).shift ((a - (c.m.row i).start : ℕ) : ℤ)

def valid (c : Curve) (i a b : ℕ) : Bool :=
  decide (i ≤ c.m.last ∧ (c.m.row i).start ≤ a ∧ a ≤ b ∧ b ≤ (c.m.row (i+1)).start)

theorem eval_shifted (c : Curve) {i a b j : ℕ} (h : c.valid i a b = true)
    (haj : a ≤ j) (hjb : j ≤ b) : (c.shifted i a).eval (j-a : ℕ) = c.eval j := by
  have ⟨hi,ha,_,hb⟩ := of_decide_eq_true h
  rw [eval, Mesh.evalUsing_piece c.starts c.pieces c.left c.right hi (ha.trans haj) (hjb.trans hb),
    shifted, Poly.eval_shift, Int.cast_natCast, ← Nat.cast_add]
  congr 2
  omega

/-- 区間の変数を一緒に動かすときと、最大値の下端で値を固定するときの共通参照 -/
def access (c : Curve) : Ref → Poly
  | .moving i a => c.shifted i a
  | .fixed i a => (c.shifted i a).atInt 0

def validRef (c : Curve) (r : Ref) (width : ℕ) : Bool :=
  match r with
  | .moving i a => c.valid i a (a+width)
  | .fixed i a => c.valid i a a

theorem eval_access (c : Curve) (r : Ref) {width off : ℕ} (hv : c.validRef r width = true) (ho : off ≤ width) :
    (c.access r).eval (off:ℝ) = c.eval (r.indexAt off) := by
  cases r with
  | moving i a =>
    have h := c.eval_shifted (i := i) (a := a) (b := a+width) (j := a+off) hv (by omega) (by omega)
    simpa only [access,Ref.indexAt,Nat.add_sub_cancel_left] using h
  | fixed i a =>
    rw [access, Poly.eval_atInt, Int.cast_zero]
    have h := c.eval_shifted (i := i) (a := a) (b := a) (j := a) hv le_rfl le_rfl
    simpa only [Nat.sub_self,Nat.cast_zero,Ref.indexAt] using h

end Curve
end BethNumericView

end

section

namespace BethNumericCover

def Covers (P : ℕ → Prop) (lo hi : ℕ) : Prop := ∀ j, lo ≤ j → j < hi → P j

theorem join {P : ℕ → Prop} {lo mid hi : ℕ}
    (left : Covers P lo mid) (right : Covers P mid hi) : Covers P lo hi := by
  intro j h₁ h₂
  by_cases hj : j < mid
  · exact left j h₁ hj
  · exact right j (le_of_not_gt hj) h₂

/-- 各行に格納されている左端と右端を照合しながら、被覆区間を左から一度だけ走査する。 -/
def checkRows {W : Type*} (left right : W → ℕ) (checkSpan : W → Bool) (lo hi : ℕ) :
    List W → Bool
  | [] => lo == hi
  | r :: rs => (left r == lo) && decide (lo < right r) && checkSpan r &&
      checkRows left right checkSpan (right r) hi rs

/-- 行ごとに証明した判定器の正当性を、チャンク全体の数学的な被覆に変換する。 -/
theorem checkRows_sound {W : Type*} (left right : W → ℕ) (checkSpan : W → Bool) (P : ℕ → Prop)
    (sound : ∀ r, checkSpan r = true → Covers P (left r) (right r))
    {lo hi : ℕ} {rows : List W} (h : checkRows left right checkSpan lo hi rows = true) : Covers P lo hi := by
  induction rows generalizing lo with
  | nil =>
    simp only [checkRows, beq_iff_eq] at h
    intro j hj hj'
    omega
  | cons r rs ih =>
    simp only [checkRows, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨he, _⟩, hr⟩, hs⟩ := h
    rw [← he]
    exact join (sound r hr) (ih hs)

end BethNumericCover

end

section

namespace BethNumericSpan

open BethNumericPoly BethNumericRows BethNumericView BethNumericCover

structure Curves where
  f : Curve
  l : Curve
  u : Curve
  c : Curve
  al : Curve
  au : Curve

inductive Series where
  | cMass | cStep | lStep | uStep
deriving DecidableEq, Inhabited

structure Span where
  a : ℕ
  width : ℕ
  tag : ℕ
  i : ℕ
  j : ℕ
  k : ℕ
  f : ℕ
deriving Inhabited

def Span.lastOffset (r : Span) := r.width-1
def Span.right (r : Span) := r.a+r.width

structure Access where
  curve : Curve
  ref : Ref

def moving (c : Curve) (i a : ℕ) : Access := ⟨c,.moving i a⟩
def fixed (c : Curve) (i a : ℕ) : Access := ⟨c,.fixed i a⟩

structure Frame where
  kind : Kind
  x : Access
  y : Access
  z : Access

def frame (g : Series) (n : ℕ+) (cs : Curves) (r : Span) : Frame :=
  let N : ℕ := n
  let X := moving cs.f r.i r.a
  match g with
  | .cMass =>
    ⟨.cdfMass,moving cs.f r.i (r.a-2*N),moving cs.c r.j r.a,moving cs.c r.k (r.a+1)⟩
  | .cStep =>
    if r.tag = 0 then ⟨.cdfZero,X,X,X⟩
    else if r.tag = 1 then ⟨.cdfSeed,X,X,X⟩
    else ⟨.cdfStep,X,(if r.a < 2*N then fixed cs.c r.j (2*N) else moving cs.c r.j r.a), X⟩
  | .lStep =>
    let Y := moving cs.l r.i r.a
    if r.tag = 0 then ⟨.lowerOne,Y,Y,Y⟩
    else if r.tag = 1 then ⟨.tail,Y,Y,Y⟩
    else ⟨.buchStep,Y,moving cs.u r.j (r.a-N),moving cs.al r.k r.a⟩
  | .uStep =>
    let Y := moving cs.u r.i r.a
    if r.tag = 0 then ⟨.upperGap,Y,moving cs.f r.f r.a,Y⟩
    else if r.tag = 1 then ⟨.tail,Y,Y,Y⟩
    else ⟨.buchStep,Y,moving cs.l r.j (r.a-N),moving cs.au r.k r.a⟩

def Frame.check (v : Frame) (n : ℕ+) (a L : ℕ) : Bool :=
  v.x.curve.validRef v.x.ref L && v.y.curve.validRef v.y.ref L && v.z.curve.validRef v.z.ref L &&
  (residual v.kind n a (v.x.curve.access v.x.ref) (v.y.curve.access v.y.ref) (v.z.curve.access v.z.ref)).test L

theorem Frame.sound (v : Frame) (n : ℕ+) (a L off : ℕ) (ho : off ≤ L) (h : v.check n a L = true) :
    Statement v.kind n (a+off) (v.x.curve.eval (v.x.ref.indexAt off))
      (v.y.curve.eval (v.y.ref.indexAt off)) (v.z.curve.eval (v.z.ref.indexAt off)) := by
  simp only [Frame.check,Bool.and_eq_true] at h
  obtain ⟨⟨⟨hx,hy⟩,hz⟩,ht⟩ := h
  have hh := BethNumericRows.test_sound v.kind n a L off _ _ _ ho ht
  rw [v.x.curve.eval_access v.x.ref hx ho, v.y.curve.eval_access v.y.ref hy ho,
      v.z.curve.eval_access v.z.ref hz ho] at hh
  exact hh

def pre (g : Series) (N : ℕ) (r : Span) : Bool :=
  match g with
  | .cMass => decide (2*N ≤ r.a)
  | .cStep => decide (r.a + r.lastOffset ≤ 2*N ∨ 2*N ≤ r.a)
  | .lStep =>
    if r.tag = 0 then true else if r.tag = 1 then decide (26*N ≤ r.a) else decide (4*N ≤ r.a)
  | .uStep =>
    if r.tag = 0 then true else if r.tag = 1 then decide (26*N ≤ r.a) else decide (3*N ≤ r.a)

def check (g : Series) (n : ℕ+) (cs : Curves) (r : Span) : Bool :=
  pre g n r && (frame g n cs r).check n r.a r.lastOffset

def Goal (g : Series) (N : ℕ) (cs : Curves) (j : ℕ) : Prop :=
  match g with
  | .cMass => (cs.c.eval j - cs.c.eval (j+1)) * (j:ℝ)^2 * ((j:ℝ)+1)^2 ≤
      cs.f.eval (j-2*N) * (N:ℝ)^2 * (2*(j:ℝ)+1)
  | .cStep => cs.f.eval j ≤ max 0 (1-400000*Real.exp (-((j:ℝ)/N))) ∨
      cs.f.eval j * (distortion*(N:ℝ)^2) ≤ (j:ℝ)^2 * cs.c.eval (max j (2*N))
  | .lStep => 1 ≤ cs.l.eval j ∨
      (26*N ≤ j ∧ 3000000*Real.exp (-((j:ℝ)/N)) ≤ cs.l.eval j) ∨
      (4*N ≤ j ∧ distortion*(N:ℝ)^2*cs.al.eval j ≤ (cs.l.eval j-(distortion-1)*cs.u.eval (j-N))*(j:ℝ)^2)
  | .uStep => 1 ≤ cs.f.eval j*(1+cs.u.eval j) ∨
      (26*N ≤ j ∧ 3000000*Real.exp (-((j:ℝ)/N)) ≤ cs.u.eval j) ∨
      distortion*(N:ℝ)^2*cs.au.eval j ≤ (cs.u.eval j-(distortion-1)*cs.l.eval (j-N))*(j:ℝ)^2

theorem sound (g : Series) (n : ℕ+) (cs : Curves) (r : Span) (h : check g n cs r = true) :
    Covers (Goal g n cs) r.a r.right := by
  rw [check,Bool.and_eq_true] at h
  obtain ⟨hp,hf⟩ := h
  intro t hrt htr
  let off := t - r.a
  have ho : off ≤ r.lastOffset := by dsimp [off,Span.lastOffset,Span.right] at *; omega
  have ht : r.a + off = t := by dsimp [off]; omega
  have hs := (frame g n cs r).sound n r.a r.lastOffset off ho hf
  cases g with
  | cMass =>
    have hbase : 2*(n:ℕ) ≤ r.a := of_decide_eq_true hp
    have hsub : r.a-2*(n:ℕ)+off = t-2*(n:ℕ) := by omega
    have hsuc : r.a+1+off = t+1 := by omega
    simpa only [frame,Goal,Statement,moving,Ref.indexAt,ht,hsub,hsuc] using hs
  | cStep =>
    change _ ∨ _ at ⊢
    by_cases h0 : r.tag = 0
    · simp only [frame,if_pos h0,moving,Ref.indexAt,ht,Statement] at hs
      exact Or.inl (hs.trans (le_max_left _ _))
    by_cases h1 : r.tag = 1
    · simp only [frame,if_neg h0,if_pos h1,moving,Ref.indexAt,ht,Statement] at hs
      exact Or.inl (hs.trans (le_max_right _ _))
    have hb : r.a+r.lastOffset ≤ 2*(n:ℕ) ∨ 2*(n:ℕ) ≤ r.a := of_decide_eq_true hp
    by_cases hlt : r.a < 2*(n:ℕ)
    · have hsmall : t ≤ 2*(n:ℕ) := by omega
      simp only [frame,if_neg h0,if_neg h1,if_pos hlt,moving,fixed,Ref.indexAt,ht,Statement] at hs
      exact Or.inr (by simpa only [max_eq_right hsmall] using hs)
    · have hlarge : 2*(n:ℕ) ≤ t := by omega
      simp only [frame,if_neg h0,if_neg h1,if_neg hlt,moving,Ref.indexAt,ht,Statement] at hs
      exact Or.inr (by simpa only [max_eq_left hlarge] using hs)
  | lStep =>
    change _ ∨ _ ∨ _ at ⊢
    by_cases h0 : r.tag = 0
    · exact Or.inl (by simpa only [frame,if_pos h0,moving,Ref.indexAt,ht,Statement] using hs)
    by_cases h1 : r.tag = 1
    · have hb : 26*(n:ℕ) ≤ r.a := by simpa [pre,h0,h1] using hp
      exact Or.inr (Or.inl ⟨hb.trans hrt,by simpa only [frame,if_neg h0,if_pos h1,moving,Ref.indexAt,ht,Statement] using hs⟩)
    have hb : 4*(n:ℕ) ≤ r.a := by simpa [pre,h0,h1] using hp
    have hsub : r.a-(n:ℕ)+off = t-(n:ℕ) := by omega
    exact Or.inr (Or.inr ⟨hb.trans hrt,by simpa only [frame,if_neg h0,if_neg h1,moving,Ref.indexAt,ht,hsub,Statement] using hs⟩)
  | uStep =>
    change _ ∨ _ ∨ _ at ⊢
    by_cases h0 : r.tag = 0
    · exact Or.inl (by simpa only [frame,if_pos h0,moving,Ref.indexAt,ht,Statement] using hs)
    by_cases h1 : r.tag = 1
    · have hb : 26*(n:ℕ) ≤ r.a := by simpa [pre,h0,h1] using hp
      exact Or.inr (Or.inl ⟨hb.trans hrt,by simpa only [frame,if_neg h0,if_pos h1,moving,Ref.indexAt,ht,Statement] using hs⟩)
    have hb : 3*(n:ℕ) ≤ r.a := by simpa [pre,h0,h1] using hp
    have hsub : r.a-(n:ℕ)+off = t-(n:ℕ) := by omega
    exact Or.inr (Or.inr (by simpa only [frame,if_neg h0,if_neg h1,moving,Ref.indexAt,ht,hsub,Statement] using hs))

def unpack (a i j k f : ℕ) : List ℕ → List Span
  | [] => []
  | v::vs =>
    let w := v%8192
    let tag := v/8192%4
    let i' := i + v/32768%2
    let j' := j + v/65536%2
    let k' := k + v/131072%2
    let f' := f + v/262144%2
    ⟨a,w,tag,i',j',k',f'⟩ :: unpack (a+w) i' j' k' f' vs

end BethNumericSpan

end

section

namespace BethNumericInstance

open BethNumericData BethNumericView BethNumericMesh BethNumericSpan BethNumericCover

structure Valid where
  f : BethNumericData.f.Starts
  l : BethNumericData.l.Starts
  u : BethNumericData.u.Starts
  c : cf.Starts
  al : BethNumericData.al.Starts
  au : BethNumericData.au.Starts

def n : ℕ+ := 15000

def pot (m src : Mesh) (h : m.Starts) : Curve :=
  ⟨m,BethNumericPotView.potPiece n m src,h,fun i _ ↦ BethNumericPotView.left n m src i,
    fun i _ ↦ BethNumericPotView.right n m src i⟩

def curves (h : Valid) : Curves :=
  ⟨Curve.cubic f h.f,Curve.cubic l h.l,Curve.cubic u h.u,Curve.cubic cf h.c,pot al u h.al,pot au l h.au⟩

def verify (h : Valid) (g : Series) (lo hi i j k f : ℕ) (vs : List ℕ) : Bool :=
  checkRows Span.a Span.right (check g n (curves h)) lo hi (unpack lo i j k f vs)

theorem covered (h : Valid) (g : Series) (lo hi i j k f : ℕ) (vs : List ℕ)
    (hc : verify h g lo hi i j k f vs = true) :
    Covers (Goal g n (curves h)) lo hi :=
  checkRows_sound _ _ _ _ (sound g n (curves h)) hc

def decode (dict : Array ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | t+1, z => (dict[z%512]?.getD 0)::decode dict t (z/512)

theorem packed (h : Valid) (g : Series) (lo hi i j k f : ℕ) (dict : Array ℕ) (count z : ℕ)
    (hc : verify h g lo hi i j k f (decode dict count z) = true) :
    Covers (Goal g n (curves h)) lo hi :=
  covered h g lo hi i j k f _ hc

end BethNumericInstance

end

section

open Finset

namespace BethNumericBridge

private theorem sum_differences (b : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ range n, (b k - b (k+1))) = b 0 - b n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; ring

/-- CDFの残和の局所差分をすべて足し、Abel変形の合計と照合する。 -/
theorem cdf_remainder (N cap j : ℕ) (hN : 0 < N) (hj : j ≤ cap) {K : ℝ} (hK : 0 < K)
    (F A : ℕ → ℝ)
    (hend : A (cap+2*N) * ((cap+2*N : ℕ) : ℝ)^2 ≤ F cap * (N : ℝ)^2)
    (hdiff : ∀ k : ℕ, 2*N ≤ k → k < cap+2*N →
      (A k - A (k+1)) * (k:ℝ)^2 * ((k:ℝ)+1)^2 ≤ F (k-2*N) * (N:ℝ)^2 * (2*k+1)) :
    (j:ℝ)^2 * A (max j (2*N)) / (K * (N:ℝ)^2) ≤
      ∑ t ∈ range (cap+1), BethCdfGrid.increment F t * BethCdfGrid.cutBound N K j t := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have htop : 0 < (cap:ℝ) + 2*N := by positivity
  let b (t : ℕ) := A (max j (t+2*N))
  let g (t : ℕ) := if j ≤ t+2*N then F t * BethCdfGrid.kernel N t else 0
  have hrow (t : ℕ) (ht : t < cap) : b t - b (t+1) ≤ (N:ℝ)^2 * g t := by
    by_cases hb : j ≤ t+2*N
    · have hbt : j ≤ t+1+2*N := by omega
      have hk : 0 < (t:ℝ) + 2*N := by positivity
      have hs := hdiff (t+2*N) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at hs
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs
      simp only [b, g, hb, if_true, max_eq_right hb, max_eq_right hbt, BethCdfGrid.kernel]
      rw [show t+1+2*N = t+2*N+1 by omega]
      calc
        _ ≤ (F t * (N:ℝ)^2 * (2*((t:ℝ) + 2*N)+1)) /
            (((t:ℝ) + 2*N)^2 * ((t:ℝ)+2*N+1)^2) := by
              rw [le_div_iff₀ (by positivity)]
              linarith only [hs]
        _ = _ := by ring
    · have h₁ : t+2*N ≤ j := by omega
      have h₂ : t+1+2*N ≤ j := by omega
      simp only [b, g, max_eq_left h₁, max_eq_left h₂, hb, if_false, sub_self, mul_zero, le_rfl]
  have hs : b 0 - b cap ≤ (N:ℝ)^2 * ∑ t ∈ range cap, g t := by
    rw [← sum_differences b cap, mul_sum]
    exact sum_le_sum fun t ht ↦ hrow t (mem_range.mp ht)
  have ht : b cap ≤ (N:ℝ)^2 * (F cap / ((cap:ℝ) + 2*N)^2) := by
    rw [show b cap = A (cap+2*N) from congrArg A (max_eq_right (by omega))]
    rw [← mul_div_assoc, le_div_iff₀ (sq_pos_of_pos htop)]
    push_cast at hend
    linarith only [hend]
  have hsum : A (max j (2*N)) / (N:ℝ)^2 ≤ F cap / ((cap:ℝ) + 2*N)^2 + ∑ t ∈ range cap, g t := by
    have h0 : b 0 = A (max j (2*N)) := by simp [b]
    rw [h0] at hs
    rw [div_le_iff₀ (sq_pos_of_pos hNR)]
    linarith only [hs, ht]
  rw [BethCdfGrid.abel_update F N cap hN K j (by omega)]
  calc
    _ = (j:ℝ)^2 / K * (A (max j (2*N)) / (N:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum (div_nonneg (sq_nonneg (j:ℝ)) hK.le)

/-- Buchstabの誤差上界の残和を端点から寄せた局所不等式で評価する。 -/
theorem buchstab_remainder (N j cap : ℕ) (hj : j ≤ cap) {K : ℝ} (hK : 0 ≤ K)
    (e A : ℕ → ℝ) (hend : 1/1000000 ≤ A cap)
    (hdiff : ∀ k : ℕ, j ≤ k → k < cap →
      (2*(k:ℝ)+1)*e (k-N) ≤ (A k - A (k+1)) * (N:ℝ)^2) :
    BethTail.tableStep K N j cap e ≤ (K-1)*e (j-N) + K*(N:ℝ)^2 * A j / (j:ℝ)^2 := by
  have hs : (∑ i ∈ range (cap-j), (2*((j+i : ℕ):ℝ)+1) * e (j+i-N)) ≤
      (A j - A cap)*(N:ℝ)^2 := by
    calc
      _ ≤ ∑ i ∈ range (cap-j), (A (j+i) - A (j+(i+1))) * (N:ℝ)^2 := by
        refine sum_le_sum fun i hi ↦ ?_
        have hi' := mem_range.mp hi
        exact hdiff (j+i) (by omega) (by omega)
      _ = _ := by
        rw [← sum_mul, sum_differences (fun i ↦ A (j+i))]
        simp [Nat.add_sub_of_le hj]
  have ht := mul_le_mul_of_nonneg_right hend (sq_nonneg (N:ℝ))
  have hsum : (N:ℝ)^2 / 1000000 +
      (∑ i ∈ range (cap-j), (2*((j+i : ℕ):ℝ)+1) * e (j+i-N)) ≤ (N:ℝ)^2 * A j := by
    linarith only [hs, ht]
  unfold BethTail.tableStep
  refine add_le_add le_rfl ?_
  calc
    _ ≤ K / (j:ℝ)^2 * ((N:ℝ)^2 * A j) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg hK (sq_nonneg _))
    _ = _ := by ring

/-- 差分を調べる範囲と点ごとの選択肢を、正の分母を払って指定する。 -/
structure LocalData (N : ℕ) (K : ℝ) where
  F : ℕ → ℝ
  e : Bool → ℕ → ℝ
  C : ℕ → ℝ
  A : Bool → ℕ → ℝ
  F_mono : ∀ {a b : ℕ}, a ≤ b → b ≤ 40*N → F a ≤ F b
  F_zero : 0 ≤ F 0
  F_cap : F (40*N) ≤ 1
  e_anti : ∀ side, Antitone (e side)
  e_nonneg : ∀ side j, 0 ≤ e side j
  cdf_end : C (42*N) * ((42*N : ℕ) : ℝ)^2 ≤ F (40*N) * (N : ℝ)^2
  cdf_diff : ∀ k : ℕ, 2*N ≤ k → k < 42*N →
    (C k - C (k+1)) * (k:ℝ)^2 * ((k:ℝ)+1)^2 ≤ F (k-2*N) * (N:ℝ)^2 * (2*k+1)
  cdf_branch : ∀ j ≤ 40*N, F j ≤ max 0 (1-400000*Real.exp (-((j:ℝ)/N))) ∨
    F j * (K*(N:ℝ)^2) ≤ (j:ℝ)^2 * C (max j (2*N))
  buch_end : ∀ side, 1/1000000 ≤ A side (40*N)
  buch_diff : ∀ (side : Bool) (k : ℕ), (if side then 3*N else 4*N) ≤ k → k < 40*N →
    (2*(k:ℝ)+1)*e (!side) (k-N) ≤ (A side k - A side (k+1))*(N:ℝ)^2
  lower_branch : ∀ j < 40*N, 1 ≤ e false j ∨
    (26*N ≤ j ∧ 3000000*Real.exp (-((j:ℝ)/N)) ≤ e false j) ∨
    (4*N ≤ j ∧ K*(N:ℝ)^2*A false j ≤ (e false j-(K-1)*e true (j-N))*(j:ℝ)^2)
  upper_branch : ∀ j < 40*N, 3*N ≤ j → 1 ≤ F j*(1+e true j) ∨
    (26*N ≤ j ∧ 3000000*Real.exp (-((j:ℝ)/N)) ≤ e true j) ∨
    K*(N:ℝ)^2*A true j ≤ (e true j-(K-1)*e false (j-N))*(j:ℝ)^2

def LocalData.toProfile {N : ℕ} {K : ℝ} (a : LocalData N K) (hN : 0 < N) (hK : 0 < K) :
    BethProfile.Profile N K := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h42 : 40*N+2*N = 42*N := by omega
  have bstep (side : Bool) (j : ℕ) (hj : j < 40*N) (hbase : (if side then 3*N else 4*N) ≤ j)
      (hval : K*(N:ℝ)^2*a.A side j ≤ (a.e side j-(K-1)*a.e (!side) (j-N))*(j:ℝ)^2) :
      BethTail.tableStep K N j (40*N) (a.e (!side)) ≤ a.e side j := by
    have hj0 : 0 < j := by cases side <;> simp at hbase <;> omega
    have hR : (0 : ℝ) < j := by exact_mod_cast hj0
    have htrec := buchstab_remainder N j (40*N) hj.le hK.le (a.e (!side)) (a.A side)
      (a.buch_end side) (fun k hk hkc ↦ a.buch_diff side k (hbase.trans hk) hkc)
    have hd := (div_le_iff₀ (sq_pos_of_pos hR)).2 hval
    exact htrec.trans (by linarith only [hd])
  refine ⟨a.F, a.e, a.F_mono, a.F_zero, a.F_cap, ?_, a.e_anti, a.e_nonneg, ?_, ?_⟩
  · intro j hj
    rcases a.cdf_branch j hj with hs | hr
    · exact hs.trans (le_max_left _ _)
    · apply (le_div_iff₀ (mul_pos hK (sq_pos_of_pos hNR))).2 hr |>.trans
      apply (le_max_right _ _).trans'
      exact cdf_remainder N (40*N) j hN hj hK a.F a.C (by simpa only [h42] using a.cdf_end)
        (by simpa only [h42] using a.cdf_diff)
  · intro j hj
    rcases a.lower_branch j hj with h | h | ⟨hbase,h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hbase, bstep false j hj hbase h⟩)
  · intro j hj h3
    rcases a.upper_branch j hj h3 with h | h | h
    · have hf : 0 ≤ a.F j := a.F_zero.trans (a.F_mono (Nat.zero_le j) hj.le)
      have hf' : 0 < a.F j := lt_of_le_of_ne hf (by rintro he; rw [← he] at h; linarith)
      exact Or.inl ⟨hf', (div_le_iff₀ hf').2 (by linarith only [h])⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (bstep true j hj h3 h))

end BethNumericBridge

end

section

/- Assemble the certified rational inequalities into the sieve profile. -/

namespace BethNumericConclusion

open BethNumericMesh BethNumericData BethNumericInstance BethNumericSpan BethNumericCover

theorem valid : Valid :=
  ⟨BethNumericFacts.f_starts, BethNumericFacts.l_starts, BethNumericFacts.u_starts,
   BethNumericFacts.cf_starts, BethNumericFacts.al_starts, BethNumericFacts.au_starts⟩

def Difference (pot base : Mesh) (start : ℕ) : Prop :=
  ∀ k : ℕ, start ≤ k → k < 600000 →
    (2*(k:ℝ)+1)*base.eval (k-(n:ℕ)) ≤
      (pot.evalUsing (BethNumericPotView.potPiece n pot base) k -
       pot.evalUsing (BethNumericPotView.potPiece n pot base) (k+1))*((n:ℕ):ℝ)^2

theorem of_checks
    (mass : Covers (Goal .cMass n (curves valid)) 30000 630000)
    (cdf : Covers (Goal .cStep n (curves valid)) 0 600001)
    (lower : Covers (Goal .lStep n (curves valid)) 0 600000)
    (upper : Covers (Goal .uStep n (curves valid)) 45000 600000)
    (ldiff : Difference al u 60000) (udiff : Difference au l 45000) :
    ∃ t : BethProfile.Profile 15000 BethEnvironment.distortion,
      t.e false 63999 ≤ 1 - 1/100000 := by
  let d : BethNumericBridge.LocalData 15000 BethEnvironment.distortion := {
    F := f.eval
    e := fun s ↦ if s then u.eval else l.eval
    C := cf.eval
    A := fun s ↦ if s then (curves valid).au.eval else (curves valid).al.eval
    F_mono := fun h _ ↦ BethNumericFacts.f_mono h
    F_zero := BethNumericFacts.F_zero
    F_cap := BethNumericFacts.F_cap
    e_anti := by
      intro side
      cases side
      · exact BethNumericFacts.l_anti
      · exact BethNumericFacts.u_anti
    e_nonneg := BethNumericFacts.e_nonneg
    cdf_end := BethNumericFacts.cdf_end
    cdf_diff := fun k hk ht ↦ mass k hk ht
    cdf_branch := fun j hj ↦ cdf j (Nat.zero_le _) (by omega)
    buch_end := by
      intro side
      cases side
      · exact BethNumericFacts.al_end _ (curves valid).al.left (curves valid).al.right
      · exact BethNumericFacts.au_end _ (curves valid).au.left (curves valid).au.right
    buch_diff := by
      intro side
      cases side
      · exact ldiff
      · exact udiff
    lower_branch := fun j hj ↦ lower j (Nat.zero_le _) hj
    upper_branch := fun j hj hb ↦ upper j hb hj
  }
  exact ⟨d.toProfile (by norm_num) (by norm_num [BethEnvironment.distortion]), BethNumericFacts.margin⟩

end BethNumericConclusion

end

section

namespace BethNumericChecksCompact
open BethNumericSpan BethNumericCover BethNumericInstance

private def ds : Array ℕ := #[131073,49248,213040,213280,49200,49488,82640,278552,16480,16387,65919,278531,99071,66303,82304,82688,213664,99839,49464,16408,16432,16396,67071,16390,82256,49155,32816,32792,32780,32774,16576,65583,32960,32771,16768,278534,81968,278576,278540,65559,278624,32864,81944,213352,49872,74448,32770,33152,1,278912,65631,41008,82016,81932,280520,49968,49344,41776,65547,99072,49176,49158,278720,49164,83456,40963,17920,279296,75264,213376,280064,65541,52224,81926,40966,33536,49536,40984,41056,33080,65727,41152,262600,40972,98687,82112,41728,767,214432,98688,81923,65538,74064,278600,16672,101375,16385,213160,32769,68607,49920,1536,16720,17104,17152,196656,278936,40961,34304,213088,278984,41680,272328,768,96,213760,206240,278529,383,16456,43312,76800,33488,16696,216424,208232,65537,16552,8864,53856,213004,45664,49272,196609,82064,16648,16528,3,6,11,1535,16624,213184,16504,204806,279704,12,24,32773,50688,114736,16816,17080,49368,49153,8240,8912,35840,48,720,197280,17056,212998,16600,17512,16792,213016,206336,205568,204848,262168,262216,262147,262145,98495,192,2,32959,55296,81921,114712,17008,17200,17800,8204,9728,41272,8195,8600,8198,8960,43000,42280,360,196704,245856,17176,50784,17896,19456,17440,18160,16840,214528,205184,204992,204824,204812,204896,9584,312,262240,196992,49296,16888,262528,32888,262192,294924,294936,262336,205160,98399,32779,163841,98352,33535,22528,51864,19816,16744,81992,82424,82472,16912,82520,82160,16864,82568,82208,82616,49632,82760,82400,82040,83216,16984,82496,17344,73944,8312,8288,75120,8336,8384,9008,8648,8528,74400,9056,74040,41368,41344,74136,9320,73776,8504,76128,9224,8193,384,33944,456,1080,197376,213400,245784,245772,245763,212995,245808,213112,213136,213592,214000,17128,19072,51528,50808,17680,50088,20152,52800,20872,52080,51360,17248,50640,17968,18688,18016,21040,214120,18328,237616,8216,205088,205472,42592,10856,11576,44032,264,262552,32912,196620,196611,196614,196632,49224,49320,213256,17488,279272,17992,279008,280184,279824,279464,213928,18880,278744,213208,19600,278792,18376,278840,17872,279656,17608,294918,262912,33848,1944,200040,264136,198960,19768,215344,207560,206840,271656,270792,270408]
private def codes : Array ℕ := #[0x34000c00034000c00034000c00034000c00034000c000340057,0x28000a00028005400028000a00028005400028000a000280076,0x18040601018040601018040601018040601018040601018040608,0x10164000c00034000c000b8421d0e06c342910164000c000340057,0xb8421d0e06c342910164000c00034000c000b8421d0e06c3472,0x80c02030080c02030080c02030080c02030080c02030080c025e,0xe8003a000e8003a000e8003a000e8003a000e8003a000e8008b,0x138004e00138004e00138004e00138004e00138004e00138004e30,0xf8003e000f8003e000f8003e000f8003e000f8003e000f8003e30,0x30000d00030000d00030000d00030000d00030000d000300057,0x34000d00034000c000b8421d0e06c342910164000c000340057,0xb00022000b0002c000b00022000b0002c000b00022000b0002c30,0x582c462603894503e1890c8c2b160d8160b118980e25140f86268,0x190006400190006400190006400190006400190006400190006430,0xd0a4402f1d80022000b0002200170843a1c0d8685220178ec008c,0x88005c210e870361a148805e3b00044001600044002e108743893,0x178ec0011000580011000b8421d0e06c3429100bc7600088002c30,0x10874381b0d0a4402f1d80022000b0002200170843a1c0d86852af,0x88002c00088005c210e870361a148805e3b0004400160004400b0,0xd8685220178ec0011000580011000b8421d0e06c3429100bc7630,0x44002e10874381b0d0a4402f1d80022000b0002200170843a92,0x100bc7600088002c00088005c210e870361a148805e3b00044008c,0x170843a1c0d8685220178ec0011000580011000b8421d0e06c3472,0x44001600044002e10874381b0d0a4402f1d80022000b0002230,0x2f800c6002f800c6002f800c6002f800c6002f800c6002f800c630,0x410890090485c2a130a0203c22080208448048242e1509850101e,0x10140405010140407090080a02028080a02038480405010140466,0x384804050101404050101c2402028080a02028080e12010140466,0x28080a02028080e12010140405010140407090080a02028080a14,0x1b02c16231301c4a281f0c48646158b06c0b0588c4c07128a07c22,0x2d800b600181f800303f000607e000c0fc00181f800303f2150a30,0x2d800b6002d800b6002d800b6002d800b6002d800b6002d800b630,0x238008e00238008e00238008e0023801125b00224b6004496c0089,0x238008e00238008e00238008e00238008e00238008e00238008e30,0xe8003a002288e004511c008a238008e00238008e00238008e30,0x138004e00138004e00138004e00138004e00138004e0013801248b,0xf8003e000f8003e000f8003e000f8003e00138004e00138004e30,0x190003e000f8003e000f8003e000f8003e000f8003e000f8003e30,0x1900064001900064001900064001900064006f0006400190006430,0x28000a00028000a000280006400190006400190006400190006430,0x28000a00028000a00028000a00028000a00028000a00028000a030,0x5000140005000140005000a00028000a00028000a00057000a030,0x5000140005000140005000a800050001400068001a00050001430,0x5000a800050001400050001400050001400050001400050001430,0x5000a80005000140005000a800050001400050001400050001430,0x34000c001c4180006000180005000a80005000a80005000a830,0x30000d00028005400028000a00028005400028000a000280076,0x34000c000440011000440011000440016000440011000440057,0xb0002200588805e3b0004400160004400940e870361a148805e71,0x31188421d0e06c361d10988c4620e188c46210874381b0d0807630,0x580011000b8421d0e06c3429100bc76004a074381b0d0a44030,0x6f870361a148805e3b0004400160004400940e870361a148805e71,0x108843a1c70b80c46210874381b0d0a4402f1d80022000b0002230,0x2f8002c000b0002c00088002c00088016220178ec00e2178805293,0x305700018002f800c630,0x2d168b45a2d168b45a2d168b45a59accc0043225490b272b9164e3,0x24924924924924924924924924924924924924968b45a2d168b409,0x1a8d46a351a8d46a351a8d46a351a9249249249249249249249217,0x1a8d46a351a8d46a351a8d46a351a8d46a351a8d46a351a8d46a15,0x150a8542a150a8542a150a8542a150a8542a150a854b41a8d46a15,0x150a8542a150a8542a150a854b4150a8542a150a8542a150a85413,0x120904824120904824122584824120904824150a8542a150a85413,0x122584824120904824120904824120904824122584824120904814,0x209068341a0d068341a0904824120904824120904824120904814,0x1a0d068341a0d06804120d068341a0d068341a0d068341a0d06808,0x2a954aa0443154aa552a95468341a0d008241a0d068341a0d06808,0x730a81c040c0381c552a8110c552a954aa552a95408862a954aa1e,0x70381c040c0381c0e020601c0e07010300e070380806078103022,0x330900818070381c040c0381c0e020601c0e07010300e070380866,0x70380818070381c040c0381e04030dc0c0f020181c0e020601c22,0x20601c0e070110ee7070381c040c0381c0e020601c0e070103022,0xc0381c0e020601c0e07010300e070380818070381c040c0381c22,0x703808182f0d01c0e020601c0e07010300e070380818070381c14,0x7810300e070380818070381c040c0381c0e020601c0e070103022,0x78100c0f020181e040303c080643ba008060783c1e040303c0867,0x20181e04032d50c040303c0806078100c0f020181e040303c0867,0x30dc0c373fba46e061b8186e061b8181e040303c0806078100c68,0x7811d455078100c0f020181e040303c0806078100c37030dc0cb6,0x78100c0f020181e040303c0806078100c0f020181e040303c0867,0x20181e040303c0806078100c0f020181e040303c08063fbac0867,0x303c08190c8f47e3c020047018023b5d8040303c0806078100c68,0x1f8f008011c0600806020181e040c8647a3f1e01002380c0100c14,0x201808060781032191e8fc7804008e03004030100c0f020643217,0xc8f47e3c0200470180201808777703c08190c8f47e3c020047066,0x1c0600806020181e040c8647a3f1e01002380c0100c040303c0809,0x781032191e8fc7804008e03004030100c0f02064323d1f8f00808,0x200470180201808977783c08190c8f47e3c020047018020180867,0x20181e040c8647a3f1e01002380c0100c040303c08190c8f47e13,0x1e8fc7804008e03004030100c0f02064323d1f8f008011c0600867,0x201808063bbc008190c8f47e3c020047018020180806078103209,0x20047018020180806078100c0f0783c08190c8f47e3c020047066,0xc8f47e3c020047018020180806078100c0f0783c08190c8f47e13,0x781032191e8fc7804008e03004030100c0f020181e0f4b8600809,0x1e0181e0f0781032191e8fc7804008e03004030100c0f020181e68,0x20181e040303c1e0f02064323d1f8f008011c0600806020181e13,0x20600806020181e040303c1e0f02064323d1f8f008011c0600867,0x1e8fc7804008e03004320186e060783c1e040c8647a3f1e0100288,0x30dd302a200dc32191e8fc7804008e03004320186e06200dc3209,0x1f8f008011c0600864030dc0c401b864323d1f8f008011c0600868,0x1b81880370c8647a3f1e01002380c010bcf1030dc0c401b8643217,0x1e01002380c010c8061b81880370c8647a3f1e01002380c010c867,0x31006e190c8f47e3c020047018021900c3703261e4370c8647a15,0x8e0300432235e637031006e190c8f47e3c020047018021900cb6,0x202dde8370310080401b8e07018021900c37031006e3d1e8fc7814,0x4c8188040200dc0c40201006e0620235ea401b8188040200dc0c42,0x1e0110c0432018803703101f0f7200dc0c40201006e062010080f6,0x268cc9c51359acd6412514c9a4d25104d66b358fd349a4d0647a15,0x28be9f2332b0b4722d220e482412514c9a3327144b8332b12894b8,0x1c904824a29934664e289706656168e45a441c904824a2993466fb,0x2e0ccac2d1c8b5fafc1c904824a29934664e289706656168e45ab9,0x209049453268cc9c512e0ccac2d1c8b48839209049453268cc9cfe,0x199585a3916910724120928a64d19938a25c19c01742d1c8b488ff,0x20928a64d19938a25c199585a3916910724120928a64d19938a301,0x2b0b4722d220e482412514c9a3327144b8332b0b4722d81c0872bb,0x29934664e2897066565e410722d220e482412514c9a3327144b89b,0x168e45a441c904824a29934664e289706656168e45a441c90482bd,0x268cc9c512e0ccac2d1c8b4889b2b104824a29934664e2897066be,0x5e4145a441c9289453268cc9c512e0ccac2d1c8b488392090494b8,0x2514c9a3327144b8332b0b4722d220e4a653268cc9c512e0ccac9c,0x198b4883928944b8332b0b46706289389a4120928a633359acd6bb,0x22110722d221108839169121107220e45a4422110722d2211088be,0x3c9e05a80859e05a793c0b4f30a5f8b4f2781691088441ca0212b9,0x86944ac2d3c0b4f278169e618c0169e4f09c,0x363061e6c3612c964b2592c964b2592c5e2f178bc5e2f178bc5f0e,0x36194cb11881b0ca65329b0ca65389c4e24b4fa78e26c4ea753a65,0x1e0f4326231188381a610a540295044852a0389c8ca6536194ca65,0x800420010800420010800420010800420012600c024c018049808,0x8400210008400210008400210008400287898042001080042008,0x84002100084002100084002100084002100084002100084002a1,0x9b587185145e2d158a0042001080042001080042001080056a14,0x18040601018040601018040601018040601018040601018054677,0x80c02030080c02030080c02030080c021e368040601018040608,0x1804060101804060101804da8e0080c02030080c02030080c025e,0x80c02030080c027f8c8040601018040601018040601018040608,0x4446802030080c02030080c02030080c02030080c02030080c025e,0x80c02030080c02030080c02030080c020300a3cc201018040608,0x2280406450080c02030080c02030080c02030080c02030080c025e,0x2280412090b8542614041b410030080c3c8e0080c8a0101914025e,0x191402032280412090b8542614041b410030080c8a0101914025e,0x80c8a010191402032280412090b8542614041b410030080c8a08,0xa84c28080f00c10100084002032280412090b8542614041b4105e,0x800420730082412170a84c28080f00c1010009de3673008241217,0x485c2a130a0203c030404002103980412090b8542614040780608,0x4078441000840e601048242e1509850101e018202001081cc0209,0x8020b001048242e1509850101e1104010978e00412090b8542614,0x2c00412090b85426140407844100416002090485c2a130a0203c22,0x48242e1509850101e1104010580082412170a84c28080f0882008,0xa84c28080f0882008211618a090485c2a130a0203c2208021891d,0xf08820082147898090485c2a130a0203c22080208458628241217,0x43182648048242e1509850101e1104010422402412170a84c2808,0x2402412170a84c28080f08820082112012090b85426140407844a1,0xb85426140407844100410890090485c2a130a0211014110401042,0xa0203c220802084988f82412170a84c28080f0882008211201209,0x111788a082112012090b85426140407844100410890090485c2a13,0x48242e1509850101e1104010425bc8012090b85426140407844a1,0xa84c28080f088200846c8490090485c2a130a0203c220802084c7,0x4c96102584096191242c204b12391161021e0f0882008211202e17,0xb824c06030054c060300242e15098503c682416193262c204b125,0xb85426140407844100405c2e1509850101e30180c0090b8542613,0xa0203c22080208448048242e1509850101e47a1c2008211201209,0x1104010429449c12090b85426140407844100410890090485c2a13,0x48242e1509850101e1104010422402412170a84c28080f08994a3,0xa84c28080f0882008214aa52090485c2a130a0203c220802084c7,0x40784410042954848048242e1509850101e110401042240241217,0x1104010422402412170a84c28080f08820082112012090b8542614,0x2112012090b85426140407844100410a5664048242e1509850101e,0x211202a1509850101e1104010a4529202e170a84c28080f0882008,0x341a0441e0404c12090b85408603018012170a84c28080f0882008,0x53209046d471cce682512894c0236a388a012c4b40858960783c22,0x2992895306180804014a961025897cb99601081cd960101a090413,0x5f9d1a0cf482419ca966b3150a79a1d106805429c9d33274c89d31,0x144ad373a20ce936601d1067441b4552833a20ce935,0x259489e4b2913c9652279a4f4522792ca44f259489e4b2913cd29f,0x259489e4b2913cd27a2913c96522792d82d32792ca44f349e8a4d2,0x3d1489e693d14a701a259489e4b2913c9652279a4f4522792ca4d2,0x10884381b34b51544f34b51853e9ecf10a8542cecd33a34ce49e9e,0x297424020293004052e8480405260080a5d090080a026a8040817,0x9f93004052e8480405260080a5d090080a4c01014ba12010149814,0x90080a4c01014ba120101498020297424020293004052e8480487,0x1014ba120101498020297424020293004052e8480405260080a77,0x1014bc0101014ba12010149802029300405260080a5d090080a22,0x4129808020293004052e8480405260080a5d090080a4c01014ba7b,0x101c2402028080a02028080e12010140405010140407420080415,0x10140407090080a020280946840101c2402028080a02028080e7b,0x10140407090080a02028080a020384804050101404050101c2414,0x90080a02028080a020384804050101404050101cfed5010140466,0x101404050101c2402028080a02028080e12010140405010140413,0x28080e12010140405010140407090080a02028080a02038480466,0x11fe8002028080a020384804050101404050101c2402028080a14,0x28080a020384804050101404050101c2402028080a02028080e7b,0x101c2402028080a02028080e12010140405010140407090080a14,0x10140407090080a02440e004050101c2402028080a02028080e7b,0x11140a022281c24022281404450384804050101404050101c2414,0x11140a022281c160b118980e251421004071581c240247d040e7b,0x90088a05011140e0b0588c4c07128a10802038ac0e12011140e7b,0x38480445028088a070582c46260389450840101c5607090088a13,0x11a824022281404450382c16231301c4a28420080e2b038480422,0x128a0c20718848046a3b80c58023502c16231301c4a283081c627b,0x11a8160b118980e25141840e3109008d42b16008d40b0588c4c13,0x38c42402350ac58023502c16231301c4a283081c6212011a85667,0x582c4626038945061038c4246e158b0046a0582c462603894507f,0x128a0c20718848dc2b4882c16231301c4a283081c6212370acef42,0x18848dc2b4882c16231301c4a283081c6212370ad220b0588c4c13,0xa182c16231301c4a283081c6212370ad220b0588c4c07128a0c213,0x1301c4a283081c6243230ac58360582c4626038945061038c486c4,0x21918562ca20c4160b118980e25141840e3121918562c1b02c1617,0x3894503e1890c8c2b160d8160b118980e25140f862436301c5667,0x21918562c1b02c16231301c4a28440946243230ac58360582c4615,0x3894503e1890c8c2b160d8160b118980e25140f86243230accc22,0x21918562c1b02c16231301c4a281f0c4bd45230ac58360582c4615,0xa302c16231301c4a281f0c48646158b06c0b0588c4c07128a07c22,0x3894503e1890c8c2b160d8160b118980e25140f86243230ac5866,0x1890c8c2b160d846231301c4a281f0c4868da38ac58360582c4615,0x64d2cf82c1b1f05836a552458363e0b06c7c16322907c160d87c1e,0x3a898ea753a82c4626038947c43158b06d4da60b06c7c160d8f867,0x128a07c312188c462603894503e3a9d4ea0b118980e071182cea60,0x230ac58360582c462603894503e47d388646158b06c0b0588c4c13,0x128a07c3121918562c1b02c16231301c4a281f0c4864615b59334f,0x230ac58360582c462603894503e18b2aa046158b06c0b0588c4c13,0x128a07c3121918562c1b02c16231301c4a281f0c48646158b1ad51,0x230ac58360582c462603894503e1890d4b52158b06c0b0588c4c13,0x128a07c3121918562c1b02c16231301c4a281f0c48646158b2a668,0x8e0986e158b06c261301c4a281f0c486a4350ac58361188c4c13,0x6d06db6ad56ab559546d2a9b21b55b6156d7279489e1c0e874369e,0xacd60f5576cd58d8526e360d2aa6b93ca55527aadb8d36dab1588a,0x268cc704c321b8562cae0b06d5b010b12a6e0913040290d06ab49f,0x3837550cc6733d209054b419aa7379c0fa6f38202ba6f2714c94bd,0x381f4de703e9bd015f3e9bce07d379c1a35e379c0fa6f381f5009b,0x1349d615d581ba9c]

private theorem certifiedStarts : Valid :=
  ⟨BethNumericFacts.f_starts, BethNumericFacts.l_starts, BethNumericFacts.u_starts,
   BethNumericFacts.cf_starts, BethNumericFacts.al_starts, BethNumericFacts.au_starts⟩

private structure Book where
  series : Series
  ends : Array ℕ
  marks : Array ℕ

private def endpoint (b : Book) (i : ℕ) := b.ends[i]?.getD 0

private structure Page where
  x : ℕ
  y : ℕ
  z : ℕ
  f : ℕ
  count : ℕ
  code : ℕ

private def page (b : Book) (i : ℕ) : Page :=
  let u := b.marks[i]?.getD 0
  ⟨u%1024, u/1024%1024, u/1048576%1024, u/1073741824%1024,
    u/1099511627776%32, codes[u/35184372088832]?.getD 0⟩

private def test (b : Book) (i : ℕ) : Bool :=
  let p := page b i
  verify certifiedStarts b.series (endpoint b i) (endpoint b (i+1)) p.x p.y p.z p.f (decode ds p.count p.code)

private def Segment (v : Valid) (b : Book) (i size : ℕ) : Prop :=
  Covers (Goal b.series n (curves v)) (endpoint b i) (endpoint b (i+size))

private def checks (b : Book) (i : ℕ) : ℕ → Bool
  | 0 => true
  | size+1 => test b i && checks b (i+1) size

private theorem certify (v : Valid) (b : Book) (i size : ℕ) (h : checks b i size = true) :
    Segment v b i size := by
  obtain rfl : v = certifiedStarts := by cases v; rfl
  induction size generalizing i with
  | zero =>
    intro j h₁ h₂
    exact False.elim (Nat.not_lt_of_ge h₁ h₂)
  | succ size ih =>
    simp only [checks, Bool.and_eq_true] at h
    obtain ⟨h₁,h₂⟩ := h
    let p := page b i
    have H := packed certifiedStarts b.series (endpoint b i) (endpoint b (i+1)) p.x p.y p.z p.f ds p.count p.code h₁
    unfold Segment
    rw [show i+(size+1) = i+1+size by omega]
    exact join H (ih (i+1) h₂)

private def cm : Book := ⟨.cMass,#[30000,30026,30062,30125,30197,30288,30432,30576,30720,31007,31295,31583,31871,32351,32927,33503,34079,34703,35855,37007,38159,39791,42095,45359,50735,55343,59951,66864,71472,76080,80688,85296,89904,94512,99888,109104,118320,127536,143664,152880,162096,171312,180528,189744,198960,208176,214128,217392,223344,226608,232560,235824,241776,245040,250992,254256,260400,266544,272688,281856,289583,299952,306477,317231,324888,332592,343152,349487,360240,370991,389423,407855,426287,427439,432432,441600,449327,459696,466221,476975,484632,492336,502896,509231,519984,527663,533880,549167,586031,622895,630000],#[0x3d80000100000,0x3f80000b02800,0x4180001605800,0x4380002108000,0x4580002d0b000,0xd8000370dc00,0xd80004310c00,0xd80004f13c00,0x4780005b16c00,0xf80006719800,0xf8000731c800,0xf80007f1f800,0x4980008b22800,307863414265856,307863426861056,307863439456256,0x4b8000bb2e800,483785325090816,0x4d8000d334800,483785350281217,0x4f8000eb3a801,0x518000f73d801,0x5380010340801,0x5580010f43802,0x5780011b46803,0x5980012749804,0x5b8001334c806,61572984928270,61572997523473,61573010118676,61573022713879,61573035309082,61573047904285,0x5d80018661820,343048049805347,343048062400553,343048074995759,0x5f8001b66d835,26388751386687,26388763981893,26388776577099,26388789172305,26388801767511,26388814362717,26388826957923,0x780021685869,0x980021d87478,0x78002228888a,0x98002298a499,0x780022e8b8ab,0x98002358d4ba,0x780023a8e8cc,0x9800241904db,0x7800246918ed,0x980024d934fc,378232623417614,378232631814426,378232640211238,518970136963378,554154514300228,589338892685653,624523271073125,659707647360376,694892027844998,730076404133273,765260782519721,800445160906170,835629538241996,0x618002a3a8ddb,413417087870442,413417100465645,413417113060848,0x638002ceb35f3,0x658002ceb3a0b,518970246122014,554154623458864,589339001844289,624523380231761,659707756519012,694892137003634,730076513291909,765260891678357,800445270064806,835629647400632,0x6780030bc2ec7,0x69800310c3ed9,0x6b800314c52ed,870814045729528,870814058324734,0x6c900335cd304]⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm0(v : Valid) : Segment v cm 0 4 :=
  certify v cm 0 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm4(v : Valid) : Segment v cm 4 4 :=
  certify v cm 4 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm8(v : Valid) : Segment v cm 8 4 :=
  certify v cm 8 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm12(v : Valid) : Segment v cm 12 4 :=
  certify v cm 12 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm16(v : Valid) : Segment v cm 16 4 :=
  certify v cm 16 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm20(v : Valid) : Segment v cm 20 4 :=
  certify v cm 20 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm24(v : Valid) : Segment v cm 24 4 :=
  certify v cm 24 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm28(v : Valid) : Segment v cm 28 4 :=
  certify v cm 28 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm32(v : Valid) : Segment v cm 32 4 :=
  certify v cm 32 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm36(v : Valid) : Segment v cm 36 4 :=
  certify v cm 36 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm40(v : Valid) : Segment v cm 40 4 :=
  certify v cm 40 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm44(v : Valid) : Segment v cm 44 4 :=
  certify v cm 44 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm48(v : Valid) : Segment v cm 48 4 :=
  certify v cm 48 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm52(v : Valid) : Segment v cm 52 4 :=
  certify v cm 52 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm56(v : Valid) : Segment v cm 56 4 :=
  certify v cm 56 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm60(v : Valid) : Segment v cm 60 4 :=
  certify v cm 60 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm64(v : Valid) : Segment v cm 64 4 :=
  certify v cm 64 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm68(v : Valid) : Segment v cm 68 4 :=
  certify v cm 68 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm72(v : Valid) : Segment v cm 72 4 :=
  certify v cm 72 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm76(v : Valid) : Segment v cm 76 4 :=
  certify v cm 76 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm80(v : Valid) : Segment v cm 80 4 :=
  certify v cm 80 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm84(v : Valid) : Segment v cm 84 4 :=
  certify v cm 84 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cm88(v : Valid) : Segment v cm 88 2 :=
  certify v cm 88 2 (by decide +kernel)
theorem cMass (v : Valid) : Covers (Goal .cMass n (curves v)) 30000 630000 :=
  (join (join (join (join (cm0 v) (cm4 v)) (join (cm8 v) (join (cm12 v) (cm16 v)))) (join (join (cm20 v) (join (cm24 v) (cm28 v))) (join (cm32 v) (join (cm36 v) (cm40 v))))) (join (join (join (cm44 v) (join (cm48 v) (cm52 v))) (join (cm56 v) (join (cm60 v) (cm64 v)))) (join (join (cm68 v) (join (cm72 v) (cm76 v))) (join (cm80 v) (join (cm84 v) (cm88 v))))))

private def cs : Book := ⟨.cStep,#[0,30039,30162,30384,30672,31200,31776,32736,33888,35376,37584,40560,45360,53424,60336,69936,76848,84480,91440,99120,111408,122928,138240,151344,163632,175152,182784,187380,192816,196605,202560,206640,211920,216624,221178,226608,233424,239613,246576,255000,262704,270000,276474,287232,294900,304944,313320,322560,331680,347952,375000,397320,397800,405312,412464,423552,430080,441648,448509,460032,466932,477696,485352,495408,503802,510000,538416,576816,600001],#[0x6f80000000000,0x7180000003c07,0x7380000009c07,0x758000000fc07,0x7780000015c07,0x798000001bc08,0x7b80000021c09,0x7d80000027c0a,0x7f8000002dc0c,0x818000003380d,0x838000003940e,0x858000003ec10,0x8780000043c13,0x8980000048818,0x8b8000004d01d,0x8d80000051823,0x8f80000056028,0x918000005ac2d,0x938000005f831,0x9580000064436,0x978000006843d,0x998000006c045,0x9b8000006f44f,0x9d80000073057,0x9f8000007705f,0xa18000007ac67,0xa38000007d075,0xa58000007e887,0xa780000080897,0xa9800000818aa,0xab800000838ba,0xad800000850cc,0xaf800000868dd,0xb1800000884ee,0xb380000089901,0xb58000008b910,0xb78000008d920,0xb98000008f930,0xbb8000009213d,0xbd8000009494a,0xbf80000097557,0xc180000099965,0xc38000009b177,0xc58000009cd87,0xc78000009e19a,0xc98000009fdaa,0xcb800000a11bd,0xcd800000a29ce,0xcf800000a41df,0xd1800000a6deb,0xd3800000ab1f0,0xd5800000aedf8,0xd7800000aee10,0xd9800000b0222,0xdb800000b1635,0xdd800000b3245,0xdf800000b4259,0xe1800000b6268,0xe3800000b727c,0xe5800000b8e8c,0xe7800000ba29e,0xe9800000bbeaf,0xeb800000bd2c1,0xed800000beed1,0xef800000c02e4,0xf1800000c12f7,0xf3800000c5efb,0xf5000000c9b01]⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs0(v : Valid) : Segment v cs 0 4 :=
  certify v cs 0 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs4(v : Valid) : Segment v cs 4 4 :=
  certify v cs 4 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs8(v : Valid) : Segment v cs 8 4 :=
  certify v cs 8 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs12(v : Valid) : Segment v cs 12 4 :=
  certify v cs 12 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs16(v : Valid) : Segment v cs 16 4 :=
  certify v cs 16 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs20(v : Valid) : Segment v cs 20 4 :=
  certify v cs 20 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs24(v : Valid) : Segment v cs 24 4 :=
  certify v cs 24 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs28(v : Valid) : Segment v cs 28 4 :=
  certify v cs 28 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs32(v : Valid) : Segment v cs 32 4 :=
  certify v cs 32 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs36(v : Valid) : Segment v cs 36 4 :=
  certify v cs 36 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs40(v : Valid) : Segment v cs 40 4 :=
  certify v cs 40 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs44(v : Valid) : Segment v cs 44 4 :=
  certify v cs 44 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs48(v : Valid) : Segment v cs 48 4 :=
  certify v cs 48 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs52(v : Valid) : Segment v cs 52 4 :=
  certify v cs 52 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs56(v : Valid) : Segment v cs 56 4 :=
  certify v cs 56 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs60(v : Valid) : Segment v cs 60 4 :=
  certify v cs 60 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem cs64(v : Valid) : Segment v cs 64 4 :=
  certify v cs 64 4 (by decide +kernel)
theorem cStep (v : Valid) : Covers (Goal .cStep n (curves v)) 0 600001 :=
  (join (join (join (join (cs0 v) (cs4 v)) (join (cs8 v) (cs12 v))) (join (join (cs16 v) (cs20 v)) (join (cs24 v) (cs28 v)))) (join (join (join (cs32 v) (cs36 v)) (join (cs40 v) (cs44 v))) (join (join (cs48 v) (cs52 v)) (join (cs56 v) (join (cs60 v) (cs64 v))))))

private def ls : Book := ⟨.lStep,#[0,16896,50688,64032,72192,80736,89952,95712,100320,104928,109440,114048,118656,122976,127488,132096,136416,141024,145632,150144,154752,159360,163968,168288,172896,177888,181728,185856,189792,193524,198912,202749,208800,214272,219648,224256,233460,245568,256608,267264,276474,288720,300672,311904,319488,331764,375000,397368,399354,411600,423552,434784,442368,454644,466848,478848,489984,502272,506112,518832,536424,555000,600000],#[0xf780000000000,0xf980000000017,0xfb8000000001f,0xfd8000050142c,0xff80000f03c3a,4529987934776389,4565172319460433,0xb8000360d85e,0xb8000421086a,4600356732483702,96757116658818,96757129254030,4635541141308570,4670725525992613,96757167039665,4705909923271869,0xb8000a1284c8,0xb8000ad2b4d4,4741094333146336,96757228966124,96757241561336,96757254156548,4776278754566416,0xb8000f43d11b,4811463151845671,4846647537579314,4881831920164151,4917016302748989,4952200686383426,4987385064769861,5022569444205897,5057753821542731,5092938200978767,5128122577266001,5163306952503635,5198491327741269,5233675702978902,5268860078216536,5304044452404570,5339228825543004,5374413199731037,5409597573919071,905997948647777,5444781950206307,5479966323344741,5515150697532774,5550335076968814,5585519452206449,5620703825344881,5655888199532915,905997969639797,5691072575820151,5726256948958585,5761441323146618,5796625697334652,5831810071522686,5866994444661120,5902178818849154,5937363191987587,5972547582969221,6007731969752464,6037418800496022]⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls0(v : Valid) : Segment v ls 0 4 :=
  certify v ls 0 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls4(v : Valid) : Segment v ls 4 4 :=
  certify v ls 4 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls8(v : Valid) : Segment v ls 8 4 :=
  certify v ls 8 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls12(v : Valid) : Segment v ls 12 4 :=
  certify v ls 12 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls16(v : Valid) : Segment v ls 16 4 :=
  certify v ls 16 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls20(v : Valid) : Segment v ls 20 4 :=
  certify v ls 20 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls24(v : Valid) : Segment v ls 24 4 :=
  certify v ls 24 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls28(v : Valid) : Segment v ls 28 4 :=
  certify v ls 28 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls32(v : Valid) : Segment v ls 32 4 :=
  certify v ls 32 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls36(v : Valid) : Segment v ls 36 4 :=
  certify v ls 36 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls40(v : Valid) : Segment v ls 40 4 :=
  certify v ls 40 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls44(v : Valid) : Segment v ls 44 4 :=
  certify v ls 44 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls48(v : Valid) : Segment v ls 48 4 :=
  certify v ls 48 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls52(v : Valid) : Segment v ls 52 4 :=
  certify v ls 52 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls56(v : Valid) : Segment v ls 56 4 :=
  certify v ls 56 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem ls60(v : Valid) : Segment v ls 60 2 :=
  certify v ls 60 2 (by decide +kernel)
theorem lStep (v : Valid) : Covers (Goal .lStep n (curves v)) 0 600000 :=
  (join (join (join (join (ls0 v) (ls4 v)) (join (ls8 v) (ls12 v))) (join (join (ls16 v) (ls20 v)) (join (ls24 v) (ls28 v)))) (join (join (join (ls32 v) (ls36 v)) (join (ls40 v) (ls44 v))) (join (join (ls48 v) (ls52 v)) (join (ls56 v) (ls60 v)))))

private def us : Book := ⟨.uStep,#[45000,56520,67272,77976,80370,84888,90000,95232,100296,105672,110364,113736,117960,121800,125976,130200,134088,138240,142152,146328,150216,154392,158280,162504,166344,170520,174744,179400,182472,185856,188952,192456,196560,200136,205464,208896,214992,220800,225000,233460,244992,253896,264168,275712,284616,294888,306432,315000,325608,337536,376776,397357,399312,410112,417792,430032,440832,448512,460752,471552,479232,491472,501864,503868,518088,536400,554952,597960,600000],#[6078120679468032,6113312569848847,6148504460229661,6183696351660074,6218882885926962,6254070486588480,6289258086200398,6324446760603739,6359634361265257,6394820888184951,6430008490945667,941249677858957,6465198254834840,976439440698530,0x39811c6b218ac,6500391250445495,6535578854255810,6570766458066124,6605952989184215,6641140594044129,6676327124112620,6711514728972534,941280938125569,6746704491812108,976470700965142,0x398190df3e920,6781897487422763,6817085093332276,6852281284977976,6887478550365500,6922674743060800,6957870934706501,6993072491912519,7028274049118538,7063473460940109,7098678237272399,7133880867170641,7169085643502931,7204290419835220,7239496269909333,0x3b84d13b55957,7274722522127705,7309928371152218,0x3b85c14056d5c,7345155696062814,7380361545087327,7415566320370017,7450773242086754,7485979091111268,7521183866393958,7556376834714989,7591578390871408,7626788532764016,449197029836146,7662016931416435,7697221706699125,449261459593591,7732450105351544,7767654880634234,449325889351036,7802883279286653,7838088054569343,7873288534884741,7908489013100947,7943688419674523,7978876017187243,8014063624146354,8030563822102969]⟩
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us0(v : Valid) : Segment v us 0 4 :=
  certify v us 0 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us4(v : Valid) : Segment v us 4 4 :=
  certify v us 4 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us8(v : Valid) : Segment v us 8 4 :=
  certify v us 8 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us12(v : Valid) : Segment v us 12 4 :=
  certify v us 12 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us16(v : Valid) : Segment v us 16 4 :=
  certify v us 16 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us20(v : Valid) : Segment v us 20 4 :=
  certify v us 20 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us24(v : Valid) : Segment v us 24 4 :=
  certify v us 24 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us28(v : Valid) : Segment v us 28 4 :=
  certify v us 28 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us32(v : Valid) : Segment v us 32 4 :=
  certify v us 32 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us36(v : Valid) : Segment v us 36 4 :=
  certify v us 36 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us40(v : Valid) : Segment v us 40 4 :=
  certify v us 40 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us44(v : Valid) : Segment v us 44 4 :=
  certify v us 44 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us48(v : Valid) : Segment v us 48 4 :=
  certify v us 48 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us52(v : Valid) : Segment v us 52 4 :=
  certify v us 52 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us56(v : Valid) : Segment v us 56 4 :=
  certify v us 56 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us60(v : Valid) : Segment v us 60 4 :=
  certify v us 60 4 (by decide +kernel)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 5000000 in
private theorem us64(v : Valid) : Segment v us 64 4 :=
  certify v us 64 4 (by decide +kernel)
theorem uStep (v : Valid) : Covers (Goal .uStep n (curves v)) 45000 600000 :=
  (join (join (join (join (us0 v) (us4 v)) (join (us8 v) (us12 v))) (join (join (us16 v) (us20 v)) (join (us24 v) (us28 v)))) (join (join (join (us32 v) (us36 v)) (join (us40 v) (us44 v))) (join (join (us48 v) (us52 v)) (join (us56 v) (join (us60 v) (us64 v))))))

end BethNumericChecksCompact

end

section

namespace BethNumericBoundary

open BethNumericMesh BethNumericData BethNumericInstance BethNumericPotView BethNumericCover

def okay (m src : Mesh) (i : ℕ) : Bool :=
  checkSource n m src i && checkSlack n m src i

def run (m src : Mesh) (a : ℕ) : ℕ → Bool
  | 0 => true
  | q+1 => okay m src (a+q) && run m src a q

theorem cert (m src : Mesh) (a w : ℕ) (h : run m src a w = true) :
    Covers (fun i ↦ okay m src i = true) a (a+w) := by
  induction w with
  | zero => intro j hj hj'; omega
  | succ q ih =>
    rw [run,Bool.and_eq_true] at h
    intro j hlo hhi
    by_cases he : j = a+q
    · simpa [he] using h.1
    · exact ih h.2 j hlo (by omega)

theorem result (m src : Mesh) (hm : m.Starts) (hs : src.Starts) (endIndex : ℕ)
    (hsize : m.last+1 = endIndex)
    (checks : Covers (fun i ↦ okay m src i = true) 0 endIndex)
    (k : ℕ) (hlo : (m.row 0).start ≤ k) (hhi : k < (m.row (m.last+1)).start) :
    (2*(k:ℝ)+1)*src.eval (k-n) ≤
      (m.evalUsing (potPiece n m src) k-m.evalUsing (potPiece n m src) (k+1))*((n : ℕ):ℝ)^2 := by
  have ck (i : ℕ) (hi : i ≤ m.last) : checkSource n m src i = true ∧ checkSlack n m src i = true := by
    simpa only [okay,Bool.and_eq_true] using checks i (Nat.zero_le _) (by omega)
  exact mass_diff n hm hs (fun i hi => (ck i hi).1) (fun i hi => (ck i hi).2) k hlo hhi

end BethNumericBoundary

end

section

namespace BethNumericPotChecks
open BethNumericCover BethNumericBoundary BethNumericData

set_option maxRecDepth 10000 in
private theorem al0 : Covers (fun i ↦ okay al u i = true) 0 24 :=
  cert al u 0 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al1 : Covers (fun i ↦ okay al u i = true) 24 48 :=
  cert al u 24 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al2 : Covers (fun i ↦ okay al u i = true) 48 72 :=
  cert al u 48 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al3 : Covers (fun i ↦ okay al u i = true) 72 96 :=
  cert al u 72 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al4 : Covers (fun i ↦ okay al u i = true) 96 120 :=
  cert al u 96 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al5 : Covers (fun i ↦ okay al u i = true) 120 144 :=
  cert al u 120 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al6 : Covers (fun i ↦ okay al u i = true) 144 168 :=
  cert al u 144 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al7 : Covers (fun i ↦ okay al u i = true) 168 192 :=
  cert al u 168 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al8 : Covers (fun i ↦ okay al u i = true) 192 216 :=
  cert al u 192 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al9 : Covers (fun i ↦ okay al u i = true) 216 240 :=
  cert al u 216 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al10 : Covers (fun i ↦ okay al u i = true) 240 264 :=
  cert al u 240 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al11 : Covers (fun i ↦ okay al u i = true) 264 288 :=
  cert al u 264 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al12 : Covers (fun i ↦ okay al u i = true) 288 312 :=
  cert al u 288 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al13 : Covers (fun i ↦ okay al u i = true) 312 336 :=
  cert al u 312 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al14 : Covers (fun i ↦ okay al u i = true) 336 360 :=
  cert al u 336 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al15 : Covers (fun i ↦ okay al u i = true) 360 384 :=
  cert al u 360 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al16 : Covers (fun i ↦ okay al u i = true) 384 408 :=
  cert al u 384 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al17 : Covers (fun i ↦ okay al u i = true) 408 432 :=
  cert al u 408 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem al18 : Covers (fun i ↦ okay al u i = true) 432 439 :=
  cert al u 432 7 (by rfl)
theorem alRows : Covers (fun i ↦ okay al u i = true) 0 439 :=
  (join (join (join (join al0 al1) (join al2 al3)) (join (join al4 al5) (join al6 (join al7 al8)))) (join (join (join al9 al10) (join al11 (join al12 al13))) (join (join al14 al15) (join al16 (join al17 al18)))))
set_option maxRecDepth 10000 in
private theorem au0 : Covers (fun i ↦ okay au l i = true) 0 24 :=
  cert au l 0 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au1 : Covers (fun i ↦ okay au l i = true) 24 48 :=
  cert au l 24 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au2 : Covers (fun i ↦ okay au l i = true) 48 72 :=
  cert au l 48 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au3 : Covers (fun i ↦ okay au l i = true) 72 96 :=
  cert au l 72 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au4 : Covers (fun i ↦ okay au l i = true) 96 120 :=
  cert au l 96 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au5 : Covers (fun i ↦ okay au l i = true) 120 144 :=
  cert au l 120 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au6 : Covers (fun i ↦ okay au l i = true) 144 168 :=
  cert au l 144 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au7 : Covers (fun i ↦ okay au l i = true) 168 192 :=
  cert au l 168 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au8 : Covers (fun i ↦ okay au l i = true) 192 216 :=
  cert au l 192 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au9 : Covers (fun i ↦ okay au l i = true) 216 240 :=
  cert au l 216 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au10 : Covers (fun i ↦ okay au l i = true) 240 264 :=
  cert au l 240 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au11 : Covers (fun i ↦ okay au l i = true) 264 288 :=
  cert au l 264 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au12 : Covers (fun i ↦ okay au l i = true) 288 312 :=
  cert au l 288 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au13 : Covers (fun i ↦ okay au l i = true) 312 336 :=
  cert au l 312 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au14 : Covers (fun i ↦ okay au l i = true) 336 360 :=
  cert au l 336 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au15 : Covers (fun i ↦ okay au l i = true) 360 384 :=
  cert au l 360 24 (by rfl)
set_option maxRecDepth 10000 in
private theorem au16 : Covers (fun i ↦ okay au l i = true) 384 385 :=
  cert au l 384 1 (by rfl)
theorem auRows : Covers (fun i ↦ okay au l i = true) 0 385 :=
  (join (join (join (join au0 au1) (join au2 au3)) (join (join au4 au5) (join au6 au7))) (join (join (join au8 au9) (join au10 au11)) (join (join au12 au13) (join au14 (join au15 au16)))))
end BethNumericPotChecks

end

section

/- The finite integer checks furnish the lower main term at 63999/15000. -/

namespace BethComplete

open BethNumericData BethNumericInstance BethNumericConclusion

theorem finite_profile : ∃ t : BethProfile.Profile 15000 BethEnvironment.distortion,
    t.e false 63999 ≤ 1 - 1/100000 := by
  apply of_checks (BethNumericChecksCompact.cMass valid) (BethNumericChecksCompact.cStep valid)
    (BethNumericChecksCompact.lStep valid) (BethNumericChecksCompact.uStep valid)
  · intro k hk htop
    apply BethNumericBoundary.result al u valid.al valid.u 439 (by decide +kernel)
      BethNumericPotChecks.alRows k
    · exact (show (al.row 0).start ≤ 60000 by decide +kernel).trans hk
    · exact htop.trans_le (by decide +kernel)
  · intro k hk htop
    apply BethNumericBoundary.result au l valid.au valid.l 385 (by decide +kernel)
      BethNumericPotChecks.auRows k
    · exact (show (au.row 0).start ≤ 45000 by decide +kernel).trans hk
    · exact htop.trans_le (by decide +kernel)

end BethComplete

end

theorem OMA.solution : type_of% @Erdos724.erdos_724.variants.beth := by
  obtain ⟨t, hmargin⟩ := BethComplete.finite_profile
  exact BethGoal.of_profile t hmargin
