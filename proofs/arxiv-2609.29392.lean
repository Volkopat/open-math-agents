import OMAStatements.S_arxiv_2609_29392

namespace OMA.P_arxiv_2609_29392

open OMA.S_arxiv_2609_29392

/-! ### Part 1: Properties of `IsLMax`, `lmaxStart`, and Foata's bijection `foataInv` -/

private lemma lmaxStart_mem {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) :
    lmaxStart π p ≤ p ∧ IsLMax π (lmaxStart π p) := by
  unfold lmaxStart
  exact (Finset.mem_filter.mp
    (Finset.max'_mem (Finset.univ.filter (fun q : Fin n => q ≤ p ∧ IsLMax π q)) _)).2

private lemma le_lmaxStart {n : ℕ} (π : Equiv.Perm (Fin n)) {p q : Fin n}
    (hq : q ≤ p) (hlm : IsLMax π q) : q ≤ lmaxStart π p :=
  Finset.le_max' _ q (Finset.mem_filter.mpr ⟨Finset.mem_univ q, hq, hlm⟩)

private lemma lmaxStart_eq_self_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) :
    lmaxStart π p = p ↔ IsLMax π p := by
  constructor
  · intro h; rw [← h]; exact (lmaxStart_mem π p).2
  · intro h; exact le_antisymm (lmaxStart_mem π p).1 (le_lmaxStart π le_rfl h)

private lemma isLMax_zero {n : ℕ} (π : Equiv.Perm (Fin n)) (hn : 0 < n) :
    IsLMax π ⟨0, hn⟩ := fun q hq => by
  have := Fin.lt_def.mp hq; dsimp only at this; omega

private lemma lt_of_lmaxStart_lt {n : ℕ} (π : Equiv.Perm (Fin n)) (p q : Fin n)
    (h1 : lmaxStart π p < q) (h2 : q ≤ p) : ¬ IsLMax π q :=
  fun hlm => not_le_of_gt h1 (le_lmaxStart π h2 hlm)

private lemma val_le_lmaxStart {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) :
    π p ≤ π (lmaxStart π p) := by
  rcases eq_or_lt_of_le (lmaxStart_mem π p).1 with heq | hlt
  · rw [heq]
  · by_contra hgt
    push Not at hgt
    have hlm : IsLMax π p := by
      intro q hqp
      rcases lt_or_ge q (lmaxStart π p) with hql | hge
      · exact lt_trans ((lmaxStart_mem π p).2 q hql) hgt
      · rcases eq_or_lt_of_le hge with rfl | hgtl
        · exact hgt
        · have hbound : ∀ k (hk : k < n), (lmaxStart π p).val < k → k < p.val →
              π ⟨k, hk⟩ < π (lmaxStart π p) := by
            intro k
            induction k using Nat.strong_induction_on with
            | h k ih =>
              intro hk hlk hkp
              have hnot : ¬ IsLMax π ⟨k, hk⟩ :=
                lt_of_lmaxStart_lt π p ⟨k, hk⟩ (Fin.lt_def.mpr hlk) (Fin.le_def.mpr (le_of_lt hkp))
              unfold IsLMax at hnot
              push Not at hnot
              obtain ⟨t, htk, htle⟩ := hnot
              rcases lt_trichotomy t (lmaxStart π p) with htl | rfl | hgt'
              · exact lt_of_le_of_lt htle ((lmaxStart_mem π p).2 t htl)
              · exact lt_of_le_of_ne htle (fun h => ne_of_gt (Fin.lt_def.mpr hlk) (π.injective h))
              · exact lt_of_le_of_lt htle (ih t.val (Fin.lt_def.mp htk) t.isLt
                  (Fin.lt_def.mp hgt') (lt_trans (Fin.lt_def.mp htk) hkp))
          exact lt_trans (hbound q.val q.isLt (Fin.lt_def.mp hgtl) (Fin.lt_def.mp hqp)) hgt
    exact lt_of_lmaxStart_lt π p p hlt le_rfl hlm

private lemma val_lt_lmaxStart_of_ne {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n)
    (hne : lmaxStart π p ≠ p) : π p < π (lmaxStart π p) :=
  lt_of_le_of_ne (val_le_lmaxStart π p) (fun h => hne (π.injective h).symm)

private lemma lmaxStart_succ_of_not_isLMax {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n)
    (h : p.val + 1 < n) (hnot : ¬ IsLMax π ⟨p.val + 1, h⟩) :
    lmaxStart π ⟨p.val + 1, h⟩ = lmaxStart π p := by
  apply le_antisymm
  · have hmem := lmaxStart_mem π ⟨p.val + 1, h⟩
    have hlt : lmaxStart π ⟨p.val + 1, h⟩ < ⟨p.val + 1, h⟩ :=
      lt_of_le_of_ne hmem.1 (fun heq => hnot (heq ▸ hmem.2))
    exact le_lmaxStart π (Fin.le_def.mpr (by have := Fin.lt_def.mp hlt; dsimp only at this; omega)) hmem.2
  · exact le_lmaxStart π (le_trans (lmaxStart_mem π p).1 (Fin.le_def.mpr (by dsimp only; omega))) (lmaxStart_mem π p).2

private lemma foataInv_fixed_iff {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n) :
    foataInv π x = x ↔
      IsLMax π (π.symm x) ∧ ∀ h : (π.symm x).val + 1 < n, π (π.symm x) < π ⟨(π.symm x).val + 1, h⟩ := by
  obtain ⟨p, rfl⟩ := π.surjective x
  simp only [Equiv.symm_apply_apply]
  unfold foataInv
  simp only [Equiv.symm_apply_apply]
  constructor
  · intro hfix
    by_cases hlt : p.val + 1 < n
    · rw [dif_pos hlt] at hfix
      by_cases hlm1 : IsLMax π ⟨p.val + 1, hlt⟩
      · rw [if_neg (not_not.mpr hlm1)] at hfix
        have hlp : lmaxStart π p = p := π.injective hfix
        exact ⟨(lmaxStart_eq_self_iff π p).mp hlp, fun _ => hlm1 p (Fin.lt_def.mpr (by dsimp only; omega))⟩
      · rw [if_pos hlm1] at hfix
        exfalso
        have := π.injective hfix
        have hval := congrArg Fin.val this; dsimp only at hval; omega
    · rw [dif_neg hlt] at hfix
      have hlp : lmaxStart π p = p := π.injective hfix
      exact ⟨(lmaxStart_eq_self_iff π p).mp hlp, fun h => absurd h hlt⟩
  · rintro ⟨hlm, hnext⟩
    by_cases hlt : p.val + 1 < n
    · rw [dif_pos hlt]
      have hlm1 : IsLMax π ⟨p.val + 1, hlt⟩ := by
        intro q hq
        have hqp : q ≤ p := Fin.le_def.mpr (by have := Fin.lt_def.mp hq; dsimp only at this; omega)
        rcases eq_or_lt_of_le hqp with rfl | hqlt
        · exact hnext hlt
        · exact lt_trans (hlm q hqlt) (hnext hlt)
      rw [if_neg (not_not.mpr hlm1), (lmaxStart_eq_self_iff π p).mpr hlm]
    · rw [dif_neg hlt, (lmaxStart_eq_self_iff π p).mpr hlm]

private lemma foataInv_injective {n : ℕ} (π : Equiv.Perm (Fin n)) :
    Function.Injective (foataInv π) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := π.surjective x
  obtain ⟨q, rfl⟩ := π.surjective y
  suffices hpq : p = q by rw [hpq]
  unfold foataInv at hxy
  simp only [Equiv.symm_apply_apply] at hxy
  have haux : ∀ a b : Fin n, a < b → lmaxStart π a = lmaxStart π b →
      (∀ h : a.val + 1 < n, IsLMax π ⟨a.val + 1, h⟩) → False := by
    intro a b hab hls ha_lm
    have ha1 : a.val + 1 < n := by have := b.isLt; have := Fin.lt_def.mp hab; omega
    have hlm1 : IsLMax π ⟨a.val + 1, ha1⟩ := ha_lm ha1
    have hle1 : (⟨a.val + 1, ha1⟩ : Fin n) ≤ b :=
      Fin.le_def.mpr (by have := Fin.lt_def.mp hab; dsimp only; omega)
    have hle_ls := le_lmaxStart π hle1 hlm1
    have hla := (lmaxStart_mem π a).1
    rw [← hls] at hle_ls
    have h1 := Fin.le_def.mp (le_trans hle_ls hla)
    dsimp only at h1; omega
  have hstep : ∀ a : Fin n,
      (∃ (ha : a.val + 1 < n), ¬ IsLMax π ⟨a.val + 1, ha⟩ ∧
        (if h : a.val + 1 < n then if ¬ IsLMax π ⟨a.val + 1, h⟩ then π ⟨a.val + 1, h⟩ else π (lmaxStart π a)
          else π (lmaxStart π a)) = π ⟨a.val + 1, ha⟩) ∨
      ((∀ ha : a.val + 1 < n, IsLMax π ⟨a.val + 1, ha⟩) ∧
        (if h : a.val + 1 < n then if ¬ IsLMax π ⟨a.val + 1, h⟩ then π ⟨a.val + 1, h⟩ else π (lmaxStart π a)
          else π (lmaxStart π a)) = π (lmaxStart π a)) := by
    intro a
    by_cases ha : a.val + 1 < n
    · by_cases hlm : IsLMax π ⟨a.val + 1, ha⟩
      · exact Or.inr ⟨fun _ => hlm, by rw [dif_pos ha, if_neg (not_not.mpr hlm)]⟩
      · exact Or.inl ⟨ha, hlm, by rw [dif_pos ha, if_pos hlm]⟩
    · exact Or.inr ⟨fun h => absurd h ha, by rw [dif_neg ha]⟩
  rcases hstep p with ⟨hp1, hpnot, hpeq⟩ | ⟨hplm, hpeq⟩ <;>
    rcases hstep q with ⟨hq1, hqnot, hqeq⟩ | ⟨hqlm, hqeq⟩
  · rw [hpeq, hqeq] at hxy
    have := π.injective hxy
    exact Fin.ext (by have hval := congrArg Fin.val this; dsimp only at hval; omega)
  · rw [hpeq, hqeq] at hxy
    exact absurd (π.injective hxy ▸ (lmaxStart_mem π q).2) hpnot
  · rw [hpeq, hqeq] at hxy
    exact absurd ((π.injective hxy).symm ▸ (lmaxStart_mem π p).2) hqnot
  · rw [hpeq, hqeq] at hxy
    have hls : lmaxStart π p = lmaxStart π q := π.injective hxy
    rcases lt_trichotomy p q with hlt | rfl | hgt
    · exact absurd (haux p q hlt hls hplm) id
    · rfl
    · exact absurd (haux q p hgt hls.symm hqlm) id

private noncomputable def foataInvPerm {n : ℕ} (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (foataInv π) (Finite.injective_iff_bijective.mp (foataInv_injective π))

private lemma foataInvPerm_apply {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n) :
    foataInvPerm π x = foataInv π x := rfl

-- Prove `foataInvPerm` is injective on `Equiv.Perm (Fin n)` (hence a bijection!)
private lemma foataInvPerm_orbit_in_block {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) :
    lmaxStart π (π.symm (foataInv π (π p))) = lmaxStart π p := by
  unfold foataInv
  simp only [Equiv.symm_apply_apply]
  by_cases h1 : p.val + 1 < n
  · rw [dif_pos h1]
    by_cases h2 : IsLMax π ⟨p.val + 1, h1⟩
    · rw [if_neg (not_not.mpr h2), Equiv.symm_apply_apply]
      exact (lmaxStart_eq_self_iff π (lmaxStart π p)).mpr (lmaxStart_mem π p).2
    · rw [if_pos h2, Equiv.symm_apply_apply]
      exact lmaxStart_succ_of_not_isLMax π p h1 h2
  · rw [dif_neg h1, Equiv.symm_apply_apply]
    exact (lmaxStart_eq_self_iff π (lmaxStart π p)).mpr (lmaxStart_mem π p).2

private lemma foataInvPerm_pow_same_block {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) (k : ℕ) :
    lmaxStart π (π.symm ((foataInvPerm π ^ k) (π p))) = lmaxStart π p := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, foataInvPerm_apply]
    have h1 := foataInvPerm_orbit_in_block π (π.symm ((foataInvPerm π ^ k) (π p)))
    rw [Equiv.apply_symm_apply] at h1
    exact h1.trans ih

private lemma foataInvPerm_cycle_step {n : ℕ} (π : Equiv.Perm (Fin n)) (s : Fin n) (_hs : IsLMax π s)
    (d : ℕ) (hd : s.val + d < n) (hblock : ∀ t, 1 ≤ t → (htd : t ≤ d) → ¬ IsLMax π ⟨s.val + t, by omega⟩) :
    (foataInvPerm π ^ d) (π s) = π ⟨s.val + d, hd⟩ := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega) (fun t ht1 ht2 => hblock t ht1 (by omega))]
    rw [foataInvPerm_apply]
    unfold foataInv
    simp only [Equiv.symm_apply_apply]
    have hlt : s.val + d + 1 < n := by omega
    have hnot : ¬ IsLMax π ⟨s.val + d + 1, hlt⟩ := by
      have := hblock (d + 1) (by omega) le_rfl
      convert this using 2
      exact Fin.ext (by dsimp only; omega)
    rw [dif_pos hlt, if_pos hnot]
    rfl

private lemma isLMax_iff_orbit_max {n : ℕ} (π : Equiv.Perm (Fin n)) (p : Fin n) :
    IsLMax π p ↔ ∀ k : ℕ, (foataInvPerm π ^ k) (π p) ≤ π p := by
  constructor
  · intro hlm k
    set q := π.symm ((foataInvPerm π ^ k) (π p))
    have hq : π q = (foataInvPerm π ^ k) (π p) := π.apply_symm_apply _
    rw [← hq]
    have hls : lmaxStart π q = lmaxStart π p := foataInvPerm_pow_same_block π p k
    have hlp : lmaxStart π p = p := (lmaxStart_eq_self_iff π p).mpr hlm
    have := val_le_lmaxStart π q
    rwa [hls, hlp] at this
  · intro hmax
    set s := lmaxStart π p
    have hs : IsLMax π s := (lmaxStart_mem π p).2
    have hsp : s ≤ p := (lmaxStart_mem π p).1
    have hsp' : s.val ≤ p.val := Fin.le_def.mp hsp
    have hp_lt : p.val < n := p.isLt
    have hblock : ∀ t, 1 ≤ t → (ht : t ≤ p.val - s.val) → ¬ IsLMax π ⟨s.val + t, by omega⟩ := by
      intro t ht1 ht2
      exact lt_of_lmaxStart_lt π p ⟨s.val + t, by omega⟩
        (Fin.lt_def.mpr (by dsimp only; omega))
        (Fin.le_def.mpr (by dsimp only; omega))
    have hpow := foataInvPerm_cycle_step π s hs (p.val - s.val) (by omega) hblock
    have hpeq : (⟨s.val + (p.val - s.val), by omega⟩ : Fin n) = p := Fin.ext (by dsimp only; omega)
    rw [hpeq] at hpow
    have hord := orderOf_pos (foataInvPerm π)
    set o := orderOf (foataInvPerm π)
    have hinv : (foataInvPerm π ^ (o - (p.val - s.val) % o)) (π p) = π s := by
      rw [← hpow, ← Equiv.Perm.mul_apply, ← pow_add]
      have hdiv : o ∣ (o - (p.val - s.val) % o) + (p.val - s.val) := by
        have hlt := Nat.mod_lt (p.val - s.val) hord
        have hdm := Nat.div_add_mod (p.val - s.val) o
        have h1 : (o - (p.val - s.val) % o) + (p.val - s.val) = o + o * ((p.val - s.val) / o) := by
          omega
        rw [h1]; exact ⟨1 + (p.val - s.val) / o, by ring⟩
      obtain ⟨m, hm⟩ := hdiv
      rw [hm, pow_mul, pow_orderOf_eq_one, one_pow, Equiv.Perm.one_apply]
    have hle : π s ≤ π p := hinv ▸ hmax _
    have heq : π p = π s := le_antisymm (val_le_lmaxStart π p) hle
    exact (π.injective heq) ▸ hs

private lemma foataInvPerm_injective {n : ℕ} : Function.Injective (foataInvPerm (n := n)) := by
  intro π₁ π₂ hσ
  have hσ_app : ∀ x, foataInv π₁ x = foataInv π₂ x := fun x =>
    congrFun (congrArg DFunLike.coe hσ) x
  have hprefix : ∀ i (hi : i < n), π₁ ⟨i, hi⟩ = π₂ ⟨i, hi⟩ := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      have hprev : ∀ q : Fin n, q.val < i → π₁ q = π₂ q := fun q hq => ih q.val hq q.isLt
      have hlmax_iff : IsLMax π₁ ⟨i, hi⟩ ↔ IsLMax π₂ ⟨i, hi⟩ := by
        cases i with
        | zero => exact ⟨fun _ => isLMax_zero π₂ hi, fun _ => isLMax_zero π₁ hi⟩
        | succ i' =>
          have hi' : i' < n := by omega
          have heq_prev : π₁ ⟨i', hi'⟩ = π₂ ⟨i', hi'⟩ := hprev ⟨i', hi'⟩ (by dsimp only; omega)
          have hstep : ∀ (π : Equiv.Perm (Fin n)),
              ¬ IsLMax π ⟨i' + 1, hi⟩ ↔ ∀ q : Fin n, q.val ≤ i' → foataInv π (π ⟨i', hi'⟩) ≠ π q := by
            intro π
            constructor
            · intro hnot q hq hcontra
              unfold foataInv at hcontra
              simp only [Equiv.symm_apply_apply] at hcontra
              rw [dif_pos hi, if_pos hnot] at hcontra
              have := π.injective hcontra
              have hval := congrArg Fin.val this; dsimp only at hval; omega
            · intro hall hlm
              have hcontra : foataInv π (π ⟨i', hi'⟩) = π (lmaxStart π ⟨i', hi'⟩) := by
                unfold foataInv; simp only [Equiv.symm_apply_apply]
                rw [dif_pos hi, if_neg (not_not.mpr hlm)]
              have hle := Fin.le_def.mp (lmaxStart_mem π ⟨i', hi'⟩).1
              exact hall (lmaxStart π ⟨i', hi'⟩) hle hcontra
          have hnot_iff : ¬ IsLMax π₁ ⟨i' + 1, hi⟩ ↔ ¬ IsLMax π₂ ⟨i' + 1, hi⟩ := by
            rw [hstep π₁, hstep π₂, heq_prev, hσ_app]
            constructor <;> intro h q hq <;> [rw [← hprev q (by omega)]; rw [hprev q (by omega)]] <;> exact h q hq
          exact not_iff_not.mp hnot_iff
      by_cases hlm1 : IsLMax π₁ ⟨i, hi⟩
      · have hlm2 : IsLMax π₂ ⟨i, hi⟩ := hlmax_iff.mp hlm1
        have hmin : ∀ (π : Equiv.Perm (Fin n)) (hlm : IsLMax π ⟨i, hi⟩) (x : Fin n),
            (∀ q : Fin n, q.val < i → π q ≠ x) →
            (∀ k : ℕ, (foataInvPerm π ^ k) x ≤ x) →
            π ⟨i, hi⟩ ≤ x := by
          intro π hlm x hunused hmax
          have hx_lm : IsLMax π (π.symm x) := by
            rw [isLMax_iff_orbit_max, Equiv.apply_symm_apply]; exact hmax
          have hge : i ≤ (π.symm x).val := by
            by_contra hlt
            exact hunused (π.symm x) (by omega) (π.apply_symm_apply x)
          rcases eq_or_lt_of_le hge with heq | hlt
          · have : (⟨i, hi⟩ : Fin n) = π.symm x := Fin.ext heq
            rw [this, Equiv.apply_symm_apply]
          · exact le_of_lt (hx_lm ⟨i, hi⟩ (Fin.lt_def.mpr hlt) |> fun h => by rwa [Equiv.apply_symm_apply] at h)
        have h1le2 : π₁ ⟨i, hi⟩ ≤ π₂ ⟨i, hi⟩ := by
          apply hmin π₁ hlm1 (π₂ ⟨i, hi⟩)
          · intro q hq heq
            rw [hprev q hq] at heq
            have := π₂.injective heq
            have hval := congrArg Fin.val this; dsimp only at hval; omega
          · rw [hσ]; exact (isLMax_iff_orbit_max π₂ ⟨i, hi⟩).mp hlm2
        have h2le1 : π₂ ⟨i, hi⟩ ≤ π₁ ⟨i, hi⟩ := by
          apply hmin π₂ hlm2 (π₁ ⟨i, hi⟩)
          · intro q hq heq
            rw [← hprev q hq] at heq
            have := π₁.injective heq
            have hval := congrArg Fin.val this; dsimp only at hval; omega
          · rw [← hσ]; exact (isLMax_iff_orbit_max π₁ ⟨i, hi⟩).mp hlm1
        exact le_antisymm h1le2 h2le1
      · have hlm2 : ¬ IsLMax π₂ ⟨i, hi⟩ := fun h => hlm1 (hlmax_iff.mpr h)
        cases i with
        | zero => exact absurd (isLMax_zero π₁ hi) hlm1
        | succ i' =>
          have hi' : i' < n := by omega
          have heq1 : foataInv π₁ (π₁ ⟨i', hi'⟩) = π₁ ⟨i' + 1, hi⟩ := by
            unfold foataInv; simp only [Equiv.symm_apply_apply]; rw [dif_pos hi, if_pos hlm1]
          have heq2 : foataInv π₂ (π₂ ⟨i', hi'⟩) = π₂ ⟨i' + 1, hi⟩ := by
            unfold foataInv; simp only [Equiv.symm_apply_apply]; rw [dif_pos hi, if_pos hlm2]
          rw [← heq1, ← heq2, hprev ⟨i', hi'⟩ (by dsimp only; omega), hσ_app]
  ext p
  exact congrArg Fin.val (hprefix p.val p.isLt)

private noncomputable def foataEquiv (n : ℕ) : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) :=
  Equiv.ofBijective foataInvPerm (Finite.injective_iff_bijective.mp foataInvPerm_injective)

/-! ### Part 2: Counting fixed points of `foataInv` and compositions (stars and bars) -/

private def foataFPSet {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun x => foataInv π x = x

private lemma card_foataFP_empty (n : ℕ) :
    Fintype.card {π : Equiv.Perm (Fin n) // foataFPSet π = ∅} = derangementCount n := by
  unfold derangementCount
  refine Fintype.card_congr ?_
  refine Equiv.subtypeEquiv (foataEquiv n) fun π => ?_
  simp only [foataFPSet, Finset.eq_empty_iff_forall_notMem, Finset.mem_filter, Finset.mem_univ,
    true_and, foataEquiv, Equiv.ofBijective_apply, foataInvPerm_apply]

private lemma card_filter_add_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] :
    (s.filter p).card + (s.filter (fun x => ¬ p x)).card = s.card := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h3 : ∀ x ∈ s, (if p x then 1 else 0) + (if ¬ p x then 1 else 0) = 1 := by
    intro x _; by_cases hx : p x <;> simp [hx]
  rw [Finset.sum_congr rfl h3]; simp

private lemma card_perm_moving_eq {N k : ℕ} (S : Finset (Fin N)) (hS : S.card = k) :
    Fintype.card {σ : Equiv.Perm (Fin N) // Finset.univ.filter (fun x => σ x ≠ x) = S} =
      derangementCount k := by
  classical
  let iso : Fin k ≃o S := S.orderIsoOfFin hS
  unfold derangementCount
  refine Fintype.card_congr ?_
  refine
    { toFun := fun ⟨σ, hσ⟩ =>
        ⟨{ toFun := fun i => iso.symm ⟨σ (iso i).val, by
            have hmem : (iso i).val ∈ Finset.univ.filter (fun x => σ x ≠ x) :=
              (Finset.ext_iff.mp hσ (iso i).val).mpr (iso i).prop
            have hne : σ (iso i).val ≠ (iso i).val := (Finset.mem_filter.mp hmem).2
            exact (Finset.ext_iff.mp hσ (σ (iso i).val)).mp
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne (σ.injective h)⟩)⟩
           invFun := fun i => iso.symm ⟨σ.symm (iso i).val, by
            have hmem : (iso i).val ∈ Finset.univ.filter (fun x => σ x ≠ x) :=
              (Finset.ext_iff.mp hσ (iso i).val).mpr (iso i).prop
            have hne : σ (iso i).val ≠ (iso i).val := (Finset.mem_filter.mp hmem).2
            exact (Finset.ext_iff.mp hσ (σ.symm (iso i).val)).mp
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne (by
                have := congrArg σ h; simpa using this)⟩)⟩
           left_inv := fun i => by simp
           right_inv := fun i => by simp }, fun i hi => by
          have hmem : (iso i).val ∈ Finset.univ.filter (fun x => σ x ≠ x) :=
            (Finset.ext_iff.mp hσ (iso i).val).mpr (iso i).prop
          have hne : σ (iso i).val ≠ (iso i).val := (Finset.mem_filter.mp hmem).2
          have h1 := congrArg (fun j => (iso j).val) hi
          simp only [Equiv.coe_fn_mk, OrderIso.apply_symm_apply] at h1
          exact hne h1⟩
      invFun := fun ⟨τ, hτ⟩ =>
        ⟨{ toFun := fun x => if hx : x ∈ S then (iso (τ (iso.symm ⟨x, hx⟩))).val else x
           invFun := fun x => if hx : x ∈ S then (iso (τ.symm (iso.symm ⟨x, hx⟩))).val else x
           left_inv := fun x => by
            by_cases hx : x ∈ S
            · simp only [hx, ↓reduceDIte]
              have hmem : (iso (τ (iso.symm ⟨x, hx⟩))).val ∈ S := (iso _).prop
              simp [hmem]
            · simp [hx]
           right_inv := fun x => by
            by_cases hx : x ∈ S
            · simp only [hx, ↓reduceDIte]
              have hmem : (iso (τ.symm (iso.symm ⟨x, hx⟩))).val ∈ S := (iso _).prop
              simp [hmem]
            · simp [hx] }, by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_fn_mk]
          by_cases hx : x ∈ S
          · simp only [hx, ↓reduceDIte, iff_true]
            intro heq
            have : τ (iso.symm ⟨x, hx⟩) = iso.symm ⟨x, hx⟩ := by
              apply iso.injective
              apply Subtype.ext
              simpa using heq
            exact hτ _ this
          · simp [hx]⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        ext x
        simp only [Equiv.coe_fn_mk]
        by_cases hx : x ∈ S
        · simp [hx]
        · simp only [hx, ↓reduceDIte]
          by_contra hne
          have hne' : σ x ≠ x := fun h => hne (congrArg Fin.val h.symm)
          apply hx; rw [← hσ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hne'⟩
      right_inv := fun ⟨τ, hτ⟩ => by
        ext i
        simp }

private lemma card_foataFP_card (N k : ℕ) (hk : k ≤ N) :
    Fintype.card {σ : Equiv.Perm (Fin N) // (foataFPSet σ).card = N - k} =
      Nat.choose N k * derangementCount k := by
  classical
  have h1 : Fintype.card {σ : Equiv.Perm (Fin N) // (foataFPSet σ).card = N - k} =
      Fintype.card {σ : Equiv.Perm (Fin N) // (Finset.univ.filter fun x => σ x ≠ x).card = k} := by
    refine Fintype.card_congr ?_
    refine Equiv.subtypeEquiv (foataEquiv N) fun σ => ?_
    have hcomp : (Finset.univ.filter fun x : Fin N => foataInv σ x = x).card +
        (Finset.univ.filter fun x : Fin N => foataInv σ x ≠ x).card = N := by
      have := card_filter_add_not (Finset.univ : Finset (Fin N)) (fun x => foataInv σ x = x)
      simpa using this
    simp only [foataFPSet, foataEquiv, Equiv.ofBijective_apply, foataInvPerm_apply]
    omega
  rw [h1]
  have hsig : {σ : Equiv.Perm (Fin N) // (Finset.univ.filter fun x => σ x ≠ x).card = k} ≃
      Σ S : {S : Finset (Fin N) // S.card = k},
        {σ : Equiv.Perm (Fin N) // Finset.univ.filter (fun x => σ x ≠ x) = S.val} :=
    { toFun := fun ⟨σ, hσ⟩ => ⟨⟨Finset.univ.filter (fun x => σ x ≠ x), hσ⟩, ⟨σ, rfl⟩⟩
      invFun := fun ⟨⟨S, hS⟩, ⟨σ, hσ⟩⟩ => ⟨σ, hσ.symm ▸ hS⟩
      left_inv := fun ⟨_, _⟩ => rfl
      right_inv := fun ⟨⟨S, hS⟩, ⟨σ, hσ⟩⟩ => by
        dsimp only at hσ ⊢
        refine Sigma.ext (Subtype.ext hσ) ?_
        have haux : ∀ {S₁ S₂ : {S : Finset (Fin N) // S.card = k}} (h : S₁ = S₂)
            (a : {σ : Equiv.Perm (Fin N) // Finset.univ.filter (fun x => σ x ≠ x) = S₁.val})
            (b : {σ : Equiv.Perm (Fin N) // Finset.univ.filter (fun x => σ x ≠ x) = S₂.val}),
            a.val = b.val → HEq a b := by
          rintro _ _ rfl ⟨a, _⟩ ⟨b, _⟩ hab; subst hab; rfl
        exact haux (Subtype.ext hσ) _ _ rfl }
  rw [Fintype.card_congr hsig, Fintype.card_sigma]
  have hsum : ∀ S : {S : Finset (Fin N) // S.card = k},
      Fintype.card {σ : Equiv.Perm (Fin N) // Finset.univ.filter (fun x => σ x ≠ x) = S.val} =
        derangementCount k := fun S => card_perm_moving_eq S.val S.prop
  simp only [hsum, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  congr 1
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun S : Finset (Fin N) => S.card = k) =
      Finset.powersetCard k (Finset.univ : Finset (Fin N)) := by
    ext S; simp [Finset.mem_powersetCard]
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

private lemma hockey_stick (r s : ℕ) :
    ∑ t ∈ Finset.range (s + 1), Nat.choose (t + r) r = Nat.choose (s + r + 1) (r + 1) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : s + 1 + r + 1 = (s + r + 1) + 1 := by omega
    have h2 : s + 1 + r = s + r + 1 := by omega
    rw [h1, h2]
    rw [Nat.choose_succ_succ (s + r + 1) r, add_comm]

private lemma finite_compositions (r s : ℕ) :
    Finite {g : Fin (r + 1) → ℕ // ∑ i, g i = s} := by
  refine Finite.of_injective (f := fun x (i : Fin (r + 1)) =>
    (⟨x.val i, by
      have hle : x.val i ≤ ∑ j, x.val j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      have := x.prop; omega⟩ : Fin (s + 1))) ?_
  intro ⟨g1, _⟩ ⟨g2, _⟩ h
  apply Subtype.ext
  ext i
  exact congrArg Fin.val (congrFun h i)

private lemma card_compositions (r s : ℕ) :
    Nat.card {g : Fin (r + 1) → ℕ // ∑ i, g i = s} = Nat.choose (s + r) r := by
  induction r generalizing s with
  | zero =>
    have hne : Nonempty {g : Fin 1 → ℕ // ∑ i, g i = s} := ⟨⟨fun _ => s, by simp⟩⟩
    have hsub : Subsingleton {g : Fin 1 → ℕ // ∑ i, g i = s} :=
      ⟨fun ⟨g1, hg1⟩ ⟨g2, hg2⟩ => by
        ext i; fin_cases i
        change g1 0 = g2 0
        have h1 : g1 0 = s := by simpa using hg1
        have h2 : g2 0 = s := by simpa using hg2
        exact h1.trans h2.symm⟩
    rw [Nat.card_unique]; simp
  | succ r ih =>
    have : ∀ t : Fin (s + 1), Finite {g' : Fin (r + 1) → ℕ // ∑ i, g' i = s - t.val} :=
      fun t => finite_compositions r (s - t.val)
    let e : {g : Fin (r + 2) → ℕ // ∑ i, g i = s} ≃
        Σ t : Fin (s + 1), {g' : Fin (r + 1) → ℕ // ∑ i, g' i = s - t.val} :=
      { toFun := fun ⟨g, hg⟩ =>
          ⟨⟨g 0, by
            have h0 : g 0 ≤ ∑ i, g i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
            omega⟩,
           ⟨fun i => g i.succ, by
            dsimp only
            rw [Fin.sum_univ_succ] at hg; omega⟩⟩
        invFun := fun ⟨t, ⟨g', hg'⟩⟩ =>
          ⟨Fin.cons t.val g', by
            rw [Fin.sum_univ_succ, Fin.cons_zero]
            simp only [Fin.cons_succ]
            have ht := t.isLt; omega⟩
        left_inv := fun ⟨g, _⟩ => by
          ext i; refine Fin.cases ?_ ?_ i <;> simp
        right_inv := fun ⟨t, ⟨g', _⟩⟩ => by
          ext <;> simp }
    rw [Nat.card_congr e, Nat.card_sigma]
    have hfin : ∀ t : Fin (s + 1),
        Nat.card {g' : Fin (r + 1) → ℕ // ∑ i, g' i = s - t.val} = Nat.choose (s - t.val + r) r :=
      fun t => ih (s - t.val)
    simp only [hfin]
    rw [Fin.sum_univ_eq_sum_range (fun t => Nat.choose (s - t + r) r)]
    have hrev : ∑ t ∈ Finset.range (s + 1), Nat.choose (s - t + r) r =
        ∑ t ∈ Finset.range (s + 1), Nat.choose (t + r) r := by
      rw [← Finset.sum_range_reflect (fun t => Nat.choose (t + r) r) (s + 1)]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [Finset.mem_range] at ht
      have : s + 1 - 1 - t = s - t := by omega
      rw [this]
    rw [hrev, hockey_stick r s]
    have : s + r + 1 = s + (r + 1) := by omega
    rw [this]

private lemma card_compositions_ge1 (r s : ℕ) (F : Finset (Fin r)) :
    Nat.card {g : Fin (r + 1) → ℕ // (∑ i, g i = s) ∧ ∀ j ∈ F, 1 ≤ g j.succ} =
      if s < F.card then 0 else Nat.choose (s - F.card + r) r := by
  classical
  by_cases hlt : s < F.card
  · rw [if_pos hlt]
    have hempty : IsEmpty {g : Fin (r + 1) → ℕ // (∑ i, g i = s) ∧ ∀ j ∈ F, 1 ≤ g j.succ} := by
      constructor
      rintro ⟨g, hg, hge⟩
      have h1 : F.card ≤ ∑ j ∈ F, g j.succ := by
        calc F.card = ∑ _j ∈ F, 1 := by simp
          _ ≤ ∑ j ∈ F, g j.succ := Finset.sum_le_sum hge
      have h2 : ∑ j ∈ F, g j.succ ≤ ∑ i : Fin (r + 1), g i := by
        have hsub : F.image Fin.succ ⊆ Finset.univ := Finset.subset_univ _
        rw [← Finset.sum_image (f := g) (fun a _ b _ h => Fin.succ_injective _ h)]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      omega
    let hfin : Fintype {g : Fin (r + 1) → ℕ // (∑ i, g i = s) ∧ ∀ j ∈ F, 1 ≤ g j.succ} :=
      @Fintype.ofIsEmpty _ hempty
    rw [@Nat.card_eq_fintype_card _ hfin]; exact @Fintype.card_eq_zero _ hfin hempty
  · rw [if_neg hlt]
    let e : {g : Fin (r + 1) → ℕ // (∑ i, g i = s) ∧ ∀ j ∈ F, 1 ≤ g j.succ} ≃
        {g' : Fin (r + 1) → ℕ // ∑ i, g' i = s - F.card} :=
      { toFun := fun ⟨g, hg, hge⟩ =>
          ⟨fun i => if i ∈ F.image Fin.succ then g i - 1 else g i, by
            have hadd : (∑ i : Fin (r + 1), (if i ∈ F.image Fin.succ then g i - 1 else g i)) + F.card =
                ∑ i : Fin (r + 1), g i := by
              have hcard : F.card = ∑ i : Fin (r + 1), if i ∈ F.image Fin.succ then 1 else 0 := by
                rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
                    Finset.card_image_of_injective _ (Fin.succ_injective _)]
                simp
              rw [hcard, ← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun i _ => ?_
              by_cases hi : i ∈ F.image Fin.succ
              · simp only [hi, ↓reduceIte]
                obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp hi
                have := hge j hjF; omega
              · simp [hi]
            dsimp only at hadd ⊢; omega⟩
        invFun := fun ⟨g', hg'⟩ =>
          ⟨fun i => if i ∈ F.image Fin.succ then g' i + 1 else g' i, by
            constructor
            · have hcard : F.card = ∑ i : Fin (r + 1), if i ∈ F.image Fin.succ then 1 else 0 := by
                rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter,
                    Finset.card_image_of_injective _ (Fin.succ_injective _)]
                simp
              have hsum : ∑ i : Fin (r + 1), (if i ∈ F.image Fin.succ then g' i + 1 else g' i) =
                  (∑ i, g' i) + ∑ i : Fin (r + 1), if i ∈ F.image Fin.succ then 1 else 0 := by
                rw [← Finset.sum_add_distrib]
                refine Finset.sum_congr rfl fun i _ => by split_ifs <;> omega
              rw [hsum, hg', ← hcard]; omega
            · intro j hj
              have hmem : j.succ ∈ F.image Fin.succ := Finset.mem_image_of_mem _ hj
              simp [hmem]⟩
        left_inv := fun ⟨g, _, hge⟩ => by
          ext i
          by_cases hi : i ∈ F.image Fin.succ
          · simp only [hi, ↓reduceIte]
            obtain ⟨j, hjF, rfl⟩ := Finset.mem_image.mp hi
            have := hge j hjF; omega
          · simp [hi]
        right_inv := fun ⟨g', _⟩ => by
          ext i; by_cases hi : i ∈ F.image Fin.succ <;> simp [hi] }
    rw [Nat.card_congr e, card_compositions]

/-! ### Part 3: Main bijection for `(12; 3 → 3)` and `(21; 3 → 3)` -/

private def AvoidsArrow (asc : Bool) {n : ℕ} (π : Equiv.Perm (Fin n)) : Prop :=
  ∀ x₁ x₂ x₃ : Fin n, x₁ < x₂ → x₂ < x₃ →
    (if asc then π.symm x₂ < π.symm x₁ else π.symm x₁ < π.symm x₂) →
    foataInv π x₃ ≠ x₃

private lemma avoids_false_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    AvoidsArrow false π ↔ ¬ ContainsArrow12_33 π := by
  unfold AvoidsArrow ContainsArrow12_33
  simp only [Bool.false_eq_true, ↓reduceIte, not_exists, not_and]

private lemma avoids_true_iff {n : ℕ} (π : Equiv.Perm (Fin n)) :
    AvoidsArrow true π ↔ ¬ ContainsArrow21_33 π := by
  unfold AvoidsArrow ContainsArrow21_33
  simp only [↓reduceIte, not_exists, not_and]

-- Auxiliary: for a monotone ordering `asc` on `Fin (m - 1)` and given gap counts `g : Fin (r + 1) → ℕ`
-- summing to `m - 1` (`r = n - m`), build the permutation `π` from `(σ, g)` and prove bijectivity!
private def gapPrefix {r : ℕ} (g : Fin (r + 1) → ℕ) (j : ℕ) : ℕ :=
  ∑ t ∈ (Finset.univ : Finset (Fin (r + 1))).filter (fun t => t.val < j), g t

private lemma gapPrefix_zero {r : ℕ} (g : Fin (r + 1) → ℕ) : gapPrefix g 0 = 0 := by
  simp [gapPrefix]

private lemma gapPrefix_succ {r : ℕ} (g : Fin (r + 1) → ℕ) (j : ℕ) (hj : j < r + 1) :
    gapPrefix g (j + 1) = gapPrefix g j + g ⟨j, hj⟩ := by
  unfold gapPrefix
  have hdisj : (Finset.univ.filter fun t : Fin (r + 1) => t.val < j + 1) =
      insert ⟨j, hj⟩ (Finset.univ.filter fun t : Fin (r + 1) => t.val < j) := by
    ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [hdisj, Finset.sum_insert (by simp), add_comm]

private lemma gapPrefix_top {r : ℕ} (g : Fin (r + 1) → ℕ) :
    gapPrefix g (r + 1) = ∑ t : Fin (r + 1), g t := by
  unfold gapPrefix
  congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; exact t.isLt

private lemma gapPrefix_mono {r : ℕ} (g : Fin (r + 1) → ℕ) {a b : ℕ} (hab : a ≤ b) :
    gapPrefix g a ≤ gapPrefix g b :=
  Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢; omega) (fun _ _ _ => Nat.zero_le _)

-- Position of `m_idx` is `g 0`; position of `σ j` (`j : Fin (n - m)`) is `j.val + 1 + gapPrefix g (j.val + 1)`
private def hiPos {n m : ℕ} (g : Fin (n - m + 1) → ℕ) (j : Fin (n - m)) : ℕ :=
  j.val + 1 + gapPrefix g (j.val + 1)

private lemma hiPos_strictMono {n m : ℕ} (g : Fin (n - m + 1) → ℕ) :
    StrictMono (hiPos g) := by
  intro a b hab
  unfold hiPos
  have hle : gapPrefix g (a.val + 1) ≤ gapPrefix g (b.val + 1) := gapPrefix_mono g (by omega)
  have := Fin.lt_def.mp hab
  omega

private lemma hiPos_gt_g0 {n m : ℕ} (g : Fin (n - m + 1) → ℕ) (j : Fin (n - m)) :
    g 0 < hiPos g j := by
  unfold hiPos
  have h1 : g 0 = gapPrefix g 1 := by
    rw [gapPrefix_succ g 0 (by omega), gapPrefix_zero, zero_add]; rfl
  have h2 : gapPrefix g 1 ≤ gapPrefix g (j.val + 1) := gapPrefix_mono g (by omega)
  omega

private lemma hiPos_lt_n {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1) (j : Fin (n - m)) :
    hiPos g j < n := by
  unfold hiPos
  have hle : gapPrefix g (j.val + 1) ≤ m - 1 := by
    rw [← hg, ← gapPrefix_top]; exact gapPrefix_mono g (by omega)
  have hj := j.isLt
  omega

-- Given `π` with max fixed point `m_idx` and `AvoidsArrow asc π`:
-- extract `σ : Equiv.Perm (Fin (n - m))` and `g : Fin (n - m + 1) → ℕ`!
private lemma maxFP_left_lt {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (π : Equiv.Perm (Fin n)) (hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩)
    (q : Fin n) (hq : q < π.symm ⟨m - 1, by omega⟩) : (π q).val < m - 1 := by
  have hlm := ((foataInv_fixed_iff π ⟨m - 1, by omega⟩).mp hfix).1
  have hlt := hlm q hq
  rw [Equiv.apply_symm_apply] at hlt
  exact Fin.lt_def.mp hlt

private lemma maxFP_pos_hi_gt {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n)
    (π : Equiv.Perm (Fin n)) (hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩)
    (q : Fin n) (hval : m ≤ (π q).val) : π.symm ⟨m - 1, by omega⟩ < q := by
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · rw [heq, Equiv.apply_symm_apply] at hval; dsimp only at hval; omega
  · have := maxFP_left_lt hm hmn π hfix q hlt; omega

private lemma maxFP_card_hi {n m : ℕ} (π : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun q : Fin n => m ≤ (π q).val).card = n - m := by
  have hbij : (Finset.univ.filter fun q : Fin n => m ≤ (π q).val) =
      (Finset.univ.filter fun v : Fin n => m ≤ v.val).map π.symm.toEmbedding := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    exact ⟨fun h => ⟨π q, h, by simp⟩, fun ⟨v, hv, hq⟩ => by rw [← hq, Equiv.apply_symm_apply]; exact hv⟩
  rw [hbij, Finset.card_map]
  have hval : (Finset.univ.filter fun v : Fin n => m ≤ v.val).card =
      ((Finset.range n).filter fun v => m ≤ v).card := by
    refine Finset.card_bij (fun v _ => v.val) (fun v hv => ?_) (fun _ _ _ _ h => Fin.ext h) (fun x hx => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hv ⊢
      exact ⟨v.isLt, hv⟩
    · simp only [Finset.mem_filter, Finset.mem_range] at hx
      exact ⟨⟨x, hx.1⟩, by simp [hx.2], rfl⟩
  rw [hval]
  have hfilt : (Finset.range n).filter (fun v => m ≤ v) = Finset.Ico m n := by
    ext x; simp [Finset.mem_Ico]; omega
  rw [hfilt, Nat.card_Ico]

private lemma fin_strictMono_id {k : ℕ} {f : Fin k → Fin k} (hf : StrictMono f) (j : Fin k) : f j = j := by
  cases k with
  | zero => exact Fin.elim0 j
  | succ k' =>
    have hge : ∀ i : Fin (k' + 1), i ≤ f i := by
      intro i
      induction i using Fin.induction with
      | zero => exact Fin.zero_le _
      | succ i ih =>
        have hlt := hf (show i.castSucc < i.succ from Fin.lt_def.mpr (by simp))
        have h1 := Fin.le_def.mp ih; have h2 := Fin.lt_def.mp hlt
        simp only [Fin.val_castSucc] at h1 h2
        exact Fin.le_def.mpr (by simp; omega)
    have hle : ∀ i : Fin (k' + 1), f i ≤ i := by
      intro i
      suffices ∀ d (i : Fin (k' + 1)), k' - i.val = d → f i ≤ i from this (k' - i.val) i rfl
      intro d
      induction d with
      | zero =>
        intro i hi
        have := (f i).isLt; exact Fin.le_def.mpr (by omega)
      | succ d ih =>
        intro i hi
        have hi1 : i.val + 1 < k' + 1 := by omega
        have hlt := hf (show i < ⟨i.val + 1, hi1⟩ from Fin.lt_def.mpr (by simp))
        have hnext := ih ⟨i.val + 1, hi1⟩ (by dsimp only; omega)
        have := Fin.lt_def.mp hlt; have := Fin.le_def.mp hnext; dsimp only at this
        exact Fin.le_def.mpr (by omega)
    exact le_antisymm (hle j) (hge j)

private def hiSet {n : ℕ} (m : ℕ) (π : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun q => m ≤ (π q).val

private noncomputable def hiIso {n : ℕ} (m : ℕ) (π : Equiv.Perm (Fin n)) :
    Fin (n - m) ≃o hiSet m π :=
  (hiSet m π).orderIsoOfFin (maxFP_card_hi π)

private noncomputable def extSigma {n : ℕ} (m : ℕ) (π : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n - m)) :=
  Equiv.ofBijective
    (fun j => ⟨(π (hiIso m π j).val).val - m, by
      have hlt := (π (hiIso m π j).val).isLt
      have hge : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
      omega⟩)
    (Finite.injective_iff_bijective.mp fun j1 j2 heq => by
      have h1 : m ≤ (π (hiIso m π j1).val).val := (Finset.mem_filter.mp (hiIso m π j1).prop).2
      have h2 : m ≤ (π (hiIso m π j2).val).val := (Finset.mem_filter.mp (hiIso m π j2).prop).2
      have hval : (π (hiIso m π j1).val).val = (π (hiIso m π j2).val).val := by
        have := congrArg Fin.val heq; dsimp only at this; omega
      exact (hiIso m π).injective (Subtype.ext (π.injective (Fin.ext hval))))

private noncomputable def extG {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (π : Equiv.Perm (Fin n)) : Fin (n - m + 1) → ℕ := fun i =>
  if h0 : i.val = 0 then (π.symm ⟨m - 1, by omega⟩).val
  else
    let j : Fin (n - m) := ⟨i.val - 1, by omega⟩
    let nextPos : ℕ :=
      if hnext : j.val + 1 < n - m then (hiIso m π ⟨j.val + 1, hnext⟩).val.val else n
    nextPos - (hiIso m π j).val.val - 1

private def isSmallPos (n m : ℕ) (g : Fin (n - m + 1) → ℕ) (p : ℕ) : Bool :=
  !(p == g 0) && (List.finRange (n - m)).all (fun j => !(p == hiPos g j))

private def smallRank (n m : ℕ) (g : Fin (n - m + 1) → ℕ) (p : ℕ) : ℕ :=
  ((List.range p).filter (isSmallPos n m g)).length

private lemma smallRank_lt {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1) (p : Fin n)
    (hp0 : p.val ≠ g 0) (hphi : ¬ ∃ j : Fin (n - m), p.val = hiPos g j) :
    smallRank n m g p.val < m - 1 := by
  have hp_sm : isSmallPos n m g p.val = true := by
    simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      List.all_eq_true, List.mem_finRange, true_implies]
    exact ⟨hp0, fun j h => hphi ⟨j, h⟩⟩
  have htot : ((List.range n).filter (isSmallPos n m g)).length = m - 1 := by
    have hset : ((Finset.range n).filter (fun x => isSmallPos n m g x = true)).card = m - 1 := by
      have hcomp : (Finset.range n).filter (fun x => isSmallPos n m g x = false) =
          insert (g 0) (Finset.univ.image (hiPos g)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_image,
          Finset.mem_univ, true_and, isSmallPos, Bool.and_eq_false_iff, Bool.not_eq_false',
          beq_iff_eq, List.all_eq_false, List.mem_finRange, Bool.not_eq_true', Bool.not_eq_false]
        constructor
        · rintro ⟨_, rfl | ⟨j, hj⟩⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨j, hj.symm⟩
        · rintro (rfl | ⟨j, rfl⟩)
          · refine ⟨?_, Or.inl rfl⟩
            have h0 : g 0 ≤ ∑ i, g i :=
              Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
            omega
          · exact ⟨hiPos_lt_n hm1 hmn g hg j, Or.inr ⟨j, rfl⟩⟩
      have hnotmem : g 0 ∉ Finset.univ.image (hiPos g) := by
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        rintro ⟨j, hj⟩
        exact ne_of_lt (hiPos_gt_g0 g j) hj.symm
      have hcard_f : ((Finset.range n).filter (fun x => isSmallPos n m g x = false)).card =
          1 + (n - m) := by
        rw [hcomp, Finset.card_insert_of_notMem hnotmem,
            Finset.card_image_of_injective _ (hiPos_strictMono g).injective,
            Finset.card_univ, Fintype.card_fin]
        omega
      have hadd := card_filter_add_not (Finset.range n) (fun x => isSmallPos n m g x = true)
      have hneg : ((Finset.range n).filter fun x => ¬ isSmallPos n m g x = true) =
          (Finset.range n).filter (fun x => isSmallPos n m g x = false) := by
        ext x; simp
      rw [hneg, hcard_f, Finset.card_range] at hadd
      omega
    rw [← hset, ← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)]
    congr 1; ext x; simp
  have h1 : (List.filter (isSmallPos n m g) (List.range p.val)).toFinset ⊂
      (List.filter (isSmallPos n m g) (List.range n)).toFinset := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx => by
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hx ⊢
      exact ⟨lt_trans hx.1 p.isLt, hx.2⟩, fun heq => ?_⟩
    have hmem : p.val ∈ (List.filter (isSmallPos n m g) (List.range n)).toFinset := by
      simp [p.isLt, hp_sm]
    rw [← heq] at hmem; simp at hmem
  have hc := Finset.card_lt_card h1
  rw [List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range),
      List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range), htot] at hc
  exact hc

private lemma smallRank_strict {n m : ℕ} (g : Fin (n - m + 1) → ℕ) {a b : Fin n}
    (hab : a < b) (ha : isSmallPos n m g a.val = true) :
    smallRank n m g a.val < smallRank n m g b.val := by
  have h1 : (List.filter (isSmallPos n m g) (List.range a.val)).toFinset ⊂
      (List.filter (isSmallPos n m g) (List.range b.val)).toFinset := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun x hx => by
      simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hx ⊢
      exact ⟨lt_trans hx.1 (Fin.lt_def.mp hab), hx.2⟩, fun heq => ?_⟩
    have hmem : a.val ∈ (List.filter (isSmallPos n m g) (List.range b.val)).toFinset := by
      simp [Fin.lt_def.mp hab, ha]
    rw [← heq] at hmem; simp at hmem
  have hc := Finset.card_lt_card h1
  rwa [List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range),
       List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)] at hc

private noncomputable def buildFun {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ)
    (hg : ∑ i, g i = m - 1) (p : Fin n) : Fin n :=
  if h0 : p.val = g 0 then ⟨m - 1, by omega⟩
  else if hhi : ∃ j : Fin (n - m), p.val = hiPos g j then
    ⟨m + (σ (Classical.choose hhi)).val, by have := (σ (Classical.choose hhi)).isLt; omega⟩
  else
    let r := smallRank n m g p.val
    if asc then ⟨r, by have := smallRank_lt hm1 hmn g hg p h0 hhi; omega⟩
    else ⟨m - 2 - r, by omega⟩

private lemma buildFun_inj {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1) :
    Function.Injective (buildFun hm1 hmn asc σ g hg) := by
  intro p1 p2 heq
  dsimp only [buildFun] at heq
  have hval := congrArg Fin.val heq
  by_cases h1 : p1.val = g 0 <;> by_cases h2 : p2.val = g 0
  · exact Fin.ext (h1.trans h2.symm)
  · rw [dif_pos h1, dif_neg h2] at hval
    by_cases hhi2 : ∃ j : Fin (n - m), p2.val = hiPos g j
    · rw [dif_pos hhi2] at hval; dsimp only at hval; omega
    · rw [dif_neg hhi2] at hval
      have := smallRank_lt hm1 hmn g hg p2 h2 hhi2
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hval <;> omega
  · rw [dif_neg h1, dif_pos h2] at hval
    by_cases hhi1 : ∃ j : Fin (n - m), p1.val = hiPos g j
    · rw [dif_pos hhi1] at hval; dsimp only at hval; omega
    · rw [dif_neg hhi1] at hval
      have := smallRank_lt hm1 hmn g hg p1 h1 hhi1
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hval <;> omega
  · rw [dif_neg h1, dif_neg h2] at hval
    by_cases hhi1 : ∃ j : Fin (n - m), p1.val = hiPos g j <;>
      by_cases hhi2 : ∃ j : Fin (n - m), p2.val = hiPos g j
    · rw [dif_pos hhi1, dif_pos hhi2] at hval
      dsimp only at hval
      have hσeq : σ (Classical.choose hhi1) = σ (Classical.choose hhi2) := Fin.ext (by omega)
      have hjeq := σ.injective hσeq
      exact Fin.ext ((Classical.choose_spec hhi1).trans (by rw [hjeq]; exact (Classical.choose_spec hhi2).symm))
    · rw [dif_pos hhi1, dif_neg hhi2] at hval
      have := smallRank_lt hm1 hmn g hg p2 h2 hhi2
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hval <;> omega
    · rw [dif_neg hhi1, dif_pos hhi2] at hval
      have := smallRank_lt hm1 hmn g hg p1 h1 hhi1
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hval <;> omega
    · rw [dif_neg hhi1, dif_neg hhi2] at hval
      have hlt1 := smallRank_lt hm1 hmn g hg p1 h1 hhi1
      have hlt2 := smallRank_lt hm1 hmn g hg p2 h2 hhi2
      have hsm1 : isSmallPos n m g p1.val = true := by
        simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
          List.all_eq_true, List.mem_finRange, true_implies]
        exact ⟨h1, fun j h => hhi1 ⟨j, h⟩⟩
      have hsm2 : isSmallPos n m g p2.val = true := by
        simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
          List.all_eq_true, List.mem_finRange, true_implies]
        exact ⟨h2, fun j h => hhi2 ⟨j, h⟩⟩
      have hr_eq : smallRank n m g p1.val = smallRank n m g p2.val := by
        cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hval <;> omega
      rcases lt_trichotomy p1 p2 with hlt | rfl | hgt
      · exact absurd hr_eq (ne_of_lt (smallRank_strict g hlt hsm1))
      · rfl
      · exact absurd hr_eq.symm (ne_of_lt (smallRank_strict g hgt hsm2))

private noncomputable def buildPerm {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ)
    (hg : ∑ i, g i = m - 1) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (buildFun hm1 hmn asc σ g hg)
    (Finite.injective_iff_bijective.mp (buildFun_inj hm1 hmn asc σ g hg))

private lemma buildPerm_g0 {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1) :
    buildPerm hm1 hmn asc σ g hg ⟨g 0, by
      have h0 : g 0 ≤ ∑ i, g i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      omega⟩ = ⟨m - 1, by omega⟩ := by
  simp [buildPerm, buildFun]

private lemma buildPerm_hi {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1)
    (j : Fin (n - m)) :
    buildPerm hm1 hmn asc σ g hg ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ =
      ⟨m + (σ j).val, by have := (σ j).isLt; omega⟩ := by
  have hne : hiPos g j ≠ g 0 := ne_of_gt (hiPos_gt_g0 g j)
  have hex : ∃ j' : Fin (n - m), hiPos g j = hiPos g j' := ⟨j, rfl⟩
  simp only [buildPerm, Equiv.ofBijective_apply, buildFun, hne, ↓reduceDIte, hex]
  have hcj : Classical.choose hex = j := (hiPos_strictMono g).injective (Classical.choose_spec hex).symm
  exact Fin.ext (by dsimp only; rw [hcj])

private lemma buildPerm_small {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1)
    (p : Fin n) (hp0 : p.val ≠ g 0) (hphi : ∀ j : Fin (n - m), p.val ≠ hiPos g j) :
    (buildPerm hm1 hmn asc σ g hg p).val < m - 1 := by
  have hnot : ¬ ∃ j : Fin (n - m), p.val = hiPos g j := fun ⟨j, hj⟩ => hphi j hj
  have hsm_lt : smallRank n m g p.val < m - 1 := smallRank_lt hm1 hmn g hg p hp0 hnot
  simp only [buildPerm, Equiv.ofBijective_apply, buildFun, hp0, ↓reduceDIte, hnot]
  cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

private lemma isLMax_hi_iff {n m : ℕ} (π : Equiv.Perm (Fin n)) (j : Fin (n - m)) :
    IsLMax π (hiIso m π j).val ↔ IsLMax (extSigma m π) j := by
  constructor
  · intro hlm j' hj'
    have hlt : (hiIso m π j').val < (hiIso m π j).val := (hiIso m π).strictMono hj'
    have hval := hlm (hiIso m π j').val hlt
    have h1 : m ≤ (π (hiIso m π j').val).val := (Finset.mem_filter.mp (hiIso m π j').prop).2
    have h2 : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
    simp only [extSigma, Equiv.ofBijective_apply, Fin.lt_def]
    have := Fin.lt_def.mp hval; omega
  · intro hlm q hq
    by_cases hqm : m ≤ (π q).val
    · have hqmem : q ∈ hiSet m π := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqm⟩
      let j' : Fin (n - m) := (hiIso m π).symm ⟨q, hqmem⟩
      have hj'eq : (hiIso m π j').val = q :=
        congrArg Subtype.val ((hiIso m π).apply_symm_apply ⟨q, hqmem⟩)
      have hj'lt : j' < j := by
        rw [← (hiIso m π).lt_iff_lt]; exact Subtype.mk_lt_mk.mpr (hj'eq.symm ▸ hq)
      have hlt := hlm j' hj'lt
      simp only [extSigma, Equiv.ofBijective_apply, Fin.lt_def, hj'eq] at hlt
      have h2 : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
      exact Fin.lt_def.mpr (by omega)
    · have h2 : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
      exact Fin.lt_def.mpr (by omega)

private lemma hiPos_extG {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (π : Equiv.Perm (Fin n)) (hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩)
    (j : Fin (n - m)) :
    hiPos (extG hm1 hmn π) j = (hiIso m π j).val.val := by
  have hpm_lt : ∀ j' : Fin (n - m), (π.symm ⟨m - 1, by omega⟩).val < (hiIso m π j').val.val :=
    fun j' => Fin.lt_def.mp
      (maxFP_pos_hi_gt hm1 hmn π hfix (hiIso m π j').val (Finset.mem_filter.mp (hiIso m π j').prop).2)
  have hfirst : ∀ h0 : 0 < n - m, (hiIso m π ⟨0, h0⟩).val.val = (π.symm ⟨m - 1, by omega⟩).val + 1 := by
    intro h0
    have hpm1 : (π.symm ⟨m - 1, by omega⟩).val + 1 < n := by
      have := hpm_lt ⟨0, h0⟩; have := (hiIso m π ⟨0, h0⟩).val.isLt; omega
    have hgt : (⟨m - 1, by omega⟩ : Fin n) < π ⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hpm1⟩ := by
      have := ((foataInv_fixed_iff π ⟨m - 1, by omega⟩).mp hfix).2 hpm1
      rwa [Equiv.apply_symm_apply] at this
    have hmem : (⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hpm1⟩ : Fin n) ∈ hiSet m π := by
      simp only [hiSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hgt' : m - 1 < (π ⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hpm1⟩).val := Fin.lt_def.mp hgt
      omega
    have hle : (hiIso m π ⟨0, h0⟩).val ≤ ⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hpm1⟩ := by
      let j0 := (hiIso m π).symm ⟨⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hpm1⟩, hmem⟩
      have h0le : (⟨0, h0⟩ : Fin (n - m)) ≤ j0 := Fin.le_def.mpr (Nat.zero_le _)
      have hmono := (hiIso m π).monotone h0le
      have hsub : hiIso m π ⟨0, h0⟩ ≤ ⟨⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hpm1⟩, hmem⟩ := by
        simpa [j0] using hmono
      exact Subtype.coe_le_coe.mpr hsub
    have hgt0 := hpm_lt ⟨0, h0⟩
    have hle' := Fin.le_def.mp hle; dsimp only at hle'; omega
  suffices ∀ k (hk : k < n - m), hiPos (extG hm1 hmn π) ⟨k, hk⟩ = (hiIso m π ⟨k, hk⟩).val.val from
    this j.val j.isLt
  intro k
  induction k with
  | zero =>
    intro hk
    unfold hiPos; dsimp only
    rw [gapPrefix_succ _ 0 (by omega), gapPrefix_zero, zero_add]
    dsimp only [extG]; rw [dif_pos rfl]
    have := hfirst hk; omega
  | succ k ih =>
    intro hk
    have ih' := ih (by omega)
    unfold hiPos at ih' ⊢
    dsimp only at ih' ⊢
    rw [gapPrefix_succ _ (k + 1) (by omega)]
    have he : extG hm1 hmn π ⟨k + 1, by omega⟩ =
        (hiIso m π ⟨k + 1, hk⟩).val.val - (hiIso m π ⟨k, by omega⟩).val.val - 1 := by
      dsimp only [extG]
      have hne : k + 1 ≠ 0 := by omega
      rw [dif_neg hne]
      have hnext : k + 1 < n - m := hk
      simp only [Nat.add_sub_cancel, hnext, ↓reduceDIte]
    have hlt_iso : (hiIso m π ⟨k, by omega⟩).val.val < (hiIso m π ⟨k + 1, hk⟩).val.val :=
      Fin.lt_def.mp ((hiIso m π).strictMono (Fin.lt_def.mpr (by dsimp only; omega)))
    rw [he]; omega

private lemma sum_extG {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (π : Equiv.Perm (Fin n)) (hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩) :
    ∑ i, extG hm1 hmn π i = m - 1 := by
  rw [← gapPrefix_top]
  by_cases hnm : n - m = 0
  · have hpm : (π.symm ⟨m - 1, by omega⟩).val = n - 1 := by
      by_contra hne
      have hlt : (π.symm ⟨m - 1, by omega⟩).val + 1 < n := by
        have := (π.symm ⟨m - 1, by omega⟩).isLt; omega
      have hgt := ((foataInv_fixed_iff π ⟨m - 1, by omega⟩).mp hfix).2 hlt
      rw [Equiv.apply_symm_apply] at hgt
      have hgt' : m - 1 < (π ⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hlt⟩).val := Fin.lt_def.mp hgt
      have hlt' := (π ⟨(π.symm ⟨m - 1, by omega⟩).val + 1, hlt⟩).isLt
      omega
    have h1 : n - m + 1 = 0 + 1 := by omega
    rw [h1, gapPrefix_succ _ 0 (by omega), gapPrefix_zero, zero_add]
    simp only [extG, ↓reduceDIte, hpm]; omega
  · let lastJ : Fin (n - m) := ⟨n - m - 1, by omega⟩
    have htop : n - m + 1 = (lastJ.val + 1) + 1 := by dsimp only [lastJ]; omega
    rw [htop, gapPrefix_succ _ (lastJ.val + 1) (by omega)]
    have hhip := hiPos_extG hm1 hmn π hfix lastJ
    unfold hiPos at hhip
    have hlastG : extG hm1 hmn π ⟨lastJ.val + 1, by omega⟩ = n - (hiIso m π lastJ).val.val - 1 := by
      dsimp only [extG]
      have hne : lastJ.val + 1 ≠ 0 := by omega
      rw [dif_neg hne]
      have hnot : ¬ (lastJ.val + 1 < n - m) := by dsimp only [lastJ]; omega
      simp only [Nat.add_sub_cancel, hnot, ↓reduceDIte]
    have hlt_n : (hiIso m π lastJ).val.val < n := (hiIso m π lastJ).val.isLt
    rw [hlastG]; dsimp only [lastJ] at hhip ⊢; omega

private lemma ge1_extG {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n)
    (π : Equiv.Perm (Fin n)) (_hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩)
    (hmax : ∀ x : Fin n, foataInv π x = x → x ≤ ⟨m - 1, by omega⟩)
    (j : Fin (n - m))
    (hjfix : foataInv (extSigma m π) (extSigma m π j) = extSigma m π j) :
    1 ≤ extG hm1 hmn π j.succ := by
  have hnotfix : foataInv π (π (hiIso m π j).val) ≠ π (hiIso m π j).val := by
    intro h
    have hle : (π (hiIso m π j).val).val ≤ m - 1 := Fin.le_def.mp (hmax (π (hiIso m π j).val) h)
    have hge : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
    omega
  have hlm_σ := ((foataInv_fixed_iff (extSigma m π) (extSigma m π j)).mp hjfix)
  rw [Equiv.symm_apply_apply] at hlm_σ
  have hlm_π : IsLMax π (hiIso m π j).val := (isLMax_hi_iff π j).mpr hlm_σ.1
  have hp_lt : ∃ h : (hiIso m π j).val.val + 1 < n,
      ¬ π (hiIso m π j).val < π ⟨(hiIso m π j).val.val + 1, h⟩ := by
    by_contra hall
    push Not at hall
    apply hnotfix
    rw [foataInv_fixed_iff, Equiv.symm_apply_apply]
    exact ⟨hlm_π, hall⟩
  obtain ⟨hp1, hle_next⟩ := hp_lt
  dsimp only [extG]
  have hne : j.succ.val ≠ 0 := by simp
  rw [dif_neg hne]
  have hjeq : (⟨j.succ.val - 1, by omega⟩ : Fin (n - m)) = j := Fin.ext (by simp)
  simp only [hjeq]
  split_ifs with hnext
  · have hjeq1 : (⟨j.succ.val - 1 + 1, hnext⟩ : Fin (n - m)) = ⟨j.val + 1, hnext⟩ := Fin.ext (by simp)
    simp only [hjeq1]
    have hgt_σ : extSigma m π j < extSigma m π ⟨j.val + 1, hnext⟩ := hlm_σ.2 hnext
    simp only [extSigma, Equiv.ofBijective_apply, Fin.lt_def] at hgt_σ
    have h1 : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
    have h2 : m ≤ (π (hiIso m π ⟨j.val + 1, hnext⟩).val).val :=
      (Finset.mem_filter.mp (hiIso m π ⟨j.val + 1, hnext⟩).prop).2
    have hgt_π : π (hiIso m π j).val < π (hiIso m π ⟨j.val + 1, hnext⟩).val :=
      Fin.lt_def.mpr (by omega)
    have hpos_gt : (hiIso m π j).val.val < (hiIso m π ⟨j.val + 1, hnext⟩).val.val :=
      Fin.lt_def.mp ((hiIso m π).strictMono (Fin.lt_def.mpr (by dsimp only; omega)))
    have hne_pos : (hiIso m π ⟨j.val + 1, hnext⟩).val.val ≠ (hiIso m π j).val.val + 1 := by
      intro heq
      have : (hiIso m π ⟨j.val + 1, hnext⟩).val = ⟨(hiIso m π j).val.val + 1, hp1⟩ := Fin.ext heq
      rw [this] at hgt_π; exact hle_next hgt_π
    omega
  · omega

private lemma foataFPSet_le_of_max'_eq {n : ℕ} {π : Equiv.Perm (Fin n)} {mIdx : Fin n}
    (hne : (foataFPSet π).Nonempty) (hmax : (foataFPSet π).max' hne = mIdx)
    {x : Fin n} (hx : foataInv π x = x) : x ≤ mIdx := by
  rw [← hmax]
  exact Finset.le_max' (foataFPSet π) x (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩)

private lemma buildPerm_fix_m {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ)
    (hg : ∑ i, g i = m - 1) :
    foataInv (buildPerm hm1 hmn asc σ g hg) ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩ := by
  have hg0_lt : g 0 < n := by
    have h0 : g 0 ≤ ∑ i, g i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    omega
  have hpm : (buildPerm hm1 hmn asc σ g hg).symm ⟨m - 1, by omega⟩ = ⟨g 0, hg0_lt⟩ := by
    apply (buildPerm hm1 hmn asc σ g hg).injective
    rw [Equiv.apply_symm_apply]; exact (buildPerm_g0 hm1 hmn asc σ g hg).symm
  rw [foataInv_fixed_iff, hpm]
  refine ⟨fun q hq => ?_, fun hlt => ?_⟩
  · have hq0 : q.val ≠ g 0 := ne_of_lt (Fin.lt_def.mp hq)
    have hqhi : ∀ j : Fin (n - m), q.val ≠ hiPos g j := fun j heq =>
      not_lt_of_ge (le_of_lt (Fin.lt_def.mp hq)) (heq ▸ hiPos_gt_g0 g j)
    have hsm := buildPerm_small hm1 hmn asc σ g hg q hq0 hqhi
    rw [buildPerm_g0 hm1 hmn asc σ g hg]
    exact Fin.lt_def.mpr hsm
  · have hlt' : g 0 + 1 < n := hlt
    have hnm_pos : 0 < n - m := by
      by_contra h0
      have h0eq : g 0 = m - 1 := by
        rw [← hg, ← gapPrefix_top]
        have h1 : gapPrefix g (n - m + 1) = gapPrefix g (0 + 1) := by congr 1; omega
        rw [h1, gapPrefix_succ g 0 (by omega), gapPrefix_zero, zero_add]; rfl
      omega
    have h0pos : hiPos g ⟨0, hnm_pos⟩ = g 0 + 1 := by
      unfold hiPos; dsimp only
      rw [gapPrefix_succ g 0 (by omega), gapPrefix_zero, zero_add]
      have : g ⟨0, by omega⟩ = g 0 := rfl
      omega
    have heq : (⟨(⟨g 0, hg0_lt⟩ : Fin n).val + 1, hlt⟩ : Fin n) =
        ⟨hiPos g ⟨0, hnm_pos⟩, hiPos_lt_n hm1 hmn g hg ⟨0, hnm_pos⟩⟩ :=
      Fin.ext h0pos.symm
    rw [buildPerm_g0 hm1 hmn asc σ g hg, heq, buildPerm_hi hm1 hmn asc σ g hg ⟨0, hnm_pos⟩]
    exact Fin.lt_def.mpr (by dsimp only; omega)

private lemma buildPerm_no_hi_fp {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ)
    (hg : ∑ i, g i = m - 1)
    (hge1 : ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ)
    (x : Fin n) (hx : (⟨m - 1, by omega⟩ : Fin n) < x) :
    foataInv (buildPerm hm1 hmn asc σ g hg) x ≠ x := by
  intro hxf
  have hxm : m ≤ x.val := by have hx' : m - 1 < x.val := Fin.lt_def.mp hx; omega
  let j : Fin (n - m) := σ.symm ⟨x.val - m, by have := x.isLt; omega⟩
  have hxj : buildPerm hm1 hmn asc σ g hg ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ = x := by
    rw [buildPerm_hi hm1 hmn asc σ g hg j]; ext; simp [j]; omega
  have hpx : (buildPerm hm1 hmn asc σ g hg).symm x = ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ := by
    apply (buildPerm hm1 hmn asc σ g hg).injective; rw [Equiv.apply_symm_apply, hxj]
  have hxf' := (foataInv_fixed_iff (buildPerm hm1 hmn asc σ g hg) x).mp hxf
  rw [hpx, hxj] at hxf'
  have hσfix : foataInv σ (σ j) = σ j := by
    rw [foataInv_fixed_iff, Equiv.symm_apply_apply]
    refine ⟨fun j' hj' => ?_, fun hlt => ?_⟩
    · have hpos_lt : (⟨hiPos g j', hiPos_lt_n hm1 hmn g hg j'⟩ : Fin n) <
          ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ :=
        Fin.lt_def.mpr (hiPos_strictMono g hj')
      have hval := hxf'.1 _ hpos_lt
      rw [buildPerm_hi hm1 hmn asc σ g hg j', buildPerm_hi hm1 hmn asc σ g hg j] at hval
      have hval' : m + (σ j').val < m + (σ j).val := Fin.lt_def.mp hval
      exact Fin.lt_def.mpr (by omega)
    · have hnext_lt : hiPos g j + 1 < n := by
        have := hiPos_lt_n hm1 hmn g hg ⟨j.val + 1, hlt⟩
        have := hiPos_strictMono g (show j < ⟨j.val + 1, hlt⟩ from Fin.lt_def.mpr (by dsimp only; omega))
        omega
      have hgt := hxf'.2 hnext_lt
      have hnot_sm : ¬ (hiPos g j + 1 ≠ g 0 ∧ ∀ j' : Fin (n - m), hiPos g j + 1 ≠ hiPos g j') := by
        rintro ⟨h0, hhi⟩
        have hsm := buildPerm_small hm1 hmn asc σ g hg ⟨hiPos g j + 1, hnext_lt⟩ h0 hhi
        have hgt' : x.val < (buildPerm hm1 hmn asc σ g hg ⟨hiPos g j + 1, hnext_lt⟩).val := by
          have := Fin.lt_def.mp hgt; dsimp only at this; exact this
        omega
      have hne0 : hiPos g j + 1 ≠ g 0 := by have := hiPos_gt_g0 g j; omega
      push Not at hnot_sm
      obtain ⟨j', hj'⟩ := hnot_sm hne0
      have hj'eq : j' = ⟨j.val + 1, hlt⟩ := by
        have hgtj : j < j' := by
          by_contra hle; push Not at hle
          have := (hiPos_strictMono g).monotone hle
          omega
        have hle1 : (⟨j.val + 1, hlt⟩ : Fin (n - m)) ≤ j' :=
          Fin.le_def.mpr (by have := Fin.lt_def.mp hgtj; dsimp only; omega)
        rcases eq_or_lt_of_le hle1 with rfl | hlt'
        · rfl
        · have := hiPos_strictMono g hlt'
          have := hiPos_strictMono g (show j < ⟨j.val + 1, hlt⟩ from Fin.lt_def.mpr (by dsimp only; omega))
          omega
      subst hj'eq
      have hpos_eq : (⟨hiPos g j + 1, hnext_lt⟩ : Fin n) =
          ⟨hiPos g ⟨j.val + 1, hlt⟩, hiPos_lt_n hm1 hmn g hg ⟨j.val + 1, hlt⟩⟩ := Fin.ext hj'
      have hgt' : (buildPerm hm1 hmn asc σ g hg ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩).val <
          (buildPerm hm1 hmn asc σ g hg ⟨hiPos g ⟨j.val + 1, hlt⟩, hiPos_lt_n hm1 hmn g hg ⟨j.val + 1, hlt⟩⟩).val := by
        have h1 := Fin.lt_def.mp hgt
        rw [← hxj] at h1
        simpa only [← hpos_eq] using h1
      rw [buildPerm_hi hm1 hmn asc σ g hg j, buildPerm_hi hm1 hmn asc σ g hg ⟨j.val + 1, hlt⟩] at hgt'
      dsimp only at hgt'
      exact Fin.lt_def.mpr (by omega)
  have hgj : 1 ≤ g j.succ := hge1 j hσfix
  have hnext_lt : hiPos g j + 1 < n := by
    unfold hiPos
    have h1 : gapPrefix g (j.val + 1) + g j.succ = gapPrefix g (j.val + 2) :=
      (gapPrefix_succ g (j.val + 1) (by omega)).symm
    have h2 : gapPrefix g (j.val + 2) ≤ m - 1 := by
      rw [← hg, ← gapPrefix_top]; exact gapPrefix_mono g (by omega)
    have hj := j.isLt; omega
  have hne0 : hiPos g j + 1 ≠ g 0 := by have := hiPos_gt_g0 g j; omega
  have hne_hi : ∀ j' : Fin (n - m), hiPos g j + 1 ≠ hiPos g j' := by
    intro j' heq
    rcases le_or_gt j' j with hle | hgt
    · have : hiPos g j' ≤ hiPos g j := (hiPos_strictMono g).monotone hle
      omega
    · have hsucc_le : j.val + 1 ≤ j'.val := by have := Fin.lt_def.mp hgt; omega
      have hgp : gapPrefix g (j.val + 2) ≤ gapPrefix g (j'.val + 1) := gapPrefix_mono g (by omega)
      have h1 : gapPrefix g (j.val + 2) = gapPrefix g (j.val + 1) + g j.succ :=
        gapPrefix_succ g (j.val + 1) (by omega)
      unfold hiPos at heq; omega
  have hsm := buildPerm_small hm1 hmn asc σ g hg ⟨hiPos g j + 1, hnext_lt⟩ hne0 hne_hi
  have hgt' : x.val < (buildPerm hm1 hmn asc σ g hg ⟨hiPos g j + 1, hnext_lt⟩).val := by
    have := Fin.lt_def.mp (hxf'.2 hnext_lt); dsimp only at this; exact this
  omega

private lemma buildPerm_maxFP {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ)
    (hg : ∑ i, g i = m - 1)
    (hge1 : ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ) :
    ∃ h : (foataFPSet (buildPerm hm1 hmn asc σ g hg)).Nonempty,
      (foataFPSet (buildPerm hm1 hmn asc σ g hg)).max' h = ⟨m - 1, by omega⟩ := by
  have hfix_m := buildPerm_fix_m hm1 hmn asc σ g hg
  have hmem_m : (⟨m - 1, by omega⟩ : Fin n) ∈ foataFPSet (buildPerm hm1 hmn asc σ g hg) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix_m⟩
  refine ⟨⟨⟨m - 1, by omega⟩, hmem_m⟩, le_antisymm ?_
    (Finset.le_max' (foataFPSet (buildPerm hm1 hmn asc σ g hg)) ⟨m - 1, by omega⟩ hmem_m)⟩
  refine Finset.max'_le (foataFPSet (buildPerm hm1 hmn asc σ g hg)) _ ⟨m - 1, by omega⟩ fun x hx => ?_
  by_contra hgt; push Not at hgt
  exact buildPerm_no_hi_fp hm1 hmn asc σ g hg hge1 x hgt (Finset.mem_filter.mp hx).2

private lemma buildPerm_avoids {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ)
    (hg : ∑ i, g i = m - 1)
    (hge1 : ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ) :
    AvoidsArrow asc (buildPerm hm1 hmn asc σ g hg) := by
  have hg0_lt : g 0 < n := by
    have h0 : g 0 ≤ ∑ i, g i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
    omega
  intro x₁ x₂ x₃ h12 h23 hord hfix3
  have hx3_le : x₃ ≤ ⟨m - 1, by omega⟩ := by
    by_contra hgt; push Not at hgt
    exact buildPerm_no_hi_fp hm1 hmn asc σ g hg hge1 x₃ hgt hfix3
  have hx1_lt : x₁.val < m - 1 := by
    have h1 := Fin.lt_def.mp (lt_trans h12 h23); have h2 : x₃.val ≤ m - 1 := Fin.le_def.mp hx3_le; omega
  have hx2_lt : x₂.val < m - 1 := by
    have h1 := Fin.lt_def.mp h23; have h2 : x₃.val ≤ m - 1 := Fin.le_def.mp hx3_le; omega
  have hsm_of_lt : ∀ x : Fin n, x.val < m - 1 →
      isSmallPos n m g ((buildPerm hm1 hmn asc σ g hg).symm x).val = true := by
    intro x hx
    simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      List.all_eq_true, List.mem_finRange, true_implies]
    refine ⟨fun h => ?_, fun j h => ?_⟩
    · have heq : (buildPerm hm1 hmn asc σ g hg).symm x = ⟨g 0, hg0_lt⟩ := Fin.ext h
      have h1 := congrArg (buildPerm hm1 hmn asc σ g hg) heq
      rw [Equiv.apply_symm_apply, buildPerm_g0] at h1
      have hval := congrArg Fin.val h1; dsimp only at hval; omega
    · have heq : (buildPerm hm1 hmn asc σ g hg).symm x =
          ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ := Fin.ext h
      have h1 := congrArg (buildPerm hm1 hmn asc σ g hg) heq
      rw [Equiv.apply_symm_apply, buildPerm_hi] at h1
      have hval := congrArg Fin.val h1; dsimp only at hval; omega
  have hr_val : ∀ p : Fin n, isSmallPos n m g p.val = true →
      (buildPerm hm1 hmn asc σ g hg p).val =
        if asc then smallRank n m g p.val else m - 2 - smallRank n m g p.val := by
    intro p hsm
    simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
      List.all_eq_true, List.mem_finRange, true_implies] at hsm
    have hnot : ¬ ∃ j : Fin (n - m), p.val = hiPos g j := fun ⟨j, hj⟩ => hsm.2 j hj
    simp only [buildPerm, Equiv.ofBijective_apply, buildFun, hsm.1, ↓reduceDIte, hnot]
    cases asc <;> rfl
  have hp1_sm := hsm_of_lt x₁ hx1_lt
  have hp2_sm := hsm_of_lt x₂ hx2_lt
  have hv1 := hr_val ((buildPerm hm1 hmn asc σ g hg).symm x₁) hp1_sm
  have hv2 := hr_val ((buildPerm hm1 hmn asc σ g hg).symm x₂) hp2_sm
  rw [Equiv.apply_symm_apply] at hv1 hv2
  have h12' := Fin.lt_def.mp h12
  cases asc
  · simp only [Bool.false_eq_true, ↓reduceIte] at hord hv1 hv2
    have hlt_r := smallRank_strict g hord hp1_sm
    omega
  · simp only [↓reduceIte] at hord hv1 hv2
    have hlt_r := smallRank_strict g hord hp2_sm
    omega

private lemma buildPerm_left_inv {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (π : Equiv.Perm (Fin n)) (hav : AvoidsArrow asc π)
    (hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩) :
    buildPerm hm1 hmn asc (extSigma m π) (extG hm1 hmn π) (sum_extG hm1 hmn π hfix) = π := by
  let mIdx : Fin n := ⟨m - 1, by omega⟩
  have hg := sum_extG hm1 hmn π hfix
  ext p
  by_cases hp0 : p.val = extG hm1 hmn π 0
  · have hp_eq : p = π.symm mIdx := Fin.ext (by rw [hp0]; simp [extG, mIdx])
    have hp_eq2 : p = ⟨extG hm1 hmn π 0, by
      have h0 : extG hm1 hmn π 0 ≤ ∑ i, extG hm1 hmn π i :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      omega⟩ := Fin.ext hp0
    rw [hp_eq2, buildPerm_g0, ← hp_eq2, hp_eq, Equiv.apply_symm_apply]
  · by_cases hhi : ∃ j : Fin (n - m), p.val = hiPos (extG hm1 hmn π) j
    · obtain ⟨j, hj⟩ := hhi
      have hp_eq : p = (hiIso m π j).val := Fin.ext (hj.trans (hiPos_extG hm1 hmn π hfix j))
      have hp_eq' : p = ⟨hiPos (extG hm1 hmn π) j, hiPos_lt_n hm1 hmn (extG hm1 hmn π) hg j⟩ :=
        Fin.ext hj
      rw [hp_eq', buildPerm_hi, ← hp_eq', hp_eq]
      simp only [extSigma, Equiv.ofBijective_apply]
      have hge : m ≤ (π (hiIso m π j).val).val := (Finset.mem_filter.mp (hiIso m π j).prop).2
      omega
    · have hsm_iff : ∀ q : Fin n, isSmallPos n m (extG hm1 hmn π) q.val = true ↔ (π q).val < m - 1 := by
        intro q
        simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
          List.all_eq_true, List.mem_finRange, true_implies]
        constructor
        · rintro ⟨hq0, hqhi⟩
          have hne_m : π q ≠ mIdx := fun h => hq0 (by
            have := congrArg π.symm h; rw [Equiv.symm_apply_apply] at this
            simp [extG, mIdx, this])
          have hlt_m : (π q).val < m := by
            by_contra hge; push Not at hge
            have hmem : q ∈ hiSet m π := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hge⟩
            let j := (hiIso m π).symm ⟨q, hmem⟩
            apply hqhi j
            rw [hiPos_extG hm1 hmn π hfix j]
            exact (congrArg (fun z => z.val.val) ((hiIso m π).apply_symm_apply ⟨q, hmem⟩)).symm
          have : (π q).val ≠ m - 1 := fun h => hne_m (Fin.ext h)
          omega
        · intro hlt
          refine ⟨fun h => ?_, fun j h => ?_⟩
          · have hqeq : q = π.symm mIdx := Fin.ext (by simpa [extG, mIdx] using h)
            rw [hqeq, Equiv.apply_symm_apply] at hlt; dsimp only [mIdx] at hlt; omega
          · have hqeq : q = (hiIso m π j).val := Fin.ext (h.trans (hiPos_extG hm1 hmn π hfix j))
            rw [hqeq] at hlt
            have := (Finset.mem_filter.mp (hiIso m π j).prop).2; omega
      have hpsm : (π p).val < m - 1 := (hsm_iff p).mp (by
        simp only [isSmallPos, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
          List.all_eq_true, List.mem_finRange, true_implies]
        exact ⟨hp0, fun j h => hhi ⟨j, h⟩⟩)
      have hord_sm : ∀ q : Fin n, (π q).val < m - 1 →
          (q < p ↔ if asc then (π q).val < (π p).val else (π p).val < (π q).val) := by
        intro q hqsm
        cases asc
        · simp only [Bool.false_eq_true, ↓reduceIte]
          constructor
          · intro hqp
            by_contra hle; push Not at hle
            rcases eq_or_lt_of_le hle with heq | hlt'
            · exact ne_of_lt hqp (π.injective (Fin.ext heq))
            · exact hav (π q) (π p) mIdx (Fin.lt_def.mpr hlt') (Fin.lt_def.mpr hpsm)
                (by simp [hqp]) hfix
          · intro hlt'
            by_contra hle; push Not at hle
            rcases eq_or_lt_of_le hle with rfl | hgt
            · omega
            · exact hav (π p) (π q) mIdx (Fin.lt_def.mpr hlt') (Fin.lt_def.mpr hqsm)
                (by simp [hgt]) hfix
        · simp only [↓reduceIte]
          constructor
          · intro hqp
            by_contra hle; push Not at hle
            rcases eq_or_lt_of_le hle with heq | hlt'
            · exact ne_of_lt hqp (π.injective (Fin.ext heq.symm))
            · exact hav (π p) (π q) mIdx (Fin.lt_def.mpr hlt') (Fin.lt_def.mpr hqsm)
                (by simp [hqp]) hfix
          · intro hlt'
            by_contra hle; push Not at hle
            rcases eq_or_lt_of_le hle with rfl | hgt
            · omega
            · exact hav (π q) (π p) mIdx (Fin.lt_def.mpr hlt') (Fin.lt_def.mpr hpsm)
                (by simp [hgt]) hfix
      have hcard_sm : smallRank n m (extG hm1 hmn π) p.val =
          (Finset.univ.filter fun q : Fin n => q < p ∧ (π q).val < m - 1).card := by
        unfold smallRank
        rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ List.nodup_range)]
        refine Finset.card_bij
          (fun x hx => ⟨x, lt_trans (List.mem_range.mp (List.mem_filter.mp (List.mem_toFinset.mp hx)).1) p.isLt⟩)
          (fun x hx => ?_) (fun _ _ _ _ h => congrArg Fin.val h) (fun q hq => ?_)
        · simp only [List.mem_toFinset, List.mem_filter, List.mem_range] at hx
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨Fin.lt_def.mpr hx.1, (hsm_iff _).mp hx.2⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          exact ⟨q.val, by simp [Fin.lt_def.mp hq.1, (hsm_iff q).mpr hq.2], Fin.ext rfl⟩
      have hrank_eq : smallRank n m (extG hm1 hmn π) p.val =
          if asc then (π p).val else m - 2 - (π p).val := by
        rw [hcard_sm]
        cases asc
        · simp only [Bool.false_eq_true, ↓reduceIte] at hord_sm ⊢
          have hbij : (Finset.univ.filter fun q : Fin n => q < p ∧ (π q).val < m - 1).card =
              (Finset.Ioo (π p).val (m - 1)).card := by
            refine Finset.card_bij (fun q _ => (π q).val) (fun q hq => ?_)
              (fun q1 _ q2 _ h => π.injective (Fin.ext h)) (fun v hv => ?_)
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioo] at hq ⊢
              exact ⟨(hord_sm q hq.2).mp hq.1, hq.2⟩
            · simp only [Finset.mem_Ioo] at hv
              refine ⟨π.symm ⟨v, by omega⟩, ?_, by simp⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
              exact ⟨(hord_sm _ (by simpa using hv.2)).mpr (by simpa using hv.1), hv.2⟩
          rw [hbij, Nat.card_Ioo]; omega
        · simp only [↓reduceIte] at hord_sm ⊢
          have hbij : (Finset.univ.filter fun q : Fin n => q < p ∧ (π q).val < m - 1).card =
              (Finset.range (π p).val).card := by
            refine Finset.card_bij (fun q _ => (π q).val) (fun q hq => ?_)
              (fun q1 _ q2 _ h => π.injective (Fin.ext h)) (fun v hv => ?_)
            · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] at hq ⊢
              exact (hord_sm q hq.2).mp hq.1
            · simp only [Finset.mem_range] at hv
              refine ⟨π.symm ⟨v, by omega⟩, ?_, by simp⟩
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply]
              have hv_lt : (π (π.symm ⟨v, by omega⟩)).val < m - 1 := by simp; omega
              exact ⟨(hord_sm _ hv_lt).mpr (by simpa using hv), by omega⟩
          rw [hbij, Finset.card_range]
      simp only [buildPerm, Equiv.ofBijective_apply, buildFun, hp0, ↓reduceDIte, hhi]
      cases asc <;> simp only [Bool.false_eq_true, ↓reduceIte] at hrank_eq ⊢ <;> omega

private lemma buildPerm_right_inv {n m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool)
    (σ : Equiv.Perm (Fin (n - m))) (g : Fin (n - m + 1) → ℕ) (hg : ∑ i, g i = m - 1) :
    extSigma m (buildPerm hm1 hmn asc σ g hg) = σ ∧
      extG hm1 hmn (buildPerm hm1 hmn asc σ g hg) = g := by
  have hhi_eq : ∀ j : Fin (n - m),
      (hiIso m (buildPerm hm1 hmn asc σ g hg) j).val = ⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ := by
    have hset : hiSet m (buildPerm hm1 hmn asc σ g hg) =
        Finset.univ.image (fun j : Fin (n - m) => (⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩ : Fin n)) := by
      ext p
      simp only [hiSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · intro hpm
        by_cases hp0 : p.val = g 0
        · exfalso
          have heq : p = ⟨g 0, by
            have h0 : g 0 ≤ ∑ i, g i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
            omega⟩ := Fin.ext hp0
          rw [heq, buildPerm_g0] at hpm; dsimp only at hpm; omega
        · by_contra hnot
          have hne : ∀ j : Fin (n - m), p.val ≠ hiPos g j := fun j hj => hnot ⟨j, Fin.ext hj.symm⟩
          have := buildPerm_small hm1 hmn asc σ g hg p hp0 hne; omega
      · rintro ⟨j, rfl⟩
        rw [buildPerm_hi]; dsimp only; omega
    let f : Fin (n - m) → hiSet m (buildPerm hm1 hmn asc σ g hg) := fun j =>
      ⟨⟨hiPos g j, hiPos_lt_n hm1 hmn g hg j⟩, by
        rw [hset]; exact Finset.mem_image_of_mem _ (Finset.mem_univ j)⟩
    have hf_mono : StrictMono f := fun a b hab =>
      Subtype.mk_lt_mk.mpr (Fin.lt_def.mpr (hiPos_strictMono g hab))
    have hid : ∀ j : Fin (n - m), (hiIso m (buildPerm hm1 hmn asc σ g hg)).symm (f j) = j := by
      have hmono : StrictMono (fun j => (hiIso m (buildPerm hm1 hmn asc σ g hg)).symm (f j)) :=
        (hiIso m (buildPerm hm1 hmn asc σ g hg)).symm.strictMono.comp hf_mono
      exact fun j => fin_strictMono_id hmono j
    intro j
    have := congrArg (fun z => (hiIso m (buildPerm hm1 hmn asc σ g hg) z).val) (hid j)
    simpa [f] using this.symm
  constructor
  · ext j
    simp only [extSigma, Equiv.ofBijective_apply, hhi_eq j, buildPerm_hi]
    omega
  · ext i
    dsimp only [extG]
    by_cases h0 : i.val = 0
    · rw [dif_pos h0]
      have hpm : (buildPerm hm1 hmn asc σ g hg).symm ⟨m - 1, by omega⟩ = ⟨g 0, by
        have h0le : g 0 ≤ ∑ i, g i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
        omega⟩ := by
        apply (buildPerm hm1 hmn asc σ g hg).injective
        rw [Equiv.apply_symm_apply]; exact (buildPerm_g0 hm1 hmn asc σ g hg).symm
      rw [hpm]
      have : i = 0 := Fin.ext h0
      rw [this]
    · rw [dif_neg h0]
      let j : Fin (n - m) := ⟨i.val - 1, by omega⟩
      split_ifs with hnext
      · rw [hhi_eq ⟨j.val + 1, hnext⟩, hhi_eq j]
        dsimp only [hiPos]
        have : (⟨j.val + 1, hnext⟩ : Fin (n - m)).val + 1 = (j.val + 1) + 1 := rfl
        rw [this, gapPrefix_succ g (j.val + 1) (by omega)]
        have heq_i : (⟨j.val + 1, by omega⟩ : Fin (n - m + 1)) = i := Fin.ext (by dsimp only [j]; omega)
        rw [heq_i]; omega
      · rw [hhi_eq j]
        dsimp only [hiPos]
        have hlast : j.val + 1 = n - m := by dsimp only [j] at hnext ⊢; omega
        have hsum : gapPrefix g (n - m) + g i = m - 1 := by
          have heq_i : (⟨n - m, by omega⟩ : Fin (n - m + 1)) = i := Fin.ext (by dsimp only; omega)
          rw [← hg, ← gapPrefix_top, gapPrefix_succ g (n - m) (by omega), heq_i]
        rw [hlast]; omega

private lemma card_RHS_eq (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    Nat.card (Σ (σ : Equiv.Perm (Fin (n - m))),
      {g : Fin (n - m + 1) → ℕ //
        (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ}) =
    ∑ k ∈ Finset.range (n - m + 1),
      Nat.choose (n - m) k * Nat.choose (m + k - 1) (n - m) * derangementCount k := by
  classical
  have : ∀ σ : Equiv.Perm (Fin (n - m)),
      Finite {g : Fin (n - m + 1) → ℕ //
        (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ} := by
    intro σ
    have := finite_compositions (n - m) (m - 1)
    exact Finite.of_injective
      (f := fun x => (⟨x.val, x.prop.1⟩ : {g : Fin (n - m + 1) → ℕ // ∑ i, g i = m - 1}))
      (fun ⟨_, _⟩ ⟨_, _⟩ h => Subtype.ext (by simpa using congrArg Subtype.val h))
  rw [Nat.card_sigma]
  have hinner : ∀ σ : Equiv.Perm (Fin (n - m)),
      Nat.card {g : Fin (n - m + 1) → ℕ //
        (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ} =
      Nat.choose (m + (n - m - (foataFPSet σ).card) - 1) (n - m) := by
    intro σ
    let F : Finset (Fin (n - m)) := Finset.univ.filter fun j => foataInv σ (σ j) = σ j
    have hFcard : F.card = (foataFPSet σ).card := by
      refine Finset.card_bij (fun j _ => σ j) (fun j hj => ?_) (fun _ _ _ _ h => σ.injective h) (fun x hx => ?_)
      · simp only [F, foataFPSet, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢; exact hj
      · simp only [foataFPSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
        exact ⟨σ.symm x, by simp [F, hx], by simp⟩
    have heq_sub : {g : Fin (n - m + 1) → ℕ //
        (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ} =
      {g : Fin (n - m + 1) → ℕ // (∑ i, g i = m - 1) ∧ ∀ j ∈ F, 1 ≤ g j.succ} := by
      congr 1; ext g; simp [F]
    rw [heq_sub, card_compositions_ge1 (n - m) (m - 1) F, hFcard]
    have hfp_le : (foataFPSet σ).card ≤ n - m := by
      calc (foataFPSet σ).card ≤ (Finset.univ : Finset (Fin (n - m))).card := Finset.card_le_card (Finset.subset_univ _)
        _ = n - m := by simp
    split_ifs with hlt
    · symm; apply Nat.choose_eq_zero_of_lt; omega
    · congr 1; omega
  simp only [hinner]
  have hgroup : ∑ σ : Equiv.Perm (Fin (n - m)),
      Nat.choose (m + (n - m - (foataFPSet σ).card) - 1) (n - m) =
    ∑ k ∈ Finset.range (n - m + 1),
      (Finset.univ.filter fun σ : Equiv.Perm (Fin (n - m)) => n - m - (foataFPSet σ).card = k).card *
        Nat.choose (m + k - 1) (n - m) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (g := fun σ : Equiv.Perm (Fin (n - m)) => n - m - (foataFPSet σ).card)
      (t := Finset.range (n - m + 1)) (fun σ _ => by rw [Finset.mem_range]; omega)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_congr rfl (fun σ hσ => by rw [(Finset.mem_filter.mp hσ).2])]
    simp
  rw [hgroup]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hcard_k : (Finset.univ.filter fun σ : Equiv.Perm (Fin (n - m)) =>
      n - m - (foataFPSet σ).card = k).card = Nat.choose (n - m) k * derangementCount k := by
    have hiff : ∀ σ : Equiv.Perm (Fin (n - m)),
        (n - m - (foataFPSet σ).card = k) ↔ (foataFPSet σ).card = (n - m) - k := by
      intro σ
      have hle : (foataFPSet σ).card ≤ n - m := by
        calc (foataFPSet σ).card ≤ (Finset.univ : Finset (Fin (n - m))).card := Finset.card_le_card (Finset.subset_univ _)
          _ = n - m := by simp
      omega
    simp only [hiff]
    rw [← Fintype.card_subtype]
    exact card_foataFP_card (n - m) k (by omega)
  rw [hcard_k]; ring

private lemma card_avoids_fixed_max (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) (asc : Bool) :
    Nat.card {π : Equiv.Perm (Fin n) //
      AvoidsArrow asc π ∧
      ∃ h : (foataFPSet π).Nonempty, (foataFPSet π).max' h = ⟨m - 1, by omega⟩} =
    ∑ k ∈ Finset.range (n - m + 1),
      Nat.choose (n - m) k * Nat.choose (m + k - 1) (n - m) * derangementCount k := by
  let LHS := {π : Equiv.Perm (Fin n) //
    AvoidsArrow asc π ∧ ∃ h : (foataFPSet π).Nonempty, (foataFPSet π).max' h = ⟨m - 1, by omega⟩}
  let RHS := Σ (σ : Equiv.Perm (Fin (n - m))),
    {g : Fin (n - m + 1) → ℕ //
      (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ (σ j) = σ j → 1 ≤ g j.succ}
  suffices e : LHS ≃ RHS by
    rw [Nat.card_congr e, card_RHS_eq n m hm1 hmn]
  refine
    { toFun := fun ⟨π, hprop⟩ =>
        have hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩ := by
          obtain ⟨hne, hmax⟩ := hprop.2
          rw [← hmax]; exact (Finset.mem_filter.mp (Finset.max'_mem (foataFPSet π) hne)).2
        have hle_max : ∀ x : Fin n, foataInv π x = x → x ≤ ⟨m - 1, by omega⟩ := fun x hx => by
          obtain ⟨hne, hmax⟩ := hprop.2
          exact foataFPSet_le_of_max'_eq hne hmax hx
        ⟨extSigma m π, ⟨extG hm1 hmn π, sum_extG hm1 hmn π hfix, ge1_extG hm1 hmn π hfix hle_max⟩⟩
      invFun := fun ⟨σ, ⟨g, hg, hge1⟩⟩ =>
        ⟨buildPerm hm1 hmn asc σ g hg,
          buildPerm_avoids hm1 hmn asc σ g hg hge1,
          buildPerm_maxFP hm1 hmn asc σ g hg hge1⟩
      left_inv := fun ⟨π, hav, hne, hmax⟩ => by
        have hfix : foataInv π ⟨m - 1, by omega⟩ = ⟨m - 1, by omega⟩ := by
          rw [← hmax]; exact (Finset.mem_filter.mp (Finset.max'_mem (foataFPSet π) hne)).2
        exact Subtype.ext (buildPerm_left_inv hm1 hmn asc π hav hfix)
      right_inv := fun ⟨σ, ⟨g, hg, hge1⟩⟩ => by
        dsimp only
        obtain ⟨hσ_eq, hg_eq⟩ := buildPerm_right_inv hm1 hmn asc σ g hg
        refine Sigma.ext hσ_eq ?_
        have haux : ∀ {σ₁ σ₂ : Equiv.Perm (Fin (n - m))} (h : σ₁ = σ₂)
            (a : {g : Fin (n - m + 1) → ℕ // (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ₁ (σ₁ j) = σ₁ j → 1 ≤ g j.succ})
            (b : {g : Fin (n - m + 1) → ℕ // (∑ i, g i = m - 1) ∧ ∀ j : Fin (n - m), foataInv σ₂ (σ₂ j) = σ₂ j → 1 ≤ g j.succ}),
            a.val = b.val → HEq a b := by
          rintro _ _ rfl ⟨a, _⟩ ⟨b, _⟩ hab; subst hab; rfl
        exact haux hσ_eq _ _ hg_eq }

private lemma card_avoids_eq (n : ℕ) (_hn : 1 ≤ n) (asc : Bool) :
    Nat.card {π : Equiv.Perm (Fin n) // AvoidsArrow asc π} =
      derangementCount n +
        ∑ m ∈ Finset.Icc 1 n, ∑ k ∈ Finset.range (n - m + 1),
          Nat.choose (n - m) k * Nat.choose (m + k - 1) (n - m) * derangementCount k := by
  classical
  -- Split into `foataFPSet π = ∅` and `(foataFPSet π).Nonempty`
  let eSplit : {π : Equiv.Perm (Fin n) // AvoidsArrow asc π} ≃
      {π : Equiv.Perm (Fin n) // foataFPSet π = ∅} ⊕
      Σ m : Finset.Icc 1 n,
        {π : Equiv.Perm (Fin n) //
          AvoidsArrow asc π ∧
          ∃ h : (foataFPSet π).Nonempty, (foataFPSet π).max' h = ⟨m.val - 1, by
            have := Finset.mem_Icc.mp m.prop; omega⟩} :=
    { toFun := fun ⟨π, hav⟩ =>
        if h : foataFPSet π = ∅ then Sum.inl ⟨π, h⟩
        else
          have hne : (foataFPSet π).Nonempty := Finset.nonempty_iff_ne_empty.mpr h
          let x := (foataFPSet π).max' hne
          Sum.inr ⟨⟨x.val + 1, Finset.mem_Icc.mpr ⟨by omega, x.isLt⟩⟩,
            ⟨π, hav, hne, Fin.ext (by simp [x])⟩⟩
      invFun := fun s => match s with
        | Sum.inl ⟨π, hemp⟩ => ⟨π, fun _ _ x₃ _ _ _ hfix => by
            have hmem : x₃ ∈ foataFPSet π := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfix⟩
            rw [hemp] at hmem; exact Finset.notMem_empty _ hmem⟩
        | Sum.inr ⟨_, ⟨π, hav, _⟩⟩ => ⟨π, hav⟩
      left_inv := fun ⟨π, hav⟩ => by
        by_cases h : foataFPSet π = ∅ <;> simp [h]
      right_inv := fun s => match s with
        | Sum.inl ⟨π, hemp⟩ => by simp [hemp]
        | Sum.inr ⟨⟨m, hm⟩, ⟨π, hav, hne, hmax⟩⟩ => by
          have hne' : foataFPSet π ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hne
          simp only [hne', ↓reduceDIte, Sum.inr.injEq]
          have hm1 := (Finset.mem_Icc.mp hm).1
          have hmeq : (⟨((foataFPSet π).max' hne).val + 1,
              Finset.mem_Icc.mpr ⟨by omega, ((foataFPSet π).max' hne).isLt⟩⟩ : Finset.Icc 1 n) = ⟨m, hm⟩ := by
            ext; dsimp only; rw [hmax]; dsimp only; omega
          refine Sigma.ext hmeq ?_
          have haux : ∀ {m₁ m₂ : Finset.Icc 1 n} (h : m₁ = m₂)
              (a : {π : Equiv.Perm (Fin n) // AvoidsArrow asc π ∧ ∃ h : (foataFPSet π).Nonempty, (foataFPSet π).max' h = ⟨m₁.val - 1, by have := Finset.mem_Icc.mp m₁.prop; omega⟩})
              (b : {π : Equiv.Perm (Fin n) // AvoidsArrow asc π ∧ ∃ h : (foataFPSet π).Nonempty, (foataFPSet π).max' h = ⟨m₂.val - 1, by have := Finset.mem_Icc.mp m₂.prop; omega⟩}),
              a.val = b.val → HEq a b := by
            rintro _ _ rfl ⟨a, _⟩ ⟨b, _⟩ hab; subst hab; rfl
          exact haux hmeq _ _ rfl }
  rw [Nat.card_congr eSplit, Nat.card_sum, Nat.card_eq_fintype_card, card_foataFP_empty, Nat.card_sigma]
  congr 1
  rw [Finset.univ_eq_attach, ← Finset.sum_attach (Finset.Icc 1 n)
    (fun m => ∑ k ∈ Finset.range (n - m + 1),
      Nat.choose (n - m) k * Nat.choose (m + k - 1) (n - m) * derangementCount k)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hm := Finset.mem_Icc.mp m.prop
  exact card_avoids_fixed_max n m.val hm.1 hm.2 asc

theorem main_proof : type_of% @OMA.S_arxiv_2609_29392.main := by
  intro n hn
  constructor
  · have e1 : {π : Equiv.Perm (Fin n) // ¬ ContainsArrow12_33 π} ≃
        {π : Equiv.Perm (Fin n) // AvoidsArrow false π} :=
      Equiv.subtypeEquivRight fun π => (avoids_false_iff π).symm
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e1]
    exact card_avoids_eq n hn false
  · have e2 : {π : Equiv.Perm (Fin n) // ¬ ContainsArrow21_33 π} ≃
        {π : Equiv.Perm (Fin n) // AvoidsArrow true π} :=
      Equiv.subtypeEquivRight fun π => (avoids_true_iff π).symm
    rw [← Nat.card_eq_fintype_card, Nat.card_congr e2]
    exact card_avoids_eq n hn true

end OMA.P_arxiv_2609_29392

theorem OMA.solution : type_of% @OMA.S_arxiv_2609_29392.main :=
  OMA.P_arxiv_2609_29392.main_proof
