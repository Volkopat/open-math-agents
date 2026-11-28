import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2
import Mathlib

/-!
# Proof of Erdos64.erdos_64.R1.H1.R1.H1.R1.H2.R2.H1.R1.H2.R1.H2.R2.H2

Commuting two-coset case for finite odd-order groups: given a finite group A of odd order,
a normal subgroup N, elements s ∈ N \ {1} and t ∉ N such that r := t⁻¹ * s * t commutes with s,
the bipartite Schreier/bi-Cayley graph on Bool × A with shifts {1, s, t} contains a cycle of
length 8 or 16.

Proof by exhaustive case split on the small relations between s and r = t⁻¹ * s * t:
- Since |A| is odd, every element has odd order, so s² ≠ 1, r ≠ 1, t² ∉ N, and s * r ≠ 1
  (as t⁻¹ * s * t = s⁻¹ is impossible when t has odd order).
- Case 1 (r = s, s³ = 1): explicit 8-cycle inside the two cosets N and tN.
- Case 2 (r = s, s³ ≠ 1): explicit 16-cycle inside the three disjoint cosets N, tN, t²N
  using the distinct powers 1, s, s², s³.
- Case 3 (r = s²): explicit 8-cycle inside N and tN.
- Case 4 (s² * r = 1): explicit 8-cycle inside N and tN.
- Case 5 (all remaining cases): the 12 elements s^x * r^y (x ∈ Fin 3, y ∈ Fin 2) in N and tN
  are pairwise distinct and span an explicit 16-cycle.
-/

namespace Erdos64CommutingTwoCoset

open SimpleGraph

private lemma cycle_of_verts {A : Type} [Group A] (s t : A) (u : ℕ)
    (v : Fin (u + 2) → Bool × A)
    (hinj : Function.Injective v)
    (hadj : ∀ i : Fin (u + 2),
      ((v i).1 = false ∧ (v (i + 1)).1 = true ∧
        ((v (i + 1)).2 = (v i).2 ∨ (v (i + 1)).2 = s * (v i).2 ∨ (v (i + 1)).2 = t * (v i).2)) ∨
      ((v (i + 1)).1 = false ∧ (v i).1 = true ∧
        ((v i).2 = (v (i + 1)).2 ∨ (v i).2 = s * (v (i + 1)).2 ∨ (v i).2 = t * (v (i + 1)).2))) :
    cycleGraph (u + 2) ⊑ SimpleGraph.fromRel (fun x w : Bool × A =>
      x.1 = false ∧ w.1 = true ∧ (w.2 = x.2 ∨ w.2 = s * x.2 ∨ w.2 = t * x.2)) := by
  let G := SimpleGraph.fromRel (fun x w : Bool × A =>
    x.1 = false ∧ w.1 = true ∧ (w.2 = x.2 ∨ w.2 = s * x.2 ∨ w.2 = t * x.2))
  have next (i : Fin (u + 2)) : G.Adj (v i) (v (i + 1)) := by
    apply (SimpleGraph.fromRel_adj ..).mpr
    rcases hadj i with h | h
    · refine ⟨fun e => Bool.false_ne_true (h.1.symm.trans ((congrArg Prod.fst e).trans h.2.1)),
        Or.inl h⟩
    · refine ⟨fun e => Bool.false_ne_true (h.1.symm.trans ((congrArg Prod.fst e.symm).trans h.2.1)),
        Or.inr h⟩
  apply isContained_iff_exists_le_comap.mpr
  refine ⟨⟨v, hinj⟩, ?_⟩
  intro i j h
  change G.Adj (v i) (v j)
  rcases cycleGraph_adj.mp h with h | h
  · have eq : i = j + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [eq] using (next j).symm
  · have eq : j = i + 1 := by simpa [add_comm] using sub_eq_iff_eq_add.mp h
    simpa only [eq] using next i

private lemma odd_sq_eq_one {A : Type} [Group A] [Fintype A]
    (hodd : Odd (Nat.card A)) {g : A} (hg : g ^ 2 = 1) : g = 1 := by
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one hg
  have hpos : 0 < orderOf g := orderOf_pos g
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by decide) hdvd
  have hne2 : orderOf g ≠ 2 := by
    intro h2
    have hcard : 2 ∣ Nat.card A := h2 ▸ orderOf_dvd_natCard g
    obtain ⟨m, hm⟩ := hodd
    omega
  exact orderOf_eq_one_iff.mp (by omega)

private lemma odd_conj_ne_inv {A : Type} [Group A] [Fintype A]
    (hodd : Odd (Nat.card A)) {s t : A} (hs : s ≠ 1) :
    s * (t⁻¹ * s * t) ≠ 1 := by
  intro hsr
  have hinv : t⁻¹ * s * t = s⁻¹ := eq_inv_of_mul_eq_one_right hsr
  have heven : ∀ k : ℕ, (t ^ (2 * k))⁻¹ * s * (t ^ (2 * k)) = s := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : t ^ (2 * (k + 1)) = t ^ (2 * k) * t * t := by
        rw [Nat.mul_succ, pow_add, pow_two, mul_assoc]
      rw [h1]
      have h2 : (t ^ (2 * k) * t * t)⁻¹ * s * (t ^ (2 * k) * t * t) =
          t⁻¹ * (t⁻¹ * ((t ^ (2 * k))⁻¹ * s * t ^ (2 * k)) * t) * t := by group
      rw [h2, ih, hinv]
      have h3 : t⁻¹ * s⁻¹ * t = (t⁻¹ * s * t)⁻¹ := by group
      rw [h3, hinv, inv_inv]
  have hord_odd : Odd (orderOf t) := by
    have hdvd : orderOf t ∣ Nat.card A := orderOf_dvd_natCard t
    obtain ⟨m, hm⟩ := hdvd
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    obtain ⟨q, hq⟩ := hnot
    obtain ⟨p, hp⟩ := hodd
    have : Nat.card A = 2 * (q * m) := by rw [hm, hq]; ring
    omega
  obtain ⟨k, hk⟩ := hord_odd
  have htpow : t ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one t
  have hstep : s = s⁻¹ := by
    calc s = (t ^ (2 * k + 1))⁻¹ * s * t ^ (2 * k + 1) := by rw [htpow]; group
      _ = t⁻¹ * ((t ^ (2 * k))⁻¹ * s * t ^ (2 * k)) * t := by rw [pow_succ]; group
      _ = t⁻¹ * s * t := by rw [heven k]
      _ = s⁻¹ := hinv
  have hs2 : s ^ 2 = 1 := by rw [sq, mul_eq_one_iff_eq_inv]; exact hstep
  exact hs (odd_sq_eq_one hodd hs2)

private lemma odd_sq_not_mem {A : Type} [Group A] [Fintype A]
    (hodd : Odd (Nat.card A)) (N : Subgroup A) {t : A} (ht : t ∉ N) :
    t ^ 2 ∉ N := by
  intro ht2
  have hord_odd : Odd (orderOf t) := by
    have hdvd : orderOf t ∣ Nat.card A := orderOf_dvd_natCard t
    obtain ⟨m, hm⟩ := hdvd
    by_contra hnot
    rw [Nat.not_odd_iff_even] at hnot
    obtain ⟨q, hq⟩ := hnot
    obtain ⟨p, hp⟩ := hodd
    have : Nat.card A = 2 * (q * m) := by rw [hm, hq]; ring
    omega
  obtain ⟨k, hk⟩ := hord_odd
  have htpow : t ^ (2 * k + 1) = 1 := hk ▸ pow_orderOf_eq_one t
  have h2k : t ^ (2 * k) ∈ N := by
    rw [pow_mul]
    exact N.pow_mem ht2 k
  have h1 : t ^ (2 * k + 1) ∈ N := htpow.symm ▸ N.one_mem
  have ht_eq : t = (t ^ (2 * k))⁻¹ * t ^ (2 * k + 1) := by rw [pow_succ]; group
  exact ht (ht_eq ▸ N.mul_mem (N.inv_mem h2k) h1)

private lemma case_eq_ord3 {A : Type} [Group A] (s t : A) (N : Subgroup A)
    (hsN : s ∈ N) (htN : t ∉ N) (hs1 : s ≠ 1) (hs2 : s ^ 2 ≠ 1)
    (hs3 : s ^ 3 = 1) (hst : s * t = t * s) :
    cycleGraph 8 ⊑ SimpleGraph.fromRel (fun u w : Bool × A =>
      u.1 = false ∧ w.1 = true ∧ (w.2 = u.2 ∨ w.2 = s * u.2 ∨ w.2 = t * u.2)) := by
  let trace : Fin 8 → Bool × Bool × Fin 3 :=
    ![(false, false, 0), (true, false, 0), (false, false, 2), (true, false, 2),
      (false, false, 1), (true, true, 1), (false, true, 0), (true, true, 0)]
  let lift (p : Bool × Bool × Fin 3) : Bool × A :=
    (p.1, if p.2.1 then t * s ^ p.2.2.val else s ^ p.2.2.val)
  have htrace_inj : Function.Injective trace := by
    intro i j h; revert i j h; decide
  have hlift_inj : Function.Injective lift := by
    rintro ⟨b1, c1, j1⟩ ⟨b2, c2, j2⟩ h
    have hb : b1 = b2 := congrArg Prod.fst h
    have hg : (if c1 then t * s ^ j1.val else s ^ j1.val) =
        (if c2 then t * s ^ j2.val else s ^ j2.val) := congrArg Prod.snd h
    have hdisj : ∀ (a b : Fin 3), t * s ^ a.val ≠ s ^ b.val := by
      intro a b heq
      have hmem : t * s ^ a.val * (s ^ a.val)⁻¹ ∈ N :=
        heq ▸ N.mul_mem (N.pow_mem hsN b.val) (N.inv_mem (N.pow_mem hsN a.val))
      exact htN (by simpa [mul_assoc] using hmem)
    have hcj : c1 = c2 ∧ s ^ j1.val = s ^ j2.val := by
      cases c1 <;> cases c2 <;> simp at hg
      · exact ⟨rfl, hg⟩
      · exact absurd hg.symm (hdisj j2 j1)
      · exact absurd hg (hdisj j1 j2)
      · exact ⟨rfl, hg⟩
    have hj : j1 = j2 := by
      have heq := hcj.2
      fin_cases j1 <;> fin_cases j2
      all_goals try rfl
      all_goals simp only [pow_zero, pow_one] at heq
      · exact absurd heq.symm hs1
      · exact absurd heq.symm hs2
      · exact absurd heq hs1
      · exact absurd (mul_left_cancel (show s * 1 = s * s by simpa [sq] using heq)).symm hs1
      · exact absurd heq hs2
      · exact absurd (mul_left_cancel (show s * s = s * 1 by simpa [sq] using heq)) hs1
    exact Prod.ext hb (Prod.ext hcj.1 hj)
  apply cycle_of_verts s t 6 (lift ∘ trace) (hlift_inj.comp htrace_inj)
  intro i
  fin_cases i
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace]; rw [← pow_succ', hs3]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, sq]))⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, hst]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩

private lemma case_eq_ord_ge5 {A : Type} [Group A] (s t : A) (N : Subgroup A)
    (hsN : s ∈ N) (htN : t ∉ N) (ht2N : t ^ 2 ∉ N)
    (hs1 : s ≠ 1) (hs2 : s ^ 2 ≠ 1) (hs3 : s ^ 3 ≠ 1) (hst : s * t = t * s) :
    cycleGraph 16 ⊑ SimpleGraph.fromRel (fun u w : Bool × A =>
      u.1 = false ∧ w.1 = true ∧ (w.2 = u.2 ∨ w.2 = s * u.2 ∨ w.2 = t * u.2)) := by
  let trace : Fin 16 → Bool × Fin 3 × Fin 4 :=
    ![(false, 0, 0), (true, 0, 1), (false, 0, 1), (true, 0, 2),
      (false, 0, 2), (true, 0, 3), (false, 0, 3), (true, 1, 3),
      (false, 1, 2), (true, 1, 2), (false, 1, 1), (true, 2, 1),
      (false, 2, 0), (true, 2, 0), (false, 1, 0), (true, 1, 0)]
  let lift (p : Bool × Fin 3 × Fin 4) : Bool × A :=
    (p.1, t ^ p.2.1.val * s ^ p.2.2.val)
  have htrace_inj : Function.Injective trace := by
    intro i j h; revert i j h; decide
  have hlift_inj : Function.Injective lift := by
    rintro ⟨b1, i1, j1⟩ ⟨b2, i2, j2⟩ h
    have hb : b1 = b2 := congrArg Prod.fst h
    have hg : t ^ i1.val * s ^ j1.val = t ^ i2.val * s ^ j2.val := congrArg Prod.snd h
    have hdisj : ∀ (k : ℕ), t ^ k ∉ N → ∀ (a b : Fin 4), t ^ k * s ^ a.val ≠ s ^ b.val := by
      intro k hk a b heq
      have hmem : t ^ k * s ^ a.val * (s ^ a.val)⁻¹ ∈ N :=
        heq ▸ N.mul_mem (N.pow_mem hsN b.val) (N.inv_mem (N.pow_mem hsN a.val))
      exact hk (by simpa [mul_assoc] using hmem)
    have hi : i1 = i2 := by
      fin_cases i1 <;> fin_cases i2
      all_goals try rfl
      all_goals simp only [pow_zero, one_mul, pow_one] at hg
      · exact absurd hg.symm (by simpa using hdisj 1 (by simpa using htN) j2 j1)
      · exact absurd hg.symm (hdisj 2 ht2N j2 j1)
      · exact absurd hg (by simpa using hdisj 1 (by simpa using htN) j1 j2)
      · exact absurd (mul_left_cancel (show t * s ^ j1.val = t * (t * s ^ j2.val) by
          simpa [sq, mul_assoc] using hg)).symm (by simpa using hdisj 1 (by simpa using htN) j2 j1)
      · exact absurd hg (hdisj 2 ht2N j1 j2)
      · exact absurd (mul_left_cancel (show t * (t * s ^ j1.val) = t * s ^ j2.val by
          simpa [sq, mul_assoc] using hg)) (by simpa using hdisj 1 (by simpa using htN) j1 j2)
    subst hi
    have hs_eq : s ^ j1.val = s ^ j2.val := mul_left_cancel hg
    have hj : j1 = j2 := by
      have hpow_ne : ∀ a b : Fin 4, a.val < b.val → s ^ a.val ≠ s ^ b.val := by
        intro a b hlt heq
        have hd : s ^ (b.val - a.val) = 1 := by
          have : s ^ a.val * 1 = s ^ a.val * s ^ (b.val - a.val) := by
            rw [mul_one, ← pow_add, Nat.add_sub_of_le (le_of_lt hlt), heq]
          exact (mul_left_cancel this).symm
        have hba : b.val - a.val = 1 ∨ b.val - a.val = 2 ∨ b.val - a.val = 3 := by omega
        rcases hba with h1 | h2 | h3
        · exact hs1 (by simpa [h1] using hd)
        · exact hs2 (by simpa [h2] using hd)
        · exact hs3 (by simpa [h3] using hd)
      rcases lt_trichotomy j1.val j2.val with hlt | heqv | hgt
      · exact absurd hs_eq (hpow_ne j1 j2 hlt)
      · exact Fin.ext heqv
      · exact absurd hs_eq.symm (hpow_ne j2 j1 hgt)
    exact Prod.ext hb (Prod.ext rfl hj)
  have hst2 : s * t ^ 2 = t ^ 2 * s := by
    rw [sq, ← mul_assoc, hst, mul_assoc, hst, ← mul_assoc]
  apply cycle_of_verts s t 14 (lift ∘ trace) (hlift_inj.comp htrace_inj)
  intro i
  fin_cases i
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, sq]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, pow_succ']))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by
      simp [lift, trace]
      rw [← mul_assoc, hst, mul_assoc, ← pow_succ']))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by
      simp [lift, trace]
      rw [← mul_assoc, hst, mul_assoc, sq]))⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace, sq, mul_assoc]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, hst2]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace, sq]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩

private lemma case_sq {A : Type} [Group A] (s t : A) (N : Subgroup A)
    (hsN : s ∈ N) (htN : t ∉ N) (hs1 : s ≠ 1) (hs2 : s ^ 2 ≠ 1)
    (hst : s * t = t * s ^ 2) :
    cycleGraph 8 ⊑ SimpleGraph.fromRel (fun u w : Bool × A =>
      u.1 = false ∧ w.1 = true ∧ (w.2 = u.2 ∨ w.2 = s * u.2 ∨ w.2 = t * u.2)) := by
  let trace : Fin 8 → Bool × Bool × Fin 3 :=
    ![(false, false, 0), (true, false, 1), (false, false, 1), (true, false, 2),
      (false, false, 2), (true, true, 2), (false, true, 0), (true, true, 0)]
  let lift (p : Bool × Bool × Fin 3) : Bool × A :=
    (p.1, if p.2.1 then t * s ^ p.2.2.val else s ^ p.2.2.val)
  have htrace_inj : Function.Injective trace := by
    intro i j h; revert i j h; decide
  have hlift_inj : Function.Injective lift := by
    rintro ⟨b1, c1, j1⟩ ⟨b2, c2, j2⟩ h
    have hb : b1 = b2 := congrArg Prod.fst h
    have hg : (if c1 then t * s ^ j1.val else s ^ j1.val) =
        (if c2 then t * s ^ j2.val else s ^ j2.val) := congrArg Prod.snd h
    have hdisj : ∀ (a b : Fin 3), t * s ^ a.val ≠ s ^ b.val := by
      intro a b heq
      have hmem : t * s ^ a.val * (s ^ a.val)⁻¹ ∈ N :=
        heq ▸ N.mul_mem (N.pow_mem hsN b.val) (N.inv_mem (N.pow_mem hsN a.val))
      exact htN (by simpa [mul_assoc] using hmem)
    have hcj : c1 = c2 ∧ s ^ j1.val = s ^ j2.val := by
      cases c1 <;> cases c2 <;> simp at hg
      · exact ⟨rfl, hg⟩
      · exact absurd hg.symm (hdisj j2 j1)
      · exact absurd hg (hdisj j1 j2)
      · exact ⟨rfl, hg⟩
    have hj : j1 = j2 := by
      have heq := hcj.2
      fin_cases j1 <;> fin_cases j2
      all_goals try rfl
      all_goals simp only [pow_zero, pow_one] at heq
      · exact absurd heq.symm hs1
      · exact absurd heq.symm hs2
      · exact absurd heq hs1
      · exact absurd (mul_left_cancel (show s * 1 = s * s by simpa [sq] using heq)).symm hs1
      · exact absurd heq hs2
      · exact absurd (mul_left_cancel (show s * s = s * 1 by simpa [sq] using heq)) hs1
    exact Prod.ext hb (Prod.ext hcj.1 hj)
  apply cycle_of_verts s t 6 (lift ∘ trace) (hlift_inj.comp htrace_inj)
  intro i
  fin_cases i
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, sq]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, hst]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩

private lemma case_inv_sq {A : Type} [Group A] (s t : A) (N : Subgroup A)
    (hsN : s ∈ N) (htN : t ∉ N) (hs1 : s ≠ 1) (hs2 : s ^ 2 ≠ 1)
    (hst : s * (t * s ^ 2) = t) :
    cycleGraph 8 ⊑ SimpleGraph.fromRel (fun u w : Bool × A =>
      u.1 = false ∧ w.1 = true ∧ (w.2 = u.2 ∨ w.2 = s * u.2 ∨ w.2 = t * u.2)) := by
  let trace : Fin 8 → Bool × Bool × Fin 3 :=
    ![(false, false, 2), (true, true, 2), (false, true, 2), (true, true, 0),
      (false, false, 0), (true, false, 1), (false, false, 1), (true, false, 2)]
  let lift (p : Bool × Bool × Fin 3) : Bool × A :=
    (p.1, if p.2.1 then t * s ^ p.2.2.val else s ^ p.2.2.val)
  have htrace_inj : Function.Injective trace := by
    intro i j h; revert i j h; decide
  have hlift_inj : Function.Injective lift := by
    rintro ⟨b1, c1, j1⟩ ⟨b2, c2, j2⟩ h
    have hb : b1 = b2 := congrArg Prod.fst h
    have hg : (if c1 then t * s ^ j1.val else s ^ j1.val) =
        (if c2 then t * s ^ j2.val else s ^ j2.val) := congrArg Prod.snd h
    have hdisj : ∀ (a b : Fin 3), t * s ^ a.val ≠ s ^ b.val := by
      intro a b heq
      have hmem : t * s ^ a.val * (s ^ a.val)⁻¹ ∈ N :=
        heq ▸ N.mul_mem (N.pow_mem hsN b.val) (N.inv_mem (N.pow_mem hsN a.val))
      exact htN (by simpa [mul_assoc] using hmem)
    have hcj : c1 = c2 ∧ s ^ j1.val = s ^ j2.val := by
      cases c1 <;> cases c2 <;> simp at hg
      · exact ⟨rfl, hg⟩
      · exact absurd hg.symm (hdisj j2 j1)
      · exact absurd hg (hdisj j1 j2)
      · exact ⟨rfl, hg⟩
    have hj : j1 = j2 := by
      have heq := hcj.2
      fin_cases j1 <;> fin_cases j2
      all_goals try rfl
      all_goals simp only [pow_zero, pow_one] at heq
      · exact absurd heq.symm hs1
      · exact absurd heq.symm hs2
      · exact absurd heq hs1
      · exact absurd (mul_left_cancel (show s * 1 = s * s by simpa [sq] using heq)).symm hs1
      · exact absurd heq hs2
      · exact absurd (mul_left_cancel (show s * s = s * 1 by simpa [sq] using heq)) hs1
    exact Prod.ext hb (Prod.ext hcj.1 hj)
  apply cycle_of_verts s t 6 (lift ∘ trace) (hlift_inj.comp htrace_inj)
  intro i
  fin_cases i
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, hst]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace]))⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, sq]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace])⟩

private lemma case_generic {A : Type} [Group A] (s t r : A) (N : Subgroup A)
    (hsN : s ∈ N) (hrN : r ∈ N) (htN : t ∉ N)
    (hst : s * t = t * r) (hcomm : Commute r s)
    (hs1 : s ≠ 1) (hs2 : s ^ 2 ≠ 1) (hr1 : r ≠ 1)
    (hsr : s * r ≠ 1) (hneq : r ≠ s) (hnsq : r ≠ s ^ 2) (hnisq : s ^ 2 * r ≠ 1) :
    cycleGraph 16 ⊑ SimpleGraph.fromRel (fun u w : Bool × A =>
      u.1 = false ∧ w.1 = true ∧ (w.2 = u.2 ∨ w.2 = s * u.2 ∨ w.2 = t * u.2)) := by
  let trace : Fin 16 → Bool × Bool × Fin 3 × Fin 2 :=
    ![(false, false, 0, 0), (true, false, 1, 0), (false, false, 1, 0), (true, false, 2, 0),
      (false, false, 2, 0), (true, true, 2, 0), (false, true, 2, 0), (true, true, 2, 1),
      (false, false, 2, 1), (true, false, 2, 1), (false, false, 1, 1), (true, false, 1, 1),
      (false, false, 0, 1), (true, true, 0, 1), (false, true, 0, 0), (true, true, 0, 0)]
  let val (x : Fin 3) (y : Fin 2) : A := s ^ x.val * r ^ y.val
  let lift (p : Bool × Bool × Fin 3 × Fin 2) : Bool × A :=
    (p.1, if p.2.1 then t * val p.2.2.1 p.2.2.2 else val p.2.2.1 p.2.2.2)
  have htrace_inj : Function.Injective trace := by
    intro i j h; revert i j h; decide
  have hval_mem (x : Fin 3) (y : Fin 2) : val x y ∈ N :=
    N.mul_mem (N.pow_mem hsN x.val) (N.pow_mem hrN y.val)
  have hdisj (x1 x2 : Fin 3) (y1 y2 : Fin 2) : t * val x1 y1 ≠ val x2 y2 := by
    intro heq
    have hmem : t * val x1 y1 * (val x1 y1)⁻¹ ∈ N :=
      heq ▸ N.mul_mem (hval_mem x2 y2) (N.inv_mem (hval_mem x1 y1))
    exact htN (by simpa [mul_assoc] using hmem)
  have hval_inj : ∀ (x1 x2 : Fin 3) (y1 y2 : Fin 2), val x1 y1 = val x2 y2 → x1 = x2 ∧ y1 = y2 := by
    intro x1 x2 y1 y2 heq
    have hcase01 : ∀ (a b : Fin 3), s ^ a.val ≠ s ^ b.val * r := by
      intro a b h
      fin_cases a <;> fin_cases b
      all_goals simp only [pow_zero, pow_one, one_mul] at h
      · exact hr1 h.symm
      · exact hsr h.symm
      · exact hnisq h.symm
      · exact hneq h.symm
      · exact hr1 (mul_left_cancel (show s * 1 = s * r by simpa using h)).symm
      · exact hsr (mul_left_cancel (show s * 1 = s * (s * r) by simpa [sq, mul_assoc] using h)).symm
      · exact hnsq h.symm
      · exact hneq (mul_left_cancel (show s * s = s * r by simpa [sq] using h)).symm
      · exact hr1 (mul_left_cancel (show s ^ 2 * 1 = s ^ 2 * r by simpa using h)).symm
    fin_cases y1 <;> fin_cases y2
    · simp only [val, pow_zero, mul_one] at heq
      refine ⟨?_, rfl⟩
      fin_cases x1 <;> fin_cases x2
      all_goals try rfl
      all_goals simp only [pow_zero, pow_one] at heq
      · exact absurd heq.symm hs1
      · exact absurd heq.symm hs2
      · exact absurd heq hs1
      · exact absurd (mul_left_cancel (show s * 1 = s * s by simpa [sq] using heq)).symm hs1
      · exact absurd heq hs2
      · exact absurd (mul_left_cancel (show s * s = s * 1 by simpa [sq] using heq)) hs1
    · simp only [val, pow_zero, pow_one, mul_one] at heq
      exact absurd heq (hcase01 x1 x2)
    · simp only [val, pow_zero, pow_one, mul_one] at heq
      exact absurd heq.symm (hcase01 x2 x1)
    · simp only [val, pow_one] at heq
      have hxeq : s ^ x1.val = s ^ x2.val := mul_right_cancel heq
      refine ⟨?_, rfl⟩
      fin_cases x1 <;> fin_cases x2
      all_goals try rfl
      all_goals simp only [pow_zero, pow_one] at hxeq
      · exact absurd hxeq.symm hs1
      · exact absurd hxeq.symm hs2
      · exact absurd hxeq hs1
      · exact absurd (mul_left_cancel (show s * 1 = s * s by simpa [sq] using hxeq)).symm hs1
      · exact absurd hxeq hs2
      · exact absurd (mul_left_cancel (show s * s = s * 1 by simpa [sq] using hxeq)) hs1
  have hlift_inj : Function.Injective lift := by
    rintro ⟨b1, c1, x1, y1⟩ ⟨b2, c2, x2, y2⟩ h
    have hb : b1 = b2 := congrArg Prod.fst h
    have hg : (if c1 then t * val x1 y1 else val x1 y1) =
        (if c2 then t * val x2 y2 else val x2 y2) := congrArg Prod.snd h
    have hcval : c1 = c2 ∧ val x1 y1 = val x2 y2 := by
      cases c1 <;> cases c2 <;> simp at hg
      · exact ⟨rfl, hg⟩
      · exact absurd hg.symm (hdisj x2 x1 y2 y1)
      · exact absurd hg (hdisj x1 x2 y1 y2)
      · exact ⟨rfl, hg⟩
    obtain ⟨hx, hy⟩ := hval_inj x1 x2 y1 y2 hcval.2
    exact Prod.ext hb (Prod.ext hcval.1 (Prod.ext hx hy))
  apply cycle_of_verts s t 14 (lift ∘ trace) (hlift_inj.comp htrace_inj)
  intro i
  fin_cases i
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, val]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace, val])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, val, sq]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace, val])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace, val]))⟩
  · right; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace, val])⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inl (by
      simp [lift, trace, val]
      rw [← mul_assoc s, hst, mul_assoc t, (hcomm.pow_right 2).eq]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace, val]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace, val])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, val, sq, mul_assoc]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace, val])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, val]))⟩
  · left; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace, val]))⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inl (by simp [lift, trace, val, hst]))⟩
  · left; refine ⟨rfl, rfl, Or.inl (by simp [lift, trace, val])⟩
  · right; refine ⟨rfl, rfl, Or.inr (Or.inr (by simp [lift, trace, val]))⟩

end Erdos64CommutingTwoCoset

theorem OMA.solution :
    OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2.H2 := by
  intro A _ _ s t hodd hs1 N hN _ hsN htN hcomm
  let r : A := t⁻¹ * s * t
  have hrN : r ∈ N := by simpa [r] using hN.conj_mem s hsN t⁻¹
  have hst : s * t = t * r := by dsimp [r]; group
  have hr1 : r ≠ 1 := by
    intro h
    have : t * r * t⁻¹ = t * 1 * t⁻¹ := congrArg (fun x => t * x * t⁻¹) h
    have hs_eq : s = 1 := by
      have : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
      simpa [r, this] using congrArg (fun x => t * x * t⁻¹) h
    exact hs1 hs_eq
  have hs2 : s ^ 2 ≠ 1 := fun h => hs1 (Erdos64CommutingTwoCoset.odd_sq_eq_one hodd h)
  have hsr : s * r ≠ 1 := Erdos64CommutingTwoCoset.odd_conj_ne_inv hodd hs1
  by_cases hrs : r = s
  · have hst' : s * t = t * s := hrs ▸ hst
    by_cases hs3 : s ^ 3 = 1
    · exact ⟨3, by decide, Erdos64CommutingTwoCoset.case_eq_ord3 s t N hsN htN hs1 hs2 hs3 hst'⟩
    · have ht2N : t ^ 2 ∉ N := Erdos64CommutingTwoCoset.odd_sq_not_mem hodd N htN
      exact ⟨4, by decide,
        Erdos64CommutingTwoCoset.case_eq_ord_ge5 s t N hsN htN ht2N hs1 hs2 hs3 hst'⟩
  · by_cases hrsq : r = s ^ 2
    · exact ⟨3, by decide,
        Erdos64CommutingTwoCoset.case_sq s t N hsN htN hs1 hs2 (hrsq ▸ hst)⟩
    · by_cases hrisq : s ^ 2 * r = 1
      · have hst' : s * (t * s ^ 2) = t := by
          calc s * (t * s ^ 2) = (s * t) * s ^ 2 := by rw [mul_assoc]
            _ = t * r * s ^ 2 := by rw [hst]
            _ = t * (r * s ^ 2) := by rw [mul_assoc]
            _ = t * (s ^ 2 * r) := by rw [(hcomm.pow_right 2).eq]
            _ = t := by rw [hrisq, mul_one]
        exact ⟨3, by decide,
          Erdos64CommutingTwoCoset.case_inv_sq s t N hsN htN hs1 hs2 hst'⟩
      · exact ⟨4, by decide,
          Erdos64CommutingTwoCoset.case_generic s t r N hsN hrN htN hst hcomm
            hs1 hs2 hr1 hsr hrs hrsq hrisq⟩
