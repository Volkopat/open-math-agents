import FormalConjectures.ErdosProblems.«1190»

open ZMod Finset Function

-- Problem: Erdős Problem 1190 — lt one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1190.lean:72 (declaration Erdos1190.erdos_1190.variants.lt_one)
-- Credit: @LordMike (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA

open Finset

/-- Every fibre of the reduction map `ZMod L → ZMod n` has `L / n` elements. -/
lemma card_fiber (L n : ℕ) [NeZero L] (h : n ∣ L) (c : ZMod n) :
    (univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = c)).card * n = L := by
  classical
  haveI : NeZero n := ⟨fun h0 => NeZero.ne L (by subst h0; simpa using h)⟩
  have key : ∀ b : ZMod n,
      (univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = b)).card
        = (univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = 0)).card := by
    intro b
    obtain ⟨x0, hx0⟩ := castHom_surjective h b
    symm
    refine card_equiv (Equiv.addRight x0) ?_
    intro x
    simp only [mem_filter, mem_univ, true_and, Equiv.coe_addRight]
    rw [← castHom_apply (h := h), ← castHom_apply (h := h), map_add, hx0]
    constructor
    · intro hx; rw [hx, zero_add]
    · intro hx; exact add_eq_right.mp hx
  have h1 := card_eq_sum_card_fiberwise
    (f := fun x : ZMod L => (ZMod.cast x : ZMod n)) (s := univ) (t := univ) (by simp)
  rw [sum_congr rfl (fun b _ => key b)] at h1
  rw [key c]
  simpa [ZMod.card, mul_comm] using h1.symm

/-- A character sum over a shift-invariant set vanishes. -/
lemma shift_sum (L N : ℕ) [NeZero L] [NeZero N] (h : N ∣ L) (A : Finset (ZMod L)) (d : ZMod L)
    (hd : (ZMod.cast d : ZMod N) ≠ 0) (hA : ∀ x, x ∈ A ↔ x + d ∈ A) :
    ∑ x ∈ A, (stdAddChar (ZMod.cast x : ZMod N) : ℂ) = 0 := by
  have e : ∑ x ∈ A, (stdAddChar (ZMod.cast x : ZMod N) : ℂ)
      = ∑ x ∈ A, (stdAddChar (ZMod.cast (x + d) : ZMod N) : ℂ) :=
    (sum_equiv (Equiv.addRight d) (by intro x; simpa using hA x) (by intro x _; simp)).symm
  have e2 : ∀ x : ZMod L, (stdAddChar (ZMod.cast (x + d) : ZMod N) : ℂ)
      = stdAddChar (ZMod.cast x : ZMod N) * stdAddChar (ZMod.cast d : ZMod N) := by
    intro x
    rw [← castHom_apply (h := h), map_add, AddChar.map_add_eq_mul, castHom_apply,
      castHom_apply]
  rw [sum_congr rfl (fun x _ => e2 x), ← sum_mul] at e
  have hne : (stdAddChar (ZMod.cast d : ZMod N) : ℂ) ≠ 1 := by
    intro h1
    rw [← (stdAddChar (N := N)).map_zero_eq_one] at h1
    exact hd (injective_stdAddChar h1)
  have : (∑ x ∈ A, (stdAddChar (ZMod.cast x : ZMod N) : ℂ))
      * (1 - stdAddChar (ZMod.cast d : ZMod N)) = 0 := by
    rw [mul_sub, mul_one, ← e, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hne

end OMA

theorem OMA.solution : type_of% @Erdos1190.erdos_1190.variants.lt_one := by
  classical
  intro m hm S a hS hdisj
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  set L : ℕ := ∏ n ∈ S, n with hL
  have hpos : ∀ n ∈ S, 2 ≤ n := fun n hn => by have := hS n hn; omega
  have hL0 : L ≠ 0 := prod_ne_zero_iff.mpr (fun n hn => by have := hpos n hn; omega)
  haveI : NeZero L := ⟨hL0⟩
  have hdvd : ∀ n ∈ S, n ∣ L := fun n hn => dvd_prod_of_mem _ hn
  let C : ℕ → Finset (ZMod L) := fun n =>
    Finset.univ.filter (fun x : ZMod L => (ZMod.cast x : ZMod n) = (a n : ZMod n))
  have hcard : ∀ n ∈ S, (C n).card * n = L := fun n hn => OMA.card_fiber L n (hdvd n hn) _
  have hpd : (S : Set ℕ).PairwiseDisjoint C := by
    intro n hn n' hn' hnn
    rw [onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    refine hdisj n hn n' hn' hnn ⟨(ZMod.cast x : ℤ), ?_, ?_⟩
    · rw [← intCast_eq_intCast_iff, intCast_cast]; exact hx
    · rw [← intCast_eq_intCast_iff, intCast_cast]; exact hx'
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have hsum : (∑ n ∈ S, (n : ℝ)⁻¹) = ((S.biUnion C).card : ℝ) / L := by
    rw [card_biUnion hpd, Nat.cast_sum, sum_div]
    refine sum_congr rfl (fun n hn => ?_)
    have hn0 : (n : ℝ) ≠ 0 := by have := hpos n hn; positivity
    have := hcard n hn
    have h2 : ((C n).card : ℝ) * n = L := by exact_mod_cast this
    rw [eq_div_iff hLR.ne', ← h2]; field_simp
  rw [hsum, div_lt_one hLR]
  suffices hU : S.biUnion C ≠ Finset.univ by
    have : (S.biUnion C).card < (Finset.univ : Finset (ZMod L)).card :=
      Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hU)
    rw [Finset.card_univ, ZMod.card] at this
    exact_mod_cast this
  intro hU
  set N : ℕ := S.max' hne with hN
  have hNS : N ∈ S := max'_mem S hne
  have hN2 : 2 ≤ N := hpos N hNS
  haveI : NeZero N := ⟨by omega⟩
  have hNL : N ∣ L := hdvd N hNS
  -- the sum of the character over everything vanishes
  have htot : ∑ x : ZMod L, (stdAddChar (ZMod.cast x : ZMod N) : ℂ) = 0 := by
    refine OMA.shift_sum L N hNL Finset.univ 1 ?_ (by simp)
    rw [← castHom_apply (h := hNL), map_one]
    intro h1
    have := (natCast_eq_zero_iff 1 N).mp (by simpa using h1)
    have := Nat.le_of_dvd one_pos this
    omega
  -- the sum over each class with modulus different from `N` vanishes
  have hother : ∀ n ∈ S, n ≠ N →
      ∑ x ∈ C n, (stdAddChar (ZMod.cast x : ZMod N) : ℂ) = 0 := by
    intro n hn hnN
    have hnle : n ≤ N := le_max' S n hn
    have hn2 := hpos n hn
    refine OMA.shift_sum L N hNL (C n) (n : ZMod L) ?_ ?_
    · rw [← castHom_apply (h := hNL), map_natCast]
      intro h1
      have := Nat.le_of_dvd (by omega) ((natCast_eq_zero_iff n N).mp h1)
      omega
    · intro x
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← castHom_apply (h := hdvd n hn), ← castHom_apply (h := hdvd n hn), map_add,
        map_natCast, natCast_self, add_zero]
  -- the sum over the class with modulus `N`
  have hmain : ∑ x ∈ C N, (stdAddChar (ZMod.cast x : ZMod N) : ℂ)
      = ((C N).card : ℂ) * stdAddChar ((a N : ZMod N)) := by
    rw [sum_congr rfl (g := fun _ => (stdAddChar ((a N : ZMod N)) : ℂ))]
    · rw [sum_const, nsmul_eq_mul]
    · intro x hx
      simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      rw [hx]
  have hsplit : ∑ x : ZMod L, (stdAddChar (ZMod.cast x : ZMod N) : ℂ)
      = ∑ n ∈ S, ∑ x ∈ C n, (stdAddChar (ZMod.cast x : ZMod N) : ℂ) := by
    rw [← hU, sum_biUnion hpd]
  rw [sum_eq_single_of_mem N hNS (fun n hn hnN => hother n hn hnN), hmain] at hsplit
  rw [htot] at hsplit
  rcases mul_eq_zero.mp hsplit.symm with h0 | h0
  · have hc : (C N).card = 0 := by exact_mod_cast h0
    have := hcard N hNS
    rw [hc, zero_mul] at this
    exact hL0 this.symm
  · have h1 : (stdAddChar ((a N : ZMod N)) : ℂ) * stdAddChar (-(a N : ZMod N)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1

