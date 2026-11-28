import OMAReductions.R_Green4_large_green_4_R1

/-!
# Density Lower Bound for the Extremal Product-Free Family in `A_n`

We prove `OMA.R_Green4_large_green_4_R1.H1`: for all sufficiently large `n`,
there exist `x : Fin n` and `I : Set (Fin n)` such that the density of
`Green4.extremalFamily x I` inside `alternatingGroup (Fin n)` is at least
`n ^ (-33 / 50)`.

Taking `x = 0` and `I = {1, ..., k}` with `k = ⌊√n / 2⌋`, every permutation
mapping `x` into `I` and `I` disjointly into `Iᶜ` leaves `n - 1 - k ≥ 2`
elements whose images can be permuted freely. Swapping two fixed elements
outside `{x} ∪ I` pairs odd and even permutations bijectively, so the density in
`A_n` equals the density in `S_n`:
`(k / n) * ∏_{j=0}^{k-1} (n - k - j) / (n - 1 - j) ≥ (k / n) * (1 - k / (n - k))^k`.
By Bernoulli's inequality this is at least `(2 / 9) * n ^ (-1 / 2) ≥ n ^ (-33 / 50)`
for all `n ≥ 100000`.
-/

namespace OMA.Green4H1

open Finset Filter
open scoped Classical

private def goodPerms {n : ℕ} (x : Fin n) (I : Finset (Fin n)) : Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p : Equiv.Perm (Fin n) => p x ∈ I ∧ Disjoint (I.image p) I)

private lemma mem_goodPerms_iff {n : ℕ} (x : Fin n) (I : Finset (Fin n))
    (p : Equiv.Perm (Fin n)) :
    p ∈ goodPerms x I ↔
      p x ∈ (I : Set (Fin n)) ∧ Disjoint ((I : Set (Fin n)).image p) (I : Set (Fin n)) := by
  simp only [goodPerms, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_coe,
    ← Finset.coe_image, Finset.disjoint_coe]

private lemma card_even_goodPerms_mul_two {n : ℕ} (x : Fin n) (I : Finset (Fin n))
    (a b : Fin n) (hab : a ≠ b) (hax : a ≠ x) (hbx : b ≠ x) (haI : a ∉ I) (hbI : b ∉ I) :
    2 * ((goodPerms x I).filter (fun p => p ∈ alternatingGroup (Fin n))).card =
      (goodPerms x I).card := by
  let τ : Equiv.Perm (Fin n) := Equiv.swap a b
  have hτ_sign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hab
  have hτ_mul : ∀ p : Equiv.Perm (Fin n), p ∈ goodPerms x I → p * τ ∈ goodPerms x I := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hpx, hdisj⟩
    rw [goodPerms, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [Equiv.Perm.coe_mul, Function.comp_apply, τ,
        Equiv.swap_apply_of_ne_of_ne hax.symm hbx.symm]
      exact hpx
    · have himg : I.image (p * τ) = I.image p := by
        ext y
        simp only [Finset.mem_image, Equiv.Perm.coe_mul, Function.comp_apply]
        constructor
        · rintro ⟨z, hz, rfl⟩
          have hza : z ≠ a := fun h => haI (h ▸ hz)
          have hzb : z ≠ b := fun h => hbI (h ▸ hz)
          exact ⟨z, hz, by simp [τ, Equiv.swap_apply_of_ne_of_ne hza hzb]⟩
        · rintro ⟨z, hz, rfl⟩
          have hza : z ≠ a := fun h => haI (h ▸ hz)
          have hzb : z ≠ b := fun h => hbI (h ▸ hz)
          exact ⟨z, hz, by simp [τ, Equiv.swap_apply_of_ne_of_ne hza hzb]⟩
      rw [himg]
      exact hdisj
  have hbij : ((goodPerms x I).filter (fun p => p ∈ alternatingGroup (Fin n))).card =
      ((goodPerms x I).filter (fun p => p ∉ alternatingGroup (Fin n))).card := by
    refine Finset.card_bij (fun p _ => p * τ) ?_ ?_ ?_
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hgood, heven⟩
      rw [Finset.mem_filter]
      refine ⟨hτ_mul p hgood, ?_⟩
      rw [Equiv.Perm.mem_alternatingGroup] at heven ⊢
      rw [map_mul, heven, hτ_sign, one_mul]
      decide
    · intro p₁ _ p₂ _ heq
      exact mul_right_cancel heq
    · intro σ hσ
      rcases Finset.mem_filter.mp hσ with ⟨hgood, hodd⟩
      refine ⟨σ * τ, ?_, ?_⟩
      · rw [Finset.mem_filter]
        refine ⟨hτ_mul σ hgood, ?_⟩
        rw [Equiv.Perm.mem_alternatingGroup] at hodd ⊢
        rw [map_mul, hτ_sign]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hneg1
        · exact absurd h1 hodd
        · rw [hneg1]; decide
      · rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  have hpart := Finset.card_filter_add_card_filter_not (s := goodPerms x I)
    (fun p => p ∈ alternatingGroup (Fin n))
  omega

private lemma card_goodPerms_eq {n k : ℕ} (hk : 2 * k + 1 ≤ n)
    (x : Fin n) (I : Finset (Fin n)) (hxI : x ∉ I) (hIc : I.card = k) :
    (goodPerms x I).card =
      k * ((n - k).descFactorial k) * (n - 1 - k).factorial := by
  classical
  let S : Finset (Fin n) := insert x I
  have hSc : S.card = k + 1 := by rw [Finset.card_insert_of_notMem hxI, hIc]
  let E : Finset (S ↪ Fin n) := Finset.univ.filter (fun f : S ↪ Fin n =>
    f ⟨x, Finset.mem_insert_self x I⟩ ∈ I ∧
    ∀ z : S, z.1 ∈ I → f z ∉ I)
  have hcard_E : E.card = k * (n - k).descFactorial k := by
    let target := I ×ˢ (Finset.univ : Finset (I ↪ (Iᶜ : Finset (Fin n))))
    have hbij : E.card = target.card := by
      refine Finset.card_bij
        (fun f hf =>
          (f ⟨x, Finset.mem_insert_self x I⟩,
           ⟨fun z => ⟨f ⟨z.1, Finset.mem_insert_of_mem z.2⟩,
              Finset.mem_compl.mpr ((Finset.mem_filter.mp hf).2.2 ⟨z.1, Finset.mem_insert_of_mem z.2⟩ z.2)⟩,
            fun z₁ z₂ h => by
              have h1 : f ⟨z₁.1, Finset.mem_insert_of_mem z₁.2⟩ = f ⟨z₂.1, Finset.mem_insert_of_mem z₂.2⟩ :=
                congrArg Subtype.val h
              have h2 := f.injective h1
              exact Subtype.ext (congrArg (Subtype.val : S → Fin n) h2)⟩))
        ?_ ?_ ?_
      · intro f hf
        rw [Finset.mem_product]
        exact ⟨(Finset.mem_filter.mp hf).2.1, Finset.mem_univ _⟩
      · intro f₁ _ f₂ _ heq
        rcases Prod.mk.inj heq with ⟨hx_eq, hI_eq⟩
        apply DFunLike.ext
        rintro ⟨z, hz⟩
        rcases Finset.mem_insert.mp hz with rfl | hzI
        · exact hx_eq
        · have hstep := congrArg (fun g : I ↪ (Iᶜ : Finset (Fin n)) => (g ⟨z, hzI⟩).1) hI_eq
          exact hstep
      · rintro ⟨y, g⟩ hpair
        rcases Finset.mem_product.mp hpair with ⟨hyI, _⟩
        let ffn : S → Fin n := fun z =>
          if hz : z.1 = x then y else (g ⟨z.1, (Finset.mem_insert.mp z.2).resolve_left hz⟩).1
        have hfinj : Function.Injective ffn := by
          intro z₁ z₂ heq
          dsimp only [ffn] at heq
          by_cases h1 : z₁.1 = x <;> by_cases h2 : z₂.1 = x
          · exact Subtype.ext (h1.trans h2.symm)
          · simp only [dif_pos h1, dif_neg h2] at heq
            have hnot : (g ⟨z₂.1, (Finset.mem_insert.mp z₂.2).resolve_left h2⟩).1 ∉ I :=
              Finset.mem_compl.mp (g _).2
            exact absurd (heq ▸ hyI) hnot
          · simp only [dif_neg h1, dif_pos h2] at heq
            have hnot : (g ⟨z₁.1, (Finset.mem_insert.mp z₁.2).resolve_left h1⟩).1 ∉ I :=
              Finset.mem_compl.mp (g _).2
            exact absurd (heq.symm ▸ hyI) hnot
          · simp only [dif_neg h1, dif_neg h2] at heq
            have hg := g.injective (Subtype.ext heq)
            exact Subtype.ext (congrArg (Subtype.val : I → Fin n) hg)
        refine ⟨⟨ffn, hfinj⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · change ffn ⟨x, Finset.mem_insert_self x I⟩ ∈ I
            simp [ffn, hyI]
          · intro z hzI
            change ffn z ∉ I
            have hzx : z.1 ≠ x := fun h => hxI (h ▸ hzI)
            simp only [ffn, dif_neg hzx]
            exact Finset.mem_compl.mp (g _).2
        · apply Prod.ext
          · change ffn ⟨x, Finset.mem_insert_self x I⟩ = y
            simp [ffn]
          · apply DFunLike.ext
            rintro ⟨z, hzI⟩
            apply Subtype.ext
            change ffn ⟨z, Finset.mem_insert_of_mem hzI⟩ = (g ⟨z, hzI⟩).1
            have hzx : z ≠ x := fun h => hxI (h ▸ hzI)
            simp [ffn, dif_neg hzx]
    rw [hbij, Finset.card_product, hIc, Finset.card_univ, Fintype.card_embedding_eq,
      Fintype.card_coe, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hIc]
  let restrict : Equiv.Perm (Fin n) → (S ↪ Fin n) := fun p =>
    ⟨fun z => p z.1, fun z₁ z₂ h => Subtype.ext (p.injective h)⟩
  have hmaps : ∀ p ∈ goodPerms x I, restrict p ∈ E := by
    intro p hp
    rcases (Finset.mem_filter.mp hp).2 with ⟨hpx, hdisj⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hpx, ?_⟩
    intro z hzI
    exact Finset.disjoint_left.mp hdisj (Finset.mem_image_of_mem p hzI)
  have hfiber : ∀ f ∈ E, ((goodPerms x I).filter (fun p => restrict p = f)).card =
      (n - 1 - k).factorial := by
    intro f hf
    let imgF : Finset (Fin n) := Finset.univ.image f
    have himgFc : imgF.card = k + 1 := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ, Fintype.card_coe, hSc]
    have hcomp_eq : (Sᶜ : Finset (Fin n)).card = (imgFᶜ : Finset (Fin n)).card := by
      rw [Finset.card_compl, Finset.card_compl, Fintype.card_fin, hSc, himgFc]
    have hcomp_val : (Sᶜ : Finset (Fin n)).card = n - 1 - k := by
      rw [Finset.card_compl, Fintype.card_fin, hSc]; omega
    let eqv : (Sᶜ : Finset (Fin n)) ≃ (imgFᶜ : Finset (Fin n)) :=
      Fintype.equivOfCardEq (by simp only [Fintype.card_coe, hcomp_eq])
    have hbij : ((goodPerms x I).filter (fun p => restrict p = f)).card =
        (Finset.univ : Finset (Equiv.Perm (Sᶜ : Finset (Fin n)))).card := by
      refine Finset.card_bij
        (fun p hp =>
          ⟨fun u => eqv.symm ⟨p u.1, by
              rw [Finset.mem_compl]
              intro hmem
              rcases Finset.mem_image.mp hmem with ⟨z, _, hfz⟩
              have hrest : restrict p = f := (Finset.mem_filter.mp hp).2
              have hpz : p z.1 = f z := congrArg (fun g => g z) hrest
              have heq : z.1 = u.1 := p.injective (hpz.trans hfz)
              exact (Finset.mem_compl.mp u.2) (heq ▸ z.2)⟩,
           fun u => ⟨p.symm (eqv u).1, by
              rw [Finset.mem_compl]
              intro hmem
              have hrest : restrict p = f := (Finset.mem_filter.mp hp).2
              have hpz : p (p.symm (eqv u).1) = f ⟨p.symm (eqv u).1, hmem⟩ :=
                congrArg (fun g => g ⟨p.symm (eqv u).1, hmem⟩) hrest
              rw [Equiv.apply_symm_apply] at hpz
              exact (Finset.mem_compl.mp (eqv u).2)
                (hpz ▸ Finset.mem_image_of_mem f (Finset.mem_univ _))⟩,
           fun u => by
             apply Subtype.ext
             dsimp only
             rw [Equiv.apply_symm_apply]
             exact p.symm_apply_apply u.1,
           fun u => by
             apply eqv.injective
             rw [Equiv.apply_symm_apply]
             apply Subtype.ext
             exact p.apply_symm_apply (eqv u).1⟩)
        ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro p₁ hp₁ p₂ hp₂ heq
        have h1 : restrict p₁ = f := (Finset.mem_filter.mp hp₁).2
        have h2 : restrict p₂ = f := (Finset.mem_filter.mp hp₂).2
        apply DFunLike.ext
        intro z
        by_cases hz : z ∈ S
        · have hz1 : p₁ z = f ⟨z, hz⟩ := congrArg (fun g => g ⟨z, hz⟩) h1
          have hz2 : p₂ z = f ⟨z, hz⟩ := congrArg (fun g => g ⟨z, hz⟩) h2
          exact hz1.trans hz2.symm
        · have hzu : z ∈ Sᶜ := Finset.mem_compl.mpr hz
          have hstep := congrArg (fun σ => (eqv (σ ⟨z, hzu⟩)).1) heq
          simpa using hstep
      · intro σ _
        let fwd : Fin n → Fin n := fun z =>
          if hz : z ∈ S then f ⟨z, hz⟩ else (eqv (σ ⟨z, Finset.mem_compl.mpr hz⟩)).1
        have hfwd_inj : Function.Injective fwd := by
          intro z₁ z₂ heq
          dsimp only [fwd] at heq
          by_cases h1 : z₁ ∈ S <;> by_cases h2 : z₂ ∈ S
          · simp only [dif_pos h1, dif_pos h2] at heq
            exact congrArg (Subtype.val : S → Fin n) (f.injective heq)
          · simp only [dif_pos h1, dif_neg h2] at heq
            exact absurd (heq ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨z₁, h1⟩ : S)))
              (Finset.mem_compl.mp (eqv _).2)
          · simp only [dif_neg h1, dif_pos h2] at heq
            exact absurd (heq.symm ▸ Finset.mem_image_of_mem f (Finset.mem_univ (⟨z₂, h2⟩ : S)))
              (Finset.mem_compl.mp (eqv _).2)
          · simp only [dif_neg h1, dif_neg h2] at heq
            have hstep := σ.injective (eqv.injective (Subtype.ext heq))
            exact congrArg (Subtype.val : (Sᶜ : Finset (Fin n)) → Fin n) hstep
        let p : Equiv.Perm (Fin n) := Equiv.ofBijective fwd (Finite.injective_iff_bijective.mp hfwd_inj)
        have hp_rest : restrict p = f := by
          apply DFunLike.ext
          intro z
          change fwd z.1 = f z
          simp [fwd, z.2]
        refine ⟨p, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, hp_rest⟩
          rw [goodPerms, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_, ?_⟩
          · have hfx := (Finset.mem_filter.mp hf).2.1
            have hpx : p x = f ⟨x, Finset.mem_insert_self x I⟩ :=
              congrArg (fun g => g ⟨x, Finset.mem_insert_self x I⟩) hp_rest
            rwa [hpx]
          · rw [Finset.disjoint_left]
            intro y hyimg hyI
            rcases Finset.mem_image.mp hyimg with ⟨z, hzI, rfl⟩
            have hpz : p z = f ⟨z, Finset.mem_insert_of_mem hzI⟩ :=
              congrArg (fun g => g ⟨z, Finset.mem_insert_of_mem hzI⟩) hp_rest
            rw [hpz] at hyI
            exact (Finset.mem_filter.mp hf).2.2 ⟨z, Finset.mem_insert_of_mem hzI⟩ hzI hyI
        · apply DFunLike.ext
          intro u
          apply eqv.injective
          apply Subtype.ext
          change (eqv (eqv.symm ⟨p u.1, _⟩)).1 = (eqv (σ u)).1
          rw [Equiv.apply_symm_apply]
          change fwd u.1 = (eqv (σ u)).1
          have hnot : u.1 ∉ S := Finset.mem_compl.mp u.2
          simp [fwd, dif_neg hnot]
    rw [hbij, Finset.card_univ, Fintype.card_perm, Fintype.card_coe, hcomp_val]
  have hsum := Finset.card_eq_sum_card_fiberwise hmaps
  rw [hsum, Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hcard_E]

private lemma descFactorial_mul_factorial_eq {m k : ℕ} (hk : k ≤ m) :
    m.descFactorial k * (m - k).factorial = m.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.descFactorial_succ, mul_assoc, mul_comm (m - k), mul_assoc]
    have hfac : (m - k) * (m - (k + 1)).factorial = (m - k).factorial := by
      have hpos : m - k = (m - (k + 1)) + 1 := by omega
      conv_rhs => rw [hpos, Nat.factorial_succ]
      rw [← hpos]
    rw [mul_comm (m - (k + 1)).factorial (m - k), hfac]
    exact ih (by omega)

private lemma prod_ratio_ge {n k : ℕ} (hk : 2 * k ≤ n) :
    ((n - k).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ) / (n.factorial : ℝ) ≥
      (1 / (n : ℝ)) * (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k := by
  by_cases hn0 : n = 0
  · subst hn0
    have hk0 : k = 0 := by omega
    subst hk0; simp
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnk_pos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
    have : 0 < n - k := by omega
    exact_mod_cast this
  have hstep : ((n - k).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ) / (n.factorial : ℝ) =
      (1 / (n : ℝ)) * (∏ j ∈ Finset.range k, ((n - k - j : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ)) := by
    have h1 : ((n - k).descFactorial k : ℝ) = ∏ j ∈ Finset.range k, ((n - k - j : ℕ) : ℝ) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    have h2 : (n.factorial : ℝ) =
        (n : ℝ) * (∏ j ∈ Finset.range k, ((n - 1 - j : ℕ) : ℝ)) * ((n - 1 - k).factorial : ℝ) := by
      have hnat : n.factorial = n * (n - 1).descFactorial k * (n - 1 - k).factorial := by
        have hfac1 : n.factorial = n * (n - 1).factorial := by
          cases n with
          | zero => contradiction
          | succ m => simp [Nat.factorial_succ]
        rw [hfac1, mul_assoc, descFactorial_mul_factorial_eq (by omega)]
      rw [hnat, Nat.descFactorial_eq_prod_range]
      push_cast
      rfl
    have hfac_ne : ((n - 1 - k).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hprod_ne : (∏ j ∈ Finset.range k, ((n - 1 - j : ℕ) : ℝ)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
      have hj' := Finset.mem_range.mp hj
      have : 0 < n - 1 - j := by omega
      exact_mod_cast this.ne'
    rw [h1, h2, Finset.prod_div_distrib]
    field_simp [hn_pos.ne', hfac_ne, hprod_ne]
  rw [hstep]
  gcongr
  have hterm : ∀ j ∈ Finset.range k,
      1 - (k : ℝ) / ((n - k : ℕ) : ℝ) ≤ ((n - k - j : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ) := by
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hden_pos : (0 : ℝ) < ((n - 1 - j : ℕ) : ℝ) := by
      have : 0 < n - 1 - j := by omega
      exact_mod_cast this
    rw [le_div_iff₀ hden_pos, sub_mul, one_mul, div_mul_eq_mul_div, sub_le_iff_le_add]
    have hdiff : ((n - 1 - j : ℕ) : ℝ) - ((n - k - j : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have hnat : (n - k - j) + k = (n - 1 - j) + 1 := by omega
      have hcast : ((n - k - j : ℕ) : ℝ) + (k : ℝ) = ((n - 1 - j : ℕ) : ℝ) + 1 := by
        exact_mod_cast hnat
      linarith
    have hge : ((n - k : ℕ) : ℝ) ≤ ((n - 1 - j : ℕ) : ℝ) := by
      have : n - k ≤ n - 1 - j := by omega
      exact_mod_cast this
    have hdiv : ((k : ℝ) - 1) * ((n - k : ℕ) : ℝ) ≤ (k : ℝ) * ((n - 1 - j : ℕ) : ℝ) := by
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      nlinarith
    have hdiv' : (k : ℝ) - 1 ≤ (k : ℝ) * ((n - 1 - j : ℕ) : ℝ) / ((n - k : ℕ) : ℝ) :=
      (le_div_iff₀ hnk_pos).mpr hdiv
    linarith
  have hnonneg : 0 ≤ 1 - (k : ℝ) / ((n - k : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one hnk_pos]
    have : k ≤ n - k := by omega
    exact_mod_cast this
  calc
    (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k
        = ∏ _j ∈ Finset.range k, (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) := by simp
    _ ≤ ∏ j ∈ Finset.range k, ((n - k - j : ℕ) : ℝ) / ((n - 1 - j : ℕ) : ℝ) :=
        Finset.prod_le_prod (fun _ _ => hnonneg) hterm

end OMA.Green4H1

theorem OMA.solution : OMA.R_Green4_large_green_4_R1.H1 := by
  unfold OMA.R_Green4_large_green_4_R1.H1
  rw [Filter.eventually_atTop]
  refine ⟨100000, fun n hn => ?_⟩
  let k : ℕ := Nat.sqrt n / 2
  have hk_lo : 100 ≤ k := by
    have h1 : 316 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by omega)
    dsimp [k]; omega
  have h2k_sq : (2 * k) ^ 2 ≤ n := by
    have hle : 2 * k ≤ Nat.sqrt n := by dsimp [k]; omega
    calc (2 * k) ^ 2 ≤ (Nat.sqrt n) ^ 2 := Nat.pow_le_pow_left hle 2
      _ ≤ n := by simpa [sq] using Nat.sqrt_le n
  have hk_sq4 : 4 * k ^ 2 ≤ n := by nlinarith
  have h2k1 : 2 * k + 1 ≤ n := by nlinarith
  have h2k2 : k + 3 ≤ n := by nlinarith
  let x : Fin n := ⟨0, by omega⟩
  let I : Finset (Fin n) := Finset.univ.filter (fun z : Fin n => 1 ≤ z.1 ∧ z.1 ≤ k)
  have hxI : x ∉ I := by simp [x, I]
  have hIc : I.card = k := by
    have hbij : I.card = (Finset.Icc 1 k).card := by
      refine Finset.card_bij (fun z _ => z.1) ?_ ?_ ?_
      · intro z hz
        rcases (Finset.mem_filter.mp hz).2 with ⟨h1, h2⟩
        exact Finset.mem_Icc.mpr ⟨h1, h2⟩
      · intro z₁ _ z₂ _ h; exact Fin.ext h
      · intro m hm
        rcases Finset.mem_Icc.mp hm with ⟨h1, h2⟩
        refine ⟨⟨m, by omega⟩, ?_, rfl⟩
        simp [I, h1, h2]
    rw [hbij, Nat.card_Icc]; omega
  let a : Fin n := ⟨k + 1, by omega⟩
  let b : Fin n := ⟨k + 2, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a, b] at this; omega
  have hax : a ≠ x := by intro h; have := congrArg Fin.val h; dsimp [a, x] at this; omega
  have hbx : b ≠ x := by intro h; have := congrArg Fin.val h; dsimp [b, x] at this; omega
  have haI : a ∉ I := by simp [a, I]
  have hbI : b ∉ I := by simp [b, I]
  refine ⟨x, (I : Set (Fin n)), ?_⟩
  open scoped Classical in
  have hext_eq : (Green4.extremalFamily x (I : Set (Fin n))).ncard =
      ((OMA.Green4H1.goodPerms x I).filter (fun p => p ∈ alternatingGroup (Fin n))).card := by
    let F : Finset (alternatingGroup (Fin n)) :=
      ((OMA.Green4H1.goodPerms x I).filter (fun p => p ∈ alternatingGroup (Fin n))).subtype
        (fun p => p ∈ alternatingGroup (Fin n))
    have hcoe : Green4.extremalFamily x (I : Set (Fin n)) = (F : Set (alternatingGroup (Fin n))) := by
      ext ⟨p, hp⟩
      simp [F, Green4.extremalFamily, OMA.Green4H1.mem_goodPerms_iff,
        Equiv.Perm.mem_alternatingGroup.mp hp]
    rw [hcoe, Set.ncard_coe_finset]
    refine Finset.card_bij (fun (p : alternatingGroup (Fin n)) _ => p.1) ?_ ?_ ?_
    · intro p hp
      exact Finset.mem_subtype.mp hp
    · intro p₁ _ p₂ _ h; exact Subtype.ext h
    · intro p hp
      refine ⟨⟨p, (Finset.mem_filter.mp hp).2⟩, ?_, rfl⟩
      exact Finset.mem_subtype.mpr hp
  open scoped Classical in
  have hcard_alt : 2 * Fintype.card (alternatingGroup (Fin n)) = n.factorial := by
    let τ : Equiv.Perm (Fin n) := Equiv.swap a b
    have hτ_sign : Equiv.Perm.sign τ = -1 := Equiv.Perm.sign_swap hab
    have hbij : ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun p => p ∈ alternatingGroup (Fin n))).card =
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
        (fun p => p ∉ alternatingGroup (Fin n))).card := by
      refine Finset.card_bij (fun p _ => p * τ) ?_ ?_ ?_
      · intro p hp
        have heven : p ∈ alternatingGroup (Fin n) := (Finset.mem_filter.mp hp).2
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [Equiv.Perm.mem_alternatingGroup] at heven ⊢
        rw [map_mul, heven, hτ_sign, one_mul]
        decide
      · intro p₁ _ p₂ _ h; exact mul_right_cancel h
      · intro σ hσ
        have hodd : σ ∉ alternatingGroup (Fin n) := (Finset.mem_filter.mp hσ).2
        refine ⟨σ * τ, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [Equiv.Perm.mem_alternatingGroup] at hodd ⊢
          rw [map_mul, hτ_sign]
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | hneg1
          · exact absurd h1 hodd
          · rw [hneg1]; decide
        · rw [mul_assoc, Equiv.swap_mul_self, mul_one]
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Equiv.Perm (Fin n))))
      (fun p => p ∈ alternatingGroup (Fin n))
    have hcard_even : Fintype.card (alternatingGroup (Fin n)) =
        ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter
          (fun p => p ∈ alternatingGroup (Fin n))).card := by
      rw [Fintype.card_subtype]
    have huniv : (Finset.univ : Finset (Equiv.Perm (Fin n))).card = n.factorial := by
      rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    omega
  open scoped Classical in
  have hcard_good := OMA.Green4H1.card_even_goodPerms_mul_two x I a b hab hax hbx haI hbI
  have hcard_all := OMA.Green4H1.card_goodPerms_eq h2k1 x I hxI hIc
  have hratio_eq :
      ((Green4.extremalFamily x (I : Set (Fin n))).ncard : ℝ) /
        (Fintype.card (alternatingGroup (Fin n)) : ℝ) =
      (k : ℝ) * (((n - k).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ) / (n.factorial : ℝ)) := by
    open scoped Classical in
    rw [hext_eq]
    have halt_pos : (0 : ℝ) < (Fintype.card (alternatingGroup (Fin n)) : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := alternatingGroup (Fin n))
    have hfac_pos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
    have h1 : (2 : ℝ) * (((OMA.Green4H1.goodPerms x I).filter (fun p => p ∈ alternatingGroup (Fin n))).card : ℝ) =
        ((OMA.Green4H1.goodPerms x I).card : ℝ) := by exact_mod_cast hcard_good
    have h2 : (2 : ℝ) * (Fintype.card (alternatingGroup (Fin n)) : ℝ) = (n.factorial : ℝ) := by
      exact_mod_cast hcard_alt
    have h3 : ((OMA.Green4H1.goodPerms x I).card : ℝ) =
        (k : ℝ) * ((n - k).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ) := by
      exact_mod_cast hcard_all
    field_simp [halt_pos.ne', hfac_pos.ne']
    nlinarith
  rw [hratio_eq]
  have hprod := OMA.Green4H1.prod_ratio_ge (n := n) (k := k) (by omega)
  have hstep1 :
      (k : ℝ) * ((1 / (n : ℝ)) * (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k) ≤
      (k : ℝ) * (((n - k).descFactorial k : ℝ) * ((n - 1 - k).factorial : ℝ) / (n.factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg k)
  have hnk_pos : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by
    have : 0 < n - k := by omega
    exact_mod_cast this
  have hbern_arg : -(2 : ℝ) ≤ -((k : ℝ) / ((n - k : ℕ) : ℝ)) := by
    have hle1 : (k : ℝ) / ((n - k : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hnk_pos]
      have : k ≤ n - k := by omega
      exact_mod_cast this
    linarith
  have hbern : 1 - (k : ℝ) * ((k : ℝ) / ((n - k : ℕ) : ℝ)) ≤
      (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k := by
    have hb := one_add_mul_le_pow hbern_arg k
    simpa [sub_eq_add_neg, mul_neg] using hb
  have htwo_thirds : (2 : ℝ) / 3 ≤ 1 - (k : ℝ) * ((k : ℝ) / ((n - k : ℕ) : ℝ)) := by
    have h1 : 4 * (k : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hk_sq4
    have h4k : 4 * k ≤ n := by nlinarith
    have h2 : 3 * (n : ℝ) ≤ 4 * ((n - k : ℕ) : ℝ) := by
      have hnat : 3 * n ≤ 4 * (n - k) := by omega
      exact_mod_cast hnat
    have hdiv : (k : ℝ) * ((k : ℝ) / ((n - k : ℕ) : ℝ)) ≤ 1 / 3 := by
      rw [mul_div_assoc', div_le_iff₀ hnk_pos]
      nlinarith
    linarith
  have hk_real_lo : Real.sqrt (n : ℝ) / 3 ≤ (k : ℝ) := by
    have hsq : (n : ℝ) < ((Nat.sqrt n + 1 : ℕ) : ℝ) ^ 2 := by
      have hnat : n < (Nat.sqrt n + 1) ^ 2 := by simpa [sq] using Nat.lt_succ_sqrt n
      exact_mod_cast hnat
    have hsqrt_lt : Real.sqrt (n : ℝ) ≤ (Nat.sqrt n : ℝ) + 1 := by
      have hle : (n : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) ^ 2 := by push_cast at hsq; linarith
      calc Real.sqrt (n : ℝ) ≤ Real.sqrt (((Nat.sqrt n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt hle
        _ = (Nat.sqrt n : ℝ) + 1 := Real.sqrt_sq (by positivity)
    have hdiv2 : (Nat.sqrt n : ℝ) ≤ 2 * (k : ℝ) + 1 := by
      have hnat : Nat.sqrt n ≤ 2 * k + 1 := by dsimp [k]; omega
      exact_mod_cast hnat
    have hk100 : (100 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_lo
    linarith
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hstep2 : (2 : ℝ) / 9 * (n : ℝ) ^ (-(1 : ℝ) / 2) ≤
      (k : ℝ) * ((1 / (n : ℝ)) * (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k) := by
    have hpow : (n : ℝ) ^ (-(1 : ℝ) / 2) = Real.sqrt (n : ℝ) / (n : ℝ) := by
      rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = (1 / 2 : ℝ) - 1 by norm_num,
        Real.rpow_sub hn_pos, Real.rpow_one]
    rw [hpow]
    have h1 : (2 : ℝ) / 3 ≤ (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k := htwo_thirds.trans hbern
    have h2 : (Real.sqrt (n : ℝ) / 3) * ((1 / (n : ℝ)) * (2 / 3)) ≤
        (k : ℝ) * ((1 / (n : ℝ)) * (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k) := by
      apply mul_le_mul hk_real_lo
      · exact mul_le_mul_of_nonneg_left h1 (by positivity)
      · positivity
      · positivity
    calc (2 : ℝ) / 9 * (Real.sqrt (n : ℝ) / (n : ℝ))
        = (Real.sqrt (n : ℝ) / 3) * ((1 / (n : ℝ)) * (2 / 3)) := by ring
      _ ≤ (k : ℝ) * ((1 / (n : ℝ)) * (1 - (k : ℝ) / ((n - k : ℕ) : ℝ)) ^ k) := h2
  have hstep3 : (n : ℝ) ^ (-(33 : ℝ) / 50) ≤ (2 : ℝ) / 9 * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    have h5 : (5 : ℝ) ≤ (n : ℝ) ^ ((4 : ℝ) / 25) := by
      have h5_25 : (5 : ℝ) ^ (25 : ℕ) ≤ (n : ℝ) ^ (4 : ℕ) := by
        have hnat : (5 : ℕ) ^ 25 ≤ n ^ 4 := by
          have h10 : (100000 : ℕ) ^ 4 ≤ n ^ 4 := Nat.pow_le_pow_left hn 4
          have hbig : (5 : ℕ) ^ 25 ≤ (100000 : ℕ) ^ 4 := by norm_num
          exact hbig.trans h10
        exact_mod_cast hnat
      have hpow4 : ((5 : ℝ) ^ (25 : ℕ)) ^ ((1 : ℝ) / 25) ≤ ((n : ℝ) ^ (4 : ℕ)) ^ ((1 : ℝ) / 25) :=
        Real.rpow_le_rpow (by positivity) h5_25 (by norm_num)
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hn_pos.le] at hpow4
      norm_num at hpow4
      exact hpow4
    have hmul : (n : ℝ) ^ (-(33 : ℝ) / 50) * (n : ℝ) ^ ((4 : ℝ) / 25) = (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hn_pos]
      congr 1; norm_num
    have hpos1 : 0 ≤ (n : ℝ) ^ (-(33 : ℝ) / 50) := Real.rpow_nonneg hn_pos.le _
    have hle5 : (n : ℝ) ^ (-(33 : ℝ) / 50) * 5 ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [← hmul]
      exact mul_le_mul_of_nonneg_left h5 hpos1
    linarith
  exact hstep3.trans (hstep2.trans hstep1)
