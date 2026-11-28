import OMAReductions.R_Erdos835_johnson_chromaticNumber_R2

/-! Extract exact trace quotas and restrict the obstruction to prime color counts. -/

open Finset

namespace OMA.R_Erdos835_johnson_chromaticNumber_R2_H1_R1

/-- The remaining half-coloring obstruction at prime color counts, with the
central color fixed to zero and a single explicit quota for each trace. -/
def H1 : Prop :=
  ∀ k : ℕ, 6 ≤ k → (k+1).Prime → ∀ A : Finset (Fin (2*k)), A.card = k →
    ¬ ∃ F : Fin (k+1) → Finset (Finset (Fin (2*k))),
      A ∈ F 0 ∧
      (∀ i B, B ∈ F i → B.card = k ∧ k ≤ 2*(A ∩ B).card) ∧
      (∀ B : Finset (Fin (2*k)), B.card = k → k ≤ 2*(A ∩ B).card →
        ∃! i, B ∈ F i) ∧
      (∀ i B C, B ∈ F i → C ∈ F i → (B ∩ C).card + 1 ≠ k) ∧
      (∀ i B, B ∈ F i → 2*(A ∩ B).card = k → Bᶜ ∈ F i) ∧
      (∀ I : Finset (Fin (2*k)), I ⊆ A → k ≤ 2*I.card → ∀ i,
        ((k : ℤ)+1) * ((F i).filter (fun B => A ∩ B = I)).card =
          (k.choose (k-I.card) : ℤ) +
            (-1 : ℤ)^(k-I.card) * (if i = 0 then (k : ℤ) else -1))

/-- The alternating residues on the lower half of an even binomial row force
the row length to be prime. -/
def H2 : Prop :=
  ∀ k : ℕ, 3 ≤ k → Even k →
    (∀ t : ℕ, 2*t ≤ k → (k.choose t : ZMod (k+1)) = (-1) ^ t) →
    (k+1).Prime

lemma prime_of_residues : H2 := by
  intro k hk he h
  have hfull (t : ℕ) (ht : t ≤ k) : (k.choose t : ZMod (k+1)) = (-1)^t := by
    by_cases ht' : 2*t ≤ k
    · exact h t ht'
    rw [← Nat.choose_symm ht, h (k-t) (by omega)]
    have hmul : (-1 : ZMod (k+1))^(k-t) * (-1)^t = 1 := by
      rw [← pow_add, Nat.sub_add_cancel ht, he.neg_one_pow]
    have hsq : (-1 : ZMod (k+1))^t * (-1)^t = 1 := by
      rw [← pow_add]
      exact (show Even (t+t) from ⟨t,rfl⟩).neg_one_pow
    calc
      _ = (-1 : ZMod (k+1))^(k-t) * ((-1)^t * (-1)^t) := by rw [hsq, mul_one]
      _ = _ := by rw [← mul_assoc, hmul, one_mul]
  have hd : (k+1) ∣ (Icc 1 k).gcd (Nat.choose (k+1)) :=
    dvd_gcd_iff.mpr fun t ht => by
      have ht' := mem_Icc.mp ht
      obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      rw [Nat.choose_succ_succ', Nat.cast_add, hfull s (by omega), hfull (s+1) ht'.2, pow_succ]
      ring
  have hd' : (k+1) ∣ (Icc 1 (k+1-1)).gcd (Nat.choose (k+1)) := by simpa using hd
  by_cases hpow : IsPrimePow (k+1)
  · rw [Choose.gcd_choose_eq_minFac_of_isPrimePow hpow] at hd'
    exact Nat.prime_def_minFac.mpr
      ⟨by omega, le_antisymm (Nat.minFac_le (by omega)) (Nat.le_of_dvd (Nat.minFac_pos _) hd')⟩
  · rw [Choose.gcd_choose_eq_one_of_not_isPrimePow (by omega) hpow] at hd'
    have hone := Nat.dvd_one.mp hd'
    omega

lemma trace_size {k : ℕ} {A I : Finset (Fin (2*k))} (hA : A.card = k) (hI : I ⊆ A) :
    ((univ : Finset (Finset (Fin (2*k)))).filter
      (fun B => B.card = k ∧ A ∩ B = I)).card = k.choose (k-I.card) := by
  classical
  let U := Aᶜ.powersetCard (k-I.card)
  have hrecover (J : Finset (Fin (2*k))) (hJ : J ⊆ Aᶜ) : (I ∪ J) \ A = J := by
    ext z
    simp only [mem_sdiff, mem_union]
    have hout : z ∈ J → z ∉ A := fun hz => mem_compl.mp (hJ hz)
    have hin : z ∈ I → z ∈ A := fun hz => hI hz
    tauto
  have hIc : I.card ≤ k := (card_le_card hI).trans_eq hA
  have eq : (univ : Finset (Finset (Fin (2*k)))).filter
        (fun B => B.card = k ∧ A ∩ B = I) = U.image (I ∪ ·) := by
    ext B
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨hB,hInt⟩
      have hdiff := card_sdiff_add_card_inter B A
      rw [inter_comm, hInt, hB] at hdiff
      refine ⟨B \ A, mem_powersetCard.mpr ⟨?_,by omega⟩,?_⟩
      · exact fun z hz => mem_compl.mpr (mem_sdiff.mp hz).2
      · rw [← hInt]
        ext z
        simp only [mem_union, mem_inter, mem_sdiff]
        tauto
    · rintro ⟨J,hJU,rfl⟩
      obtain ⟨hj,hc⟩ := mem_powersetCard.mp hJU
      have hdis : Disjoint I J := disjoint_left.mpr fun z hz hz' =>
        (mem_compl.mp (hj hz')) (hI hz)
      refine ⟨by rw [card_union_of_disjoint hdis,hc]; omega,?_⟩
      ext z
      simp only [mem_inter, mem_union]
      have ho : z ∈ J → z ∉ A := fun hz => mem_compl.mp (hj hz)
      have hi : z ∈ I → z ∈ A := fun hz => hI hz
      tauto
  rw [eq, card_image_of_injOn (f := (I ∪ ·)) (s := U) (by
    intro J hJ L hL heq
    have q := congrArg (fun S : Finset (Fin (2*k)) => S \ A) heq
    simpa only [hrecover J (mem_powersetCard.mp hJ).1,
      hrecover L (mem_powersetCard.mp hL).1] using q)]
  simp only [U, card_powersetCard, card_compl, Fintype.card_fin, hA]
  congr 1
  omega

lemma trace_quota {k : ℕ} {A I : Finset (Fin (2*k))} (hA : A.card = k) (hI : I ⊆ A)
    (hcap : k ≤ 2*I.card) (F : Fin (k+1) → Finset (Finset (Fin (2*k)))) (a : Fin (k+1))
    (hsize : ∀ i B, B ∈ F i → B.card = k)
    (hpart : ∀ B : Finset (Fin (2*k)), B.card = k → k ≤ 2*(A ∩ B).card →
        ∃! i, B ∈ F i)
    (hdiff : ∀ i j : Fin (k+1),
      (((F i).filter (fun B => A ∩ B = I)).card : ℤ) -
          ((F j).filter (fun B => A ∩ B = I)).card =
        (-1 : ℤ) ^ (k-I.card) * ((if a = i then 1 else 0) - (if a = j then 1 else 0)))
    (i : Fin (k+1)) :
    ((k : ℤ)+1) * ((F i).filter (fun B => A ∩ B = I)).card =
      (k.choose (k-I.card) : ℤ) +
        (-1 : ℤ)^(k-I.card) * (((k : ℤ)+1) * (if a = i then 1 else 0) - 1) := by
  classical
  let T (j : Fin (k+1)) := (F j).filter (fun B => A ∩ B = I)
  have hcover : (univ : Finset (Fin (k+1))).biUnion T =
      (univ : Finset (Finset (Fin (2*k)))).filter (fun B => B.card = k ∧ A ∩ B = I) := by
    ext B
    simp only [mem_biUnion, mem_univ, true_and, T, mem_filter]
    constructor
    · rintro ⟨j,hB,hInt⟩
      exact ⟨hsize j B hB,hInt⟩
    · rintro ⟨hB,hInt⟩
      obtain ⟨j,hj,_⟩ := hpart B hB (hInt ▸ hcap)
      exact ⟨j,hj,hInt⟩
  have hpw : (↑(univ : Finset (Fin (k+1))) : Set (Fin (k+1))).PairwiseDisjoint T := by
    intro j _ l _ hne
    apply disjoint_left.mpr
    intro B hb hc
    have ⟨hj,hInt⟩ := mem_filter.mp hb
    obtain ⟨m,_,hu⟩ := hpart B (hsize j B hj) (hInt ▸ hcap)
    exact hne ((hu j hj).trans (hu l (mem_filter.mp hc).1).symm)
  have hsum : ∑ j : Fin (k+1), (T j).card = k.choose (k-I.card) := by
    rw [← card_biUnion hpw, hcover, trace_size hA hI]
  let s : ℤ := (-1)^(k-I.card)
  let δ (j : Fin (k+1)) : ℤ := if a = j then 1 else 0
  have hδ : ∑ j : Fin (k+1), δ j = 1 := by simp [δ]
  have hdi (j : Fin (k+1)) : ((T i).card : ℤ) =
      (T j).card + s * δ i - s * δ j := by
    have hh := hdiff i j
    change ((T i).card : ℤ) - (T j).card = s * (δ i - δ j) at hh
    rw [mul_sub] at hh
    linarith
  have hsum' : ∑ j : Fin (k+1), ((T j).card : ℤ) = (k.choose (k-I.card) : ℤ) := by
    exact_mod_cast hsum
  have summed := Finset.sum_congr (s₁ := (univ : Finset (Fin (k+1)))) rfl (fun j _ => hdi j)
  have hsδ : (∑ j : Fin (k+1), s * δ j) = s := by rw [← mul_sum, hδ, mul_one]
  rw [sum_sub_distrib, sum_add_distrib, hsδ, hsum'] at summed
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at summed
  change ((k : ℤ)+1) * (T i).card = (k.choose (k-I.card) : ℤ) + s * (((k : ℤ)+1) * δ i - 1)
  linarith only [summed]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 6000000 in
lemma latin_three_rows :
    ∀ p q : Equiv.Perm (Fin 4),
    (∀ j, p j ≠ j ∧ q j ≠ j ∧ p j ≠ q j) →
      (∃ j l, j ≠ l ∧ p j = l ∧ p l = j) ∨
      (∃ j l, j ≠ l ∧ q j = l ∧ q l = j) ∨
      (∃ j l, j ≠ l ∧ p j = q l ∧ p l = q j) := by
  decide +kernel

lemma intercalate (L : Fin 4 → Fin 4 → Fin 4)
    (row : ∀ i, Function.Injective (L i)) (col : ∀ j, Function.Injective (L · j)) :
    ∃ (i t j l : Fin 4), i ≠ t ∧ j ≠ l ∧ L i j = L t l ∧ L i l = L t j := by
  let e := Equiv.ofBijective (L 0) (row 0).bijective_of_finite
  let p := (Equiv.ofBijective (L 1) (row 1).bijective_of_finite).trans e.symm
  let q := (Equiv.ofBijective (L 2) (row 2).bijective_of_finite).trans e.symm
  have hp (j) : e (p j) = L 1 j := by simp [p]
  have hq (j) : e (q j) = L 2 j := by simp [q]
  have he (j) : e j = L 0 j := rfl
  have neq (j : Fin 4) : p j ≠ j ∧ q j ≠ j ∧ p j ≠ q j := by
    refine ⟨fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
    · exact (by decide : (1 : Fin 4) ≠ 0) (col j ((hp j).symm.trans ((congrArg e hh).trans (he j))))
    · exact (by decide : (2 : Fin 4) ≠ 0) (col j ((hq j).symm.trans ((congrArg e hh).trans (he j))))
    · exact (by decide : (1 : Fin 4) ≠ 2) (col j ((hp j).symm.trans ((congrArg e hh).trans (hq j))))
  rcases latin_three_rows p q neq with ⟨j,l,hjl,h1,h2⟩ | ⟨j,l,hjl,h1,h2⟩ | ⟨j,l,hjl,h1,h2⟩
  · exact ⟨1,0,j,l,by decide,hjl,
      (hp j).symm.trans ((congrArg e h1).trans (he l)),
      (hp l).symm.trans ((congrArg e h2).trans (he j))⟩
  · exact ⟨2,0,j,l,by decide,hjl,
      (hq j).symm.trans ((congrArg e h1).trans (he l)),
      (hq l).symm.trans ((congrArg e h2).trans (he j))⟩
  · exact ⟨1,2,j,l,by decide,hjl,
      (hp j).symm.trans ((congrArg e h1).trans (hq l)),
      (hp l).symm.trans ((congrArg e h2).trans (hq j))⟩

set_option maxHeartbeats 1000000 in
/-- A four-by-four first shell produces an intercalate, which leaves two
noncentral colors competing for the same block in a size-two trace. -/
lemma no_half_four (A : Finset (Fin 8)) (hA : A.card = 4)
    (F : Fin 5 → Finset (Finset (Fin 8)))
    (hsize : ∀ i B, B ∈ F i → B.card = 4 ∧ 4 ≤ 2*(A ∩ B).card)
    (hpart : ∀ B : Finset (Fin 8), B.card = 4 → 4 ≤ 2*(A ∩ B).card → ∃! i, B ∈ F i)
    (hproper : ∀ i B C, B ∈ F i → C ∈ F i → (B ∩ C).card + 1 ≠ 4)
    (hzero : ∀ I : Finset (Fin 8), I ⊆ A → I.card = 3 →
      ((F 0).filter (fun B => A ∩ B = I)).card = 0)
    (hother : ∀ I : Finset (Fin 8), I ⊆ A → I.card = 2 →
      ∀ c : Fin 5, c ≠ 0 → ((F c).filter (fun B => A ∩ B = I)).Nonempty) :
    False := by
  classical
  have hAc : (Aᶜ).card = 4 := by rw [card_compl, Fintype.card_fin, hA]
  let e : Fin 4 ≃ ↑A := Fintype.equivOfCardEq (by simp [hA])
  let g : Fin 4 ≃ ↑(Aᶜ : Finset (Fin 8)) := Fintype.equivOfCardEq (by simp only [Fintype.card_fin, Fintype.card_coe, hAc])
  let x (i : Fin 4) := (e i).val
  let y (j : Fin 4) := (g j).val
  have hx (i : Fin 4) : x i ∈ A := (e i).property
  have hy (j : Fin 4) : y j ∉ A := mem_compl.mp (g j).property
  have xinj : Function.Injective x := fun _ _ h => e.injective (Subtype.ext h)
  have yinj : Function.Injective y := fun _ _ h => g.injective (Subtype.ext h)
  let B (i j : Fin 4) := insert (y j) (A.erase (x i))
  have hE (i : Fin 4) : (A.erase (x i)).card = 3 := by rw [card_erase_of_mem (hx i),hA]
  have hBc (i j : Fin 4) : (B i j).card = 4 := by
    simp [B, card_insert_of_notMem (fun h => hy j (mem_of_mem_erase h)), hE]
  have hBi (i j : Fin 4) : A ∩ B i j = A.erase (x i) := by
    ext v
    simp only [B, mem_inter, mem_insert, mem_erase]
    have hv : v = y j → v ∉ A := fun h => h.symm ▸ hy j
    tauto
  let C (i j : Fin 4) := (hpart (B i j) (hBc i j) (by rw [hBi,hE]; decide)).exists.choose
  have hC (i j : Fin 4) : B i j ∈ F (C i j) :=
    (hpart (B i j) (hBc i j) (by rw [hBi,hE]; decide)).exists.choose_spec
  have hC0 (i j : Fin 4) : C i j ≠ 0 := by
    intro hc
    have h := hzero _ (erase_subset _ _) (hE i)
    rw [card_eq_zero] at h
    have hm : B i j ∈ (F 0).filter (fun T => A ∩ T = A.erase (x i)) :=
      mem_filter.mpr ⟨hc ▸ hC i j,hBi i j⟩
    rw [h] at hm
    exact notMem_empty _ hm
  have positive (i j : Fin 4) : 0 < (C i j).val := by
    exact Nat.pos_of_ne_zero (fun h => hC0 i j (Fin.ext h))
  let L (i j : Fin 4) : Fin 4 := ⟨(C i j).val - 1, by have := (C i j).isLt; omega⟩
  have hue {i t j l : Fin 4} : L i j = L t l ↔ C i j = C t l := by
    constructor
    · intro h
      apply Fin.ext
      have h' := congrArg Fin.val h
      change (C i j).val - 1 = (C t l).val - 1 at h'
      have := positive i j
      have := positive t l
      omega
    · intro h
      apply Fin.ext
      exact congrArg (fun c : Fin 5 => c.val - 1) h
  have hrow (i : Fin 4) : Function.Injective (L i) := by
    intro j l h
    by_contra hjl
    have hi : B i j ∩ B i l = A.erase (x i) := by
      ext v
      simp only [B, mem_inter, mem_insert]
      have hn : y j ≠ y l := fun h => hjl (yinj h)
      grind
    have code := hue.mp h
    exact hproper _ _ _ (hC i j) (code.symm ▸ hC i l) (by rw [hi,hE])
  have hcol (j : Fin 4) : Function.Injective (L · j) := by
    intro i t h
    by_contra hit
    have hd : x i ≠ x t := fun h => hit (xinj h)
    have hi : B i j ∩ B t j = insert (y j) ((A.erase (x i)).erase (x t)) := by
      ext v
      simp only [B, mem_inter, mem_insert, mem_erase]
      tauto
    have hD : x t ∈ A.erase (x i) := mem_erase.mpr ⟨hd.symm, hx t⟩
    have hout : y j ∉ (A.erase (x i)).erase (x t) :=
      fun h => hy j (mem_of_mem_erase (mem_of_mem_erase h))
    have code := hue.mp h
    exact hproper _ _ _ (hC i j) (code.symm ▸ hC t j)
      (by rw [hi,card_insert_of_notMem hout,card_erase_of_mem hD,hE])
  obtain ⟨i,t,j,l,hit,hjl,hi,hl⟩ := intercalate L hrow hcol
  let I := (A.erase (x i)).erase (x t)
  have hIA : I ⊆ A := (erase_subset _ _).trans (erase_subset _ _)
  have hIc : I.card = 2 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨fun h => hit (xinj h.symm),hx t⟩), hE]
  let u := C i j
  let v := C i l
  have huv : u ≠ v := fun h => hjl (hrow i (hue.mpr h))
  have forced (S : Finset (Fin 8)) (hSI : A ∩ S = I) :
      (S ∈ F u ∨ S ∈ F v) → S \ A ⊆ (Aᶜ.erase (y j)).erase (y l) := by
    have hforbid (a b : Fin 4) (hac : I ⊆ A.erase (x a)) (hS : S ∈ F (C a b)) :
        y b ∉ S := by
      intro hys
      have hEq : S ∩ B a b = insert (y b) I := by
        ext w
        simp only [B, mem_inter, mem_insert]
        have ha (h : w ∈ A.erase (x a)) : w ∈ A := mem_of_mem_erase h
        have iffI : w ∈ I ↔ w ∈ A ∧ w ∈ S := by rw [← hSI,mem_inter]
        have yy : w = y b → w ∈ S := fun e => e.symm ▸ hys
        have inc : w ∈ I → w ∈ A.erase (x a) := fun h => hac h
        tauto
      have hout : y b ∉ I := fun h => hy b (hIA h)
      exact hproper _ _ _ hS (hC a b) (by rw [hEq, card_insert_of_notMem hout, hIc])
    have hiI : I ⊆ A.erase (x i) := erase_subset _ _
    have htI : I ⊆ A.erase (x t) := by
      intro z hz
      exact mem_erase.mpr ⟨(mem_erase.mp hz).1, hIA hz⟩
    intro hS z hz
    obtain ⟨hzS,hzA⟩ := mem_sdiff.mp hz
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,mem_compl.mpr hzA⟩⟩
    · intro eql
      rcases hS with hu | hv
      · exact hforbid t l htI ((hue.mp hi) ▸ hu) (eql ▸ hzS)
      · exact hforbid i l hiI hv (eql ▸ hzS)
    · intro eqj
      rcases hS with hu | hv
      · exact hforbid i j hiI hu (eqj ▸ hzS)
      · exact hforbid t j htI ((hue.mp hl) ▸ hv) (eqj ▸ hzS)
  obtain ⟨S,hS⟩ := hother I hIA hIc u (hC0 i j)
  obtain ⟨T,hT⟩ := hother I hIA hIc v (hC0 i l)
  obtain ⟨hSu,hSI⟩ := mem_filter.mp hS
  obtain ⟨hTv,hTI⟩ := mem_filter.mp hT
  let R := (Aᶜ.erase (y j)).erase (y l)
  have hRc : R.card = 2 := by
    have hyl : y l ∈ Aᶜ.erase (y j) :=
      mem_erase.mpr ⟨fun he => hjl (yinj he.symm),mem_compl.mpr (hy l)⟩
    rw [card_erase_of_mem hyl,card_erase_of_mem (mem_compl.mpr (hy j)),hAc]
  have eqR (W : Finset (Fin 8)) (hWI : A ∩ W = I) (hWc : W.card = 4)
      (hmem : W ∈ F u ∨ W ∈ F v) : W = I ∪ R := by
    have hd := card_sdiff_add_card_inter W A
    rw [inter_comm,hWI,hIc,hWc] at hd
    have hR' : W \ A = R :=
      eq_of_subset_of_card_le (forced W hWI hmem) (by rw [hRc]; omega)
    rw [← hR',← hWI]
    ext z
    simp only [mem_union,mem_inter,mem_sdiff]
    tauto
  have eqST : S = T :=
    (eqR S hSI (hsize _ _ hSu).1 (Or.inl hSu)).trans
      (eqR T hTI (hsize _ _ hTv).1 (Or.inr hTv)).symm
  obtain ⟨m,_,hm⟩ := hpart S (hsize _ _ hSu).1 (hsize _ _ hSu).2
  exact huv ((hm u hSu).trans (hm v (eqST.symm ▸ hTv)).symm)

theorem main : H1 → H2 → OMA.R_Erdos835_johnson_chromaticNumber_R2.H1 := by
  classical
  intro hprime hres k hk he A hA
  rintro ⟨F,a,ha,hsize,hpart,hproper,heq,htrace⟩
  have hquota (I : Finset (Fin (2*k))) (hI : I ⊆ A) (hc : k ≤ 2*I.card) (i : Fin (k+1)) :=
    trace_quota hA hI hc F a (fun j B hb => (hsize j B hb).1) hpart (htrace I hI hc) i
  have hp : (k+1).Prime := hres k hk he (by
    intro t ht
    obtain ⟨I,hI,hIc⟩ := exists_subset_card_eq (s := A) (n := k-t) (by rw [hA]; omega)
    have : Nontrivial (Fin (k+1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
    obtain ⟨b,hba⟩ := exists_ne a
    have hab := hba.symm
    have hq := hquota I hI (by omega) b
    have hKt : k-I.card = t := by omega
    rw [hKt, if_neg hab] at hq
    have hz := congrArg (fun x : ℤ => (x : ZMod (k+1))) hq
    push_cast at hz
    have hzero : (↑k : ZMod (k+1)) + 1 = 0 := by
      simpa only [Nat.cast_add, Nat.cast_one] using ZMod.natCast_self (k+1)
    simp only [hzero, zero_mul, zero_sub, mul_neg_one] at hz
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hz.symm))
  let e : Equiv.Perm (Fin (k+1)) := Equiv.swap 0 a
  have he0 : e 0 = a := Equiv.swap_apply_left _ _
  let G (i : Fin (k+1)) := F (e i)
  have hAG : A ∈ G 0 := by simpa only [G,he0] using ha
  have gsize (i) (B) : B ∈ G i → B.card = k ∧ k ≤ 2*(A ∩ B).card := hsize (e i) B
  have gproper (i B C) : B ∈ G i → C ∈ G i → (B ∩ C).card + 1 ≠ k := hproper (e i) B C
  have gequator (i B) : B ∈ G i → 2*(A ∩ B).card = k → Bᶜ ∈ G i := heq (e i) B
  have gpart (B : Finset (Fin (2*k))) (hB : B.card = k) (hcap : k ≤ 2*(A ∩ B).card) :
      ∃! i, B ∈ G i := by
    obtain ⟨j,hj,huniq⟩ := hpart B hB hcap
    refine ⟨e.symm j, by simpa [G] using hj, fun i hi => ?_⟩
    apply e.injective
    simpa using huniq (e i) hi
  have gquota (I : Finset (Fin (2*k))) (hI : I ⊆ A) (hc : k ≤ 2*I.card) (i : Fin (k+1)) :
      ((k : ℤ)+1) * ((G i).filter (fun B => A ∩ B = I)).card =
        (k.choose (k-I.card) : ℤ) +
          (-1 : ℤ)^(k-I.card) * (if i = 0 then (k : ℤ) else -1) := by
    have eq : a = e i ↔ i = 0 := ⟨fun h => e.injective (h.symm.trans he0.symm),
      fun h => (h ▸ he0).symm⟩
    have hq := hquota I hI hc (e i)
    rw [if_congr eq rfl rfl] at hq
    split_ifs at hq ⊢ <;> convert hq using 2 <;> ring
  by_cases hk4 : k = 4
  · subst k
    refine no_half_four A hA G gsize gpart gproper ?_ ?_
    · intro I hI hc
      have hh := gquota I hI (by omega) 0
      change (5 : ℤ) * ((G 0).filter (fun B => A ∩ B = I)).card =
        (Nat.choose 4 (4-I.card) : ℤ) +
          (-1 : ℤ)^(4-I.card) * (if (0 : Fin 5) = 0 then (4 : ℤ) else -1) at hh
      rw [hc] at hh
      have num : (Nat.choose 4 (4-3) : ℤ) +
          (-1 : ℤ)^(4-3 : ℕ) * (if (0 : Fin 5) = 0 then (4 : ℤ) else -1) = 0 := by decide
      rw [num] at hh
      have hs := (mul_eq_zero.mp hh).resolve_left (by decide : (5 : ℤ) ≠ 0)
      exact_mod_cast hs
    · intro I hI hc i hi
      apply Finset.card_pos.mp
      have hh := gquota I hI (by omega) i
      change (5 : ℤ) * ((G i).filter (fun B => A ∩ B = I)).card =
        (Nat.choose 4 (4-I.card) : ℤ) +
          (-1 : ℤ)^(4-I.card) * (if i = 0 then (4 : ℤ) else -1) at hh
      rw [hc, if_neg hi] at hh
      have num : (Nat.choose 4 (4-2) : ℤ) + (-1 : ℤ)^(4-2 : ℕ) * (-1 : ℤ) = 5 := by decide
      rw [num] at hh
      have hmul : (5 : ℤ) * ((G i).filter (fun B => A ∩ B = I)).card = 5 * 1 := by
        simpa only [mul_one] using hh
      have hs := mul_left_cancel₀ (by decide : (5 : ℤ) ≠ 0) hmul
      rw [show ((G i).filter (fun B => A ∩ B = I)).card = 1 by exact_mod_cast hs]
      decide
  · have h6 : 6 ≤ k := by
      obtain ⟨l,hl⟩ := he
      omega
    exact hprime k h6 hp A hA ⟨G,hAG,gsize,gpart,gproper,gequator,gquota⟩

end OMA.R_Erdos835_johnson_chromaticNumber_R2_H1_R1
