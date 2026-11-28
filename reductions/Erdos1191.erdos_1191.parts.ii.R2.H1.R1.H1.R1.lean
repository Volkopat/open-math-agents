import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1

/-!
# Thinning repeated differences by their positions

Associate the half-open interval `[v,u)` with a repeated positive difference
`u-v` in the upper block. A bound on the number of pairwise disjoint such
intervals gives a large subset avoiding all of them. An additional sparse
list of exceptional lengths can be kept. The resulting criterion implies the
exact sparse-overlap hypothesis in the reduction for Erdős 1191(ii).
-/

-- Credit: @ellisjr

namespace OMA.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1_H1_R1
open Finset

/-- Each long collision either has one of the listed exceptional lengths
or spans a listed interval in the upper block. The first list is sparse per
mark and every disjoint family from the second list is polynomial in `j`. -/
def H1 : Prop :=
  ∃ d k c J : ℕ, ∀ N : ℕ, ∃ B : ℕ → Finset ℕ,
    (∀ j, B j ⊆ Ico (2^j) (2^(j+1))) ∧ (∀ j, IsSidon (B j : Set ℕ)) ∧
    ∀ j, J ≤ j → j ≤ N →
      2^j ≤ (B j).card^2 * (j+1)^(2*(d+1)) ∧
      ∃ (F : Finset ℕ) (E : Finset (ℕ × ℕ)),
        F.card ≤ (B j).card * (j+1)^k ∧
        (∀ P ⊆ E, (∀ e ∈ P, ∀ f ∈ P, e ≠ f → e.2 ≤ f.1 ∨ f.2 ≤ e.1) → P.card < (j+1)^c) ∧
        ∀ i, i<j → ∀ a∈B i, ∀ b∈B i, ∀ u∈B j, ∀ v∈B j,
          b<a → v<u → a-b=u-v → 2^(j/2)*(j+1)^2 ≤ u-v → u-v ∈ F ∨ (v,u) ∈ E

/-- A bound on disjoint bad intervals gives a large set avoiding all the listed pairs. -/
def H2 : Prop :=
  ∀ (S : Finset ℕ) (E : Finset (ℕ × ℕ)) (q : ℕ),
    (∀ P ⊆ E, (∀ e ∈ P, ∀ f ∈ P, e ≠ f → e.2 ≤ f.1 ∨ f.2 ≤ e.1) → P.card < q) →
    ∃ T ⊆ S, S.card ≤ T.card * q ∧ ∀ v ∈ T, ∀ u ∈ T, v < u → (v,u) ∉ E

/-- Color each mark by the maximum number of disjoint intervals ending by that mark. -/
lemma finite_interval_thinning : H2 := by
  intro S E q hpack
  classical
  let apart := fun P : Finset (ℕ × ℕ) =>
    ∀ e ∈ P, ∀ f ∈ P, e ≠ f → e.2 ≤ f.1 ∨ f.2 ≤ e.1
  change (∀ P ⊆ E, apart P → P.card < q) at hpack
  let allowedAt := fun x : ℕ => E.powerset.filter (fun P => apart P ∧ ∀ e ∈ P, e.2 ≤ x)
  have empty_mem (x : ℕ) : (∅ : Finset (ℕ × ℕ)) ∈ allowedAt x := by simp [allowedAt, apart]
  choose P hp hmax using fun x => exists_max_image (allowedAt x) Finset.card ⟨∅, empty_mem x⟩
  have spec (x : ℕ) : P x ⊆ E ∧ apart (P x) ∧ ∀ e ∈ P x, e.2 ≤ x := by
    simpa only [allowedAt, mem_filter, mem_powerset] using hp x
  let rank := fun x : ℕ => (P x).card
  have hbound (x : ℕ) : rank x < q := hpack _ (spec x).1 (spec x).2.1
  have rise {v u : ℕ} (hvu : v < u) (he : (v,u) ∈ E) : rank v < rank u := by
    let e := (v,u)
    have hnew : e ∉ P v := fun h => (not_le_of_gt hvu) ((spec v).2.2 e h)
    have hgood : insert e (P v) ∈ allowedAt u := by
      apply mem_filter.mpr
      refine ⟨mem_powerset.mpr (insert_subset he (spec v).1), ?_, ?_⟩
      · intro a ha b hb hn
        rcases mem_insert.mp ha with rfl | ha
        · rcases mem_insert.mp hb with rfl | hb
          · exact (hn rfl).elim
          · exact Or.inr ((spec v).2.2 b hb)
        · rcases mem_insert.mp hb with rfl | hb
          · exact Or.inl ((spec v).2.2 a ha)
          · exact (spec v).2.1 a ha b hb hn
      · intro a ha
        rcases mem_insert.mp ha with rfl | ha
        · exact le_rfl
        · exact ((spec v).2.2 _ ha).trans hvu.le
    have hle := hmax u _ hgood
    rw [card_insert_of_notMem hnew] at hle
    exact hle
  let fiber := fun k : ℕ => S.filter (fun x => rank x = k)
  have hq : 0 < q := Nat.zero_lt_of_lt (hbound 0)
  obtain ⟨k, _, hk⟩ := exists_max_image (range q) (fun y => (fiber y).card) ⟨0, mem_range.mpr hq⟩
  refine ⟨fiber k, filter_subset _ _, ?_, ?_⟩
  · calc
      S.card = ∑ y ∈ range q, (fiber y).card := card_eq_sum_card_fiberwise
        (f := rank) (fun x _ => mem_range.mpr (hbound x))
      _ ≤ ∑ _y ∈ range q, (fiber k).card := sum_le_sum hk
      _ = _ := by simp [Nat.mul_comm]
  · intro v hv u hu hvu he
    have hs := rise hvu he
    have hv' := (mem_filter.mp hv).2
    have hu' := (mem_filter.mp hu).2
    omega

/-- Thinning the upper endpoints at each scale gives the specified sparse family. -/
theorem main : H1 → H2 → OMA.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1.H1 := by
  intro h hthin
  classical
  obtain ⟨d,k,c,J,hfam⟩ := h
  refine ⟨d+c,c+k,J,fun N => ?_⟩
  obtain ⟨B, hloc, hsid, hdata⟩ := hfam N
  have sel (j : ℕ) : ∃ T ⊆ B j,
      ∀ (_ : J ≤ j) (_ : j ≤ N),
        2^j ≤ T.card^2 * (j+1)^(2*(d+c+1)) ∧
        ∃ F : Finset ℕ, F.card ≤ T.card * (j+1)^(c+k) ∧
          ∀ i, i<j → ∀ a∈B i, ∀ b∈B i, ∀ u∈T, ∀ v∈T,
            b<a → v<u → a-b=u-v → 2^(j/2)*(j+1)^2 ≤ u-v → u-v ∈ F := by
    by_cases hj : J ≤ j ∧ j ≤ N
    · obtain ⟨hd,F,E,hF,hP,hcross⟩ := hdata j hj.1 hj.2
      obtain ⟨T,hsub,ht,hsafe⟩ := hthin (B j) E ((j+1)^c) hP
      refine ⟨T,hsub,fun _ _ => ⟨?_,F,?_,?_⟩⟩
      · calc
          2^j ≤ (B j).card^2 * (j+1)^(2*(d+1)) := hd
          _ ≤ (T.card*(j+1)^c)^2 * (j+1)^(2*(d+1)) :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left ht 2)
          _ = _ := by rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add]; congr 2; ring
      · calc
          F.card ≤ (B j).card*(j+1)^k := hF
          _ ≤ (T.card*(j+1)^c)*(j+1)^k := Nat.mul_le_mul_right _ ht
          _ = _ := by rw [mul_assoc, ← pow_add]
      · intro i hij a ha b hb u hu v hv hba hvu heq hlong
        exact (hcross i hij a ha b hb u (hsub hu) v (hsub hv) hba hvu heq hlong).resolve_right
          (hsafe v hv u hu hvu)
    · exact ⟨∅, empty_subset _, fun hlo hhi => (hj ⟨hlo,hhi⟩).elim⟩
  choose T hsub hT using sel
  refine ⟨T,fun j => (hsub j).trans (hloc j),fun j => Set.IsSidon.subset (hsid j) (hsub j),?_⟩
  intro j hj hjN
  obtain ⟨hd,F,hF,hsep⟩ := hT j hj hjN
  refine ⟨hd,F,hF,?_⟩
  intro i hij a ha b hb
  exact hsep i hij a (hsub i ha) b (hsub i hb)

theorem of_interval_packing (h : H1) : OMA.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1.H1 := main h finite_interval_thinning

/-- Every cut can remove only those previously present directed gaps whose
endpoints straddle the cut. Sidon rulers supply the uniqueness of lengths. -/
theorem rotation_lower_bound (T c : ℕ) (E : Finset (ℕ × ℕ)) (F : Finset ℕ)
    (hpos : ∀ e ∈ E, e.1 < e.2)
    (huniq : Set.InjOn (fun e : ℕ × ℕ => e.2-e.1) (E : Set (ℕ × ℕ)))
    (hF : let rotate := fun x : ℕ => if x < c then x + (T-c) else x-c
      ∀ e ∈ E, rotate e.1 < rotate e.2 → rotate e.2 - rotate e.1 ∈ F) :
    E.card ≤ F.card + (E.filter (fun e => e.1 < c ∧ c ≤ e.2)).card := by
  classical
  dsimp only at hF
  let hit := E.filter (fun e => e.1 < c ∧ c ≤ e.2)
  have hleft : (E \ hit).card ≤ F.card := by
    apply card_le_card_of_injOn (fun e : ℕ × ℕ => e.2-e.1)
    · intro e he
      change e.2 - e.1 ∈ F
      obtain ⟨he, hmiss⟩ := mem_sdiff.mp he
      have hord := hpos e he
      have hsep : ¬(e.1<c ∧ c≤e.2) := fun h => hmiss (mem_filter.mpr ⟨he,h⟩)
      by_cases h : e.1 < c
      · have h' : e.2 < c := by omega
        have hy := hF e he (by simp only [if_pos h, if_pos h']; omega)
        simpa only [if_pos h, if_pos h', Nat.add_sub_add_right] using hy
      · have h' : ¬ e.2 < c := by omega
        have hy := hF e he (by simp only [if_neg h, if_neg h']; omega)
        have hd : (e.2-c)-(e.1-c) = e.2-e.1 := by omega
        simpa only [if_neg h, if_neg h', hd] using hy
    · exact fun a ha b hb heq => huniq (mem_sdiff.mp ha).1 (mem_sdiff.mp hb).1 heq
  calc
    E.card = (E \ hit).card + hit.card := (card_sdiff_add_card_eq_card (filter_subset _ _)).symm
    _ ≤ _ := Nat.add_le_add_right hleft _

/-- Among all `T` starting positions of an oriented circular gap `d`,
exactly `T-d` give ordinary signed difference `+d`. -/
theorem unwrapped_count {T d : ℕ} (hd : 0 < d) (hdT : d < T) :
    ((range T).filter (fun x => ((x+d) % T)-x = d)).card = T-d := by
  have he : (range T).filter (fun x => ((x+d) % T)-x = d) = range (T-d) := by
    ext x
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨hx, hv⟩
      by_contra! h
      have hlarge : T ≤ x+d := by omega
      have hsmall : x+d-T < T := by omega
      rw [Nat.mod_eq_sub_mod hlarge, Nat.mod_eq_of_lt hsmall] at hv
      omega
    · intro h
      have hx : x+d < T := by omega
      rw [Nat.mod_eq_of_lt hx]
      omega
  rw [he, card_range]


lemma same_directed_endpoints (Y : Finset ℕ) (sidon : IsSidon (Y : Set ℕ))
    {a b c d : ℕ} (ha : a∈Y) (hb : b∈Y) (hc : c∈Y) (hd : d∈Y) (ne : a≠b)
    (gap : (a : ℤ)-b=(c : ℤ)-d) : a=c ∧ b=d := by
  have eq : a+d=c+b := by omega
  rcases sidon a ha c hc d hd b hb eq with yes|no
  · exact ⟨yes.1,yes.2.symm⟩
  · exact (ne no.1).elim

/-- If the two distinct left endpoints and two distinct right endpoints
belong to one Sidon ruler, their two signed gaps determine them. In
particular the gap in lengths and the signed gap between starts identify
the unordered pair of lengths. One may subtract any predicted separation
depending only on the gap in lengths. -/
theorem count_interval_positions (Y : Finset ℕ) (sidon : IsSidon (Y : Set ℕ))
    (R : Finset (ℕ×ℕ)) (start finish : ℕ → ℕ) (center : ℕ → ℤ) (E : Finset (ℕ×ℤ))
    (hit : ∀ r∈R, r.1<r.2 ∧ start r.1∈Y ∧ start r.2∈Y ∧ finish r.1∈Y ∧ finish r.2∈Y ∧
      start r.1+r.1=finish r.1 ∧ start r.2+r.2=finish r.2 ∧
      start r.1≠start r.2 ∧ finish r.1≠finish r.2)
    (window : ∀ r∈R, (r.2-r.1,(start r.2 : ℤ)-start r.1-center (r.2-r.1))∈E) :
    R.card≤E.card := by
  apply card_le_card_of_injOn (fun r => (r.2-r.1,(start r.2 : ℤ)-start r.1-center (r.2-r.1)))
  · exact window
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd eq
    obtain ⟨ab,sa,sb,fa,fb,ea,eb,ns,nf⟩ := hit _ hab
    obtain ⟨cd,sc,sd,fc,fd,ec,ed,_,_⟩ := hit _ hcd
    obtain ⟨len,place⟩ := Prod.mk.inj eq
    dsimp only at *
    rw [len] at place
    have left := same_directed_endpoints Y sidon sa sb sc sd ns (by omega)
    have right := same_directed_endpoints Y sidon fa fb fc fd nf (by omega)
    apply Prod.ext <;> dsimp only <;> omega

lemma dyadic_index {k j : ℕ} (positive : 0<k) (bound : k<2^j) :
    ∃ h<j, 2^h≤k ∧ k<2^(h+1) := by
  induction j with
  | zero => simp at bound; omega
  | succ j ih =>
    by_cases small : k<2^j
    · obtain ⟨h,hj,bx,by'⟩ := ih small
      exact ⟨h,by omega,bx,by'⟩
    · exact ⟨j,Nat.lt_succ_self _,by omega,bound⟩

/-- The integer pairs (w,t) with 0<w<2^j and w*(1+|t|)≤B fit in
a set of size at most 2*j*B. Each dyadic range for w costs at most 2B. -/
theorem divisor_window (j B : ℕ) : ∃ E : Finset (ℕ×ℤ), E.card≤2*j*B ∧
    ∀ (w : ℕ) (t : ℤ), 0<w → w<2^j → w*(1+t.natAbs)≤B → (w,t)∈E := by
  let cell := fun h : ℕ => (Ico (2^h) (2^(h+1)) : Finset ℕ) ×ˢ
    (Ico (-(B/2^h : ℕ) : ℤ) ((B/2^h : ℕ) : ℤ))
  refine ⟨(range j).biUnion cell,?_,?_⟩
  · have size (h : ℕ) : (cell h).card≤2*B := by
      let D := B/2^h
      have l : (Ico (2^h) (2^(h+1)) : Finset ℕ).card=2^h := by
        rw [Nat.card_Ico,pow_succ]; omega
      have r : (Ico (-(D : ℤ)) (D : ℤ)).card=2*D := by rw [Int.card_Ico]; omega
      have cost : D*2^h≤B := Nat.div_mul_le_self .. 
      change ((Ico (2^h) (2^(h+1)) : Finset ℕ) ×ˢ Ico (-(D : ℤ)) (D : ℤ)).card≤2*B
      rw [card_product,l,r]; nlinarith only [cost]
    calc
      _ ≤ ∑ h∈range j,(cell h).card := card_biUnion_le
      _ ≤ ∑ _h∈range j,2*B := sum_le_sum (fun h _ => size h)
      _ = _ := by simp; ring
  · intro w t pos hi paid
    obtain ⟨h,hj,low,high⟩ := dyadic_index pos hi
    have small : (1+t.natAbs)*2^h≤B := (Nat.mul_le_mul_left (1+t.natAbs) low).trans
      ((Nat.mul_comm ..).le.trans paid)
    have abs := (Nat.le_div_iff_mul_le (show 0<(2 : ℕ)^h by positivity)).mpr small
    have both : -(t.natAbs : ℤ)≤t ∧ t≤(t.natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact ⟨neg_abs_le _,le_abs_self _⟩
    exact mem_biUnion.mpr ⟨h,mem_range.mpr hj,mem_product.mpr ⟨mem_Ico.mpr ⟨low,high⟩,
      mem_Ico.mpr ⟨by omega,by omega⟩⟩⟩

/-- At every horizon, the same-label pairs in this range satisfy a
square-root-size bound on taking B equal to the upper cap times any
fixed polynomial. The predicted separation may vary with the length gap. -/
theorem product_position_bound (j B : ℕ) (Y : Finset ℕ) (sidon : IsSidon (Y : Set ℕ))
    (R : Finset (ℕ×ℕ)) (start finish : ℕ → ℕ) (center : ℕ → ℤ)
    (hit : ∀ r∈R, r.1<r.2 ∧ start r.1∈Y ∧ start r.2∈Y ∧ finish r.1∈Y ∧ finish r.2∈Y ∧
      start r.1+r.1=finish r.1 ∧ start r.2+r.2=finish r.2 ∧
      start r.1≠start r.2 ∧ finish r.1≠finish r.2)
    (paid : ∀ r∈R, r.2-r.1<2^j ∧ (r.2-r.1)*(1+((start r.2 : ℤ)-start r.1-center (r.2-r.1)).natAbs)≤B) :
    R.card≤2*j*B := by
  obtain ⟨E,size,contains⟩ := divisor_window j B
  apply (count_interval_positions Y sidon R start finish center E hit ?_).trans size
  exact fun r hr => contains _ _ (Nat.sub_pos_of_lt (hit r hr).1) (paid r hr).1 (paid r hr).2

end OMA.R_Erdos1191_erdos_1191_parts_ii_R2_H1_R1_H1_R1
