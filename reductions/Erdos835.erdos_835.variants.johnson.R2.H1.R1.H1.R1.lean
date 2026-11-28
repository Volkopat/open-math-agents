import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1

/-! Collapse each connected component for a single missing color to one Boolean choice. -/

open Finset Relation

namespace OMA.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1_H1_R1

/-- Color the smaller Johnson graph. Give each missing-color component a label
and a local bipartition. The cycle test then concerns only the component flips.
The component budget uses the lower bound for the size of a Steiner trade. -/
def H1 : Prop :=
  ∃ (p : ℕ), Nat.Prime p ∧ 17 ≤ p ∧
    ∃ (x y : Fin (2*p-3)), x ≠ y ∧
      ∃ (d : Finset (Fin (2*p-3)) → Fin p)
        (b : Finset (Fin (2*p-3)) → Fin p → Bool)
        (q : Finset (Fin (2*p-3)) → Fin p →
          Fin (2 * (2*p-5).choose (p-3) / 2^(p-3))),
        let V := fun S : Finset (Fin (2*p-3)) => S.card = p-3 ∧ x ∉ S ∧ y ∉ S
        let M := fun S c => ∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ c
        (∀ S, V S → ∀ a ∉ S, ∀ t ∉ S, a ≠ x → a ≠ y → t ≠ x → t ≠ y → a ≠ t →
          d (insert a S) ≠ d (insert t S)) ∧
        (∀ S T, V S → V T → (S ∩ T).card = p-4 → ∀ c, M S c → M T c →
          q S c = q T c ∧ b S c ≠ b T c) ∧
        let r := fun u v : Fin (2 * (2*p-5).choose (p-3) / 2^(p-3)) × Bool =>
          ∃ S c e, V S ∧ M S c ∧ M S e ∧ c ≠ e ∧ q S c = u.1 ∧ q S e = v.1 ∧
            xor (b S c) u.2 ≠ xor (b S e) v.2
        ∀ i, ¬ ReflTransGen r (i, false) (i, true)

/-- A symmetric Boolean implication relation invariant under flipping both bits
has a consistent assignment if its closure never joins opposite literals. -/
def H2 : Prop :=
  ∀ (α : Type) (r : α × Bool → α × Bool → Prop),
    (∀ u v, r u v → r v u) →
    (∀ u v, r u v → r (u.1, !u.2) (v.1, !v.2)) →
    (∀ i, ¬ ReflTransGen r (i, false) (i, true)) →
    ∃ f : α → Bool, ∀ u v, r u v → f u.1 = u.2 → f v.1 = v.2

lemma symmetric_implications : H2 := by
  classical
  intro α r hsym hflip hno
  let reach (u : α × Bool) : Set (α × Bool) := {v | ReflTransGen r u v}
  have rev {u v : α × Bool} (h : ReflTransGen r u v) : ReflTransGen r v u := by
    induction h with
    | refl => exact .refl
    | tail _ hstep ih => exact (ReflTransGen.single (hsym _ _ hstep)).trans ih
  have equal {u v : α × Bool} (h : r u v) : reach u = reach v := by
    ext w
    change ReflTransGen r u w ↔ ReflTransGen r v w
    exact ⟨fun hp => (ReflTransGen.single (hsym _ _ h)).trans hp,
      fun hp => (ReflTransGen.single h).trans hp⟩
  let both (a : α) := reach (a, false) ∪ reach (a, true)
  let key (a : α) : {A : Set (α × Bool) // A.Nonempty} :=
    ⟨both a, ⟨(a, false), Or.inl ReflTransGen.refl⟩⟩
  let rep (a : α) := (key a).property.choose
  have in_both (a : α) : rep a ∈ both a := (key a).property.choose_spec
  let f (a : α) : Bool := decide (rep a ∈ reach (a, true))
  have hf (a : α) (i : Bool) : f a = i ↔ rep a ∈ reach (a, i) := by
    cases i
    · have not_both : rep a ∈ reach (a, false) → rep a ∉ reach (a, true) :=
        fun ha hb => hno a (ha.trans (rev hb))
      simpa only [f, decide_eq_false_iff_not] using
        (show (rep a ∉ reach (a, true)) ↔ rep a ∈ reach (a, false) from
          ⟨fun hn => (in_both a).resolve_right hn, not_both⟩)
    · simp [f]
  refine ⟨f, ?_⟩
  rintro ⟨a, i⟩ ⟨b, j⟩ h hf'
  have hkey : key a = key b := by
    apply Subtype.ext
    change both a = both b
    have h₁ := equal h
    have h₂ := equal (hflip _ _ h)
    cases i <;> cases j <;> simp only [both, Bool.not_false, Bool.not_true] at h₁ h₂ ⊢
    · rw [h₁, h₂]
    · rw [h₁, h₂, Set.union_comm]
    · rw [h₁, h₂, Set.union_comm]
    · rw [h₁, h₂]
  have hrep : rep a = rep b :=
    congrArg (fun s : {A : Set (α × Bool) // A.Nonempty} => s.property.choose) hkey
  apply (hf b j).2
  rw [← hrep, ← equal h]
  exact (hf a i).1 hf'

set_option maxHeartbeats 500000 in
theorem main : H1 → H2 → OMA.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1.H1 := by
  rintro ⟨p, hp, hp17, x, y, hxy, d, b, q, hproper, hcomponent, hcycles⟩ hsolve
  let V := fun S : Finset (Fin (2*p-3)) => S.card = p-3 ∧ x ∉ S ∧ y ∉ S
  let M := fun S c => ∀ a ∉ S, a ≠ x → a ≠ y → d (insert a S) ≠ c
  let r := fun u v : Fin (2 * (2*p-5).choose (p-3) / 2^(p-3)) × Bool =>
    ∃ S c e, V S ∧ M S c ∧ M S e ∧ c ≠ e ∧ q S c = u.1 ∧ q S e = v.1 ∧
      xor (b S c) u.2 ≠ xor (b S e) v.2
  have hsym : ∀ u v, r u v → r v u := by
    rintro u v ⟨S,c,e,hv,hc,he,hne,hcu,hev,hb⟩
    exact ⟨S,e,c,hv,he,hc,hne.symm,hev,hcu,hb.symm⟩
  have hflip : ∀ u v, r u v → r (u.1, !u.2) (v.1, !v.2) := by
    rintro ⟨a,i⟩ ⟨t,j⟩ ⟨S,c,e,hv,hc,he,hne,hcu,hev,hb⟩
    refine ⟨S,c,e,hv,hc,he,hne,hcu,hev,?_⟩
    change xor (b S c) (!i) ≠ xor (b S e) (!j)
    simpa only [Bool.xor_not, ne_eq, Bool.not_inj_iff] using hb
  obtain ⟨f, hf⟩ := hsolve _ r hsym hflip hcycles
  let side := fun S c => xor (b S c) (f (q S c))
  refine ⟨p, hp, hp17, x, y, hxy, d, ?_, side, ?_, ?_⟩
  · intro S hS hx hy
    exact hproper S ⟨hS,hx,hy⟩
  · intro S hS hx hy c e hc he hne hs
    have hrs : r (q S c, f (q S c)) (q S e, !(f (q S e))) := by
      refine ⟨S,c,e,⟨hS,hx,hy⟩,hc,he,hne,rfl,rfl,?_⟩
      change xor (b S c) (f (q S c)) ≠ xor (b S e) (!(f (q S e)))
      change xor (b S c) (f (q S c)) = xor (b S e) (f (q S e)) at hs
      rw [hs, Bool.xor_not]
      exact fun he => (Bool.eq_not_self _).mp he
    have h := hf _ _ hrs rfl
    exact (Bool.eq_not_self _).mp h
  · intro U hU hx hy a ha t ht hax hay htx hty hat c hc he
    have hVA : V (insert a U) := by
      refine ⟨?_, by simp [hax.symm,hx], by simp [hay.symm,hy]⟩
      rw [card_insert_of_notMem ha, hU]
      omega
    have hVT : V (insert t U) := by
      refine ⟨?_, by simp [htx.symm,hx], by simp [hty.symm,hy]⟩
      rw [card_insert_of_notMem ht, hU]
      omega
    have hI : insert a U ∩ insert t U = U := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      grind
    obtain ⟨hq, hb⟩ := hcomponent _ _ hVA hVT (by rwa [hI]) c hc he
    change xor (b (insert a U) c) (f (q (insert a U) c)) ≠
      xor (b (insert t U) c) (f (q (insert t U) c))
    rw [hq]
    exact fun heq => hb (Bool.xor_left_inj.mp heq)

-- The incidence and inclusion-exclusion argument is adapted from PR 10320
-- by @VestigeClub. Here the two families can cover any face with equal multiplicity.
section

variable {α : Type*} [DecidableEq α]

-- Count a block J.filter (once ⊆ ·) for each of its elements outside J.
lemma extension_count [Fintype α] {Q : Finset (Finset α)} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (J : Finset α) :
    ∑ a ∈ univ \ J, (Q.filter ((insert a J) ⊆ ·)).card =
      (k - J.card) * (Q.filter (J ⊆ ·)).card := by
  have hex (a : α) :
      Q.filter (insert a J ⊆ ·) = (Q.filter (J ⊆ ·)).filter (a ∈ ·) := by
    ext B
    simp only [mem_filter, insert_subset_iff]
    tauto
  calc
    _ = ∑ a ∈ univ \ J, ∑ B ∈ Q.filter (J ⊆ ·), if a ∈ B then (1 : ℕ) else 0 := by
      apply sum_congr rfl
      intro a _
      rw [hex, ← sum_filter]
      simp
    _ = ∑ B ∈ Q.filter (J ⊆ ·), ∑ a ∈ univ \ J, if a ∈ B then (1 : ℕ) else 0 := sum_comm
    _ = ∑ _B ∈ Q.filter (J ⊆ ·), (k - J.card) := by
      apply sum_congr rfl
      intro B hB
      have hJB := (mem_filter.mp hB).2
      have hBc := hQ B (mem_filter.mp hB).1
      have hsd := card_sdiff_add_card_eq_card hJB
      rw [← sum_filter, show ((univ \ J).filter (· ∈ B)) = B \ J by
        ext a
        simp only [mem_filter, mem_sdiff, mem_univ, true_and, and_comm]]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      change (B \ J).card = k - J.card
      rw [← hBc, ← hsd, Nat.add_sub_cancel]
    _ = _ := by simp [mul_comm]

lemma proper_counts [Fintype α] {Q R : Finset (Finset α)} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (hR : ∀ B ∈ R, B.card = k)
    (hcov : ∀ J : Finset α, J.card = k - 1 →
      (Q.filter (J ⊆ ·)).card = (R.filter (J ⊆ ·)).card)
    (J : Finset α) (hJ : J.card < k) : (Q.filter (J ⊆ ·)).card = (R.filter (J ⊆ ·)).card := by
  let P (d : ℕ) := ∀ T : Finset α, k - T.card = d → T.card < k →
    (Q.filter (T ⊆ ·)).card = (R.filter (T ⊆ ·)).card
  suffices ∀ d, P d from this (k - J.card) J rfl hJ
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro T hTd hTk
    by_cases hOne : d = 1
    · exact hcov T (by omega)
    have hsum :
        ∑ a ∈ (univ \ T), (Q.filter ((insert a T) ⊆ ·)).card =
          ∑ a ∈ (univ \ T), (R.filter ((insert a T) ⊆ ·)).card := by
      apply sum_congr rfl
      intro a ha
      have hna := (mem_sdiff.mp ha).2
      have hcard := card_insert_of_notMem hna
      exact ih (k - (insert a T).card) (by omega) (insert a T) rfl (by omega)
    rw [extension_count hQ, extension_count hR] at hsum
    exact (Nat.mul_left_cancel_iff (by omega : 0 < k - T.card)).mp hsum

lemma alternating_subsets (X : Finset α) :
    ∑ J ∈ X.powerset, (-1 : ℤ) ^ J.card = if X = ∅ then 1 else 0 := by
  have hx := (Finset.prod_add (fun _ : α => (-1 : ℤ)) (fun _ => (1 : ℤ)) X).symm
  simp only [prod_const, one_pow, mul_one, neg_add_cancel] at hx
  by_cases h : X = ∅
  · subst X
    simp
  · rw [if_neg h, hx]
    exact zero_pow (by simpa using h)

lemma alternating_counts (Q : Finset (Finset α)) (A I : Finset α)
    (hI : I ⊆ A) :
    ∑ J ∈ (A \ I).powerset, (-1 : ℤ) ^ J.card * ((Q.filter ((I ∪ J) ⊆ ·)).card : ℤ) =
      ((Q.filter (fun B => A ∩ B = I)).card : ℤ) := by
  let R := Q.filter (I ⊆ ·)
  have hfilter (J : Finset α) :
      Q.filter (I ∪ J ⊆ ·) = R.filter (J ⊆ ·) := by
    ext B
    simp only [R, mem_filter, union_subset_iff]
    tauto
  have hzero {B : Finset α} (hB : B ∈ R) : (A \ I) ∩ B = ∅ ↔ A ∩ B = I := by
    have hIB : I ⊆ B := (mem_filter.mp hB).2
    constructor
    · intro hempty
      apply Subset.antisymm
      · intro x hx
        by_contra hn
        obtain ⟨ha, hb⟩ := mem_inter.mp hx
        have hm : x ∈ (A \ I) ∩ B := mem_inter.mpr ⟨mem_sdiff.mpr ⟨ha, hn⟩, hb⟩
        simp [hempty] at hm
      · exact subset_inter hI hIB
    · intro heq
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases mem_inter.mp hx with ⟨hd, hb⟩
      rcases mem_sdiff.mp hd with ⟨ha, hnot⟩
      exact hnot (heq ▸ mem_inter.mpr ⟨ha, hb⟩)
  calc
    _ = ∑ J ∈ (A \ I).powerset, ∑ B ∈ R, if J ⊆ B then (-1 : ℤ) ^ J.card else 0 := by
      apply sum_congr rfl
      intro J _
      rw [hfilter, ← sum_filter]
      simp [mul_comm]
    _ = ∑ B ∈ R, ∑ J ∈ (A \ I).powerset, if J ⊆ B then (-1 : ℤ) ^ J.card else 0 :=
      sum_comm
    _ = ∑ B ∈ R, if A ∩ B = I then (1 : ℤ) else 0 := by
      apply sum_congr rfl
      intro B hB
      rw [← sum_filter, show ((A \ I).powerset.filter (· ⊆ B)) = ((A \ I) ∩ B).powerset by
        ext J
        simp only [mem_filter, mem_powerset, Finset.subset_inter_iff], alternating_subsets]
      simp only [hzero hB]
    _ = _ := by
      rw [← sum_filter, show R.filter (fun B => A ∩ B = I) = Q.filter (fun B => A ∩ B = I) by
        ext B
        simp only [R, mem_filter, and_assoc]
        exact and_congr_right (fun _ => and_iff_right_of_imp (fun e => e ▸ inter_subset_right))]
      simp

lemma top_count {Q : Finset (Finset α)} {A : Finset α} {k : ℕ}
    (hQ : ∀ B ∈ Q, B.card = k) (hA : A.card = k) :
    ((Q.filter (A ⊆ ·)).card : ℤ) = if A ∈ Q then 1 else 0 := by
  have hf : Q.filter (A ⊆ ·) = Q.filter (· = A) := by
    ext B
    simp only [mem_filter]
    exact and_congr_right fun hb =>
      ⟨fun h => (eq_of_subset_of_card_le h (by rw [hQ B hb, hA])).symm,
        fun h => h ▸ Subset.rfl⟩
  rw [hf]
  by_cases h : A ∈ Q
  · rw [if_pos h, show Q.filter (· = A) = {A} by
      ext B
      simp only [mem_filter, mem_singleton]
      exact ⟨And.right, fun e => ⟨e.symm ▸ h, e⟩⟩]
    simp
  · rw [if_neg h, show Q.filter (· = A) = ∅ by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hBQ, rfl⟩ := mem_filter.mp hB
      exact h hBQ]
    simp

/-- Signed intersection counts for the two halves of a Steiner trade. -/
lemma trade_trace [Fintype α] {F G : Finset (Finset α)} {k : ℕ}
    (hF : ∀ B ∈ F, B.card = k) (hG : ∀ B ∈ G, B.card = k)
    (hc : ∀ J : Finset α, J.card = k - 1 →
      (F.filter (J ⊆ ·)).card = (G.filter (J ⊆ ·)).card)
    (A I : Finset α) (hA : A.card = k) (hI : I ⊆ A) :
    ((F.filter (fun B => A ∩ B = I)).card : ℤ) - (G.filter (fun B => A ∩ B = I)).card =
      (-1 : ℤ)^(k-I.card) * ((if A ∈ F then 1 else 0) - (if A ∈ G then 1 else 0)) := by
  rw [← alternating_counts F A I hI, ← alternating_counts G A I hI, ← sum_sub_distrib]
  rw [sum_eq_single (A \ I)]
  · rw [← mul_sub_left_distrib, union_sdiff_of_subset hI, top_count hF hA, top_count hG hA]
    congr 2
    have := card_sdiff_add_card_eq_card hI
    omega
  · intro J hJ hne
    have hs := mem_powerset.mp hJ
    have hu : I ∪ J ⊆ A := union_subset hI (hs.trans sdiff_subset)
    have hlt : (I ∪ J).card < k := by
      rw [← hA]
      apply card_lt_card
      refine Finset.ssubset_iff_subset_ne.mpr ⟨hu, ?_⟩
      intro heq
      apply hne
      apply Subset.antisymm hs
      intro x hx
      obtain ⟨hxA, hxI⟩ := mem_sdiff.mp hx
      exact (mem_union.mp (heq.symm ▸ hxA)).resolve_left hxI
    rw [proper_counts hF hG hc _ hlt, sub_self]
  · intro hm
    exact (hm (mem_powerset.mpr Subset.rfl)).elim

/-- A nonempty Steiner trade on k-subsets has at least 2^k distinct blocks. -/
lemma steiner_trade_size [Fintype α] {F G : Finset (Finset α)} {k : ℕ}
    (hF : ∀ B ∈ F, B.card = k) (hG : ∀ B ∈ G, B.card = k)
    (hc : ∀ J : Finset α, J.card = k - 1 →
      (F.filter (J ⊆ ·)).card = (G.filter (J ⊆ ·)).card)
    {A : Finset α} (hAF : A ∈ F) (hAG : A ∉ G) :
    2^k ≤ (F ∪ G).card := by
  have sub : A.powerset ⊆ (F ∪ G).image (A ∩ ·) := by
    intro I hI
    have ht := trade_trace hF hG hc A I (hF A hAF) (mem_powerset.mp hI)
    have hn : ((F.filter (fun B => A ∩ B = I)).card : ℤ) -
        (G.filter (fun B => A ∩ B = I)).card ≠ 0 := by
      rw [ht]
      simp [hAF, hAG]
    by_contra h
    have empty (S : Finset (Finset α)) (hsub : S ⊆ F ∪ G) :
        S.filter (fun B => A ∩ B = I) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro B hB
      obtain ⟨hBS, hBI⟩ := mem_filter.mp hB
      exact h (mem_image.mpr ⟨B, hsub hBS, hBI⟩)
    rw [empty F subset_union_left, empty G subset_union_right] at hn
    simp at hn
  have hpow : A.powerset.card = 2^k := by rw [card_powerset, hF A hAF]
  rw [← hpow]
  exact (card_le_card sub).trans card_image_le

/-- Each nonempty component of a bipartite family with zero or two blocks
at every codimension-one face is itself a Steiner trade. -/
lemma component_volume [Fintype α] {D C : Finset (Finset α)} {k : ℕ} (hk : 0 < k)
    (hD : ∀ S ∈ D, S.card = k)
    (hfaces : ∀ U : Finset α, U.card + 1 = k →
      (D.filter (U ⊆ ·)).card = 0 ∨ (D.filter (U ⊆ ·)).card = 2)
    (side : Finset α → Bool)
    (hside : ∀ S ∈ D, ∀ T ∈ D, (S ∩ T).card + 1 = k → side S ≠ side T)
    (hCD : C ⊆ D)
    (hclosed : ∀ S ∈ C, ∀ T ∈ D, (S ∩ T).card + 1 = k → T ∈ C)
    (hn : C.Nonempty) : 2^k ≤ C.card := by
  classical
  obtain ⟨A, hA⟩ := hn
  let F := C.filter (fun S => side S = side A)
  let G := C.filter (fun S => side S ≠ side A)
  have hF : F ⊆ C := filter_subset _ _
  have hG : G ⊆ C := filter_subset _ _
  have counts (U : Finset α) (hU : U.card = k-1) :
      (F.filter (U ⊆ ·)).card = (G.filter (U ⊆ ·)).card := by
    by_cases hC : (C.filter (U ⊆ ·)).Nonempty
    · obtain ⟨S, hS⟩ := hC
      obtain ⟨hSC, hUS⟩ := mem_filter.mp hS
      have hSD := hCD hSC
      have hSD' : S ∈ D.filter (U ⊆ ·) := mem_filter.mpr ⟨hSD, hUS⟩
      have hcard := (hfaces U (by omega)).resolve_left (card_pos.mpr ⟨S, hSD'⟩).ne'
      obtain ⟨T, W, hTW, hEq⟩ := card_eq_two.mp hcard
      have hS' : S = T ∨ S = W := by simpa [hEq] using hSD'
      have hTD : T ∈ D.filter (U ⊆ ·) := by simp [hEq]
      have hWD : W ∈ D.filter (U ⊆ ·) := by simp [hEq]
      have hInter : (T ∩ W).card + 1 = k := by
        have hle := card_le_card (subset_inter (mem_filter.mp hTD).2 (mem_filter.mp hWD).2)
        have hlt : (T ∩ W).card < k := by
          rw [← hD T (mem_filter.mp hTD).1]
          apply card_lt_card
          refine Finset.ssubset_iff_subset_ne.mpr ⟨inter_subset_left, ?_⟩
          intro e
          exact hTW (eq_of_subset_of_card_le (e ▸ inter_subset_right) (by
            rw [hD W (mem_filter.mp hWD).1, hD T (mem_filter.mp hTD).1]))
        omega
      have hTC : T ∈ C := by
        rcases hS' with hST | hSW
        · exact hST ▸ hSC
        · exact hclosed W (hSW ▸ hSC) T (mem_filter.mp hTD).1
            (by simpa only [inter_comm] using hInter)
      have hWC : W ∈ C := hclosed T hTC W (mem_filter.mp hWD).1 hInter
      have hCEq : C.filter (U ⊆ ·) = {T,W} := by
        apply Subset.antisymm
        · rw [← hEq]
          exact fun t ht => mem_filter.mpr ⟨hCD (mem_filter.mp ht).1, (mem_filter.mp ht).2⟩
        · apply insert_subset (mem_filter.mpr ⟨hTC, (mem_filter.mp hTD).2⟩)
          exact singleton_subset_iff.mpr (mem_filter.mpr ⟨hWC, (mem_filter.mp hWD).2⟩)
      have hdiff := hside T (mem_filter.mp hTD).1 W (mem_filter.mp hWD).1 hInter
      have feq : F.filter (U ⊆ ·) = ({T,W} : Finset (Finset α)).filter (fun S => side S = side A) := by
        rw [← hCEq]
        ext S
        simp only [F, mem_filter]
        tauto
      have geq : G.filter (U ⊆ ·) = ({T,W} : Finset (Finset α)).filter (fun S => side S ≠ side A) := by
        rw [← hCEq]
        ext S
        simp only [G, mem_filter]
        tauto
      rw [feq, geq]
      have flips (a b c : Bool) (h : a ≠ b) :
          (if a = c then 1 else 0 : ℕ) + (if b = c then 1 else 0) =
            (if a ≠ c then 1 else 0 : ℕ) + (if b ≠ c then 1 else 0) := by
        revert a b c
        decide
      have hcard_filter (P : Finset α → Prop) [DecidablePred P] :
          (({T,W} : Finset (Finset α)).filter P).card =
            (if P T then 1 else 0) + (if P W then 1 else 0) := by
        rw [filter_insert, filter_singleton]
        by_cases ht : P T <;> by_cases hw : P W <;> simp [ht, hw, hTW]
      rw [hcard_filter, hcard_filter]
      exact flips _ _ _ hdiff
    · have e : C.filter (U ⊆ ·) = ∅ := by simpa only [nonempty_iff_ne_empty, not_not] using hC
      have small (B : Finset (Finset α)) (hB : B ⊆ C) :
          B.filter (U ⊆ ·) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro S hS
        have hs := mem_filter.mpr ⟨hB (mem_filter.mp hS).1, (mem_filter.mp hS).2⟩
        simp [e] at hs
      rw [small F hF, small G hG]
  have hsize := steiner_trade_size (A := A)
    (fun S hS => hD S (hCD (hF hS))) (fun S hS => hD S (hCD (hG hS)))
    counts (by simp [F,hA]) (by simp [G])
  exact hsize.trans (card_le_card (union_subset hF hG))

end

/-- Bound the number of labels when each fiber contains at least m elements. -/
lemma component_count {α β : Type*} [DecidableEq β]
    (L : Finset α) (label : α → β) {m N : ℕ} (hm : 0 < m)
    (hN : L.card ≤ N)
    (h : ∀ j ∈ L.image label, m ≤ (L.filter (fun a => label a = j)).card) :
    (L.image label).card ≤ N / m := by
  apply (Nat.le_div_iff_mul_le hm).2
  calc
    _ = ∑ _j ∈ L.image label, m := by simp
    _ ≤ ∑ j ∈ L.image label, (L.filter (fun a => label a = j)).card :=
      Finset.sum_le_sum h
    _ = L.card := (Finset.card_eq_sum_card_image label L).symm
    _ ≤ N := hN

end OMA.R_Erdos835_erdos_835_variants_johnson_R2_H1_R1_H1_R1
