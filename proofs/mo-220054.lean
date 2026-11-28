import OMAStatements.S_mo_220054

namespace OMA.S_mo_220054

noncomputable def countTwo {n k} (c : Fin k → V n) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Finset (Fin k)))).filter
    (fun π => Good c π ∧ π.card=2)).card

noncomputable def countAway {n k} (c : Fin k → V n) (a : Fin k) : ℕ := by
  classical
  exact ((Finset.univ : Finset (Finset (Fin k))).filter
    (fun b => a ∉ b ∧ ∑ i ∈ b,c i=0)).card

end OMA.S_mo_220054

namespace OMA.S_mo_220054

open Finset

private def eps (u : ZMod 2) : ℚ := if u=0 then 1 else -1

private lemma eps_add (u v : ZMod 2) : eps (u+v)=eps u*eps v := by
  have cases' (z : ZMod 2) : z=0 ∨ z=1 := by
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  have h2 : (1:ZMod 2)+1=0 := by decide
  rcases cases' u with rfl | rfl <;> rcases cases' v with rfl | rfl <;>
    simp only [zero_add,add_zero,h2,eps,one_ne_zero,if_false] <;> norm_num

private lemma left_mul {n : ℕ} (a b x : V n) : walsh (a+b) x=walsh a x*walsh b x := by
  change eps (∑ i, (a i+b i)*x i) = eps _*eps _
  simp only [add_mul,sum_add_distrib,eps_add]

private lemma right_mul {n : ℕ} (a x y : V n) : walsh a (x+y)=walsh a x*walsh a y := by
  change eps (∑ i, a i*(x i+y i)) = eps _*eps _
  simp only [mul_add,sum_add_distrib,eps_add]

private lemma walsh_prod {n k : ℕ} (c : Fin k → V n) (s : Finset (Fin k)) (x : V n) :
    (∏ i ∈ s, walsh (c i) x) = walsh (∑ i ∈ s, c i) x := by
  induction s using Finset.induction_on with
  | empty => simp [walsh]
  | insert i s hi ih => simp [hi,ih,left_mul]

private lemma cancel {n : ℕ} (a : V n) (ha : a ≠ 0) : ∑ x : V n, walsh a x=0 := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, a i ≠ 0 := by simpa [funext_iff] using ha
  let e : V n := Pi.single i 1
  have he : walsh a e = -1 := by
    unfold walsh
    simp [e,Pi.single_apply,mul_ite,hi]
  have hshift : (∑ x : V n, walsh a (x+e)) = ∑ x : V n, walsh a x :=
    Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)
  simp only [right_mul,he,mul_neg_one,sum_neg_distrib] at hshift
  linarith

lemma moment_eq {n k : ℕ} (c : Fin k → V n) (s : Finset (Fin k)) :
    moment c s = if ∑ i ∈ s, c i = 0 then 1 else 0 := by
  classical
  unfold moment
  simp only [walsh_prod]
  by_cases h : (∑ i ∈ s, c i)=0
  · rw [if_pos h,h]
    simp [walsh]
  · simp [h,cancel _ h]

end OMA.S_mo_220054

namespace OMA.S_mo_220054

private lemma two_blocks_compl {k : ℕ} {b d : Finset (Fin k)} (hbd : b ≠ d)
    (hp : Partitions {b,d}) : d = bᶜ := by
  classical
  ext i
  obtain ⟨w,⟨hm,hi⟩,hw⟩ := hp.2 i
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  rw [Finset.mem_compl]
  constructor
  · intro hd hb
    exact hbd ((hw b ⟨by simp,hb⟩).trans (hw d ⟨by simp,hd⟩).symm)
  · intro hb
    rcases hm with rfl | rfl
    · contradiction
    · exact hi

lemma two_count {n k : ℕ} (c : Fin k → V n) (a : Fin k) (ht : ∑ i,c i=0) :
    countTwo c + 1 = countAway c a := by
  classical
  let away := (Finset.univ : Finset (Finset (Fin k))).filter fun b => a ∉ b ∧ ∑ i ∈ b,c i=0
  let two := (Finset.univ : Finset (Finset (Finset (Fin k)))).filter fun π => Good c π ∧ π.card=2
  let pack (b : Finset (Fin k)) : Finset (Finset (Fin k)) := {b,bᶜ}
  have memAway {b : Finset (Fin k)} : b ∈ away.erase ∅ ↔ b ≠ ∅ ∧ a ∉ b ∧ ∑ i ∈ b,c i=0 := by
    simp [away]
  have memTwo {π : Finset (Finset (Fin k))} : π ∈ two ↔ Good c π ∧ π.card=2 := by simp [two]
  have hset : (away.erase ∅).image pack = two := by
    ext π
    constructor
    · intro h
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hne,ha,hz⟩ := memAway.mp hb
      have hac : a ∈ bᶜ := Finset.mem_compl.mpr ha
      have hnc : bᶜ ≠ ∅ := Finset.ne_empty_of_mem hac
      have hbc : b ≠ bᶜ := fun e => ha (e ▸ hac)
      have hzc : ∑ i ∈ bᶜ, c i=0 := by simpa [hz,ht] using b.sum_add_sum_compl c
      refine memTwo.mpr ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
      · simpa [pack] using And.intro (Ne.symm hne) (Ne.symm hnc)
      · intro i
        by_cases hi : i ∈ b
        · refine ⟨b,⟨by simp [pack],hi⟩,?_⟩
          rintro y ⟨hy,hyi⟩
          simpa [pack,hi,show y ≠ bᶜ from fun h => (Finset.mem_compl.mp (h ▸ hyi)) hi] using hy
        · refine ⟨bᶜ,⟨by simp [pack],Finset.mem_compl.mpr hi⟩,?_⟩
          rintro y ⟨hy,hyi⟩
          simpa [pack,show y ≠ b from fun h => hi (h ▸ hyi)] using hy
      · intro y hy
        simp only [pack,Finset.mem_insert,Finset.mem_singleton] at hy
        rcases hy with rfl | rfl <;> assumption
      · simp [pack,hbc]
    · intro h
      obtain ⟨⟨hp,hz⟩,hcard⟩ := memTwo.mp h
      obtain ⟨b,d,hbd,rfl⟩ := Finset.card_eq_two.mp hcard
      have hcomp := two_blocks_compl hbd hp
      subst d
      by_cases ha : a ∈ b
      · refine Finset.mem_image.mpr ⟨bᶜ,memAway.mpr ⟨?_,by simpa, hz _ (by simp)⟩,?_⟩
        · intro he; exact hp.1 (by simp [he])
        · simp [pack,Finset.pair_comm]
      · refine Finset.mem_image.mpr ⟨b,memAway.mpr ⟨?_,ha,hz _ (by simp)⟩,rfl⟩
        intro he; exact hp.1 (by simp [he])
  have hinj : Set.InjOn pack (away.erase ∅) := by
    intro b hb d hd he
    have h₁ := (memAway.mp hb).2.1
    have h₂ := (memAway.mp hd).2.1
    have hm : b ∈ pack d := he ▸ (by simp [pack] : b ∈ pack b)
    simp only [pack,Finset.mem_insert,Finset.mem_singleton] at hm
    exact hm.resolve_right fun eq => h₁ (eq ▸ Finset.mem_compl.mpr h₂)
  change two.card + 1 = away.card
  rw [← hset,Finset.card_image_of_injOn hinj]
  exact Finset.card_erase_add_one (by simp [away])

end OMA.S_mo_220054

namespace OMA.S_mo_220054
open Finset
open scoped symmDiff

private lemma sum_toggle {n k : ℕ} (c : Fin k → V n) (b d : Finset (Fin k)) :
    ∑ i ∈ b ∆ d, c i = (∑ i ∈ b, c i)+(∑ i ∈ d, c i) := by
  classical
  have hs (s : Finset (Fin k)) : (∑ i, if i ∈ s then c i else 0)=∑ i ∈ s, c i := by simp
  rw [← hs,← hs,← hs,← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have h : c i+c i=0 := by funext j;exact CharTwo.add_self_eq_zero _
  by_cases hb : i∈b <;> by_cases hd : i∈d <;> simp [mem_symmDiff,hb,hd,h]

lemma away_even {n k : ℕ} (c : Fin k → V n) (a : Fin k)
    (h : ∃ b : Finset (Fin k), b.Nonempty ∧ a ∉ b ∧ ∑ i ∈ b, c i=0) : Even (countAway c a) := by
  classical
  obtain ⟨b,⟨x,hx⟩,ha,hb⟩ := h
  let S := univ.filter (fun d : Finset (Fin k) => a ∉ d ∧ ∑ i ∈ d, c i=0)
  have hmem (d : Finset (Fin k)) : d∈S ↔ a ∉ d ∧ ∑ i ∈ d, c i=0 := by simp [S]
  have ht {d} (hd : d∈S) : d ∆ b ∈ S := by
    obtain ⟨hd₁,hd₂⟩ := (hmem _).mp hd
    exact (hmem _).mpr ⟨by simp [mem_symmDiff,hd₁,ha],by rw [sum_toggle,hd₂,hb,add_zero]⟩
  let p (d : Finset (Fin k)) := x ∈ d
  have he : (S.filter p).card=(S.filter (fun d => ¬ p d)).card := by
    refine card_bij' (fun d _ => d ∆ b) (fun d _ => d ∆ b) ?_ ?_ (fun _ _ => by simp) (fun _ _ => by simp)
    · intro d hd
      obtain ⟨hd₁,hd₂⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨ht hd₁,by simpa [p,mem_symmDiff,hx] using hd₂⟩
    · intro d hd
      obtain ⟨hd₁,hd₂⟩ := mem_filter.mp hd
      exact mem_filter.mpr ⟨ht hd₁,by simpa [p,mem_symmDiff,hx] using hd₂⟩
  change Even S.card
  use (S.filter p).card
  have he' := card_filter_add_card_filter_not (s := S) p
  omega

lemma countAway_eq_one {n k : ℕ} (c : Fin k → V n) (a : Fin k)
    (h : ∀ b : Finset (Fin k), a ∉ b → (∑ i ∈ b, c i)=0 → b=∅) : countAway c a=1 := by
  classical
  unfold countAway
  suffices he : (univ.filter (fun b : Finset (Fin k) => a ∉ b ∧ ∑ i ∈ b, c i=0))={∅} by
    rw [he,card_singleton]
  ext b
  simp only [mem_filter,mem_univ,true_and,mem_singleton]
  exact ⟨fun hb => h _ hb.1 hb.2,fun hb => by subst b;simp⟩

end OMA.S_mo_220054

namespace OMA.S_mo_220054

open Finset

lemma good_total {n k} {c : Fin k → V n} {π : Finset (Finset (Fin k))} (h : Good c π) :
    ∑ i, c i = 0 := by
  classical
  have hu : π.biUnion id = univ := by
    apply eq_univ_of_forall
    intro i
    obtain ⟨b,hb,_⟩ := h.1.2 i
    exact mem_biUnion.mpr ⟨b,hb.1,hb.2⟩
  have hd : Set.PairwiseDisjoint (π : Set (Finset (Fin k))) id := by
    intro b hb d hd hne
    apply Finset.disjoint_left.mpr
    intro i hib hid
    exact hne ((h.1.2 i).unique ⟨hb,hib⟩ ⟨hd,hid⟩)
  rw [←hu, Finset.sum_biUnion hd]
  exact Finset.sum_eq_zero fun b hb => h.2 b hb

lemma cumulant_formula {n k} (c : Fin k → V n) : cumulant c = (xorSum c : ℚ) := by
  classical
  simp only [cumulant,xorSum,Int.cast_sum]
  apply sum_congr rfl
  intro π _
  by_cases hp : Partitions π
  · simp only [if_pos hp]
    by_cases hz : ∀ b ∈ π, ∑ i ∈ b, c i = 0
    · have hg : Good c π := ⟨hp,hz⟩
      rw [if_pos hg,Finset.prod_eq_one (fun b hb => by rw [moment_eq,if_pos (hz b hb)]),mul_one]
    · have hg : ¬Good c π := fun hg => hz hg.2
      push Not at hz
      obtain ⟨b,hb,hnz⟩ := hz
      rw [if_neg hg,Int.cast_zero]
      rw [Finset.prod_eq_zero hb (by rw [moment_eq,if_neg hnz]),mul_zero]
  · have hg : ¬Good c π := fun hg => hp hg.1
    simp [hp,hg]

lemma xor_zero_of_total {n k} (c : Fin k → V n) (ht : ∑ i,c i ≠ 0) : xorSum c = 0 := by
  classical
  exact Finset.sum_eq_zero fun π _ => if_neg (fun h => ht (good_total h))

lemma parity_count {n k} (c : Fin k → V n) (a : Fin k) (ht : ∑ i,c i=0) :
    (xorSum c : ZMod 2) = 1 + (countTwo c : ZMod 2) := by
  classical
  let U : Finset (Finset (Fin k)) := {univ}
  have hU : Good c U := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · have hu : (univ : Finset (Fin k)).Nonempty := ⟨a,mem_univ _⟩
      simpa [U] using hu.ne_empty.symm
    · intro i
      exact ⟨univ,⟨mem_singleton_self _,mem_univ _⟩,fun b hb => mem_singleton.mp hb.1⟩
    · intro b hb
      have e : b=univ := mem_singleton.mp hb
      simpa [e] using ht
  have h1 {π : Finset (Finset (Fin k))} (hg : Good c π) (hc : π.card = 1) : π = U := by
    obtain ⟨b,rfl⟩ := Finset.card_eq_one.mp hc
    have hb : b = univ := by
      apply eq_univ_of_forall
      intro i
      obtain ⟨t,ht,_⟩ := hg.1.2 i
      simpa [mem_singleton.mp ht.1] using ht.2
    simp [hb,U]
  have he (π : Finset (Finset (Fin k))) :
      ((if Good c π then weight π.card else 0 : ℤ) : ZMod 2) =
      (if π = U then 1 else 0) + (if Good c π ∧ π.card=2 then 1 else 0) := by
    by_cases hg : Good c π
    · rw [if_pos hg]
      by_cases hU' : π=U
      · subst π
        norm_num [U,weight]
      · rw [if_neg hU',zero_add]
        by_cases h2 : π.card=2
        · norm_num [hg,h2,weight]
          decide
        · rw [if_neg (fun h => h2 h.2)]
          have hne : π.Nonempty := by
            obtain ⟨b,hb,_⟩ := hg.1.2 a
            exact ⟨b,hb.1⟩
          have hcard := card_pos.mpr hne
          have hc1 : π.card ≠ 1 := fun h => hU' (h1 hg h)
          have h3 : 2 ≤ π.card-1 := by omega
          have heven : Even (π.card-1).factorial := even_iff_two_dvd.mpr
            (Nat.dvd_factorial (by decide : 0<2) h3)
          simp [weight, ZMod.natCast_eq_zero_iff_even.mpr heven]
    · have hu : π ≠ U := fun h => hg (h ▸ hU)
      simp [hg,hu]
  simp only [xorSum,Int.cast_sum,he,sum_add_distrib]
  rw [Finset.sum_ite_eq']
  simp only [mem_univ,if_true]
  rw [Finset.sum_boole]
  rfl

end OMA.S_mo_220054

open OMA.S_mo_220054

theorem OMA.solution : type_of% @OMA.S_mo_220054.main := by
  intro n k c a
  refine ⟨cumulant_formula c,xor_zero_of_total c,?_⟩
  by_cases ht : ∑ i,c i=0
  · rw [and_iff_right ht,← ZMod.intCast_eq_one_iff_odd,parity_count c a ht]
    have hc := two_count c a ht
    constructor
    · intro h b ha hb
      by_contra hne
      have hev := away_even c a ⟨b,Finset.nonempty_iff_ne_empty.mpr hne,ha,hb⟩
      have hcast : (countTwo c : ZMod 2)=0 := by
        apply add_left_cancel (a := (1 : ZMod 2))
        simpa using h
      have htwo := ZMod.natCast_eq_zero_iff_even.mp hcast
      obtain ⟨u,hu⟩ := htwo
      obtain ⟨v,hv⟩ := hev
      omega
    · intro h
      have ho := countAway_eq_one c a h
      have hz : countTwo c=0 := by omega
      simp [hz]
  · simp [xor_zero_of_total c ht,ht]
