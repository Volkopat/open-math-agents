import OMAReductions.R_Arxiv_2607_08366_min_modulus_R1

/-!
# Antipodal descent at exceptional even moduli

A valid set containing both endpoints of a diameter projects to a valid
set with one fewer element modulo half the modulus. Distinct non-antipodal
sets of residues are distinguished by their doubles. For a set of size k
at least four, packing the anchored subset sums, the nonzero doubles and
their reflections also proves the bound 2^(k−1)+2(k−2). For k at least
three this rules out every modulus 2^(k−1). An exhaustive certificate
excludes five-element sets modulo 24.

The subset-sum injection is due to @kyka776 (project note 56429). The
parent reduction of @rorcores proves descent for a single parity class.
Here the pair merged in the quotient consists of residues half a period apart.
-/
namespace OMA.R_Arxiv_2607_08366_min_modulus_R1_H3_R1
open Finset Arxiv.«2607.08366» OMA.R_Arxiv_2607_08366_min_modulus_R1
-- Anchored subset-sum injection from @kyka776, project note 56429.
private lemma anchored_subset_sums {N : ℕ} {A : Finset (ZMod N)} {z : ZMod N}
    (hz : z ∈ A) (hA : IsValidMod A) :
    Set.InjOn (fun B : Finset (ZMod N) => ∑ a ∈ B, (a - z))
      (↑(A.erase z).powerset : Set (Finset (ZMod N))) := by
  classical
  intro B hB C hC heq
  wlog hcard : #B ≤ #C generalizing B C
  · exact (this hC hB heq.symm (by omega)).symm
  have hB : B ⊆ A.erase z := mem_powerset.mp hB
  have hC : C ⊆ A.erase z := mem_powerset.mp hC
  change ∑ a ∈ B, (a - z) = ∑ a ∈ C, (a - z) at heq
  let q (T : Finset (ZMod N)) (a : ZMod N) : ℕ := if a ∈ T then 1 else 0
  let e (a : ZMod N) : ℕ := if a = z then #C - #B else 0
  let m (a : ZMod N) : ℕ := (1 - q C a) + q B a + e a
  have hp (a) : m a + q C a = 1 + q B a + e a := by
    by_cases ha : a ∈ C <;> simp [m, q, ha, add_left_comm, add_comm]
  have hq (T : Finset (ZMod N)) (hTA : T ⊆ A) : ∑ a ∈ A, q T a = #T := by
    calc
      _ = ∑ a ∈ T, q T a := (sum_subset hTA (fun a _ h => by simp [q, h])).symm
      _ = #T := by simp [q]
  have he : ∑ a ∈ A, e a = #C - #B := by
    rw [sum_eq_single_of_mem z hz (fun a _ h => by simp [e, h])]
    simp [e]
  have hn : ∑ a ∈ A, m a = #A := by
    have h := sum_congr (s₁ := A) rfl (fun a _ => hp a)
    simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at h
    rw [hq C (hC.trans (erase_subset _ _)), hq B (hB.trans (erase_subset _ _)), he] at h
    omega
  have hweight (T : Finset (ZMod N)) (hTA : T ⊆ A) :
      ∑ a ∈ A, (q T a : ZMod N) * (a - z) = ∑ a ∈ T, (a - z) := by
    calc
      _ = ∑ a ∈ T, (q T a : ZMod N) * (a - z) :=
        (sum_subset hTA (fun a _ h => by simp [q, h])).symm
      _ = _ := sum_congr rfl (fun a h => by simp [q, h])
  have hew : ∑ a ∈ A, (e a : ZMod N) * (a - z) = 0 := by
    apply sum_eq_zero
    intro a _
    by_cases h : a = z <;> simp [e, h]
  have hshift : ∑ a ∈ A, (m a : ZMod N) * (a - z) = ∑ a ∈ A, (a - z) := by
    have h := sum_congr (s₁ := A) rfl
      (fun a _ => congrArg (fun k : ℕ => (k : ZMod N) * (a - z)) (hp a))
    push_cast at h
    simp only [add_mul, sum_add_distrib, one_mul] at h
    rw [hweight C (hC.trans (erase_subset _ _)), hweight B (hB.trans (erase_subset _ _)),
      hew, add_zero, heq] at h
    exact add_right_cancel h
  have hw : ∑ a ∈ A, (m a : ZMod N) * a = ∑ a ∈ A, a := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, ← Nat.cast_sum, hn, sum_const,
      nsmul_eq_mul] at hshift
    exact sub_left_inj.mp hshift
  have hall := hA m hn hw
  ext a
  by_cases hb : a ∈ B <;> by_cases hc : a ∈ C
  · simp [hb, hc]
  · have hA' := mem_of_mem_erase (hB hb)
    have hne := ne_of_mem_erase (hB hb)
    have hh := hall a hA'
    simp [m, q, e, hb, hc, hne] at hh
  · have hA' := mem_of_mem_erase (hC hc)
    have hne := ne_of_mem_erase (hC hc)
    have hh := hall a hA'
    simp [m, q, e, hb, hc, hne] at hh
  · simp [hb, hc]



private theorem missed_multiple {N : Nat} (A : Finset (ZMod N)) (zA : 0∈A)
    (valid : IsValidMod A) (x : ZMod N) (hx : x∈A.erase 0)
    (S : Finset (ZMod N)) (hs : S⊆A.erase 0) (k : Nat) (hk : 2≤k) (hr : k≤#S+1) :
    (k : ZMod N)*x ≠ ∑ a∈S,a := by
  classical
  intro eqn
  let D := A.erase 0 \ S
  have hD : D ⊆ A := (Finset.sdiff_subset).trans (Finset.erase_subset _ _)
  let w (a : ZMod N) := (if a∈D then 1 else 0 : Nat) +
    (if a=x then k else 0) + (if a=0 then #S+1-k else 0)
  have xA := Finset.mem_of_mem_erase hx
  have hnum : (∑ a∈A, (if a∈D then 1 else 0 : Nat)) = #D := by
    rw [← Finset.sum_filter]
    have e : A.filter (·∈D) = D := by ext a; simp [and_iff_right_of_imp (fun hd => hD hd)]
    simp [e]
  have hweight : (∑ a∈A, (if a∈D then a else 0)) = ∑ a∈D,a := by
    rw [← Finset.sum_filter]
    have e : A.filter (·∈D) = D := by ext a; simp [and_iff_right_of_imp (fun hd => hD hd)]
    rw [e]
  have size : ∑ a∈A,w a = #A := by
    simp only [w,Finset.sum_add_distrib]
    rw [hnum]
    simp [Finset.sum_ite_eq',xA,zA]
    have c := Finset.card_sdiff_add_card_eq_card hs
    change #D+#S=#(A.erase 0) at c
    have ne := Finset.card_pos.mpr (show A.Nonempty from ⟨0,zA⟩)
    rw [Finset.card_erase_of_mem zA] at c
    omega
  have weighted : (∑ a∈A, (w a : ZMod N)*a) = ∑ a∈A,a := by
    simp only [w,Nat.cast_add,add_mul,Finset.sum_add_distrib,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,
      ite_mul,zero_mul,one_mul]
    rw [hweight]
    simp [Finset.sum_ite_eq',xA,zA]
    rw [eqn,Finset.sum_sdiff hs,← Finset.sum_erase_add _ _ zA]
    simp
  have unique := valid w size weighted x xA
  have xne := Finset.ne_of_mem_erase hx
  simp [w,xne] at unique
  split at unique <;> omega


private lemma affine_valid {N : Nat} (u c : ZMod N)
    (cancel : Function.Injective (fun x : ZMod N => u*x))
    (A : Finset (ZMod N)) (valid : IsValidMod A) :
    IsValidMod (A.image fun a => u*a+c) := by
  classical
  have inj : Set.InjOn (fun a : ZMod N => u*a+c) (A : Set (ZMod N)) :=
    fun _ _ _ _ e => cancel (add_right_cancel e)
  intro m size weighted t ht
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp ht
  rw [Finset.sum_image inj,Finset.card_image_of_injOn inj] at size
  rw [Finset.sum_image inj,Finset.sum_image inj] at weighted
  apply valid (fun b => m (u*b+c)) size _ a ha
  apply cancel
  have eqn : u*(∑ b ∈ A, (m (u*b+c) : ZMod N)*b) +
      (∑ b ∈ A, (m (u*b+c) : ZMod N))*c = u*(∑ b ∈ A, b) + (#A : ZMod N)*c := by
    calc
      _ = ∑ b ∈ A, (m (u*b+c) : ZMod N)*(u*b+c) := by
        rw [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun b _ => by ring)
      _ = ∑ b ∈ A, (u*b+c) := weighted
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  rw [← Nat.cast_sum,size] at eqn
  exact add_right_cancel eqn

private lemma anchor {N : Nat} (A : Finset (ZMod N)) (ne : A.Nonempty)
    (valid : IsValidMod A) : ∃ B : Finset (ZMod N), #B=#A ∧ 0∈B ∧ IsValidMod B := by
  obtain ⟨a,ha⟩ := ne
  let F := fun x : ZMod N => (1:ZMod N)*x + (-a)
  have inj : Function.Injective F := by intro x y h; simpa [F] using h
  exact ⟨A.image F,Finset.card_image_of_injective _ inj,
    Finset.mem_image.mpr ⟨a,ha,by simp [F]⟩,
    affine_valid 1 (-a) (fun _ _ h => by simpa using h) A valid⟩


private theorem halves (M : ℕ) (hM : 0<M) (x : ZMod (2*M)) :
    2*x=0 ↔ x=0 ∨ x=(M : ZMod (2*M)) := by
  letI : NeZero (2*M) := ⟨by omega⟩
  have hh : (M : ZMod (2*M)).val = M := ZMod.val_cast_of_lt (by omega)
  rw [show 2*x=0 ↔ -x=x by rw [neg_eq_iff_add_eq_zero,two_mul x],ZMod.neg_eq_self_iff]
  constructor
  · rintro (e|e)
    · exact Or.inl e
    · right; apply ZMod.val_injective (n := 2*M); omega
  · rintro (rfl|rfl)
    · exact Or.inl rfl
    · exact Or.inr (by omega)

private theorem normalized (M : ℕ) (hM : 0<M) (A : Finset (ZMod (2*M)))
    (ne : A.Nonempty) (valid : IsValidMod A) :
    ∃ B : Finset (ZMod (2*M)), #B=#A ∧ 0∈B ∧ IsValidMod B ∧
      (Set.InjOn (fun x => 2*x) (B : Set (ZMod (2*M))) ∨ (M : ZMod (2*M)) ∈ B) := by
  classical
  by_cases h : Set.InjOn (fun x => 2*x) (A : Set (ZMod (2*M)))
  · obtain ⟨a,ha⟩ := ne
    let F := fun x : ZMod (2*M) => 1*x + (-a)
    have inj : Function.Injective F := by intro x y e; simpa [F] using e
    refine ⟨A.image F,Finset.card_image_of_injective _ inj,
      Finset.mem_image.mpr ⟨a,ha,by simp [F]⟩,
      affine_valid 1 (-a) (fun _ _ e => by simpa using e) A valid, Or.inl ?_⟩
    intro u hu v hv eqn
    obtain ⟨x,hAx,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨y,hAy,rfl⟩ := Finset.mem_image.mp hv
    apply congrArg F
    apply h hAx hAy
    dsimp [F] at eqn
    linear_combination eqn
  · simp only [Set.InjOn,not_forall,exists_prop] at h
    obtain ⟨a,ha,b,hb,e,hn⟩ := h
    let F := fun x : ZMod (2*M) => 1*x + (-a)
    have inj : Function.Injective F := by intro x y eqn; simpa [F] using eqn
    have hroot : 2*(b-a)=0 := by linear_combination -e
    have half := ((halves M hM (b-a)).mp hroot).resolve_left (sub_ne_zero.mpr (Ne.symm hn))
    exact ⟨A.image F,Finset.card_image_of_injective _ inj,
      Finset.mem_image.mpr ⟨a,ha,by simp [F]⟩,
      affine_valid 1 (-a) (fun _ _ eqn => by simpa using eqn) A valid,
      Or.inr (Finset.mem_image.mpr ⟨b,hb,by simpa [F,sub_eq_add_neg] using half⟩)⟩

private theorem pack_even (M : ℕ) (hM : 0 < M) (A : Finset (ZMod (2*M))) (zA : 0∈A)
    (enough : 2 ≤ #A) (valid : IsValidMod A)
    (normalized : Set.InjOn (fun x => 2*x) (A : Set (ZMod (2*M))) ∨ (M : ZMod (2*M)) ∈ A) :
    2^(#A-1)+(#A-2) ≤ 2*M ∧ (4 ≤ #A → 2^(#A-1)+2*(#A-2) ≤ 2*M) := by
  classical
  letI : NeZero (2*M) := ⟨by omega⟩
  let E := A.erase 0
  let P := E.erase (M : ZMod (2*M))
  let total := ∑ a∈E,a
  let sums := E.powerset.image (fun U => ∑ a∈U,a)
  have size : #E = #A-1 := Finset.card_erase_of_mem zA
  have pc : #A-2 ≤ #P := by
    dsimp [P]
    by_cases h : (M : ZMod (2*M))∈E
    · rw [Finset.card_erase_of_mem h,size]; omega
    · rw [Finset.erase_eq_of_notMem h,size]; omega
  have nonempty : E.Nonempty := Finset.card_pos.mp (by omega)
  have inj : Set.InjOn (fun U : Finset (ZMod (2*M)) => ∑ a∈U,a) (E.powerset : Set (Finset (ZMod (2*M)))) := by
    simpa only [sub_zero] using anchored_subset_sums zA valid
  have dbl : Set.InjOn (fun x => 2*x) (P : Set (ZMod (2*M))) := by
    intro x hx y hy eqn
    have hxE := Finset.mem_of_mem_erase (show x∈P from hx)
    have hyE := Finset.mem_of_mem_erase (show y∈P from hy)
    rcases normalized with full|hmA
    · exact full (Finset.mem_of_mem_erase hxE) (Finset.mem_of_mem_erase hyE) eqn
    by_contra neq
    have e : 2*(x-y)=0 := by linear_combination eqn
    have diff := ((halves M hM _).mp e).resolve_left (sub_ne_zero.mpr neq)
    have hm0 : (M : ZMod (2*M)) ≠ 0 := by
      have hval := ZMod.val_cast_of_lt (n := 2*M) (a := M) (by omega)
      intro he; rw [he,ZMod.val_zero] at hval; omega
    have hmE : (M : ZMod (2*M)) ∈ E := Finset.mem_erase.mpr ⟨hm0,hmA⟩
    have hmy : (M : ZMod (2*M)) ≠ y := (Finset.ne_of_mem_erase (show y∈P from hy)).symm
    have sp : ({(M : ZMod (2*M)), y} : Finset _) ⊆ E := by
      intro u hu; simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl <;> assumption
    have sq : ({x} : Finset _) ⊆ E := Finset.singleton_subset_iff.mpr hxE
    have equal := inj (Finset.mem_powerset.mpr sp) (Finset.mem_powerset.mpr sq)
      (by simpa [hmy] using (show (M : ZMod (2*M))+y=x by linear_combination -diff))
    have := congrArg Finset.card equal
    simp [hmy] at this
  have comp (S : Finset (ZMod (2*M))) (sub : S⊆E) : (∑ a∈E \ S,a) + (∑ a∈S,a) = total :=
    Finset.sum_sdiff sub
  have nohalf (S : Finset (ZMod (2*M))) (sub : S⊆E) : 2*(∑ a∈S,a) ≠ total := by
    intro eqn
    have h := comp S sub
    have eqS : S = E \ S := inj (Finset.mem_powerset.mpr sub) (Finset.mem_powerset.mpr Finset.sdiff_subset)
      (by change (∑ a∈S,a) = ∑ a∈E \ S,a; linear_combination eqn - h)
    obtain ⟨x,hx⟩ := nonempty
    have hmem : x∈S ↔ x∉S := by conv_lhs => rw [eqS]; simp [hx]
    tauto
  have notFour (large : 4 ≤ #A) (x : ZMod (2*M)) (hx : x∈E) : 2*(2*x) ≠ total := by
    intro eqn
    have card := Finset.card_erase_of_mem hx
    have bad := missed_multiple A zA valid x hx (E.erase x) (Finset.erase_subset _ _) 3 (by decide) (by omega)
    apply bad
    have es : (∑ a∈E.erase x,a) + x = total := Finset.sum_erase_add _ _ hx
    push_cast
    linear_combination eqn - es

  let D := P.image fun x => 2*x
  let K := D.image fun x => total-x
  have apart : Disjoint sums D := by
    apply Finset.disjoint_left.mpr
    intro b hb hd
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x,hx,eqn⟩ := Finset.mem_image.mp hd
    have hxE := Finset.mem_of_mem_erase hx
    by_cases e : S.Nonempty
    · exact missed_multiple A zA valid x hxE S (Finset.mem_powerset.mp hS) 2 (by decide)
        (by have := Finset.card_pos.mpr e; omega) eqn
    · have := Finset.not_nonempty_iff_eq_empty.mp e
      subst S
      have eq0 : 2*x=0 := by simpa using eqn
      exact Finset.ne_of_mem_erase hx ((halves M hM x).mp eq0 |>.resolve_left (Finset.ne_of_mem_erase hxE))
  have apartK : Disjoint sums K := by
    apply Finset.disjoint_left.mpr
    intro b hb hk
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨x,hx,eqn⟩ := Finset.mem_image.mp hk
    have eqc : x=∑ a∈E \ S,a := by linear_combination -(comp S (Finset.mem_powerset.mp hS)) - eqn
    exact Finset.disjoint_left.mp apart (Finset.mem_image.mpr ⟨E \ S,Finset.mem_powerset.mpr Finset.sdiff_subset,eqc.symm⟩) hx
  have cs : #sums = 2^#E := (Finset.card_image_of_injOn inj).trans (Finset.card_powerset E)
  have cd : #D = #P := Finset.card_image_of_injOn dbl
  have small := (sums ∪ D).card_le_univ
  rw [Finset.card_union_of_disjoint apart,cs,cd,size,ZMod.card] at small
  refine ⟨by omega, fun large => ?_⟩
  have DK : Disjoint D K := by
    apply Finset.disjoint_left.mpr
    intro p hp hK
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp hK
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
    by_cases eqxy : x=y
    · subst y
      apply notFour large x (Finset.mem_of_mem_erase hx)
      linear_combination -eqn
    · have h := nohalf {x,y} (by intro b hb; simp only [Finset.mem_insert,Finset.mem_singleton] at hb; rcases hb with rfl|rfl <;> apply Finset.mem_of_mem_erase <;> assumption)
      apply h
      simp [eqxy]
      linear_combination -eqn
  have ck : #K = #D := Finset.card_image_of_injective _ (fun _ _ h => sub_right_inj.mp h)
  have uni := (sums ∪ D ∪ K).card_le_univ
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨apartK,DK⟩),
    Finset.card_union_of_disjoint apart,cs,ck,cd,size,ZMod.card] at uni
  omega
private theorem project_kernel (M : ℕ) (hM : 0 < M) (x : ZMod (2*M)) :
    ZMod.castHom (show M ∣ 2*M by exact dvd_mul_left _ _) (ZMod M) x = 0 →
      x=0 ∨ x=(M : ZMod (2*M)) := by
  letI : NeZero (2*M) := ⟨by omega⟩
  intro eqn
  have hval : (x.val : ZMod M) = 0 := by
    have e := congrArg (ZMod.castHom (show M ∣ 2*M by exact dvd_mul_left _ _) (ZMod M))
      (ZMod.natCast_zmod_val x)
    rw [map_natCast] at e
    exact e.trans eqn
  obtain ⟨j,hj⟩ := (ZMod.natCast_eq_zero_iff _ _).mp hval
  have bound := ZMod.val_lt x
  have small : j < 2 := by by_contra! h; nlinarith
  rcases (show j=0 ∨ j=1 by omega) with rfl|rfl
  · left; exact (ZMod.val_eq_zero x).mp (by simpa using hj)
  · right; apply ZMod.val_injective (n := 2*M)
    rw [ZMod.val_cast_of_lt (by omega)]; simpa using hj

private theorem merge_pair (M : ℕ) (hM : 0<M) (A : Finset (ZMod (2*M)))
    (zA : 0∈A) (tA : (M : ZMod (2*M)) ∈ A) (valid : IsValidMod A) :
    ∃ B : Finset (ZMod M), #B=#A-1 ∧ IsValidMod B := by
  classical
  letI : NeZero (2*M) := ⟨by omega⟩
  let t : ZMod (2*M) := M
  let f := ZMod.castHom (show M ∣ 2*M by exact dvd_mul_left _ _) (ZMod M)
  let E := A.erase t
  have tne : t ≠ 0 := by
    have val : t.val=M := ZMod.val_cast_of_lt (by omega)
    intro he; rw [he,ZMod.val_zero] at val; omega
  have htA : t∈A := tA
  have size : #E=#A-1 := Finset.card_erase_of_mem tA
  have inj : Set.InjOn f (E : Set (ZMod (2*M))) := by
    intro x hx y hy e
    by_contra ne
    have xy := ((project_kernel M hM (x-y)) (by change f (x-y)=0; rw [map_sub,e,sub_self])).resolve_left (sub_ne_zero.mpr ne)
    have hx0 : x≠0 := by
      rintro rfl
      have hyf : f y=0 := by rw [← e,map_zero]
      exact (project_kernel M hM y hyf).elim (fun he => ne he.symm) (Finset.ne_of_mem_erase hy)
    have hy0 : y≠0 := by
      rintro rfl
      have hxf : f x=0 := by rw [e,map_zero]
      exact (project_kernel M hM x hxf).elim ne (Finset.ne_of_mem_erase hx)
    let D := A.erase 0
    have it : t∈D := Finset.mem_erase.mpr ⟨tne,tA⟩
    have ix : x∈D := Finset.mem_erase.mpr ⟨hx0,Finset.mem_of_mem_erase hx⟩
    have iy : y∈D := Finset.mem_erase.mpr ⟨hy0,Finset.mem_of_mem_erase hy⟩
    have hty : t≠y := Ne.symm (Finset.ne_of_mem_erase hy)
    have sp : ({t,y} : Finset _) ⊆ D := by
      intro u hu; simp only [Finset.mem_insert,Finset.mem_singleton] at hu
      rcases hu with rfl|rfl <;> assumption
    have collision := anchored_subset_sums zA valid (Finset.mem_powerset.mpr sp)
      (Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr ix))
      (by simpa [hty] using (show t+y=x by linear_combination -xy))
    have := congrArg Finset.card collision
    simp [hty] at this
  refine ⟨E.image f,(Finset.card_image_of_injOn inj).trans size,?_⟩
  intro m cnt sum u hu
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hu
  rw [Finset.sum_image inj,Finset.card_image_of_injOn inj] at cnt
  rw [Finset.sum_image inj,Finset.sum_image inj] at sum
  let w (a : ZMod (2*M)) := if a=t then 0 else m (f a)
  have wt : w t=0 := by simp [w]
  have wE (a : ZMod (2*M)) (ha : a∈E) : w a=m (f a) := if_neg (Finset.ne_of_mem_erase ha)
  have wc : (∑ a∈A,w a)=#E := by
    rw [← Finset.sum_erase_add _ _ htA,wt,add_zero]
    exact (Finset.sum_congr rfl wE).trans cnt
  have ws : (∑ a∈A,(w a : ZMod (2*M))*a) = ∑ a∈E,(m (f a) : ZMod (2*M))*a := by
    rw [← Finset.sum_erase_add _ _ htA,wt,Nat.cast_zero,zero_mul,add_zero]
    exact Finset.sum_congr rfl (fun a ha => by rw [wE a ha])
  let diff := (∑ a∈A,(w a : ZMod (2*M))*a) - ∑ a∈E,a
  have fd : f diff = 0 := by
    dsimp only [diff]; rw [ws,map_sub,map_sum,map_sum]
    simp only [map_mul,map_natCast,sum,sub_self]
  have lift (b : ZMod (2*M)) (hb : b∈A) (eqn : diff+b=t) :
      ∀ a∈A,w a + (if a=b then 1 else 0) = 1 := by
    apply valid
    · rw [Finset.sum_add_distrib,wc]
      have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨0,zA⟩)
      simp only [Finset.sum_ite_eq',hb,if_true,size]; omega
    · simp only [Nat.cast_add,add_mul,Finset.sum_add_distrib,Nat.cast_ite,Nat.cast_one,
        Nat.cast_zero,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',hb,if_true]
      have hfull : (∑ a∈E,a)+t = ∑ a∈A,a := Finset.sum_erase_add _ _ tA
      dsimp only [diff] at eqn
      linear_combination eqn+hfull
  rcases project_kernel M hM diff fd with eq0|eqt
  · have all := lift t tA (by rw [eq0,zero_add])
    have hxne := Finset.ne_of_mem_erase hx
    simpa [w,hx,hxne] using all x (Finset.mem_of_mem_erase hx)
  · have bad := lift 0 zA (by rw [eqt,add_zero]) t tA
    simp [w,E,tne] at bad
private structure Table where
  depth : Nat
  onlyNonunits : Bool
  positions : Nat
  codes : Nat
  words : Nat

private def binomials : Nat := 0x22caa06b0d00fdc001b30001e000011cfe305cc700e46001960001d0000117fe804ffb00ccc0017a0001c0000113b5a0448e00b6d0015f0001b00001100f403a6600a28001450001a000010cf8a0316a008fc0012c00019000010a60802982007e80011400018000010837102297006eb000fd0001700001066de01c9300604000e7000160000104f7d0176100532000d2000150000103c90012ed00474000be000140000102d6c00f24003c9000ab00013000010217800bf4003300009900012000010182c0094c002a8000880001100001011100071c0023000078000100000100bbb00555001c7000690000f00001007d2003e90016c0005b0000e0000100507002cb0011e0004e0000d0000100318001ef000dc000420000c00001001ce0014a000a5000370000b00001000fc000d2000780002d0000a000010007e0007e000540002400009000010003800046000380001c0000800001000150002300023000150000700001000060000f000140000f000060000100001000050000a0000a0000500001000000000100004000060000400001000000000000001000030000300001000000000000000000010000200001000000000000000000000000100001000000000000000000000000000001

private def rank (tab : Table) : Nat → List Nat → Nat
  | j+1,x::xs =>
    let p := (tab.positions >>> (5*x)) % 32
    ((binomials >>> (20*(p*6+j+1))) % 1048576) + rank tab j xs
  | _,_ => 0

private def allowed (tab : Table) (N x : Nat) := !tab.onlyNonunits || !decide (x.Coprime N)

private def witness (tab : Table) (xs : List Nat) : Nat :=
  let i := rank tab tab.depth xs
  let tag := (tab.words >>> (8*i)) % 256
  (tab.codes >>> (15*tag)) % 32768

private def weight (w : Nat) (s : List Nat) (i : Nat) := (w >>> (3*s.idxOf i)) % 8

private theorem sum_word (f : Nat → Nat) (s : List Nat) (unique : s.Nodup) :
    (s.map f).sum = ∑ a∈s.toFinset,f a := by
  induction s with
  | nil => simp
  | cons a l ih =>
    obtain ⟨hne,hu⟩ := List.nodup_cons.mp unique
    simp [hne,ih hu]

private def obstruction (N : Nat) (s : List Nat) (w : Nat) : Bool :=
  let m := weight w s
  decide (s.Nodup ∧ (s.map m).sum = s.length ∧
    (s.map (fun x => m x*x)).sum % N = s.sum % N ∧ ∃ i ∈ s, m i ≠ 1)

private theorem obstruction_sound {N : Nat} [NeZero N] (s : List Nat) (w : Nat)
    (hs : ∀ i ∈ s, i < N) (bad : obstruction N s w = true)
    (valid : IsValidMod (s.toFinset.image (fun i : Nat => (i : ZMod N)))) : False := by
  let t := s.toFinset
  let m := weight w s
  obtain ⟨hu,hc,hv,i,hm,hdiff⟩ := of_decide_eq_true bad
  have hcount : (∑ a∈t,m a) = #t :=
    (sum_word m s hu).symm.trans (hc.trans (List.toFinset_card_of_nodup hu).symm)
  have hi : i ∈ t := List.mem_toFinset.mpr hm
  have plain : s.sum = ∑ a∈t,a := by simpa [t] using sum_word id s hu
  have hsum : (∑ a∈t,m a*a)%N = (∑ a∈t,a)%N := by
    rw [← sum_word (fun x => m x*x) s hu,← plain]
    exact hv
  have val (a : Nat) (ha : a ∈ t) : (a : ZMod N).val = a :=
    (ZMod.val_natCast N a).trans (Nat.mod_eq_of_lt (hs a (List.mem_toFinset.mp ha)))
  have inj : Set.InjOn (fun a : Nat => (a : ZMod N)) (t : Set Nat) := by
    intro a ha b hb eqn
    have e := congrArg ZMod.val eqn
    simpa only [val a ha,val b hb] using e
  have hlen : ∑ a ∈ t.image (fun a : Nat => (a : ZMod N)), m a.val = #(t.image (fun a : Nat => (a : ZMod N))) := by
    rw [Finset.sum_image inj,Finset.card_image_of_injOn inj]
    exact (Finset.sum_congr rfl (fun a ha => congrArg m (val a ha))).trans hcount
  have hw : ∑ a ∈ t.image (fun a : Nat => (a : ZMod N)), (m a.val : ZMod N)*a =
      ∑ a ∈ t.image (fun a : Nat => (a : ZMod N)), a := by
    rw [Finset.sum_image inj,Finset.sum_image inj]
    have eql : ((∑ a ∈ t, m a*a : Nat) : ZMod N) = ((∑ a ∈ t, a : Nat) : ZMod N) :=
      (ZMod.natCast_eq_natCast_iff' ..).mpr hsum
    push_cast at eql
    exact (Finset.sum_congr rfl (fun a ha => by rw [val a ha])).trans eql
  have res := valid (fun a => m a.val) hlen hw (i : ZMod N) (Finset.mem_image_of_mem _ hi)
  exact hdiff (by simpa only [val i hi] using res)

private def walk (N : Nat) (table : Table) : Nat → Nat → List Nat → Bool
  | 0,_,s => obstruction N s (witness table s)
  | k+1,start,s => (List.range (N-start)).all fun i =>
      !allowed table N (start+i) || walk N table k (start+i+1) ((start+i)::s)

private theorem certify_children (N : Nat) (tab : Table) (k start : Nat) (s : List Nat)
    (h : ∀ i < N-start, allowed tab N (start+i) = true →
      walk N tab k (start+i+1) ((start+i)::s) = true) :
    walk N tab (k+1) start s = true := by
  apply List.all_eq_true.mpr
  intro i hi
  cases hr : allowed tab N (start+i) with
  | false => simp [hr]
  | true => simpa [hr] using h i (List.mem_range.mp hi) hr

private theorem walk_sound {N : Nat} [NeZero N] (tab : Table) (k start : Nat) (xs : List Nat)
    (good : walk N tab k start xs = true) (hxs : ∀ x ∈ xs, x<N) (s : Finset Nat)
    (size : #s=k) (hs : ∀ x∈s, start ≤ x ∧ x<N ∧ allowed tab N x = true)
    (valid : IsValidMod ((s ∪ xs.toFinset).image fun i : Nat => (i : ZMod N))) : False := by
  induction k generalizing s start xs with
  | zero =>
    have : s = ∅ := Finset.card_eq_zero.mp size
    subst s
    exact obstruction_sound xs _ hxs good (by simpa using valid)
  | succ k ih =>
    have ne := Finset.card_pos.mp (show 0 < #s by omega)
    let a := s.min' ne
    have ha : a ∈ s := s.min'_mem ne
    obtain ⟨lo,hi,yes⟩ := hs a ha
    have child := List.all_eq_true.mp good (a-start) (List.mem_range.mpr (by omega))
    rw [show start+(a-start)=a by omega] at child
    simp only [yes,Bool.not_true,Bool.false_or] at child
    apply ih (a+1) (a::xs) child (by simpa [hi] using hxs) (s.erase a) (by rw [Finset.card_erase_of_mem ha,size]; omega)
    · intro b hb
      obtain ⟨diff,bs⟩ := Finset.mem_erase.mp hb
      have least := s.min'_le b bs
      change a ≤ b at least
      exact ⟨by omega,(hs b bs).2⟩
    · have eqn : s.erase a ∪ (a::xs).toFinset = s ∪ xs.toFinset := by
        ext b
        by_cases he : b=a <;> simp [he,ha]
      rwa [eqn]

private theorem cover {N : Nat} [NeZero N] (tab : Table) (k start : Nat) (xs : List Nat)
    (good : walk N tab k start xs = true) (A : Finset (ZMod N)) (valid : IsValidMod A)
    (inside : ∀ i ∈ xs, i<N ∧ (i : ZMod N)∈A)
    (outside : ∀ a ∈ A, a.val ∉ xs → start ≤ a.val ∧ allowed tab N a.val = true) :
    #A < k + xs.toFinset.card := by
  classical
  by_contra! large
  let F := A.image ZMod.val
  have count : #F = #A := Finset.card_image_of_injective _ (ZMod.val_injective N)
  have sub : xs.toFinset ⊆ F := by
    intro i hi
    obtain ⟨small,red⟩ := inside i (List.mem_toFinset.mp hi)
    exact Finset.mem_image.mpr ⟨(i : ZMod N),red,(ZMod.val_natCast N i).trans (Nat.mod_eq_of_lt small)⟩
  have total := Finset.card_sdiff_add_card_eq_card sub
  obtain ⟨s,hs,size⟩ := Finset.exists_subset_card_eq (show k ≤ #(F \ xs.toFinset) by omega)
  apply walk_sound tab k start xs good (fun i hi => (inside i hi).1) s size
  · intro x hx
    obtain ⟨mem,abs⟩ := Finset.mem_sdiff.mp (hs hx)
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp mem
    have h := outside a ha (fun h => abs (List.mem_toFinset.mpr h))
    exact ⟨h.1,ZMod.val_lt _,h.2⟩
  · apply isValidMod_subset _ valid
    intro y hy
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_union.mp hi with h|h
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp (hs h)).1
      simpa using ha
    · exact (inside i (List.mem_toFinset.mp h)).2

private theorem smallCase {N : Nat} [NeZero N] (big : 1<N) (k : Nat) (u t : Table)
    (uf : u.onlyNonunits=false) (tf : t.onlyNonunits=true)
    (pu : walk N u k 2 [1,0]=true) (pt : walk N t (k+1) 1 [0]=true)
    (A : Finset (ZMod N)) (zero : 0∈A) (valid : IsValidMod A) : #A < k+2 := by
  classical
  by_cases has : ∃ a∈A, IsUnit a
  · obtain ⟨a,ha,v,rfl⟩ := has
    let f := fun x : ZMod N => (↑(v⁻¹) : ZMod N)*x+0
    have cancel : Function.Injective (fun x : ZMod N => (↑(v⁻¹) : ZMod N)*x) := by
      intro a b eqn
      simpa only [← mul_assoc,Units.mul_inv, one_mul] using congrArg (fun x : ZMod N => (v : ZMod N)*x) eqn
    have inj : Function.Injective f := fun _ _ eqn => cancel (add_right_cancel eqn)
    let B := A.image f
    have b0 : 0 ∈ B := Finset.mem_image.mpr ⟨0,zero,by simp [f]⟩
    have b1 : 1 ∈ B := Finset.mem_image.mpr ⟨(v : ZMod N),ha,by simp [f]⟩
    have res := cover u k 2 [1,0] pu B (affine_valid _ 0 cancel A valid)
      (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl <;> simp [big,b1,b0,show 0<N by omega])
      (by
        intro a _ hh
        have h0 : a.val ≠ 0 := fun e => hh (by rw [e]; simp)
        have h1 : a.val ≠ 1 := fun e => hh (by rw [e]; simp)
        exact ⟨by omega,by simp [allowed,uf]⟩)
    simpa [B,Finset.card_image_of_injective _ inj] using res
  · have res := cover t (k+1) 1 [0] pt A valid
      (by intro i hi; simp only [List.mem_singleton] at hi; subst i; simp [zero,show 0<N by omega])
      (by
        intro a ha h
        have notUnit : ¬IsUnit a := fun hu => has ⟨a,ha,hu⟩
        have neg : ¬a.val.Coprime N := by
          intro cp
          apply notUnit
          simpa using (ZMod.isUnit_iff_coprime a.val N).mpr cp
        have nz : a.val ≠ 0 := fun e => h (by rw [e]; simp)
        exact ⟨by omega,by simp [allowed,tf,neg]⟩)
    simpa [Nat.add_assoc] using res
private def tab24u : Table := ⟨3,false,0xad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x1617171717171717171717171717171717171717181818181818181818181818181818181818182c2c281b1c2c2c2a2c202c2c2c242c252c192c2c2c281b1c2a2c212c2c242c252c191e2c2c2c2c281b1c2c20242c252c192c1e2c2c2c2c2a281b1c2c252c192c2c1e2c2c2c2a2c24281b1c192c2c2c1e2c2c2a242c2521191b1c2c2c1e2c242c252c19202c281b1c1e2a252c192c212c2c2c281b2719272727202727271e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f3f213f3f3f3f3f242d251e161717171717171717171717171717171717181818181818181818181818181818181832373828651b1c7a20244325402d39193333333328291b1c332533332d191e453738772924431b1c415819391e45373824432521411b192d341e4524292540412019461b1c1e432538416519683428391b2937381965202f2d391e26192626212626261e45343577202d391e353738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f3f2a203f3f3f242d252e1e151637381b1c4d2a217b2f244325392e1e16171717171717171717171717171717181818181818181818181818181818453237382824431b1c402d392e1932783724432521401b1c39191e33242a25333320332d191c1e4325373841215819392e1b2a40373867192d39281e27272719212727271e4519373820352e1e45783421392e1e34352d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c3f32213f3f242d252e3f1e35151637381b1c2920242f25392e401e1516283738321b1c43252d392e411e161717171717171717171717171718181818181818181818181818452432253828202d2f1b1c1943252937382128392e191b32294037382039195a1e2933333321192e331e262626192026261e45192d212e341e452d3920351e2d3421371e302e201e2e211e311e1e283f3415161b1c2a20242d252e3f3f1e3428151637381b1c32252f2e5a401e4515165c3724431b1c392e40411e151649242a25212d1b1c416c1e1617171717171717171717171818181818181818181818422a6a322d20285a67192a40322d212e46191e272727272019271e322d391937381e2d192e20331e302e21301e2e36201e31211e451e1e283f3f3415161b1c2d252e323f3f1e452835151624291b1c2e2f6b401e356e1516432521391b1c40411e45151625292d202e321b1c1e15164b2928212e326c711b16171717171717171717181818181818181818292d392e203738192626262126191e302e3019301e2e1921361e3131201e33211e451e1e283f3f3f3415161b1c3f3f3f3f1e452834241516212e1b1c2f401e3424281516392038461b1c1e4325151639213738412f1b4215163928203738661e1516392e212837381e1617171717171717181818181818182e3636203619313121191e4519201e45211e451e1e283f3f242d2515161b1c3f3f1e4524432535151637381b1c1e432528391516663738411b352d391516204037381e2d391516214146371e301516302028301e1516362136361e1617171717171818181818457a201945191e451e1e28242d252e2a2015161b1c1e4325392e2a21151637381b2d39282a5f151640371e302e2a28151630301e2e2a36151636361e2a31151631281e27151620271e1516217b1e1617171718181845191e28252e3f3f213f3415161b3028303029203015161e2e362829213615161e313129282015161e3529402115161e29415515161e262615161e4515161e15161e161718283636362a20363634153128312a2131313115455c286120354115452a3421416c152a35412028152727212715454e201545211545151528333333213333331e45286929206b401e455b282140341e45294020351e2934216f1e2626201e45211e451e1e28323f2a203f3f1e32282a2155401e332a2820331e2a4021281e2727201e34211e451e1e283f3f213f3f1e45282920401e452921411e2941201e26211e451e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_0 : walk 24 tab24u 2 3 [2, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_1 : walk 24 tab24u 2 4 [3, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_2 : walk 24 tab24u 2 5 [4, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_3 : walk 24 tab24u 2 6 [5, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_4 : walk 24 tab24u 2 7 [6, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_5 : walk 24 tab24u 2 8 [7, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_6 : walk 24 tab24u 2 9 [8, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_7 : walk 24 tab24u 2 10 [9, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_8 : walk 24 tab24u 2 11 [10, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_9 : walk 24 tab24u 2 12 [11, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_10 : walk 24 tab24u 2 13 [12, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_11 : walk 24 tab24u 2 14 [13, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_12 : walk 24 tab24u 2 15 [14, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_13 : walk 24 tab24u 2 16 [15, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_14 : walk 24 tab24u 2 17 [16, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_15 : walk 24 tab24u 2 18 [17, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_16 : walk 24 tab24u 2 19 [18, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_17 : walk 24 tab24u 2 20 [19, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_18 : walk 24 tab24u 2 21 [20, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_19 : walk 24 tab24u 2 22 [21, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_20 : walk 24 tab24u 2 23 [22, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u_21 : walk 24 tab24u 2 24 [23, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24u : walk 24 tab24u 3 2 [1, 0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact check24u_0
  · exact check24u_1
  · exact check24u_2
  · exact check24u_3
  · exact check24u_4
  · exact check24u_5
  · exact check24u_6
  · exact check24u_7
  · exact check24u_8
  · exact check24u_9
  · exact check24u_10
  · exact check24u_11
  · exact check24u_12
  · exact check24u_13
  · exact check24u_14
  · exact check24u_15
  · exact check24u_16
  · exact check24u_17
  · exact check24u_18
  · exact check24u_19
  · exact check24u_20
  · exact check24u_21
private def tab24n : Table := ⟨4,true,0x39ac02c0a4a007018a400c0208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x1515151515151515151515151b1b1b1b1b1b1b1b1b1b1640396e2a6a1d3b16231c40436c1f2a1d381c2c391f683b161c232c3935161c69212a381c692d232c40426b232c391e232c391e2c231e2517171717171717171717161717171717171716171717171717171717171717171717161717171717161717171717171717171717171717171717171717171717171737211a2a221d23163718271a6a1f2a1d3f32181a1f2228161d28181b1b161b1b1b182230232d6b182020201c18231c2d18251e18411818216a271f1a1d18322c211f371a1618242c2772161e186b24281a281828281a3f1840211b181b1b181e1c19192c391f2327161d332c3921161a6f332a23271a2d332c251a2521251a1e28281b1b1b331c2c213716181a372a2525181a25253f181a382c181a2d211919191b1b2c3718222d372718216a422719191919201e20771e27216a306c2c211e2d2c301e212f1e2c391e2d2c391e2c381e2c211e2c201e2c221e202115151515151515151515151b1b1b1b1b1b1b1b1b164039211f4d1d231638661f6e2145162c1c223943161c2a6520161c2020203832232c58651e2c24231e43251e2e171717171717171717161717171717171716171717171717161717171717161717171716171717171717171717171717171717171717172139401f1a1d581618211f351a4316241867391a16432a18551645212c181a32382c181b1b1b18651e182c1818361f23401a1618783721371637183723161a401838251a2518251a1e18401b181b181c1921396716182a432516211825257232182c3845182c21181e6519192e3616186727423718372737181e2767191919271e2818324d2c4d19191919451e212c1e2e331e2c5f341e342c1e2e211e45201e2e221e202115151515151515151515361a2a1f6a1d2c353f1a1f222a231d37161b1b1b1b161b1b22291629291c2020201c20231c6b2d251e252e1e3f171717171717171717171717171717171617171717161717171716171717171717171717171717171717171717691f232a1a1d46162721391a16436f232816282828251a2521251a1e382d1b1b1b2e1c672172271e166b182525161a2518273f1a3218281a28181a1e181b1818292116182929362118326a2218372d181e201919752118262626181e2626191919261e26691e332d2c1e392e1e34211e30201e30221e20212114361f1a1d713b3f141f281a281d2428151515151515152b1a2c2137161a292916211b161b1b2e1e1c721e3f141f23391a1d3f6e15151515151515233b1a393f16251a2516251a163f391b1b1b3f1c41151515151515152525211a251629291a16292c1637211a1e2e1b1b711717171717161717171617171617171717171717172129291618211641182e1e1837181826161826261826181e19181e2e191936221e2021281f23141a1d28286921141a39432d23141a2a6639141a252125151515151b1b16381c402128141e1a28282514211a252514361a302a151515151a1e161b1b2f7714222a6b30142136352a15151515201e16371e30143f27402a15151515271e16281e3615151515691e16461e2717171617171722181821212a65141a39432525141a25252e141a2a2e141a4c211515151b16382721146636422814282828141e366615151536163721142e2a2e141e354515151571166c141e273115151527162815151520166f17161718282122142828752114423622146b2a141e2015153621271431312114312a141e211515313b14402a141e6915156c141e2715152715152017212a753233211e2828291e21721e33271e336f281e28331e34211e29201e71221e2021281e28283b1e2a401e40211e28201e3f221e2021211e45201e40221e2021221e202121⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_0 : walk 24 tab24n 2 4 [3, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_1 : walk 24 tab24n 2 5 [4, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_3 : walk 24 tab24n 2 7 [6, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_5 : walk 24 tab24n 2 9 [8, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_6 : walk 24 tab24n 2 10 [9, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_7 : walk 24 tab24n 2 11 [10, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_9 : walk 24 tab24n 2 13 [12, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_11 : walk 24 tab24n 2 15 [14, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_12 : walk 24 tab24n 2 16 [15, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_13 : walk 24 tab24n 2 17 [16, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_15 : walk 24 tab24n 2 19 [18, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_17 : walk 24 tab24n 2 21 [20, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_18 : walk 24 tab24n 2 22 [21, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1_19 : walk 24 tab24n 2 23 [22, 2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_1 : walk 24 tab24n 3 3 [2, 0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact check24n_1_0
  · exact check24n_1_1
  · contradiction
  · exact check24n_1_3
  · contradiction
  · exact check24n_1_5
  · exact check24n_1_6
  · exact check24n_1_7
  · contradiction
  · exact check24n_1_9
  · contradiction
  · exact check24n_1_11
  · exact check24n_1_12
  · exact check24n_1_13
  · contradiction
  · exact check24n_1_15
  · contradiction
  · exact check24n_1_17
  · exact check24n_1_18
  · exact check24n_1_19
  · contradiction
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_2 : walk 24 tab24n 3 4 [3, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_3 : walk 24 tab24n 3 5 [4, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_5 : walk 24 tab24n 3 7 [6, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_7 : walk 24 tab24n 3 9 [8, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_8 : walk 24 tab24n 3 10 [9, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_9 : walk 24 tab24n 3 11 [10, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_11 : walk 24 tab24n 3 13 [12, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_13 : walk 24 tab24n 3 15 [14, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_14 : walk 24 tab24n 3 16 [15, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_15 : walk 24 tab24n 3 17 [16, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_17 : walk 24 tab24n 3 19 [18, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_19 : walk 24 tab24n 3 21 [20, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_20 : walk 24 tab24n 3 22 [21, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n_21 : walk 24 tab24n 3 23 [22, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check24n : walk 24 tab24n 4 1 [0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · contradiction
  · exact check24n_1
  · exact check24n_2
  · exact check24n_3
  · contradiction
  · exact check24n_5
  · contradiction
  · exact check24n_7
  · exact check24n_8
  · exact check24n_9
  · contradiction
  · exact check24n_11
  · contradiction
  · exact check24n_13
  · exact check24n_14
  · exact check24n_15
  · contradiction
  · exact check24n_17
  · contradiction
  · exact check24n_19
  · exact check24n_20
  · exact check24n_21
  · contradiction

private theorem no_five (A : Finset (ZMod 24)) (h : #A=5) (valid : IsValidMod A) : False := by
  obtain ⟨B,card,zB,vB⟩ := anchor A (Finset.card_pos.mp (by omega)) valid
  have no := smallCase (by decide : 1<24) 3 tab24u tab24n rfl rfl check24u check24n B zB vB
  omega
/-- No two elements of the anchored set project to the same residue in the half modulus. -/
def H1 : Prop := ∀ n v : ℕ, 6 ≤ n+1 → v+2 ≤ n → n+1 < 2^(v+1) →
    ∀ A : Finset (ZMod (2*(2^n-2^v))), #A=n+1 → 0∈A →
    Set.InjOn (fun x => 2*x) (A : Set (ZMod (2*(2^n-2^v)))) →
    (∃ a∈A, a.val % 2 = 1) → ¬IsValidMod A

/-- An antipodal pair survives descent only at the first power of two above the set size. -/
def H2 : Prop := ∀ n v : ℕ, 6 ≤ n+1 → v+2 ≤ n → 2^v ≤ n → n+1 < 2^(v+1) →
    ∀ A : Finset (ZMod (2*(2^n-2^v))), #A=n+1 → 0∈A →
    ((2^n-2^v : ℕ) : ZMod (2*(2^n-2^v))) ∈ A →
    (∃ a∈A, a.val % 2 = 1) → ¬IsValidMod A

private theorem subset_bound {M : ℕ} (hM : 0<M) (B : Finset (ZMod M))
    (ne : B.Nonempty) (valid : IsValidMod B) : 2^(#B-1) ≤ M := by
  classical
  letI : NeZero M := ⟨by omega⟩
  obtain ⟨x,hx⟩ := ne
  have inj := anchored_subset_sums hx valid
  have card := ((B.erase x).powerset.image (fun S => ∑ a∈S,(a-x))).card_le_univ
  rw [Finset.card_image_of_injOn inj,Finset.card_powerset,Finset.card_erase_of_mem hx,ZMod.card] at card
  exact card

theorem main : H1 → H2 → OMA.R_Arxiv_2607_08366_min_modulus_R1.H3 := by
  intro h1 h2 k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro j jlt cap
    cases k with
    | zero => omega
    | succ n =>
      cases j with
      | zero => simp at cap
      | succ v =>
        have vn : v<n := by omega
        let M := 2^n-2^v
        have hp : 2^v<2^n := Nat.pow_lt_pow_right (by decide) vn
        have hM : 0<M := Nat.sub_pos_of_lt hp
        have eqN : 2^(n+1)-2^(v+1)=2*M := by dsimp [M]; rw [pow_succ,pow_succ]; omega
        rw [eqN]
        intro A card valid
        obtain ⟨B,hB,zB,vB,shape⟩ := normalized M hM A (Finset.card_pos.mp (by omega)) valid
        have sz : #B=n+1 := hB.trans card
        have nlarge : 2 ≤ n := by
          by_contra! small
          have ve : v=0 := by omega
          subst v
          norm_num at cap
          omega
        have strong : v+2≤n := by
          by_contra! hn
          have en : n=v+1 := by omega
          have lower := (pack_even M hM B zB (by omega) vB shape).1
          rw [sz,Nat.add_sub_cancel] at lower
          dsimp [M] at lower
          rw [en,pow_succ] at lower
          omega
        by_cases little : n+1<6
        · have nv : n≤4 := by omega
          have vv : v≤2 := by omega
          have pair : n=4 ∧ v=2 := by
            interval_cases v <;> norm_num at cap ⊢ <;> omega
          obtain ⟨rfl,rfl⟩ := pair
          exact no_five B sz vB
        have mix : ∃ a∈B, a.val%2=1 := by
          by_contra! no
          obtain ⟨D,sizeD,vD⟩ := halve hM B 0
            (fun a ha => by have := no a ha; omega) vB
          have low := subset_bound hM D (Finset.card_pos.mp (by omega)) vD
          rw [sizeD,sz,Nat.add_sub_cancel] at low
          dsimp [M] at low
          have := Nat.two_pow_pos v
          omega
        rcases shape with separated|pair
        · exact h1 n v (by omega) strong cap B sz zB separated mix vB
        · by_cases prev : n<2^v
          · obtain ⟨D,dcard,vd⟩ := merge_pair M hM B zB pair vB
            exact ih n (Nat.lt_succ_self _) v vn prev D (by omega) vd
          · exact h2 n v (by omega) strong (by omega) cap B sz zB pair mix vB

end OMA.R_Arxiv_2607_08366_min_modulus_R1_H3_R1
