import OMAReductions.R_Arxiv_2607_08366_min_modulus_R1

/-!
# Balanced parity in the unique multiset-sum problem

At an even modulus 2M, translate any pair of residues a half-period apart
to 0,M. Merging that pair projects a valid set to a valid set modulo M.
When M is even and the pair's parity class contains another point, the
quotient remains balanced. Induction then suffices.

When M is odd, give each other projected residue its original parity as
a binary label. Both labels occur. Every multiset on these points with two
extra entries and the original projected sum must preserve the label sum.
In particular the labels at y,z agree whenever 2x+y=z with x,y,z among
the projected points. These restrictions concern the half modulus alone.

The analytic packing estimate and explicit competing multiplicities cover
all balanced sets through size five. The subset-sum injection comes from
@kyka776, project note 56429. The antipodal compression and even packing
estimate are also used in the sibling reduction of the exceptional moduli.
-/
namespace OMA.R_Arxiv_2607_08366_min_modulus_R1_H2_R1
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

private def bit {N : ℕ} (even : 2 ∣ N) : ZMod N →+* ZMod 2 := ZMod.castHom even _
private def fiber {N : ℕ} (even : 2 ∣ N) (A : Finset (ZMod N)) (p : ZMod 2) :=
  A.filter fun a => bit even a = p
private def balanced {N : ℕ} (even : 2 ∣ N) (A : Finset (ZMod N)) :=
  ∀ p : ZMod 2, 2 ≤ #(fiber even A p)

private theorem bit_val {N : ℕ} [NeZero N] (even : 2 ∣ N) (a : ZMod N) :
    (bit even a).val = a.val%2 := by
  have h := congrArg (bit even) (ZMod.natCast_zmod_val a)
  rw [map_natCast] at h
  rw [← h,ZMod.val_natCast]

private theorem balanced_iff {N : ℕ} [NeZero N] (even : 2 ∣ N) (A : Finset (ZMod N)) :
    balanced even A ↔
      2 ≤ #(A.filter fun a => a.val%2=0) ∧ 2 ≤ #(A.filter fun a => a.val%2=1) := by
  have eqn (p : ZMod 2) : fiber even A p = A.filter (fun a => a.val%2=p.val) := by
    ext x; simp only [fiber,Finset.mem_filter]
    rw [← bit_val even x]
    exact and_congr_right fun _ => ⟨congrArg ZMod.val, fun h => (ZMod.val_injective 2) h⟩
  constructor
  · intro h
    exact ⟨by simpa only [eqn,ZMod.val_zero] using h 0,
      by simpa only [eqn,show (1:ZMod 2).val=1 by decide] using h 1⟩
  · intro h p
    rw [eqn]
    have lt := ZMod.val_lt p
    rcases (show p.val=0 ∨ p.val=1 by omega) with e|e <;> rw [e]
    · exact h.1
    · exact h.2

private theorem balanced_image {N : ℕ} (even : 2 ∣ N) (A : Finset (ZMod N))
    (f : ZMod N → ZMod N) (inj : Function.Injective f) (c : ZMod 2)
    (comm : ∀ x, bit even (f x)=bit even x+c) (bal : balanced even A) :
    balanced even (A.image f) := by
  classical
  intro p
  have same : fiber even (A.image f) p = (fiber even A (p-c)).image f := by
    ext a
    constructor
    · intro ha
      obtain ⟨mem,atp⟩ := Finset.mem_filter.mp ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp mem
      exact Finset.mem_image.mpr ⟨b,Finset.mem_filter.mpr ⟨hb,eq_sub_iff_add_eq.mpr ((comm b).symm.trans atp)⟩,rfl⟩
    · intro ha
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨mem,atp⟩ := Finset.mem_filter.mp hb
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ mem,(comm b).trans (eq_sub_iff_add_eq.mp atp)⟩
  rw [same,Finset.card_image_of_injective _ inj]
  exact bal _

private theorem bit_unit {N : ℕ} (even : 2 ∣ N) (u : (ZMod N)ˣ) :
    bit even (u : ZMod N) = 1 := by
  have hu := u.isUnit.map (bit even)
  have ne := hu.ne_zero
  have h : ∀ b : ZMod 2, b≠0 → b=1 := by decide
  exact h _ ne
private theorem normalized (M : ℕ) (hM : 0<M) (A : Finset (ZMod (2*M)))
    (ne : A.Nonempty) (valid : IsValidMod A) (bal : balanced (dvd_mul_right 2 M) A) :
    ∃ B : Finset (ZMod (2*M)), #B=#A ∧ 0∈B ∧ IsValidMod B ∧ balanced (dvd_mul_right 2 M) B ∧
      (Set.InjOn (fun x => 2*x) (B : Set (ZMod (2*M))) ∨ (M : ZMod (2*M)) ∈ B) := by
  classical
  by_cases h : Set.InjOn (fun x => 2*x) (A : Set (ZMod (2*M)))
  · obtain ⟨a,ha⟩ := ne
    let F := fun x : ZMod (2*M) => 1*x + (-a)
    have inj : Function.Injective F := by intro x y e; simpa [F] using e
    refine ⟨A.image F,Finset.card_image_of_injective _ inj,
      Finset.mem_image.mpr ⟨a,ha,by simp [F]⟩,
      affine_valid 1 (-a) (fun _ _ e => by simpa using e) A valid, balanced_image _ A F inj (-(bit (dvd_mul_right 2 M) a)) (fun x => by simp [F]) bal, Or.inl ?_⟩
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
      affine_valid 1 (-a) (fun _ _ eqn => by simpa using eqn) A valid, balanced_image _ A F inj (-(bit (dvd_mul_right 2 M) a)) (fun x => by simp [F]) bal,
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
private def halfMap (M : ℕ) : ZMod (2*M) →+* ZMod M := ZMod.castHom (dvd_mul_left M 2) _
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
    ∃ B : Finset (ZMod M), #B=#A-1 ∧ B=(A.erase (M : ZMod (2*M))).image (halfMap M) ∧
      Set.InjOn (halfMap M) (A.erase (M : ZMod (2*M)) : Finset (ZMod (2*M))) ∧ IsValidMod B := by
  classical
  letI : NeZero (2*M) := ⟨by omega⟩
  let t : ZMod (2*M) := M
  let f := halfMap M
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
  refine ⟨E.image f,(Finset.card_image_of_injOn inj).trans size,rfl,inj,?_⟩
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
/-- A quotient multiset using only the non-antipodal sites may lift to just one
of the two possible sums. -/
private theorem lift_sum (M : ℕ) (hM : 0<M) (A : Finset (ZMod (2*M)))
    (zA : 0∈A) (hA : (M : ZMod (2*M)) ∈ A) (valid : IsValidMod A)
    (S : Finset (ZMod (2*M))) (hs : S=(A.erase (M : ZMod (2*M))).erase 0)
    (m : ZMod (2*M) → ℕ) (cnt : (∑ a∈S,m a)=#A)
    (weighted : halfMap M (∑ a∈S,(m a : ZMod (2*M))*a) = halfMap M (∑ a∈S,a)) :
    (∑ a∈S,(m a : ZMod (2*M))*a) = ∑ a∈S,a := by
  classical
  letI : NeZero (2*M) := ⟨by omega⟩
  let t : ZMod (2*M) := M
  have ht : t∈A := hA
  have tne : t ≠ 0 := by
    have val : t.val=M := ZMod.val_cast_of_lt (by omega)
    intro he; rw [he,ZMod.val_zero] at val; omega
  have hz : 0 ∈ A.erase t := Finset.mem_erase.mpr ⟨Ne.symm tne,zA⟩
  have sub : S ⊆ A := by rw [hs]; exact (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hn : (0 : ZMod (2*M))∉S := by simp [hs]
  let w (x : ZMod (2*M)) := if x∈S then m x else 0
  have count : (∑ a∈A,w a)=#A := by
    rw [← cnt,← Finset.sum_subset sub (f := w) (fun a _ ha => if_neg ha)]
    exact Finset.sum_congr rfl fun a ha => if_pos ha
  have sum : (∑ a∈A,(w a : ZMod (2*M))*a)= ∑ a∈S,(m a : ZMod (2*M))*a := by
    rw [← Finset.sum_subset sub (f := fun a => (w a : ZMod (2*M))*a) (fun a _ ha => by simp [w,ha])]
    exact Finset.sum_congr rfl fun a ha => by rw [show w a=m a from if_pos ha]
  have allsum : (∑ a∈S,a)+t=∑ a∈A,a := by
    rw [hs,← Finset.sum_erase_add _ _ ht,← Finset.sum_erase_add (A.erase t) (fun a => a) hz]
    simp [t]
  have ker : halfMap M ((∑ a∈S,(m a : ZMod (2*M))*a) - ∑ a∈S,a) = 0 := by rw [map_sub,weighted,sub_self]
  rcases project_kernel M hM _ ker with e|e
  · exact sub_eq_zero.mp e
  · have hw : (∑ a∈A,(w a : ZMod (2*M))*a)=∑ a∈A,a := by
      rw [sum,← allsum]; change _=t at e; linear_combination e
    have false_at_zero := valid w count hw 0 zA
    simp [w,hn] at false_at_zero

private theorem balance_merge (M : ℕ) (ev : 2∣M) (hM : 0<M) (A : Finset (ZMod (2*M)))
    (bal : balanced (dvd_mul_right 2 M) A) (more : 3 ≤ #(fiber (dvd_mul_right 2 M) A 0))
    (inj : Set.InjOn (halfMap M) (A.erase (M : ZMod (2*M)) : Finset (ZMod (2*M)))) :
    balanced ev ((A.erase (M : ZMod (2*M))).image (halfMap M)) := by
  classical
  letI : NeZero (2*M) := ⟨by omega⟩
  let t : ZMod (2*M) := M
  let E := A.erase t
  let src := bit (dvd_mul_right 2 M)
  have comp (x : ZMod (2*M)) : bit ev (halfMap M x)=src x := by
    rw [← ZMod.natCast_zmod_val x,map_natCast,map_natCast,map_natCast]
  have ht : src t=0 := by
    change src (M : ZMod (2*M))=0; rw [map_natCast]; exact (ZMod.natCast_eq_zero_iff _ _).mpr ev
  intro r
  have ee : fiber ev (E.image (halfMap M)) r = ((fiber (dvd_mul_right 2 M) A r).erase t).image (halfMap M) := by
    ext y
    simp only [fiber,Finset.mem_filter,Finset.mem_image,Finset.mem_erase]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,he⟩
      obtain ⟨hne,hA⟩ := Finset.mem_erase.mp hx
      exact ⟨x,⟨hne,hA,(comp x).symm.trans he⟩,rfl⟩
    · rintro ⟨x,⟨hne,hA,he⟩,rfl⟩
      exact ⟨⟨x,Finset.mem_erase.mpr ⟨hne,hA⟩,rfl⟩,(comp x).trans he⟩
  change 2≤#(fiber ev (E.image _) r)
  have smaller : Set.InjOn (halfMap M) (((fiber (dvd_mul_right 2 M) A r).erase t) : Set (ZMod (2*M))) :=
    inj.mono (by
      intro a ha
      obtain ⟨ne,mem⟩ := Finset.mem_erase.mp ha
      exact Finset.mem_erase.mpr ⟨ne,(Finset.mem_filter.mp mem).1⟩)
  rw [ee,Finset.card_image_of_injOn smaller]
  by_cases mem : t∈fiber (dvd_mul_right 2 M) A r
  · have at0 := (Finset.mem_filter.mp mem).2
    have er : r=0 := at0.symm.trans ht
    rw [Finset.card_erase_of_mem mem,er]; omega
  · rw [Finset.erase_eq_of_notMem mem]; exact bal r
/-- On the half modulus, every zero-free rival with two extra entries preserves
the sum of the binary labels. The labels record the parities of the lifts. -/
private theorem odd_projection (M : ℕ) (odd : M%2=1) (A : Finset (ZMod (2*M)))
    (zA : 0∈A) (hA : (M : ZMod (2*M))∈A) (valid : IsValidMod A)
    (bal : balanced (dvd_mul_right 2 M) A) :
    ∃ (C : Finset (ZMod M)) (label : ZMod M → ZMod 2),
      #C+2=#A ∧ 0∉C ∧ IsValidMod (insert 0 C) ∧
      (∃ x∈C, label x=0) ∧ (∃ x∈C, label x=1) ∧
      (∀ m : ZMod M → ℕ, (∑ x∈C,m x)=#C+2 →
        (∑ x∈C,(m x : ZMod M)*x)=∑ x∈C,x →
        (∑ x∈C,(m x : ZMod 2)*label x)=∑ x∈C,label x) := by
  classical
  have hM : 0<M := by omega
  letI : NeZero (2*M) := ⟨by omega⟩
  let f := halfMap M
  let t : ZMod (2*M) := M
  let g := bit (dvd_mul_right 2 M)
  let E := A.erase t
  let S := E.erase 0
  let C := S.image f
  have ht : t∈A := hA
  have tne : t≠0 := by
    have h : t.val=M := ZMod.val_cast_of_lt (by omega)
    intro e; rw [e,ZMod.val_zero] at h; omega
  have gt : g t=1 := by
    change g (M : ZMod (2*M))=1; rw [map_natCast]
    apply ZMod.val_injective (n := 2)
    rw [ZMod.val_natCast,odd]; decide
  have zE : 0∈E := Finset.mem_erase.mpr ⟨Ne.symm tne,zA⟩
  obtain ⟨B,bsize,bdef,inject,bvalid⟩ := merge_pair M hM A zA hA valid
  have iE : Set.InjOn f (E : Set (ZMod (2*M))) := inject
  have iS : Set.InjOn f (S : Set (ZMod (2*M))) := iE.mono (Finset.erase_subset _ _)
  have siz : #C+2=#A := by
    have s := Finset.card_erase_of_mem zE
    have e := Finset.card_erase_of_mem ht
    have non0 := Finset.card_pos.mpr (show E.Nonempty from ⟨0,zE⟩)
    have non1 := Finset.card_pos.mpr (show A.Nonempty from ⟨0,zA⟩)
    change #S=#E-1 at s; change #E=#A-1 at e
    change #(S.image f)+2=_
    rw [Finset.card_image_of_injOn iS]; omega
  have zC : 0∉C := by
    intro hz; obtain ⟨a,ha,e⟩ := Finset.mem_image.mp hz
    have eq0 := iE (Finset.mem_of_mem_erase ha) zE (e.trans (map_zero f).symm)
    exact Finset.ne_of_mem_erase ha eq0
  have eqC : insert 0 C=B := by
    rw [bdef]
    change insert 0 (S.image f) = E.image f
    rw [← map_zero f, ← Finset.image_insert,Finset.insert_erase zE]
  let label (y : ZMod M) : ZMod 2 :=
    if h : ∃ a∈S, f a=y then g h.choose else 0
  have tag (a : ZMod (2*M)) (ha : a∈S) : label (f a)=g a := by
    have ex : ∃ b∈S,f b=f a := ⟨a,ha,rfl⟩
    simp only [label,dif_pos ex]
    exact congrArg g (iS ex.choose_spec.1 ha ex.choose_spec.2)
  have both (r : ZMod 2) : ∃ y∈C,label y=r := by
    by_contra! no
    have small : fiber (dvd_mul_right 2 M) A r ⊆ {if r=0 then (0 : ZMod (2*M)) else t} := by
      intro a ha
      obtain ⟨mem,eqn⟩ := Finset.mem_filter.mp ha
      change g a=r at eqn
      by_cases zz : a=0
      · subst a; rw [map_zero] at eqn; subst r; simp
      by_cases tt : a=t
      · subst a; rw [gt] at eqn; subst r; simp
      have aS : a∈S := Finset.mem_erase.mpr ⟨zz,Finset.mem_erase.mpr ⟨tt,mem⟩⟩
      have yy := no (f a) (Finset.mem_image_of_mem f aS)
      exact (yy ((tag a aS).trans eqn)).elim
    have ct := Finset.card_le_card small
    rw [Finset.card_singleton] at ct
    have lb := bal r; omega
  refine ⟨C,label,siz,zC,eqC.symm ▸ bvalid,both 0,both 1,?_⟩
  intro m count wsum
  change (∑ x∈S.image f,m x) = _ at count
  change (∑ x∈S.image f,(m x : ZMod M)*x) = ∑ x∈S.image f,x at wsum
  rw [Finset.sum_image iS] at count
  rw [Finset.sum_image iS,Finset.sum_image iS] at wsum
  have lift := lift_sum M hM A zA hA valid S rfl (fun a => m (f a))
    (count.trans siz) (by change f _ = f _; simpa only [map_sum,map_mul,map_natCast] using wsum)
  have signs := congrArg g lift
  simp only [map_sum,map_mul,map_natCast] at signs
  change (∑ x∈S.image f,(m x : ZMod 2)*label x)=∑ x∈S.image f,label x
  rw [Finset.sum_image iS,Finset.sum_image iS]
  calc
    _ = ∑ a∈S,(m (f a) : ZMod 2)*g a := Finset.sum_congr rfl (fun a ha => by rw [tag a ha])
    _ = ∑ a∈S,g a := signs
    _ = _ := Finset.sum_congr rfl (fun a ha => (tag a ha).symm)
private theorem labels_edge {M : ℕ} (C : Finset (ZMod M)) (b : ZMod M → ZMod 2)
    (labels : ∀ m : ZMod M → ℕ, (∑ i∈C,m i)=#C+2 →
      (∑ i∈C,(m i : ZMod M)*i)=∑ i∈C,i →
      (∑ i∈C,(m i : ZMod 2)*b i)=∑ i∈C,b i)
    (x : ZMod M) (hx : x∈C) (y : ZMod M) (hy : y∈C) (z : ZMod M) (hz : z∈C) (eqn : 2*x+y=z) :
    b y=b z := by
  classical
  let m (i : ZMod M) : ℕ := (if i=z then 0 else 1) + (if i=x then 2 else 0) + (if i=y then 1 else 0)
  have basic {R : Type} [CommRing R] (f : ZMod M → R) :
      (∑ i∈C,(m i : R)*f i) + f z = (∑ i∈C,f i)+2*f x+f y := by
    have init : (∑ i∈C,if i=z then (0:R) else f i)+f z=∑ i∈C,f i := by
      rw [← Finset.sum_erase_add _ (fun i => if i=z then (0:R) else f i) hz]
      simp only [if_true,add_zero]
      rw [← Finset.sum_erase_add _ f hz]
      apply congrArg (· + f z)
      exact Finset.sum_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))
    simp only [m,Nat.cast_add,Nat.cast_ite,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
      add_mul,Finset.sum_add_distrib,ite_mul,zero_mul,one_mul,Finset.sum_ite_eq',hx,hy,if_true]
    linear_combination init
  have cnt : (∑ i∈C,m i)=#C+2 := by
    have e := basic (R := ℤ) (fun _ => 1)
    simp only [mul_one,Finset.sum_const,nsmul_eq_mul] at e
    exact_mod_cast (show (∑ i∈C,(m i : ℤ))=(#C : ℤ)+2 by linarith)
  have same : (∑ i∈C,(m i : ZMod M)*i)=∑ i∈C,i := by
    have e := basic (fun i => i)
    linear_combination e+eqn
  have color := basic b
  rw [labels m cnt same] at color
  have zz : (2 : ZMod 2)=0 := by decide
  rw [zz,zero_mul,add_zero] at color
  exact (add_left_cancel color).symm
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

private def balancedNat (s : Finset ℕ) : Prop :=
  2≤#(s.filter fun a => a%2=0) ∧ 2≤#(s.filter fun a => a%2=1)

private def skip (xs : List ℕ) : Bool :=
  decide (#(xs.toFinset.filter fun a => a%2=0)<2 ∨ #(xs.toFinset.filter fun a => a%2=1)<2)

private def shortWord (N : ℕ) : List ℕ → ℕ
  | [a,b,c] =>
    if (2*a)%N=(b+c)%N then 3 else
    if (2*b)%N=(a+c)%N then 24 else
    if (2*c)%N=(a+b)%N then 192 else
    0
  | [a,b,c,d] =>
    if (2*a)%N=(b+c)%N then 515 else
    if (2*a)%N=(b+d)%N then 67 else
    if (2*a)%N=(c+d)%N then 11 else
    if (2*b)%N=(a+c)%N then 536 else
    if (2*b)%N=(a+d)%N then 88 else
    if (2*b)%N=(c+d)%N then 25 else
    if (2*c)%N=(a+b)%N then 704 else
    if (2*c)%N=(a+d)%N then 200 else
    if (2*c)%N=(b+d)%N then 193 else
    if (2*d)%N=(a+b)%N then 1600 else
    if (2*d)%N=(a+c)%N then 1544 else
    if (2*d)%N=(b+c)%N then 1537 else
    if (3*a)%N=(b+c+d)%N then 4 else
    if (3*b)%N=(a+c+d)%N then 32 else
    if (3*c)%N=(a+b+d)%N then 256 else
    if (3*d)%N=(a+b+c)%N then 2048 else
    if (a+b)%N=(c+d)%N then 18 else
    if (a+c)%N=(b+d)%N then 130 else
    if (a+d)%N=(b+c)%N then 1026 else
    if (b+c)%N=(a+d)%N then 144 else
    if (b+d)%N=(a+c)%N then 1040 else
    if (c+d)%N=(a+b)%N then 1152 else
    0
  | _ => 0

private def early (N : ℕ) (s : List ℕ) : Bool :=
  let w := shortWord N s
  w != 0 && obstruction N s w

private def walk (N : Nat) (table : Table) : Nat → Nat → List Nat → Bool
  | 0,_,s => obstruction N s (witness table s) || skip s
  | k+1,start,s => early N s || (List.range (N-start)).all fun i =>
      !allowed table N (start+i) || walk N table k (start+i+1) ((start+i)::s)

private theorem certify_children (N : Nat) (tab : Table) (k start : Nat) (s : List Nat)
    (h : ∀ i < N-start, allowed tab N (start+i) = true →
      walk N tab k (start+i+1) ((start+i)::s) = true) :
    walk N tab (k+1) start s = true := by
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.all_eq_true.mpr
  intro i hi
  cases hr : allowed tab N (start+i) with
  | false => simp [hr]
  | true => simpa [hr] using h i (List.mem_range.mp hi) hr

private theorem walk_sound {N : Nat} [NeZero N] (tab : Table) (k start : Nat) (xs : List Nat)
    (good : walk N tab k start xs = true) (hxs : ∀ x ∈ xs, x<N) (s : Finset Nat)
    (size : #s=k) (hs : ∀ x∈s, start ≤ x ∧ x<N ∧ allowed tab N x = true)
    : balancedNat (s ∪ xs.toFinset) → IsValidMod ((s ∪ xs.toFinset).image fun i : Nat => (i : ZMod N)) → False := by
  induction k generalizing s start xs with
  | zero =>
    have empty : s=∅ := Finset.card_eq_zero.mp size
    subst s
    simp only [Finset.empty_union]
    intro bal valid
    change (obstruction N xs (witness tab xs) || skip xs) = true at good
    rcases Bool.or_eq_true_iff.mp good with obstruction | dropped
    · exact obstruction_sound xs _ hxs obstruction valid
    · have bad := of_decide_eq_true dropped
      obtain ⟨even,odd⟩ := bal
      change _ < 2 ∨ _ < 2 at bad
      omega
  | succ k ih =>
    intro bal valid
    change (early N xs || _) = true at good
    rcases Bool.or_eq_true_iff.mp good with found|good
    · obtain ⟨_,cert⟩ := Bool.and_eq_true_iff.mp found
      apply obstruction_sound xs _ hxs cert
      apply isValidMod_subset _ valid
      apply Finset.image_subset_image
      exact Finset.subset_union_right
    have ne := Finset.card_pos.mp (show 0 < #s by omega)
    let a := s.min' ne
    have ha : a ∈ s := s.min'_mem ne
    obtain ⟨lo,hi,yes⟩ := hs a ha
    have child := List.all_eq_true.mp good (a-start) (List.mem_range.mpr (by omega))
    rw [show start+(a-start)=a by omega] at child
    simp only [yes,Bool.not_true,Bool.false_or] at child
    have eqn : s.erase a ∪ (a::xs).toFinset = s ∪ xs.toFinset := by
        ext b
        by_cases he : b=a <;> simp [he,ha]
    apply ih (a+1) (a::xs) child (by simpa [hi] using hxs) (s.erase a) (by rw [Finset.card_erase_of_mem ha,size]; omega)
    · intro b hb
      obtain ⟨diff,bs⟩ := Finset.mem_erase.mp hb
      have least := s.min'_le b bs
      change a ≤ b at least
      exact ⟨by omega,(hs b bs).2⟩
    · rwa [eqn]
    · rwa [eqn]


private theorem cover {N : Nat} [NeZero N] (even : 2∣N) (tab : Table) (k start : Nat) (xs : List Nat)
    (good : walk N tab k start xs = true) (A : Finset (ZMod N)) (valid : IsValidMod A)
    (inside : ∀ i ∈ xs, i<N ∧ (i : ZMod N)∈A)
    (outside : ∀ a ∈ A, a.val ∉ xs → start ≤ a.val ∧ allowed tab N a.val = true)
    (size : #A = k + xs.toFinset.card) (bal : balanced even A) : False := by
  classical
  let F := A.image ZMod.val
  have count : #F = #A := Finset.card_image_of_injective _ (ZMod.val_injective N)
  have sub : xs.toFinset ⊆ F := by
    intro i hi
    obtain ⟨small,red⟩ := inside i (List.mem_toFinset.mp hi)
    exact Finset.mem_image.mpr ⟨(i : ZMod N),red,(ZMod.val_natCast N i).trans (Nat.mod_eq_of_lt small)⟩
  let s := F \ xs.toFinset
  have sc : #s=k := by have h := Finset.card_sdiff_add_card_eq_card sub; change #s+_= _ at h; omega
  have union : s ∪ xs.toFinset=F := Finset.sdiff_union_of_subset sub
  apply walk_sound tab k start xs good (fun i hi => (inside i hi).1) s sc
  · intro x hx
    obtain ⟨mem,abs⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp mem
    have h := outside a ha (fun h => abs (List.mem_toFinset.mpr h))
    exact ⟨h.1,ZMod.val_lt _,h.2⟩
  · rw [union]; obtain ⟨e,o⟩ := (balanced_iff even A).mp bal
    simpa only [balancedNat,F,Finset.filter_image,Finset.card_image_of_injective _ (ZMod.val_injective N)] using And.intro e o
  · rw [union]; simpa [F,Finset.image_image,Function.comp_def] using valid

private theorem smallCase {N : Nat} [NeZero N] (even : 2∣N) (big : 1<N) (k : Nat) (u t : Table)
    (uf : u.onlyNonunits=false) (tf : t.onlyNonunits=true)
    (pu : walk N u k 2 [1,0]=true) (pt : walk N t (k+1) 1 [0]=true)
    (A : Finset (ZMod N)) (zero : 0∈A) (valid : IsValidMod A) (bal : balanced even A) (size : #A=k+2) : False := by
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
    have res := cover even u k 2 [1,0] pu B (affine_valid _ 0 cancel A valid)
      (by intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; rcases hi with rfl|rfl <;> simp [big,b1,b0,show 0<N by omega])
      (by
        intro a _ hh
        have h0 : a.val ≠ 0 := fun e => hh (by rw [e]; simp)
        have h1 : a.val ≠ 1 := fun e => hh (by rw [e]; simp)
        exact ⟨by omega,by simp [allowed,uf]⟩)
    exact res (by simp [B,Finset.card_image_of_injective _ inj,size]) (balanced_image _ A f inj 0
      (fun x => by simp [f,map_mul,bit_unit]) bal)
  · have res := cover even t (k+1) 1 [0] pt A valid
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
    exact res (by simp [size,Nat.add_assoc]) bal
private def tab12u : Table := ⟨2,false,0x4a0e62906208000,0x40004800200104004800200804020800900040c800b0030400c80430016030080c10032080c021800b08900a20128044105021024044821100a20908105004a,0xd0e151513151515101b0d0e00121619101b000d0e1917101b16190d0e10191713000d180012101b13101b1010⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check12u : walk 12 tab12u 2 2 [1, 0]=true := by decide +kernel
private def tab12n : Table := ⟨3,true,0x18a400c0208000,0x40004800200104004800200804020800900040c800b0030400c80430016030080c10032080c021800b08900a20128044105021024044821100a20908105004a,0xc0f0011150d0d0d0d19100e0010150c0f15000d0d0d150e170c10190d0d0014101213⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check12n : walk 12 tab12n 3 1 [0]=true := by decide +kernel
private theorem check_bal_12 (A : Finset (ZMod 12)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=4) : False :=
  smallCase (by decide : 2∣12) (by decide) 2 tab12u tab12n rfl rfl check12u check12n A zA vA bA size
private def tab14u : Table := ⟨2,false,0x16a4a0e62906208000,0x40004800200104004800200804020800900040c800b0030400c80430016030080c10032080c021800b08900a20128044105021024044821100a20908105004a,0xd0e1515151315151515101b0d0e0018121f1619101b000d0e13161817101b001f0d0e1721101b1619130d0e10191721121c0d18001300101b0012101b13101b1010⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check14u : walk 14 tab14u 2 2 [1, 0]=true := by decide +kernel
private def tab14n : Table := ⟨3,true,0x6014041880100000,0x40004800200104004800200804020800900040c800b0030400c80430016030080c10032080c021800b08900a20128044105021024044821100a20908105004a,0xd0d0d0d0d0011100e1400130e1210000c100f0c13000d0d0e13140c130c0c00001010⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check14n : walk 14 tab14n 3 1 [0]=true := by decide +kernel
private theorem check_bal_14 (A : Finset (ZMod 14)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=4) : False :=
  smallCase (by decide : 2∣14) (by decide) 2 tab14u tab14n rfl rfl check14u check14n A zA vA bA size
private def tab22u : Table := ⟨3,false,0x2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x16171717171717171717171717171717171718181818181818181818181818181818182c2c281b1c2c2a2c202c2c242c252c192c2c2c281b1c2c212c242c252c191e2c2c2c2c281b1c202c252c192c1e2c2c2c2a2c241b1c2c192c2c1e2c2c2a242c2520191c2c2c1e2c242c252c192c281b1c1e2a252c192c202c2c281b27192727212727271e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f213f3f3f3f242d251e1617171717171717171717171717171718181818181818181818181818181832373828621b1c202f25402d39193333333328241b1c33332d191e453738244325201b1c19391e45242925402128191b1c1e4325384155192f28351b2937381921342d391e261926262026261e453435212d391e353738202f1e453721391e452d201e2d211e301e1e2815161b1c323f2a203f3f242d252e1e151637381b1c2a2149244225392e1e161717171717171717171717171718181818181818181818181818453237242825201b1c392e1932242a254b21412d1b191e33253333332028192e1b2a40373821192f281e272727192027271e45193721342e1e45582d202e1e342d212e1e2d39201e30211e2e1e1e283415161b1c3f213f242d252e3f1e35151637381b1c204325392e401e1516283738241b1c2d392e411e1617171717171717171717171818181818181818181818432529373820392e5a1942294037213928191e2941422d20192f1e2626261926261e45193920381e2d3921341e302e201e2e211e311e1e283f3415161b1c202d252e3f3f1e3428151637241b1c322e5a401e451516242a25201b1c40411e151643253721322e1b1c1e161717171717171717171818181818181818182a402d32203828192727272127191e2d322e19371e301921301e2e33201e31211e341e1e283f3f3415161b1c2e3f3f321e452835151625201b1c2f321e3524151629212e4c1b1c1e43151628392038412f1b15162939213738321e1617171717171717181818181818182626262026192e3621191e3119201e45211e321e1e283f3f242d15161b1c3f3f1e45243425151637381b1c1e3425281516203738411b422d1516214037381e2d151640205f371e1516302130281e16171717171718181818184561201945191e451e1e28242d252e2115161b1c1e4325392e29151637381b2d342829151640371e302e29151630301e2e29151628361e29151620311e151621261e1617171718181845191e28252e3f2a203415161b3028302a213015161e2e3628352015161e312a312115161e2a404115161e272715161e4515161e15161e1617182836363621363634153128312920313115455b28213541154529352046152941216315262620154521154515152833332a2033331e45282a2142401e452a2820341e2a4021281e2727201e45211e451e1e28323f213f3f1e32282920401e332921331e2941201e26211e351e1e283f2a203f1e452821401e2a32201e27211e331e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_0 : walk 22 tab22u 2 3 [2, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_1 : walk 22 tab22u 2 4 [3, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_2 : walk 22 tab22u 2 5 [4, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_3 : walk 22 tab22u 2 6 [5, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_4 : walk 22 tab22u 2 7 [6, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_5 : walk 22 tab22u 2 8 [7, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_6 : walk 22 tab22u 2 9 [8, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_7 : walk 22 tab22u 2 10 [9, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_8 : walk 22 tab22u 2 11 [10, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_9 : walk 22 tab22u 2 12 [11, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_10 : walk 22 tab22u 2 13 [12, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_11 : walk 22 tab22u 2 14 [13, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_12 : walk 22 tab22u 2 15 [14, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_13 : walk 22 tab22u 2 16 [15, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_14 : walk 22 tab22u 2 17 [16, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_15 : walk 22 tab22u 2 18 [17, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_16 : walk 22 tab22u 2 19 [18, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_17 : walk 22 tab22u 2 20 [19, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_18 : walk 22 tab22u 2 21 [20, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u_19 : walk 22 tab22u 2 22 [21, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22u : walk 22 tab22u 3 2 [1, 0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact check22u_0
  · exact check22u_1
  · exact check22u_2
  · exact check22u_3
  · exact check22u_4
  · exact check22u_5
  · exact check22u_6
  · exact check22u_7
  · exact check22u_8
  · exact check22u_9
  · exact check22u_10
  · exact check22u_11
  · exact check22u_12
  · exact check22u_13
  · exact check22u_14
  · exact check22u_15
  · exact check22u_16
  · exact check22u_17
  · exact check22u_18
  · exact check22u_19
private def tab22n : Table := ⟨4,true,0xa0240801c06290030080100000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x17171717171717161717171717161717171716171717171717171617171717171717171721371a1f1d1618281a211628181a22213f18161b1b18201e181c1818371f2316181d2b211a182a161a18291a1821181b19213f18271a1618251a181e1a19191a16292927391e2739271e19191926211e212c1e1e15151515151515371a211e2c161a22212a3f1b1b161b161e1c1c251e1717171717161717171717171716171617171717172136222a1821221618161e182018183b39162a161e2d27391e16182718211919191e1e2814231a281d14211a303f151515151a1e16161b1c1427223f1a15151515221e16161a1a15151515271e1616281e17171616171716181819212a14361a2114251a141e1a15151627143b39141e28151516141e2a15151615151616282828142b1e14291414211e1429141421141414211e4545211e21451e1e21281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check22n : walk 22 tab22n 4 1 [0]=true := by decide +kernel
private theorem check_bal_22 (A : Finset (ZMod 22)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=5) : False :=
  smallCase (by decide : 2∣22) (by decide) 3 tab22u tab22n rfl rfl check22u check22n A zA vA bA size
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
private theorem check24n_1 : walk 24 tab24n 3 3 [2, 0]=true := by decide +kernel
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
  · exact False.elim ((by decide : allowed tab24n 24 1 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_1
  · exact check24n_2
  · exact check24n_3
  · exact False.elim ((by decide : allowed tab24n 24 5 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_5
  · exact False.elim ((by decide : allowed tab24n 24 7 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_7
  · exact check24n_8
  · exact check24n_9
  · exact False.elim ((by decide : allowed tab24n 24 11 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_11
  · exact False.elim ((by decide : allowed tab24n 24 13 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_13
  · exact check24n_14
  · exact check24n_15
  · exact False.elim ((by decide : allowed tab24n 24 17 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_17
  · exact False.elim ((by decide : allowed tab24n 24 19 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check24n_19
  · exact check24n_20
  · exact check24n_21
  · exact False.elim ((by decide : allowed tab24n 24 23 = false).symm.trans eligible |> Bool.noConfusion)
private theorem check_bal_24 (A : Finset (ZMod 24)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=5) : False :=
  smallCase (by decide : 2∣24) (by decide) 3 tab24u tab24n rfl rfl check24u check24n A zA vA bA size
private def tab26u : Table := ⟨3,false,0x2f6ad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x161717171717171717171717171717171717171717171818181818181818181818181818181818181818182c2c281b1c2c2c2c2a2c202c2c2c2c242c252c192c2c2c281b1c2c2a2c212c2c2c242c252c191e2c2c2c2c281b1c2c2c202c242c252c192c1e2c2c2c2c2c281b1c21242c252c192c2c1e2c2c2c2c2a2c281b1c252c192c2c2c1e2c2c2c2a2c242c211b192c2c2c2c1e2c2c2a242c252c19281b1c2c2c1e2c242c252c19212c2c281b1c1e2a252c192c2c202c2c2c281b271927272721272727271e2c2c2c2c2c202c2c2c1e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f3f3f213f3f3f3f3f3f242d251e161717171717171717171717171717171717171718181818181818181818181818181818181818323738285c1b1c2962202f244225402d39193333333328331b1c2124332533332d191e4537385b6228491b1c2540415819391e4537384c292428211b1c46192d341e45373824432540202f191c2d351e452429254041211928341b1c1e432538416519202f3528391b29373819652135582d391e2619262626202626261e4534356a21582d391e3537384d202d391e453738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f3f3f2a203f3f3f3f242d252e1e151637381b1c4d4e2a21422f49244325392e1e161717171717171717171717171717171717181818181818181818181818181818181845323738282a491b1c254b402d392e19326237382a2443211b1c412d39191e3333332433252820331b1c192e1e45242a254b4021282f191b1c1e432537384155201928392e1b2a4037385519582d34281e2727271927202727271e45193738212d2f2e1e4555343520392e1e34353721392e1e454c2d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c3f323f213f3f3f242d252e3f1e35151637381b1c4d292049244225392e401e1516283738321b1c212443252d392e411e161717171717171717171717171717171818181818181818181818181818184563322429254b20401b1c2e5a1945244325386b21412d391b191e32252937384120282f195a1b3329333333212d1928331e294142373819392e5a1e26262619212626261e45194e2d202e2f1e45582d212e5a1e452d3520381e2d3921371e302e201e2e211e311e1e283f3415161b1c3f2a203f242d252e3f3f1e3428151637381b1c21244325392e42401e4515167037382a1b1c252d392e40411e15166328372432211b1c2f2e414e1e16171717171717171717171717171818181818181818181818181843252a32373820392e5a5b19422a3240372139282f191e2a3241582d202e19281e27272727211927271e33332d192033331e4519392137381e2d392e20341e302e21301e2e35201e31211e451e1e283f3f3415161b1c21242d252e3f3f3f1e452835151637381b1c25322e5a5b401e35631516492429211b1c2e4d40411e4515162443253820321b1c41651e15164325283721322e411b1c1e16171717171717171717171718181818181818181818184529402d322038282f1929412d32213738191e262626262019261e2d322e195f371e30193020301e2e3321331e3131201e45211e351e1e283f3f3f3415161b1c252e3f3f323f1e4528343515162a211b1c462f32401e3435281516252d202e1b1c32411e452415162a2d212e5a401b1c1e4315162a283920384132661b15162a2d39213738322f1e161717171717171717171818181818181818182727272720272719302e302130191e2e363619361e311921311e4532201e32211e331e1e283f3f3f3f2415161b1c3f3f3f3f1e4528492435151620381b1c2f401e4524282515162137384c1b1c1e35254b15162e203738412f1b425815162821403738711e4515162e40206c37381e15162e41215f28371e161717171717171718181818181818313131203119456121191e4519201e45211e451e1e283f3f242d252a15161b1c3f3f1e45244325342a151637381b1c1e432528352a1516553738411b342d39281516554037381e2d392a151620415f371e302a1516212830301e2a1516362036281e1516272127271e1617171717171818181818454c201945191e451e1e28242d252e3f213415161b1c1e4325392e5a2920151637381b2d3928342921151640371e302e302830151630301e2e362936151636361e312931151628311e2941151661611e26151620261e151621631e1617171718181845191e28252e3f3f2a203f3415161b302830302a21303015161e2e36282a34203615161e31312a28213115161e342a61402015161e2a40412115161e27272715161e454e15161e4515161e15161e161718283636363621363636341531283131292031313115456128292134354115455b292820414215452935212863152941552046152626212615454d2015452115451515283333332a203333331e45285b2a216246401e455c28622040341e452a6b2134351e2a403420281e272721271e454e201e45211e451e1e28323f3f213f3f3f1e322862292063401e3333282133331e45294020461e294121341e2626201e35211e451e1e283f3f2a203f3f1e45282a2155401e452a2820411e2a4021281e2727201e45211e341e1e283f3f213f321e45282920321e452921321e2941201e26211e321e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_0 : walk 26 tab26u 2 3 [2, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_1 : walk 26 tab26u 2 4 [3, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_2 : walk 26 tab26u 2 5 [4, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_3 : walk 26 tab26u 2 6 [5, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_4 : walk 26 tab26u 2 7 [6, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_5 : walk 26 tab26u 2 8 [7, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_6 : walk 26 tab26u 2 9 [8, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_7 : walk 26 tab26u 2 10 [9, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_8 : walk 26 tab26u 2 11 [10, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_9 : walk 26 tab26u 2 12 [11, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_10 : walk 26 tab26u 2 13 [12, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_11 : walk 26 tab26u 2 14 [13, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_12 : walk 26 tab26u 2 15 [14, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_13 : walk 26 tab26u 2 16 [15, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_14 : walk 26 tab26u 2 17 [16, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_15 : walk 26 tab26u 2 18 [17, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_16 : walk 26 tab26u 2 19 [18, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_17 : walk 26 tab26u 2 20 [19, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_18 : walk 26 tab26u 2 21 [20, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_19 : walk 26 tab26u 2 22 [21, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_20 : walk 26 tab26u 2 23 [22, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_21 : walk 26 tab26u 2 24 [23, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_22 : walk 26 tab26u 2 25 [24, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u_23 : walk 26 tab26u 2 26 [25, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26u : walk 26 tab26u 3 2 [1, 0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact check26u_0
  · exact check26u_1
  · exact check26u_2
  · exact check26u_3
  · exact check26u_4
  · exact check26u_5
  · exact check26u_6
  · exact check26u_7
  · exact check26u_8
  · exact check26u_9
  · exact check26u_10
  · exact check26u_11
  · exact check26u_12
  · exact check26u_13
  · exact check26u_14
  · exact check26u_15
  · exact check26u_16
  · exact check26u_17
  · exact check26u_18
  · exact check26u_19
  · exact check26u_20
  · exact check26u_21
  · exact check26u_22
  · exact check26u_23
private def tab26n : Table := ⟨4,true,0xc02c0a0240801cc5010030080100000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x17171717171717171716171717171717171617171717171716171717171716171717171717171717161717171717171717171717171717211a372a1d1f2316181a28211f1e1628181b1b1b161b1b182b2261213f1816291e211820201c181c1e182518182137271a1e16182c5b1f1a162d181d271a213f182a16231e18241b1b181b25181c182c19371f2316182a1d2b212218332a162118292922182125181e2019191c213f1830271a16181e251a1821271a191919271a1a16291e292739552d27391e2739271e19191919221e2620201e211e2c30211e212c1e1e1515151515151515151a37211f1e1d2c161b1b1b1b1b161b4c2230212a3f223016211c16201c201c1e2d25251e171717171717171617171717171617171717171717171716171716171717171717171717631f23221a16183621221a2a182321162c18161a21181a1e181b181821363f27181a212516181a1621181a27181a181a193b3916272a16392758321e2d27391e16182c27181e2719191e1919192c211e21301e1e1428281a1e1d242815151515151515361a212a5f3f1a231e2a161b1b161b161e1c1c2e1e151515151515152721221a3f4c23211a2816221a1625161e201b1b1c1717171717171717171716171716171617171717172b3b1e2a1629271629161e3928281e21221618161e1820181816182618211919191e1e281f14221a281d3314221a303f14211a302d151515151a1e16161b1c21142a363f1a14251e251a151515152e1e16161a1a14271e392d15151515281e16165a1e15151515221e1616201e17171616171716181819212a2b14361a212514251a2b142a1a141e1a151516272a143b3928142828141e2915151621142a2e141e28151516141e291515161515161628281e2814582a3b143b1e1455141421222814221e14201414211e142814142114141421224b45221e4220201e211e4545211e21451e1e211e2829211e21291e1e21281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_1 : walk 26 tab26n 3 3 [2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_3 : walk 26 tab26n 3 5 [4, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_5 : walk 26 tab26n 3 7 [6, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_7 : walk 26 tab26n 3 9 [8, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_9 : walk 26 tab26n 3 11 [10, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_11 : walk 26 tab26n 3 13 [12, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_12 : walk 26 tab26n 3 14 [13, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_13 : walk 26 tab26n 3 15 [14, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_15 : walk 26 tab26n 3 17 [16, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_17 : walk 26 tab26n 3 19 [18, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_19 : walk 26 tab26n 3 21 [20, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_21 : walk 26 tab26n 3 23 [22, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n_23 : walk 26 tab26n 3 25 [24, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check26n : walk 26 tab26n 4 1 [0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact False.elim ((by decide : allowed tab26n 26 1 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_1
  · exact False.elim ((by decide : allowed tab26n 26 3 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_3
  · exact False.elim ((by decide : allowed tab26n 26 5 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_5
  · exact False.elim ((by decide : allowed tab26n 26 7 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_7
  · exact False.elim ((by decide : allowed tab26n 26 9 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_9
  · exact False.elim ((by decide : allowed tab26n 26 11 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_11
  · exact check26n_12
  · exact check26n_13
  · exact False.elim ((by decide : allowed tab26n 26 15 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_15
  · exact False.elim ((by decide : allowed tab26n 26 17 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_17
  · exact False.elim ((by decide : allowed tab26n 26 19 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_19
  · exact False.elim ((by decide : allowed tab26n 26 21 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_21
  · exact False.elim ((by decide : allowed tab26n 26 23 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check26n_23
  · exact False.elim ((by decide : allowed tab26n 26 25 = false).symm.trans eligible |> Bool.noConfusion)
private theorem check_bal_26 (A : Finset (ZMod 26)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=5) : False :=
  smallCase (by decide : 2∣26) (by decide) 3 tab26u tab26n rfl rfl check26u check26n A zA vA bA size
private def tab28u : Table := ⟨3,false,0xce2f6ad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x16171717171717171717171717171717171717171717171718181818181818181818181818181818181818181818182c2c281b1c2c2c2c2c2a2c202c2c2c2c2c242c252c192c2c2c281b1c2c2c2a2c212c2c2c2c242c252c191e2c2c2c2c281b1c2a2c2c202c2c242c252c192c1e2c2c2c2c2c281b1c2c212c242c252c192c2c1e2c2c2c2c2c2a281b1c202c252c192c2c2c1e2c2c2c2c2a2c2c241b1c2c192c2c2c2c1e2c2c2c2a2c242c2520191c2c2c2c2c1e2c2c2a242c252c192c281b1c2c2c1e2c242c252c192c202c2c281b1c1e2a252c192c2c212c2c2c2c281b27192727272720272727271e2c2c2c2c2c212c2c2c2c1e2c2c2c2c2c202c2c2c1e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f3f3f3f213f3f3f3f3f3f3f242d251e1617171717171717171717171717171717171717171718181818181818181818181818181818181818181832373828461b1c00294d202f42244325402d39193333333328331b1c33213324332533332d191e453738776528291b1c202f2540414e19391e4537385b622928241b1c40415c192d341e4537387729244325201b1c19582d351e453738244325402128191b1c2d391e45242925404155192f28351b1c1e4325384165192134355828391b293738195534202f462d391e261926262621262626261e4534357742202f2d391e3537384d21582d391e45373877202d391e453738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f3f3f3f2a203f3f3f3f3f242d252e1e151637381b1c4d4e692a21622f7b46244325392e1e1617171717171717171717171717171717171717181818181818181818181818181818181818184532373828622a1b1c20432546402d392e19327837386f2849241b1c2f40412d39191e333333332a242825201b1c332d192e1e4578372443254b21412f1b19392e1e45242a254b40412028192d1b1c1e43253738416c21192f28342e1b2a403738671920582d35281e272727192721272727271e4519373834202d392e1e45783435212d2f2e1e3435373820392e1e45783721392e1e45582d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c3f323f3f213f3f3f3f242d252e3f1e35151637381b1c4d4e2920632f244325392e401e1516283738321b1c2921492443252d392e411e1617171717171717171717171717171717171818181818181818181818181818181818457a323738244325201b1c2d392e5a19453249242925282140411b1c2e191e32244325386b4020582d39191c1e332529333333213328192e331b42294037387720192f285a1e2941423738192d392e341e2626261926202626261e45194e3721342e5a1e4500582d202e2f1e45342d212e4d1e352d3920381e2d3921371e302e201e2e211e311e1e283f3415161b1c3f3f2a203f3f242d252e3f3f1e3428151637381b1c2a2149242f25392e5a401e451516623738631b1c2043252d392e40411e1516462837382a241b1c4b2d392e416c1e1617171717171717171717171717171718181818181818181818181818181845244325373828202d392e1b1c1943252a7837382128392e5a191b422a6b403738203928195b1e2a40416c372139192f281e2727272727192727271e454e5519212e422f1e45192d392038341e452d392134351e2d392e20371e302e21301e2e36201e31211e451e1e283f3f3415161b1c3f213f242d252e3f3f3f1e452835151637381b1c2032252f2e5a6b401e355515165c3738241b1c2d392e5a40411e4515162849242925201b1c2e40414e1e15164924282538212d391b1c4c4c1e161717171717171717171717171718181818181818181818181818425b296b322d2028462f5c19452940322d212e5a28191e2941322d392038192f1e26262626211926261e322d39192037381e2d192e2133331e302e3020301e2e3621341e3131201e35211e451e1e283f3f3f3415161b1c202d252e323f3f3f1e45283435151637241b1c392e2f005b401e3435281516242a25201b1c324d40411e4500151643253721392e1b1c416c1e4515162528582d202e32411b1c1e15164b2a5828212e326c2f5c1b16171717171717171717171718181818181818181818182a402d392e203738281927272727212727191e2d392e322019371e302e301930301e2e193620361e313121311e3333201e45211e341e1e283f3f3f3f3415161b1c2e3f3f3f3f321e4528703435151625201b1c4d2f6b321e45342824151629212e551b1c40321e3524431516293920386b401b1c1e4325151628392137384166321b421516293928203738772f1e151629392e21283738321e1617171717171717171718181818181818181826262626202626192e36362136191e31313119311e451921321e457a201e45211e321e1e283f3f3f3f242d15161b1c3f3f3f3f1e452849243425151637381b1c2f401e452428252d15162037384c1b1c1e34254b28151621783738412f1b42582d15165a20403738711e452d15165a21416c37381e2d1516404120285f371e15163030213030281e16171717171717171818181818181845614d204619456221191e4519201e45211e451e1e283f3f242d252e2115161b1c3f3f1e45244325392e29151637381b1c1e432528342e291516783738411b422d35282915166b4037381e2d392e29151640415f371e302e291516203030301e2e291516213628361e291516312031311e1516262126261e16171717171718181818184563201945191e451e1e28242d252e3f2a203415161b1c1e4325392e5a2a2135151637381b2d39285a2a3520151640371e302e30283021151630301e2e352a3628151636361e312a3131151631311e2a4041151661281e2727151627271e45151620461e1516214e1e1617171718181845191e28252e3f3f3f213f3f3415161b30283030302920303015161e2e3628362921353615161e3131312831203115161e45342961214115161e352940412015161e2941622115161e26262615161e454d15161e4515161e15161e16171828363636362a203636363415312831312a2131313131154561282a422034354115455c2a282135416c15452a3435206c63152a354121632815272727202715454e210015456e2015452115451515283333333321333333331e45285c002920556b401e456f2829215540341e455b29282034351e4529402128691e29343520461e262621261e454d201e45211e451e1e28323f3f2a203f3f3f1e32285b2a217b42401e333328332033331e452a6321416c1e2a404120281e272721271e3435201e45211e451e1e283f3f32213f3f3f1e45283229206b401e4532282140411e32294020461e293321331e2626201e45211e351e1e283f3f2a20323f1e45282a2132401e452a2820411e2a4021281e2727201e32211e331e1e283f3f213f3f1e45282920401e452921411e2941201e26211e451e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_0 : walk 28 tab28u 2 3 [2, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_1 : walk 28 tab28u 2 4 [3, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_2 : walk 28 tab28u 2 5 [4, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_3 : walk 28 tab28u 2 6 [5, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_4 : walk 28 tab28u 2 7 [6, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_5 : walk 28 tab28u 2 8 [7, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_6 : walk 28 tab28u 2 9 [8, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_7 : walk 28 tab28u 2 10 [9, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_8 : walk 28 tab28u 2 11 [10, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_9 : walk 28 tab28u 2 12 [11, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_10 : walk 28 tab28u 2 13 [12, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_11 : walk 28 tab28u 2 14 [13, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_12 : walk 28 tab28u 2 15 [14, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_13 : walk 28 tab28u 2 16 [15, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_14 : walk 28 tab28u 2 17 [16, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_15 : walk 28 tab28u 2 18 [17, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_16 : walk 28 tab28u 2 19 [18, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_17 : walk 28 tab28u 2 20 [19, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_18 : walk 28 tab28u 2 21 [20, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_19 : walk 28 tab28u 2 22 [21, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_20 : walk 28 tab28u 2 23 [22, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_21 : walk 28 tab28u 2 24 [23, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_22 : walk 28 tab28u 2 25 [24, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_23 : walk 28 tab28u 2 26 [25, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_24 : walk 28 tab28u 2 27 [26, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u_25 : walk 28 tab28u 2 28 [27, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28u : walk 28 tab28u 3 2 [1, 0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact check28u_0
  · exact check28u_1
  · exact check28u_2
  · exact check28u_3
  · exact check28u_4
  · exact check28u_5
  · exact check28u_6
  · exact check28u_7
  · exact check28u_8
  · exact check28u_9
  · exact check28u_10
  · exact check28u_11
  · exact check28u_12
  · exact check28u_13
  · exact check28u_14
  · exact check28u_15
  · exact check28u_16
  · exact check28u_17
  · exact check28u_18
  · exact check28u_19
  · exact check28u_20
  · exact check28u_21
  · exact check28u_22
  · exact check28u_23
  · exact check28u_24
  · exact check28u_25
private def tab28n : Table := ⟨4,true,0x380d0316a0240801c06014041880100000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x17171717171717171717171617171717171717171717171717171717171717161717171717171716171717171716171717171716171717171717171717171717171717171717171717171717171721271a1d4c30611f233f18211a2a1d1e1f242316181a21281f1d281628181b1b1b161b1b1b183916321e21241830384d1e1c182f2f1c2d1863231e18233f1825181839271a1d1e1f233b162c271a5a1f1d2316322c1a1f281623281d281b161b1b1b1b1b3200231e701c3923701c2c231c1e2c252525392c1e21271a1f1d3716182c271a22162d2a182c1a16211e2818281b1b1b1b181b202020181c252518253f182c182c19211f23162d181d2c39161a1e183324231a6318332c1a251825211b181b1b18332c19191e2116181e271a2a2518251e1a251830271a2c19191919271a2c1a281b1833221e3727191919191922301e212020202f271e2134222d2c00221e2c22762120201e37211e2c76212c30211e21222c212c1e392c1e1e142a1a1d2b61001f232c3f151515151515151515151a212a1f1d2d232c161b1b1b1b1b1b161b2b39351e16241c2916291e1c2138631c2c2400231e2d232c3f25251e15151515151515151515281a281f1d232828161a1f001e232d16701b1b1b1b161b1b2916231e291c7023321c58231c1e2d2525252c391e171717171717171716171717171717161717171717161717171617171717171717171717171717171717171717211f231a302d161827211a1e162a182316281e28181a252525181b1b1b182f2c182c18182139221e1618322516251e1825220030183820201820301876182f19211622182729372218273322181e2118202019191e18262226261919191922262120201e7a211e2d33215f2c211e21223021301e2c391e1e28141a1d1e1f23282828141a391f1d232c3b7015151515151515151b1b1b1b1b1b163b70231e161c5523161c2d231c1e322525252e2e1e14281a1f1d2828282815151515151515151a22211e2a2d161b1b1b1b161b202016201c25251c252c2f2f2e2e1e151515151515151528211a1e282816231a371e162a1a251625211b1b1b1b2c3f762e1c1e171717171717161717171716171717161717171717171717171717172136221e1618362216301822271e1820201828181821411618277a2218272218211820194d181e3018213019191e212233212e1e2e2e1e1e21141a1f1d2c466845141a221e2c681d00151515151515151b1b1b1b1b16202020161c25161c252e2e2e004b1e141f231a2c431d4515151515151515231a2c1e00161a252516211b161b1b2e2e2e4b1c1e151515151515152521251e1a16222c45164b20161a202e1a2e1a461b171717171716171717161717161717171717171717212c2216182c161e18222e182018182c1618452e182e18211918222e19191e31311e1e2114231a28281d2814211a1e3434241515151515151a252525161b1b161b4c763f381c1e142b221e391a351515151515152229291a1620201620761a001a381b15151515151527222129162228162120202037371e17171717161717161717171717171726211618262118261818211831183119005a1e1e2128141e281a282514251e1a25142e2e1a2a15151515361a3f1a161b2114221e343014222128281515151520202036161e142e222e2a1515151522002120161e1515151531212731161e1717171716175a161e182128221e14282b2221143622291421201420143415213122143128221428221421142015292114293f14611421152114261426151455151521282228282b221e2a22292120201e2b211e2a27212928211e21222721271e26261e1e28211e282b212a29211e21222a21291e29271e1e21223f21281e272a1e1e28281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_1 : walk 28 tab28n 3 3 [2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_3 : walk 28 tab28n 3 5 [4, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_5 : walk 28 tab28n 3 7 [6, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_6 : walk 28 tab28n 3 8 [7, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_7 : walk 28 tab28n 3 9 [8, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_9 : walk 28 tab28n 3 11 [10, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_11 : walk 28 tab28n 3 13 [12, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_13 : walk 28 tab28n 3 15 [14, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_15 : walk 28 tab28n 3 17 [16, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_17 : walk 28 tab28n 3 19 [18, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_19 : walk 28 tab28n 3 21 [20, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_20 : walk 28 tab28n 3 22 [21, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_21 : walk 28 tab28n 3 23 [22, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_23 : walk 28 tab28n 3 25 [24, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n_25 : walk 28 tab28n 3 27 [26, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check28n : walk 28 tab28n 4 1 [0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact False.elim ((by decide : allowed tab28n 28 1 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_1
  · exact False.elim ((by decide : allowed tab28n 28 3 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_3
  · exact False.elim ((by decide : allowed tab28n 28 5 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_5
  · exact check28n_6
  · exact check28n_7
  · exact False.elim ((by decide : allowed tab28n 28 9 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_9
  · exact False.elim ((by decide : allowed tab28n 28 11 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_11
  · exact False.elim ((by decide : allowed tab28n 28 13 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_13
  · exact False.elim ((by decide : allowed tab28n 28 15 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_15
  · exact False.elim ((by decide : allowed tab28n 28 17 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_17
  · exact False.elim ((by decide : allowed tab28n 28 19 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_19
  · exact check28n_20
  · exact check28n_21
  · exact False.elim ((by decide : allowed tab28n 28 23 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_23
  · exact False.elim ((by decide : allowed tab28n 28 25 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check28n_25
  · exact False.elim ((by decide : allowed tab28n 28 27 = false).symm.trans eligible |> Bool.noConfusion)
private theorem check_bal_28 (A : Finset (ZMod 28)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=5) : False :=
  smallCase (by decide : 2∣28) (by decide) 3 tab28u tab28n rfl rfl check28u check28n A zA vA bA size
private def tab30u : Table := ⟨3,false,0x37ace2f6ad2728c1ee6b16a4a0e62906208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x1617171717171717171717171717171717171717171717171717181818181818181818181818181818181818181818181818182c2c281b1c2c2c2c2c2c2a2c202c2c2c2c2c2c242c252c192c2c2c281b1c2c2c2c2a2c212c2c2c2c2c242c252c191e2c2c2c2c281b1c2c2a2c2c202c2c2c242c252c192c1e2c2c2c2c2c281b1c2c2c212c2c242c252c192c2c1e2c2c2c2c2c2c281b1c2c20242c252c192c2c2c1e2c2c2c2c2c2a2c281b1c2c252c192c2c2c2c1e2c2c2c2c2a2c2c24281b1c192c2c2c2c2c1e2c2c2c2a2c242c2521191b1c2c2c2c2c1e2c2c2a242c252c19202c281b1c2c2c1e2c242c252c192c212c2c2c281b1c1e2a252c192c2c2c202c2c2c2c281b2719272727272127272727271e2c2c2c2c2c2c202c2c2c2c1e2c2c2c2c2c212c2c2c2c1e2c2c2c2c2c202c2c2c1e2c2c2c2c212c2c2c1e2c2c2c2c202c2c1e2c2c2c212c2c1e2c2c2c202c1e2c2c212c1e2c2c201e2c211e2c1e1e15161b1c3f3f3f3f3f3f3f3f213f3f3f3f3f3f3f3f242d251e161717171717171717171717171717171717171717171717181818181818181818181818181818181818181818181832373828651b1c0069294e202f7a49244325402d39193333333328331b1c293321333324332533332d191e453738775c286e1b1c7a2024432540414219391e4537386e656f28701b1c4325404167192d341e4537385b62294924431b1c414619582d351e453738772924432521411b195c342d391e45373824432540412019681b1c2d391e4524292540416719683428581b1c1e43253841651968202f005828391b293738196534217164582d391e26192626262620262626261e45343577422176582d391e3537384d4e202f2d391e4537386a214d2d391e45373877202d391e453738212d391e453738202f1e453721391e452d201e2d211e301e1e2815161b1c323f3f3f3f3f2a203f3f3f3f3f3f242d252e1e151637381b1c4d4e69002a216d2f7a7b49244325392e1e16171717171717171717171717171717171717171717181818181818181818181818181818181818181818453237382870651b1c7b202443254b402d392e19327837385b282a7b1b1c43254b40412d39191e33333333332a2824331b1c3333332d192e1e456237382a24432521401b1c5819392e1e4578372443254b40206c67191c392e1e45242a254b4041216719462d1b1c1e43253738416a6519685828352e1b2a403738671921002f2d39281e27272719272720272727271e451937383421582d392e1e4574343577202d392e1e34353738212d2f2e1e456e373820392e1e45783721392e1e45582d202e1e452d212e1e2d39201e30211e2e1e1e283415161b1c3f323f3f3f213f3f3f3f3f242d252e3f1e35151637381b1c4d4e792920422f49244325392e401e1516283738321b1c62292163492442252d392e411e1617171717171717171717171717171717171717181818181818181818181818181818181818184579323738282924431b1c2f402d392e4e1945324c3738242825214c1b1c2d392e191e3263492429254b2820412f1b1c195a1e332433253333332128332d191b1c1e43252937384155205819392e5a1b42294037385521192d3928341e294142373819202d2f2e351e262626192621262626261e45194e373820352e5a1e45556a3421392e5a1e4534352d202e2f1e354c2d212e4c1e452d3920381e2d3921371e302e201e2e211e311e1e283f3415161b1c3f3f322a203f3f3f242d252e3f3f1e3428151637381b1c322a217c49244225392e5a401e451516703738771b1c6e202443252d392e40411e151664283738322a1b1c43252f2d392e416c1e1617171717171717171717171717171717171818181818181818181818181818181818456d49242a25287020402d1b1c5a67194524322537386b21412d2f2e1b191e43252a783738412028392e19681b322a6b403738212d39195a001e2a333333333320192e33281e272727272719272727271e454e67192d202e5a341e45194d2d212e342f1e45582d392035761e452d342137381e2d352e20371e302e21301e2e36201e31211e451e1e283f3f3415161b1c3f3f21323f242d252e3f3f3f1e452835151637381b1c2920244325392e426b401e356f15167837386e1b1c43252d392e5a40411e451516285c373824321b1c2d2f2e4041661e1516646f2824292521581b1c2e416c4d1e1617171717171717171717171717171718181818181818181818181818181843254b2932373820392e2f006519425b293240372139285a67191e45293241582d202e46195c1e29326a582d212e19686f1e2626262626192626261e33332d19213333331e4519392e2037381e2d392e215f341e302e3020301e2e3421361e3131201e45211e451e1e283f3f3f3415161b1c2a20242d252e3f3f3f3f1e45283435151637381b1c4325322e5a5c69401e34352815166a3724431b1c322e4e6540411e457c151649242a25212d1b1c2f40414e1e451516242825373820322e1b1c4c4c1e151643252a283721322e412f1b1c1e161717171717171717171717171718181818181818181818181818452a42402d322038287067192a40412d3221373867191e2727272727202719271e452d322e211937381e2d322e19205f371e3019302130301e2e333320331e313121311e4561201e34211e451e1e283f3f3f3f3415161b1c2d252e3f3f323f3f1e4528463435151624291b1c2e462f325b401e4534286e1516432521391b1c663240411e350049151625292d202e5a1b1c416c1e4524151628292d212e5a40321b1c1e43151600292839203841322f5c1b151664292d392137383271751e1617171717171717171717171818181818181818181818292d392e5a203237381926262626212626191e302e30302019301e2e36361936361e31193120311e453221611e327a201e33211e451e1e283f3f3f3f3f3415161b1c3f3f3f3f3f3f1e4528700034241516212e1b1c4d2f64401e456e2824431516392038661b1c40411e3424432515163921373846401b1c1e43254b1516392e203738416c711b42001516392821403738662f1e451516392e40206c3738661e1516392e41216f2837381e161717171717171717171818181818181818182e363636203636193131312131191e45616119461e4519217b1e457b201e45211e451e1e283f3f3f3f242d2515161b1c3f3f3f3f1e45284924432535151637381b1c2f401e452428252d3915164c37384c1b1c1e4325352839151620553738412f1b35582d3915162155403738711e452d3915162820414637381e2d3915164021285f5f371e3015163030203028301e15163636213636361e161717171717171718181818181818457962204619454c21191e4519201e45211e451e1e283f3f242d252e2a2015161b1c3f3f1e45244325392e2a21151637381b1c1e432528392e2a661516783738411b422d34282a0015166b4037381e2d352e2a28151640415f371e302e2a301516303030301e2e2a361516202836361e2a311516213131281e271516272027271e151664217a7b1e1617171717171818181818456d201945191e451e1e28242d252e3f3f213f3415161b1c1e4325392e5a00292035151637381b2d39285a5f29215f151640371e302e3028293020151630301e2e3435292821151636361e3131293131151631311e45294041151628611e29416915167a6f1e2626151626261e45151620461e1516214d1e1617171718181845191e28252e3f3f3f2a203f3f3415161b30283030302a2130303015161e2e3628362a3620353615161e313131283121313115161e455c2a3528204115161e342a6640212815161e2a4041552015161e2727272115161e454e6315161e457c15161e4515161e15161e16171828363636363621363636363415312831313129203131313115456128612921613435411545006928702035416c15455b29342141466315452935412028701529416c21716915262626202615454d216e154500201545211545151528333333332a20333333331e452869002a216d626b401e456f282a74204240341e455c2a28214034351e452a6b402035711e2a4034216f281e27272720271e454e21001e456e201e45211e451e1e28323f3f3f213f3f3f3f1e32285c7929204263401e33332829213333331e455b29282041691e4529402128341e29415520351e262621261e354d201e45211e451e1e283f3f322a203f3f3f1e4528322a217c46401e453228702040411e322a6b21416c1e2a333320281e272721271e454e201e34211e451e1e283f3f3f21323f3f1e45286429206b401e455b282140411e45293220461e2932216f1e2626201e33211e451e1e283f3f2a203f3f1e45282a2155401e452a2820411e2a4021281e2727201e45211e451e1e283f3f213f3f1e45282920401e452921411e2941201e26211e451e1e283f2a203f1e452821401e2a40201e27211e451e1e283f213f1e4528201e29211e261e1e282a201e2a211e271e1e28211e291e1e281e1e1e⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_0 : walk 30 tab30u 2 3 [2, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_1 : walk 30 tab30u 2 4 [3, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_2 : walk 30 tab30u 2 5 [4, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_3 : walk 30 tab30u 2 6 [5, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_4 : walk 30 tab30u 2 7 [6, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_5 : walk 30 tab30u 2 8 [7, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_6 : walk 30 tab30u 2 9 [8, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_7 : walk 30 tab30u 2 10 [9, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_8 : walk 30 tab30u 2 11 [10, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_9 : walk 30 tab30u 2 12 [11, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_10 : walk 30 tab30u 2 13 [12, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_11 : walk 30 tab30u 2 14 [13, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_12 : walk 30 tab30u 2 15 [14, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_13 : walk 30 tab30u 2 16 [15, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_14 : walk 30 tab30u 2 17 [16, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_15 : walk 30 tab30u 2 18 [17, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_16 : walk 30 tab30u 2 19 [18, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_17 : walk 30 tab30u 2 20 [19, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_18 : walk 30 tab30u 2 21 [20, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_19 : walk 30 tab30u 2 22 [21, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_20 : walk 30 tab30u 2 23 [22, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_21 : walk 30 tab30u 2 24 [23, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_22 : walk 30 tab30u 2 25 [24, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_23 : walk 30 tab30u 2 26 [25, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_24 : walk 30 tab30u 2 27 [26, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_25 : walk 30 tab30u 2 28 [27, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_26 : walk 30 tab30u 2 29 [28, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u_27 : walk 30 tab30u 2 30 [29, 1, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30u : walk 30 tab30u 3 2 [1, 0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact check30u_0
  · exact check30u_1
  · exact check30u_2
  · exact check30u_3
  · exact check30u_4
  · exact check30u_5
  · exact check30u_6
  · exact check30u_7
  · exact check30u_8
  · exact check30u_9
  · exact check30u_10
  · exact check30u_11
  · exact check30u_12
  · exact check30u_13
  · exact check30u_14
  · exact check30u_15
  · exact check30u_16
  · exact check30u_17
  · exact check30u_18
  · exact check30u_19
  · exact check30u_20
  · exact check30u_21
  · exact check30u_22
  · exact check30u_23
  · exact check30u_24
  · exact check30u_25
  · exact check30u_26
  · exact check30u_27
private def tab30n : Table := ⟨4,true,0x149ca3003dcd0300b5240801cc50106208000,0x50006800980050030800d00830026001406020184006820180830026001430020c04030800d20030806020c009800584006002020244010808a00a40110006010021204080841101220084221028208140228109005204080110006080029004400a0810902040500884110122008510114024084110884102824014102804510120424014880202040088003192016402580c820b0430480c904320164121820b0096190096016082190486082c16012182406490190432016490190430486402c105804b44905120944125044825104940a20928128124224908905124844828825124844828825024a,0x1515151515151515151515151515151515151a2a371d3737372b37373737371f37232c1b1b1b1b1b1b1b1b1b1b1b1b1b1b1b1640396e2a6a1d002d461f3b3516231c404349212a1d6b1f5c3516381c2c3958622b2a1d2d3b16381c232c39432b1f3b1e161c4969232c401f3b16381c69212a231d2b35381c4e246149212a161c292929292923293942551e2d00232c40396e1e2d232c4043616b232c39431e232c40391e2c40232c231e2517171717171717171717171717171717171717171717171717171717171717171617171717171717171717171716171717171717171717171717161717171717171717171717161717171717171717171716171717171717171716171717171717171717171717171717171716171717171717171717171717171717171717171717171717171717171717171717171717171717171717171727401a1d6e712b1e006c5a1f233b3f16281a2828281d2828281f28231628281a40436a2a1d5c1f24641645322c1b1b1b1b1b1b1b1b161b1b1b1b39402b1f3b1e161d23703f1c671f3b16451e70231c3f1d2b40433238651c773f2a162929291c2329212939401c1e236e3f2c6739001e2d3f2c4e4023433f2439231e2d2c23391e2c2525253f1e2c37211a2a371d222d371f2337163718271a6a432a1d751f6123163f32181a212828221d282816282828181b1b1b1b1b1b161b1b1b1b18001f2216001e23242a77182b2200326121653f1c181629292923291c29182020201c20202018001c231e2d6b186123403f421823631e2d1825251e183f3918411818216a27401a1d301f233f1618322c2127371a2a1d2d23163718372c27001a1f301e161d2418002c281a2816281e282818281d1a003032213f3818652a161b1b1b1b1b181b1b3072231e2d186b1c2f232f1e182f2c233f1c18402c1c2518252541181e2c18392c19192c39584e271a1d233b161832332c3921271a3b1e161d186f332c641f1a16231e00182a331d271a672140431838242a1628232828182828281b1b1b1b181b1b1b233900182d331c252518251c2539181c2d2c18391e2c191919331e2c21372b1f1a1e16183724372c5b1f2116301e185b2a241d2b271a303f184333382a161a292118292929241a282818282128281b1b181b1b1b1b2f182f2f2f2c18411e2d1c1919191933392c341e2c371f231622181a372a371d2b213f22181a4000432a162122181a292929292522181a2525252522181a1e2d4121181a2020202019191919191b1b1b1b74392c001c2c213f183222004e27401a16182522252525251a1841211e2d27411a1919191919191922713827651a20201e201a79271e1a27351a281a1a1629292929292929273921551e2d0042273339001e2d382734343434212739381e2d275c391e27353927641e2719191919191919192626211e26262626262621262626261e262126261e26262626261e263721221e2d372c4c21306a352c22301e2d2c20201e202f2f2c771e2c216a2230642c21221e2d2c22301e212020202f1e2c39621e2d2c49391e2c45392c381e2c37211e2c223021201e2c21222c221e20211e2c21141a281d2828282828282828281f232828151515151515151515151515151515151b1b1b1b1b1b1b1b1b1b1b1b1b1b164039212a4d1d4d1f4d3b4523163866436e21001d71244535162c1c4b39431f211e4516381c2c65401f434535161c2a232c1d40393516382d65212a6d4516381c6524232c211c32431e6d232c004042431e232449403943232c5866391e2c2440231e43232c39251e2e15151515151515151515151515151515371a3737371d3737371f3723352c161a39432a4b1d711f243b2345163f1b1b1b1b1b1b1b1b1b1b161b1b40394d1f4d1e351623382c1c661f7335451638231c2c1d58394316612d1c582a3f351643381c234e213f38321c1e237b2c3f6540721e6b2c3f613923432c2440231e2c3f23401e3f2525252c1e2e1717171717171717171717171717161717171717171717171717171617171717171717171717171617171717171717171716171717171717171717161717171717171717161717171717171716171717171717171717171717171717171717171717171717171717171717171717171717171717171717172139402a1a1d6d1f233b3f6f16182142401a431d3523243f162c1867391a1f431e231624452c186d1a00214c16452a242c181a394016212d3f382a181b161b1b1b1b1b1b184532231e3f432c183823651e1c2c1823391c402c181c251e25183f671e18412c182c1818364e27401a1d23753f6e1618743721371a371e371637371837271f1a4023163f2a5b181d281a28162828282818281a1623403f433818771b1b1b1b1b1b181b23383f1e40181c2525252518253f391c1840414118414b1839181e192139671f1a1e431658182c45351f211a4016432a18241d58391a16402d43182a3800166d21456a182c241a32451e38182c431b1b1b1b181b1b383965182c406539182c1c71181e67182c3919192e361f23672216182a432c1d37213716371837372a37231622671840452c4325222518252525252245181e672c2120182020202018391e2c67191919195b2c392c1c2e21396f16182d27402a1a21162518252525251a0032181e27452c1a7118451e212c1a183927382c1a191919191927651e1a28281a2c1a1a3616185b305b4e27403718371e37372737184e301e5f273819191919191930391e27772f2f1e2f5f2739271e281832001e734b2c45191919191919196f3945212c3845391e2c2138461e655c2c352c1e2e3321221e002c45342134342c3422391e2c0020201e20352c392c1e2e2139226d2c3521221e2c4522451e212020202c1e2e36391e2c5f37371e37452c392c1e2e36211e45222c21201e2e212239221e20211e2e2114281a1d2828281e2828281f232828281515151515151515151515151515151a372a37371d371f2437232c37351b1b1b1b1b1b1b1b1b1b1b1b165a66391f2a1e3b1d2316381c401f393b451e16231c4e1d4062436135381c2a32623b3935161c232c212a16381c1e232c426d4032391e2c2d584042232c63246d231e432d232c1e392525252e1e40151515151515151515151515151515361a2a436a1d301f75233b2c353f1a21372a221d372d23372c37161b1b1b1b1b1b1b1b1b161b1b4d1f22304d1e16242c4d1c002230350021382a1c3f22300016232d1c772a1620201c202020202f1c231e2c2d240023392c423f23721e6b2d25251e252c403f2e1e3f1717171717171717171717171717171717171717171717171717161717171717171717171617171717171717171617171717171717171717171717171717171617171717171617171717171717171717171717171717171717171717171717171717171717171717176927402a1a1d232d3b3f2c64162721391a2a1e3b1d3f16456f281f1a28231e162828281d671a402164433f2a24381a392316002d2c382a161b1b1b1b1b1b1b2332391e2c2d1c252525251c25003f1c402d3f2c1e392c41412e1e672100271f1a1e301d00160018371f211a371e16372c241827001a40303f432a3218281a281628282828181672301e00216b181b1b1b1b1b1b18303f392c40182f2f1e2f18411c1e182c67182e1818631f2327221e166318631d362127223f1a6f183200232122161a2d18372a1622251a2518252522281a1e182821201a201820201a4118412d1b181b1b186c7119190021363f622218402a321a21252516182525251a16372118372c371a4122181e212d1a2218392c381a18201e201a191919192c5c1a2e1a1a3b396a16002d27332a1621391e672733004e32391e272d5849423927213800711e332d38271e39273365281e341641181e302c41273718211e2c2d271871302142271919191919302c1e272c2f272e1e27191919191919193621392c456a22371e372d20201e202c38762e1e752136222c305f21221e302d222c1e212020202e1e2f69361e6a2d362c1e392c37372e1e387a211e30224521201e30212236221e20211e452133141a436a1d22006c1f232c683b45141a3434341d341f2d232c343434151515151515151515151515151b1b1b1b1b1b1b1b1b1b1b16401f22433b1e232416381c402239436e2116381c4e22453943162c1c2a642020161c20202020381c231e43692440232c39422d232c1e394325251e252e2e2e401e40144039421a1d6e1f23732c3b3f351515151515151515151515151566401a1f431e231d24453f16751a68213b1e452c163f1d1a403972216b166e3f381b1b1b1b161b1b1b1b4540161e2c43321c6223001e1c3f4323321c393f2d1c251e25252c661e4b2e2e2e3f1e41151515151515151515151515153621401a6a1e301d2c3f4516371f1a37231e372c16371d611a39213043163f24491a352330162c3f2a381b1b161b1b1b1b1b2330381e3f6b1c252525251c252f2c1c2f2f2c3f1e402e2e2e411e5a171717171717171717171716171717171717171716171717171717171716171717171717171617171717171716171717171717171717171717171717171717171717171717171717171717171717691f2300221e1a2c1678184e213922401a166b431823212264162c452a182522161a2525251822451a1e003818201a202020181a2c1e39181b1b1b182e2e186c18182169393f22401618421a21252522162518251a003f161e2c18321a3f22451e186f1a22322c18411a202018201a2c181e1a182e1a19191a723639621618402a5c3621161e186a32403737371837373749321839212d62181e393818381e71191919771e5a213616182c4b27453649181e45274237182c21272d182c1e2721191919192e272e271e286918221e00334518212c39332d191919191920201e202e2e2e331e34213222396a2d21221e394522451e21202020621e35332c1e39302c341e302e2e2e371e302c211e45222e21201e3721222e221e20211e3121211436391a1d711f232c58753b3f1428281a281d28232428282828151515151515151515151515371a2b21371e2c2d2437161a2b0039212a3500163f1b1b1b1b1b1b161b1b292923162929291c00162c1e1c772d232c1c00323f1c251e25252e2e1e2e74403f721e3f142a36391a1d236e2c5f3b3f6f151515151515151515151515361f1a39231e2c2d6e3f16371a3721372a373716371a3b23392c43163f6e1b1b1b161b1b1b1b23162c1e393f1c252525251c252c401c3f392e2e1e2e4b3f403f1e41151515151515151515151515281f211a281e2828282416362b1a39002a433f16002b1a37212c371637241a292916292129291b161b1b1b1b1b002c383f32002c001e771c2e1c1e2e3f6500411e71171717171717171717171617171717171717171617171717171717161717171717161717171717161717171717171717171717171717171717171717171717171717212b3639222a30001618212525222525162518292921162929291837162c1e213718222c3000321820201e20182e2e1e182f2f187718182b3b3639274016180029212916292918293616271e39182d37273737183727671e183928281828381867181e1921292916291829294116211e18412d362c451832002c371837212e181e2e1838761919752616181e26262626182626262618261e262619191919262626261e26182c223632301919191919222e1e21202020371e302c781e33392e2e1e2e453378331e342e211e2e224521201e36212231221e20211e4521282828141a1d232828282828286921141a391e2c1d2d3b455533141a2a231e3b452d6a1d141a34212a34343424341515151515151515151b1b1b1b1b1b1b16232c001e16381c252516251c25162e1c2e2e40001e5a405a5c401e402128141f1a1e281d282428283414211a341e30342d241d14361a622a30435f5c3f1515151515151515151a372c1e372137161b1b1b1b161b1b2c30165f383f162e1e2e1c2f1c1e2f5f403f5b1e3f0014232a221e1a302d001d142136222a1a303f354c1515151515151515152522251a25252516222c1a1e163721201a16202020162e1e2e2e1b1b1b1b2f2f2f411c4c14002740223f3530421a1515151515151515152772211e79306b162822281e16281a223f1630401a16201e201a41301e1a30381a2f1a1a1515151515151515153b21271e403942166627001e16403927421664214016281e282866001e5a625a38381e5c1717171717171716171717171617171717161717171617171717171717171717171717174121221e1641182c2116364518162e1e2e1820201e183646183718182171161869361622182e2e22181e2118202019193616181e2e2e18691e5a191919461e4e19191919223121201e31212261221e20211e4521212a65141a1e431d71243b45401f141a2c1e433b45241d40141a2a7239435c2d58141a2c214539436e2415151515151515151b1b1b1b1b1b162e2e2e2e162e003516381c381c1e0040726b401e40271f1466221e1a3b433f1d28142822281a28282828142122661a39453f43151515151515151522451a1e663f16201a202016201a40163f661b1b1b1b383f403f1c412114402a22393f6f2d1a14252522252525251a15151515151515152c22451e216d16222e2e2e161a202016201a3f001e1a41411a381a1a144e2740363935305f15151515151515152735361e403016282828281628366616304037371e375a305f301e2f15151515151515152c49211e4540162e2e2e21162e453616552136461e00373737621e3817171717171716171717171617171716171717171717171717171717212e222e1618212216551822451e182020186e1818313116183131311831311831181e196d181e4518452119194d21227b221e20211e4521281f2314221e1a2828281d00211422361a3930433f2314222a1a0030002d1422251a2525252515151515151515201a202020201a371e37161b161b1b30383f2f1c3f2127145c2236393f301a21142522252525251a1428211e2828281a151515151515152236353f301a20201e201637161e1a3f301a301a1a0014402a3b36396a2d14213b1e362a35391515151515151549353640216b00361e401636161e00373737621e381472271e002a6b3015151515151515273f4521403028281e281641161e30366230371e30151515151515153f216927453622411e411620161e20274636281e361717171717171717171716171617171717171717176e711e641649161e6945694e461e6700161e18224518201818182200191920211e4521212a002b22146636391a21252522142525251a2e2b21142e2e2e1a2b22141e21001a22142929291a14201e201a1515151536351a37161a272a2b0014663b363928212814282828282b3b141e00362a29142929212914401e360015151515353640361637212b2e142e2e2e2e2828141e282828291429212929147a1e0021151515153f6d364116362b21141e31312a29142929292914311e31311515151531313131163121142229292714221e41271515151520202000162714261e262615151515262626261626151515152245212016001717171716172116451828282828282828281400212a1e5c3b3314402b3b1e2a33142b425a6b211429291e291440001e144033143314142128281e28282814312b211e2a31142b313121311429291e291431311e143131143114147721221e2a6b142721403f451422281e281420201e143f4614411414213f2227401421221e291422271e1420201428141429291e2914496f1e1435631446141426211e1422261420141421221422141421141414212a001e754b32454049211e456242403245212a6d45691e6d2140461e0040726b401e402721221e00334528212828282822401e330020201e20693340331e34213222402a5c21221e404522451e21202020711e35335b1e274034341e3445276f271e286f211e45224521201e6f21226e221e20211e45212821221e28282875213b2a323f22721e6b2a20201e2061403f631e3f2127222a323321221e5b2a22281e21202020411e333b3f1e332a3f271e6f273341281e3441211e27224521201e27212271221e20211e4521212a22753b3f21221e282822291e21202020721e3f27401e3f6f28281e28453f403f1e4129211e29224521201e71212226221e20211e452128281e28282b3b1e2a292929401e4028211e28222921201e3f212227221e20211e262140211e45224521201e40212240221e20211e452121222a221e20211e2721211e292121⟩
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_1 : walk 30 tab30n 3 3 [2, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_2 : walk 30 tab30n 3 4 [3, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_3 : walk 30 tab30n 3 5 [4, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_4 : walk 30 tab30n 3 6 [5, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_5 : walk 30 tab30n 3 7 [6, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_7 : walk 30 tab30n 3 9 [8, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_8 : walk 30 tab30n 3 10 [9, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_9 : walk 30 tab30n 3 11 [10, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_11 : walk 30 tab30n 3 13 [12, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_13 : walk 30 tab30n 3 15 [14, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_14 : walk 30 tab30n 3 16 [15, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_15 : walk 30 tab30n 3 17 [16, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_17 : walk 30 tab30n 3 19 [18, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_19 : walk 30 tab30n 3 21 [20, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_20 : walk 30 tab30n 3 22 [21, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_21 : walk 30 tab30n 3 23 [22, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_23 : walk 30 tab30n 3 25 [24, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_24 : walk 30 tab30n 3 26 [25, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_25 : walk 30 tab30n 3 27 [26, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_26 : walk 30 tab30n 3 28 [27, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n_27 : walk 30 tab30n 3 29 [28, 0]=true := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem check30n : walk 30 tab30n 4 1 [0]=true := by
  apply certify_children
  intro i hi eligible
  interval_cases i
  · exact False.elim ((by decide : allowed tab30n 30 1 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_1
  · exact check30n_2
  · exact check30n_3
  · exact check30n_4
  · exact check30n_5
  · exact False.elim ((by decide : allowed tab30n 30 7 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_7
  · exact check30n_8
  · exact check30n_9
  · exact False.elim ((by decide : allowed tab30n 30 11 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_11
  · exact False.elim ((by decide : allowed tab30n 30 13 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_13
  · exact check30n_14
  · exact check30n_15
  · exact False.elim ((by decide : allowed tab30n 30 17 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_17
  · exact False.elim ((by decide : allowed tab30n 30 19 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_19
  · exact check30n_20
  · exact check30n_21
  · exact False.elim ((by decide : allowed tab30n 30 23 = false).symm.trans eligible |> Bool.noConfusion)
  · exact check30n_23
  · exact check30n_24
  · exact check30n_25
  · exact check30n_26
  · exact check30n_27
  · exact False.elim ((by decide : allowed tab30n 30 29 = false).symm.trans eligible |> Bool.noConfusion)
private theorem check_bal_30 (A : Finset (ZMod 30)) (zA : 0∈A) (vA : IsValidMod A)
    (bA : balanced (by decide) A) (size : #A=5) : False :=
  smallCase (by decide : 2∣30) (by decide) 3 tab30u tab30n rfl rfl check30u check30n A zA vA bA size
/-- With no antipodal pair, projection to the half modulus is injective. -/
def H1 : Prop := ∀ M : ℕ, 0<M → ∀ A : Finset (ZMod (2*M)),
    6≤#A → 0∈A → Set.InjOn (fun x => 2*x) (A : Set (ZMod (2*M))) →
    2≤#(A.filter fun a => a.val%2=0) → 2≤#(A.filter fun a => a.val%2=1) →
    IsValidMod A → 2^#A≤2*M

/-- For an even half modulus only the two endpoints of the diameter are even.
The other residues project injectively together with zero and still form a valid set there. -/
def H2 : Prop := ∀ M : ℕ, 0<M → 2∣M → ∀ A : Finset (ZMod (2*M)),
    6≤#A → 0∈A → (M : ZMod (2*M))∈A → #(A.filter fun a => a.val%2=0)=2 →
    IsValidMod ((A.erase (M : ZMod (2*M))).image (ZMod.castHom (dvd_mul_left M 2) (ZMod M))) →
    IsValidMod A → 2^#A≤2*M

/-- For an odd half modulus, work entirely in that smaller cyclic group. A
nonconstant binary labeling must separate at least one multiset using two
extra entries from the original sum if the group is too small. -/
def H3 : Prop := ∀ M : ℕ, M%2=1 → ∀ (C : Finset (ZMod M)) (b : ZMod M → ZMod 2),
    4≤#C → 0∉C → IsValidMod (insert 0 C) →
    (∃ x∈C,b x=0) → (∃ x∈C,b x=1) →
    (∀ x∈C,∀ y∈C,∀ z∈C,2*x+y=z → b y=b z) →
    (∀ m : ZMod M → ℕ, (∑ x∈C,m x)=#C+2 →
      (∑ x∈C,(m x : ZMod M)*x)=∑ x∈C,x →
      (∑ x∈C,(m x : ZMod 2)*b x)=∑ x∈C,b x) → 2^(#C+1)≤M

private theorem four {N : ℕ} (ev : 2∣N) (A : Finset (ZMod N)) (bal : balanced ev A) : 4≤#A := by
  classical
  have dj : Disjoint (fiber ev A 0) (fiber ev A 1) := Finset.disjoint_left.mpr (by
    intro x hx hy; have same := (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
    exact (by decide : (0:ZMod 2)≠1) same)
  have sub : fiber ev A 0 ∪ fiber ev A 1 ⊆ A := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have le := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dj] at le
  have e := bal 0; have o := bal 1; omega

private theorem low (M : ℕ) (hM : 0<M) (B : Finset (ZMod (2*M))) (zero : 0∈B)
    (valid : IsValidMod B) (bal : balanced (dvd_mul_right 2 M) B) (bound : #B≤5)
    (shape : Set.InjOn (fun x => 2*x) (B : Set (ZMod (2*M))) ∨ (M : ZMod (2*M))∈B) :
    2^#B≤2*M := by
  by_contra! fail
  have ge := four _ B bal
  have pack := (pack_even M hM B zero (by omega) valid shape).2 ge
  rcases (show #B=4 ∨ #B=5 by omega) with h|h
  · rw [h] at pack fail; norm_num at pack fail
    rcases (show M=6 ∨ M=7 by omega) with rfl|rfl
    · exact check_bal_12 B zero valid bal h
    · exact check_bal_14 B zero valid bal h
  · rw [h] at pack fail; norm_num at pack fail
    rcases (show M=11 ∨ M=12 ∨ M=13 ∨ M=14 ∨ M=15 by omega) with rfl|rfl|rfl|rfl|rfl
    · exact check_bal_22 B zero valid bal h
    · exact check_bal_24 B zero valid bal h
    · exact check_bal_26 B zero valid bal h
    · exact check_bal_28 B zero valid bal h
    · exact check_bal_30 B zero valid bal h

theorem main : H1 → H2 → H3 → OMA.R_Arxiv_2607_08366_min_modulus_R1.H2 := by
  intro sep same odd
  have key (N : ℕ) : ∀ (pos : 0<N) (ev : 2∣N) (A : Finset (ZMod N)),
      IsValidMod A → balanced ev A → 2^#A ≤ N := by
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro pos ev
      obtain ⟨M,rfl⟩ := ev
      intro A valid bal
      have hM : 0<M := by omega
      letI : NeZero (2*M) := ⟨by omega⟩
      have enough := four _ A bal
      obtain ⟨B,size,zB,vB,bB,shape⟩ := normalized M hM A (Finset.card_pos.mp (by omega)) valid bal
      rw [←size]
      by_cases small : #B≤5
      · exact low M hM B zB vB bB small shape
      have large : 6≤#B := by omega
      obtain ⟨evenC,oddC⟩ := (balanced_iff _ B).mp bB
      rcases shape with inj|pair
      · exact sep M hM B large zB inj evenC oddC vB
      by_cases em : 2∣M
      · obtain ⟨D,sc,ed,injection,vd⟩ := merge_pair M hM B zB pair vB
        by_cases big : 3 ≤ #(fiber (dvd_mul_right 2 M) B 0)
        · have bd := balance_merge M em hM B bB big injection
          rw [← ed] at bd
          have val := ih M (by omega) hM em D vd bd
          have card : #B=#D+1 := by omega
          rw [card,pow_succ]; omega
        · have eqs : fiber (dvd_mul_right 2 M) B 0 = B.filter (fun a => a.val%2=0) := by
            ext x; simp only [fiber,Finset.mem_filter]
            rw [←bit_val (dvd_mul_right 2 M) x,ZMod.val_eq_zero]
          rw [eqs] at big
          exact same M hM em B large zB pair (by omega) (ed ▸ vd) vB
      · have om : M%2=1 := by omega
        obtain ⟨C,b,s,zero,vc,e,o,labels⟩ := odd_projection M om B zB pair vB bB
        have bound := odd M om C b (by omega) zero vc e o (labels_edge C b labels) labels
        rw [← s,show #C+2=(#C+1)+1 by omega,pow_succ]
        omega
  intro n N hn ev A card valid even odd'
  letI : NeZero N := ⟨by omega⟩
  have div : 2∣N := Nat.dvd_of_mod_eq_zero ev
  rw [← card]
  exact key N hn div A valid ((balanced_iff div A).mpr ⟨even,odd'⟩)

end OMA.R_Arxiv_2607_08366_min_modulus_R1_H2_R1
