import OMAReductions.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1

-- Credit: @jenil-bodhani

section

/-! Mixed integer sums drawn from intervals with a bounded number of holes. -/
namespace Erdos13ColumnModulo
open Finset

lemma mixed_pair (A B : Finset ℕ) {L U t s : ℕ}
    (holesA : (Icc L U \ A).card ≤ t) (holesB : (Icc L U \ B).card ≤ t)
    (low : 2*(L+t) ≤ s) (high : s+2*t ≤ 2*U) :
    ∃ x ∈ A, ∃ y ∈ B, x+y=s := by
  classical
  let X := Icc L U \ A
  let Y := Icc L U \ B
  let J := Icc (s/2-t) (s/2+t)
  by_contra! hn
  have sub : J ⊆ X ∪ Y.image (fun y => s-y) := by
    intro x hx
    have h := mem_Icc.mp hx
    have xx : x ∈ Icc L U := mem_Icc.mpr ⟨by omega,by omega⟩
    have yy : s-x ∈ Icc L U := mem_Icc.mpr ⟨by omega,by omega⟩
    by_cases ax : x∈A
    · have bad : s-x ∉ B := fun byw => hn x ax (s-x) byw (by omega)
      exact mem_union_right _ (mem_image.mpr ⟨s-x,mem_sdiff.mpr ⟨yy,bad⟩,by omega⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨xx,ax⟩)
  have c := (card_le_card sub).trans (card_union_le _ _)
  have size : J.card=2*t+1 := by dsimp [J]; rw [Nat.card_Icc]; omega
  have im : (Y.image (fun y => s-y)).card ≤ Y.card := card_image_le
  change X.card≤t at holesA
  change Y.card≤t at holesB
  omega

lemma pick_height {t L U b : ℕ} {S : Finset ℕ} (h : (Icc L U \ S).card ≤ t)
    (low : L ≤ b) (high : b+t ≤ U) : ∃ x ∈ S, b≤x ∧ x≤b+t := by
  by_contra! no
  have inc : Icc b (b+t) ⊆ Icc L U \ S := by
    intro x hx
    obtain ⟨l,u⟩ := mem_Icc.mp hx
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,fun hx => by have := no x hx l; omega⟩
  have c := (card_le_card inc).trans h
  rw [Nat.card_Icc] at c
  omega

theorem mixed_heights {n L U t s : ℕ} (hn : 2≤n) (room : L+4*t ≤ U)
    (S : Fin n → Finset ℕ) (holes : ∀ i, (Icc L U \ S i).card ≤ t)
    (low : n*(L+t) ≤ s) (high : s ≤ n*(U-t)) :
    ∃ f : Fin n → ℕ, (∀ i, f i ∈ S i) ∧ ∑ i,f i=s := by
  let l := L+t
  let u := U-t
  have edge : u+t=U := by dsimp [u]; omega
  have order : l≤u := by dsimp [l,u]; omega
  have rep (j : ℕ) : ∀ (S : Fin (j+2) → Finset ℕ) (s : ℕ),
      (∀ i, (Icc L U \ S i).card ≤ t) → (j+2)*l≤ s → s≤(j+2)*u →
      ∃ f : Fin (j+2) → ℕ, (∀ i, f i ∈ S i) ∧ ∑ i, f i=s := by
    induction j with
    | zero =>
      intro S s h low high
      obtain ⟨x,hx,y,hy,he⟩ := mixed_pair (S 0) (S 1) (h 0) (h 1) low (by omega)
      exact ⟨![x,y],by simpa [Fin.forall_fin_two] using And.intro hx hy,by simpa [Fin.sum_univ_two] using he⟩
    | succ j ih =>
      intro S s h low high
      obtain ⟨lo,hlo,hLo,loL⟩ := pick_height (h 0) (b:=L) (by omega) (by omega)
      obtain ⟨hi,hhi,hiH,hHi⟩ := pick_height (h 0) (b:=u) (by dsimp [u];omega) (by omega)
      have hover : 2*l+hi ≤ 2*u+lo := by dsimp [l,u] at *; omega
      have overlap : (j+2)*l+hi ≤ (j+2)*u+lo := by
        simpa only [Nat.add_mul,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using
          Nat.add_le_add (Nat.mul_le_mul_left j order) hover
      have ext : ∃ c ∈ S 0, (j+2)*l+c≤ s ∧ s≤(j+2)*u+c := by
        have hl : (j+2)*l+l≤ s := by rwa [←Nat.succ_mul]
        have hu : s≤(j+2)*u+u := by rwa [←Nat.succ_mul]
        by_cases ls : s ≤ (j+2)*u+lo
        · exact ⟨lo,hlo,by dsimp [l] at *;omega,ls⟩
        · exact ⟨hi,hhi,by omega,by omega⟩
      obtain ⟨v,hv,vl,vu⟩ := ext
      obtain ⟨f,hf,hs⟩ := ih (fun i => S i.succ) (s-v) (fun i => h i.succ) (by omega) (by omega)
      exact ⟨Fin.cons v f,Fin.forall_fin_succ.mpr ⟨by simpa,by simpa using hf⟩,by
        simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hs];omega⟩
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hn
  have eq : n=j+2 := by omega
  clear hj
  subst n
  exact rep j S s holes low high

end Erdos13ColumnModulo

end

section

/-! An average bound for missing successors, and mixed sums starting
near the chosen populated heights of the different columns. -/
namespace Erdos13ColumnModulo
open Finset

lemma average_successors {r t p J : ℕ} (T : Finset ℕ) (S : Fin r → Finset ℕ)
    (room : 2*p+1 ≤ J) (small : t < p) (budget : r*t*t ≤ (p-t)*p)
    (target : (Icc 1 J \ T).card ≤ t) (holes : ∀ i, (Icc 1 J \ S i).card ≤ t) :
    ∃ h ∈ T, p<h ∧ h≤2*p ∧ t*(univ.filter (fun i => h+1 ∉ S i)).card ≤ p := by
  classical
  let I := Ioc p (2*p)
  let U := I.filter (fun h => h∈T)
  have loss : (I.filter (fun h => ¬h∈T)).card ≤ t := by
    refine (card_le_card ?_).trans target
    intro x hx
    obtain ⟨mem,no⟩ := mem_filter.mp hx
    obtain ⟨low,high⟩ := mem_Ioc.mp mem
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,no⟩
  have usize : p-t ≤ U.card := by
    have eq := I.card_filter_add_card_filter_not (fun h => h∈T)
    have size : I.card=p := by dsimp [I]; rw [Nat.card_Ioc]; omega
    change U.card+_=_ at eq
    omega
  have column (i : Fin r) : (U.filter (fun h => h+1∉S i)).card ≤ t := by
    refine (card_le_card_of_injOn (fun h : ℕ => h+1) ?_ (fun _ _ _ _ eq => Nat.add_right_cancel eq)).trans
      (holes i)
    intro h hh
    obtain ⟨mem,no⟩ := mem_filter.mp hh
    obtain ⟨inner,_⟩ := mem_filter.mp mem
    obtain ⟨low,high⟩ := mem_Ioc.mp inner
    change h+1 ∈ Icc 1 J \ S i
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,no⟩
  let b (h : ℕ) := (univ.filter (fun i => h+1∉S i)).card
  have total : ∑ h∈U, b h ≤ r*t := by
    calc
      (∑ h∈U, b h) = ∑ i, (U.filter (fun h => h+1∉S i)).card := by
        simp only [b,Finset.card_filter]
        exact Finset.sum_comm
      _ ≤ ∑ _ : Fin r,t := sum_le_sum (fun i _ => column i)
      _ = r*t := by simp
  by_contra! no
  have fail (h) (hh : h∈U) : p+1 ≤ t*b h := by
    obtain ⟨hI,mem⟩ := mem_filter.mp hh
    exact no h mem (mem_Ioc.mp hI).1 (mem_Ioc.mp hI).2
  have accum := sum_le_sum fail
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id,←Finset.mul_sum] at accum
  have cap := Nat.mul_le_mul_left t total
  have due := Nat.mul_le_mul_right p usize
  nlinarith only [accum,cap,budget,due,usize,Nat.sub_pos_of_lt small]

theorem mixed_from_lower_heights {n L U t s : ℕ} (hn : 2≤n) (room : L+6*t≤U)
    (S : Fin n → Finset ℕ) (holes : ∀ i, (Icc L U \ S i).card≤t)
    (b : Fin n → ℕ) (hb : ∀ i,b i∈S i ∧ L≤b i ∧ b i≤L+t)
    (low : (∑ i,b i)+2*t ≤ s) (high : s ≤ n*(U-t)) :
    ∃ f : Fin n → ℕ, (∀ i,f i∈S i) ∧ ∑ i,f i=s := by
  let u := U-t
  have edge : u+t=U := by dsimp [u];omega
  have rep (j : ℕ) : ∀ (S : Fin (j+2) → Finset ℕ) (b : Fin (j+2) → ℕ) (s : ℕ),
      (∀ i, (Icc L U \ S i).card≤t) → (∀ i,b i∈S i ∧ L≤b i ∧ b i≤L+t) →
      (∑ i,b i)+2*t ≤ s → s ≤ (j+2)*u →
      ∃ f : Fin (j+2) → ℕ, (∀ i,f i∈S i) ∧ ∑ i,f i=s := by
    induction j with
    | zero =>
      intro S b s h hb lo hi
      have l0 := (hb 0).2.1
      have l1 := (hb 1).2.1
      rw [Fin.sum_univ_two] at lo
      obtain ⟨x,hx,y,hy,he⟩ := mixed_pair (s:=s) (S 0) (S 1) (h 0) (h 1) (by omega) (by omega)
      exact ⟨![x,y],by simpa [Fin.forall_fin_two] using And.intro hx hy,
        by simpa [Fin.sum_univ_two] using he⟩
    | succ j ih =>
      intro S b s h hb low high
      let B := ∑ i : Fin (j+2),b i.succ
      have inc := sum_le_sum (s:=univ) (fun (i : Fin (j+2)) _ => (hb i.succ).2.2)
      simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at inc
      change B ≤ (j+2)*(L+t) at inc
      obtain ⟨hi,hhi,uhi,hiU⟩ := pick_height (h 0) (b:=u) (by dsimp [u];omega) (by omega)
      have lc := (hb 0).2.1
      have overlap : B+2*t+hi ≤ (j+2)*u+b 0 := by
        have mul := Nat.mul_le_mul_left j (show L+t≤u by dsimp [u];omega)
        rw [Nat.add_mul] at inc ⊢
        dsimp [u] at *
        omega
      have base : B+b 0+2*t≤ s := by
        rw [Fin.sum_univ_succ] at low
        change b 0+B+2*t≤ s at low
        omega
      have upper : s≤(j+2)*u+u := by rwa [←Nat.succ_mul]
      have ext : ∃ v∈S 0, B+2*t+v≤ s ∧ s≤(j+2)*u+v := by
        by_cases within : s ≤ (j+2)*u+b 0
        · exact ⟨b 0,(hb 0).1,by omega,within⟩
        · exact ⟨hi,hhi,by omega,by omega⟩
      obtain ⟨v,hv,lv,uv⟩ := ext
      obtain ⟨f,hf,hs⟩ := ih (fun i=>S i.succ) (fun i=>b i.succ) (s-v) (fun i=>h i.succ)
        (fun i=>hb i.succ) (by change B+2*t≤ s-v;omega) (by omega)
      exact ⟨Fin.cons v f,Fin.forall_fin_succ.mpr ⟨by simpa,by simpa using hf⟩,by
        simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hs];omega⟩
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hn
  have eq : n=j+2 := by omega
  clear hj
  subst n
  exact rep j S b s holes hb low high

end Erdos13ColumnModulo

end

section

/-!
# Fully occupied residue classes across several layers

If all J lifts of each offset occur in A, then a forbidden relation with
multiplier at most Jr among those offsets lifts to a forbidden relation in A.
The count at the end records the cost of a missing lift in each remaining class.
-/

namespace FullColumns

open Finset

def Free (r : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) → ¬ a ∣ ∑ i, b i

lemma allocate (n c k : ℕ) (bound : k ≤ n * c) :
    ∃ t : Fin n → ℕ, (∀ i, t i ≤ c) ∧ ∑ i, t i = k := by
  induction n generalizing k with
  | zero =>
    have : k = 0 := by simpa using bound
    exact ⟨fun _ => 0, fun i => i.elim0, by simp [this]⟩
  | succ n ih =>
    obtain ⟨f, hf, hsum⟩ := ih (k - min k c) (by rw [Nat.succ_mul] at bound; omega)
    refine ⟨Fin.cons (min k c) f, Fin.forall_fin_succ.mpr ⟨by simp, by simpa using hf⟩, ?_⟩
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hsum]
    omega

lemma lift_forbidden {A P : Finset ℕ} {a J r : ℕ} (hJ : 0 < J)
    (allLifts : ∀ u ∈ P, ∀ i ∈ Icc 1 J, i * a + u ∈ A) (free : Free r A)
    {u k : ℕ} (hu : u ∈ P) (b : Fin r → ℕ) (hb : ∀ i, b i ∈ P)
    (hlt : ∀ i, u < b i) (lower : r ≤ k) (upper : k ≤ r * J) :
    ∑ i, b i ≠ k * u := by
  intro hsum
  have cap : k - r ≤ r * (J - 1) := by
    rw [Nat.mul_sub, Nat.mul_one]
    omega
  obtain ⟨t, ht, heq⟩ := allocate r (J - 1) (k - r) cap
  let b' (i : Fin r) := (t i + 1) * a + b i
  have hu' : a + u ∈ A := by simpa using allLifts u hu 1 (mem_Icc.mpr ⟨le_rfl, hJ⟩)
  apply free (a + u) hu' b'
  · intro i
    exact allLifts _ (hb i) _ (mem_Icc.mpr ⟨by omega, by have := ht i; omega⟩)
  · intro i
    dsimp [b']
    rw [Nat.succ_mul]
    have := hlt i
    omega
  · refine ⟨k, ?_⟩
    simp only [b', Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one, heq, hsum]
    rw [Nat.sub_add_cancel lower]
    ring

lemma free_shell {A P : Finset ℕ} {a J r : ℕ} (hJ : 0 < J)
    (allLifts : ∀ u ∈ P, ∀ i ∈ Icc 1 J, i * a + u ∈ A)
    (free : Free r A) (X : ℕ) : Free r (P.filter fun x => x ≤ X ∧ X < J*x) := by
  intro u hu b hb hlt hdiv
  obtain ⟨huP, huX, hJu⟩ := mem_filter.mp hu
  have hpos : 0 < u := by by_contra! hn; simp [show u = 0 by omega] at hJu
  obtain ⟨k, hk⟩ := hdiv
  have hlow : r*u ≤ ∑ i, b i := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := fun _ => u) (g := b) (fun i _ => (hlt i).le)
  have hhigh : ∑ i, b i ≤ r*(J*u) := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := b) (g := fun _ => J*u) (fun i _ => (mem_filter.mp (hb i)).2.1.trans hJu.le)
  rw [hk, mul_comm u k] at hlow hhigh
  exact lift_forbidden hJ allLifts free huP b (fun i => (mem_filter.mp (hb i)).1) hlt
    (Nat.le_of_mul_le_mul_right hlow hpos) (Nat.le_of_mul_le_mul_right (by
      rwa [Nat.mul_assoc] : k*u ≤ r*J*u) hpos) (by simpa [Nat.mul_comm] using hk)

/-- Integer rounding lets the permitted shell extend below X/J. -/
lemma free_wide_shell {A P : Finset ℕ} {a J r : ℕ} (hJ : 0 < J)
    (allLifts : ∀ u ∈ P, ∀ i ∈ Icc 1 J, i * a + u ∈ A)
    (free : Free r A) (X : ℕ) :
    Free r (P.filter fun x => x ≤ X ∧ r * X < (r * J + 1) * x) := by
  intro u hu b hb hlt hdiv
  obtain ⟨huP, huX, hJu⟩ := mem_filter.mp hu
  have hpos : 0 < u := by by_contra! hn; simp [show u = 0 by omega] at hJu
  obtain ⟨k, hk⟩ := hdiv
  have hlow : r * u ≤ ∑ i, b i := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := fun _ => u) (g := b) (fun i _ => (hlt i).le)
  have hhigh : ∑ i, b i ≤ r * X := by
    simpa using Finset.sum_le_sum (s := (univ : Finset (Fin r)))
      (f := b) (g := fun _ => X) (fun i _ => (mem_filter.mp (hb i)).2.1)
  rw [hk, mul_comm u k] at hlow hhigh
  have upper : k ≤ r * J := by
    by_contra! big
    have := Nat.mul_le_mul_right u (show r * J + 1 ≤ k by omega)
    omega
  exact lift_forbidden hJ allLifts free huP b (fun i => (mem_filter.mp (hb i)).1) hlt
    (Nat.le_of_mul_le_mul_right hlow hpos) upper (by simpa [Nat.mul_comm] using hk)

def complete (B : Finset ℕ) (a J : ℕ) : Finset ℕ :=
  (B.image (· % a)).filter fun u => ∀ k ∈ Icc 1 J, k * a + u ∈ B

lemma card_bound {B : Finset ℕ} {a J : ℕ} (hj : 0 < J)
    (layers : ∀ b ∈ B, b / a ∈ Icc 1 J) :
    B.card ≤ (J-1) * (B.image (· % a)).card + (complete B a J).card := by
  classical
  let R := B.image (· % a)
  let S (u : ℕ) := (Icc 1 J).filter fun i => i*a+u ∈ B
  have hi (u : ℕ) : (B.filter (fun b => b%a=u)).card ≤ (S u).card := by
    apply card_le_card_of_injOn (fun b => b/a)
    · intro x hx
      obtain ⟨hxB, hmod⟩ := mem_filter.mp hx
      apply mem_filter.mpr
      exact ⟨layers x hxB, by simpa [← hmod, Nat.div_add_mod'] using hxB⟩
    · intro x hx y hy he
      have hx' := (mem_filter.mp hx).2
      have hy' := (mem_filter.mp hy).2
      change x/a=y/a at he
      have ex := Nat.div_add_mod x a
      have ey := Nat.div_add_mod y a
      rw [he, hx'] at ex
      rw [hy'] at ey
      omega
  have each (u) (hu : u ∈ R) :
      (B.filter (fun b => b%a=u)).card ≤ (J-1) + (if u ∈ complete B a J then 1 else 0) := by
    have sub : S u ⊆ Icc 1 J := filter_subset _ _
    have sizeI : (Icc 1 J).card = J := by simp
    have hsize := card_le_card sub
    have hfiber := hi u
    split_ifs with full
    · omega
    · have hne : S u ≠ Icc 1 J := by
        intro hEq
        apply full
        apply mem_filter.mpr
        refine ⟨hu, fun k hk => ?_⟩
        rw [← hEq] at hk
        exact (mem_filter.mp hk).2
      have := card_lt_card (ssubset_of_subset_of_ne sub hne)
      omega
  have sum := Finset.sum_le_sum each
  rw [← card_eq_sum_card_image] at sum
  have hsub : complete B a J ⊆ R := filter_subset _ _
  simpa [sum_add_distrib, Nat.mul_comm, inter_eq_right.mpr hsub] using sum

end FullColumns

end

section

/-! Near-complete columns exclude a range of scalar multiples of each offset. -/
namespace Erdos13ColumnModulo
open Finset FullColumns

def columnHeights (A : Finset ℕ) (a J u : ℕ) := (Icc 1 J).filter fun h => h*a+u ∈ A

theorem near_dilate_height {r t a k H : ℕ} (hr : 3≤r) (ha : 0<a) (kr : r≤k)
    (hH : 1≤H) (space : H+1+4*t ≤ r)
    (low : r*(t+2) ≤ (k-r)*H) (high : k*(H+t+1) ≤ r*r)
    (A P : Finset ℕ) (free : Free r A) (off : ∀ u ∈ P, 0<u ∧ u<a)
    (holes : ∀ u ∈ P, (Icc 1 (r+t) \ columnHeights A a (r+t) u).card ≤ t)
    (u : ℕ) (hu : u ∈ P) (v : Fin r → ℕ) (hv : ∀ i,v i∈P) :
    ¬ (∑ i,v i) ≡ k*u [MOD a] := by
  classical
  intro eqmod
  obtain ⟨c,hc⟩ := Nat.modEq_iff_dvd.mp eqmod
  push_cast at hc
  have sums := sum_le_sum (s:=univ) (f:=v) (g:=fun _ => a-1) (fun i _ => by
    have := (off _ (hv i)).2; omega)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at sums
  have capN : (∑ i,v i) < r*a := by
    have eq := congrArg (fun z : ℕ => r*z) (Nat.sub_add_cancel (show 1≤a by omega))
    nlinarith only [sums,eq,hr]
  have lower : -(r:ℤ) < c := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg a)
    zify at capN
    nlinarith only [hc,hh,capN,mul_nonneg (Int.natCast_nonneg k) (Int.natCast_nonneg u)]
  have upper : c < (k:ℤ) := by
    by_contra! h
    have h := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg a)
    have cap := Nat.mul_lt_mul_of_pos_left (off u hu).2 (show 0<k by omega)
    zify at cap
    have nn : (0:ℤ) ≤ ∑ i,(v i:ℤ) := sum_nonneg (fun i _ => Int.natCast_nonneg _)
    nlinarith only [cap,h,hc,nn]
  obtain ⟨h,hh,hl,hupp⟩ := pick_height (holes u hu) hH (show H+t≤r+t by omega)
  have room : h+1+4*t ≤ r+t := by omega
  have gain := Nat.mul_le_mul_left (k-r) hl
  have dec := congrArg (fun z : ℕ => z*h) (Nat.sub_add_cancel kr)
  have inLo : (r*(h+1+t):ℕ) ≤ ((k*h:ℕ):ℤ)+c := by
    zify at gain dec low ⊢
    nlinarith only [lower,gain,dec,low]
  have inHi : ((k*h:ℕ):ℤ)+c ≤ (r*r:ℕ) := by
    have hi := Nat.mul_le_mul_left k (show h+1≤H+t+1 by omega)
    zify at hi high ⊢
    nlinarith only [hi,high,upper]
  let X := (((k*h:ℕ):ℤ)+c).toNat
  have isX : (X:ℤ)=((k*h:ℕ):ℤ)+c :=
    Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg _) inLo)
  let S (i : Fin r) := (Icc (h+1) (r+t)).filter (fun j => j*a+v i ∈ A)
  have missing (i) : (Icc (h+1) (r+t) \ S i).card ≤ t := by
    refine (card_le_card ?_).trans (holes (v i) (hv i))
    intro z hz
    obtain ⟨hI,no⟩ := mem_sdiff.mp hz
    obtain ⟨l,vv⟩ := mem_Icc.mp hI
    refine mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,vv⟩,?_⟩
    intro mem
    exact no (mem_filter.mpr ⟨hI,(mem_filter.mp mem).2⟩)
  obtain ⟨f,hf,hs⟩ := mixed_heights (s:=X) (by omega : 2≤r) room S missing (by omega)
    (by rw [Nat.add_sub_cancel]; omega)
  apply free (h*a+u) (mem_filter.mp hh).2 (fun i => f i*a+v i)
  · intro i
    exact (mem_filter.mp (hf i)).2
  · intro i
    have fh := (mem_Icc.mp (mem_filter.mp (hf i)).1).1
    have mul := Nat.mul_le_mul_right a fh
    rw [Nat.add_mul,Nat.one_mul] at mul
    have := (off u hu).2
    omega
  · refine ⟨k,?_⟩
    rw [sum_add_distrib,←sum_mul,hs]
    zify at isX hc ⊢
    push_cast at *
    nlinarith only [isX,hc]

theorem near_multipliers {r t a : ℕ} (hr : 12*(t+2)≤r) (ha : 0<a)
    (A P : Finset ℕ) (free : Free r A) (off : ∀ u ∈ P, 0<u ∧ u<a)
    (holes : ∀ u ∈ P, (Icc 1 (r+t) \ columnHeights A a (r+t) u).card ≤ t)
    {k : ℕ} (allowed : k=r+2*t+6 ∨ (2*r≤k ∧ k*(2*t+3)≤r*r))
    (u : ℕ) (hu : u∈P) (v : Fin r → ℕ) (hv : ∀ i,v i∈P) :
    ¬ (∑ i,v i) ≡ k*u [MOD a] := by
  rcases allowed with eq|⟨lo,hi⟩
  · subst k
    let H := r/2
    have hH : 1≤H := by dsimp [H]; omega
    have bigH : r≤2*H+1 := by dsimp [H];omega
    have smH : 2*H≤r := by dsimp [H]; omega
    apply near_dilate_height (H:=H) (by omega) ha (by omega) hH (by omega) ?_ ?_ A P free off holes u hu v hv
    · rw [show r+2*t+6-r=2*t+6 by omega]
      have c := Nat.mul_le_mul_right (t+2) bigH
      nlinarith only [c,hr,bigH,Nat.zero_le t]
    · have c₁ : 2*(r+2*t+6) ≤ 3*r := by omega
      have c₂ : 3*(H+t+1) ≤ 2*r := by omega
      have c := Nat.mul_le_mul c₁ c₂
      nlinarith only [c]
  · apply near_dilate_height (H:=t+2) (by omega) ha (by omega) (by omega) (by omega) ?_ ?_ A P free off holes u hu v hv
    · exact Nat.mul_le_mul_right (t+2) (by omega)
    · simpa only [show t+2+t+1=2*t+3 by omega] using hi

end Erdos13ColumnModulo

end

section

/-! Scalar exclusions for high-occupancy rows on arbitrarily many layers. -/
namespace Erdos13ColumnModulo
open Finset FullColumns

/-- On a positive fraction of heights the cost of missing successors across
all r numerator columns is quadratic in the number of holes per column. -/
theorem histogram_dilate {r J t a k : ℕ} (hr : 128≤r) (span : r≤J) (ha : 0<a)
    (klo : r+40≤k) (khi : 8*(t+1)*k≤r*J)
    (sparse : 8*t+8≤J/8) (budget : r*t*t ≤ (J/8-t)*(J/8))
    (A P : Finset ℕ) (free : Free r A) (off : ∀ u∈P, 0<u ∧ u<a)
    (holes : ∀ u∈P, (Icc 1 J \ columnHeights A a J u).card ≤ t)
    (u : ℕ) (hu : u∈P) (v : Fin r → ℕ) (hv : ∀ i,v i∈P) :
    ¬ (∑ i,v i) ≡ k*u [MOD a] := by
  classical
  have kr : r≤k := by omega
  intro eqmod
  obtain ⟨c,hc⟩ := Nat.modEq_iff_dvd.mp eqmod
  push_cast at hc
  have sums := sum_le_sum (s:=univ) (f:=v) (g:=fun _ => a-1) (fun i _ => by
    have := (off _ (hv i)).2; omega)
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at sums
  have capN : (∑ i,v i) < r*a := by
    have eq := congrArg (fun z : ℕ => r*z) (Nat.sub_add_cancel (show 1≤a by omega))
    nlinarith only [sums,eq,hr]
  have lower : -(r:ℤ) < c := by
    by_contra! h
    have hh := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg a)
    zify at capN
    nlinarith only [hc,hh,capN,mul_nonneg (Int.natCast_nonneg k) (Int.natCast_nonneg u)]
  have upper : c < (k:ℤ) := by
    by_contra! h
    have h := mul_le_mul_of_nonneg_left h (Int.natCast_nonneg a)
    have cap := Nat.mul_lt_mul_of_pos_left (off u hu).2 (show 0<k by omega)
    zify at cap
    have nn : (0:ℤ) ≤ ∑ i,(v i:ℤ) := sum_nonneg (fun i _ => Int.natCast_nonneg _)
    nlinarith only [cap,h,hc,nn]
  let V (i : Fin r) := columnHeights A a J (v i)
  let b (h : ℕ) := (univ.filter (fun i => h+1∉V i)).card
  let p := J/8
  have width : 8*p≤J ∧ J<8*p+8 := by dsimp [p];omega
  change 8*t+8≤p at sparse
  have haveH : ∃ h∈columnHeights A a J u,
      h+1+6*t≤J ∧ r*(h+1)+t*b h+2*t+r ≤ k*h ∧ k*(h+1)≤r*(J-t) := by
    by_cases smallK : k≤2*r
    · obtain ⟨h,hh,low,high,cheap⟩ := average_successors (p:=p) _ V (by omega : 2*p+1≤J)
        (by omega) budget (holes u hu) (fun i => holes _ (hv i))
      change t*b h ≤ p at cheap
      have mult := Nat.mul_le_mul_right h klo
      have highk := Nat.mul_le_mul_right (h+1) smallK
      have highr := Nat.mul_le_mul_left r (show 2*(h+1)≤J-t by omega)
      exact ⟨h,hh,by omega,by nlinarith only [mult,cheap,hr,span,width.2,sparse,low],
        by nlinarith only [highk,highr]⟩
    · obtain ⟨h,hh,low,high⟩ := pick_height (holes u hu) (b:=2*t+3) (by omega) (by omega)
      have bc : b h ≤ r := by
        simpa [b] using (card_filter_le (s:=(univ : Finset (Fin r))) (fun i=>h+1∉V i))
      have cb := Nat.mul_le_mul_left t bc
      have mult := Nat.mul_le_mul_right h (show 2*r≤k by omega)
      have step := Nat.mul_le_mul_left r low
      have tx := Nat.mul_le_mul_right t (show 2≤r by omega)
      have highk := Nat.mul_le_mul_left k (show 2*(h+1)≤8*(t+1) by omega)
      have highr := Nat.mul_le_mul_left r (show J≤2*(J-t) by omega)
      exact ⟨h,hh,by omega,by nlinarith only [cb,mult,step,tx,hr],by nlinarith only [khi,highk,highr]⟩
  obtain ⟨h,hh,room,lo,hi⟩ := haveH
  let S (i : Fin r) := (Icc (h+1) J).filter (fun j=>j∈V i)
  have mis (i) : (Icc (h+1) J \ S i).card ≤ t := by
    refine (card_le_card ?_).trans (holes _ (hv i))
    intro z hz
    obtain ⟨hI,no⟩ := mem_sdiff.mp hz
    obtain ⟨l,vv⟩ := mem_Icc.mp hI
    exact mem_sdiff.mpr ⟨mem_Icc.mpr ⟨by omega,vv⟩,fun ve => no (mem_filter.mpr ⟨hI,ve⟩)⟩
  have chooseLo (i : Fin r) : ∃ z∈S i, h+1≤z ∧ z≤h+1+(if h+1∉V i then t else 0) := by
    by_cases hit : h+1∈V i
    · exact ⟨h+1,mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl,by omega⟩,hit⟩,le_rfl,by simp [hit]⟩
    · obtain ⟨z,hz,zlo,zhi⟩ := pick_height (holes _ (hv i)) (b:=h+1) (by omega) (by omega)
      exact ⟨z,mem_filter.mpr ⟨mem_Icc.mpr ⟨zlo,by omega⟩,hz⟩,zlo,by simpa [hit] using zhi⟩
  choose z zmem zlo zhi using chooseLo
  have ez : (∑ i,z i) ≤ r*(h+1)+t*b h := by
    have est := sum_le_sum (s:=univ) (fun i _=>zhi i)
    simpa [b,sum_add_distrib,sum_ite,Nat.mul_comm] using est
  have lowX : (((∑ i,z i)+2*t:ℕ):ℤ) ≤ ((k*h:ℕ):ℤ)+c := by
    zify at lo ez ⊢
    linarith only [lo,ez,lower]
  have hiX : ((k*h:ℕ):ℤ)+c ≤ (r*(J-t):ℕ) := by
    zify at hi ⊢
    nlinarith only [hi,upper]
  let X := (((k*h:ℕ):ℤ)+c).toNat
  have isX : (X:ℤ)=((k*h:ℕ):ℤ)+c := Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg _) lowX)
  obtain ⟨f,hf,hs⟩ := mixed_from_lower_heights (s:=X) (by omega : 2≤r) room S mis z
    (fun i => ⟨zmem i,zlo i,by have hv := zhi i; split at hv <;> omega⟩) (by omega) (by omega)
  apply free (h*a+u) (mem_filter.mp hh).2 (fun i => f i*a+v i)
  · intro i
    exact (mem_filter.mp (mem_filter.mp (hf i)).2).2
  · intro i
    have fh := (mem_Icc.mp (mem_filter.mp (hf i)).1).1
    have mul := Nat.mul_le_mul_right a fh
    rw [Nat.add_mul,Nat.one_mul] at mul
    have := (off u hu).2
    omega
  · refine ⟨k,?_⟩
    rw [sum_add_distrib,←sum_mul,hs]
    zify at isX hc ⊢
    push_cast at *
    nlinarith only [isX,hc]

end Erdos13ColumnModulo

end

section

/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Adapted from gdahia/ExtendingPollardForTRepresentableSums, commit 516693eeee.
Licensed under the Apache License, Version 2.0, available at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: Mantas Bakšys, Yaël Dillies
-/

/-!
# Stabilizer of a finset

This file defines the stabilizer of a finset of a group as a finset.

## Main declarations

* `Finset.mulStab`: The stabilizer of a **nonempty** finset as a finset.
-/

open Function MulAction
open scoped Pointwise

namespace Finset
variable {ι α : Type*}

section Group
variable [Group α] [DecidableEq α] {s t : Finset α} {a : α}

instance (s : Finset α) : DecidablePred (· ∈ stabilizer α (s : Set α)) :=
  fun a ↦ decidable_of_iff (a ∈ stabilizer α s) (by simp)

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`. -/

def mulStab (s : Finset α) : Finset α := {a ∈ s / s | a • s = s}

@[simp]
lemma mem_mulStab (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s = s := by
  rw [mulStab, mem_filter, mem_div, and_iff_right_of_imp]
  obtain ⟨b, hb⟩ := hs
  exact fun h ↦ ⟨_, by rw [← h]; exact smul_mem_smul_finset hb, _, hb, mul_div_cancel_right _ _⟩

lemma mulStab_subset_div : s.mulStab ⊆ s / s := filter_subset _ _

lemma mulStab_subset_div_right (ha : a ∈ s) : s.mulStab ⊆ s / {a} := by
  refine fun b hb ↦ mem_div.2 ⟨_, ?_, _, mem_singleton_self _, mul_div_cancel_right _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rw [← hb]
  exact smul_mem_smul_finset ha

@[simp]
lemma coe_mulStab (hs : s.Nonempty) : (s.mulStab : Set α) = stabilizer α (s : Set α) := by
  ext; simp [mem_mulStab hs]

lemma mem_mulStab_iff_subset_smul_finset (hs : s.Nonempty) : a ∈ s.mulStab ↔ s ⊆ a • s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_subset_smul_finset]

lemma mem_mulStab_iff_smul_finset_subset (hs : s.Nonempty) : a ∈ s.mulStab ↔ a • s ⊆ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset,
    mem_stabilizer_finset_iff_smul_finset_subset]

lemma mem_mulStab' (hs : s.Nonempty) : a ∈ s.mulStab ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ s := by
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe, stabilizer_coe_finset, mem_stabilizer_finset']

@[simp]
lemma mulStab_empty : mulStab (∅ : Finset α) = ∅ := by simp [mulStab]

@[simp]
lemma mulStab_singleton (a : α) : mulStab ({a} : Finset α) = 1 := by
  simp [mulStab, singleton_one, filter_true_of_mem]

lemma Nonempty.of_mulStab : s.mulStab.Nonempty → s.Nonempty := by
  simp_rw [nonempty_iff_ne_empty, not_imp_not]; rintro rfl; exact mulStab_empty

@[simp]
lemma one_mem_mulStab : (1 : α) ∈ s.mulStab ↔ s.Nonempty :=
  ⟨fun h ↦ Nonempty.of_mulStab ⟨_, h⟩, fun h ↦ (mem_mulStab h).2 <| one_smul _ _⟩

lemma Nonempty.mulStab (h : s.Nonempty) : s.mulStab.Nonempty := ⟨_, (one_mem_mulStab.mpr h)⟩

@[simp]
lemma mulStab_nonempty : s.mulStab.Nonempty ↔ s.Nonempty := ⟨Nonempty.of_mulStab, Nonempty.mulStab⟩

@[simp]
lemma card_mulStab_eq_one : #s.mulStab = 1 ↔ s.mulStab = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, card_one]⟩
  obtain ⟨a, ha⟩ := card_eq_one.1 h
  rw [ha]
  rw [eq_singleton_iff_nonempty_unique_mem, mulStab_nonempty, ← one_mem_mulStab] at ha
  rw [← ha.2 _ ha.1, singleton_one]

lemma Nonempty.mulStab_nontrivial (h : s.Nonempty) : s.mulStab.Nontrivial ↔ s.mulStab ≠ 1 :=
  nontrivial_iff_ne_singleton (one_mem_mulStab.mpr h)

lemma subset_mulStab_mul_left (ht : t.Nonempty) : s.mulStab ⊆ (s * t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  simp_rw [subset_iff, mem_mulStab hs, mem_mulStab (hs.mul ht)]
  rintro a h
  rw [← smul_mul_assoc, h]

@[simp]
lemma mulStab_mul (s : Finset α) : s.mulStab * s = s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact mul_empty _
  · simp only [← coe_inj, hs, coe_mul, coe_mulStab, stabilizer_mul_self]

lemma mul_subset_right_iff (ht : t.Nonempty) : s * t ⊆ t ↔ s ⊆ t.mulStab := by
  simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_subset,
    ← mem_mulStab_iff_smul_finset_subset ht, subset_iff]

lemma mul_subset_right : s ⊆ t.mulStab → s * t ⊆ t := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  · exact (mul_subset_right_iff ht).2

lemma smul_mulStab (ha : a ∈ s.mulStab) : a • s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← mem_coe, coe_mulStab hs, SetLike.mem_coe] at ha
  rw [← coe_inj, coe_smul_finset, coe_mulStab hs, smul_coe_set ha]

@[simp]
lemma mulStab_mul_mulStab (s : Finset α) : s.mulStab * s.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · simp_rw [← smul_eq_mul, ← biUnion_smul_finset, biUnion_congr rfl fun _ ↦ smul_mulStab,
      ← sup_eq_biUnion, sup_const hs.mulStab]

lemma inter_mulStab_subset_mulStab_union : s.mulStab ∩ t.mulStab ⊆ (s ∪ t).mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  intro x hx
  rw [mem_mulStab (hs.mono subset_union_left), smul_finset_union,
    (mem_mulStab hs).mp (mem_of_mem_inter_left hx),
    (mem_mulStab ht).mp (mem_of_mem_inter_right hx)]

end Group

variable [CommGroup α] [DecidableEq α] {s t : Finset α} {a : α}

lemma mulStab_subset_div_left (ha : a ∈ s) : s.mulStab ⊆ {a} / s := by
  refine fun b hb ↦ mem_div.2 ⟨_, mem_singleton_self _, _, ?_, div_div_cancel _ _⟩
  rw [mem_mulStab ⟨a, ha⟩] at hb
  rwa [← hb, ← inv_smul_mem_iff, smul_eq_mul, inv_mul_eq_div] at ha

lemma subset_mulStab_mul_right (hs : s.Nonempty) : t.mulStab ⊆ (s * t).mulStab := by
  rw [mul_comm]; exact subset_mulStab_mul_left hs

@[simp]
lemma mul_mulStab (s : Finset α) : s * s.mulStab = s := by rw [mul_comm]; exact mulStab_mul _

@[simp]
lemma mul_mulStab_mul_mul_mul_mulStab_mul :
    s * (s * t).mulStab * (t * (s * t).mulStab) = s * t := by
  rw [mul_mul_mul_comm, mulStab_mul_mulStab, mul_mulStab]

lemma smul_finset_mulStab_subset (ha : a ∈ s) : a • s.mulStab ⊆ s :=
  (smul_finset_subset_smul ha).trans s.mul_mulStab.subset

lemma mul_subset_left_iff (hs : s.Nonempty) : s * t ⊆ s ↔ t ⊆ s.mulStab := by
  rw [mul_comm, mul_subset_right_iff hs]

lemma mul_subset_left : t ⊆ s.mulStab → s * t ⊆ s := by rw [mul_comm]; exact mul_subset_right

@[simp]
lemma mulStab_idem (s : Finset α) : s.mulStab.mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.mulStab, coe_mulStab hs]
  simp

@[simp]
lemma mulStab_smul (a : α) (s : Finset α) : (a • s).mulStab = s.mulStab := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [← coe_inj, coe_mulStab hs, coe_mulStab hs.smul_finset, stabilizer_coe_finset,
    stabilizer_coe_finset, stabilizer_smul_eq_right]

lemma mulStab_image_coe_quotient (hs : s.Nonempty) :
    (s.image (↑) : Finset (α ⧸ stabilizer α (s : Set α))).mulStab = 1 := by
  simp_rw [← coe_inj, coe_mulStab (hs.image _), coe_image, coe_one]
  rw [stabilizer_image_coe_quotient, Subgroup.coe_bot, Set.singleton_one]

lemma preimage_image_quotientMk_stabilizer_eq_mul_mulStab (ht : t.Nonempty) (s : Finset α) :
    QuotientGroup.mk ⁻¹' (Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s) = s * t.mulStab := by
  rw [QuotientGroup.preimage_image_mk_eq_mul, coe_mulStab ht, stabilizer_coe_finset]

lemma preimage_image_quotientMk_mulStabilizer (s : Finset α) :
    QuotientGroup.mk ⁻¹' (Set.image ((↑) : α → α ⧸ stabilizer α (s : Set α)) s) = s := by
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  · rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab hs s, ← coe_mul, mul_mulStab]

lemma pairwiseDisjoint_smul_finset_mulStab (s : Finset α) :
    (Set.range fun a : α ↦ a • s.mulStab).PairwiseDisjoint id := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  simp only [onFun, id_eq]
  simp_rw [← disjoint_coe, ← coe_injective.ne_iff, coe_smul_finset, coe_mulStab hs]
  exact fun h ↦ isBlock_subgroup h

lemma disjoint_smul_finset_mulStab_mul_mulStab :
    ¬a • s.mulStab ⊆ t * s.mulStab → Disjoint (a • s.mulStab) (t * s.mulStab) := by
  simp_rw [@not_imp_comm (_ ≤ _), ← smul_eq_mul, ← biUnion_smul_finset, disjoint_biUnion_right,
    Classical.not_forall]
  rintro ⟨b, hb, h⟩
  rw [s.pairwiseDisjoint_smul_finset_mulStab.eq (Set.mem_range_self _) (Set.mem_range_self _) h]
  exact subset_biUnion_of_mem (· • mulStab s) hb

lemma card_mulStab_dvd_card_mul_mulStab (s t : Finset α) : #t.mulStab ∣ #(s * t.mulStab) :=
  card_dvd_card_smul_right <|
    t.pairwiseDisjoint_smul_finset_mulStab.subset <| Set.image_subset_range _ _

lemma card_mulStab_dvd_card (s : Finset α) : #s.mulStab ∣ #s := by
  simpa only [mul_mulStab] using s.card_mulStab_dvd_card_mul_mulStab s

lemma card_mulStab_le_card : #s.mulStab ≤ #s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rfl
  · exact Nat.le_of_dvd hs.card_pos s.card_mulStab_dvd_card

/-- A fintype instance for the stabilizer of a nonempty finset `s` in terms of `s.mulStab`. -/

abbrev fintypeStabilizerOfMulStab (hs : s.Nonempty) : Fintype (stabilizer α s) where
  elems := s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩
  complete a := mem_map.2
    ⟨⟨_, (mem_mulStab hs).2 a.2⟩, mem_attach _ ⟨_, (mem_mulStab hs).2 a.2⟩, Subtype.ext rfl⟩

lemma card_mulStab_dvd_card_mulStab (hs : s.Nonempty) (h : s.mulStab ⊆ t.mulStab) :
    #s.mulStab ∣ #t.mulStab := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  rw [← coe_subset, coe_mulStab hs, coe_mulStab ht, SetLike.coe_subset_coe] at h
  let : Fintype (stabilizer α s) := fintypeStabilizerOfMulStab hs
  let : Fintype (stabilizer α t) := fintypeStabilizerOfMulStab ht
  convert Subgroup.card_dvd_of_le h using 1
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(s.mulStab.attach.map
    ⟨Subtype.map id fun _ ↦ (mem_mulStab hs).1, Subtype.map_injective _ injective_id⟩)
    simp
  · simp only [stabilizer_coe_finset, Nat.card_eq_fintype_card]
    change _ = #(t.mulStab.attach.map
      ⟨Subtype.map id fun _ ↦ (mem_mulStab ht).1, Subtype.map_injective _ injective_id⟩)
    simp

/-- A version of Lagrange's theorem. -/

lemma card_mulStab_mul_card_image_coe' (s t : Finset α)
    [DecidableEq (α ⧸ stabilizer α (t : Set α))] :
    #t.mulStab * #(s.image ((↑) : α → α ⧸ stabilizer α (t : Set α))) = #(s * t.mulStab) := by
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ (Set.image ((↑) : α → α ⧸ stabilizer α (t : Set α)) s)
  have that : ↥(stabilizer α (t : Set α)) = ↥t.mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab ht, Finset.coe_sort_coe]
  have temp := this.trans ((Equiv.cast that).prodCongr (Equiv.refl _))
  rw [preimage_image_quotientMk_stabilizer_eq_mul_mulStab ht] at temp
  simpa only [coe_sort_coe, ← coe_mul, Fintype.card_prod, Fintype.card_coe, Fintype.card_ofFinset,
    toFinset_coe, mem_image, Set.mem_image, mem_coe, forall_const, eq_comm]
    using Fintype.card_congr temp

lemma card_mul_card_eq_mulStab_card_mul_coe (s t : Finset α) :
    #(s * t) = #(s * t).mulStab * #((s * t).image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α))) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  have := QuotientGroup.preimageMkEquivSubgroupProdSet _ <|
    Set.image ((↑) : α → α ⧸ stabilizer α (↑(s * t) : Set α)) ↑(s * t)
  have that : ↥(stabilizer α (↑(s * t) : Set α)) = ↥(s * t).mulStab := by
    rw [← SetLike.coe_sort_coe, ← coe_mulStab (hs.mul ht), Finset.coe_sort_coe]
  have temp := this.trans <| (Equiv.cast that).prodCongr (Equiv.refl _)
  rw [preimage_image_quotientMk_mulStabilizer] at temp
  simpa [-coe_mul] using Fintype.card_congr temp

end Finset
/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Adapted from gdahia/ExtendingPollardForTRepresentableSums, commit 516693eeee.
Licensed under the Apache License, Version 2.0, available at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: Mantas Bakšys, Yaël Dillies
-/

/-
# Kneser's addition theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`. Further,
if the inequality is strict, then we in fact have `|s + H| + |t + H| ≤ |s + t|`.

## Main declarations

* `Finset.mul_kneser`: Kneser's theorem.
* `Finset.mul_strict_kneser`: Strict Kneser theorem.

## References

* [Imre Ruzsa, *Sumsets and structure*][ruzsa2009]
* Matt DeVos, *A short proof of Kneser's addition theorem*
-/

open Function MulAction
open scoped Pointwise

variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}

namespace Finset

/- ### Auxiliary results -/

lemma mulStab_mul_ssubset_mulStab (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by
  have hCne : C.Nonempty := by
    contrapose! hab
    simp only [hab, mulStab_empty, smul_finset_empty, empty_subset]
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := ht₁
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx)
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy)
  have hsubset : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab := by
    have hxymem : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
    apply subset_trans (mulStab_subset_div_right hxymem)
    have : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (x * y) • C.mulStab := by
      apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
      rw [smul_mul_smul_comm]
      rw [← hac, ← had, smul_mul_smul_comm, smul_assoc]
      apply smul_finset_subset_smul_finset
      rw [← smul_smul]
      rw [mul_subset_iff]
      intro x hx y hy
      rw [smul_mulStab hd, smul_mulStab hc, mem_mulStab hCne, ← smul_smul,
        (mem_mulStab hCne).mp hy, (mem_mulStab hCne).mp hx]
    apply subset_trans (div_subset_div_right this) _
    simp [singleton_mul, div_eq_inv_mul, smul_smul, mul_assoc]
  have : (a * b) • C.mulStab = (a * c * (b * d)) • C.mulStab := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mulStab hc, smul_mulStab hd]
  have hsub : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (a * b) • C.mulStab := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  have hxy : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, ?_⟩
  rw [mem_mulStab' ⟨x * y, hxy⟩]
  push Not
  refine ⟨a * c * (b * d), by simp_all, ?_⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (b := w), hwz]
  exact notMem_mono (mul_subset_mul inter_subset_left inter_subset_left) hzst

lemma mulStab_union (hs₁ : (s ∩ a • C.mulStab).Nonempty) (ht₁ : (t ∩ b • C.mulStab).Nonempty)
    (hab : ¬(a * b) • C.mulStab ⊆ s * t)
    (hC : Disjoint C (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))) :
    (C ∪ s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab =
      (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab := by
  obtain rfl | hCne := C.eq_empty_or_nonempty
  · simp
  refine
    ((subset_inter (mulStab_mul_ssubset_mulStab hs₁ ht₁ hab).subset Subset.rfl).trans
          inter_mulStab_subset_mulStab_union).antisymm'
      fun x hx => ?_
  replace hx := (mem_mulStab <| (hs₁.mul ht₁).mono subset_union_right).mp hx
  rw [smul_finset_union] at hx
  suffices hxC : x ∈ C.mulStab by
    rw [(mem_mulStab hCne).mp hxC] at hx
    rw [mem_mulStab_iff_subset_smul_finset (hs₁.mul ht₁)]
    exact hC.symm.left_le_of_le_sup_left (le_sup_right.trans hx.ge)
  rw [mem_mulStab_iff_smul_finset_subset hCne]
  obtain h | h := disjoint_or_nonempty_inter (x • C) (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))
  · exact h.left_le_of_le_sup_right (le_sup_left.trans_eq hx)
  have hUn :
    ((C.biUnion fun y => x • y • C.mulStab) ∩
        (s ∩ a • C.mulStab * (t ∩ b • C.mulStab))).Nonempty := by
    have : (x • C.biUnion fun y => y • C.mulStab) = C.biUnion fun y => x • y • C.mulStab :=
      biUnion_image
    simpa [← this]
  simp_rw [biUnion_inter, biUnion_nonempty, ← smul_assoc, smul_eq_mul] at hUn
  obtain ⟨y, hy, hyne⟩ := hUn
  have hxyCsubC : (x * y) • C.mulStab ⊆ x • C := by
    rw [← smul_eq_mul, smul_assoc, smul_finset_subset_smul_finset_iff]
    exact smul_finset_mulStab_subset hy
  have hxyC : Disjoint ((x * y) • C.mulStab) C := by
    convert disjoint_smul_finset_mulStab_mul_mulStab fun hxyC => _
    · exact C.mul_mulStab.symm
    rw [mul_mulStab] at hxyC
    exact hyne.not_disjoint (hC.mono_left hxyC)
  have hxysub : (x * y) • C.mulStab ⊆ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) :=
    hxyC.left_le_of_le_sup_left (hxyCsubC.trans <| subset_union_left.trans hx.subset)
  suffices s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊂ (a * b) • C.mulStab by
    have := (card_le_card hxysub).not_gt ((card_lt_card this).trans_eq ?_)
    cases this
    simp_rw [card_smul_finset]
  apply ssubset_of_subset_not_subset
  · refine (mul_subset_mul inter_subset_right inter_subset_right).trans ?_
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  · contrapose hab
    exact hab.trans (mul_subset_mul inter_subset_left inter_subset_left)

lemma mul_aux1
    (ih : #(s' * (s' * t').mulStab) + #(t' * (s' * t').mulStab) ≤ #(s' * t') + #(s' * t').mulStab)
    (hconv : #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab)
    (hnotconv :
      #(C ∪ s' * t') + #(C ∪ s' * t').mulStab < #(s ∩ t) + #((s ∪ t) * (C ∪ s' * t').mulStab))
    (hCun : (C ∪ s' * t').mulStab = (s' * t').mulStab) (hdisj : Disjoint C (s' * t')) :
    (#((s ∪ t) * C.mulStab) - #((s ∪ t) * (s' * t').mulStab) : ℤ) <
      #C.mulStab - #(s' * (s' * t').mulStab) - #(t' * (s' * t').mulStab) := by
  set H := C.mulStab
  set H' := (s' * t').mulStab
  set C' := C ∪ s' * t'
  zify at hconv hnotconv ih
  calc
    (#((s ∪ t) * H) - #((s ∪ t) * H') : ℤ) < #C + #H - #(s ∩ t) - (#C' + #H' - #(s ∩ t)) := by
      rw [← hCun]
      linarith [hconv, hnotconv]
    _ = #H - #(s' * t') - #H' := by
      rw [card_union_of_disjoint hdisj, Int.natCast_add]
      abel
    _ ≤ #H - #(s' * H') - #(t' * H') := by linarith [ih]

lemma disjoint_smul_mulStab (hst : s ⊆ t) (has : ¬a • s.mulStab ⊆ t) :
    Disjoint s (a • s.mulStab) := by
  suffices Disjoint (a • s.mulStab) (s * s.mulStab) by
    simpa [mul_comm, disjoint_comm, mulStab_mul]
  apply disjoint_smul_finset_mulStab_mul_mulStab
  rw [mul_comm, mulStab_mul]
  contrapose has
  exact subset_trans has hst

lemma disjoint_mul_sub_card_le {a : α} (b : α) {s t C : Finset α} (has : a ∈ s)
    (hsC : Disjoint t (a • C.mulStab))
    (hst : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
        #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) =
        #(a • C.mulStab \
            (s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset
          (subset_trans (mul_subset_mul_left hst)
            (subset_trans (mul_subset_mul_right inter_subset_right) _)),
        card_smul_finset, Int.ofNat_sub]
      · apply le_trans (card_le_card (mul_subset_mul_left hst))
        apply
          le_trans (card_le_card inter_mul_subset)
            (le_of_le_of_eq (card_le_card inter_subset_right) _)
        rw [smul_mul_assoc, mulStab_mul_mulStab, card_smul_finset]
      · simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      gcongr #?_
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      replace hyst : y ∈ s := by
        apply or_iff_not_imp_right.mp (mem_union.mp hyst)
        contrapose hsC
        exact not_disjoint_iff.mpr ⟨y, hsC, hyC⟩
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

lemma inter_mul_sub_card_le {a : α} {s t C : Finset α} (has : a ∈ s)
    (hst : (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab ⊆ C.mulStab) :
    (#C.mulStab : ℤ) -
          #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
        #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
      #((s ∪ t) * C.mulStab) -
        #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp
  calc
    (#C.mulStab : ℤ) -
            #(s ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) -
          #(t ∩ a • C.mulStab * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) ≤
        #(a • C.mulStab \
            ((s ∩ a • C.mulStab ∪ t ∩ a • C.mulStab) *
              (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab)) := by
      rw [card_sdiff_of_subset, Int.ofNat_sub (card_le_card _), card_smul_finset]
      · grw [union_mul, le_sub_iff_add_le, card_union_le]
        norm_num
      all_goals
        apply subset_trans (mul_subset_mul_left hst)
        rw [← union_inter_distrib_right]
        refine subset_trans (mul_subset_mul_right inter_subset_right) ?_
        simp only [smul_mul_assoc, mulStab_mul_mulStab, Subset.rfl]
    _ ≤ #((s ∪ t) * C.mulStab) -
          #((s ∪ t) * (s ∩ a • C.mulStab * (t ∩ a • C.mulStab)).mulStab) := by
      rw [← Int.ofNat_sub (card_le_card (mul_subset_mul_left hst)),
        ← card_sdiff_of_subset (mul_subset_mul_left hst)]
      norm_cast
      apply card_le_card
      refine fun x hx => mem_sdiff.mpr ⟨?_, ?_⟩
      · apply smul_finset_subset_smul (mem_union_left t has) (mem_sdiff.mp hx).1
      have hx' := (mem_sdiff.mp hx).2
      contrapose hx'
      rw [← union_inter_distrib_right]
      obtain ⟨y, hyst, d, hd, hxyd⟩ := mem_mul.mp hx'
      obtain ⟨c, hc, hcx⟩ := mem_smul_finset.mp (mem_sdiff.mp hx).1
      rw [← hcx, ← eq_mul_inv_iff_mul_eq] at hxyd
      have hyC : y ∈ a • C.mulStab := by
        rw [hxyd, smul_mul_assoc, smul_mem_smul_finset_iff, ← mulStab_mul_mulStab]
        apply mul_mem_mul hc ((mem_mulStab hC).mpr (inv_smul_eq_iff.mpr _))
        exact Eq.symm ((mem_mulStab hC).mp (hst hd))
      rw [eq_mul_inv_iff_mul_eq, hcx] at hxyd
      rw [← hxyd]
      exact mul_mem_mul (mem_inter.mpr ⟨hyst, hyC⟩) hd

lemma card_mul_add_card_lt (hC : C.Nonempty) (hs : s' ⊆ s) (ht : t' ⊆ t)
    (hCst : C ⊆ s * t) (hCst' : Disjoint C (s' * t')) :
    #(s' * t') + #s' < #(s * t) + #s :=
  add_lt_add_of_lt_of_le
      (by
        rw [← tsub_pos_iff_lt, ← card_sdiff_of_subset (mul_subset_mul hs ht), card_pos]
        exact hC.mono (subset_sdiff.2 ⟨hCst, hCst'⟩)) <|
    card_le_card hs

/- ### Kneser's theorem -/

variable (s t)

/-- **Kneser's multiplication theorem**: A lower bound on the size of `s * t` in terms of its
stabilizer. -/

theorem mul_kneser :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab)
      ≤ #(s * t) + #(s * t).mulStab := by
  -- We're doing induction on `#(s * t) + #s` generalizing the group. This is a bit tricky
  -- in Lean.
  set n : ℕ := #(s * t) + #s with hn
  clear_value n
  induction n using Nat.strong_induction_on generalizing α with | h n ih =>
  subst hn
  -- The cases `s = ∅` and `t = ∅` are easily taken care of.
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp
  obtain rfl | ht := t.eq_empty_or_nonempty
  · simp
  classical
  -- We distinguish whether `s * t` has trivial stabilizer.
  obtain hstab | hstab := ne_or_eq (s * t).mulStab 1
  · have image_coe_mul :
      ((s * t).image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) =
        s.image (↑) * t.image (↑) :=
      image_mul (QuotientGroup.mk' _ : α →* α ⧸ stabilizer α (↑(s * t) : Set α))
    suffices hineq :
      #(s * t).mulStab *
          (#(s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) +
              #(t.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) -  1) ≤
        #(s * t) by
    -- now to prove that `#(s * (s * t).mulStab) = #(s * t).mulStab * #(s.image (↑))` and
    -- the analogous statement for `s` and `t` interchanged
    -- this will conclude the proof of the first case immediately
      rw [mul_tsub, mul_one, mul_add, tsub_le_iff_left, card_mulStab_mul_card_image_coe',
        card_mulStab_mul_card_image_coe'] at hineq
      convert! hineq using 1
      exact add_comm _ _
    refine le_of_le_of_eq (mul_le_mul_right ?_ _) (card_mul_card_eq_mulStab_card_mul_coe s t).symm
    have := ih _ ?_ (s.image (↑) : Finset (α ⧸ stabilizer α (↑(s * t) : Set α))) (t.image (↑)) rfl
    · classical
      simpa only [← image_coe_mul, mulStab_image_coe_quotient (hs.mul ht), mul_one,
        tsub_le_iff_right, card_one] using this
    rw [← image_coe_mul, card_mul_card_eq_mulStab_card_mul_coe]
    exact
      add_lt_add_of_lt_of_le
        (lt_mul_left ((hs.mul ht).image _).card_pos <|
          Finset.one_lt_card.2 ((hs.mul ht).mulStab_nontrivial.2 hstab))
        card_image_le
  -- Simplify the induction hypothesis a bit. We will only need it over `α` from now on.
  simp only [hstab, mul_one, card_one] at ih ⊢
  replace ih := fun s' t' h => @ih _ h α _ _ s' t' rfl
  obtain ⟨a, rfl⟩ | ⟨a, ha, b, hb, hab⟩ := hs.exists_eq_singleton_or_nontrivial
  · rw [card_singleton, card_singleton_mul, add_comm]
  have : b / a ∉ t.mulStab := by
    refine fun h => hab (Eq.symm (eq_of_div_eq_one ?_))
    replace h := subset_mulStab_mul_right hs h
    rw [hstab, mem_one] at h
    exact h
  simp only [mem_mulStab' ht, smul_eq_mul, Classical.not_forall, exists_prop] at this
  obtain ⟨c, hc, hbac⟩ := this
  set t' := (a / c) • t with ht'
  clear_value t'
  rw [← inv_smul_eq_iff] at ht'
  subst ht'
  rename' t' => t
  rw [mem_inv_smul_finset_iff, smul_eq_mul, div_mul_cancel] at hc
  rw [div_mul_comm, mem_inv_smul_finset_iff, smul_eq_mul, ← mul_assoc, div_mul_div_cancel',
    div_self', one_mul] at hbac
  rw [smul_finset_nonempty] at ht
  simp only [mul_smul_comm, mulStab_smul, card_smul_finset] at *
  have hst : (s ∩ t).Nonempty := ⟨_, mem_inter.2 ⟨ha, hc⟩⟩
  have hsts : s ∩ t ⊂ s :=
    ⟨inter_subset_left, not_subset.2 ⟨_, hb, fun h => hbac <| inter_subset_right h⟩⟩
  clear! a b
  set convergent : Set (Finset α) :=
    {C | C ⊆ s * t ∧ #(s ∩ t) + #((s ∪ t) * C.mulStab) ≤ #C + #C.mulStab}
  have convergent_nonempty : convergent.Nonempty := by
    refine ⟨s ∩ t * (s ∪ t), inter_mul_union_subset, (add_le_add_left (card_le_card <|
      subset_mul_left _ <| one_mem_mulStab.2 <| hst.mul <| hs.mono subset_union_left) _).trans <|
        ih (s ∩ t) (s ∪ t) ?_⟩
    exact add_lt_add_of_le_of_lt (card_le_card inter_mul_union_subset) (card_lt_card hsts)
  let C := argminOn (fun C : Finset α => #C.mulStab) _ convergent_nonempty
  set H := C.mulStab with hH
  obtain ⟨hCst, hCcard⟩ : C ∈ convergent := argminOn_mem _ _ _
  have hCmin (D : Finset α) (hDH : D.mulStab ⊂ H) : D ∉ convergent := fun hD ↦
    (card_lt_card hDH).not_ge <| argminOn_le (fun D : Finset α => #D.mulStab) _ hD
  clear_value C
  clear convergent_nonempty
  obtain rfl | hC := C.eq_empty_or_nonempty
  · simp [hst.ne_empty] at hCcard
  -- If the stabilizer of `C` is trivial, then
  -- `#s + #t - 1 = #(s ∩ t) + #(s ∪ t) - 1 = ≤ #C ≤ #(s * t)`
  obtain hCstab | hCstab := eq_singleton_or_nontrivial (one_mem_mulStab.2 hC)
  · simp only [hCstab, card_singleton, card_mul_singleton, card_inter_add_card_union] at hCcard
    grw [hCcard, hCst]
  exfalso
  have : ¬s * t * H ⊆ s * t := by
    rw [mul_subset_left_iff (hs.mul ht), hstab, ← coe_subset, coe_one]
    exact hCstab.coe.not_subset_singleton
  simp_rw [mul_subset_iff_left, Classical.not_forall, mem_mul] at this
  obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, hab⟩ := this
  set s₁ := s ∩ a • H with hs₁
  set s₂ := s ∩ b • H with hs₂
  set t₁ := t ∩ b • H with ht₁
  set t₂ := t ∩ a • H with ht₂
  have hs₁s : s₁ ⊆ s := inter_subset_left
  have hs₂s : s₂ ⊆ s := inter_subset_left
  have ht₁t : t₁ ⊆ t := inter_subset_left
  have ht₂t : t₂ ⊆ t := inter_subset_left
  have has₁ : a ∈ s₁ := mem_inter.mpr ⟨ha, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hbt₁ : b ∈ t₁ := mem_inter.mpr ⟨hb, mem_smul_finset.2 ⟨1, one_mem_mulStab.2 hC, mul_one _⟩⟩
  have hs₁ne : s₁.Nonempty := ⟨_, has₁⟩
  have ht₁ne : t₁.Nonempty := ⟨_, hbt₁⟩
  set C₁ := C ∪ s₁ * t₁
  set C₂ := C ∪ s₂ * t₂
  set H₁ := (s₁ * t₁).mulStab with hH₁
  set H₂ := (s₂ * t₂).mulStab
  have hC₁st : C₁ ⊆ s * t := union_subset hCst (mul_subset_mul hs₁s ht₁t)
  have hC₂st : C₂ ⊆ s * t := union_subset hCst (mul_subset_mul hs₂s ht₂t)
  have hstabH₁ : s₁ * t₁ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hstabH₂ : s₂ * t₂ ⊆ (a * b) • H := by
    rw [hH, ← mulStab_mul_mulStab C, ← smul_mul_smul_comm, mul_comm s₂ t₂]
    apply mul_subset_mul inter_subset_right inter_subset_right
  have hCst₁ := disjoint_of_subset_right hstabH₁ (disjoint_smul_mulStab hCst hab)
  have hCst₂ := disjoint_of_subset_right hstabH₂ (disjoint_smul_mulStab hCst hab)
  have hst₁ : #(s₁ * t₁) + #s₁ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₁s ht₁t hCst hCst₁
  have hst₂ : #(s₂ * t₂) + #s₂ < #(s * t) + #s :=
    card_mul_add_card_lt hC hs₂s ht₂t hCst hCst₂
  have hC₁stab : C₁.mulStab = H₁ := mulStab_union hs₁ne ht₁ne hab hCst₁
  have hH₁H : H₁ ⊂ H := mulStab_mul_ssubset_mulStab hs₁ne ht₁ne hab
  have aux1₁ :=
    mul_aux1 (ih _ _ hst₁) hCcard
      (not_le.1 fun h => hCmin _ (hC₁stab.trans_ssubset hH₁H) ⟨hC₁st, h⟩) hC₁stab hCst₁
  obtain ht₂ | ht₂ne := t₂.eq_empty_or_nonempty
  · have aux₁_contr :=
      disjoint_mul_sub_card_le b (hs₁s has₁) (disjoint_iff_inter_eq_empty.2 ht₂) hH₁H.subset
    linarith [aux1₁, aux₁_contr, Int.natCast_nonneg #(t₁ * (s₁ * t₁).mulStab)]
  obtain hs₂ | hs₂ne := s₂.eq_empty_or_nonempty
  · have aux1₁_contr :
      (#C.mulStab : ℤ) - #(t₁ * (s₁ * t₁).mulStab) ≤
        #((s ∪ t) * C.mulStab) - #((s ∪ t) * (s₁ * t₁).mulStab) := by
      simpa [union_comm, mul_comm s₁ t₁] using
        disjoint_mul_sub_card_le a (ht₁t hbt₁) (disjoint_iff_inter_eq_empty.2 hs₂)
          (by rw [mul_comm]; exact hH₁H.subset)
    linarith [aux1₁, aux1₁_contr, Int.natCast_nonneg #(s₁ * (s₁ * t₁).mulStab)]
  have hC₂stab : C₂.mulStab = H₂ := mulStab_union hs₂ne ht₂ne (by rwa [mul_comm]) hCst₂
  have hH₂H : H₂ ⊂ H := mulStab_mul_ssubset_mulStab hs₂ne ht₂ne (by rwa [mul_comm])
  have aux1₂ :=
    mul_aux1 (ih _ _ hst₂) hCcard
      (not_le.1 fun h => hCmin _ (hC₂stab.trans_ssubset hH₂H) ⟨hC₂st, h⟩) hC₂stab hCst₂
  obtain habH | habH := eq_or_ne (a • H) (b • H)
  · rw [hH₁, hs₁, ht₁, ← habH, hH] at hH₁H
    refine aux1₁.not_ge ?_
    simp only [hs₁, ht₁, ← habH, inter_mul_sub_card_le (hs₁s has₁) hH₁H.subset, H]
  -- temporarily skipping deduction of inequality (2)
  set S := a • H \ (s₁ ∪ t₂) with hS
  set T := b • H \ (s₂ ∪ t₁) with hT
  have hST : Disjoint S T :=
    (C.pairwiseDisjoint_smul_finset_mulStab (Set.mem_range_self _) (Set.mem_range_self _)
          habH).mono
      sdiff_le sdiff_le
  have hSst : S ⊆ a • H \ (s ∪ t) := by
    simp only [hS, hs₁, ht₂, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hTst : T ⊆ b • H \ (s ∪ t) := by
    simp only [hT, hs₂, ht₁, ← union_inter_distrib_right, sdiff_inter_self_right, Subset.rfl]
  have hSTst : Disjoint (S ∪ T) (s ∪ t) := (subset_sdiff.1 hSst).2.sup_left (subset_sdiff.1 hTst).2
  have hstconv : s * t ∉ convergent := by
    apply hCmin (s * t)
    rw [hstab]
    refine (hC.mulStab_nontrivial.mp hCstab).symm.ssubset_of_subset ?_
    simp only [one_subset, one_mem_mulStab, hC]
  simp only [Set.mem_ofPred_eq, Subset.rfl, true_and, not_le, hstab, mul_one, card_one,
    convergent] at hstconv
  zify at hstconv
  have hSTcard : (#S : ℤ) + #T + #(s ∪ t) ≤ #((s ∪ t) * H) := by
    norm_cast
    conv_lhs => rw [← card_union_of_disjoint hST, ← card_union_of_disjoint hSTst, ← mul_one (s ∪ t)]
    refine card_le_card
      (union_subset (union_subset ?_ ?_) <| mul_subset_mul_left <| one_subset.2 (one_mem_mulStab.mpr hC))
    · exact hSst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_left _ ha)
    · exact hTst.trans (sdiff_subset.trans <| smul_finset_subset_smul <| mem_union_right _ hb)
  have hH₁ne : H₁.Nonempty := (hs₁ne.mul ht₁ne).mulStab
  have hH₂ne : H₂.Nonempty := (hs₂ne.mul ht₂ne).mulStab
  -- Now we prove inequality (2)
  have aux2₁ : (#s₁ : ℤ) + #t₁ + #H₁ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₁H.subset).trans_lt aux1₁) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₁ne.mul ht₁ne) hH₁H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    gcongr _ - (Nat.cast ?_ + Nat.cast ?_) <;> exact card_le_card_mul_right hH₁ne
  have aux2₂ : (#s₂ : ℤ) + #t₂ + #H₂ ≤ #H := by
    rw [← le_sub_iff_add_le']
    refine (Int.le_of_dvd ((sub_nonneg_of_le <| Nat.cast_le.2 <| card_le_card <|
      mul_subset_mul_left hH₂H.subset).trans_lt aux1₂) <| dvd_sub
        (dvd_sub (card_mulStab_dvd_card_mulStab (hs₂ne.mul ht₂ne) hH₂H.subset).natCast
          (card_mulStab_dvd_card_mul_mulStab _ _).natCast) <|
        (card_mulStab_dvd_card_mul_mulStab _ _).natCast).trans ?_
    rw [sub_sub]
    exact sub_le_sub_left (add_le_add (Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) <|
      Nat.cast_le.2 <| card_le_card_mul_right hH₂ne) _
  -- Now we deduce inequality (3) using the above lemma in addition to the facts that `s * t` is not
  -- convergent and then induction hypothesis applied to `sᵢ` and `tᵢ`
  have aux3₁ : (#S : ℤ) + #T + #s₁ + #t₁ - #H₁ < #H :=
    calc
      (#S : ℤ) + #T + #s₁ + #t₁ - #H₁
        < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₁ * t₁) := by
        have ih₁ :=
          (add_le_add (card_le_card_mul_right hH₁ne) <| card_le_card_mul_right hH₁ne).trans
            (ih _ _ hst₁)
        zify at ih₁
        linarith [hstconv, ih₁]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₁ * t₁) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₁] using card_le_card hC₁st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux3₂ : (#S : ℤ) + #T + #s₂ + #t₂ - #H₂ < #H :=
    calc
      (#S : ℤ) + #T + #s₂ + #t₂ - #H₂
       < #S + #T + #(s ∪ t) + #(s ∩ t) - #(s * t) + #(s₂ * t₂) := by
        have ih₂ :=
          (add_le_add (card_le_card_mul_right hH₂ne) <| card_le_card_mul_right hH₂ne).trans
            (ih _ _ hst₂)
        zify at hstconv ih₂
        linarith [ih₂]
      _ ≤ #((s ∪ t) * H) + #(s ∩ t) - #C := by
        suffices (#C : ℤ) + #(s₂ * t₂) ≤ #(s * t) by linarith [this, hSTcard]
        · norm_cast
          simpa only [← card_union_of_disjoint hCst₂] using card_le_card hC₂st
      _ ≤ #H := by
        simpa only [sub_le_iff_le_add, ← Int.natCast_add, Int.ofNat_le, add_comm _ #C,
          add_comm _ #(s ∩ t)] using hCcard
  have aux4₁ : #H ≤ #S + (#s₁ + #t₂) := by
    grw [← card_smul_finset a H, card_le_card_sdiff_add_card, card_union_le]
  have aux4₂ : #H ≤ #T + (#s₂ + #t₁) := by
    grw [← card_smul_finset b H, card_le_card_sdiff_add_card, card_union_le]
  linarith [aux2₁, aux2₂, aux3₁, aux3₂, aux4₁, aux4₂]

/-- The strict version of **Kneser's multiplication theorem**. If the LHS of `Finset.mul_kneser`
does not equal the RHS, then it is in fact much smaller. -/

lemma mul_strict_kneser (h : #(s * (s * t).mulStab) + #(t * (s * t).mulStab) <
      #(s * t) + #(s * t).mulStab) :
    #(s * (s * t).mulStab) + #(t * (s * t).mulStab) ≤ #(s * t) :=
  Nat.le_of_lt_add_of_dvd h
      ((card_mulStab_dvd_card_mul_mulStab _ _).add <| card_mulStab_dvd_card_mul_mulStab _ _) <|
    card_mulStab_dvd_card _

end Finset
namespace Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The translation stabilizer of a finite set. For the empty set this
finite-set convention returns the empty set as well. -/
def addStab (s : Finset G) : Finset G :=
  @mulStab (Multiplicative G) _ _ s

lemma mem_addStab {s : Finset G} {x : G} (hs : s.Nonempty) :
    x ∈ s.addStab ↔ x +ᵥ s = s :=
  @mem_mulStab (Multiplicative G) _ _ s x hs

theorem add_kneser (s t : Finset G) :
    (s + (s + t).addStab).card + (t + (s + t).addStab).card ≤
      (s + t).card + (s + t).addStab.card :=
  @mul_kneser (Multiplicative G) _ _ s t

end Finset

/-
License supplied with the adapted Bakšys–Dillies files.

Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/

end

section

open scoped Pointwise

namespace Finset

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

lemma coe_addStab {s : Finset G} (hs : s.Nonempty) :
    (s.addStab : Set G) = AddAction.stabilizer G (s : Set G) :=
  @coe_mulStab (Multiplicative G) _ _ s hs

lemma zero_mem_addStab {s : Finset G} : (0 : G) ∈ s.addStab ↔ s.Nonempty :=
  @one_mem_mulStab (Multiplicative G) _ _ s

lemma add_addStab (s : Finset G) : s + s.addStab = s :=
  @mul_mulStab (Multiplicative G) _ _ s

lemma addStab_add_addStab (s : Finset G) : s.addStab + s.addStab = s.addStab :=
  @mulStab_mul_mulStab (Multiplicative G) _ _ s

lemma subset_addStab_add_left {s t : Finset G} (ht : t.Nonempty) :
    s.addStab ⊆ (s + t).addStab :=
  @subset_mulStab_mul_left (Multiplicative G) _ _ s t ht

/-- Growth of iterated sums, with the defect measured by the stabilizer of the final sum. -/
lemma card_nsmul_bound {r : ℕ} (hr : 0 < r) (B : Finset G) (hB : B.Nonempty) :
    r * B.card ≤ (r • B).card + (r - 1) * (r • B).addStab.card := by
  have aux (j : ℕ) (hj : j + 1 ≤ r) :
      (j + 1) * B.card ≤ ((j + 1) • B).card + j * (r • B).addStab.card := by
    induction j with
    | zero => simp
    | succ j ih =>
      let T := (j + 1) • B
      let S := (j + 2) • B
      have hT : T.Nonempty := hB.nsmul
      have hS : S.Nonempty := hB.nsmul
      have hS' : T + B = S := (succ_nsmul B (j + 1)).symm
      have zeroS : 0 ∈ S.addStab := zero_mem_addStab.mpr hS
      have hsmall : T.card + B.card ≤ S.card + S.addStab.card := by
        have kn := add_kneser T B
        rw [hS'] at kn
        exact (Nat.add_le_add (card_le_card (subset_add_left T zeroS))
          (card_le_card (subset_add_left B zeroS))).trans kn
      have hnum : j + 2 + (r - (j + 2)) = r := by omega
      have subset : S.addStab ⊆ (r • B).addStab := by
        have hne : ((r - (j + 2)) • B).Nonempty := hB.nsmul
        have h := subset_addStab_add_left (s := S) hne
        simpa only [S, ← add_nsmul, hnum] using h
      have hcard := card_le_card subset
      have ind := ih (by omega)
      change (j + 1) * B.card ≤ T.card + j * (r • B).addStab.card at ind
      change (j + 2) * B.card ≤ S.card + (j + 1) * (r • B).addStab.card
      nlinarith only [hsmall, hcard, ind]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  simpa using aux j le_rfl

/-- The r-fold Kneser inequality for the stabilizer of the final sumset. -/
lemma card_nsmul_addStab_bound {r : ℕ} (hr : 0 < r) (B : Finset G) (hB : B.Nonempty) :
    r * (B + (r • B).addStab).card ≤ (r • B).card + (r - 1) * (r • B).addStab.card := by
  let H := (r • B).addStab
  have hH : H.Nonempty := ⟨0, zero_mem_addStab.mpr hB.nsmul⟩
  have hidem : H + H = H := addStab_add_addStab _
  have powH (j : ℕ) : (j + 1) • H = H := by
    induction j with
    | zero => exact one_nsmul H
    | succ j ih => rw [succ_nsmul, ih, hidem]
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  have hrH : r • H = H := hj ▸ powH j
  have heq : r • (B + H) = r • B := by rw [nsmul_add, hrH]; exact add_addStab _
  simpa only [heq] using card_nsmul_bound hr (B + H) (hB.add hH)

end Finset

end

section

/-! # A cyclic quotient obstruction for a forbidden iterated sum -/

namespace OMA.Erdos13Cyclic

open Finset
open scoped Pointwise

lemma quotient_periods {G : Type} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (hne : S.Nonempty) :
    let H := AddAction.stabilizer G (S : Set G)
    let p := QuotientAddGroup.mk' H
    ∀ (q : G ⧸ H), q ∈ (S.image p).addStab ↔ q = 0 := by
  classical
  intro H p
  have fix (x : G) : x ∈ H ↔ x +ᵥ S = S := by
    change x ∈ AddAction.stabilizer G (S : Set G) ↔ _
    rw [AddAction.mem_stabilizer_iff, ← Finset.coe_vadd_finset, Finset.coe_inj]
  have saturated (z : G) : p z ∈ S.image p ↔ z ∈ S := by
    constructor
    · intro hz
      obtain ⟨y, hy, heq⟩ := mem_image.mp hz
      have hmem : z - y ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp heq.symm
      have hz' := vadd_mem_vadd_finset (a := z - y) hy
      rw [(fix _).mp hmem] at hz'
      simpa [vadd_eq_add] using hz'
    · exact mem_image_of_mem _
  intro q
  rw [Finset.mem_addStab (hne.image _)]
  constructor
  · intro hq
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective H q
    apply (QuotientAddGroup.eq_zero_iff x).mpr
    apply (fix x).mpr
    apply Finset.eq_of_subset_of_card_le _ (by simp)
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_vadd_finset.mp hz
    apply (saturated _).mp
    have h := vadd_mem_vadd_finset (a := p x) (mem_image_of_mem p hy)
    rw [hq] at h
    simpa only [vadd_eq_add, map_add] using h
  · rintro rfl
    simp

theorem quotient_witness {r a : ℕ} (hr : 2 ≤ r) (ha : 0 < a)
    (T : Finset ℕ) (hT : T.Nonempty)
    (free : ∀ b : Fin r → ℕ, (∀ i, b i ∈ T) → ¬ a ∣ ∑ i, b i) :
    ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ T, ¬ d ∣ b) ∧
      r * (T.image (fun x => x % d)).card ≤ d + r - 2 := by
  classical
  let : NeZero a := ⟨ha.ne'⟩
  let B := T.image (fun x : ℕ => (x : ZMod a))
  let S := r • B
  have hB : B.Nonempty := hT.image _
  have hS : S.Nonempty := hB.nsmul
  have hz : (0 : ZMod a) ∉ S := by
    intro h
    obtain ⟨f, hf⟩ := Finset.mem_nsmul.mp h
    have chooseNat (i : Fin r) : ∃ x ∈ T, (x : ZMod a) = (f i : ZMod a) :=
      mem_image.mp (f i).property
    choose b hb he using chooseNat
    apply free b hb
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    rw [Nat.cast_sum]
    simpa only [he, List.sum_ofFn] using hf
  let H := AddAction.stabilizer (ZMod a) (S : Set (ZMod a))
  let Q := ZMod a ⧸ H
  let p := QuotientAddGroup.mk' H
  let C := B.image p
  have pmem (x : ZMod a) (hx : x ∈ H) : x +ᵥ S = S := by
    apply Finset.coe_inj.mp
    rw [Finset.coe_vadd_finset]
    exact AddAction.mem_stabilizer_iff.mp hx
  have mapS : S.image p = r • C := Finset.image_nsmul p B r
  have hzQ : (0 : Q) ∉ r • C := by
    rw [← mapS]
    rintro h
    obtain ⟨y, hy, hyp⟩ := mem_image.mp h
    have hneg := pmem (-y) (H.neg_mem ((QuotientAddGroup.eq_zero_iff y).mp hyp))
    have h0 := vadd_mem_vadd_finset (a := -y) hy
    rw [hneg] at h0
    exact hz (by simpa [vadd_eq_add] using h0)
  have per : (r • C).addStab = {0} := by
    ext q
    rw [← mapS, mem_singleton]
    exact quotient_periods S hS q
  have hC : C.Nonempty := hB.image _
  have estimate := Finset.card_nsmul_bound (r := r) (by omega) C hC
  rw [per] at estimate
  have simplified : r * C.card ≤ (r • C).card + (r - 1) := by
    simpa only [card_singleton, Nat.mul_one] using estimate
  let g : Q := p 1
  let d := addOrderOf g
  have gen (n : ℕ) : p (n : ZMod a) = n • g := by
    change p (n : ZMod a) = n • p 1
    rw [← map_nsmul]
    simp [nsmul_eq_mul]
  let : Fintype Q := Fintype.ofFinite _
  have hd : d = Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    apply addOrderOf_eq_card_of_forall_mem_zmultiples
    intro x
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective H x
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.val : ℤ), ?_⟩
    rw [natCast_zsmul]
    change z.val • g = p z
    rw [← gen, ZMod.natCast_zmod_val]
  have cardIneq := Finset.card_lt_univ_of_notMem hzQ
  have hpos : 0 < d := hd ▸ Fintype.card_pos
  refine ⟨d, hpos, ?_, ?_, ?_⟩
  · apply addOrderOf_dvd_iff_nsmul_eq_zero.mpr
    simpa using (gen a).symm
  · intro b hb hdvd
    have hzero : p (b : ZMod a) = 0 := (gen b).trans (addOrderOf_dvd_iff_nsmul_eq_zero.mp hdvd)
    have hbt : p (b : ZMod a) ∈ C := mem_image_of_mem _ (mem_image_of_mem _ hb)
    rw [hzero] at hbt
    apply hzQ
    simpa using (nsmul_mem_nsmul (n := r) hbt)
  · have conv (n : ℕ) : (n % d) • g = p (n : ZMod a) :=
      (nsmul_eq_nsmul_iff_modEq.mpr (Nat.mod_modEq n d)).trans (gen n).symm
    have imageC : (T.image (fun x => x % d)).image (fun i => i • g) = C := by
      dsimp [C, B]
      rw [Finset.image_image, Finset.image_image]
      exact Finset.image_congr fun n _ => conv n
    have inj : (↑(T.image (fun x => x % d)) : Set ℕ).InjOn (fun i => i • g) := by
      intro x hx y hy hh
      obtain ⟨m, _, rfl⟩ := mem_image.mp hx
      obtain ⟨n, _, rfl⟩ := mem_image.mp hy
      have modEq := nsmul_eq_nsmul_iff_modEq.mp hh
      change m % d % d = n % d % d at modEq
      simpa only [Nat.mod_mod] using modEq
    have hcard := Finset.card_image_of_injOn inj
    rw [imageC] at hcard
    rw [← hcard]
    omega

end OMA.Erdos13Cyclic

end

section

/-! Complete residue lifts prohibit further congruences among offsets. -/

namespace Erdos13ColumnModulo
open Finset

lemma allocate_mixed (m : ℕ) (l u : Fin m → ℕ) (k : ℕ)
    (each : ∀ i, l i ≤ u i) (low : ∑ i, l i ≤ k) (high : k ≤ ∑ i, u i) :
    ∃ f : Fin m → ℕ, (∀ i, l i ≤ f i ∧ f i ≤ u i) ∧ ∑ i, f i = k := by
  induction m generalizing k with
  | zero => exact ⟨fun i => i.elim0,fun i => i.elim0,by simpa [eq_comm] using high⟩
  | succ m ih =>
    let x := min (u 0) (k-∑ i : Fin m, l i.succ)
    rw [Fin.sum_univ_succ] at low high
    have part_bound : (∑ i : Fin m, l i.succ) ≤ ∑ i : Fin m, u i.succ :=
      sum_le_sum fun i _ => each i.succ
    have tail := ih (fun i => l i.succ) (fun i => u i.succ) (k-x) (fun i => each i.succ)
      (by dsimp [x]; omega) (by dsimp [x]; omega)
    obtain ⟨f,hf,hs⟩ := tail
    refine ⟨Fin.cons x f, Fin.forall_fin_succ.mpr ⟨?_,?_⟩,?_⟩
    · simp only [Fin.cons_zero]
      have := each 0
      dsimp [x]
      omega
    · simpa using hf
    · simp only [Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,hs]
      dsimp [x]
      omega

lemma next_dilate {r a : ℕ} {A P : Finset ℕ} (hr : 3 ≤ r)
    (off : ∀ u ∈ P, 0 < u ∧ u < a)
    (lifts : ∀ u ∈ P, ∀ j ∈ Icc 1 r, j*a+u ∈ A)
    (free : FullColumns.Free r A) (u : ℕ) (hu : u ∈ P)
    (v : Fin r → ℕ) (hv : ∀ i, v i ∈ P) :
    ¬ (∑ i, v i) ≡ (r+1)*u [MOD a] := by
  classical
  intro eqmod
  obtain ⟨c,hc⟩ := Nat.modEq_iff_dvd.mp eqmod
  let n := (univ.filter (fun i : Fin r => v i ≤ u)).card
  have nc : n ≤ r := by simpa [n] using card_filter_le (s := (univ : Finset (Fin r))) (fun i => v i ≤ u)
  have sum_cap : (∑ i, v i) ≤ n*u+(r-n)*(a-1) := by
    have loc (i : Fin r) : v i ≤ if v i ≤ u then u else a-1 := by
      split
      · assumption
      · have := (off _ (hv i)).2
        omega
    have h := sum_le_sum (s := (univ : Finset (Fin r))) (fun i _ => loc i)
    have count := (univ : Finset (Fin r)).card_filter_add_card_filter_not (fun i => v i ≤ u)
    simp only [card_univ,Fintype.card_fin] at count
    simpa only [sum_ite,sum_const,nsmul_eq_mul, Nat.cast_id,
      show #(univ.filter fun i : Fin r => ¬ v i ≤ u) = r-n by dsimp [n]; omega] using h
  have small : (∑ i, v i) + n*a < (r+1)*u+r*a := by
    have nd := Nat.sub_add_cancel nc
    have ru := Nat.mul_le_mul_right u nc
    have aux := congrArg (fun z : ℕ => z*a) nd
    have xpos := (off u hu).1
    nlinarith only [sum_cap,ru,aux,xpos,Nat.mul_le_mul_left (r-n) (Nat.sub_le a 1)]
  have pos := (off u hu).1
  have ua := (off u hu).2
  have ksmall : (r+1)*u < (r+1)*a := Nat.mul_lt_mul_of_pos_left ua (by omega)
  push_cast at hc
  have cmin : (n:ℤ) - r < c := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at small
    nlinarith only [hc,hz,small]
  have cmax : c < (r+1:ℕ) := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at ksmall
    have nn : (0:ℤ) ≤ ∑ i,(v i:ℤ) := sum_nonneg (fun i _ => Int.natCast_nonneg _)
    push_cast at hz
    nlinarith only [hc,hz,ksmall,nn]
  let h := max 1 ((n:ℤ)-c).toNat
  have h1 : 1 ≤ h := le_max_left _ _
  have hlow : (n:ℤ) ≤ (h:ℤ)+c := by
    have hh := le_max_right 1 ((n:ℤ)-c).toNat
    change _ ≤ h at hh
    omega
  have hcap : h ≤ r-1 := by dsimp [h]; omega
  have heither : h=1 ∨ (h:ℤ)=(n:ℤ)-c := by dsimp [h]; omega
  have upper : (((r+1)*h:ℕ):ℤ)+c ≤ (r*r:ℕ) := by
    rcases heither with h₁|h₂
    · rw [h₁,Nat.mul_one]
      have bound : 2*r+1 ≤ r*r := by nlinarith [Nat.mul_le_mul_left r hr]
      omega
    · have z := Nat.mul_le_mul_left r hcap
      have rr : r*(r-1)=r*r-r := by rw [Nat.mul_sub,Nat.mul_one]
      have rt := Nat.le_mul_self r
      zify at z nc ⊢
      have succ : (r:ℤ)-1=(r-1:ℕ) := by omega
      push_cast at *
      nlinarith only [z,nc,h₂,succ]
  let K := (((r+1)*h:ℕ)+c).toNat
  have Kint : (K:ℤ)=((r+1)*h:ℕ)+c := by
    apply Int.toNat_of_nonneg
    rw [Nat.add_mul,Nat.one_mul]
    push_cast
    nlinarith only [hlow,Int.natCast_nonneg n, mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg h)]
  let l (i : Fin r) := h + if v i ≤ u then 1 else 0
  have lsum : ∑ i,l i = r*h+n := by simp [l,sum_add_distrib,n]
  have minK : ∑ i,l i ≤ K := by
    rw [lsum]
    have id : (r+1)*h=r*h+h := by ring
    omega
  obtain ⟨f,hf,hfs⟩ := allocate_mixed r l (fun _ => r) K
    (fun i => by dsimp [l]; split <;> omega) minK (by simpa using (show K ≤ r*r by omega))
  have base := lifts u hu h (mem_Icc.mpr ⟨h1,by omega⟩)
  apply free _ base (fun i => f i*a+v i)
  · intro i
    apply lifts _ (hv i) _ (mem_Icc.mpr ⟨?_,(hf i).2⟩)
    have o := (hf i).1
    dsimp [l] at o
    split at o <;> omega
  · intro i
    have o := (hf i).1
    dsimp [l] at o
    split at o
    · have F := Nat.mul_le_mul_right a o
      have := (off _ hu).2
      rw [Nat.add_mul,Nat.one_mul] at F
      omega
    · have F := Nat.mul_le_mul_right a o
      simp only [Nat.add_zero] at F
      omega
  · refine ⟨r+1,?_⟩
    rw [sum_add_distrib,←sum_mul,hfs]
    zify at Kint hc ⊢
    push_cast at *
    nlinarith only [Kint,hc]

end Erdos13ColumnModulo

end

section

/-! Allocation of a divisor height for modular relations of intermediate arity. -/
namespace Erdos13ColumnModulo

lemma choose_base {r j n : ℕ} (hr : 3 ≤ r) (hj : 0 < j) (nc : n ≤ r)
    (top : 2*(r+j) ≤ r*r+1) (c : ℤ)
    (cl : (n:ℤ)-r < c) (cu : c < (r+j:ℕ)) :
    ∃ h : ℕ, 1 ≤ h ∧ h < r ∧
      (n:ℤ) ≤ j*h+c ∧ (((r+j)*h:ℕ):ℤ)+c ≤ (r*r:ℕ) := by
  by_cases simple : (n:ℤ) ≤ j+c
  · refine ⟨1,le_rfl,by omega,by simpa using simple,?_⟩
    rw [Nat.mul_one]
    omega
  let m := ((n:ℤ)-c).toNat
  have mval : (m:ℤ)=(n:ℤ)-c := by dsimp [m]; omega
  have mcap : m < r := by omega
  have jm : j < m := by omega
  let h := (m-1)/j+1
  have hmin : (h-1)*j < m := by
    have bound := Nat.div_mul_le_self (m-1) j
    dsimp [h]
    exact lt_of_le_of_lt bound (Nat.sub_lt (lt_trans hj jm) (by decide))
  have hmax : m ≤ h*j := by
    have rem := Nat.mod_add_div (m-1) j
    have lt := Nat.mod_lt (m-1) hj
    dsimp [h]
    rw [Nat.add_mul,Nat.one_mul]
    rw [mul_comm j _] at rem
    omega
  have h1 : 1 ≤ h := Nat.succ_pos _
  have hdec : h-1+1=h := by omega
  have part := congrArg (fun z : ℕ => z*j) hdec
  have hm : h ≤ m := by
    have h := Nat.mul_le_mul_left (h-1) hj
    rw [Nat.mul_one] at h
    omega
  have min : (n:ℤ) ≤ j*h+c := by
    rw [Nat.mul_comm] at hmax
    zify at hmax
    omega
  refine ⟨h,h1,by omega,min,?_⟩
  have extra : h*j ≤ m+j-1 := by nlinarith only [hmin, part, Nat.sub_add_cancel (show 1 ≤ m+j by omega)]
  by_cases one : j=1
  · subst j
    simp only [Nat.mul_one,Nat.add_sub_cancel] at extra
    have z := Nat.mul_le_mul_left r (show h ≤ r-1 by omega)
    have dec : r-1+1=r := by omega
    have ident := congrArg (fun x : ℕ => r*x) dec
    zify at extra nc z ident ⊢
    nlinarith only [z,ident,extra,mval,nc]
  · have h2 := Nat.mul_le_mul_left (h-1) (show 2≤j by omega)
    have bound : 2*h≤r+1 := by omega
    have cap : h ≤ r-2 := by omega
    have z := Nat.mul_le_mul_left r cap
    have dec : r-2+2=r := by omega
    have ident := congrArg (fun x : ℕ => r*x) dec
    have extra' : h*j ≤ m+j := by omega
    zify at extra' nc z ident jm mcap ⊢
    nlinarith only [z,ident,extra',nc,jm,mcap,mval]
end Erdos13ColumnModulo

end

section

/-! A complete column rules out dilate relations across an interval of multipliers. -/
namespace Erdos13ColumnModulo
open Finset

lemma dilate_range {r a j : ℕ} {A P : Finset ℕ} (hr : 3 ≤ r) (hj : 0 < j) (top : 2*(r+j) ≤ r*r+1)
    (off : ∀ u ∈ P, 0 < u ∧ u < a)
    (lifts : ∀ u ∈ P, ∀ j ∈ Icc 1 r, j*a+u ∈ A)
    (free : FullColumns.Free r A) (u : ℕ) (hu : u ∈ P)
    (v : Fin r → ℕ) (hv : ∀ i, v i ∈ P) :
    ¬ (∑ i, v i) ≡ (r+j)*u [MOD a] := by
  classical
  intro eqmod
  obtain ⟨c,hc⟩ := Nat.modEq_iff_dvd.mp eqmod
  let n := (univ.filter (fun i : Fin r => v i ≤ u)).card
  have nc : n ≤ r := by simpa [n] using card_filter_le (s := (univ : Finset (Fin r))) (fun i => v i ≤ u)
  have sum_cap : (∑ i, v i) ≤ n*u+(r-n)*(a-1) := by
    have loc (i : Fin r) : v i ≤ if v i ≤ u then u else a-1 := by
      split
      · assumption
      · have := (off _ (hv i)).2
        omega
    have h := sum_le_sum (s := (univ : Finset (Fin r))) (fun i _ => loc i)
    have count := (univ : Finset (Fin r)).card_filter_add_card_filter_not (fun i => v i ≤ u)
    simp only [card_univ,Fintype.card_fin] at count
    simpa only [sum_ite,sum_const,nsmul_eq_mul, Nat.cast_id,
      show #(univ.filter fun i : Fin r => ¬ v i ≤ u) = r-n by dsimp [n]; omega] using h
  have small : (∑ i, v i) + n*a < (r+j)*u+r*a := by
    have nd := Nat.sub_add_cancel nc
    have ru := Nat.mul_le_mul_right u nc
    have aux := congrArg (fun z : ℕ => z*a) nd
    have xpos := (off u hu).1
    have uj := Nat.mul_le_mul_right u hj
    nlinarith only [sum_cap,ru,aux,xpos,uj,Nat.mul_le_mul_left (r-n) (Nat.sub_le a 1)]
  have pos := (off u hu).1
  have ua := (off u hu).2
  have ksmall : (r+j)*u < (r+j)*a := Nat.mul_lt_mul_of_pos_left ua (by omega)
  push_cast at hc
  have cmin : (n:ℤ) - r < c := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at small
    nlinarith only [hc,hz,small]
  have cmax : c < (r+j:ℕ) := by
    by_contra! hn
    have hz := mul_le_mul_of_nonneg_left hn (Int.natCast_nonneg a)
    zify at ksmall
    have nn : (0:ℤ) ≤ ∑ i,(v i:ℤ) := sum_nonneg (fun i _ => Int.natCast_nonneg _)
    push_cast at hz
    nlinarith only [hc,hz,ksmall,nn]
  obtain ⟨h,h1,hcap,hlow,upper⟩ := choose_base hr hj nc top c cmin cmax
  let K := (((r+j)*h:ℕ)+c).toNat
  have Kint : (K:ℤ)=((r+j)*h:ℕ)+c := by
    apply Int.toNat_of_nonneg
    rw [Nat.add_mul]
    push_cast
    nlinarith only [hlow,Int.natCast_nonneg n, mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg h)]
  let l (i : Fin r) := h + if v i ≤ u then 1 else 0
  have lsum : ∑ i,l i = r*h+n := by simp [l,sum_add_distrib,n]
  have minK : ∑ i,l i ≤ K := by
    rw [lsum]
    have id : (r+j)*h=r*h+j*h := by ring
    zify at id ⊢
    push_cast at Kint
    omega
  obtain ⟨f,hf,hfs⟩ := allocate_mixed r l (fun _ => r) K
    (fun i => by dsimp [l]; split <;> omega) minK (by simpa using (show K ≤ r*r by omega))
  have base := lifts u hu h (mem_Icc.mpr ⟨h1,by omega⟩)
  apply free _ base (fun i => f i*a+v i)
  · intro i
    apply lifts _ (hv i) _ (mem_Icc.mpr ⟨?_,(hf i).2⟩)
    have o := (hf i).1
    dsimp [l] at o
    split at o <;> omega
  · intro i
    have o := (hf i).1
    dsimp [l] at o
    split at o
    · have F := Nat.mul_le_mul_right a o
      have := (off _ hu).2
      rw [Nat.add_mul,Nat.one_mul] at F
      omega
    · have F := Nat.mul_le_mul_right a o
      simp only [Nat.add_zero] at F
      omega
  · refine ⟨r+j,?_⟩
    rw [sum_add_distrib,←sum_mul,hfs]
    zify at Kint hc ⊢
    push_cast at *
    nlinarith only [Kint,hc]

end Erdos13ColumnModulo

end

section

/-! Density estimates for complete columns in an aperiodic cyclic quotient. -/
namespace Erdos13ColumnModulo
open Finset
open scoped Pointwise

lemma coprime_scalar {q k : ℕ} (cop : k.Coprime q) :
    Function.Injective (fun x : ZMod q => k • x) := by
  intro x y h
  simpa only [nsmul_eq_mul] using ((ZMod.isUnit_iff_coprime k q).mpr cop).mul_right_inj.mp
    (show (k : ZMod q)*x = k*y by simpa [nsmul_eq_mul] using h)

lemma twice_card {q : ℕ} [NeZero q] (R : Finset (ZMod q)) :
    R.card ≤ 2*(R.image (fun x => 2 • x)).card := by
  let f (x : ZMod q) := (2 • x,2*x.val/q)
  let T := R.image (fun x => 2 • x) ×ˢ range 2
  have incl (x : ZMod q) (hx : x ∈ R) : f x ∈ T := by
    apply mem_product.mpr
    exact ⟨mem_image_of_mem _ hx,mem_range.mpr ((Nat.div_lt_iff_lt_mul (NeZero.pos q)).mpr
      (Nat.mul_lt_mul_of_pos_left x.val_lt (by decide)))⟩
  have inject (x : ZMod q) : (2 • x).val = (2*x.val)%q := by
    have eq : (2 • x : ZMod q) = ((2*x.val:ℕ):ZMod q) := by
      simp [nsmul_eq_mul]
    rw [eq,ZMod.val_natCast]
  have count := card_le_card_of_injOn f incl (by
    intro x hx y hy he
    have h₁ := congrArg (fun t : ZMod q × ℕ => t.1.val) he
    have h₂ := congrArg Prod.snd he
    change (2 • x).val = (2 • y).val at h₁
    change 2*x.val/q = 2*y.val/q at h₂
    rw [inject,inject] at h₁
    have xq := Nat.mod_add_div (2*x.val) q
    have yq := Nat.mod_add_div (2*y.val) q
    rw [h₁,h₂] at xq
    exact ZMod.val_injective q (by omega))
  simpa [T,Nat.mul_comm] using count

lemma cyclic_estimates {q r k L : ℕ} [NeZero q] (hr : 2 ≤ r)
    (R : Finset (ZMod q)) (hne : R.Nonempty)
    (aper : (r • R).addStab = {0})
    (cop : k.Coprime q) (low : r < k) (high : 2*k ≤ r+L)
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R) :
    r*R.card+L ≤ q+(r-1) ∧
    (r+1)*R.card+(R.card+1)/2 ≤ q+(r-1) ∧
    (2 ∣ k → (r+2)*R.card ≤ q+(r-1)) ∧
    ((2:ℕ).Coprime q → (r+2)*R.card ≤ q+(r-1)) := by
  classical
  let S := r • R
  have growth : r*R.card ≤ S.card+(r-1) := by
    have h := Finset.card_nsmul_bound (r:=r) (by omega) R hne
    rwa [aper,card_singleton,Nat.mul_one] at h
  have pair (T : Finset (ZMod q)) (disj : Disjoint S T) : S.card+T.card ≤ q := by
    have count := (S∪T).card_le_univ
    rwa [card_union_of_disjoint disj,ZMod.card] at count
  obtain ⟨x,hx⟩ := hne
  have orde : L < addOrderOf x := by
    have pos := addOrderOf_pos x
    by_contra! h
    have bad := excluded x hx (r+addOrderOf x) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    rw [add_nsmul,addOrderOf_nsmul_eq_zero,add_zero] at bad
    exact bad (nsmul_mem_nsmul hx)
  let f (i : ℕ) := (r+1+i) • x
  have E := pair ((range L).image f) (disjoint_left.mpr (by
    intro y hy h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have := mem_range.mp hi
    exact excluded x hx _ (mem_Ioc.mpr ⟨by omega,by omega⟩) hy))
  have cardF : ((range L).image f).card=L := by
    rw [card_image_of_injOn,card_range]
    intro i hi j hj eq
    have same := (nsmul_eq_nsmul_iff_modEq.mp eq).add_left_cancel' (r+1)
    have iord := (mem_range.mp hi).trans orde
    have jord := (mem_range.mp hj).trans orde
    simpa [Nat.ModEq,Nat.mod_eq_of_lt iord,Nat.mod_eq_of_lt jord] using same
  rw [cardF] at E
  let U := R.image (fun z => k • z)
  let D := R.image (fun z => 2 • z)
  let V := D.image (fun z => k • z)
  have ci := coprime_scalar cop
  have cu : U.card=R.card := card_image_of_injective _ ci
  have cv : V.card=D.card := card_image_of_injective _ ci
  have uv : Disjoint U V := disjoint_left.mpr (by
    intro z hu hv
    obtain ⟨x,hx,hxz⟩ := mem_image.mp hu
    obtain ⟨w,hw,hwz⟩ := mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hw
    have eq : x=2 • y := ci (hxz.trans hwz.symm)
    have forbid := excluded y hy (r+1) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    apply forbid
    have rp : r-1+1=r := by omega
    have o := Finset.add_mem_add (nsmul_mem_nsmul (n:=r-1) hy) hx
    rw [eq,←add_nsmul,←succ_nsmul,rp] at o
    simpa [show r-1+2=r+1 by omega] using o)
  have pack := pair (U∪V) (disjoint_left.mpr (by
    intro z hz h
    rcases mem_union.mp h with hu|hv
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      exact excluded x hx k (mem_Ioc.mpr ⟨low,by omega⟩) hz
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
      rw [←mul_nsmul] at hz
      exact excluded x hx _ (mem_Ioc.mpr ⟨by omega,high⟩) hz))
  rw [card_union_of_disjoint uv,cu,cv] at pack
  have half := twice_card R
  change R.card ≤ 2*D.card at half
  have full (odd : (2:ℕ).Coprime q) : (r+2)*R.card ≤ q+(r-1) := by
    have dd : D.card=R.card := card_image_of_injective _ (coprime_scalar odd)
    rw [dd] at pack
    nlinarith only [growth,pack]
  refine ⟨by omega,?_,fun d => full (cop.of_dvd_left d),full⟩
  rw [Nat.add_mul,Nat.one_mul]
  omega

lemma packing_arithmetic {r q s k L : ℕ} (hr : 5 ≤ r)
    (low : r < k) (high : 2*k ≤ r+L)
    (full_range : 2*(r+L) ≤ r*r+1 ∧ r*r+1 < 2*(r+L+1))
    (one : r*s+L ≤ q+(r-1)) (two : (r+1)*s+(s+1)/2 ≤ q+(r-1))
    (evenK : 2 ∣ k → (r+2)*s ≤ q+(r-1))
    (oddQ : (2:ℕ).Coprime q → (r+2)*s ≤ q+(r-1)) :
    (r+1)*s ≤ q := by
  have large (hh : 2*(r-1) ≤ s+1) : (r+1)*s ≤ q := by omega
  have small (hh : s+r-1 ≤ L) : (r+1)*s ≤ q := by
    rw [Nat.add_mul,Nat.one_mul]
    omega
  by_cases rr : 7 ≤ r
  · have d : r-7+7=r := by omega
    have z := Nat.mul_le_mul_left (r-7) (show 8 ≤ r+1 by omega)
    have Lb : 3*r ≤ L+4 := by
      obtain ⟨_,b⟩ := full_range
      nlinarith only [d,z,b]
    by_cases h : 2*(r-1) ≤ s+1
    · exact large h
    · exact small (by omega)
  · interval_cases r
    · have h6 : k=6 := by omega
      have stronger := evenK (h6 ▸ by decide)
      omega
    · by_cases h : 10 ≤ s+1
      · exact large (by omega)
      by_cases hh : s ≤ 7
      · exact small (by omega)
      by_contra! bad
      have v : q=55 := by omega
      have stronger := oddQ (v ▸ by decide)
      omega

/-- An aperiodic cyclic quotient admitting an invertible k with both k and
2k in the prohibited multiplier interval has density at most 1/(r+1). -/
theorem good_cyclic_packing {q r k L : ℕ} [NeZero q] (hr : 5 ≤ r)
    (R : Finset (ZMod q)) (hne : R.Nonempty)
    (aper : (r • R).addStab = {0}) (cop : k.Coprime q)
    (low : r < k) (high : 2*k ≤ r+L)
    (full_range : 2*(r+L) ≤ r*r+1 ∧ r*r+1 < 2*(r+L+1))
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R) :
    (r+1)*R.card ≤ q := by
  obtain ⟨a,b,c,d⟩ := cyclic_estimates (by omega) R hne aper cop low high excluded
  exact packing_arithmetic hr low high full_range a b c d

end Erdos13ColumnModulo

end

section

/-! Reduction of modular complete-column constraints to an aperiodic cyclic group. -/
namespace Erdos13ColumnModulo
open Finset
open scoped Pointwise

theorem reduce_columns {r a L : ℕ} (ha : 0 < a) (P : Finset ℕ) (hne : P.Nonempty)
    (excl : ∀ u ∈ P, ∀ j ∈ Ioc r (r+L), ∀ v : Fin r → ℕ,
      (∀ i,v i ∈ P) → ¬ (∑ i,v i) ≡ j*u [MOD a]) :
    ∃ q : ℕ, ∃ hq : 0 < q, q ∣ a ∧
      let R := P.image (fun x : ℕ => (x : ZMod q))
      (r • R).addStab = {0} ∧
        ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R := by
  classical
  let : NeZero a := ⟨ha.ne'⟩
  let B := P.image (fun x : ℕ => (x : ZMod a))
  let S := r • B
  have hB : B.Nonempty := hne.image _
  have hS : S.Nonempty := hB.nsmul
  let H := AddAction.stabilizer (ZMod a) (S : Set (ZMod a))
  let Q := ZMod a ⧸ H
  let π := QuotientAddGroup.mk' H
  let g : Q := π 1
  let q := Nat.card Q
  let : Fintype Q := Fintype.ofFinite _
  have hq : 0 < q := by dsimp [q]; rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  let : NeZero q := ⟨hq.ne'⟩
  have generates (x : Q) : x ∈ AddSubgroup.zmultiples g := by
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective H x
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.val : ℤ),?_⟩
    rw [natCast_zsmul]
    change z.val • π 1 = π z
    rw [←map_nsmul]
    simp [nsmul_eq_mul]
  let e : ZMod q ≃+ Q := zmodAddEquivOfGenerator generates rfl
  let p := e.symm.toAddMonoidHom.comp π
  have p1 : p 1 = 1 := zmodAddEquivOfGenerator_symm_apply_generator generates rfl
  have pn (x : ℕ) : p (x : ZMod a) = (x : ZMod q) := by
    calc
      p (x : ZMod a) = p (x • (1 : ZMod a)) := by simp [nsmul_eq_mul]
      _ = x • p 1 := map_nsmul _ _ _
      _ = x := by rw [p1]; simp [nsmul_eq_mul]
  have surj : Function.Surjective p := e.symm.surjective.comp (QuotientAddGroup.mk'_surjective H)
  have fix (z : ZMod a) : z ∈ H ↔ z +ᵥ S = S := by
    change z ∈ AddAction.stabilizer (ZMod a) (S : Set (ZMod a)) ↔ _
    rw [AddAction.mem_stabilizer_iff,←Finset.coe_vadd_finset,Finset.coe_inj]
  have sat (z : ZMod a) : p z ∈ S.image p ↔ z ∈ S := by
    refine ⟨?_,mem_image_of_mem _⟩
    intro hz
    obtain ⟨y,hy,hEq⟩ := mem_image.mp hz
    have eqπ : π y = π z := e.symm.injective hEq
    have hmem : z-y ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp eqπ.symm
    have hfix := vadd_mem_vadd_finset (a := z-y) hy
    rw [(fix _).mp hmem] at hfix
    simpa [vadd_eq_add] using hfix
  let R := P.image (fun x : ℕ => (x : ZMod q))
  have mapped : S.image p = r • R := by
    have m : B.image p = R := by
      dsimp [B,R]
      rw [image_image]
      exact image_congr fun x _ => pn x
    exact (Finset.image_nsmul p B r).trans (congrArg (r • ·) m)
  refine ⟨q,hq,?_,?_,?_⟩
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp [←pn a]
  · ext w
    change w ∈ (r • R).addStab ↔ _
    rw [←mapped,mem_singleton,mem_addStab (hS.image _)]
    constructor
    · obtain ⟨z,rfl⟩ := surj w
      intro hw
      have hz : z ∈ H := (fix _).mpr (by
        apply Finset.eq_of_subset_of_card_le _ (by simp)
        intro v hv
        obtain ⟨y,hy,rfl⟩ := mem_vadd_finset.mp hv
        apply (sat _).mp
        have h := vadd_mem_vadd_finset (a:=p z) (mem_image_of_mem p hy)
        rw [hw] at h
        simpa [vadd_eq_add] using h)
      have hzero := (QuotientAddGroup.eq_zero_iff z).mpr hz
      change e.symm (π z)=0
      rw [show π z =0 from hzero,map_zero]
    · rintro rfl
      simp
  · intro x hx j hj hjx
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    change j • (u : ZMod q) ∈ r • R at hjx
    rw [←mapped,←pn u,←map_nsmul,sat] at hjx
    obtain ⟨v,hv⟩ := Finset.mem_nsmul.mp hjx
    have rep (i : Fin r) : ∃ w ∈ P, (w : ZMod a)=(v i:ZMod a) := mem_image.mp (v i).property
    choose b hb be using rep
    apply excl u hu j hj b hb
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_sum,Nat.cast_mul]
    simpa [List.sum_ofFn,be,nsmul_eq_mul] using hv

end Erdos13ColumnModulo

end

section

namespace Erdos13HalfOccupied

open Finset

/-- Count a set in consecutive periods and in the last partial period. -/
lemma count_by_period (q t s : ℕ) (hs : s ≤ q) (R : Finset ℕ) :
    ∀ (v : ℕ) (B : Finset ℕ), B ⊆ Ico v (v + (t * q + s)) →
      (∀ b ∈ B, b % q ∈ R) → B.card ≤ t * R.card + min s R.card := by
  classical
  have one (v : ℕ) (B : Finset ℕ) (hI : B ⊆ Ico v (v+q))
      (hR : ∀ b ∈ B, b % q ∈ R) : B.card ≤ R.card := by
    apply card_le_card_of_injOn (fun x : ℕ => x % q) hR
    exact (Nat.mod_injOn_Ico v q).mono (by exact_mod_cast hI)
  induction t with
  | zero =>
    intro v B hI hR
    simp only [Nat.zero_mul, Nat.zero_add] at hI ⊢
    apply le_min
    · have := card_le_card hI
      simpa using this
    · apply one v B _ hR
      exact hI.trans (Ico_subset_Ico_right (by omega))
  | succ t ih =>
    intro v B hI hR
    let P := B.filter (fun b => b < v+q)
    let Q := B.filter (fun b => ¬b < v+q)
    have hP : P.card ≤ R.card := by
      apply one v P
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Ico.mpr ⟨(mem_Ico.mp (hI h.1)).1, h.2⟩
      · intro x hx
        exact hR x (mem_filter.mp hx).1
    have hQ : Q.card ≤ t * R.card + min s R.card := by
      apply ih (v+q) Q
      · intro x hx
        have h := mem_filter.mp hx
        have hi := mem_Ico.mp (hI h.1)
        rw [Nat.succ_mul] at hi
        exact mem_Ico.mpr ⟨by omega, by omega⟩
      · intro x hx
        exact hR x (mem_filter.mp hx).1
    have hab := B.card_filter_add_card_filter_not (fun b => b < v+q)
    change P.card + Q.card = B.card at hab
    rw [Nat.succ_mul]
    omega

/-- A period q with at most (q+1)/3 occupied classes cannot support a
strict majority for two full periods, once q exceeds four. For one full
period, its length is forced to lie within one of three quarters of m. -/
lemma small_period_or_near {m q c b : ℕ} (hq : 0 < q)
    (hqm : q ≤ m) (he : 3*c ≤ q+1) (major : m < 2*b)
    (cap : b ≤ (m / q) * c + min (m % q) c) :
    q ≤ 4 ∨ (3*m / 4 - 2 ≤ q ∧ q ≤ 3*m / 4 + 2) := by
  by_cases hsmall : q ≤ 4
  · exact Or.inl hsmall
  right
  let t := m/q
  let s := m%q
  have dec : s + t*q = m := by
    dsimp [s, t]
    simpa only [Nat.mul_comm] using Nat.mod_add_div m q
  have hs : s < q := Nat.mod_lt _ hq
  have hcap : b ≤ t*c + min s c := cap
  have ht : t ≤ 1 := by
    by_contra! high
    have h2c : 2*c ≤ q := by omega
    have hdiff : 2*(q-2*c) ≤ t*(q-2*c) := Nat.mul_le_mul_right _ high
    rw [Nat.mul_sub] at hdiff
    have aux : t*(2*c) ≤ t*q := Nat.mul_le_mul_left t h2c
    have ident : t*(2*c) = 2*(t*c) := by ring
    have hd : t*(q-2*c) = t*q-t*(2*c) := Nat.mul_sub _ _ _
    have hmin : 2*min s c ≤ s+c := by omega
    omega
  have hone : t = 1 := Nat.le_antisymm ht (Nat.div_pos hqm hq)
  rw [hone, Nat.one_mul] at dec hcap
  omega

/-- All but boundedly many possible divisors force the selected small element
above r times the size of the upper interval, up to r-2. -/
lemma force_large_divisor {r m q a v : ℕ} (hr : 3 ≤ r) (hq : 0 < q)
    (hqa : q ≤ a) (B : Finset ℕ) (hB : B ⊆ Ico v (v+m))
    (major : m < 2*B.card)
    (quotient : r * (B.image (fun x => x%q)).card ≤ q + r - 2) :
    q ∈ range 5 ∪ Icc (3*m / 4 - 2) (3*m / 4 + 2) ∨
      (m < q ∧ r*B.card ≤ a+r-2) := by
  classical
  let R := B.image (fun x => x%q)
  have hR (b) (hb : b ∈ B) : b%q ∈ R := mem_image_of_mem _ hb
  change r * R.card ≤ q+r-2 at quotient
  by_cases hqm : q ≤ m
  · left
    have h3 : 3 * R.card ≤ q + 1 := by
      by_cases hc : R.card = 0
      · simp [hc]
      have hr3 := Nat.mul_le_mul_right (R.card-1) hr
      rw [Nat.mul_sub, Nat.mul_sub] at hr3
      have hrc : r ≤ r*R.card := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left r (show 1 ≤ R.card by omega)
      omega
    have rem := Nat.mod_add_div m q
    have dec : m / q * q + m % q = m := by
      simpa only [Nat.mul_comm, Nat.add_comm] using rem
    have hI : B ⊆ Ico v (v + (m/q*q + m%q)) := by simpa only [dec] using hB
    have cap := count_by_period q (m/q) (m%q) (Nat.mod_lt _ hq).le R v B hI hR
    rcases small_period_or_near hq hqm h3 major cap with h | h
    · exact mem_union_left _ (mem_range.mpr (by omega))
    · exact mem_union_right _ (mem_Icc.mpr h)
  · right
    refine ⟨by omega, ?_⟩
    have hinj : (B : Set ℕ).InjOn (fun x => x % q) := by
      apply (Nat.mod_injOn_Ico v q).mono
      intro b hb
      have := mem_Ico.mp (hB hb)
      exact mem_Ico.mpr ⟨this.1, by omega⟩
    have heq : R.card = B.card := card_image_of_injOn hinj
    rw [heq] at quotient
    omega

lemma exceptional_card (m : ℕ) :
    (range 5 ∪ Icc (3*m/4-2) (3*m/4+2)).card ≤ 10 := by
  have h := card_union_le (range 5) (Icc (3*m/4-2) (3*m/4+2))
  simp only [card_range, Nat.card_Icc] at h
  omega

/-- The chosen quotient for the smaller of two elements cannot also divide
the larger element. Therefore all exceptional quotients cost at most ten
elements of a finite set, even when the quotients vary along the set. -/
lemma exceptional_elements (A : Finset ℕ) (f : ℕ → ℕ) (m : ℕ)
    (divides : ∀ a ∈ A, f a ∣ a)
    (only_here : ∀ a ∈ A, ∀ b ∈ A, a < b → ¬ f a ∣ b) :
    (A.filter (fun a => f a ∈ range 5 ∪ Icc (3*m/4-2) (3*m/4+2))).card ≤ 10 := by
  classical
  refine le_trans (card_le_card_of_injOn f ?_ ?_) (exceptional_card m)
  · intro a ha
    exact (mem_filter.mp ha).2
  · intro a ha b hb hfb
    have ha' := (mem_filter.mp ha).1
    have hb' := (mem_filter.mp hb).1
    rcases lt_trichotomy a b with h | h | h
    · exact False.elim (only_here a ha' b hb' h (hfb.symm ▸ divides b hb'))
    · exact h
    · exact False.elim (only_here b hb' a ha' h (hfb ▸ divides a ha'))

end Erdos13HalfOccupied

end

section

/-! A cyclic obstruction giving a strict saving for complete columns,
apart from an explicit exceptional case at arity three. -/
namespace Erdos13ColumnModulo
open Finset FullColumns
open scoped Pointwise

lemma scalar_card {q : ℕ} (k : ℕ) (kp : 0<k) [NeZero q] (R : Finset (ZMod q)) :
    R.card ≤ k*(R.image (fun x => k • x)).card := by
  let f (x : ZMod q) := (k • x,k*x.val/q)
  let T := R.image (fun x => k • x) ×ˢ range k
  have incl (x : ZMod q) (hx : x ∈ R) : f x ∈ T := by
    apply mem_product.mpr
    exact ⟨mem_image_of_mem _ hx,mem_range.mpr ((Nat.div_lt_iff_lt_mul (NeZero.pos q)).mpr
      (Nat.mul_lt_mul_of_pos_left x.val_lt kp))⟩
  have inject (x : ZMod q) : (k • x).val = (k*x.val)%q := by
    have eq : (k • x : ZMod q) = ((k*x.val:ℕ):ZMod q) := by
      simp [nsmul_eq_mul]
    rw [eq,ZMod.val_natCast]
  have count := card_le_card_of_injOn f incl (by
    intro x hx y hy he
    have h₁ := congrArg (fun t : ZMod q × ℕ => t.1.val) he
    have h₂ := congrArg Prod.snd he
    change (k • x).val = (k • y).val at h₁
    change k*x.val/q = k*y.val/q at h₂
    rw [inject,inject] at h₁
    have xq := Nat.mod_add_div (k*x.val) q
    have yq := Nat.mod_add_div (k*y.val) q
    rw [h₁,h₂] at xq
    exact ZMod.val_injective q (Nat.eq_of_mul_eq_mul_left kp (by omega)))
  simpa [T,Nat.mul_comm] using count

lemma unrestricted_cycle {q r L : ℕ} [NeZero q] (hr : 3≤r)
    (R : Finset (ZMod q)) (hne : R.Nonempty) (aper : (r • R).addStab = {0})
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r (r+L), j • x ∉ r • R) :
    r*R.card+L ≤ q+(r-1) ∧
    (∀ x ∈ R, L < addOrderOf x) ∧
    (∀ j ∈ Ioc r (r+L), j*(r*R.card)+R.card ≤ j*(q+(r-1)) ∧
        (j.Coprime q → (r+1)*R.card ≤ q+(r-1))) := by
  classical
  let S := r • R
  have growth : r*R.card ≤ S.card+(r-1) := by
    have h := Finset.card_nsmul_bound (r:=r) (by omega) R hne
    rwa [aper,card_singleton,Nat.mul_one] at h
  have pair (T : Finset (ZMod q)) (disj : Disjoint S T) : S.card+T.card ≤ q := by
    have count := (S∪T).card_le_univ
    rwa [card_union_of_disjoint disj,ZMod.card] at count
  have order_guard (x) (hx : x ∈ R) : L < addOrderOf x := by
    have pos := addOrderOf_pos x
    by_contra! h
    have bad := excluded x hx (r+addOrderOf x) (mem_Ioc.mpr ⟨by omega,by omega⟩)
    rw [add_nsmul,addOrderOf_nsmul_eq_zero,add_zero] at bad
    exact bad (nsmul_mem_nsmul hx)
  obtain ⟨x,hx⟩ := hne
  have orde := order_guard x hx
  let f (i : ℕ) := (r+1+i) • x
  have E := pair ((range L).image f) (disjoint_left.mpr (by
    intro y hy h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have := mem_range.mp hi
    exact excluded x hx _ (mem_Ioc.mpr ⟨by omega,by omega⟩) hy))
  have cardF : ((range L).image f).card=L := by
    rw [card_image_of_injOn,card_range]
    intro i hi j hj eq
    have same := (nsmul_eq_nsmul_iff_modEq.mp eq).add_left_cancel' (r+1)
    have iord := (mem_range.mp hi).trans orde
    have jord := (mem_range.mp hj).trans orde
    simpa [Nat.ModEq,Nat.mod_eq_of_lt iord,Nat.mod_eq_of_lt jord] using same
  rw [cardF] at E
  refine ⟨by omega,order_guard,?_⟩
  intro j hj
  have jp : 0<j := by have := (mem_Ioc.mp hj).1; omega
  let V := R.image (fun x => j • x)
  have packing := pair V (disjoint_left.mpr (by
    intro z hz h
    obtain ⟨x,hx,rfl⟩ := mem_image.mp h
    exact excluded x hx j hj hz))
  have sc := scalar_card j jp R
  change R.card ≤ j*V.card at sc
  have jpack := Nat.mul_le_mul_left j packing
  have jgrowth := Nat.mul_le_mul_left j growth
  refine ⟨by nlinarith only [sc,jgrowth,jpack],?_⟩
  intro cop
  have h : V.card=R.card := card_image_of_injective _ (coprime_scalar cop)
  rw [h] at packing
  rw [Nat.add_mul,Nat.one_mul]
  omega

lemma small_three_unit {q : ℕ} (hp : 0<q) (sm : q ≤ 24) (dvd : 3 ∣ q) :
    (4:ℕ).Coprime q ∨ (5:ℕ).Coprime q := by
  obtain ⟨v,rfl⟩ := dvd
  have hi : v ≤ 8 := by omega
  have vp : 0<v := by omega
  interval_cases v <;> decide

def densityFactor (r : ℕ) := 2*(r+1)*r

theorem universal_cycle {q r : ℕ} [NeZero q] (hr : 3≤r)
    (R : Finset (ZMod q)) (hne : R.Nonempty) (aper : (r • R).addStab = {0})
    (excluded : ∀ x ∈ R, ∀ j ∈ Ioc r ((r*r+1)/2), j • x ∉ r • R) :
    (densityFactor r*r+1)*R.card ≤ densityFactor r*q ∨
      (r=3 ∧ (q=3 ∨ q=6) ∧ ∀ x ∈ R, 2 < addOrderOf x) := by
  let L := (r*r+1)/2-r
  have quad := Nat.mul_le_mul_left r hr
  have rL : r+L=(r*r+1)/2 := by dsimp [L]; omega
  have ll : 2 ≤ L := by dsimp [L]; omega
  obtain ⟨span,guard,per⟩ := unrestricted_cycle (L:=L) hr R hne aper (by rwa [rL])
  have one := (per (r+1) (mem_Ioc.mpr ⟨by omega,by omega⟩)).1
  let s := R.card
  change r*s+L ≤ q+(r-1) at span
  change (r+1)*(r*s)+s ≤ (r+1)*(q+(r-1)) at one
  by_cases strict : r*s<q
  · left
    change (densityFactor r*r+1)*s ≤ densityFactor r*q
    by_cases big : 2*(r+1)*(r-1) ≤ s
    · have cut : (2*(r+1)*r+1)*s ≤ 2*(r+1)*q := by nlinarith only [one,big]
      have diff := Nat.mul_le_mul_left (densityFactor r-2*(r+1)) strict.le
      have band : 2*(r+1) ≤ densityFactor r := by
        exact (by simpa only [Nat.mul_one,densityFactor] using Nat.mul_le_mul_left (2*(r+1)) (show 1≤r by omega))
      have dec := Nat.sub_add_cancel band
      have eqL := congrArg (fun z : ℕ => z*(r*s)) dec
      have eqR := congrArg (fun z : ℕ => z*q) dec
      nlinarith only [cut,diff,eqL,eqR]
    · have small : s ≤ densityFactor r :=
        (le_of_lt (lt_of_not_ge big)).trans (Nat.mul_le_mul_left _ (Nat.sub_le r 1))
      have diff := Nat.mul_le_mul_left (densityFactor r) (show r*s+1≤q by omega)
      nlinarith only [diff,small]
  · right
    have eqr : r=3 := by
      by_contra! no
      have g : 4≤r := by omega
      have sq := Nat.mul_le_mul_left r g
      have cut : r≤L := by dsimp [L]; omega
      omega
    subst r
    have lval : L=2 := by decide
    have eq : 3*s=q := by omega
    have sm : q≤24 := by omega
    have cop := small_three_unit (NeZero.pos q) sm (show 3∣q from ⟨s,eq.symm⟩)
    have sharp : 4*s ≤ q+2 := by
      rcases cop with h|h
      · exact (per 4 (mem_Ioc.mpr ⟨by decide,by omega⟩)).2 h
      · exact (per 5 (mem_Ioc.mpr ⟨by decide,by omega⟩)).2 h
    have hp := NeZero.pos q
    exact ⟨rfl,by omega,by simpa [lval] using guard⟩

/-- Complete columns are uniformly sparse throughout their full ambient period.
The only exception forces arity three and removes all multiples of three. -/
theorem complete_universal {r a : ℕ} (hr : 3≤r) (ha : 0<a) (P : Finset ℕ)
    {A : Finset ℕ} (off : ∀ u ∈ P, 0 < u ∧ u<a)
    (lifts : ∀ u ∈ P, ∀ i ∈ Icc 1 r, i*a+u ∈ A) (free : Free r A) :
    (densityFactor r*r+1)*P.card ≤ densityFactor r*a ∨
      r=3 ∧ 3∣a ∧ ∀ u ∈ P, ¬3∣u := by
  classical
  by_cases hn : P.Nonempty
  · let L := (r*r+1)/2-r
    have quad := Nat.mul_le_mul_left r hr
    have rL : r+L=(r*r+1)/2 := by dsimp [L]; omega
    obtain ⟨q,hq,dvd,aper,excluded⟩ := reduce_columns (r:=r) (L:=L) ha P hn (by
      intro u hu j hj f hf
      have h := mem_Ioc.mp hj
      have e : r+(j-r)=j := by omega
      simpa only [e] using dilate_range hr (j:=j-r) (by omega) (by omega) off lifts free u hu f hf)
    let : NeZero q := ⟨hq.ne'⟩
    let R := P.image (fun x : ℕ => (x : ZMod q))
    rcases universal_cycle hr R (hn.image _) aper (by rwa [←rL]) with bound|⟨r3,q36,ord⟩
    · left
      let T := P.image (·%q)
      have eq : R.image ZMod.val=T := by
        dsimp [R,T]
        rw [image_image]
        exact image_congr (fun x _ => ZMod.val_natCast _ _)
      have dense : T.card=R.card := eq ▸ card_image_of_injective _ (ZMod.val_injective q)
      have dec : a/q*q=a := Nat.div_mul_cancel dvd
      have cap := Erdos13HalfOccupied.count_by_period q (a/q) 0 (Nat.zero_le _) T 0 P (by
        intro x hx
        have := (off x hx).2
        simpa only [Nat.zero_add,Nat.add_zero,dec,mem_Ico,Nat.zero_le,true_and] using this)
        (fun x hx => mem_image_of_mem _ hx)
      simp only [min_eq_left (Nat.zero_le _),Nat.add_zero,dense] at cap
      have a1 := Nat.mul_le_mul_left (densityFactor r*r+1) cap
      have a2 := Nat.mul_le_mul_left (a/q) bound
      have aid := congrArg (fun z : ℕ => densityFactor r*z) dec
      nlinarith only [a1,a2,aid]
    · have dq : 3 ∣ q := by rcases q36 with rfl|rfl <;> decide
      refine Or.inr ⟨r3,dq.trans dvd,?_⟩
      intro u hu dvu
      have quo : q ∣ 2*u := by
        obtain ⟨j,rfl⟩ := dvu
        rcases q36 with e|e <;> rw [e]
        · exact ⟨2*j,by ring⟩
        · exact ⟨j,by ring⟩
      have zero : 2 • (u : ZMod q)=0 := by
        rw [nsmul_eq_mul]
        simpa only [Nat.cast_mul,Nat.cast_ofNat] using (ZMod.natCast_eq_zero_iff _ _).mpr quo
      have div := addOrderOf_dvd_iff_nsmul_eq_zero.mpr zero
      have cap := Nat.le_of_dvd (by decide : 0<2) div
      exact (Nat.not_lt_of_ge cap) (ord _ (mem_image_of_mem _ hu))
  · left
    rw [not_nonempty_iff_eq_empty.mp hn]
    simp

end Erdos13ColumnModulo

end

section

/-! Reduction of modular complete-column constraints to an aperiodic cyclic group. -/
namespace Erdos13ColumnModulo
open Finset
open scoped Pointwise

theorem reduce_selected_columns {r a : ℕ} (K : Finset ℕ) (ha : 0 < a) (P : Finset ℕ) (hne : P.Nonempty)
    (excl : ∀ u ∈ P, ∀ j ∈ K, ∀ v : Fin r → ℕ,
      (∀ i,v i ∈ P) → ¬ (∑ i,v i) ≡ j*u [MOD a]) :
    ∃ q : ℕ, ∃ _hq : 0 < q, q ∣ a ∧
      let R := P.image (fun x : ℕ => (x : ZMod q))
      (r • R).addStab = {0} ∧
        ∀ x ∈ R, ∀ j ∈ K, j • x ∉ r • R := by
  classical
  let : NeZero a := ⟨ha.ne'⟩
  let B := P.image (fun x : ℕ => (x : ZMod a))
  let S := r • B
  have hB : B.Nonempty := hne.image _
  have hS : S.Nonempty := hB.nsmul
  let H := AddAction.stabilizer (ZMod a) (S : Set (ZMod a))
  let Q := ZMod a ⧸ H
  let π := QuotientAddGroup.mk' H
  let g : Q := π 1
  let q := Nat.card Q
  let : Fintype Q := Fintype.ofFinite _
  have hq : 0 < q := by dsimp [q]; rw [Nat.card_eq_fintype_card]; exact Fintype.card_pos
  let : NeZero q := ⟨hq.ne'⟩
  have generates (x : Q) : x ∈ AddSubgroup.zmultiples g := by
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective H x
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨(z.val : ℤ),?_⟩
    rw [natCast_zsmul]
    change z.val • π 1 = π z
    rw [←map_nsmul]
    simp [nsmul_eq_mul]
  let e : ZMod q ≃+ Q := zmodAddEquivOfGenerator generates rfl
  let p := e.symm.toAddMonoidHom.comp π
  have p1 : p 1 = 1 := zmodAddEquivOfGenerator_symm_apply_generator generates rfl
  have pn (x : ℕ) : p (x : ZMod a) = (x : ZMod q) := by
    calc
      p (x : ZMod a) = p (x • (1 : ZMod a)) := by simp [nsmul_eq_mul]
      _ = x • p 1 := map_nsmul _ _ _
      _ = x := by rw [p1]; simp [nsmul_eq_mul]
  have surj : Function.Surjective p := e.symm.surjective.comp (QuotientAddGroup.mk'_surjective H)
  have fix (z : ZMod a) : z ∈ H ↔ z +ᵥ S = S := by
    change z ∈ AddAction.stabilizer (ZMod a) (S : Set (ZMod a)) ↔ _
    rw [AddAction.mem_stabilizer_iff,←Finset.coe_vadd_finset,Finset.coe_inj]
  have sat (z : ZMod a) : p z ∈ S.image p ↔ z ∈ S := by
    refine ⟨?_,mem_image_of_mem _⟩
    intro hz
    obtain ⟨y,hy,hEq⟩ := mem_image.mp hz
    have eqπ : π y = π z := e.symm.injective hEq
    have hmem : z-y ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp eqπ.symm
    have hfix := vadd_mem_vadd_finset (a := z-y) hy
    rw [(fix _).mp hmem] at hfix
    simpa [vadd_eq_add] using hfix
  let R := P.image (fun x : ℕ => (x : ZMod q))
  have mapped : S.image p = r • R := by
    have m : B.image p = R := by
      dsimp [B,R]
      rw [image_image]
      exact image_congr fun x _ => pn x
    exact (Finset.image_nsmul p B r).trans (congrArg (r • ·) m)
  refine ⟨q,hq,?_,?_,?_⟩
  · apply (ZMod.natCast_eq_zero_iff _ _).mp
    simp [←pn a]
  · ext w
    change w ∈ (r • R).addStab ↔ _
    rw [←mapped,mem_singleton,mem_addStab (hS.image _)]
    constructor
    · obtain ⟨z,rfl⟩ := surj w
      intro hw
      have hz : z ∈ H := (fix _).mpr (by
        apply Finset.eq_of_subset_of_card_le _ (by simp)
        intro v hv
        obtain ⟨y,hy,rfl⟩ := mem_vadd_finset.mp hv
        apply (sat _).mp
        have h := vadd_mem_vadd_finset (a:=p z) (mem_image_of_mem p hy)
        rw [hw] at h
        simpa [vadd_eq_add] using h)
      have hzero := (QuotientAddGroup.eq_zero_iff z).mpr hz
      change e.symm (π z)=0
      rw [show π z =0 from hzero,map_zero]
    · rintro rfl
      simp
  · intro x hx j hj hjx
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
    change j • (u : ZMod q) ∈ r • R at hjx
    rw [←mapped,←pn u,←map_nsmul,sat] at hjx
    obtain ⟨v,hv⟩ := Finset.mem_nsmul.mp hjx
    have rep (i : Fin r) : ∃ w ∈ P, (w : ZMod a)=(v i:ZMod a) := mem_image.mp (v i).property
    choose b hb be using rep
    apply excl u hu j hj b hb
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    rw [Nat.cast_sum,Nat.cast_mul]
    simpa [List.sum_ofFn,be,nsmul_eq_mul] using hv

end Erdos13ColumnModulo

end

section

/-! Density of residue classes supporting all but a bounded number of lifts. -/
namespace Erdos13ColumnModulo
open Finset FullColumns
open scoped Pointwise

lemma near_cyclic {r q g l : ℕ} [NeZero q] (hr : 3≤r) (hl : 3≤l)
    (cop : g.Coprime q) (large : 2*r<g) (R : Finset (ZMod q)) (hn : R.Nonempty)
    (aper : (r • R).addStab={0})
    (short : ∀ x∈R, (r-1+l) • x ∉ r • R)
    (long : ∀ x∈R, ∀ j∈Ioc (2*r) (l*g), j • x ∉ r • R) :
    (r+1)*R.card≤q := by
  classical
  let S := r • R
  have grow : r*R.card ≤ S.card+(r-1) := by
    have h := Finset.card_nsmul_bound (r:=r) (by omega) R hn
    rwa [aper,card_singleton,Nat.mul_one] at h
  have pair (T : Finset (ZMod q)) (disj : Disjoint S T) : S.card+T.card ≤ q := by
    have c := (S∪T).card_le_univ
    rwa [card_union_of_disjoint disj,ZMod.card] at c
  let L := (l+1)*r
  have cover : 2*r+L ≤ l*g := by
    have a := Nat.mul_le_mul_left l large.le
    have b := Nat.mul_le_mul_right r hl
    dsimp [L]
    nlinarith only [a,b]
  obtain ⟨x,hx⟩ := hn
  have order : L < addOrderOf x := by
    by_contra! h
    let d := addOrderOf x
    have pos : 0<d := addOrderOf_pos _
    let z := r/d+1
    have rem := Nat.mod_add_div r d
    have lt := Nat.mod_lt r pos
    rw [mul_comm d _] at rem
    have c : r < z*d ∧ z*d ≤ r+d := by dsimp [z];rw [Nat.add_mul,Nat.one_mul];omega
    have bad := long x hx (r+z*d) (mem_Ioc.mpr ⟨by omega,by change d≤L at h;omega⟩)
    have zero : (z*d) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (dvd_mul_left _ _)
    rw [add_nsmul,zero,add_zero] at bad
    exact bad (nsmul_mem_nsmul hx)
  let f (i : ℕ) := (2*r+1+i) • x
  have arc := pair ((range L).image f) (disjoint_left.mpr (by
    intro y hy h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have := mem_range.mp hi
    exact long x hx _ (mem_Ioc.mpr ⟨by omega,by omega⟩) hy))
  have cf : ((range L).image f).card=L := by
    rw [card_image_of_injOn,card_range]
    intro i hi j hj h
    have e := (nsmul_eq_nsmul_iff_modEq.mp h).add_left_cancel' (2*r+1)
    simpa [Nat.ModEq,Nat.mod_eq_of_lt ((mem_range.mp hi).trans order),
      Nat.mod_eq_of_lt ((mem_range.mp hj).trans order)] using e
  rw [cf] at arc
  by_cases small : R.card+(r-1)≤L
  · rw [Nat.add_mul,Nat.one_mul]
    omega
  let U := R.image (fun x => g • x)
  let D := R.image (fun x => l • x)
  let V := D.image (fun x => g • x)
  have inj := coprime_scalar cop
  have cu : U.card=R.card := card_image_of_injective _ inj
  have cv : V.card=D.card := card_image_of_injective _ inj
  have dis : Disjoint U V := disjoint_left.mpr (by
    intro z hu hv
    obtain ⟨x,hx,e⟩ := mem_image.mp hu
    obtain ⟨w,hw,ew⟩ := mem_image.mp hv
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hw
    have eq : x=l • y := inj (e.trans ew.symm)
    apply short y hy
    have h := Finset.add_mem_add (nsmul_mem_nsmul (n:=r-1) hy) hx
    rwa [eq,←add_nsmul,←succ_nsmul,Nat.sub_add_cancel (show 1≤r by omega)] at h)
  have pack := pair (U∪V) (disjoint_left.mpr (by
    intro z hz hu
    rcases mem_union.mp hu with hu|hv
    · obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
      have inc := Nat.mul_le_mul_right g (show 1≤l by omega)
      exact long x hx _ (mem_Ioc.mpr ⟨large,by omega⟩) hz
    · obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hw
      rw [←mul_nsmul] at hz
      have inc := Nat.mul_le_mul_right g (show 1≤l by omega)
      exact long x hx _ (mem_Ioc.mpr ⟨by omega,le_rfl⟩) hz))
  rw [card_union_of_disjoint dis,cu,cv] at pack
  have sc := scalar_card l (by omega) R
  change R.card ≤ l*D.card at sc
  have many : r-1 ≤ D.card := by
    by_contra! no
    have m := Nat.mul_le_mul_left l (show D.card+1≤r by omega)
    dsimp [L] at small
    nlinarith only [m,sc,lt_of_not_ge small,Nat.sub_le r 1,Nat.zero_le l]
  rw [Nat.add_mul,Nat.one_mul]
  omega

def NearGood (r t a : ℕ) := ∃ g : ℕ, 2*r<g ∧ (2*t+7)*g*(2*t+3) ≤ r*r ∧ g.Coprime a

theorem near_columns {r t a : ℕ} (hr : 12*(t+2)≤r) (ha : 0<a) (good : NearGood r t a)
    (A P : Finset ℕ) (free : Free r A) (off : ∀ u ∈ P, 0<u ∧ u<a)
    (holes : ∀ u ∈ P, (Icc 1 (r+t) \ columnHeights A a (r+t) u).card ≤ t) :
    (r+1)*P.card ≤ a := by
  classical
  obtain ⟨g,gg,cap,cop⟩ := good
  by_cases hn : P.Nonempty
  · let l := 2*t+7
    let K := insert (r-1+l) (Ioc (2*r) (l*g))
    obtain ⟨q,hq,dvd,aper,ex⟩ := reduce_selected_columns K (r:=r) ha P hn (by
      intro u hu j hj f hf
      apply near_multipliers hr ha A P free off holes ?_ u hu f hf
      rcases mem_insert.mp hj with e|mem
      · left; dsimp [l] at e; omega
      · obtain ⟨below,above⟩ := mem_Ioc.mp mem
        exact Or.inr ⟨below.le,(Nat.mul_le_mul_right (2*t+3) above).trans cap⟩)
    let : NeZero q := ⟨hq.ne'⟩
    let R := P.image (fun x : ℕ => (x : ZMod q))
    have s := near_cyclic (r:=r) (l:=l) (by omega) (by dsimp [l];omega) (cop.of_dvd_right dvd)
      gg R (hn.image _) aper (fun x hx => ex x hx _ (mem_insert_self _ _))
      (fun x hx j hj => ex x hx j (mem_insert_of_mem hj))
    let T := P.image (·%q)
    have im : R.image ZMod.val=T := by
      dsimp [R,T]
      rw [image_image]
      exact image_congr (fun x _ => ZMod.val_natCast _ _)
    have dense : T.card=R.card := im ▸ card_image_of_injective _ (ZMod.val_injective q)
    have dec : a/q*q = a := Nat.div_mul_cancel dvd
    have cover := Erdos13HalfOccupied.count_by_period q (a/q) 0 (Nat.zero_le _) T 0 P (by
      intro x hx
      have := (off x hx).2
      simpa only [Nat.zero_add,Nat.add_zero,dec,mem_Ico,Nat.zero_le,true_and] using this)
      (fun x hx => mem_image_of_mem _ hx)
    simp only [min_eq_left (Nat.zero_le _),Nat.add_zero,dense] at cover
    have c₁ := Nat.mul_le_mul_left (r+1) cover
    have c₂ := Nat.mul_le_mul_left (a/q) s
    nlinarith only [c₁,c₂,dec]
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp

end Erdos13ColumnModulo

end

section

/-! Separated unit scalars pack many disjoint dilates outside an iterated sumset. -/
namespace Erdos13ColumnModulo
open Finset FullColumns
open scoped Pointwise

lemma histogram_cyclic_packing {q r T g : ℕ} [NeZero q] (hr : 80 ≤ r) (loT : 3 ≤ T) (hiT : T ≤ r)
    (glo : r+40 ≤ g) (ghi : g ≤ 2*r) (unit : g.Coprime q) (I : Finset ℕ)
    (bounds : ∀ i ∈ I, 1 ≤ i ∧ i ≤ T ∧ i.Coprime q)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i < j → i+40 ≤ j) (R : Finset (ZMod q)) (hn : R.Nonempty)
    (aper : (r • R).addStab={0})
    (excl : ∀ x ∈ R, ∀ k ∈ Icc (r+40) (2*r*T), k • x ∉ r • R) :
    (2*r+I.card)*R.card ≤ 2*q := by
  classical
  let S := r • R
  have grow : r*R.card ≤ S.card+(r-1) := by
    have h := Finset.card_nsmul_bound (r:=r) (by omega) R hn
    rwa [aper,card_singleton,Nat.mul_one] at h
  have large := Nat.mul_le_mul_left (2*r) loT
  have pair (U : Finset (ZMod q)) (disj : Disjoint S U) : S.card+U.card ≤ q := by
    have h := (S∪U).card_le_univ
    rwa [card_union_of_disjoint disj,ZMod.card] at h
  obtain ⟨x,hx⟩ := hn
  have order : 2*r < addOrderOf x := by
    by_contra! small
    let d := addOrderOf x
    have hd : 0 < d := addOrderOf_pos _
    let z := 39/d+1
    have rem := Nat.mod_add_div 39 d
    rw [mul_comm d _] at rem
    have mlt := Nat.mod_lt 39 hd
    have b : 40 ≤ z*d ∧ z*d ≤ 39+d := by dsimp [z]; rw [Nat.add_mul,Nat.one_mul];omega
    have forbidden := excl x hx (r+z*d) (mem_Icc.mpr ⟨by omega,by change d ≤ 2*r at small; omega⟩)
    have zero : (z*d) • x=0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp (dvd_mul_left _ _)
    rw [add_nsmul,zero,add_zero] at forbidden
    exact forbidden (nsmul_mem_nsmul hx)
  let arc (j : ℕ) := (r+40+j) • x
  have outside := pair ((range (2*r)).image arc) (disjoint_left.mpr (by
    intro z hz h
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    have b := mem_range.mp hi
    exact excl x hx _ (mem_Icc.mpr ⟨by omega,by omega⟩) hz))
  have arcs : ((range (2*r)).image arc).card=2*r := by
    rw [card_image_of_injOn,card_range]
    intro i hi j hj he
    have e := (nsmul_eq_nsmul_iff_modEq.mp he).add_left_cancel' (r+40)
    simpa [Nat.ModEq,Nat.mod_eq_of_lt ((mem_range.mp hi).trans order),
      Nat.mod_eq_of_lt ((mem_range.mp hj).trans order)] using e
  rw [arcs] at outside
  let f (p : ℕ × ZMod q) := g • (p.1 • p.2)
  have separate (i j : ℕ) (a b : ZMod q) (hi : i ∈ I) (hj : j ∈ I) (ij : i < j)
      (ha : a ∈ R) (hb : b ∈ R) (e : f (i,a)=f (j,b)) : False := by
    have eq : i • a=j • b := coprime_scalar unit e
    have ir := (bounds i hi).2.1.trans hiT
    have gap := sep i hi j hj ij
    have jr := (bounds j hj).2.1.trans hiT
    have kbound : r+40 ≤ r-i+j ∧ r-i+j ≤ 2*r*T := by omega
    apply excl b hb (r-i+j) (mem_Icc.mpr kbound)
    have h := add_mem_add (nsmul_mem_nsmul (n:=r-i) hb) (nsmul_mem_nsmul (n:=i) ha)
    rw [eq,←add_nsmul,←add_nsmul,Nat.sub_add_cancel ir] at h
    exact h
  have inject : Set.InjOn f (I ×ˢ R : Finset (ℕ × ZMod q)) := by
    rintro ⟨i,a⟩ hi ⟨j,b⟩ hj e
    obtain ⟨hI,ha⟩ := mem_product.mp hi
    obtain ⟨hJ,hb⟩ := mem_product.mp hj
    rcases lt_trichotomy i j with ij|rfl|ji
    · exact False.elim (separate i j a b hI hJ ij ha hb e)
    · exact Prod.ext rfl (coprime_scalar (bounds i hI).2.2 (coprime_scalar unit e))
    · exact False.elim (separate j i b a hJ hI ji hb ha e.symm)
  have pack := pair ((I ×ˢ R).image f) (disjoint_left.mpr (by
    intro z hz he
    obtain ⟨⟨i,b⟩,hp,rfl⟩ := mem_image.mp he
    obtain ⟨hi,hb⟩ := mem_product.mp hp
    obtain ⟨pos,bt,_⟩ := bounds i hi
    have l := Nat.mul_le_mul_left g pos
    have u := Nat.mul_le_mul ghi bt
    have bad := excl b hb (g*i) (mem_Icc.mpr ⟨by omega,u⟩)
    rw [Nat.mul_comm g i,mul_nsmul] at bad
    exact bad hz))
  rw [card_image_of_injOn inject,card_product] at pack
  rw [Nat.add_mul]
  nlinarith only [grow,pack,outside,Nat.sub_le r 1]

/-- Lift the aperiodic quotient estimate through the complete residue periods
in the integer interval [0,a). -/
lemma histogram_columns {a r T g : ℕ} (ha : 0 < a) (hr : 80 ≤ r) (loT : 3 ≤ T) (hiT : T ≤ r)
    (glo : r+40 ≤ g) (ghi : g ≤ 2*r) (unit : g.Coprime a) (I : Finset ℕ)
    (bounds : ∀ i ∈ I, 1 ≤ i ∧ i ≤ T ∧ i.Coprime a)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i < j → i+40 ≤ j) (P : Finset ℕ) (off : ∀ u ∈ P, u < a)
    (excl : ∀ u ∈ P, ∀ k ∈ Icc (r+40) (2*r*T), ∀ v : Fin r→ℕ, (∀ i,v i ∈ P) →
      ¬ (∑ i,v i) ≡ k*u [MOD a]) : (2*r+I.card)*P.card ≤ 2*a := by
  classical
  by_cases hn : P.Nonempty
  · obtain ⟨q,hq,dvd,aper,ex⟩ := reduce_selected_columns (Icc (r+40) (2*r*T)) ha P hn excl
    let : NeZero q := ⟨hq.ne'⟩
    let R := P.image (fun x : ℕ => (x : ZMod q))
    have pack := histogram_cyclic_packing hr loT hiT glo ghi (unit.of_dvd_right dvd) I
      (fun i hi => ⟨(bounds i hi).1,(bounds i hi).2.1,(bounds i hi).2.2.of_dvd_right dvd⟩)
      sep R (hn.image _) aper ex
    let D := P.image (·%q)
    have im : R.image ZMod.val=D := by
      dsimp [R,D]
      rw [image_image]
      exact image_congr (fun x _ => ZMod.val_natCast _ _)
    have dense : D.card=R.card := im ▸ card_image_of_injective _ (ZMod.val_injective q)
    have dec : a/q*q=a := Nat.div_mul_cancel dvd
    have cover := Erdos13HalfOccupied.count_by_period q (a/q) 0 (Nat.zero_le _) D 0 P (by
      intro x hx
      simpa only [Nat.zero_add,Nat.add_zero,dec,mem_Ico,Nat.zero_le,true_and] using off x hx)
      (fun x hx => mem_image_of_mem _ hx)
    simp only [min_eq_left (Nat.zero_le _),Nat.add_zero,dense] at cover
    have c₁ := Nat.mul_le_mul_left (2*r+I.card) cover
    have c₂ := Nat.mul_le_mul_left (a/q) pack
    nlinarith only [c₁,c₂,dec]
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp

end Erdos13ColumnModulo

end

section

namespace OMA.Erdos13UpperShell
open Finset

/-- Each represented residue can occur in at most k places in a window of length k*d. -/
theorem count_residues_in_blocks {B : Finset ℕ} {a d k : ℕ} (hd : 0 < d)
    (hs : B ⊆ Ioc a (a + k*d)) :
    B.card ≤ k * (B.image (fun x => x % d)).card := by
  classical
  let f := fun x : ℕ => ((x - (a+1)) / d, x % d)
  have bound : B.card ≤ ((range k) ×ˢ (B.image fun x => x % d)).card := by
    apply card_le_card_of_injOn f
    · intro x hx
      have h := mem_Ioc.mp (hs hx)
      exact mem_product.mpr ⟨mem_range.mpr ((Nat.div_lt_iff_lt_mul hd).mpr (by omega)),
        mem_image_of_mem _ hx⟩
    · intro x hx y hy he
      have hx' := mem_Ioc.mp (hs hx)
      have hy' := mem_Ioc.mp (hs hy)
      have eqD : (x - (a+1))/d = (y - (a+1))/d := congrArg Prod.fst he
      have eqM : x ≡ y [MOD d] := congrArg Prod.snd he
      have eqP : (x-(a+1)) % d = (y-(a+1)) % d :=
        Nat.ModEq.sub_right (by omega) (by omega) eqM
      have eqT := Nat.mod_add_div (x-(a+1)) d
      rw [eqD, eqP, Nat.mod_add_div] at eqT
      omega
  simpa [card_product] using bound

theorem upper_shell_tail {r a d N : ℕ} (hr : 2 ≤ r) (ha : N ≤ 2*a)
    (han : a ≤ N) (hd : 16*r < d) (hdvd : d ∣ a) (B : Finset ℕ)
    (hs : B ⊆ Ioc a N) (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (r+1)*B.card ≤ N + 16*r := by
  have hpos : 0 < d := by omega
  obtain ⟨h, hh⟩ := hdvd
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  by_cases hsmall : h ≤ 16
  · have cover : B ⊆ Ioc a (a+h*d) := by
      intro x hx
      have hb := mem_Ioc.mp (hs hx)
      rw [mul_comm h d, ← hh]
      exact mem_Ioc.mpr ⟨hb.1, by omega⟩
    have cnt : B.card ≤ h*R.card := count_residues_in_blocks hpos cover
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left h hres'
    have hrh := Nat.mul_le_mul_right r hsmall
    have len := card_le_card hs
    rw [Nat.card_Ioc] at len
    have len' : B.card + a ≤ N := by omega
    nlinarith only [hc, hk, hrh, len', hh]
  · let q := (N-a)/d
    have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
    have len : N-a < (q+1)*d := by
      rw [Nat.add_mul, Nat.one_mul]
      have := Nat.mod_add_div (N-a) d
      have := Nat.mod_lt (N-a) hpos
      change N-a < (N-a)/d*d + d
      rw [Nat.mul_comm ((N-a)/d) d]
      omega
    have cnt : B.card ≤ (q+1)*R.card := by
      apply count_residues_in_blocks hpos
      intro x hx
      have hb := mem_Ioc.mp (hs hx)
      exact mem_Ioc.mpr ⟨hb.1, by omega⟩
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left (q+1) hres'
    have hqr := Nat.mul_le_mul_left q (show 16*r ≤ d by omega)
    have hdb := Nat.mul_le_mul_left d (show 16 ≤ h by omega)
    have hL : (N-a) + a = N := by omega
    have h2 := Nat.mul_le_mul_right B.card hr
    nlinarith only [hc, hk, hqr, hdb, hq, hh, hL, ha, han, h2, Nat.zero_le N, Nat.zero_le r]

/-- The only additive input is the cyclic quotient witness. -/
theorem upper_shell_of_quotients {r N : ℕ} (hr : 2 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ N ≤ 2*a ∧ a ≤ N)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2) :
    (r+1)*A.card ≤ N + (r+1)*(16*r+1) + 16*r := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, (sub a ha).1, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ 16*r
  have low : E.card ≤ 16*r := by
    have hc : E.card ≤ (Icc 1 (16*r)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => 16*r < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have hB : B ⊆ Ioc a N := by
      intro x hx
      have hx' := mem_filter.mp hx
      exact mem_Ioc.mpr ⟨hx'.2, (sub x hx'.1).2.2⟩
    have ht := upper_shell_tail hr (sub a hf.1).2.1 (sub a hf.1).2.2 hf.2
      (div a hf.1) B hB (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ 16*r
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ 16*r+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r]

end OMA.Erdos13UpperShell

end

section

/-! Widen the upper half by permitting a small incomplete second period. -/

namespace OMA.Erdos13UpperShell
open Finset

theorem wide_shell_tail {r a d N : ℕ} (hr : 3 ≤ r)
    (cut : 4*r*N ≤ 8*r*a + N)
    (han : a ≤ N) (hd : 16*r < d) (hdvd : d ∣ a) (B : Finset ℕ)
    (hs : B ⊆ Ioc a N) (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (r+1)*B.card ≤ N + 32*r := by
  by_cases half : N ≤ 2*a
  · have bound := upper_shell_tail (by omega) half han hd hdvd B hs hres
    omega
  have eEq : N - 2*a + 2*a = N := by omega
  have eScaled := congrArg (fun n : ℕ => 4*r*n) eEq
  have eBudget : 4*r*(N-2*a) ≤ N := by nlinarith only [eScaled, cut]
  have eLo := Nat.mul_le_mul_right (N-2*a) (show 1 ≤ r by omega)
  have eSimple : 4*(N-2*a) ≤ N := by nlinarith only [eBudget,eLo]
  have lengthBound : 8*(N-a) ≤ 5*N := by omega
  have hpos : 0 < d := by omega
  obtain ⟨h, hh⟩ := hdvd
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  by_cases hsmall : h ≤ 16
  · let P := B.filter fun x => x ≤ 2*a
    let Q := B.filter fun x => ¬ x ≤ 2*a
    have cover : P ⊆ Ioc a (a+h*d) := by
      intro x hx
      have hp := mem_filter.mp hx
      rw [mul_comm h d, ← hh]
      exact mem_Ioc.mpr ⟨(mem_Ioc.mp (hs hp.1)).1, by omega⟩
    have hp := count_residues_in_blocks hpos cover
    have hIm : (P.image (fun x => x%d)) ⊆ R := image_subset_image (filter_subset _ _)
    have cnt := hp.trans (Nat.mul_le_mul_left h (card_le_card hIm))
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left h hres'
    have hrh := Nat.mul_le_mul_right r hsmall
    have hQ : Q ⊆ Ioc (2*a) N := by
      intro x hx
      have hq := mem_filter.mp hx
      exact mem_Ioc.mpr ⟨lt_of_not_ge hq.2, (mem_Ioc.mp (hs hq.1)).2⟩
    have hQc := card_le_card hQ
    rw [Nat.card_Ioc] at hQc
    have hQr := Nat.mul_le_mul_left r hQc
    have partition : P.card+Q.card = B.card := B.card_filter_add_card_filter_not _
    have hSum := congrArg (fun s : ℕ => r*s) partition
    have h3 := Nat.mul_le_mul_right B.card hr
    have ha2 : 2*a ≤ N := by omega
    nlinarith only [hc, hk, hrh, hh, hQr, hSum, h3, ha2, eBudget, Nat.zero_le r]
  · let q := (N-a)/d
    have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
    have len : N-a < (q+1)*d := by
      rw [Nat.add_mul, Nat.one_mul]
      have := Nat.mod_add_div (N-a) d
      have := Nat.mod_lt (N-a) hpos
      change N-a < (N-a)/d*d + d
      rw [Nat.mul_comm ((N-a)/d) d]
      omega
    have cnt : B.card ≤ (q+1)*R.card := by
      apply count_residues_in_blocks hpos
      intro x hx
      have hb := mem_Ioc.mp (hs hx)
      exact mem_Ioc.mpr ⟨hb.1, by omega⟩
    have hc := Nat.mul_le_mul_left r cnt
    have hk := Nat.mul_le_mul_left (q+1) hres'
    have hqr := Nat.mul_le_mul_left q (show 16*r ≤ d by omega)
    have hdb := Nat.mul_le_mul_left d (show 16 ≤ h by omega)
    have h3 := Nat.mul_le_mul_right B.card hr
    nlinarith only [hc, hk, hqr, hdb, hq, hh, han, lengthBound, h3, Nat.zero_le N, Nat.zero_le r]

theorem wide_shell_of_quotients {r N : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ 4*r*N ≤ 8*r*a + N ∧ a ≤ N)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2) :
    (r+1)*A.card ≤ N + (r+1)*(16*r+1) + 32*r := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, (sub a ha).1, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ 16*r
  have low : E.card ≤ 16*r := by
    have hc : E.card ≤ (Icc 1 (16*r)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => 16*r < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have hB : B ⊆ Ioc a N := by
      intro x hx
      have hx' := mem_filter.mp hx
      exact mem_Ioc.mpr ⟨hx'.2, (sub x hx'.1).2.2⟩
    have ht := wide_shell_tail hr (sub a hf.1).2.1 (sub a hf.1).2.2 hf.2
      (div a hf.1) B hB (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ 16*r
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ 16*r+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r]

end OMA.Erdos13UpperShell

end

section

/-! # Cyclic quotient witnesses for admissible sets and their residue fibers -/
namespace OMA.Erdos13Cyclic

open Finset

theorem witness_of_free {r : ℕ} (hr : 2 ≤ r) {A : Finset ℕ} (free : FullColumns.Free r A)
    (pos : ∀ a ∈ A, 0 < a) (a : ℕ) (ha : a ∈ A)
    (hne : (A.filter fun x => a < x).Nonempty) :
    ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2 := by
  obtain ⟨d, hd, hdvd, hno, hsize⟩ := quotient_witness hr (pos a ha) _ hne
    (fun b hb => free a ha b (fun i => (mem_filter.mp (hb i)).1) (fun i => (mem_filter.mp (hb i)).2))
  exact ⟨d, hd, hdvd, fun b hb hlt => hno b (mem_filter.mpr ⟨hb,hlt⟩), hsize⟩

theorem count_residue_fibers (B : Finset ℕ) {a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hdvd : d ∣ a) :
    (B.image (fun x => x % a)).card ≤ (a / d) * (B.image (fun x => x % d)).card := by
  classical
  let R := B.image (fun x => x % a)
  let T := B.image (fun x => x % d)
  have bound : R.card ≤ ((range (a / d)) ×ˢ T).card := by
    apply card_le_card_of_injOn (fun x => (x / d, x % d))
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
      refine mem_product.mpr ⟨mem_range.mpr ?_, ?_⟩
      · apply (Nat.div_lt_iff_lt_mul hd).mpr
        rw [Nat.div_mul_cancel hdvd]
        exact Nat.mod_lt _ ha
      · change y % a % d ∈ T
        rw [Nat.mod_mod_of_dvd _ hdvd]
        exact mem_image_of_mem _ hy
    · intro x hx y hy hp
      have h1 : x / d = y / d := congrArg Prod.fst hp
      have h2 : x % d = y % d := congrArg Prod.snd hp
      have eq := Nat.mod_add_div x d
      rwa [h1, h2, Nat.mod_add_div, eq_comm] at eq
  simpa [card_product] using bound

theorem residue_bound_of_quotient (B : Finset ℕ) {r a d : ℕ} (ha : 0 < a) (hd : 0 < d)
    (hdvd : d ∣ a) (hres : r * (B.image (fun x => x % d)).card ≤ d + r - 2) :
    r * (B.image (fun x => x % a)).card ≤ a + (a / d) * r := by
  have basic := count_residue_fibers B ha hd hdvd
  calc r * (B.image (fun x => x % a)).card ≤ r * ((a/d) * (B.image (fun x => x % d)).card) :=
         Nat.mul_le_mul_left _ basic
       _ = (a/d) * (r * (B.image (fun x => x % d)).card) := by ring
       _ ≤ (a/d) * (d+r) := Nat.mul_le_mul_left _ (by omega)
       _ = _ := by rw [Nat.mul_add, Nat.div_mul_cancel hdvd]

theorem wide_shell {r N : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ 4*r*N ≤ 8*r*a + N ∧ a ≤ N) (free : FullColumns.Free r A) :
    (r+1)*A.card ≤ N + (r+1)*(16*r+1) + 32*r :=
  OMA.Erdos13UpperShell.wide_shell_of_quotients hr A sub
    (witness_of_free (by omega) free (fun a ha => (sub a ha).1))

end OMA.Erdos13Cyclic

end

section

/-! Counting occupied heights with disjoint bands of rows of bounded deficit. -/
namespace Erdos13ColumnModulo
open Finset FullColumns

def missingHeights (B : Finset ℕ) (a J u : ℕ) := (Icc 1 J \ columnHeights B a J u).card

def histogramRows (B : Finset ℕ) (a J h : ℕ) :=
  (B.image (·%a)).filter (fun u=>missingHeights B a J u≤h)

def histogramUnits (a T L : ℕ) : Prop :=
  ∃ I : Finset ℕ, (∀ i ∈ I, 1 ≤ i ∧ i ≤ T ∧ Nat.Coprime i a) ∧
    (∀ i ∈ I, ∀ j ∈ I, i < j → i + 40 ≤ j) ∧ T ≤ L * I.card

lemma histogram_card {a J : ℕ} (B : Finset ℕ)
    (layers : ∀ b∈B, b/a∈Icc 1 J) :
    B.card ≤ ∑ h∈range J,(histogramRows B a J h).card := by
  classical
  let R := B.image (·%a)
  let H := columnHeights B a J
  have fiber (u : ℕ) : (B.filter (fun b=>b%a=u)).card ≤ (H u).card := by
    apply card_le_card_of_injOn (fun b=>b/a)
    · intro x hx
      obtain ⟨xb,res⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨layers x xb,by simpa [←res,Nat.div_add_mod'] using xb⟩
    · intro x hx y hy he
      have h₁ := (mem_filter.mp hx).2
      have h₂ := (mem_filter.mp hy).2
      change x/a=y/a at he
      have e₁ := Nat.div_add_mod x a
      have e₂ := Nat.div_add_mod y a
      rw [he,h₁] at e₁
      rw [h₂] at e₂
      omega
  have row (u : ℕ) : (H u).card = ∑ h∈range J,if missingHeights B a J u≤h then 1 else 0 := by
    rw [←sum_filter]
    have filt : (range J).filter (fun h=>missingHeights B a J u≤h) = Ico (missingHeights B a J u) J := by
      ext h
      simp [and_comm]
    rw [filt]
    have inc : H u⊆Icc 1 J := filter_subset _ _
    have cap := card_le_card inc
    simp only [Nat.card_Icc,Nat.add_sub_cancel] at cap
    simp [missingHeights,card_sdiff_of_subset inc,H] at *
    omega
  rw [card_eq_sum_card_image (fun x=>x%a) B]
  calc _ ≤ ∑ u∈R, (H u).card := sum_le_sum (fun u _=>fiber u)
       _ = _ := by
         simp_rw [row]
         rw [sum_comm]
         apply sum_congr rfl
         intro h _
         rw [←sum_filter]
         simp [histogramRows,R]

lemma histogram_group {r J a h T L g : ℕ} (hr : 128≤r) (span : r≤J) (ha : 0<a)
    (sq : r≤T*T) (Tlo : 4≤T) (Thi : T≤r) (scale : 16*(h+1)*T≤J)
    (glo : r+40≤g) (ghi : g≤2*r) (unit : g.Coprime a) (units : histogramUnits a T L)
    (B : Finset ℕ) (free : Free r B) (off : ∀ u∈B.image (·%a), 0<u ∧ u<a) :
    6*r*r*L*(histogramRows B a J h).card+a*T ≤ 6*r*L*a := by
  classical
  let P := histogramRows B a J h
  have offs (u) (hu : u∈P) := off _ (mem_filter.mp hu).1
  obtain ⟨I,bounds,sep,sz⟩ := units
  have scale₁ := Nat.mul_le_mul_left (h+1) Tlo
  have scale₂ := Nat.mul_le_mul_left h Tlo
  have sparse : 8*h+8≤J/8 := (Nat.le_div_iff_mul_le (by decide)).mpr (by nlinarith only [scale,scale₁])
  have cheap : h*T ≤ J/8-h := by
    have hh : h*T+h≤J/8 := (Nat.le_div_iff_mul_le (by decide)).mpr (by nlinarith only [scale,scale₂])
    omega
  have budget : r*h*h≤(J/8-h)*(J/8) := by
    have h₁ := Nat.mul_le_mul_right (h*h) sq
    have h₂ := Nat.mul_le_mul cheap (cheap.trans (Nat.sub_le _ _))
    nlinarith only [h₁,h₂]
  have est := histogram_columns ha (by omega : 80≤r) (by omega : 3≤T) Thi glo ghi unit
    I bounds sep P (fun u hu => (offs u hu).2) (by
      intro u hu k hk v hv
      have lim := Nat.mul_le_mul_left (8*(h+1)) (mem_Icc.mp hk).2
      have upper := Nat.mul_le_mul_left r scale
      exact histogram_dilate hr span ha (mem_Icc.mp hk).1 (by nlinarith only [lim,upper])
        sparse budget B P free offs (fun _ hx=>(mem_filter.mp hx).2) u hu v hv)
  have sub : I ⊆ Icc 1 T := fun i hi => mem_Icc.mpr ⟨(bounds i hi).1,(bounds i hi).2.1⟩
  have szI : I.card≤r := (card_le_card sub).trans (by simpa using Thi)
  have cost : 6*r*r*P.card+a*I.card≤6*r*a := by
    by_cases big : a≤3*r*P.card
    · have one := Nat.mul_le_mul_left (3*r) est
      have two := Nat.mul_le_mul_right I.card big
      nlinarith only [one,two]
    · have one := Nat.mul_le_mul_left (2*r) (le_of_lt (lt_of_not_ge big))
      have two := Nat.mul_le_mul_left a szI
      nlinarith only [one,two,Nat.zero_le (r*a)]
  have d₁ := Nat.mul_le_mul_left L cost
  have d₂ := Nat.mul_le_mul_left a sz
  change 6*r*r*L*P.card+a*T≤_
  nlinarith only [d₁,d₂]

end Erdos13ColumnModulo

end

section

/-! Dyadic counting at a low pivot. The scale products are exact integers. -/
namespace Erdos13ColumnModulo
open Finset FullColumns

def histogramGood (a r U L : ℕ) : Prop :=
  (∃ g : ℕ, r+40 ≤ g ∧ g ≤ 2*r ∧ g.Coprime a) ∧
    ∀ T : ℕ, U ≤ T → T ≤ r → histogramUnits a T L

lemma dyadic_sum_bound {K s W : ℕ} (f : ℕ → ℕ)
    (band : ∀ j<K, s*W  ≤  ∑ h∈Ico (s*2^j) (s*2^(j+1)),f h) :
    K*(s*W)  ≤  ∑ h∈Ico s (s*2^K), f h := by
  have step (k : ℕ) (hk : k ≤ K) : k*(s*W)  ≤  ∑ h∈Ico s (s*2^k),f h := by
    induction k with
    | zero => simp
    | succ k ih =>
      have p : s ≤ s*2^k := Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)
      have q : s*2^k ≤ s*2^(k+1) := by rw [pow_succ,←Nat.mul_assoc];omega
      rw [←Finset.sum_Ico_consecutive f p q, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) (band k (by omega))
  exact step K le_rfl

/-- At a good pivot with at least r layers, the number of strictly larger
elements gains an entire additional unit in the denominator. -/
theorem histogram_tail {r a d J U L K : ℕ} (hr : 128 ≤ r) (ha : 0<a) (span : r ≤ J)
    (Lpos : 0<L) (many : 3072*L ≤ K) (Ulo : 4 ≤ U) (Usq : r ≤ U*U)
    (scope : 128*(U*2^K) ≤ r) (good : histogramGood a r U L)
    (hd : r*r ≤ d) (dvd : d∣a) (B : Finset ℕ) (free : Free r B)
    (off : ∀ u∈B.image (·%a), 0<u ∧ u<a)
    (layers : ∀ b∈B, b/a∈Icc 1 J) (quot : r*(B.image (·%d)).card ≤ d+r-2) :
    (r+2)*B.card ≤ J*a := by
  classical
  let W := U*2^K
  let s := J/(64*W)
  have Wpos : 0<W := mul_pos (by omega) (pow_pos (by decide) _)
  have upper : 64*W*s ≤ J := Nat.mul_div_le _ _
  have spos : 1 ≤ s := (Nat.le_div_iff_mul_le (by positivity)).mpr (by change 128*W ≤ r at scope;omega)
  have lower : J ≤ 128*s*W := by
    have de := Nat.mod_add_div J (64*W)
    have re := Nat.mod_lt J (by positivity : 0<64*W)
    change J%(64*W)+(64*W)*s=J at de
    have big := Nat.mul_le_mul_left W spos
    nlinarith only [de,re,big]
  let e := a/d
  have dpos : 0<d := (Nat.mul_pos (by omega : 0<r) (by omega)).trans_le hd
  have res := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha dpos dvd quot
  let n (h : ℕ) := (histogramRows B a J h).card
  let m := 6*r*L*(a+r*e)
  let g (h : ℕ) := m-6*r*r*L*n h
  have budget (h) : 6*r*r*L*n h ≤ m := by
    have le := Nat.mul_le_mul_left r (card_filter_le (B.image (·%a)) (fun u=>missingHeights B a J u ≤ h))
    have main := Nat.mul_le_mul_left (6*r*L) (le.trans res)
    change 6*r*r*L*(histogramRows B a J h).card ≤ 6*r*L*(a+r*(a/d))
    dsimp [histogramRows]
    nlinarith only [main]
  obtain ⟨⟨k,kl,kh,unit⟩,units⟩ := good
  have band (j) (hj : j<K) :
      s*(a*W)  ≤  ∑ h∈Ico (s*2^j) (s*2^(j+1)),g h := by
    let T := U*2^(K-j)
    let z := s*2^j
    have eq : z*T=s*W := by
      dsimp [z,T,W]
      rw [show s*2^j*(U*2^(K-j))=s*U*(2^j*2^(K-j)) by ring,←pow_add]
      rw [Nat.add_sub_of_le (by omega : j ≤ K)]
      ring
    have TU : U ≤ T := Nat.le_mul_of_pos_right _ (pow_pos (by decide) _)
    have TW : T ≤ W := Nat.mul_le_mul_left U (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
    have limited : T ≤ r := by change 128*W ≤ r at scope;omega
    have single (h) (hit : h∈Ico (s*2^j) (s*2^(j+1))) : a*T ≤ g h := by
      have htop := (mem_Ico.mp hit).2
      rw [pow_succ,←Nat.mul_assoc] at htop
      have lim := Nat.mul_le_mul_right T (show h+1 ≤ 2*z by dsimp [z];omega)
      have grp := histogram_group hr span ha (Usq.trans (Nat.mul_le_mul TU TU))
        (Ulo.trans TU) limited (by nlinarith only [lim,eq,upper] : 16*(h+1)*T ≤ J)
        kl kh unit (units T TU limited) B free off
      have ext := Nat.mul_le_mul_left (6*r*L) (Nat.le_add_right a (r*e))
      change 6*r*r*L*n h+a*T ≤ 6*r*L*a at grp
      change a*T ≤ m-6*r*r*L*n h
      change 6*r*L*a ≤ m at ext
      omega
    have sum := sum_le_sum single
    have width : (Ico (s*2^j) (s*2^(j+1))).card = z := by rw [Nat.card_Ico,pow_succ,←Nat.mul_assoc];dsimp [z];omega
    simp only [sum_const,width,nsmul_eq_mul] at sum
    nlinarith only [sum,congrArg (a*·) eq]
  have savings := dyadic_sum_bound (W:=a*W) g band
  have sub : Ico s (s*2^K)⊆range J := by
    intro h hh
    have low := (mem_Ico.mp hh).2
    have p₁ : 2^K ≤ W := Nat.le_mul_of_pos_left _ (by omega)
    have p₂ := Nat.mul_le_mul_left s p₁
    apply mem_range.mpr
    nlinarith only [low,p₂,upper]
  have all := savings.trans (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _=>Nat.zero_le _))
  have total : (∑ h∈range J,g h)+6*r*r*L*(∑ h∈range J,n h)=J*m := by
    rw [Finset.mul_sum,←sum_add_distrib]
    calc _ = ∑ _h∈range J,m := sum_congr rfl (fun h _=>Nat.sub_add_cancel (budget h))
         _ = _ := by simp
  have count := Nat.mul_le_mul_left (6*r*r*L) (histogram_card B layers)
  change 6*r*r*L*B.card  ≤  6*r*r*L*(∑ h∈range J,n h) at count
  have saved := Nat.mul_le_mul many (Nat.mul_le_mul_left a lower)
  have alloc : 3072*L*(a*J)  ≤  128*(K*(s*(a*W))) := by nlinarith only [saved]
  have base : 6*r*r*L*B.card + 24*L*(J*a)  ≤  J*m := by nlinarith only [all,alloc,total,count]
  have exactD : e*d=a := Nat.div_mul_cancel dvd
  have small := Nat.mul_le_mul_left e hd
  have extras := Nat.mul_le_mul_left (J*6*L) (small.trans exactD.le)
  dsimp [m] at base
  have raw : 6*L*(r*r*B.card+3*(J*a)) ≤ 6*L*(r*(J*a)) := by nlinarith only [base,extras]
  have result := Nat.le_of_mul_le_mul_left raw (by positivity)
  have c₂ := Nat.mul_le_mul_left (r+2) result
  have rem : 0 ≤ r*J*a := Nat.zero_le _
  have last : (r*r)*((r+2)*B.card) ≤ (r*r)*(J*a) := by
    nlinarith only [c₂,rem,Nat.zero_le (J*a)]
  exact Nat.le_of_mul_le_mul_left last (by positivity)

end Erdos13ColumnModulo

end

section

namespace ThirdStrip

open Finset FullColumns

/-- Two occupied lifts also give freeness on a slightly wider shell, by
integrality of the multiplier. -/
lemma free_wider {r a X : ℕ} {A P S : Finset ℕ}
    (both : ∀ u ∈ P, ∀ k ∈ Icc 1 2, k*a+u ∈ A) (free : Free r A)
    (sub : S ⊆ P) (band : ∀ u ∈ S, 0 < u ∧ u ≤ X ∧ r*X < (2*r+1)*u) :
    Free r S := by
  intro u hu b hb hlt hd
  obtain ⟨k, hk⟩ := hd
  have lower : r*u ≤ ∑ i, b i := by
    simpa using sum_le_sum (s := (univ : Finset (Fin r))) (f := fun _ => u)
      (g := b) (fun i _ => (hlt i).le)
  have upper : ∑ i, b i ≤ r*X := by
    simpa using sum_le_sum (s := (univ : Finset (Fin r))) (f := b)
      (g := fun _ => X) (fun i _ => (band _ (hb i)).2.1)
  have eq : ∑ i, b i = k*u := by simpa [Nat.mul_comm] using hk
  rw [eq] at lower upper
  have bound : k ≤ r*2 := by
    have hlt' : k*u < (2*r+1)*u := lt_of_le_of_lt upper (band _ hu).2.2
    have hh : k < 2*r+1 := Nat.lt_of_mul_lt_mul_right hlt'
    omega
  exact lift_forbidden (by decide : 0 < 2) both free (sub hu) b
    (fun i => sub (hb i)) hlt (Nat.le_of_mul_le_mul_right lower (band _ hu).1) bound eq

/-- Iterating the shell estimate bounds the number of doubly occupied offsets.
At r=3, the strictly wider shell pays for the per-shell additive error. -/
lemma complete_half {r a C D : ℕ} (hr : 3 ≤ r) {A P : Finset ℕ}
    (both : ∀ u ∈ P, ∀ k ∈ Icc 1 2, k*a+u ∈ A) (free : Free r A)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      Free r S → (r+1)*S.card ≤ X+C)
    (within : ∀ u ∈ P, u ≤ D) :
    2*P.card ≤ D + (24*(C+1)+2) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have inductionBound (X : ℕ) : 2*(F X).card ≤ X + (24*(C+1)+2) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ 24*(C+1)
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have hh := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        omega
      let t := if r = 3 then 11*X/24 else X/2
      have ht : t < X := by dsimp [t]; split_ifs <;> omega
      let S := (F X).filter fun x => t < x
      have data (x : ℕ) (hx : x ∈ S) :
          0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X ∧ r*X < (2*r+1)*x := by
        obtain ⟨hFx, htx⟩ := mem_filter.mp hx
        have hxX := (mem_filter.mp hFx).2
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true] at htx
          constructor
          · omega
          constructor
          · omega
          constructor
          · exact hxX
          · omega
        · simp only [t, if_neg h3] at htx
          have hX : X ≤ 2*x := by omega
          have hh := Nat.mul_le_mul_left r hX
          have hxpos : 0 < x := by omega
          exact ⟨hxpos, by nlinarith only [hh, Nat.zero_le X], hxX, by nlinarith only [hh, hxpos]⟩
      have incl : S ⊆ P := (filter_subset _ _).trans (filter_subset _ _)
      have count := wide X S (fun x hx => ⟨(data x hx).1, (data x hx).2.1, (data x hx).2.2.1⟩)
        (free_wider both free incl (fun x hx => ⟨(data x hx).1,(data x hx).2.2⟩))
      have balance : 2*S.card + t ≤ X := by
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true]
          omega
        · simp only [t, if_neg h3]
          have hc := Nat.mul_le_mul_right S.card (show 5 ≤ r+1 by omega)
          omega
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have eq : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F, mem_filter]
        constructor
        · rintro ⟨⟨hxP, _⟩, hxt⟩
          exact ⟨hxP, by omega⟩
        · rintro ⟨hxP, hxt⟩
          exact ⟨⟨hxP, by omega⟩, by omega⟩
      rw [eq] at part
      change S.card + (F t).card = (F X).card at part
      have tail := ih t ht
      omega
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using inductionBound D

/-- Combine the two independent upper bounds on the final partial period. -/
lemma two_layers {r N a E K R P B : ℕ} (hr : 1 ≤ r) (layers : 2*a ≤ N)
    (res : r*R ≤ a+E) (duplicates : P ≤ R) (half : 2*P ≤ N-2*a+K)
    (count : B ≤ R+P) : (r+1)*B ≤ N+2*E+K := by
  have single : B ≤ 2*R := by omega
  have more := Nat.mul_le_mul_left (r-1) single
  have ident : r-1+1=r := by omega
  have iB := congrArg (fun j : ℕ => j*B) ident
  have iR := congrArg (fun j : ℕ => j*(2*R)) ident
  have dec := Nat.sub_add_cancel layers
  nlinarith only [more, iB, iR, dec, res, count, half]


/-- A tail spanning at most two complete residue layers satisfies the target
bound as soon as its image modulo the divisor obeys the cyclic sumset bound. -/
lemma strip_tail {r a N E C : ℕ} {A B : Finset ℕ} (hr : 3 ≤ r) (ha : 0 < a)
    (hain : a ∈ A) (lo : 2*a ≤ N) (hi : N ≤ 3*a) (subA : B ⊆ A)
    (sub : B ⊆ Ioc a N) (free : FullColumns.Free r A)
    (res : r*(B.image (·%a)).card ≤ a+E)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      FullColumns.Free r S → (r+1)*S.card ≤ X+C) :
    (r+1)*B.card ≤ N+2*E+(24*(C+1)+2) := by
  classical
  let P := FullColumns.complete B a 2
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 2) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u : ℕ) (hu : u ∈ P) : u ≤ N-2*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu 2 (by decide)))).2
    omega
  have half := complete_half hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free wide bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 2 := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < 3*a := by
      by_contra! hbr
      have eq : b = 3*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have count : B.card ≤ (B.image (·%a)).card + P.card := by
    simpa [P] using FullColumns.card_bound (B := B) (by decide : 0 < 2) layers
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  exact two_layers (by omega) lo res (card_le_card subR) half count

end ThirdStrip

end

section

/-! A cardinal bound in the top two thirds of the interval. -/
namespace OMA.Erdos13UpperShell
open Finset FullColumns

lemma third_large_stabilizer {r a d N : ℕ} (hr : 3 ≤ r) (ha : N ≤ 3*a)
    (han : a ≤ N) (hd : 64*r < d) (large : 64 < a/d)
    (B : Finset ℕ) (hs : B ⊆ Ioc a N)
    (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (r+1)*B.card ≤ N + 32*r := by
  have hpos : 0 < d := by omega
  have hD := (Nat.mul_le_mul_right d (show 64 ≤ a/d by omega)).trans (Nat.div_mul_le_self _ _)
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  have lengthBound : 3*(N-a) ≤ 2*N := by omega
  let q := (N-a)/d
  have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
  have len : N-a < (q+1)*d := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.mod_add_div (N-a) d
    have := Nat.mod_lt (N-a) hpos
    change N-a < (N-a)/d*d + d
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have cnt : B.card ≤ (q+1)*R.card := by
    apply count_residues_in_blocks hpos
    intro x hx
    have hb := mem_Ioc.mp (hs hx)
    exact mem_Ioc.mpr ⟨hb.1, by omega⟩
  have hc := Nat.mul_le_mul_left r cnt
  have hk := Nat.mul_le_mul_left (q+1) hres'
  have hqr := Nat.mul_le_mul_left q (show 64*r ≤ d by omega)

  have h3 := Nat.mul_le_mul_right B.card hr
  nlinarith only [hc, hk, hqr, hD, hq, han, lengthBound, h3, Nat.zero_le N, Nat.zero_le r]

lemma select_large_quotient {r N L K : ℕ} (A : Finset ℕ)
    (positive : ∀ a ∈ A, 0 < a)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2)
    (tail : ∀ a ∈ A, ∀ d : ℕ, L < d → d ∣ a →
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 →
      (r+1)*(A.filter fun x => a<x).card ≤ N+K) :
    (r+1)*A.card ≤ N + K + (r+1)*(L+1) := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, positive a ha, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ L
  have low : E.card ≤ L := by
    have hc : E.card ≤ (Icc 1 (L)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => L < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have ht : (r+1)*B.card ≤ N+K := tail a hf.1 (f a) hf.2 (div a hf.1) (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ L
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ L+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r, Nat.zero_le K]

/-- Every admissible set in the top two thirds satisfies the desired bound. -/
theorem bound_on_third_shell {r N : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ N ≤ 3*a ∧ a ≤ N) (free : Free r A) :
    (r+1)*A.card ≤ N + (128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1) := by
  classical
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  apply select_large_quotient A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd hres
  let B := A.filter fun x => a < x
  change (r+1)*B.card ≤ _
  have hB : B ⊆ Ioc a N := by
    intro x hx
    have hf := mem_filter.mp hx
    exact mem_Ioc.mpr ⟨hf.2,(sub x hf.1).2.2⟩
  have apos := pos a hain
  have ha := (sub a hain).2.1
  have han := (sub a hain).2.2
  by_cases upper : N ≤ 2*a
  · have := upper_shell_tail (by omega : 2≤r) upper han (by omega : 16*r<d) hdvd B hB hres
    omega
  by_cases large : 64 < a/d
  · have := third_large_stabilizer hr ha han hd large B hB hres
    omega
  · have reduced := OMA.Erdos13Cyclic.residue_bound_of_quotient B apos (by omega : 0<d) hdvd hres
    have hR := reduced.trans (Nat.add_le_add_left (Nat.mul_le_mul_right r (show a/d≤64 by omega)) a)
    have w (X : ℕ) (S : Finset ℕ)
        (hs : ∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) (hf : Free r S) :
        (r+1)*S.card ≤ X+((r+1)*(16*r+1)+32*r) := by
      simpa only [Nat.add_assoc] using OMA.Erdos13Cyclic.wide_shell hr S hs hf
    have hb := ThirdStrip.strip_tail hr apos hain (by omega : 2*a ≤ N) ha
      (show B ⊆ A by exact filter_subset _ _) hB free hR w
    omega

end OMA.Erdos13UpperShell

end

section

/-! Strict savings for the sparse terminal interval. -/
namespace OMA.Erdos13UpperShell
open Finset FullColumns ThirdStrip

lemma complete_strict {r a C D : ℕ} (hr : 3 ≤ r) {A P : Finset ℕ}
    (both : ∀ u ∈ P, ∀ k ∈ Icc 1 2, k*a+u ∈ A) (free : Free r A)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      Free r S → (r+1)*S.card ≤ X+C)
    (within : ∀ u ∈ P, u ≤ D) :
    25*P.card ≤ 12*D + 25*(100*(C+1)+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have inductionBound (X : ℕ) : 25*(F X).card ≤ 12*X + 25*(100*(C+1)+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ 100*(C+1)
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have hh := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        omega
      let t := if r = 3 then 11*X/24 else X/2
      have ht : t < X := by dsimp [t]; split_ifs <;> omega
      let S := (F X).filter fun x => t < x
      have data (x : ℕ) (hx : x ∈ S) :
          0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X ∧ r*X < (2*r+1)*x := by
        obtain ⟨hFx, htx⟩ := mem_filter.mp hx
        have hxX := (mem_filter.mp hFx).2
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true] at htx
          constructor
          · omega
          constructor
          · omega
          constructor
          · exact hxX
          · omega
        · simp only [t, if_neg h3] at htx
          have hX : X ≤ 2*x := by omega
          have hh := Nat.mul_le_mul_left r hX
          have hxpos : 0 < x := by omega
          exact ⟨hxpos, by nlinarith only [hh, Nat.zero_le X], hxX, by nlinarith only [hh, hxpos]⟩
      have incl : S ⊆ P := (filter_subset _ _).trans (filter_subset _ _)
      have count := wide X S (fun x hx => ⟨(data x hx).1, (data x hx).2.1, (data x hx).2.2.1⟩)
        (free_wider both free incl (fun x hx => ⟨(data x hx).1,(data x hx).2.2⟩))
      have balance : 25*S.card + 12*t ≤ 12*X := by
        by_cases h3 : r = 3
        · subst r
          simp only [t, if_true]
          omega
        · simp only [t, if_neg h3]
          have hc := Nat.mul_le_mul_right S.card (show 5 ≤ r+1 by omega)
          omega
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have eq : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F, mem_filter]
        constructor
        · rintro ⟨⟨hxP, _⟩, hxt⟩
          exact ⟨hxP, by omega⟩
        · rintro ⟨hxP, hxt⟩
          exact ⟨⟨hxP, by omega⟩, by omega⟩
      rw [eq] at part
      change S.card + (F t).card = (F X).card at part
      have tail := ih t ht
      omega
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using inductionBound D

lemma strip_strict_tail {r a N E C : ℕ} {A B : Finset ℕ} (hr : 3 ≤ r) (ha : 0 < a)
    (hain : a ∈ A) (lo : 2*a ≤ N) (hi : N ≤ 3*a) (subA : B ⊆ A)
    (sub : B ⊆ Ioc a N) (free : FullColumns.Free r A)
    (res : r*(B.image (·%a)).card ≤ a+E)
    (wide : ∀ (X : ℕ) (S : Finset ℕ), (∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) →
      FullColumns.Free r S → (r+1)*S.card ≤ X+C) :
    (24*(r+1)+1)*B.card ≤ 24*N+48*E+2*(25*(100*(C+1)+1)) := by
  classical
  let P := FullColumns.complete B a 2
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 2) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u : ℕ) (hu : u ∈ P) : u ≤ N-2*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu 2 (by decide)))).2
    omega
  have half := complete_strict hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free wide bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 2 := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < 3*a := by
      by_contra! hbr
      have eq : b = 3*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have count : B.card ≤ (B.image (·%a)).card + P.card := by
    simpa [P] using FullColumns.card_bound (B := B) (by decide : 0 < 2) layers
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  have single : B.card ≤ 2*(B.image (·%a)).card := by have := card_le_card subR; omega
  have enough : 25 ≤ 24*r := by omega
  have weighted := Nat.mul_le_mul_left (24*r-25) single
  have eq := Nat.sub_add_cancel enough
  have eqB := congrArg (fun n : ℕ => n*B.card) eq
  have eqR := congrArg (fun n : ℕ => n*(B.image (·%a)).card) eq
  have dec := Nat.sub_add_cancel lo
  nlinarith only [res, half, count, weighted, eqB, eqR, dec]

lemma third_large_strict {r a d N : ℕ} (hr : 3 ≤ r) (ha : N ≤ 3*a)
    (han : a ≤ N) (hd : 64*r < d) (large : 64 < a/d)
    (B : Finset ℕ) (hs : B ⊆ Ioc a N)
    (hres : r * (B.image (fun x => x%d)).card ≤ d + r - 2) :
    (24*(r+1)+1)*B.card ≤ 24*N+100*r := by
  have hpos : 0 < d := by omega
  have hD := (Nat.mul_le_mul_right d (show 64 ≤ a/d by omega)).trans (Nat.div_mul_le_self _ _)
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at hres
  have hres' : r*R.card ≤ d+r := by omega
  have lengthBound : 3*(N-a) ≤ 2*N := by omega
  let q := (N-a)/d
  have hq : q*d ≤ N-a := Nat.div_mul_le_self _ _
  have len : N-a < (q+1)*d := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.mod_add_div (N-a) d
    have := Nat.mod_lt (N-a) hpos
    change N-a < (N-a)/d*d + d
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have cnt : B.card ≤ (q+1)*R.card := by
    apply count_residues_in_blocks hpos
    intro x hx
    have hb := mem_Ioc.mp (hs hx)
    exact mem_Ioc.mpr ⟨hb.1, by omega⟩
  have hc := Nat.mul_le_mul_left r cnt
  have hk := Nat.mul_le_mul_left (q+1) hres'
  have hqr := Nat.mul_le_mul_left q (show 64*r ≤ d by omega)

  have h3 := Nat.mul_le_mul_right B.card hr
  nlinarith only [hc, hk, hqr, hD, hq, han, lengthBound, h3, Nat.zero_le N, Nat.zero_le r]

lemma select_large_scaled {r t N L K : ℕ} (A : Finset ℕ)
    (positive : ∀ a ∈ A, 0 < a)
    (witness : ∀ a ∈ A, (A.filter fun x => a < x).Nonempty →
      ∃ d : ℕ, 0 < d ∧ d ∣ a ∧ (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
        r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d + r - 2)
    (tail : ∀ a ∈ A, ∀ d : ℕ, L < d → d ∣ a →
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 →
      t*(A.filter fun x => a<x).card ≤ N+K) :
    t*A.card ≤ N + K + t*(L+1) := by
  classical
  have aw (a) (ha : a ∈ A) : ∃ d : ℕ, 0 < d ∧ d ∣ a ∧
      (∀ b ∈ A, a < b → ¬ d ∣ b) ∧
      r * ((A.filter fun x => a < x).image (fun x => x % d)).card ≤ d+r-2 := by
    by_cases ht : (A.filter fun x => a < x).Nonempty
    · exact witness a ha ht
    · rw [not_nonempty_iff_eq_empty] at ht
      refine ⟨a, positive a ha, dvd_refl _, ?_, by simp [ht]⟩
      intro b hb hlt
      have hmem : b ∈ (A.filter fun x => a < x) := mem_filter.mpr ⟨hb, hlt⟩
      simp [ht] at hmem
  choose! f pos div later size using aw
  let E := A.filter fun x => f x ≤ L
  have low : E.card ≤ L := by
    have hc : E.card ≤ (Icc 1 (L)).card := by
      apply card_le_card_of_injOn f
      · intro x hx
        have h := mem_filter.mp hx
        exact mem_Icc.mpr ⟨pos x h.1, h.2⟩
      · intro x hx y hy he
        have hxa := (mem_filter.mp hx).1
        have hya := (mem_filter.mp hy).1
        rcases lt_trichotomy x y with h | h | h
        · exact False.elim (later x hxa y hya h (he ▸ div y hya))
        · exact h
        · exact False.elim (later y hya x hxa h (he ▸ div x hxa))
    simpa using hc
  let G := A.filter fun x => L < f x
  by_cases non : G.Nonempty
  · let a := G.min' non
    have hag : a ∈ G := min'_mem _ _
    have hf := mem_filter.mp hag
    let B := A.filter fun x => a < x
    have ht : t*B.card ≤ N+K := tail a hf.1 (f a) hf.2 (div a hf.1) (size a hf.1)
    have cover : A ⊆ E ∪ insert a B := by
      intro x hx
      by_cases h : f x ≤ L
      · exact mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)
      · have hxg : x ∈ G := mem_filter.mpr ⟨hx, by omega⟩
        have hax : a ≤ x := min'_le _ _ hxg
        by_cases eq : x = a
        · exact mem_union_right _ (mem_insert.mpr (Or.inl eq))
        · exact mem_union_right _ (mem_insert.mpr (Or.inr (mem_filter.mpr ⟨hx, by omega⟩)))
    have cnt := (card_le_card cover).trans (card_union_le _ _)
    have ins := card_insert_le a B
    have hcard : A.card ≤ L+1+B.card := by omega
    have := Nat.mul_le_mul_left (r+1) hcard
    nlinarith only [this, ht]
  · have cover : A ⊆ E := by
      intro x hx
      apply mem_filter.mpr
      refine ⟨hx, ?_⟩
      by_contra! h
      exact non ⟨x,mem_filter.mpr ⟨hx,h⟩⟩
    have hc := Nat.mul_le_mul_left (r+1) ((card_le_card cover).trans low)
    nlinarith only [hc, Nat.zero_le N, Nat.zero_le r, Nat.zero_le K]



lemma sparse_upper_strict {r m a E : ℕ} (hr : 3 ≤ r) (A B : Finset ℕ)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a ((r+1)*m))
    (sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m)
    (num : r*B.card ≤ a+E) :
    (24*(r+1)+1)*B.card ≤ 24*((r+1)*m)+25*E := by
  classical
  let T := Ioc (r*m) ((r+1)*m) ∩ A
  change 2*T.card ≤ m at sparse
  by_cases low : a ≤ r*m
  · have incl : B ⊆ Ioc a (r*m) ∪ T := by
      intro x hx
      have hx' := mem_Ioc.mp (sub hx)
      by_cases h : x ≤ r*m
      · exact mem_union_left _ (mem_Ioc.mpr ⟨hx'.1,h⟩)
      · exact mem_union_right _ (mem_inter.mpr ⟨mem_Ioc.mpr ⟨by omega,hx'.2⟩,subA hx⟩)
    have bound := (card_le_card incl).trans (card_union_le _ _)
    rw [Nat.card_Ioc] at bound
    have delta := Nat.sub_add_cancel low
    have cap : (r+1)*B.card ≤ (r+1)*(m+E) := by
      nlinarith only [bound, delta, sparse, num, Nat.zero_le m, Nat.zero_le (r*E)]
    have sml : B.card ≤ m+E := Nat.le_of_mul_le_mul_left cap (by omega)
    nlinarith only [bound, delta, sparse, num, sml, Nat.zero_le m]
  · have incl : B ⊆ T := by
      intro x hx
      have hx' := mem_Ioc.mp (sub hx)
      exact mem_inter.mpr ⟨mem_Ioc.mpr ⟨by omega,hx'.2⟩,subA hx⟩
    have hB : 2*B.card ≤ m := (Nat.mul_le_mul_left 2 (card_le_card incl)).trans sparse
    have mul := Nat.mul_le_mul_left r hB
    nlinarith only [hB, mul, Nat.zero_le m, Nat.zero_le E]

theorem stability_third {r m : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : ∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ 3*a ∧ a ≤ (r+1)*m)
    (free : Free r A) (sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m) :
    (24*(r+1)+1)*A.card ≤ 24*((r+1)*m) +
      (3072*r + 2*(25*(100*((r+1)*(16*r+1)+32*r+1)+1))) +
      (24*(r+1)+1)*(64*r+1) := by
  classical
  let N := (r+1)*m
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  apply select_large_scaled A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd hres
  let B := A.filter fun x => a < x
  change (24*(r+1)+1)*B.card ≤ 24*N+_
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := by
    intro x hx
    have hf := mem_filter.mp hx
    exact mem_Ioc.mpr ⟨hf.2,(sub x hf.1).2.2⟩
  have apos := pos a hain
  have ha : N ≤ 3*a := (sub a hain).2.1
  have han : a ≤ N := (sub a hain).2.2
  by_cases large : 64 < a/d
  · have := third_large_strict hr ha han hd large B hB hres
    omega
  have reduced := OMA.Erdos13Cyclic.residue_bound_of_quotient B apos (by omega : 0<d) hdvd hres
  have hR := reduced.trans (Nat.add_le_add_left (Nat.mul_le_mul_right r (show a/d≤64 by omega)) a)
  by_cases upper : N ≤ 2*a
  · have cnt : B.card ≤ (B.image (fun x => x%a)).card := by
      have hI : B ⊆ Ioc a (a+1*a) := by
        intro x hx
        have hx' := mem_Ioc.mp (hB hx)
        exact mem_Ioc.mpr ⟨hx'.1, by omega⟩
      simpa only [Nat.one_mul] using count_residues_in_blocks apos hI
    have h := sparse_upper_strict hr A B hBA hB sparse ((Nat.mul_le_mul_left r cnt).trans hR)
    change (24*(r+1)+1)*B.card ≤ 24*N+25*(64*r) at h
    omega
  · have w (X : ℕ) (S : Finset ℕ)
        (hs : ∀ x ∈ S, 0 < x ∧ 4*r*X ≤ 8*r*x+X ∧ x ≤ X) (hf : Free r S) :
        (r+1)*S.card ≤ X+((r+1)*(16*r+1)+32*r) := by
      simpa only [Nat.add_assoc] using OMA.Erdos13Cyclic.wide_shell hr S hs hf
    have h := strip_strict_tail hr apos hain (by omega : 2*a ≤ N) ha hBA hB free hR w
    convert h using 1 <;> ring

end OMA.Erdos13UpperShell

end

section

/-! Induction on the number of complete residue layers. -/
namespace OMA.Erdos13ManyLayers
open Finset FullColumns

def Shell (r J C : ℕ) : Prop :=
  ∀ (N : ℕ) (A : Finset ℕ), (∀ a ∈ A, 0 < a ∧ N ≤ J*a ∧ a ≤ N) →
    Free r A → (r+1)*A.card ≤ N+C

lemma gap_factor {r J : ℕ} (hJ : 3 ≤ J) (hr : J < r) :
    J*J + (r+1) + 1 ≤ J*(r+1) := by
  have hr' : r-(J+1)+(J+1)=r := by omega
  have hJ' : J-1+1=J := by omega
  have h := congrArg (fun z : ℕ => J*z) hr'
  have h' := congrArg (fun z : ℕ => z*(r-(J+1))) hJ'
  nlinarith only [hJ, hr', h, h', Nat.zero_le ((J-1)*(r-(J+1)))]

lemma pay_shell {r J X C t b : ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (cap : (r+1)*b ≤ X+C) (round : J*t ≤ X) (big : J*J*C ≤ X) :
    J*b+t ≤ X := by
  have hcap := Nat.mul_le_mul_left (J*J) cap
  have hround := Nat.mul_le_mul_left (r+1) round
  have factor := Nat.mul_le_mul_right X (gap_factor hJ hr)
  have hcombine : J*(r+1)*(J*b+t) ≤ J*(r+1)*X := by
    nlinarith only [hcap, hround, factor, big]
  exact Nat.le_of_mul_le_mul_left hcombine (by positivity)

lemma complete_bound {r a J C D : ℕ} (hJ : 3 ≤ J) (hr : J < r) {A P : Finset ℕ}
    (allLifts : ∀ u ∈ P, ∀ k ∈ Icc 1 J, k*a+u ∈ A) (free : Free r A)
    (prev : Shell r J C) (within : ∀ u ∈ P, u ≤ D) :
    J*P.card ≤ D + J*(J*J*C+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have step (X : ℕ) : J*(F X).card ≤ X + J*(J*J*C+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ J*J*C
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        have := Nat.mul_le_mul_left J (show (F X).card ≤ J*J*C+1 by omega)
        omega
      let t := X/J
      have ht : t < X := Nat.div_lt_self (by omega) (by omega)
      let S := P.filter fun u => u ≤ X ∧ X < J*u
      have bound := prev X S (by
        intro x hx
        have h := (mem_filter.mp hx).2
        have hp : 0 < x := by
          by_contra! hz
          simp [show x=0 by omega] at h
        exact ⟨hp,h.2.le,h.1⟩) (free_shell (by omega : 0<J) allLifts free X)
      have envelope := pay_shell hJ hr bound (Nat.mul_div_le X J) (le_of_not_ge small)
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have hiff (x : ℕ) : t<x ↔ X<J*x := by
        dsimp [t]
        rw [Nat.div_lt_iff_lt_mul (by omega : 0<J), Nat.mul_comm]
      have eq₁ : ((F X).filter fun x => t<x) = S := by
        ext x
        simp only [F,S,mem_filter,hiff]
        tauto
      have eq₂ : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F,mem_filter]
        constructor
        · rintro ⟨⟨hx, _⟩, hs⟩
          exact ⟨hx, by omega⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨hx, by omega⟩, by omega⟩
      rw [eq₁,eq₂] at part
      have hi := ih t ht
      have hparts := congrArg (fun k => J*k) part
      change J*S.card + t ≤ X at envelope
      rw [Nat.mul_add] at hparts
      omega
  have h := step D
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using h

lemma layers_count {r J N a E K R P B : ℕ} (hJ : 1 ≤ J) (hr : J ≤ r+1)
    (lo : J*a ≤ N) (imageBound : r*R ≤ a+E) (fullSub : P ≤ R)
    (fullBound : J*P ≤ N-J*a+K) (count : B ≤ (J-1)*R+P) :
    (r+1)*B ≤ N + J*E + K := by
  have c := Nat.mul_le_mul_left (r+1) count
  have i := Nat.mul_le_mul_left J imageBound
  have p := Nat.mul_le_mul_left (r+1-J) fullSub
  have hj : J-1+1=J := by omega
  have ht : r+1-J+J=r+1 := by omega
  have idj := congrArg (fun k : ℕ => (r+1)*k*R) hj
  have idp := congrArg (fun k : ℕ => k*P) ht
  have idr := congrArg (fun k : ℕ => k*R) ht
  have dec := Nat.sub_add_cancel lo
  nlinarith only [c, i, p, fullBound, idj, idp, idr, dec]


lemma layer_tail {r J a N E C : ℕ} {A B : Finset ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (ha : 0 < a) (hain : a ∈ A) (lo : J*a ≤ N) (hi : N ≤ (J+1)*a)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a N) (free : Free r A)
    (imageBound : r*(B.image (·%a)).card ≤ a+E) (prev : Shell r J C) :
    (r+1)*B.card ≤ N+J*E+J*(J*J*C+1) := by
  classical
  let P := FullColumns.complete B a J
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 J) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u) (hu : u ∈ P) : u ≤ N-J*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu J (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    omega
  have last := complete_bound hJ hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free prev bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 J := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < (J+1)*a := by
      by_contra! hbr
      have eq : b = (J+1)*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  exact layers_count (by omega) (by omega) lo imageBound (card_le_card subR) last
    (FullColumns.card_bound (by omega : 0<J) layers)

lemma medium_quotient {r a d N : ℕ} (hr : 3 ≤ r) (han : a ≤ N) (shell : N ≤ r*a)
    (hd : 4*r*r*(r+1) < d) (large : 4*(r+1) < a/d)
    (B : Finset ℕ) (sub : B ⊆ Ioc a N)
    (quot : r * (B.image (fun x => x%d)).card ≤ d+r-2) :
    (r+1)*B.card ≤ N+r*(r+1) := by
  classical
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at quot
  let t := (N-a)/d
  have hdpos : 0 < d := by omega
  have hperiod : t*d ≤ N-a := Nat.div_mul_le_self _ _
  have dsmall := (Nat.mul_le_mul_right d large.le).trans (Nat.div_mul_le_self _ _)
  have hMul : t*(4*r*r*(r+1)) ≤ r*a := by
    exact (Nat.mul_le_mul_left t hd.le).trans (hperiod.trans (by omega))
  have htr : t*(4*r*(r+1)) ≤ a := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0<r)
    convert hMul using 1 <;> ring
  have len : N-a < (t+1)*d := by
    rw [Nat.succ_mul]
    have rem := Nat.mod_add_div (N-a) d
    have hrem := Nat.mod_lt (N-a) hdpos
    dsimp [t]
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have count : B.card ≤ (t+1)*R.card := by
    apply OMA.Erdos13UpperShell.count_residues_in_blocks hdpos
    intro x hx
    have h := mem_Ioc.mp (sub hx)
    exact mem_Ioc.mpr ⟨h.1, by omega⟩
  have hcount := Nat.mul_le_mul_left r count
  have qbound := Nat.mul_le_mul_left (t+1) (show r*R.card ≤ d+r by omega)
  have hbase : r*B.card ≤ N-a+d+t*r+r := by
    nlinarith only [hcount,qbound,hperiod]
  have L := Nat.mul_le_mul_left (r+1) hbase
  have smallSum : (r+1)*d+(r+1)*t*r ≤ a := by
    nlinarith only [htr,dsmall,Nat.zero_le ((r+1)*d), Nat.zero_le ((r+1)*t*r)]
  have hl : r*((r+1)*B.card) ≤ r*(N+(r+1)) := by
    have dec := congrArg (fun z : ℕ => (r+1)*z) (Nat.sub_add_cancel han)
    nlinarith only [L, dec, smallSum, shell]
  have bound := Nat.le_of_mul_le_mul_left hl (by omega : 0<r)
  have hr' := Nat.mul_le_mul_right (r+1) (show 1≤r by omega)
  omega

lemma next_shell {r J C : ℕ} (hJ : 3 ≤ J) (hr : J < r) (prev : Shell r J C) :
    ∃ K : ℕ, Shell r (J+1) K := by
  classical
  let L := 4*r*r*(r+1)
  let E := 4*(r+1)*r
  let K := C + r*(r+1) + J*E + J*(J*J*C+1)
  refine ⟨K + (r+1)*(L+1), ?_⟩
  intro N A sub free
  have pos (a : ℕ) (ha : a ∈ A) := (sub _ ha).1
  rw [← Nat.add_assoc N K]
  apply OMA.Erdos13UpperShell.select_large_quotient (L := L) A pos
    (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd hres
  let B := A.filter fun x => a < x
  change (r+1)*B.card ≤ N + K
  have hB : B ⊆ Ioc a N := by
    intro x hx
    have h := mem_filter.mp hx
    exact mem_Ioc.mpr ⟨h.2,(sub x h.1).2.2⟩
  have hFree : Free r B := fun x hx b hb => free _ (mem_filter.mp hx).1 b
    (fun i => (mem_filter.mp (hb i)).1)
  have ha := (sub a hain).1
  have hi := (sub a hain).2.1
  have han := (sub a hain).2.2
  by_cases earlier : N ≤ J*a
  · have h := prev N B (by
      intro x hx
      have hI := mem_Ioc.mp (hB hx)
      exact ⟨by omega, earlier.trans (Nat.mul_le_mul_left J hI.1.le), hI.2⟩) hFree
    dsimp [K]
    omega
  by_cases large : 4*(r+1) < a/d
  · have shell : N ≤ r*a := hi.trans (Nat.mul_le_mul_right a hr)
    have h := medium_quotient (r := r) (by omega) han shell hd large B hB hres
    dsimp [K]
    omega
  · have dpos : 0 < d := by dsimp [L] at hd; omega
    have fib := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha dpos hdvd hres
    have imageBound : r * (B.image (·%a)).card ≤ a+E :=
      fib.trans (Nat.add_le_add_left (Nat.mul_le_mul_right r (show a/d ≤ 4*(r+1) by omega)) a)
    have h := layer_tail hJ hr ha hain (by omega : J*a ≤ N) hi
      (show B ⊆ A by exact filter_subset _ _) hB free imageBound prev
    dsimp [K]
    omega

/-- The unrestricted estimate holds for every set supported above N/r. -/
theorem shell_to_arity (r : ℕ) (hr : 3 ≤ r) : ∃ C : ℕ, Shell r r C := by
  have go (j : ℕ) : j+3 ≤ r → ∃ C : ℕ, Shell r (j+3) C := by
    induction j with
    | zero =>
      intro _
      exact ⟨(128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1),
        fun N A h f => by simpa only [Nat.add_assoc] using
          OMA.Erdos13UpperShell.bound_on_third_shell hr A h f⟩
    | succ j ih =>
      intro h
      obtain ⟨C, old⟩ := ih (by omega)
      exact next_shell (by omega) (by omega) old
  simpa only [Nat.sub_add_cancel hr] using go (r-3) (by omega)

end OMA.Erdos13ManyLayers

end

section

/-! A strict saving for sparse terminal intervals with every element at least N/r. -/

namespace OMA.Erdos13ManyLayers
open Finset FullColumns OMA.Erdos13UpperShell

lemma gap_factor_strict {r J : ℕ} (hJ : 3 ≤ J) (hr : J < r) :
    (4*J+1)*J + 4*(r+1) + 1 ≤ 4*J*(r+1) := by
  have de : r-(J+1)+(J+1)=r := by omega
  have hj1 : J-1+1=J := by omega
  have e1 := congrArg (fun z : ℕ => J*z) de
  have e2 := congrArg (fun z : ℕ => z*(r-(J+1))) hj1
  nlinarith only [hJ,de,hj1,e1,e2,Nat.zero_le ((J-1)*(r-(J+1)))]

lemma pay_shell_strict {r J X C t b : ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (cap : (r+1)*b ≤ X+C) (round : J*t ≤ X) (big : J*(4*J+1)*C ≤ X) :
    (4*J+1)*b+4*t ≤ 4*X := by
  have hcap := Nat.mul_le_mul_left (J*(4*J+1)) cap
  have hround := Nat.mul_le_mul_left (4*(r+1)) round
  have factor := Nat.mul_le_mul_right X (gap_factor_strict hJ hr)
  have hcombine : J*(r+1)*((4*J+1)*b+4*t) ≤ J*(r+1)*(4*X) := by
    nlinarith only [hcap, hround, factor, big]
  exact Nat.le_of_mul_le_mul_left hcombine (by positivity)

lemma complete_bound_strict {r a J C D : ℕ} (hJ : 3 ≤ J) (hr : J < r) {A P : Finset ℕ}
    (allLifts : ∀ u ∈ P, ∀ k ∈ Icc 1 J, k*a+u ∈ A) (free : Free r A)
    (prev : Shell r J C) (within : ∀ u ∈ P, u ≤ D) :
    (4*J+1)*P.card ≤ 4*D + (4*J+1)*(J*(4*J+1)*C+1) := by
  classical
  let F (t : ℕ) := P.filter fun u => u ≤ t
  have step (X : ℕ) : (4*J+1)*(F X).card ≤ 4*X + (4*J+1)*(J*(4*J+1)*C+1) := by
    induction X using Nat.strong_induction_on with
    | h X ih =>
      by_cases small : X ≤ J*(4*J+1)*C
      · have incl : F X ⊆ range (X+1) := by
          intro x hx
          exact mem_range.mpr (by have := (mem_filter.mp hx).2; omega)
        have cc := card_le_card incl
        rw [card_range] at cc
        have := Nat.mul_le_mul_left (4*J+1) (show (F X).card ≤ J*(4*J+1)*C+1 by omega)
        omega
      let t := X/J
      have ht : t < X := Nat.div_lt_self (by omega) (by omega)
      let S := P.filter fun u => u ≤ X ∧ X < J*u
      have bound := prev X S (by
        intro x hx
        have h := (mem_filter.mp hx).2
        have hp : 0 < x := by
          by_contra! hz
          simp [show x=0 by omega] at h
        exact ⟨hp,h.2.le,h.1⟩) (free_shell (by omega : 0<J) allLifts free X)
      have envelope := pay_shell_strict hJ hr bound (Nat.mul_div_le X J) (le_of_not_ge small)
      have part := (F X).card_filter_add_card_filter_not (fun x => t < x)
      have hiff (x : ℕ) : t<x ↔ X<J*x := by
        dsimp [t]
        rw [Nat.div_lt_iff_lt_mul (by omega : 0<J), Nat.mul_comm]
      have eq₁ : ((F X).filter fun x => t<x) = S := by
        ext x
        simp only [F,S,mem_filter,hiff]
        tauto
      have eq₂ : ((F X).filter fun x => ¬t<x) = F t := by
        ext x
        simp only [F,mem_filter]
        constructor
        · rintro ⟨⟨hx, _⟩, hs⟩
          exact ⟨hx, by omega⟩
        · rintro ⟨hx, hs⟩
          exact ⟨⟨hx, by omega⟩, by omega⟩
      rw [eq₁,eq₂] at part
      have hi := ih t ht
      have hparts := congrArg (fun k => (4*J+1)*k) part
      change (4*J+1)*S.card + 4*t ≤ 4*X at envelope
      rw [Nat.mul_add] at hparts
      omega
  have h := step D
  have eq : F D = P := filter_eq_self.mpr within
  simpa only [eq] using h


lemma layers_count_strict {r J N a E K R P B : ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (lo : J*a ≤ N) (imageBound : r*R ≤ a+E) (fullSub : P ≤ R)
    (fullBound : (4*J+1)*P ≤ 4*(N-J*a)+K) (count : B ≤ (J-1)*R+P) :
    (4*J*(r+1)+1)*B ≤ 4*J*N+4*J*J*E+J*K := by
  have sub : J-1+1=J := by omega
  have subR := congrArg (fun k : ℕ => k*R) sub
  have single : B ≤ J*R := by nlinarith only [count,fullSub,subR]
  let H := 4*J*r
  let L := (4*J+1)*(J-1)
  have hL : L ≤ H := by
    have hjr := Nat.mul_le_mul_left (4*J) hr.le
    have hjj := congrArg (fun k : ℕ => (4*J+1)*k) sub
    dsimp [L,H]
    nlinarith only [hjr,hjj,Nat.zero_le J]
  have dec := Nat.sub_add_cancel lo
  have hdc := congrArg (fun n : ℕ => 4*J*n) dec
  have cb := Nat.mul_le_mul_left (J*(4*J+1)) count
  have fb := Nat.mul_le_mul_left J fullBound
  have rb := Nat.mul_le_mul_left (4*J*J) imageBound
  have mult := Nat.mul_le_mul_left (H-L) single
  have e := Nat.sub_add_cancel hL
  have eB := congrArg (fun n : ℕ => n*B) e
  have eR := congrArg (fun n : ℕ => n*J*R) e
  have sj := congrArg (fun k : ℕ => (4*J+1)*k*B) sub
  dsimp [H,L] at mult eB eR
  nlinarith only [cb,fb,rb,mult,eB,eR,sj,hdc]
lemma layer_tail_strict {r J a N E C : ℕ} {A B : Finset ℕ} (hJ : 3 ≤ J) (hr : J < r)
    (ha : 0 < a) (hain : a ∈ A) (lo : J*a ≤ N) (hi : N ≤ (J+1)*a)
    (subA : B ⊆ A) (sub : B ⊆ Ioc a N) (free : Free r A)
    (imageBound : r*(B.image (·%a)).card ≤ a+E) (prev : Shell r J C) :
    (4*J*(r+1)+1)*B.card ≤ 4*J*N+4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) := by
  classical
  let P := FullColumns.complete B a J
  have completeLift (u : ℕ) (hu : u ∈ P) (k : ℕ) (hk : k ∈ Icc 1 J) :
      k*a+u ∈ B := (mem_filter.mp hu).2 k hk
  have bounds (u) (hu : u ∈ P) : u ≤ N-J*a := by
    have := (mem_Ioc.mp (sub (completeLift u hu J (mem_Icc.mpr ⟨by omega,le_rfl⟩)))).2
    omega
  have last := complete_bound_strict hJ hr
    (fun u hu k hk => subA (completeLift u hu k hk)) free prev bounds
  have layers (b : ℕ) (hb : b ∈ B) : b / a ∈ Icc 1 J := by
    have mem := mem_Ioc.mp (sub hb)
    have strict : b < (J+1)*a := by
      by_contra! hbr
      have eq : b = (J+1)*a := by omega
      have dv : a ∣ b := eq ▸ dvd_mul_left _ _
      have hsum : a ∣ ∑ _i : Fin r, b := by
        simpa using dv.trans (dvd_mul_left b r)
      exact free a hain (fun _ => b) (fun _ => subA hb) (fun _ => mem.1) hsum
    refine mem_Icc.mpr ⟨Nat.div_pos mem.1.le ha, ?_⟩
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul ha).mpr strict)
  have subR : P ⊆ B.image (·%a) := filter_subset _ _
  exact layers_count_strict hJ hr lo imageBound (card_le_card subR) last
    (FullColumns.card_bound (by omega : 0<J) layers)

lemma medium_quotient_strict {r a d N : ℕ} (hr : 3 ≤ r) (han : a ≤ N) (shell : N ≤ r*a)
    (hd : 4*r*r*(r+1) < d) (large : 4*(r+1) < a/d)
    (B : Finset ℕ) (sub : B ⊆ Ioc a N)
    (quot : r * (B.image (fun x => x%d)).card ≤ d+r-2) :
    (2*r*r*(r+1)+1)*B.card ≤ 2*r*r*N+2*r*r*(r+1) := by
  classical
  let R := B.image (fun x => x%d)
  change r*R.card ≤ d+r-2 at quot
  let t := (N-a)/d
  have hdpos : 0 < d := by omega
  have hperiod : t*d ≤ N-a := Nat.div_mul_le_self _ _
  have dsmall := (Nat.mul_le_mul_right d large.le).trans (Nat.div_mul_le_self _ _)
  have hMul : t*(4*r*r*(r+1)) ≤ r*a := by
    exact (Nat.mul_le_mul_left t hd.le).trans (hperiod.trans (by omega))
  have htr : t*(4*r*(r+1)) ≤ a := by
    apply Nat.le_of_mul_le_mul_left _ (by omega : 0<r)
    convert hMul using 1 <;> ring
  have len : N-a < (t+1)*d := by
    rw [Nat.succ_mul]
    have rem := Nat.mod_add_div (N-a) d
    have hrem := Nat.mod_lt (N-a) hdpos
    dsimp [t]
    rw [Nat.mul_comm ((N-a)/d) d]
    omega
  have count : B.card ≤ (t+1)*R.card := by
    apply OMA.Erdos13UpperShell.count_residues_in_blocks hdpos
    intro x hx
    have h := mem_Ioc.mp (sub hx)
    exact mem_Ioc.mpr ⟨h.1, by omega⟩
  have hcount := Nat.mul_le_mul_left r count
  have qbound := Nat.mul_le_mul_left (t+1) (show r*R.card ≤ d+r by omega)
  have hbase : r*B.card ≤ N-a+d+t*r+r := by
    nlinarith only [hcount,qbound,hperiod]
  have L := Nat.mul_le_mul_left (r+1) hbase
  have dec := congrArg (fun z : ℕ => (r+1)*z) (Nat.sub_add_cancel han)
  have hl : 2*r*((r+1)*B.card)+a ≤ 2*r*N+2*r*(r+1) := by
    nlinarith only [L,dec,htr,dsmall,shell]
  have length := card_le_card sub
  rw [Nat.card_Ioc] at length
  have card : B.card ≤ r*a := by omega
  have scaled := Nat.mul_le_mul_left r hl
  nlinarith only [card,scaled]


lemma lift_gain {r M t N C D b : ℕ} (le : t ≤ M) (major : (r+1)*b ≤ N+C)
    (strict : (t*(r+1)+1)*b ≤ t*N+D) :
    (M*(r+1)+1)*b ≤ M*N+(D+M*C) := by
  have mult := Nat.mul_le_mul_left (M-t) major
  have h := Nat.sub_add_cancel le
  have hb := congrArg (fun k : ℕ => k*(r+1)*b) h
  have hn := congrArg (fun k : ℕ => k*N) h
  have hc := Nat.mul_le_mul_right C (Nat.sub_le M t)
  nlinarith only [mult,strict,hb,hn,hc]

/-- A uniform positive gap below the conjectured density when the top m
integers are at most half occupied and the set is supported above N/r. -/
theorem sparse_top_stability_scaled (r M : ℕ) (hr : 3 ≤ r) (base : 24 ≤ M)
    (medium : 2*r*r ≤ M) (layers : 4*r ≤ M) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ r*a ∧ a ≤ (r+1)*m) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (M*(r+1)+1)*A.card ≤ M*((r+1)*m)+K := by
  classical
  obtain ⟨C, prev⟩ := shell_to_arity r hr
  let D₃ := (3072*r + 2*(25*(100*((r+1)*(16*r+1)+32*r+1)+1))) +
    (24*(r+1)+1)*(64*r+1)
  let L := 4*r*r*(r+1)
  let E := 4*(r+1)*r
  let Dm := 2*r*r*(r+1)
  let Dj := 4*r*r*E+r*((4*r+1)*(r*(4*r+1)*C+1))
  let D := D₃+Dm+Dj
  refine ⟨D+M*C+(M*(r+1)+1)*(L+1), ?_⟩
  intro m A sub free sparse
  let N := (r+1)*m
  have pos (a) (ha : a ∈ A) := (sub a ha).1
  change (M*(r+1)+1)*A.card ≤ M*N+(D+M*C+(M*(r+1)+1)*(L+1))
  rw [← Nat.add_assoc (M*N)]
  apply select_large_scaled A pos (OMA.Erdos13Cyclic.witness_of_free (by omega) free pos)
  intro a hain d hd hdvd quot
  let B := A.filter fun x => a < x
  change (M*(r+1)+1)*B.card ≤ M*N+(D+M*C)
  have hBA : B ⊆ A := filter_subset _ _
  have hB : B ⊆ Ioc a N := fun x hx => mem_Ioc.mpr
    ⟨(mem_filter.mp hx).2,(sub x (hBA hx)).2.2⟩
  have freeB : Free r B := fun x hx b hb => free _ (hBA hx) b (fun i => hBA (hb i))
  have major := prev N B (fun x hx => sub x (hBA hx)) freeB
  have ha := pos a hain
  have han : a ≤ N := (sub a hain).2.2
  have span : N ≤ r*a := (sub a hain).2.1
  by_cases third : N ≤ 3*a
  · have sub3 (x) (hx : x ∈ B) : 0 < x ∧ N ≤ 3*x ∧ x ≤ N := by
      have h := mem_Ioc.mp (hB hx)
      exact ⟨pos x (hBA hx),by omega,h.2⟩
    have card := card_le_card (inter_subset_inter (Subset.rfl (s := Ioc (r*m) N)) hBA)
    have sp : 2*(Ioc (r*m) N ∩ B).card ≤ m := (Nat.mul_le_mul_left 2 card).trans sparse
    have strong : (24*(r+1)+1)*B.card ≤ 24*N+D₃ := by
      simpa only [N,D₃,Nat.add_assoc] using stability_third hr B sub3 freeB sp
    apply lift_gain base major
    exact strong.trans (Nat.add_le_add_left (by dsimp [D]; omega) _)
  by_cases big : 4*(r+1) < a/d
  · have strong := medium_quotient_strict hr han span hd big B hB quot
    apply lift_gain medium major
    exact strong.trans (Nat.add_le_add_left (by dsimp [D,Dm]; omega) _)
  · let J := (N-1)/a
    have hJ : 3 ≤ J := by
      apply (Nat.le_div_iff_mul_le ha).mpr
      omega
    have Jlt : J < r := by
      apply (Nat.div_lt_iff_lt_mul ha).mpr
      omega
    have hLo : J*a ≤ N := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
    have hi : N ≤ (J+1)*a := by
      have ex := Nat.mod_add_div (N-1) a
      have rem := Nat.mod_lt (N-1) ha
      change N ≤ ((N-1)/a+1)*a
      rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm ((N-1)/a) a]
      omega
    have dpos : 0 < d := by omega
    have fiber := OMA.Erdos13Cyclic.residue_bound_of_quotient B ha dpos hdvd quot
    have rB := fiber.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right r (show a/d ≤ 4*(r+1) by omega)) a)
    have prevJ : Shell r J C := by
      intro X S hS f
      exact prev X S (fun x hx => ⟨(hS x hx).1,(hS x hx).2.1.trans
        (Nat.mul_le_mul_right x Jlt.le),(hS x hx).2.2⟩) f
    have est := layer_tail_strict hJ Jlt ha hain hLo hi hBA hB free rB prevJ
    have leM := (Nat.mul_le_mul_left 4 Jlt.le).trans layers
    apply lift_gain leM major
    have num : 4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) ≤ Dj := by
      dsimp [Dj]
      gcongr <;> omega
    change (4*J*(r+1)+1)*B.card ≤ 4*J*N+4*J*J*E+J*((4*J+1)*(J*(4*J+1)*C+1)) at est
    dsimp [D]
    omega


/-- A uniform positive gap below the conjectured density when the top m
integers are at most half occupied and the set is supported above N/r. -/
theorem sparse_top_stability (r : ℕ) (hr : 3 ≤ r) :
    ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
      (∀ a ∈ A, 0 < a ∧ (r+1)*m ≤ r*a ∧ a ≤ (r+1)*m) → Free r A →
      2*(Ioc (r*m) ((r+1)*m) ∩ A).card ≤ m →
      (24*r*r*(r+1)+1)*A.card ≤ 24*r*r*((r+1)*m)+K := by
  apply sparse_top_stability_scaled
  · exact hr
  · nlinarith [Nat.mul_le_mul hr hr]
  · gcongr <;> decide
  · have h := Nat.mul_le_mul_right r (show 1≤r by omega)
    nlinarith only [h,Nat.zero_le (r*r)]

end OMA.Erdos13ManyLayers

end

section

namespace Erdos13HalfOccupied

open Finset

/-- For m≥6, a divisor large enough for the half-occupied top interval lies
in the upper two thirds of the ambient interval. -/
lemma three_mul_ge_endpoint {r m b a : ℕ} (hr : 3 ≤ r) (hm : 6 ≤ m)
    (half : m < 2*b) (size : r*b ≤ a+r-2) :
    (r+1)*m ≤ 3*a := by
  have h₁ := Nat.mul_le_mul_left r half.le
  have h₂ := Nat.mul_le_mul (show 0 ≤ r-2 by omega) (show 0 ≤ m-6 by omega)
  have hr' : r-2+2=r := by omega
  have hm' : m-6+6=m := by omega
  have hprod := congrArg (fun x : ℕ => x*(m-6+6)) hr'
  have hprod' := congrArg (fun x : ℕ => r*x) hm'
  have heq := congrArg (fun x : ℕ => 2*x) hm'
  have heq' := congrArg (fun x : ℕ => 6*x) hr'
  have hr₂ : 2 ≤ a+r := by omega
  have hs : r*b+2 ≤ a+r := by omega
  nlinarith only [h₁, hprod, hprod', heq, heq', hs, Nat.zero_le ((r-2)*(m-6))]

/-- More than half of the top interval is enough to reduce the remaining
bound to the case with every element at least N/3. The quotient assumptions
are applied only to prospective smaller exceptions. -/
lemma half_occupied_bridge {r m C : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 ((r+1)*m))
    (half : m < 2*(Ioc (r*m) ((r+1)*m) ∩ A).card)
    (quotients : ∀ a ∈ A, 3*a < (r+1)*m →
      ∃ q : ℕ, 0 < q ∧ q ∣ a ∧
        (∀ x ∈ A, a < x → ¬ q ∣ x) ∧
        r*((A.filter (fun x => a < x)).image (fun x => x%q)).card ≤ q+r-2)
    (upper : ∀ S ⊆ A, (∀ x ∈ S, (r+1)*m ≤ 3*x) → S.card ≤ m+C) :
    A.card ≤ m + C + (10+5*(r+1)) := by
  classical
  by_cases big : 6 ≤ m
  · let N := (r+1)*m
    let B := Ioc (r*m) N ∩ A
    let D := A.filter (fun a => 3*a < N)
    let U := A.filter (fun a => ¬ 3*a < N)
    have hDU := A.card_filter_add_card_filter_not (fun a => 3*a < N)
    change D.card + U.card = A.card at hDU
    have hU : U.card ≤ m+C := by
      apply upper U (filter_subset _ _)
      intro x hx
      exact le_of_not_gt (mem_filter.mp hx).2
    have hI : B ⊆ Ico (r*m+1) (r*m+1+m) := by
      intro x hx
      have h := mem_Ioc.mp (mem_inter.mp hx).1
      change r*m<x ∧ x≤(r+1)*m at h
      rw [Nat.add_mul, Nat.one_mul] at h
      exact mem_Ico.mpr ⟨by omega, by omega⟩
    have hqall (a : ℕ) (ha : a ∈ D) : ∃ q : ℕ, 0 < q ∧ q ∣ a ∧
          (∀ x ∈ A, a < x → ¬ q ∣ x) ∧
          r*((A.filter (fun x => a < x)).image (fun x => x%q)).card ≤ q+r-2 := by
      have h := mem_filter.mp ha
      exact quotients a h.1 h.2
    choose! f fpos fdvd fonly fcard using hqall
    have hexc (a : ℕ) (ha : a ∈ D) : f a ∈ range 5 ∪ Icc (3*m/4-2) (3*m/4+2) := by
      have h := mem_filter.mp ha
      change a ∈ A ∧ 3*a<N at h
      have hab : a ≤ r*m := by
        have hm' : m ≤ r*m := by
          simpa using Nat.mul_le_mul_right m (show 1 ≤ r by omega)
        dsimp [N] at h
        rw [Nat.add_mul, Nat.one_mul] at h
        omega
      have hBT : B ⊆ A.filter (fun x => a < x) := by
        intro x hx
        have ⟨h₁, h₂⟩ := mem_inter.mp hx
        exact mem_filter.mpr ⟨h₂, lt_of_le_of_lt hab (mem_Ioc.mp h₁).1⟩
      have card := card_le_card (image_subset_image (f := fun x => x % f a) hBT)
      have hcap := (Nat.mul_le_mul_left r card).trans (fcard a ha)
      have hpos : 0 < a := (mem_Icc.mp (sub h.1)).1
      rcases force_large_divisor hr (fpos a ha) (Nat.le_of_dvd hpos (fdvd a ha))
          B hI half hcap with exc | good
      · exact exc
      · exact False.elim ((not_lt_of_ge (three_mul_ge_endpoint hr big half good.2)) h.2)
    have hD := exceptional_elements D f m fdvd (fun a ha x hx =>
      fonly a ha x (mem_filter.mp hx).1)
    rw [filter_eq_self.mpr hexc] at hD
    omega
  · have hcard := card_le_card sub
    simp only [Nat.card_Icc, Nat.add_one_sub_one] at hcard
    have := Nat.mul_le_mul_left (r+1) (show m ≤ 5 by omega)
    nlinarith

end Erdos13HalfOccupied

end

section

/-! The majority case for every arity at least three. -/

namespace Erdos13HalfOccupied

open Finset

/-- The quotient selection in the majority reduction follows from the cyclic
sumset theorem for every prospective small divisor: its tail contains an
element of the majority set. -/
lemma half_bound_of_shell {r m C : ℕ} (hr : 3 ≤ r) (A : Finset ℕ)
    (sub : A ⊆ Icc 1 ((r+1)*m))
    (free : ∀ a ∈ A, ∀ b : Fin r → ℕ, (∀ i, b i ∈ A) → (∀ i, a < b i) →
      ¬ a ∣ ∑ i, b i)
    (half : m < 2*(Ioc (r*m) ((r+1)*m) ∩ A).card)
    (upper : ∀ S ⊆ A, (∀ x ∈ S, (r+1)*m ≤ 3*x) → S.card ≤ m+C) :
    A.card ≤ m + C + (10+5*(r+1)) := by
  apply half_occupied_bridge hr A sub half _ upper
  intro a ha hsmall
  apply OMA.Erdos13Cyclic.witness_of_free (by omega : 2 ≤ r) free
    (fun x hx => (mem_Icc.mp (sub hx)).1) a ha
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < (Ioc (r*m) ((r+1)*m) ∩ A).card by omega)
  obtain ⟨hI, hA⟩ := mem_inter.mp hx
  have hlarge := (mem_Ioc.mp hI).1
  have hm : m ≤ r*m := by
    simpa using Nat.mul_le_mul_right m (show 1 ≤ r by omega)
  rw [Nat.add_mul, Nat.one_mul] at hsmall
  exact ⟨x, mem_filter.mpr ⟨hA, by omega⟩⟩

/-- At every arity r≥3, any set exceeding m by a sufficiently large constant
and occupying over half of its top interval contains a forbidden sum. -/
theorem majority_witness {r : ℕ} (hr : 3 ≤ r) : ∃ K : ℕ, ∀ (m : ℕ) (A : Finset ℕ),
    A ⊆ Icc 1 ((r+1)*m) → m+K < A.card →
    m < 2*(Ioc (r*m) ((r+1)*m) ∩ A).card →
    ∃ a ∈ A, ∃ b : Fin r → ℕ, (∀ i, b i ∈ A ∧ a < b i) ∧ a ∣ ∑ i, b i := by
  let E := (128*r + 24*((r+1)*(16*r+1)+32*r+1)+2) + (r+1)*(64*r+1)
  refine ⟨E + (10+5*(r+1)), ?_⟩
  intro m A sub large half
  by_contra absent
  have free : FullColumns.Free r A := by
    intro a ha b hb hlt hd
    exact absent ⟨a, ha, b, (fun i => ⟨hb i, hlt i⟩), hd⟩
  have bound : A.card ≤ m+E+(10+5*(r+1)) := by
    apply half_bound_of_shell hr A sub free half
    intro S hS third
    have onS : FullColumns.Free r S := fun a ha b hb => free a (hS ha) b (fun i => hS (hb i))
    have h := OMA.Erdos13UpperShell.bound_on_third_shell hr S
      (fun x hx => ⟨(mem_Icc.mp (sub (hS hx))).1, third x hx, (mem_Icc.mp (sub (hS hx))).2⟩) onS
    have hbound : (r+1)*S.card ≤ (r+1)*m+E := by simpa only [E, Nat.add_assoc] using h
    by_contra! tooMany
    have mul := Nat.mul_le_mul_left (r+1) (show m+E+1 ≤ S.card by omega)
    nlinarith only [hbound, mul, Nat.zero_le (r*E), Nat.zero_le r]
  omega

end Erdos13HalfOccupied

end

section

/-! From the residue-column estimate at low pivots to the original
all-endpoint bound, conditional on the count of exceptional pivots. -/
namespace Erdos13ColumnModulo
open Finset FullColumns

/-- All endpoints and all sets are allowed. The only counting input concerning
the pivots is that the exceptional ones have density at most r⁻¹⁰. -/
theorem global_histogram {r U L K E : ℕ} (hr : 128 ≤ r) (lp : 0<L) (many : 3072*L  ≤  K)
    (ul : 4 ≤ U) (sq : r ≤ U*U) (scope : 128*(U*2^K) ≤ r)
    (bad : ∀ (N : ℕ) (B : Finset ℕ), B⊆Icc 1 N →
      (∀ a∈B, ¬histogramGood a r U L) → r^10*B.card  ≤  N+E) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N → Free r A →
      (A.card : ℝ)  ≤  (N : ℝ)/((r : ℝ)+1)+C := by
  classical
  let T := 24*r*r
  let H := T*(r+1)+1
  have hp : 0<H := by dsimp [H]; omega
  have price : (r+1)*H ≤ r^10 := by
    have tr : T  ≤  r^3 := by
      have h := Nat.mul_le_mul_right (r*r) (show 24 ≤ r by omega)
      dsimp [T]
      nlinarith only [h]
    have rb : r+1  ≤  2*r := by omega
    have h1 : H  ≤  3*r^4 := by
      have s := Nat.mul_le_mul tr rb
      have p : 1 ≤ r^4 := pow_pos (by omega : 0<r) 4
      dsimp [H]
      nlinarith only [s,p]
    have h2 := Nat.mul_le_mul rb h1
    have six : 6 ≤ r^5 := by
      have base := Nat.pow_le_pow_left (show 2 ≤ r by omega) 5
      norm_num at base
      omega
    have h3 := Nat.mul_le_mul_right (r^5) six
    nlinarith only [h2,h3]
  obtain ⟨highError,high⟩ := OMA.Erdos13ManyLayers.sparse_top_stability r (by omega)
  obtain ⟨majorError,major⟩ := Erdos13HalfOccupied.majority_witness (r:=r) (by omega)
  let D := highError+H*(r*r+1)+E+majorError
  have rounded (m : ℕ) (A : Finset ℕ) (sub : A⊆Icc 1 ((r+1)*m))
      (free : Free r A) : A.card ≤ m+D := by
    by_cases sparse : 2*(Ioc (r*m) ((r+1)*m) ∩ A).card  ≤  m
    · let N := (r+1)*m
      let G := A.filter (fun a => histogramGood a r U L)
      let B := A.filter (fun a => ¬histogramGood a r U L)
      have ginc : G⊆A := filter_subset _ _
      have binc : B⊆A := filter_subset _ _
      have pos (x) (hx : x∈G) := (mem_Icc.mp (sub (ginc hx))).1
      have gf : Free r G := fun x hx b hb => free _ (ginc hx) b (fun i => ginc (hb i))
      have cap := OMA.Erdos13UpperShell.select_large_scaled (r:=r) (L:=r*r) (t:=H)
        (N:=T*N) (K:=highError) G pos (OMA.Erdos13Cyclic.witness_of_free (by omega) gf pos) (by
          intro a ha d hd dvd quot
          let F := G.filter (a<·)
          have fi : F⊆G := filter_subset _ _
          have fa : F⊆A := fi.trans ginc
          have ff : Free r F := fun x hx b hb => gf _ (fi hx) b (fun i => fi (hb i))
          have strict (x) (hx : x∈F) := (mem_filter.mp hx).2
          have upper (x) (hx : x∈F) : x ≤ N := (mem_Icc.mp (sub (fa hx))).2
          have ap := pos a ha
          by_cases above : N ≤ r*a
          · exact high m F (fun x hx => ⟨pos _ (fi hx),
                above.trans (Nat.mul_le_mul_left r (strict x hx).le),upper x hx⟩) ff
                ((Nat.mul_le_mul_left 2 (card_le_card (inter_subset_inter (Subset.rfl) fa))).trans sparse)
          · have off (u) (hu : u∈F.image (·%a)) : 0<u ∧ u<a := by
              obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
              refine ⟨Nat.pos_of_ne_zero ?_,Nat.mod_lt _ ap⟩
              intro eq
              apply gf a ha (fun _ => x) (fun _ => fi hx) (fun _ => strict x hx)
              have dv := Nat.dvd_of_mod_eq_zero eq
              simpa using dv.trans (dvd_mul_left x r)
            have tail := histogram_tail hr ap ((Nat.le_div_iff_mul_le ap).mpr (by omega : r*a ≤ N))
              lp many ul sq scope (mem_filter.mp ha).2 hd.le dvd F ff off (fun x hx =>
                mem_Icc.mpr ⟨Nat.div_pos (strict x hx).le ap,Nat.div_le_div_right (upper x hx)⟩) quot
            have lim : (r+2)*F.card  ≤  N := tail.trans (Nat.div_mul_le_self N a)
            have pay : H  ≤  T*(r+2) := by
              dsimp [H,T]
              nlinarith [Nat.mul_pos (show 0<r by omega) (show 0<r by omega)]
            have cc : H*F.card ≤ T*N := calc
              _ ≤ (T*(r+2))*F.card := Nat.mul_le_mul_right F.card pay
              _ = T*((r+2)*F.card) := Nat.mul_assoc ..
              _ ≤ T*N := Nat.mul_le_mul_left T lim
            exact cc.trans (Nat.le_add_right _ _))
      have fee := bad N B (binc.trans sub) (fun a ha => (mem_filter.mp ha).2)
      have cost := (Nat.mul_le_mul_right B.card price).trans fee
      have cost' : H*B.card ≤ m+E := by
        apply Nat.le_of_mul_le_mul_left _ (show 0<r+1 by omega)
        rw [Nat.mul_add,←Nat.mul_assoc]
        have extra := Nat.le_mul_of_pos_left E (show 0<r+1 by omega)
        dsimp [N] at cost
        omega
      have partition : G.card+B.card=A.card := A.card_filter_add_card_filter_not _
      have tot : H*A.card ≤ H*m+(highError+H*(r*r+1)+E) := by
        rw [←partition,Nat.mul_add]
        have id : T*N+m=H*m := by dsimp [N,H]; ring
        omega
      apply Nat.le_of_mul_le_mul_left _ hp
      have lift := Nat.le_mul_of_pos_left D hp
      rw [Nat.mul_add]
      dsimp [D] at lift ⊢
      omega
    · by_contra! fail
      obtain ⟨a,ha,b,bs,dv⟩ := major m A sub (show m+majorError<A.card by dsimp [D] at fail; omega)
        (by omega)
      exact free a ha b (fun i => (bs i).1) (fun i => (bs i).2) dv
  refine ⟨(D:ℝ)+1,?_⟩
  intro N A sub free
  let m := N/(r+1)+1
  have extra : N ≤ (r+1)*m := by
    have rel := Nat.mod_add_div N (r+1)
    have zz := Nat.mod_lt N (show 0<r+1 by omega)
    dsimp [m]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have a := rounded m A (fun x hx => mem_Icc.mpr ⟨(mem_Icc.mp (sub hx)).1,(mem_Icc.mp (sub hx)).2.trans extra⟩) free
  have le : (A.card:ℝ) ≤ (N/(r+1):ℕ)+1+(D:ℝ) := by exact_mod_cast a
  have hd := Nat.cast_div_le (m:=N) (n:=r+1) (α:=ℝ)
  push_cast at hd
  linarith

end Erdos13ColumnModulo

end

section

/-! Finite inclusion-exclusion and high-moment estimates for restricted
prime divisors of an integer. -/
namespace Erdos13CoprimeSieve

open Finset

lemma prime_subset_dvd {T : Finset ℕ} (pr : ∀ p∈T, p.Prime) (a : ℕ) :
    (∏ p∈T,p) ∣ a ↔ ∀ p∈T,p∣a := by
  constructor
  · intro h p hp
    exact (dvd_prod_of_mem (fun q : ℕ => q) hp).trans h
  · exact prod_primes_dvd _ (fun p hp => (pr p hp).prime)

lemma prime_mask {T : Finset ℕ} (pr : ∀ p∈T, p.Prime) (a : ℕ) (B : ℝ) :
    (∏ p∈T, if p∣a then B else 0) = if (∏ p∈T,p)∣a then B^T.card else 0 := by
  classical
  split_ifs with all
  · have hit := (prime_subset_dvd pr a).mp all
    simpa [hit] using (show (∏ p∈T, if p∣a then B else 0) = ∏ _∈T,B by
      apply prod_congr rfl
      intro p hp
      rw [if_pos (hit p hp)])
  · have fail : ¬∀ p∈T,p∣a := fun h => all ((prime_subset_dvd pr a).mpr h)
    push Not at fail
    obtain ⟨p,hp,hp'⟩ := fail
    exact prod_eq_zero hp (if_neg hp')

lemma weight_expansion {P : Finset ℕ} (pr : ∀ p∈P,p.Prime) (a : ℕ) (B : ℝ) :
    (1+B)^((P.filter (·∣a)).card) =
      ∑ T∈P.powerset, (if (∏ p∈T,p)∣a then B^T.card else 0) := by
  classical
  calc (1+B)^((P.filter (·∣a)).card) = ∏ p∈P,(1 + if p∣a then B else 0) := by
        rw [← Finset.prod_const]
        rw [Finset.prod_filter]
        apply prod_congr rfl
        intro p _
        split_ifs <;> simp_all
      _ = ∑ T∈P.powerset, (if (∏ p∈T,p)∣a then B^T.card else 0) := by
        rw [Finset.prod_one_add]
        exact sum_congr rfl fun T hT => prime_mask (fun p hp => pr p (mem_powerset.mp hT hp)) a B

/-- The bound on the moment is uniform in the endpoint N. -/
theorem prime_factor_moment {P : Finset ℕ} (pr : ∀ p∈P, p.Prime)
    (N : ℕ) (B : ℝ) (hB : 0≤B) :
    (∑ a∈Ioc 0 N,(1+B)^((P.filter (·∣a)).card)) ≤ N*∏ p∈P,(1+B/p) := by
  classical
  simp_rw [weight_expansion pr]
  rw [sum_comm,prod_one_add,Finset.mul_sum]
  apply sum_le_sum
  intro T hT
  let d := ∏ p∈T,p
  have hc := Nat.Ioc_filter_dvd_card_eq_div N d
  have eq : (∑ a∈Ioc 0 N, if d∣a then B^T.card else 0) = (N/d:ℕ)*B^T.card := by
    rw [←sum_filter]
    simp [hc]
  have prof : (∏ p∈T, B/(p:ℝ)) = B^T.card/(d:ℝ) := by
    simp [d,Finset.prod_div_distrib]
  change (∑ a∈Ioc 0 N, if d∣a then B^T.card else 0) ≤ _
  rw [eq,prof]
  have h := mul_le_mul_of_nonneg_right (Nat.cast_div_le (m:=N) (n:=d) (α:=ℝ)) (pow_nonneg hB T.card)
  exact h.trans_eq (by ring)

lemma multiples_discrepancy {d : ℕ} (hd : 0<d) (v L : ℕ) :
    |(((Ioc v (v+L)).filter (d∣·)).card : ℝ) - (L:ℝ)/d| ≤ 1 := by
  let F (s : Finset ℕ) := s.filter (d∣·)
  have dis : Disjoint (F (Ioc 0 v)) (F (Ioc v (v+L))) :=
    (Ioc_disjoint_Ioc_of_le le_rfl).mono (filter_subset _ _) (filter_subset _ _)
  have eq : F (Ioc 0 v) ∪ F (Ioc v (v+L)) = F (Ioc 0 (v+L)) := by
    dsimp [F]
    rw [←filter_union, Ioc_union_Ioc_eq_Ioc (by omega) (by omega)]
  have count := card_union_of_disjoint dis
  dsimp [F] at eq count
  rw [eq,Nat.Ioc_filter_dvd_card_eq_div,Nat.Ioc_filter_dvd_card_eq_div] at count
  let b := ((Ioc v (v+L)).filter (d∣·)).card
  change (v+L)/d = v/d+b at count
  have m₁ := Nat.mod_add_div v d
  have m₂ := Nat.mod_add_div (v+L) d
  have r₁ := Nat.mod_lt v hd
  have r₂ := Nat.mod_lt (v+L) hd
  have ns : (v+L)%d+d*b=L+v%d := by
    rw [count,Nat.mul_add] at m₂
    omega
  have realEq : (((v+L)%d:ℕ):ℝ)+(d:ℝ)*(b:ℝ) = (L:ℝ)+((v%d:ℕ):ℝ) := by exact_mod_cast ns
  have rd : 0<(d:ℝ) := by exact_mod_cast hd
  have ra : ((v%d:ℕ):ℝ)<d := by exact_mod_cast r₁
  have rb : (((v+L)%d:ℕ):ℝ)<d := by exact_mod_cast r₂
  change |(b:ℝ)-(L:ℝ)/d| ≤ 1
  rw [← mul_le_mul_iff_of_pos_right rd,←abs_of_pos rd,←abs_mul]
  rw [abs_of_pos rd, sub_mul, div_mul_cancel₀ _ rd.ne']
  apply abs_le.mpr
  constructor <;> linarith [show (0:ℝ)≤((v%d:ℕ):ℝ) by positivity,
    show (0:ℝ)≤(((v+L)%d:ℕ):ℝ) by positivity]

/-- Inclusion-exclusion with fewer than one unit of discrepancy per subset
of prime factors, independently of where the interval starts. -/
theorem interval_sieve {P : Finset ℕ} (pr : ∀ p∈P,p.Prime) (v L : ℕ) :
    |(((Ioc v (v+L)).filter (fun a => ∀ p∈P, ¬p∣a)).card : ℝ) -
      (L:ℝ)*∏ p∈P, (1-1/(p:ℝ))| ≤ 2^P.card := by
  classical
  let I := Ioc v (v+L)
  let hit (T : Finset ℕ) := (I.filter ((T.prod id)∣·)).card
  let d (T : Finset ℕ) := T.prod id
  have split : ((I.filter (fun a => ∀ p∈P, ¬p∣a)).card : ℝ) =
      ∑ T∈P.powerset, (-1:ℝ)^T.card*(hit T:ℝ) := by
    have ind (a : ℕ) : (if ∀ p∈P, ¬p∣a then (1:ℝ) else 0) =
        (1+(-1:ℝ))^((P.filter (·∣a)).card) := by
      by_cases all : ∀ p∈P, ¬p∣a
      · have hz : P.filter (·∣a) = ∅ := filter_eq_empty_iff.mpr all
        rw [if_pos all,hz]
        simp
      · have ne : (P.filter (·∣a)).Nonempty := by
          push Not at all
          obtain ⟨p,hp,div⟩ := all
          exact ⟨p,mem_filter.mpr ⟨hp,div⟩⟩
        simp [all, (card_pos.mpr ne).ne']
    calc ((I.filter (fun a => ∀ p∈P, ¬p∣a)).card : ℝ) =
        ∑ a∈I, (if ∀ p∈P, ¬p∣a then (1:ℝ) else 0) := by rw [←sum_filter]; simp
      _ = ∑ a∈I, ∑ T∈P.powerset, (if d T∣a then (-1:ℝ)^T.card else 0) := by
        apply sum_congr rfl
        intro a _
        exact (ind a).trans (weight_expansion pr a (-1))
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro T _
        rw [←sum_filter]
        simp [hit,d,mul_comm]
  have prof : (L:ℝ)*∏ p∈P,(1-1/(p:ℝ)) =
      ∑ T∈P.powerset, (-1:ℝ)^T.card*((L:ℝ)/(d T:ℝ)) := by
    simp_rw [sub_eq_add_neg,← neg_div]
    rw [prod_one_add,Finset.mul_sum]
    apply sum_congr rfl
    intro T _
    simp [d,Finset.prod_div_distrib]
    ring
  change |((I.filter (fun a => ∀ p∈P,¬p∣a)).card:ℝ) - _| ≤ _
  rw [split,prof,←sum_sub_distrib]
  calc _ ≤ ∑ T∈P.powerset, |(-1:ℝ)^T.card*(hit T:ℝ)-(-1:ℝ)^T.card*((L:ℝ)/(d T:ℝ))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _T∈P.powerset, (1:ℝ) := by
      apply sum_le_sum
      intro T hT
      rw [←mul_sub,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      apply multiples_discrepancy
      apply prod_pos
      exact fun p hp => (pr p (mem_powerset.mp hT hp)).pos
    _ = _ := by simp

end Erdos13CoprimeSieve

end

section

/-! Elementary upper bounds for finite Euler products from counting squarefree divisors. -/
namespace Erdos13CoprimeSieve
open Finset
open Real

theorem prime_log_sum {P : Finset ℕ} {X : ℕ} (hX : 2 ≤ X)
    (pr : ∀ p∈P, p.Prime) (cap : ∀ p∈P, p ≤ X) :
    (∑ p∈P, log p / p) ≤ 2*log X := by
  classical
  let I := Ioc 0 X
  have loc {n : ℕ} (hn : n∈I) : (∑ p∈P, if p∣n then log p else 0) ≤ log X := by
    have hn0 := (mem_Ioc.mp hn).1
    have hnX := (mem_Ioc.mp hn).2
    let F := P.filter (·∣n)
    have div : F.prod id ∣ n := (prime_subset_dvd (T:=F)
      (fun p hp => pr p (mem_filter.mp hp).1) _).mpr (fun _ hp => (mem_filter.mp hp).2)
    have dpos : 0 < F.prod id := prod_pos fun p hp => (pr p (mem_filter.mp hp).1).pos
    rw [←sum_filter]
    change (∑ p∈F, log (p:ℝ)) ≤ _
    rw [←log_prod (fun p hp => Nat.cast_ne_zero.mpr (pr p (mem_filter.mp hp).1).ne_zero),
      ←Nat.cast_prod]
    apply Real.log_le_log
    · exact_mod_cast dpos
    · exact_mod_cast (Nat.le_of_dvd hn0 div).trans hnX
  have bound := sum_le_sum (fun n hn => loc hn)
  rw [sum_comm] at bound
  have fold (p : ℕ) : (∑ n∈I, if p∣n then log (p:ℝ) else 0) =
      (X/p:ℕ)*log (p:ℝ) := by
    rw [←sum_filter]
    simp [I,Nat.Ioc_filter_dvd_card_eq_div]
  simp_rw [fold] at bound
  simp [I] at bound
  have step (p : ℕ) (hp : p∈P) :
      (X:ℝ)*(log p / p) ≤ 2*((X/p:ℕ)*log (p:ℝ)) := by
    have pp := (pr p hp).pos
    have cp := cap p hp
    have quo : 1 ≤ X / p := (Nat.one_le_div_iff pp).mpr cp
    have rem := Nat.mod_lt X pp
    have e := Nat.mod_add_div X p
    have nx : X ≤ 2*(X/p)*p := by nlinarith [Nat.mul_le_mul_right p quo]
    have rx : (X:ℝ)/(p:ℝ) ≤ 2*(X/p:ℕ) := (div_le_iff₀ (by exact_mod_cast pp)).mpr (by exact_mod_cast nx)
    have h := mul_le_mul_of_nonneg_right rx (log_nonneg (x:=(p:ℝ)) (by exact_mod_cast (pr p hp).one_le))
    linarith only [show (X:ℝ)*(log p/p)=(X/p)*log (p:ℝ) by ring, h]
  have h := sum_le_sum step
  rw [←mul_sum,←mul_sum] at h
  apply (le_of_mul_le_mul_left (a:=(X:ℝ)) _ (by exact_mod_cast (show 0<X by omega)))
  nlinarith

private lemma subset_mass_moment {P : Finset ℕ} (pr : ∀ p∈P,p.Prime) :
    (∑ T∈P.powerset,(∏ p∈T,(p:ℝ)⁻¹)*(∑ p∈T,log (p:ℝ))) ≤
      (∏ p∈P,(1+(p:ℝ)⁻¹))*(∑ p∈P,log (p:ℝ)/p) := by
  classical
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
    have ih0 := ih (fun q hq => pr q (mem_insert_of_mem hq))
    let V := ∑ T∈P.powerset, (∏ q∈T,(q:ℝ)⁻¹)*(∑ q∈T,log (q:ℝ))
    let M := ∏ q∈P, (1+(q:ℝ)⁻¹)
    have hM : 0 ≤ M := prod_nonneg fun _ _ => by positivity
    have pp := pr p (mem_insert_self p P)
    have lp : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast pp.one_le)
    have ex : ∑ T∈P.powerset, (∏ q∈insert p T,(q:ℝ)⁻¹)*(∑ q∈insert p T,log (q:ℝ)) =
        (p:ℝ)⁻¹*V+((p:ℝ)⁻¹*log (p:ℝ))*M := by
      dsimp [V,M]
      rw [prod_one_add, mul_sum, mul_sum,←sum_add_distrib]
      apply sum_congr rfl
      intro T hT
      have hpt : p∉T := fun h => hp (mem_powerset.mp hT h)
      rw [prod_insert hpt,sum_insert hpt]
      ring
    rw [sum_powerset_insert hp,ex,prod_insert hp,sum_insert hp]
    change V + ((p:ℝ)⁻¹*V + ((p:ℝ)⁻¹*log (p:ℝ))*M) ≤
        (1+(p:ℝ)⁻¹)*M*(log p/p + _)
    change V ≤ M*_ at ih0
    rw [div_eq_mul_inv]
    have hW : 0 ≤ (p:ℝ)⁻¹ := by positivity
    have hL : 0 ≤ (p:ℝ)⁻¹*((p:ℝ)⁻¹*log p*M) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left ih0 hW]

/-- A finite Euler-product bound, obtained from a first logarithmic moment over
the squarefree divisors. -/
theorem plus_product_le {P : Finset ℕ} {X : ℕ} (hX : 2≤X)
    (pr : ∀ p∈P,p.Prime) (cap : ∀ p∈P,p≤X) :
    (∏ p∈P,(1+(p:ℝ)⁻¹)) ≤ 2*(1 + 4*log X) := by
  classical
  let d (T : Finset ℕ) := T.prod id
  let w (T : Finset ℕ) : ℝ := (d T:ℝ)⁻¹
  let M := ∏ p∈P,(1+(p:ℝ)⁻¹)
  let H := P.powerset.filter (fun T => d T ≤ X^4)
  have dpos {T} (hT : T∈P.powerset) : 0<d T :=
    prod_pos fun p hp => (pr p (mem_powerset.mp hT hp)).pos
  have wp (T : Finset ℕ) : w T = ∏ p∈T,(p:ℝ)⁻¹ := by
    simp [w,d]
  have lp {T} (hT : T∈P.powerset) : log (d T:ℝ) = ∑ p∈T,log (p:ℝ) := by
    simp only [d,id_eq,Nat.cast_prod]
    exact log_prod fun p hp => Nat.cast_ne_zero.mpr (pr p (mem_powerset.mp hT hp)).ne_zero
  have sumw : (∑ T∈P.powerset,w T) = M := by simp_rw [wp]; exact (prod_one_add _).symm
  have mom : (∑ T∈P.powerset, w T*log (d T:ℝ)) ≤ M*(2*log X) := by
    calc _ = ∑ T∈P.powerset,(∏ p∈T,(p:ℝ)⁻¹)*(∑ p∈T,log (p:ℝ)) :=
          sum_congr rfl fun T hT => by rw [wp,lp hT]
      _ ≤ M*(∑ p∈P,log (p:ℝ)/p) := subset_mass_moment pr
      _ ≤ _ := mul_le_mul_of_nonneg_left (prime_log_sum hX pr cap) (prod_nonneg fun _ _ => by positivity)
  have inj : Set.InjOn d (H : Set (Finset ℕ)) := by
    intro S hS T hT eq
    have root {U} (hU : U∈H) : (d U).primeFactors=U := Nat.primeFactors_prod
      fun p hp => pr p (mem_powerset.mp (mem_filter.mp hU).1 hp)
    exact (root hS).symm.trans ((congrArg Nat.primeFactors eq).trans (root hT))
  have small : (∑ T∈H, w T) ≤ 1+4*log X := by
    calc _ = ∑ n∈H.image d,(n:ℝ)⁻¹ := (sum_image inj).symm
      _ ≤ ∑ n∈Icc 1 (X^4),(n:ℝ)⁻¹ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨T,hT,rfl⟩ := mem_image.mp hn
          exact mem_Icc.mpr ⟨dpos (mem_filter.mp hT).1,(mem_filter.mp hT).2⟩
        · intros; positivity
      _ = (harmonic (X^4):ℝ) := by simp [harmonic_eq_sum_Icc]
      _ ≤ 1+log ((X^4:ℕ):ℝ) := harmonic_le_one_add_log _
      _ = _ := by simp
  have lx : 0<log (X:ℝ) := log_pos (by exact_mod_cast (show 1<X by omega))
  have major {T} (hT : T∈P.powerset) : (4*log (X:ℝ))*w T ≤
      (if d T ≤ X^4 then (4*log (X:ℝ))*w T else 0)+w T*log (d T:ℝ) := by
    have hwp : 0≤ w T := by dsimp [w]; positivity
    by_cases lt : d T ≤ X^4
    · rw [if_pos lt]
      have hlog := log_nonneg (x:=(d T:ℝ)) (by exact_mod_cast dpos hT)
      exact le_add_of_nonneg_right (mul_nonneg hwp hlog)
    · rw [if_neg lt,zero_add,mul_comm]
      apply mul_le_mul_of_nonneg_left _ hwp
      have comp := Real.log_le_log (x:=((X^4:ℕ):ℝ)) (y:=(d T:ℝ))
        (by positivity) (by exact_mod_cast (le_of_not_ge lt))
      simpa using comp
  have bound := sum_le_sum (fun T ht => major ht)
  rw [←mul_sum,sumw,sum_add_distrib,←sum_filter,←mul_sum] at bound
  change (4*log (X:ℝ))*M ≤ (4*log (X:ℝ))*(∑ T∈H,w T)+_ at bound
  change M ≤ _
  have aux := mul_le_mul_of_nonneg_left small (show 0≤4*log (X:ℝ) by positivity)
  apply (le_of_mul_le_mul_left (a:=2*log (X:ℝ)) _ (by positivity))
  nlinarith

private lemma correction_product (X : ℕ) :
    (∏ n∈Icc 2 (X+1), (n:ℝ)^2/((n:ℝ)^2-1)) = 2*((X:ℝ)+1)/((X:ℝ)+2) := by
  induction X with
  | zero => norm_num
  | succ X ih =>
    rw [prod_Icc_succ_top (by omega),ih]
    push_cast
    have hX : 0 ≤ (X:ℝ) := by positivity
    have hq : ((X:ℝ)+1+1)^2-1≠0 := by nlinarith
    field_simp [hq]
    ring

theorem minus_product_inverse_le {P : Finset ℕ} {X : ℕ} (hX : 2≤X)
    (pr : ∀ p∈P,p.Prime) (cap : ∀ p∈P,p≤X) :
    (∏ p∈P,(1-(p:ℝ)⁻¹)⁻¹) ≤ 4*(1+4*log X) := by
  let f (p : ℕ) : ℝ := (p:ℝ)^2/((p:ℝ)^2-1)
  have fbig {p : ℕ} (h : 2≤p) : 1≤f p := by
    have hp : (2:ℝ)≤(p:ℝ) := by exact_mod_cast h
    apply (le_div_iff₀ (by nlinarith : 0<(p:ℝ)^2-1)).mpr
    linarith
  have corr : (∏ p∈P, f p) ≤ 2 := by
    calc _ ≤ ∏ p∈Icc 2 (X+1), f p := by
          apply prod_le_prod_of_subset_of_one_le
          · exact fun p hp => mem_Icc.mpr ⟨(pr p hp).two_le,(cap p hp).trans (by omega)⟩
          · exact fun p hp => (fbig (pr p hp).two_le).trans' zero_le_one
          · exact fun p hp _ => fbig (mem_Icc.mp hp).1
      _ = _ := correction_product X
      _ ≤ _ := by apply (div_le_iff₀ (by positivity)).mpr; linarith
  have fact : (∏ p∈P,(1-(p:ℝ)⁻¹)⁻¹) = (∏ p∈P,(1+(p:ℝ)⁻¹))*(∏ p∈P,f p) := by
    rw [←prod_mul_distrib]
    apply prod_congr rfl
    intro p hp
    have p2 : 2≤(p:ℝ) := by exact_mod_cast (pr p hp).two_le
    have p0 : (p:ℝ)≠0 := by linarith
    have p1 : (p:ℝ)-1≠0 := by linarith
    have ps : (p:ℝ)^2-1≠0 := by nlinarith
    dsimp [f]
    field_simp
    ring
  rw [fact]
  have H := mul_le_mul (plus_product_le hX pr cap) corr
    (prod_nonneg (fun p hp => (fbig (pr p hp).two_le).trans' zero_le_one))
    (by have := log_nonneg (x:=(X:ℝ)) (by exact_mod_cast (show 1≤X by omega)); positivity)
  linarith

/-- Moment tail estimate for integers with too many prime divisors from P. -/
theorem bad_pivot_bound {P : Finset ℕ} {X : ℕ} (hX : 2≤X)
    (pr : ∀ p∈P,p.Prime) (cap : ∀ p∈P,p≤X) (B N : ℕ) (u : ℝ) :
    (((Ioc 0 N).filter (fun a => u ≤ (1+(B:ℝ))^((P.filter (·∣a)).card))).card:ℝ)*u ≤
      N*(2*(1+4*log X))^B := by
  classical
  let I := Ioc 0 N
  let w (a : ℕ) := (1+(B:ℝ))^((P.filter (·∣a)).card)
  let F := I.filter (fun a => u ≤ w a)
  have hi : (∑ _a∈F,u) ≤ ∑ a∈F,w a := sum_le_sum (fun _ ha => (mem_filter.mp ha).2)
  have him := sum_le_sum_of_subset_of_nonneg (filter_subset (fun a => u≤w a) I)
    (f:=w) (by intro a _ _; dsimp [w]; positivity)
  have pk : (∏ p∈P,(1+(B:ℝ)/p)) ≤ (∏ p∈P, (1+(p:ℝ)⁻¹))^B := by
    rw [←prod_pow]
    apply prod_le_prod (fun _ _ => by positivity)
    intro p hp
    rw [div_eq_mul_inv]
    apply one_add_mul_le_pow
    have : (0:ℝ)≤(p:ℝ)⁻¹ := by positivity
    linarith
  change (F.card:ℝ)*u ≤ _
  simpa only [sum_const,nsmul_eq_mul] using hi.trans (him.trans ((prime_factor_moment pr N B
    (by positivity)).trans (mul_le_mul_of_nonneg_left (pk.trans (pow_le_pow_left₀
    (prod_nonneg (fun _ _ => by positivity)) (plus_product_le hX pr cap) B)) (by positivity))))

end Erdos13CoprimeSieve

end

section

namespace Erdos13CoprimeSieve
open Finset Real

noncomputable def sieveDen (k : ℕ) : ℝ := 8*(1+4*log (2*(k:ℝ)+2))

theorem den_pos (k : ℕ) : 0<sieveDen k := by
  have : 0≤log (2*(k:ℝ)+2) := log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) k])
  dsimp [sieveDen]; positivity

theorem prime_sift_density {P : Finset ℕ} (pr : ∀p∈P,p.Prime) :
    1 ≤ sieveDen P.card*(∏ p∈P,(1-(p:ℝ)⁻¹)) := by
  classical
  let X := 2*P.card+2
  let S := P.filter (·≤X)
  let Q := P \ S
  let C := 4*(1+4*log (X:ℝ))
  let f (p : ℕ) : ℝ := 1-(p:ℝ)⁻¹
  have hX : 2≤X := by dsimp [X]; omega
  have pos {p} (hp : p∈P) : 0<f p := by
    have h : 1<(p:ℝ) := by exact_mod_cast (pr p hp).one_lt
    exact sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr h)
  have ssub : S⊆P := filter_subset _ _
  have small := minus_product_inverse_le hX (fun p hp => pr p (ssub hp))
    (fun p hp => (mem_filter.mp hp).2)
  change (∏ p∈S,(f p)⁻¹) ≤ C at small
  rw [prod_inv_distrib] at small
  have spos : 0 < ∏ p∈S, f p := prod_pos fun _ hp => pos (ssub hp)
  have ssmall : 1 ≤ C*∏ p∈S,f p := by
    rw [←div_le_iff₀ spos,one_div]; exact small
  have x0 : 0<(X:ℝ) := by exact_mod_cast (show 0<X by omega)
  have x2 : 2≤(X:ℝ) := by exact_mod_cast hX
  have t0 : 0≤1-(X:ℝ)⁻¹ := sub_nonneg.mpr ((inv_le_one₀ x0).mpr (by linarith))
  have qsmall : (1-(X:ℝ)⁻¹)^Q.card ≤ ∏ p∈Q, f p := by
    rw [← Finset.prod_const (s:=Q)]
    apply prod_le_prod (fun _ _ => t0)
    intro p hp
    have h := mem_sdiff.mp hp
    have xp : X < p := by
      by_contra! fail
      exact h.2 (mem_filter.mpr ⟨h.1,fail⟩)
    have xp' : (X:ℝ)≤(p:ℝ) := by exact_mod_cast xp.le
    dsimp [f]
    linarith [inv_anti₀ x0 xp']
  have b := one_add_mul_le_pow (a:= -(X:ℝ)⁻¹) (by linarith) Q.card
  rw [←sub_eq_add_neg] at b
  have card : Q.card ≤ P.card := card_le_card sdiff_subset
  have qbound : (Q.card:ℝ) / (X:ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ x0).mpr
    have hx : (X:ℝ)=2*(P.card:ℝ)+2 := by simp [X]
    have qc : (Q.card:ℝ)≤(P.card:ℝ) := by exact_mod_cast card
    linarith
  have qlarge : 1/2 ≤ ∏ p∈Q, f p := by
    rw [div_eq_mul_inv] at qbound
    linarith [b.trans qsmall]
  have ce : sieveDen P.card = 2*C := by simp [sieveDen,C,X]; ring
  have c0 : 0≤C := by
    have := log_nonneg (x:=(X:ℝ)) (by linarith); dsimp [C]; positivity
  change 1 ≤ sieveDen P.card*(∏ p∈P, f p)
  rw [ce, ←prod_sdiff ssub]
  change 1 ≤ 2*C*((∏ p∈Q,f p)*(∏ p∈S,f p))
  have j := mul_le_mul_of_nonneg_left qlarge (mul_nonneg c0 spos.le)
  nlinarith

def restrictedPrimes (X a : ℕ) : Finset ℕ :=
  ((range (X+1)).filter Nat.Prime).filter (·∣a)

def unitsIn (a v L : ℕ) : Finset ℕ := (Ioc v (v+L)).filter (·.Coprime a)

theorem units_discrepancy (a X v L : ℕ) (hx : v+L≤X) :
    |((unitsIn a v L).card:ℝ)-(L:ℝ)*(∏ p∈restrictedPrimes X a,(1-(p:ℝ)⁻¹))| ≤
      (2:ℝ)^(restrictedPrimes X a).card := by
  let P := restrictedPrimes X a
  have hp {p} (h : p∈P) := mem_filter.mp (mem_filter.mp h).1
  have pr : ∀p∈P,p.Prime := fun _ h => (hp h).2
  have eq : unitsIn a v L = (Ioc v (v+L)).filter (fun n=>∀p∈P,¬p∣n) := by
    apply filter_congr
    intro n hn
    rw [← not_iff_not, Nat.Prime.not_coprime_iff_dvd]
    push Not
    constructor
    · rintro ⟨p,pp,dp,da⟩
      have cap := (Nat.le_of_dvd (by have := (mem_Ioc.mp hn).1; omega) dp).trans ((mem_Ioc.mp hn).2.trans hx)
      exact ⟨p,mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega),pp⟩,da⟩,dp⟩
    · rintro ⟨p,pm,dp⟩
      exact ⟨p,pr p pm,dp,(mem_filter.mp pm).2⟩
  simpa only [eq,one_div] using interval_sieve pr v L

theorem units_count_finite (a X v L : ℕ) (hx : v+L≤X)
    (gap : 2*(sieveDen (restrictedPrimes X a).card)*2^(restrictedPrimes X a).card ≤ (L:ℝ)) :
    (L:ℝ) ≤ 2*sieveDen (restrictedPrimes X a).card*(unitsIn a v L).card := by
  let P := restrictedPrimes X a
  let W := sieveDen P.card
  let d := ∏ p∈P,(1-(p:ℝ)⁻¹)
  have w0 : 0 ≤ W := (den_pos _).le
  have pr : ∀p∈P,p.Prime := fun _ h => (mem_filter.mp (mem_filter.mp h).1).2
  have p := prime_sift_density pr
  change 1 ≤ W*d at p
  have u := (abs_le.mp (units_discrepancy a X v L hx)).1
  change -(2:ℝ)^P.card ≤ (↑(unitsIn a v L).card:ℝ) - L*d at u
  change 2*W*2^P.card ≤ (L:ℝ) at gap
  change (L:ℝ) ≤ 2*W*(unitsIn a v L).card
  nlinarith [mul_le_mul_of_nonneg_left u w0, mul_le_mul_of_nonneg_left p (Nat.cast_nonneg L : (0:ℝ)≤L)]

end Erdos13CoprimeSieve

end

section

namespace Erdos13CoprimeSieve
open Finset Real Filter
open scoped Topology

/-- The fixed high moment used to count exceptional pivots costs at most
a quadratic factor in the arity. -/
lemma eventually_moment_cost (B : ℕ) : ∀ᶠ r : ℕ in atTop,
    (2*(1+4*log (2*(r:ℝ))))^B ≤ (r:ℝ)^2 := by
  have lim : Tendsto (fun n : ℕ => 2*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have logbig := (tendsto_log_atTop.comp lim).eventually_ge_atTop (1:ℝ)
  have rat := (tendsto_pow_log_div_mul_add_atTop 1 0 B one_ne_zero).comp lim
  have rat' := rat.eventually_le_const (show (0:ℝ)<1 by norm_num)
  have hconst := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (2*10^B)
  filter_upwards [logbig,rat',hconst,eventually_ge_atTop (1:ℕ)] with r hlog hr hconst rp
  change 1 ≤ log (2*(r:ℝ)) at hlog
  change log (2*(r:ℝ))^B / (1*(2*(r:ℝ))+0) ≤ 1 at hr
  simp only [one_mul,add_zero] at hr
  have rpos : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have p : log (2*(r:ℝ))^B ≤ 2*(r:ℝ) := by
    simpa only [one_mul] using (div_le_iff₀ (show 0<2*(r:ℝ) by positivity)).mp hr
  calc _ ≤ (10*log (2*(r:ℝ)))^B := pow_le_pow_left₀ (by linarith) (by linarith) _
    _ = (10:ℝ)^B*log (2*(r:ℝ))^B := mul_pow _ _ _
    _ ≤ 10^B*(2*(r:ℝ)) := mul_le_mul_of_nonneg_left p (by positivity)
    _ ≤ (r:ℝ)^2 := by nlinarith only [mul_le_mul_of_nonneg_right hconst rpos.le]

/-- A fixed high moment controls the exceptional pivots at each arity. -/
theorem few_bad_pivots_of_moment_cost {r : ℕ} (rpos : 1≤r)
    (cost : (2*(1+4*log (2*(r:ℝ))))^(2^48-1 : ℕ) ≤ (r:ℝ)^2) (N : ℕ) :
    r^10*((Ioc 0 N).filter (fun a =>
      r < 2^(4*(restrictedPrimes (2*r) a).card))).card ≤ N := by
  classical
  let B : ℕ := 2^48-1
  have base : 1+B=2^48 := by norm_num [B]
  change (2*(1+4*log (2*(r:ℝ))))^B ≤ (r:ℝ)^2 at cost
  let P := (range (2*r+1)).filter Nat.Prime
  let F := (Ioc 0 N).filter (fun a => r<2^(4*((P.filter (·∣a)).card)))
  let G := (Ioc 0 N).filter (fun a =>
    (r:ℝ)^12 ≤ (1+(B:ℝ))^((P.filter (·∣a)).card))
  have sub : F⊆G := by
    intro a ha
    obtain ⟨ha,h⟩ := mem_filter.mp ha
    apply mem_filter.mpr ⟨ha,?_⟩
    let s := (P.filter (·∣a)).card
    change r<2^(4*s) at h
    have power := Nat.pow_le_pow_left h.le 12
    have id : (2^(4*s):ℕ)^12=(1+B)^s := by
      rw [base,←pow_mul,←pow_mul]
      congr 1
      omega
    rw [id] at power
    exact_mod_cast power
  have pr (p) (hp : p∈P) : p.Prime := (mem_filter.mp hp).2
  have cap (p) (hp : p∈P) : p≤2*r := by
    have := mem_range.mp (mem_filter.mp hp).1
    omega
  have moment := bad_pivot_bound (by omega : 2≤2*r) pr cap B N ((r:ℝ)^12)
  change (G.card:ℝ)*(r:ℝ)^12 ≤ _ at moment
  push_cast at moment
  have embed : (F.card:ℝ) ≤ G.card := by exact_mod_cast card_le_card sub
  have rpos' : 0<(r:ℝ) := by exact_mod_cast (show 0<r by omega)
  have count := (mul_le_mul_of_nonneg_right embed (show 0≤(r:ℝ)^12 by positivity)).trans
    (moment.trans (mul_le_mul_of_nonneg_left cost (show 0≤(N:ℝ) by positivity)))
  have final : (r:ℝ)^10*(F.card:ℝ) ≤ (N:ℝ) := by
    apply (mul_le_mul_iff_left₀ (show 0<(r:ℝ)^2 by positivity)).mp
    convert count using 1
    ring
  exact_mod_cast final

/-- For all sufficiently large arities, the number of bases with too many
distinct prime factors below 2r is uniformly at most N/r¹⁰. -/
theorem eventually_few_bad_pivots : ∀ᶠ r : ℕ in atTop, ∀ N : ℕ,
    r^10*((Ioc 0 N).filter (fun a =>
      r < 2^(4*(restrictedPrimes (2*r) a).card))).card ≤ N := by
  filter_upwards [eventually_moment_cost (2^48-1),eventually_ge_atTop (1:ℕ)] with r cost rpos
  exact few_bad_pivots_of_moment_cost rpos cost

/-- The fixed prime-factor moment is affordable as soon as log r reaches 2¹⁰⁰. -/
lemma large_log_moment_cost {r : ℕ} (hr : (2:ℝ)^100 ≤ log (r:ℝ)) :
    (2*(1+4*log (2*(r:ℝ))))^(2^48-1 : ℕ) ≤ (r:ℝ)^2 := by
  have rp : r≠0 := by rintro rfl; norm_num at hr
  have rpos : 0<(r:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero rp
  let t : ℝ := log (r:ℝ)
  let y : ℝ := √t
  have bt : (2:ℝ)^100≤t := hr
  have yt : y^2=t := Real.sq_sqrt (by linarith : 0≤t)
  have y0 : 0≤y := Real.sqrt_nonneg _
  have by₀ : (2:ℝ)^50≤y := by
    by_contra! less
    have h := mul_self_lt_mul_self y0 less
    nlinarith only [h,yt,bt]
  have yp : 0<y := by linarith
  have log_two := log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))
  have lg : log (2*(r:ℝ))=log 2+t := log_mul (by norm_num) rpos.ne'
  let v : ℝ := 2*(1+4*log (2*(r:ℝ)))
  have vp : 0<v := by
    dsimp [v]
    rw [lg]
    have := log_nonneg (by norm_num : 1≤(2:ℝ))
    linarith
  have upper : v ≤ 20*y^2 := by
    dsimp [v]
    rw [lg,yt]
    linarith
  have aux : log v ≤ 3*y := by
    calc log v ≤ log (20*y^2) := log_le_log vp upper
      _ = log 20 + 2*log y := by rw [log_mul (by norm_num) (by positivity),log_pow]; norm_num
      _ ≤ 3*y := by
        have := log_le_sub_one_of_pos (by norm_num : 0<(20:ℝ))
        linarith [log_le_sub_one_of_pos yp]
  let B : ℕ := 2^48-1
  have bnd : (B:ℝ)*3 ≤ 2*y := by
    dsimp [B]
    norm_num
    linarith
  have res : (B:ℝ)*log v ≤ 2*t := by
    calc _ ≤ (B:ℝ)*(3*y) := mul_le_mul_of_nonneg_left aux (by positivity)
      _ ≤ 2*y^2 := by nlinarith only [mul_le_mul_of_nonneg_right bnd y0]
      _ = _ := by rw [yt]
  change v^B ≤ (r:ℝ)^2
  apply (log_le_log_iff (pow_pos vp B) (pow_pos rpos 2)).mp
  rw [log_pow,log_pow]
  exact_mod_cast res

theorem few_bad_pivots_of_large_log {r : ℕ} (hr : (2:ℝ)^100 ≤ log (r:ℝ)) (N : ℕ) :
    r^10*((Ioc 0 N).filter (fun a =>
      r < 2^(4*(restrictedPrimes (2*r) a).card))).card ≤ N := by
  have nz : r ≠ 0 := by rintro rfl; norm_num at hr
  have p : 1 ≤ r := Nat.pos_of_ne_zero nz
  exact few_bad_pivots_of_moment_cost p (large_log_moment_cost hr) N

end Erdos13CoprimeSieve

end

section

/-! The sieve loss of order log log r allows sufficiently many dyadic scales. -/
namespace Erdos13ColumnModulo
open Filter Asymptotics

noncomputable def histogramLoss (C : ℝ) (r : ℕ) : ℕ := ⌈C*(1+Real.log (Real.log (r:ℝ)))⌉₊

lemma histogramUnits_of_real {a T r : ℕ} (C : ℝ) (I : Finset ℕ)
    (bounds : ∀ i ∈ I, 1 ≤ i ∧ i ≤ T ∧ i.Coprime a)
    (sep : ∀ i ∈ I, ∀ j ∈ I, i < j → i+40 ≤ j)
    (sz : (T:ℝ) ≤ I.card*(C*(1+Real.log (Real.log (r:ℝ))))) :
    histogramUnits a T (histogramLoss C r) := by
  refine ⟨I,bounds,sep,?_⟩
  have mul := mul_le_mul_of_nonneg_left (Nat.le_ceil (C*(1+Real.log (Real.log (r:ℝ)))))
    (show (0:ℝ) ≤ I.card by positivity)
  dsimp [histogramLoss]
  rw [Nat.mul_comm]
  exact_mod_cast sz.trans mul

theorem histogram_scale {r L : ℕ} (hr : 128 ≤ r) (lg : 4*Real.log 256 ≤ Real.log (r:ℝ))
    (small : 12288*(L:ℝ) ≤ Real.log (r:ℝ)) :
    4 ≤ r.sqrt+1 ∧ r ≤ (r.sqrt+1)*(r.sqrt+1) ∧ 128*((r.sqrt+1)*2^(3072*L)) ≤ r := by
  have rt : 4 ≤ r.sqrt := Nat.le_sqrt.mpr (by omega)
  have bound : (256*2^(3072*L))^2 ≤ r := by
    have hlog2 : Real.log 2 ≤ 1 := by linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
    have mul := mul_le_mul_of_nonneg_left hlog2 (show (0:ℝ) ≤ 3072*L by positivity)
    have est : ((256:ℝ)*2^(3072*L))^2 ≤ r := by
      apply (Real.log_le_log_iff (by positivity) (by exact_mod_cast (show 0<r by omega))).mp
      rw [Real.log_pow,Real.log_mul (by norm_num) (by positivity),Real.log_pow]
      push_cast
      linarith
    exact_mod_cast est
  have z := Nat.le_sqrt'.mpr bound
  have p := Nat.mul_le_mul_right r.sqrt z
  have double := Nat.mul_le_mul_right (128*2^(3072*L)) (show r.sqrt+1 ≤ 2*r.sqrt by omega)
  exact ⟨by omega,(Nat.lt_succ_sqrt r).le,by nlinarith only [p,double,Nat.sqrt_le r]⟩

/-- The constants may depend arbitrarily on the absolute sieve constant C. -/
theorem histogram_parameters (C : ℝ) (hC : 0<C) :
    ∀ᶠ r : ℕ in atTop, 128 ≤ r ∧ 0<histogramLoss C r ∧ 4 ≤ r.sqrt+1 ∧
      r ≤ (r.sqrt+1)*(r.sqrt+1) ∧ 128*((r.sqrt+1)*2^(3072*histogramLoss C r)) ≤ r := by
  have lim : Tendsto (fun r : ℕ=>Real.log (r:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have slow := Real.isLittleO_log_id_atTop.comp_tendsto lim
  have frac : (0:ℝ)<1/(24576*C) := by positivity
  have abs := slow.bound frac
  filter_upwards [eventually_ge_atTop 128,lim.eventually_ge_atTop 1,
    lim.eventually_ge_atTop (4*Real.log 256),lim.eventually_ge_atTop (24576*(C+1)),abs] with r hr h1 h2 h3 h4
  have lg := Real.log_nonneg h1
  change ‖Real.log (Real.log (r:ℝ))‖ ≤ (1/(24576*C))*‖Real.log (r:ℝ)‖ at h4
  rw [Real.norm_of_nonneg lg,Real.norm_of_nonneg (by linarith)] at h4
  have cpos : 0<C*(1+Real.log (Real.log (r:ℝ))) := by positivity
  have ceiling := Nat.ceil_lt_add_one cpos.le
  have small := (le_div_iff₀ (show 0<24576*C by positivity)).mp (by convert h4 using 1;ring : Real.log (Real.log (r:ℝ)) ≤ Real.log (r:ℝ)/(24576*C))
  refine ⟨hr,Nat.one_le_ceil_iff.mpr cpos,histogram_scale hr h2 ?_⟩
  dsimp [histogramLoss]
  nlinarith only [ceiling,small,h3]

theorem histogram_parameters_explicit {r : ℕ} (hr : 2^48 ≤ r)
    (lg : (2:ℝ)^100 ≤ Real.log (r:ℝ)) :
    128 ≤ r ∧ 0<histogramLoss 10000 r ∧ 4 ≤ r.sqrt+1 ∧
      r ≤ (r.sqrt+1)*(r.sqrt+1) ∧ 128*((r.sqrt+1)*2^(3072*histogramLoss 10000 r)) ≤ r := by
  let t := Real.log (r:ℝ)
  let y := Real.sqrt t
  have tp : 0<t := lt_of_lt_of_le (by positivity) lg
  have yp : 0<y := Real.sqrt_pos.mpr tp
  have sy : y^2=t := Real.sq_sqrt tp.le
  have ylarge : (2:ℝ)^50 ≤ y := by
    change (2:ℝ)^100 ≤ t at lg
    nlinarith only [sy,lg,yp,show (0:ℝ)≤2^50 by positivity]
  have logid : Real.log t=2*Real.log y := by rw [←sy,Real.log_pow];norm_num
  have logle : Real.log t≤2*y := by linarith only [logid,Real.log_le_sub_one_of_pos yp]
  have t1 : (1:ℝ)≤t := (by norm_num : (1:ℝ)≤2^100).trans lg
  have lgn := Real.log_nonneg t1
  have cpos : (0:ℝ)<10000*(1+Real.log t) := by positivity
  have ce := Nat.ceil_lt_add_one cpos.le
  have big := mul_nonneg (sub_nonneg.mpr ylarge) (le_of_lt yp)
  have sL : 12288*(histogramLoss 10000 r:ℝ) ≤ Real.log (r:ℝ) := by
    change 12288*(⌈10000*(1+Real.log t)⌉₊:ℝ) ≤ t
    nlinarith only [ce,logle,sy,big,ylarge]
  have h128 : 128 ≤ r := (by norm_num : 128 ≤ (2:ℕ)^48).trans hr
  have h256 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<256)
  have p256 : 4*Real.log 256 ≤ t := by nlinarith only [h256,lg]
  exact ⟨h128,Nat.one_le_ceil_iff.mpr cpos,histogram_scale h128 p256 sL⟩

lemma histogram_log_threshold_aux {M r : ℕ} (hM : 48 ≤ M) (hM' : (2:ℝ)^101 ≤ M)
    (hg : 2^M ≤ r) : 2^48 ≤ r ∧ (2:ℝ)^100 ≤ Real.log (r:ℝ) := by
  have bound := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) hM
  have lower : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have compare : ((2:ℝ)^M) ≤ (r:ℝ) := by exact_mod_cast hg
  have logCmp := Real.log_le_log (by positivity) compare
  rw [Real.log_pow] at logCmp
  have cost := mul_le_mul_of_nonneg_left lower (show (0:ℝ)≤M by positivity)
  exact ⟨bound.trans hg,by linarith only [hM',logCmp,cost]⟩

lemma histogram_log_threshold {r : ℕ} (hg : 2^(2^102) ≤ r) :
    2^48 ≤ r ∧ (2:ℝ)^100 ≤ Real.log (r:ℝ) :=
  histogram_log_threshold_aux (M:=2^102) (by norm_num) (by norm_num) hg

end Erdos13ColumnModulo

end

section

/-! Uniformly spaced units in the intervals used by the column histogram. -/
namespace Erdos13CoprimeSieve
open Finset Real Erdos13ColumnModulo

private lemma den_exp (w : ℕ) : 2*sieveDen w ≤ (2:ℝ)^(max 12 w) := by
  have lg := log_le_sub_one_of_pos (show (0:ℝ)<2*w+2 by positivity)
  have large (j : ℕ) (hj : 12≤j) : 128*j+144 ≤ 2^j := by
    induction j, hj using Nat.le_induction with
    | base => norm_num
    | succ j hj ih =>
      rw [Nat.pow_succ]
      omega
  have wm := le_max_right 12 w
  have h := large (max 12 w) (le_max_left ..)
  have h' : 128*w+144 ≤ 2^(max 12 w) := by omega
  have c : 128*(w:ℝ)+144 ≤ (2:ℝ)^max 12 w := by exact_mod_cast h'
  dsimp [sieveDen]; linarith

private lemma sqrt_gap {r w : ℕ} (hr : 2^48≤r) (good : 2^(4*w)≤r) :
    2*sieveDen w*2^w ≤ (r.sqrt:ℝ) := by
  let h := max 12 w
  have hw : (2:ℕ)^w ≤ 2^h := Nat.pow_le_pow_right (by norm_num) (le_max_right ..)
  have hf : 2^(4*h) ≤ r := by
    rcases le_total w 12 with e|e
    · simpa [h,max_eq_left e] using hr
    · simpa [h,max_eq_right e] using good
  have square : (2^h*2^h)^2 ≤ r := by
    convert hf using 1
    rw [←Nat.pow_add,←Nat.pow_mul]
    congr 1; omega
  have sq := Nat.le_sqrt.mpr (by simpa [sq] using square)
  have hw' : (2:ℝ)^w ≤ (2:ℝ)^h := by exact_mod_cast hw
  have prod := mul_le_mul (den_exp w) hw' (by positivity) (by positivity)
  exact prod.trans (by exact_mod_cast sq)

private lemma den_loss {r w : ℕ} (hr : 2^48≤r) (good : 2^(4*w)≤r) :
    80*sieveDen w ≤ 10000*(1+log (log (r:ℝ))) := by
  have log2 : (1:ℝ)/2 ≤ log 2 := by linarith [Real.log_two_gt_d9]
  have log2' : log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have lw := Real.log_le_log (x:=(2:ℝ)^(4*w)) (y:=(r:ℝ)) (by positivity) (by exact_mod_cast good)
  have lr := Real.log_le_log (x:=(2:ℝ)^48) (y:=(r:ℝ)) (by positivity) (by exact_mod_cast hr)
  rw [Real.log_pow] at lw lr
  push_cast at lw lr
  have t : 2 ≤ log (r:ℝ) := by linarith
  have col : 2*(w:ℝ)+2 ≤ 2*log (r:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left log2 (Nat.cast_nonneg (α:=ℝ) w)]
  have logBound := Real.log_le_log (by positivity) col
  rw [Real.log_mul (by norm_num) (by linarith)] at logBound
  have nonneg := log_nonneg (x:=log (r:ℝ)) (by linarith)
  dsimp [sieveDen]
  linarith

lemma select_separated (S : Finset ℕ) :
    ∃ I ⊆ S, (∀ i∈I,∀ j∈I,i<j → i+40≤j) ∧ S.card≤40*I.card := by
  let F (b : ℕ) := S.filter (fun n => n%40=b)
  have both : S.card = ∑ b∈range 40,(F b).card :=
    card_eq_sum_card_fiberwise (fun x hx => mem_range.mpr (Nat.mod_lt x (by decide)))
  have ex : ∃ b ∈ range 40,S.card ≤ 40*(F b).card := by
    by_contra! fail
    have h := sum_lt_sum_of_nonempty (s:=range 40) (show (range 40).Nonempty from ⟨0,by simp⟩) fail
    rw [←mul_sum,←both] at h
    simp at h
  obtain ⟨b,_,hi⟩ := ex
  refine ⟨F b,filter_subset _ _,?_,hi⟩
  intro i im j jm lt
  have ei := (mem_filter.mp im).2
  have ej := (mem_filter.mp jm).2
  omega

theorem good_pivot_histogram {r a : ℕ} (hr : 2^48≤r)
    (good : 2^(4*(restrictedPrimes (2*r) a).card)≤r) :
    histogramGood a r (r.sqrt+1) (histogramLoss 10000 r) := by
  classical
  let w := (restrictedPrimes (2*r) a).card
  have sq := sqrt_gap hr good
  change 2*sieveDen w*2^w ≤ (r.sqrt:ℝ) at sq
  have loss := den_loss hr good
  change 80*sieveDen w ≤ 10000*(1+log (log (r:ℝ))) at loss
  have count (v L : ℕ) (endp : v+L ≤ 2*r) (length : r.sqrt ≤ L) :
      (L:ℝ) ≤ 2*sieveDen w*(unitsIn a v L).card :=
    units_count_finite _ _ _ _ endp (sq.trans (by exact_mod_cast length))
  constructor
  · let v := r+39
    let L := r-39
    have endp : v+L=2*r := by dsimp [v,L]; omega
    have length : r.sqrt ≤ L := by
      have h := Nat.sqrt_le r
      have lo : 40 ≤ r.sqrt := Nat.le_sqrt.mpr (by omega)
      have sq2 := Nat.mul_le_mul_right r.sqrt (show 2 ≤ r.sqrt by omega)
      dsimp [L]; omega
    have ud := count v L endp.le length
    have pos : 0 < (unitsIn a v L).card := by
      by_contra! zero
      simp [Nat.le_zero.mp zero] at ud
      dsimp [L] at ud
      omega
    obtain ⟨g, hg⟩ := card_pos.mp pos
    obtain ⟨hm,cop⟩ := mem_filter.mp hg
    obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    exact ⟨g,by dsimp [v] at lo; omega,hi.trans_eq endp,cop⟩
  · intro T lo hi
    have ud := count 0 T (by omega) (by omega)
    obtain ⟨I,sub,sep,size⟩ := select_separated (unitsIn a 0 T)
    apply histogramUnits_of_real 10000 I _ sep
    · have size' : ((unitsIn a 0 T).card:ℝ) ≤ 40*I.card := by exact_mod_cast size
      have W := den_pos w
      nlinarith [mul_le_mul_of_nonneg_left size' W.le,
        mul_le_mul_of_nonneg_left loss (Nat.cast_nonneg (α:=ℝ) I.card)]
    · intro i hi
      obtain ⟨hm,cop⟩ := mem_filter.mp (sub hi)
      exact ⟨(mem_Ioc.mp hm).1, by simpa using (mem_Ioc.mp hm).2,cop⟩

end Erdos13CoprimeSieve

end

section

/-! The exact Erdős 13 inequality holds at every sufficiently large arity. -/
namespace Erdos13LargeArity
open Finset Filter Erdos13ColumnModulo Erdos13CoprimeSieve

theorem bound_of_parameters {r : ℕ} (big : 2^48 ≤ r)
    (params : 128 ≤ r ∧ 0<histogramLoss 10000 r ∧ 4 ≤ r.sqrt+1 ∧
      r ≤ (r.sqrt+1)*(r.sqrt+1) ∧ 128*((r.sqrt+1)*2^(3072*histogramLoss 10000 r)) ≤ r)
    (rare : ∀ N : ℕ, r^10*((Ioc 0 N).filter (fun a =>
      r < 2^(4*(restrictedPrimes (2*r) a).card))).card ≤ N) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N → FullColumns.Free r A →
      (A.card : ℝ) ≤ (N : ℝ)/((r : ℝ)+1)+C := by
  obtain ⟨hr,lp,ul,sq,scope⟩ := params
  apply global_histogram (E:=0) hr lp le_rfl ul sq scope
  intro N B sub bad
  have inc : B ⊆ (Ioc 0 N).filter (fun a => r < 2^(4*(restrictedPrimes (2*r) a).card)) := by
    intro a ha
    obtain ⟨pos,upper⟩ := mem_Icc.mp (sub ha)
    apply mem_filter.mpr
    exact ⟨mem_Ioc.mpr ⟨pos,upper⟩,lt_of_not_ge (fun h => bad a ha (good_pivot_histogram big h))⟩
  simpa using (Nat.mul_le_mul_left (r^10) (card_le_card inc)).trans (rare N)

theorem eventually_general :
    ∀ᶠ r : ℕ in atTop, ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N →
      FullColumns.Free r A → (A.card : ℝ) ≤ (N : ℝ)/((r : ℝ)+1)+C := by
  filter_upwards [eventually_ge_atTop (2^48 : ℕ),histogram_parameters 10000 (by norm_num),
    eventually_few_bad_pivots] with r big params rare
  exact bound_of_parameters big params rare

end Erdos13LargeArity

end

section

/-! A concrete upper bound for the finite set of arities where the
general Erdős 13 inequality is still needed. -/
namespace Erdos13LargeArity
open Finset Erdos13ColumnModulo Erdos13CoprimeSieve

theorem explicit_general (r : ℕ) (hr : 2^(2^102 : ℕ) ≤ r) :
    ∃ C : ℝ, ∀ (N : ℕ) (A : Finset ℕ), A⊆Icc 1 N → FullColumns.Free r A →
      (A.card : ℝ) ≤ (N : ℝ)/((r : ℝ)+1)+C := by
  obtain ⟨big,lg⟩ := histogram_log_threshold hr
  exact bound_of_parameters big (histogram_parameters_explicit big lg) (few_bad_pivots_of_large_log lg)

end Erdos13LargeArity

end

theorem OMA.solution : OMA.R_Erdos13_erdos_13_variants_general_R1_H1_R1_H3_R1.H1 :=
  Erdos13LargeArity.explicit_general
