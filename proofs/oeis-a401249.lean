import OMAStatements.S_oeis_a401249

/-! The odd divisors in the first block inject into the odd divisors of every block. -/
-- Credit: @STARDUSTLC666

namespace OddDivisorBlocks

open Finset OMA.S_oeis_a401249

-- Every cut strictly below b has a divisor just above it, within a factor of two.
private def Dense (b : ℕ) : Prop :=
  ∀ x : ℕ, 1 ≤ x → x < b → ∃ y : ℕ, y ∣ b ∧ x < y ∧ y ≤ 2*x

private lemma dense_mul {b q : ℕ} (dense : Dense b) (hq : 0 < q) (near : q ≤ 2*b) :
    Dense (b*q) := by
  intro x hx last
  by_cases small : x < b
  · obtain ⟨y,hy,greater,le⟩ := dense x hx small
    exact ⟨y, hy.trans (dvd_mul_right b q), greater, le⟩
  by_cases next : x < q
  · exact ⟨q, dvd_mul_left q b, next, by omega⟩
  have one : 1 ≤ x/q := (Nat.le_div_iff_mul_le hq).mpr (by omega)
  obtain ⟨y,hy,greater,le⟩ := dense (x/q) one ((Nat.div_lt_iff_lt_mul hq).mpr last)
  refine ⟨y*q, Nat.mul_dvd_mul hy (dvd_refl q), (Nat.div_lt_iff_lt_mul hq).mp greater, ?_⟩
  calc
    y*q ≤ (2*(x/q))*q := Nat.mul_le_mul_right q le
    _ = 2*((x/q)*q) := Nat.mul_assoc _ _ _
    _ ≤ 2*x := Nat.mul_le_mul_left 2 (Nat.div_mul_le_self x q)

private lemma dense_factor (n : ℕ) (hn : 0 < n) :
    ∃ b r : ℕ, n = b*r ∧ 0 < b ∧ Dense b ∧ ∀ q : ℕ, q ∣ r → 1 < q → 2*b < q := by
  classical
  let good := n.divisors.filter Dense
  have one : 1 ∈ good := mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hn.ne',
    fun x hx lt => by omega⟩
  obtain ⟨b,mem,best⟩ := exists_max_image good id ⟨1,one⟩
  obtain ⟨divis,dense⟩ := mem_filter.mp mem
  obtain ⟨r,eq⟩ := (Nat.mem_divisors.mp divis).1
  have hb : 0 < b := Nat.pos_of_mem_divisors divis
  refine ⟨b,r,eq,hb,dense,?_⟩
  intro q hq large
  by_contra! near
  have dvd : b*q ∣ n := eq ▸ Nat.mul_dvd_mul_left b hq
  have inSet : b*q ∈ good := mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨dvd,hn.ne'⟩,dense_mul dense (by omega) near⟩
  have bound : b*q ≤ b := best _ inSet
  have more := Nat.mul_lt_mul_of_pos_left large hb
  omega

-- Propagate a property from one to every divisor using steps of ratio at most two.
private lemma propagate {b : ℕ} (hb : 0 < b) (dense : Dense b) (P : ℕ → Prop)
    (first : P 1) (step : ∀ x y, x ∣ b → y ∣ b → x < y → y ≤ 2*x → P x → P y)
    (y : ℕ) (hy : y ∣ b) : P y := by
  classical
  induction y using Nat.strong_induction_on with
  | h y ih =>
    have yp := Nat.pos_of_dvd_of_pos hy hb
    by_cases eq : y = 1
    · simpa [eq] using first
    let prev := b.divisors.filter (· < y)
    have entry : 1 ∈ prev := mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hb.ne',by omega⟩
    obtain ⟨x,hx,best⟩ := exists_max_image prev id ⟨1,entry⟩
    obtain ⟨member,lt⟩ := mem_filter.mp hx
    have xd := (Nat.mem_divisors.mp member).1
    obtain ⟨u,du,xu,ux⟩ := dense x (Nat.pos_of_mem_divisors member)
      (lt.trans_le (Nat.le_of_dvd hb hy))
    have yu : y ≤ u := by
      by_contra! uy
      have bound : u ≤ x := best u (mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨du,hb.ne'⟩,uy⟩)
      omega
    exact step x y xd hy lt (yu.trans ux) (ih x lt xd)

private def Far (A B : List ℕ) : Prop := ∀ x ∈ A, ∀ y ∈ B, 2*x < y

private lemma separated (L : List (List ℕ)) (sorted : L.flatten.Pairwise (· ≤ ·))
    (cuts : L.IsChain (fun A B => ∃ ha hb, decide (B.head hb ≤ 2*A.getLast ha) = false)) :
    L.Pairwise Far := by
  induction L with
  | nil => simp
  | cons A tail ih =>
    have sort := List.pairwise_append.mp (show (A ++ tail.flatten).Pairwise (· ≤ ·) from sorted)
    refine List.pairwise_cons.mpr ⟨?_, ih sort.2.1 cuts.tail⟩
    intro C hC x hx y hy
    cases tail with
    | nil => simp at hC
    | cons B rest =>
      obtain ⟨ha,hb,gap⟩ := (List.isChain_cons_cons.mp cuts).1
      have g : 2*A.getLast ha < B.head hb := by simpa using gap
      have xlast := sort.1.rel_getLast hx
      have sb := List.pairwise_append.mp
        (show (B ++ rest.flatten).Pairwise (· ≤ ·) from sort.2.1)
      have by' : B.head hb ≤ y := by
        rcases List.mem_cons.mp hC with rfl | hC
        · exact sb.1.rel_head hy
        · exact sb.2.2 _ (List.head_mem hb) _ (List.mem_flatten.mpr ⟨C,hC,hy⟩)
      omega

private lemma compare_blocks {L : List (List ℕ)} (sep : L.Pairwise Far)
    {A B : List ℕ} (a : A ∈ L) (b : B ∈ L) : A = B ∨ Far A B ∨ Far B A := by
  induction L with
  | nil => simp at a
  | cons C rest ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp sep
    rcases List.mem_cons.mp a with rfl | ar <;> rcases List.mem_cons.mp b with rfl | br
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (head _ br))
    · exact Or.inr (Or.inr (head _ ar))
    · exact ih tail ar br

private lemma flatten_blocks (n : ℕ) : (blocks n).flatten = n.divisors.sort (· ≤ ·) :=
  List.flatten_splitBy _ _

private lemma mem_blocks {n x : ℕ} :
    (∃ B ∈ blocks n, x ∈ B) ↔ x ∈ n.divisors := by
  rw [← List.mem_flatten, flatten_blocks, Finset.mem_sort]

private lemma block_separation (n : ℕ) : (blocks n).Pairwise Far := by
  have sort : (blocks n).flatten.Pairwise (· ≤ ·) := by
    rw [flatten_blocks]
    exact Finset.pairwise_sort _ _
  exact separated _ sort (List.isChain_getLast_head_splitBy
    (fun x y : ℕ => decide (y ≤ 2*x)) (n.divisors.sort (· ≤ ·)))

private lemma closed {n : ℕ} {B : List ℕ} (member : B ∈ blocks n) {x y : ℕ}
    (hx : x ∈ B) (hy : y ∈ n.divisors) (xy : x ≤ 2*y) (yx : y ≤ 2*x) : y ∈ B := by
  obtain ⟨C,hC,cy⟩ := mem_blocks.mpr hy
  rcases compare_blocks (block_separation n) member hC with eq | before | after
  · exact eq ▸ cy
  · exact (not_lt_of_ge yx (before x hx y cy)).elim
  · exact (not_lt_of_ge xy (after y cy x hx)).elim

private lemma small_chain (b : ℕ) (a : ℕ) (tail : List ℕ) (start : a ≤ b)
    (chain : (a :: tail).IsChain (fun x y => decide (y ≤ 2*x) = true))
    (gap : ∀ x ∈ tail, x ≤ b ∨ 2*b < x) : ∀ x ∈ a :: tail, x ≤ b := by
  induction tail generalizing a with
  | nil => simpa using start
  | cons y tail ih =>
    have near : y ≤ 2*a := by simpa using (List.isChain_cons_cons.mp chain).1
    have small := (gap y List.mem_cons_self).resolve_right (by omega)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | rest
    · exact start
    · exact ih y small chain.tail (fun z hz => gap z (List.mem_cons_of_mem _ hz)) x rest

private lemma odd_count_le {A B : List ℕ} {q : ℕ} (pos : 0 < q) (odd : Odd q)
    (an : A.Nodup) (bn : B.Nodup) (copy : ∀ x ∈ A, q*x ∈ B) :
    A.countP (fun d => decide (Odd d)) ≤ B.countP (fun d => decide (Odd d)) := by
  classical
  let f (d : ℕ) := decide (Odd d)
  let src := (A.filter f).toFinset
  let dst := (B.filter f).toFinset
  have sub : src.image (fun x => q*x) ⊆ dst := by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hv
    have h : x ∈ A ∧ Odd x := by simpa [src,f] using hx
    have ho := odd.mul h.2
    simpa [dst,f] using (show q*x ∈ B ∧ Odd (q*x) from ⟨copy x h.1,ho⟩)
  have count := Finset.card_le_card sub
  rw [card_image_of_injective _ (fun _ _ eq => Nat.eq_of_mul_eq_mul_left pos eq)] at count
  simpa only [src,dst,List.toFinset_card_of_nodup (an.filter f),
    List.toFinset_card_of_nodup (bn.filter f), List.countP_eq_length_filter, f] using count

private lemma first_min {n : ℕ} (hn : 0 < n) {F : List ℕ} {tail : List (List ℕ)}
    (decomp : blocks n = F :: tail) :
    ∀ B ∈ blocks n, F.countP (fun d => decide (Odd d)) ≤ B.countP (fun d => decide (Odd d)) := by
  classical
  obtain ⟨b,r,eq,hb,dense,far⟩ := dense_factor n hn
  have rp : 0 < r := by by_contra! h; simp [show r = 0 by omega] at eq; omega
  have whole (x : ℕ) (hx : x ∣ n) : ∃ t q, t ∣ b ∧ q ∣ r ∧ x = t*q :=
    exists_dvd_and_dvd_of_dvd_mul (eq ▸ hx)
  have split (x : ℕ) (hx : x ∣ n) : x ∣ b ∨ 2*b < x := by
    obtain ⟨t,q,ht,hq,rfl⟩ := whole x hx
    by_cases unit : q = 1
    · exact Or.inl (by simpa [unit] using ht)
    · have large := far q hq (by have := Nat.pos_of_dvd_of_pos hq rp; omega)
      have le := Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_dvd_of_pos ht hb)
        (Nat.pos_of_dvd_of_pos hq rp)) (dvd_mul_left q t)
      exact Or.inr (large.trans_le le)
  have hF : F ∈ blocks n := decomp ▸ List.mem_cons_self
  have notempty : [] ∉ blocks n := List.nil_notMem_splitBy _ _
  have flatten := flatten_blocks n
  have sorted : (blocks n).flatten.Pairwise (· ≤ ·) := flatten ▸ Finset.pairwise_sort _ _
  have nodup : (blocks n).flatten.Nodup := flatten ▸ Finset.sort_nodup _ _
  have member_dvd {C : List ℕ} (hc : C ∈ blocks n) {x : ℕ} (hx : x ∈ C) : x ∣ n :=
    (Nat.mem_divisors.mp (mem_blocks.mp ⟨C,hc,hx⟩)).1
  have first : ∀ x ∈ F, x ∣ b := by
    cases F with
    | nil => exact (notempty hF).elim
    | cons a l =>
      have one : 1 ∈ (blocks n).flatten := flatten ▸ (n.divisors.mem_sort _).mpr
        (Nat.one_mem_divisors.mpr hn.ne')
      rw [decomp] at sorted one
      have low : a ≤ 1 := sorted.rel_head one
      have bound := small_chain b a l (by omega) (List.isChain_of_mem_splitBy hF)
        (by
          intro x hx
          rcases split x (member_dvd hF (List.mem_cons_of_mem a hx)) with h | h
          · exact Or.inl (Nat.le_of_dvd hb h)
          · exact Or.inr h)
      intro x hx
      exact (split x (member_dvd hF hx)).resolve_right (by have := bound x hx; omega)
  intro B hB
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil B (fun e => notempty (e ▸ hB))
  obtain ⟨t,q,dt,dq,ex⟩ := whole x (member_dvd hB hx)
  have qp := Nat.pos_of_dvd_of_pos dq rp
  have odd : Odd q := by
    by_contra h
    have even : 2 ∣ q := even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp h)
    have impossible := far 2 (even.trans dq) (by decide)
    omega
  have product (s : ℕ) (ds : s ∣ b) : q*s ∈ n.divisors := by
    apply Nat.mem_divisors.mpr
    exact ⟨by rw [eq, Nat.mul_comm q]; exact Nat.mul_dvd_mul ds dq, hn.ne'⟩
  have qmem : q ∈ n.divisors := by simpa using product 1 (one_dvd _)
  obtain ⟨C,hC,cq⟩ := mem_blocks.mpr qmem
  have copies : ∀ s, s ∣ b → q*s ∈ C :=
    propagate hb dense (fun s => q*s ∈ C) (by simpa using cq) (by
      intro u v _ dv uv near cu
      apply closed hC cu (product v dv)
      · nlinarith [Nat.mul_le_mul_left q uv.le]
      · nlinarith [Nat.mul_le_mul_left q near])
  have inC : x ∈ C := by simpa [ex, Nat.mul_comm] using copies t dt
  have same : C = B := by
    rcases compare_blocks (block_separation n) hC hB with h | h | h
    · exact h
    · have bad := h x inC x hx; omega
    · have bad := h x hx x inC; omega
  have nd {L : List ℕ} (mem : L ∈ blocks n) : L.Nodup :=
    (List.pairwise_flatten.mp nodup).1 L mem
  exact odd_count_le qp odd (nd hF) (nd hB) (fun y hy => same ▸ copies y (first y hy))

end OddDivisorBlocks

open OddDivisorBlocks OMA.S_oeis_a401249

theorem OMA.solution : type_of% @OMA.S_oeis_a401249.main := by
  intro n hn
  cases eq : blocks n with
  | nil =>
    have h := mem_blocks.mpr (Nat.one_mem_divisors.mpr (by omega : n ≠ 0))
    simp [eq] at h
  | cons F L =>
    have least := first_min hn eq
    let f (B : List ℕ) := B.countP (fun d => decide (Odd d))
    have low : ∀ z ∈ (F::L).map f, f F ≤ z := by
      intro z hz
      obtain ⟨B,hB,rfl⟩ := List.mem_map.mp hz
      exact least B (eq ▸ hB)
    have val : ((F::L).map f).min? = some (f F) := by
      apply List.min?_eq_some_iff.mpr
      exact ⟨List.mem_map.mpr ⟨F,List.mem_cons_self,rfl⟩,low⟩
    unfold A401249 A384225
    rw [eq]
    change (((F::L).map f).min?).getD 0 = f F
    rw [val]
    rfl
