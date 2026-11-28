import OMAStatements.S_oeis_a246600

/-!
# Mean number of divisors whose binary ones occur in the dividend

We prove Amiram Eldar's 2023 conjecture for OEIS A246600. The average
converges to one plus the sum of the divisor weights, and that series
converges. The term one comes from the diagonal with multiplier one.

One aligned square of side 2^h has at most 3^h admissible pairs. This
gives a uniform bound on the pairs for which both factors are large.
Periodicity gives the contribution of each fixed divisor. For fixed
multiplier at least two, one forbidden digit gives zero density.
The two limits and the uniform bound then give the claimed mean.

Source: https://oeis.org/A246600
Sequence: N. J. A. Sloane. Mean-value conjecture: Amiram Eldar.
-/


/- Turn the sum over dividends into a count of ordered divisor-multiplier pairs. -/

namespace A246600Counts

open Finset OMA.S_oeis_a246600

private def admissible (p : ℕ × ℕ) : Prop :=
  p.1 &&& (p.1*p.2) = p.1

private instance decidableAdmissible (p : ℕ × ℕ) : Decidable (admissible p) :=
  inferInstanceAs (Decidable (p.1 &&& (p.1*p.2) = p.1))

def allPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 1 N).filter fun p => p.1*p.2 ≤ N ∧ admissible p

def properPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Icc 1 N ×ˢ Icc 2 N).filter fun p => p.1*p.2 ≤ N ∧ admissible p

private theorem coord_le_product (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    d ≤ d*k ∧ k ≤ d*k :=
  ⟨by simpa using Nat.mul_le_mul_left d hk,
   by simpa using Nat.mul_le_mul_right k hd⟩

private theorem fiber_all (N n : ℕ) (hn : 1 ≤ n) (hN : n ≤ N) :
    ((((Icc 1 N ×ˢ Icc 1 N).filter admissible).filter (fun p => p.1*p.2 = n)).card) =
      term n := by
  unfold term
  apply card_bij (fun p _ => p.1)
  · intro p hp
    simp only [mem_filter,mem_product,mem_Icc] at hp
    have hdiv : p.1 ∣ n := ⟨p.2,hp.2.symm⟩
    apply mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hdiv,by omega⟩,?_⟩
    simpa only [admissible,hp.2] using hp.1.2
  · intro p hp q hq heq
    simp only [mem_filter,mem_product,mem_Icc] at hp hq
    apply Prod.ext heq
    apply Nat.eq_of_mul_eq_mul_left (show 0 < p.1 by omega)
    rw [hp.2,heq,hq.2]
  · intro d hd
    obtain ⟨hdiv,hbits⟩ := mem_filter.mp hd
    obtain ⟨⟨k,hk⟩,_⟩ := Nat.mem_divisors.mp hdiv
    have hdp : 1 ≤ d := by
      by_contra! h
      have : d=0 := by omega
      simp [this] at hk
      omega
    have hkp : 1 ≤ k := by
      by_contra! h
      have : k=0 := by omega
      simp [this] at hk
      omega
    obtain ⟨hda,hka⟩ := coord_le_product d k hdp hkp
    refine ⟨(d,k),?_ ,rfl⟩
    simp only [mem_filter,mem_product,mem_Icc,admissible]
    exact ⟨⟨⟨⟨hdp,by omega⟩,⟨hkp,by omega⟩⟩,by simpa only [←hk] using hbits⟩,hk.symm⟩

theorem all_pairs_sum (N : ℕ) : (allPairs N).card = ∑ k ∈ range N, term (k+1) := by
  have set_eq : allPairs N =
      ((Icc 1 N ×ˢ Icc 1 N).filter admissible).filter (fun p => p.1*p.2 ∈ Icc 1 N) := by
    ext p
    simp only [allPairs,mem_filter,mem_product,mem_Icc]
    constructor
    · rintro ⟨⟨dl,kl⟩,⟨hn,hgood⟩⟩
      exact ⟨⟨⟨dl,kl⟩,hgood⟩,dl.1.trans (coord_le_product _ _ dl.1 kl.1).1,hn⟩
    · rintro ⟨⟨⟨dl,kl⟩,hgood⟩,⟨_,hn⟩⟩
      exact ⟨⟨dl,kl⟩,hn,hgood⟩
  have card_sum : (allPairs N).card = ∑ n ∈ Icc 1 N, term n := by
    rw [set_eq,←sum_card_fiberwise_eq_card_filter]
    apply sum_congr rfl
    intro n hn
    exact fiber_all N n (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
  let f : ℕ ↪ ℕ := ⟨fun k => k+1,by
    intro a b h
    change a+1=b+1 at h
    omega⟩
  have range_eq : Icc 1 N = (range N).map f := by
    ext n
    simp only [mem_Icc,mem_map,mem_range]
    change (1 ≤ n ∧ n ≤ N) ↔ ∃ k, k < N ∧ k+1=n
    constructor
    · intro h
      exact ⟨n-1,by omega,by omega⟩
    · rintro ⟨k,hk,rfl⟩
      omega
  rw [card_sum,range_eq,sum_map]
  rfl

private theorem diagonal_pairs (N : ℕ) :
    ((allPairs N).filter fun p => p.2=1).card = N := by
  have h : ((allPairs N).filter fun p => p.2=1).card = (Icc 1 N).card := by
    apply card_bij (fun p _ => p.1)
    · intro p hp
      exact (mem_product.mp ((mem_filter.mp (mem_filter.mp hp).1).1)).1
    · intro p hp q hq he
      exact Prod.ext he ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm)
    · intro d hd
      refine ⟨(d,1),?_ ,rfl⟩
      have hN : 1 ≤ N := (mem_Icc.mp hd).1.trans (mem_Icc.mp hd).2
      refine mem_filter.mpr ⟨mem_filter.mpr
        ⟨mem_product.mpr ⟨hd,mem_Icc.mpr ⟨le_rfl,hN⟩⟩,?_⟩,rfl⟩
      change d*1 ≤ N ∧ d &&& (d*1) = d
      simpa using (mem_Icc.mp hd).2
  simpa [Nat.card_Icc] using h

theorem all_pairs_split (N : ℕ) : (allPairs N).card = N + (properPairs N).card := by
  have h : (allPairs N).filter (fun p => ¬ p.2 = 1) = properPairs N := by
    ext p
    simp only [allPairs,properPairs,mem_filter,mem_product,mem_Icc]
    constructor
    · rintro ⟨⟨⟨dl,kl⟩,good⟩,hk⟩
      exact ⟨⟨dl,by omega,kl.2⟩,good⟩
    · rintro ⟨⟨dl,kl⟩,good⟩
      exact ⟨⟨⟨dl,by omega,kl.2⟩,good⟩,by omega⟩
  calc
    _ = ((allPairs N).filter fun p => p.2=1).card +
      ((allPairs N).filter fun p => ¬p.2=1).card :=
        (card_filter_add_card_filter_not _).symm
    _ = _ := by rw [diagonal_pairs,h]

end A246600Counts

/- Split the proper divisor pairs into a fixed-divisor band, a fixed-multiplier band,
and the tail where both coordinates are large. -/

namespace A246600Partition

open Finset A246600Counts

def divisorRow (N d : ℕ) : Finset ℕ :=
  (Icc 2 (N/d)).filter (fun k => d &&& (d*k) = d)

def multiplierRow (N k : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun d => d &&& (d*k) = d)

def tailPairs (N D : ℕ) : Finset (ℕ × ℕ) :=
  (Icc D N ×ˢ Icc D N).filter (fun p : ℕ × ℕ =>
    p.1*p.2 ≤ N ∧ p.1 &&& (p.1*p.2) = p.1)

private def smallDivisors (N D : ℕ) : Finset (ℕ × ℕ) :=
  (properPairs N).filter (fun p => p.1 ∈ Ico 1 D)

private def smallMultipliers (N D : ℕ) : Finset (ℕ × ℕ) :=
  (properPairs N).filter (fun p => p.2 ∈ Ico 2 D)

private theorem proper_mem {N : ℕ} {p : ℕ × ℕ} :
    p ∈ properPairs N ↔
      (p.1 ∈ Icc 1 N ∧ p.2 ∈ Icc 2 N) ∧ (p.1*p.2 ≤ N ∧ p.1 &&& (p.1*p.2) = p.1) :=
  (mem_filter.trans (and_congr_left' mem_product))

private theorem divisor_fibre (N d : ℕ) (hd : 1 ≤ d) :
    ((properPairs N).filter (fun p => p.1 = d)).card = (divisorRow N d).card := by
  apply card_bij (fun p _ => p.2)
  · intro p hp
    obtain ⟨hm,he⟩ := mem_filter.mp hp
    obtain ⟨⟨_,hk⟩,hp,hb⟩ := proper_mem.mp hm
    rw [he] at hp hb
    have hdiv : p.2 ≤ N/d := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa only [Nat.mul_comm] using hp)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hk).1,hdiv⟩,hb⟩
  · intro p hp q hq he
    exact Prod.ext ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) he
  · intro k hk
    obtain ⟨hi,hb⟩ := mem_filter.mp hk
    obtain ⟨hlo,hhi⟩ := mem_Icc.mp hi
    have hp : d*k ≤ N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hhi
    have hdn : d ≤ N := le_trans (by simpa using Nat.mul_le_mul_left d (show 1≤k by omega)) hp
    have hkn : k ≤ N := le_trans (by simpa using Nat.mul_le_mul_right k hd) hp
    exact ⟨(d,k),mem_filter.mpr ⟨proper_mem.mpr
      ⟨⟨mem_Icc.mpr ⟨hd,hdn⟩,mem_Icc.mpr ⟨hlo,hkn⟩⟩,hp,hb⟩,rfl⟩,rfl⟩

private theorem multiplier_fibre_le (N k : ℕ) :
    ((properPairs N).filter (fun p => p.2 = k)).card ≤ (multiplierRow N k).card := by
  apply card_le_card_of_injOn Prod.fst
  · intro p hp
    obtain ⟨hm,he⟩ := mem_filter.mp (mem_coe.mp hp)
    obtain ⟨⟨hd,_⟩,_,hb⟩ := proper_mem.mp hm
    exact mem_filter.mpr ⟨hd,by simpa only [he] using hb⟩
  · intro p hp q hq he
    exact Prod.ext he ((mem_filter.mp (mem_coe.mp hp)).2.trans (mem_filter.mp (mem_coe.mp hq)).2.symm)

private theorem small_divisors_eq (N D : ℕ) :
    (smallDivisors N D).card = ∑ d ∈ Ico 1 D, (divisorRow N d).card := by
  rw [smallDivisors,←sum_card_fiberwise_eq_card_filter]
  apply sum_congr rfl
  intro d hd
  exact divisor_fibre N d (mem_Ico.mp hd).1

private theorem small_multipliers_le (N D : ℕ) :
    (smallMultipliers N D).card ≤ ∑ k ∈ Ico 2 D, (multiplierRow N k).card := by
  rw [smallMultipliers,←sum_card_fiberwise_eq_card_filter]
  exact sum_le_sum (fun k _ => multiplier_fibre_le N k)

theorem bounds (N D : ℕ) :
    (∑ d ∈ Ico 1 D, (divisorRow N d).card) ≤ (properPairs N).card ∧
    (properPairs N).card ≤ (∑ d ∈ Ico 1 D, (divisorRow N d).card) +
      (∑ k ∈ Ico 2 D, (multiplierRow N k).card) + (tailPairs N D).card := by
  have covered : properPairs N ⊆ smallDivisors N D ∪ smallMultipliers N D ∪ tailPairs N D := by
    intro p hp
    obtain ⟨⟨hd,hk⟩,hprod,hbits⟩ := proper_mem.mp hp
    by_cases h : p.1 < D
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,mem_Ico.mpr ⟨(mem_Icc.mp hd).1,h⟩⟩))
    by_cases g : p.2 < D
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp,mem_Ico.mpr ⟨(mem_Icc.mp hk).1,g⟩⟩))
    exact mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_Icc.mpr ⟨by omega,(mem_Icc.mp hd).2⟩,
       mem_Icc.mpr ⟨by omega,(mem_Icc.mp hk).2⟩⟩,hprod,hbits⟩)
  constructor
  · rw [←small_divisors_eq]
    exact card_filter_le _ _
  · calc
      _ ≤ (smallDivisors N D ∪ smallMultipliers N D ∪ tailPairs N D).card := card_le_card covered
      _ ≤ (smallDivisors N D ∪ smallMultipliers N D).card + (tailPairs N D).card := card_union_le _ _
      _ ≤ (smallDivisors N D).card + (smallMultipliers N D).card + (tailPairs N D).card :=
        Nat.add_le_add_right (card_union_le _ _) _
      _ ≤ _ := by rw [small_divisors_eq]; exact Nat.add_le_add_right (Nat.add_le_add_left (small_multipliers_le N D) _) _

end A246600Partition

/- The exact residue count for divisors that are binary submasks of their multiples. -/
namespace A246600Residues

open Finset Filter Topology
open OMA.S_oeis_a246600

private def ind (d y : ℕ) : ℕ := if d &&& y = d then 1 else 0

private def supers (h d : ℕ) : ℕ := ∑ y ∈ range (2^h), ind d y

private def row (h d : ℕ) : ℕ := ∑ k ∈ range (2^h), ind d (d*k)

private theorem even_odd_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ∑ i ∈ range (2*n), f i = ∑ j ∈ range n, (f (2*j)+f (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih, add_assoc]

private theorem and_ee (a b : ℕ) : (2*a) &&& (2*b) = 2*(a &&& b) := by
  simpa only [Nat.bit_false, Bool.false_and] using Nat.land_bit false a false b

private theorem and_eo (a b : ℕ) : (2*a) &&& (2*b+1) = 2*(a &&& b) := by
  simpa only [Nat.bit_false, Nat.bit_true, Bool.false_and] using Nat.land_bit false a true b

private theorem and_oo (a b : ℕ) : (2*a+1) &&& (2*b+1) = 2*(a &&& b)+1 := by
  simpa only [Nat.bit_true, Bool.true_and] using Nat.land_bit true a true b

private theorem ind_even (a b : ℕ) :
    ind (2*a) (2*b) = ind a b ∧ ind (2*a) (2*b+1) = ind a b := by
  simp [ind,and_ee,and_eo]

private theorem ind_odd (a b : ℕ) :
    ind (2*a+1) (2*b) = 0 ∧ ind (2*a+1) (2*b+1) = ind a b := by
  have he : (2*a+1) &&& (2*b) = 2*(b &&& a) := by rw [Nat.and_comm,and_eo]
  have hn : 2*(b &&& a) ≠ 2*a+1 := by omega
  simp [ind,he,hn,and_oo]

private theorem supers_even (h a : ℕ) : supers (h+1) (2*a) = 2*supers h a := by
  unfold supers
  rw [pow_succ',even_odd_sum]
  simp only [ind_even, sum_add_distrib]
  rw [two_mul]

private theorem supers_odd (h a : ℕ) : supers (h+1) (2*a+1) = supers h a := by
  simp only [supers,pow_succ',even_odd_sum,ind_odd,zero_add]

private theorem low_ind (h d y : ℕ) (hd : d<2^h) :
    ind d (y%2^h) = ind d y := by
  have eq := Nat.and_mod_two_pow (a:=d) (b:=y) (n:=h)
  rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt (Nat.and_le_left.trans_lt hd)] at eq
  simp [ind,eq]

private theorem periodic_ind (h d k : ℕ) (hd : d<2^h) :
    ind d (d*(k+2^h)) = ind d (d*k) := by
  rw [←low_ind h d _ hd, Nat.mul_add, Nat.add_mul_mod_self_right,low_ind h d _ hd]

private theorem row_odd (h d : ℕ) (hd : d<2^h) (ho : Odd d) : row h d=supers h d := by
  let f : Fin (2^h) → Fin (2^h) := fun x => ⟨d*x.val % 2^h, Nat.mod_lt _ (by positivity)⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : d*a.val ≡ d*b.val [MOD 2^h] := congrArg Fin.val hab
    apply Fin.ext
    exact (Nat.ModEq.cancel_left_of_coprime (((Nat.coprime_two_left.mpr ho).pow_left h)) hab').eq_of_lt_of_lt a.isLt b.isLt
  let e := Equiv.ofBijective f ⟨hf, Finite.surjective_of_injective hf⟩
  have he := e.sum_comp (fun x : Fin (2^h) => ind d x.val)
  change (∑ i : Fin (2^h), ind d ((d*i.val)%2^h)) = ∑ i : Fin (2^h), ind d i.val at he
  simp only [low_ind h d _ hd] at he
  unfold row supers
  rw [←Fin.sum_univ_eq_sum_range (fun k => ind d (d*k)), ←Fin.sum_univ_eq_sum_range (ind d)]
  exact he

private theorem row_eq_supers (h d : ℕ) (hd : d<2^h) : row h d=supers h d := by
  induction h generalizing d with
  | zero =>
    obtain rfl : d=0 := by simpa using hd
    simp [row,supers,ind]
  | succ h ih =>
    rcases Nat.even_or_odd d with ⟨a,ha⟩ | ho
    · rw [show d=2*a by omega] at hd ⊢
      have ha' : a<2^h := by rw [pow_succ'] at hd; omega
      rw [supers_even,←ih a ha']
      simp only [row,pow_succ, Nat.mul_two, sum_range_add]
      simp only [Nat.mul_assoc, (ind_even _ _).1]
      rw [two_mul]
      congr 1
      apply sum_congr rfl
      intro k _
      rw [Nat.add_comm,periodic_ind h a k ha']
    · exact row_odd _ _ hd ho

private theorem row_weight (h d : ℕ) (hd : d<2^h) :
    row h d * 2^d.bitIndices.length = 2^h := by
  rw [row_eq_supers h d hd]
  induction h generalizing d with
  | zero =>
    obtain rfl : d=0 := by simpa using hd
    simp [supers,ind]
  | succ h ih =>
    rcases Nat.even_or_odd d with ⟨a,ha⟩ | ⟨a,ha⟩
    · rw [show d=2*a by omega] at hd ⊢
      have ha' : a<2^h := by rw [pow_succ'] at hd; omega
      simp only [supers_even,Nat.bitIndices_two_mul,List.length_map,mul_assoc,ih a ha',pow_succ']
    · rw [show d=2*a+1 by omega] at hd ⊢
      have ha' : a<2^h := by rw [pow_succ'] at hd; omega
      simp only [supers_odd,Nat.bitIndices_two_mul_add_one,List.length_cons,List.length_map,pow_succ]
      rw [←mul_assoc,ih a ha']

private theorem sum_supers (h : ℕ) : ∑ d ∈ range (2^h), supers h d = 3^h := by
  induction h with
  | zero => simp [supers,ind]
  | succ h ih =>
    rw [pow_succ',even_odd_sum]
    simp only [supers_even,supers_odd]
    simp_rw [show ∀ x : ℕ, 2*x+x=3*x by omega]
    rw [←mul_sum,ih,pow_succ']

theorem pair_count (h : ℕ) :
    (∑ d ∈ range (2^h), ((range (2^h)).filter (fun k => d &&& ((d*k)%2^h) = d)).card) = 3^h := by
  rw [←sum_supers]
  apply sum_congr rfl
  intro d hd
  have hlt := mem_range.mp hd
  rw [←row_eq_supers h d hlt,card_filter]
  change (∑ k ∈ range (2^h), ind d ((d*k)%2^h))=_
  simp only [low_ind h d _ hlt,row]

theorem truncate (h d k : ℕ) (hc : d &&& (d*k) = d) :
    (d%2^h) &&& (((d%2^h)*(k%2^h))%2^h) = d%2^h := by
  rw [←Nat.mul_mod,←Nat.and_mod_two_pow,hc]


theorem square_bound (h u v : ℕ) :
    ((((Ico (u*2^h) ((u+1)*2^h)).product (Ico (v*2^h) ((v+1)*2^h))).filter
      (fun p => p.1 &&& (p.1*p.2) = p.1)).card) ≤ 3^h := by
  rw [←pair_count h,Finset.product_eq_sprod,card_filter,sum_product]
  simp only [sum_Ico_eq_sum_range,Nat.add_mul,one_mul,Nat.add_sub_cancel_left]
  refine sum_le_sum (fun d hd => ?_)
  rw [card_filter]
  refine sum_le_sum (fun k hk => ?_)
  have hd := mem_range.mp hd
  have hk := mem_range.mp hk
  split_ifs with h1 h2
  · exact le_rfl
  · have hh := truncate h (u*2^h+d) (v*2^h+k) (by simpa only [Nat.add_mul] using h1)
    simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hk] at hh
    exact False.elim (h2 hh)
  · omega
  · omega


private theorem div_ratio (L : ℕ) (hL : 0<L) :
    Tendsto (fun N : ℕ => ((N/L:ℕ):ℝ)/(N:ℝ)) atTop (𝓝 (1/(L:ℝ))) := by
  have hz := tendsto_mod_div_atTop_nhds_zero_nat hL
  have h := ((tendsto_const_nhds (x:=(1:ℝ))).sub hz).div_const (L:ℝ)
  rw [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hn
  have hN : (N:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hP : (L:ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have eq : (↑(N%L):ℝ)+(L:ℝ)*↑(N/L) = N := by exact_mod_cast Nat.mod_add_div N L
  field_simp
  linarith

theorem fixed_divisor (d : ℕ) (hd : 0<d) :
    Tendsto (fun N : ℕ =>
      (((Icc 2 (N/d)).filter (fun k => d &&& (d*k) = d)).card : ℝ)/(N:ℝ))
      atTop (𝓝 (weight d)) := by
  let h := d+1
  let Q := 2^h
  have hQ : 0<Q := by dsimp [Q]; positivity
  have hlt : d < Q := by exact Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ d))
  let C := row h d
  let f := fun k => ind d (d*k)
  let F := fun l => ∑ k ∈ range l, f k
  have period (t k : ℕ) : f (t*Q+k) = f k := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul,show t*Q+Q+k=(t*Q+k)+Q by omega]
      exact (periodic_ind h d _ hlt).trans ih
  have blocks (t : ℕ) : F (t*Q) = t*C := by
    induction t with
    | zero => simp [F]
    | succ t ih =>
      have he := sum_range_add f (t*Q) Q
      simp only [period] at he
      change F (t*Q+Q) = F (t*Q)+C at he
      rw [Nat.succ_mul,he,ih,Nat.succ_mul]
  have mono : Monotone F := by
    intro a b hab
    apply sum_le_sum_of_subset
    exact range_mono hab
  let g := fun N => ((Icc 2 (N/d)).filter (fun k => d &&& (d*k) = d)).card
  let m := fun N => N/(d*Q)
  have bounds (N : ℕ) (hN : d≤N) : m N*C ≤ g N+F 2 ∧ g N ≤ (m N+1)*C := by
    have hk : 0<N/d := Nat.div_pos hN hd
    have hm : m N = N/d/Q := (Nat.div_div_eq_div_mul ..).symm
    have low : m N*Q ≤ N/d+1 := (hm ▸ Nat.div_mul_le_self _ _).trans (Nat.le_succ _)
    have high : N/d+1 ≤ (m N+1)*Q := by
      rw [hm,Nat.succ_mul]
      have eq := Nat.mod_add_div (N/d) Q
      have hr := Nat.mod_lt (N/d) hQ
      rw [Nat.mul_comm Q] at eq
      omega
    have hI : Icc 2 (N/d) = Ico 2 (N/d+1) := by ext x; simp
    have hF : F 2 + g N = F (N/d+1) := by
      simpa only [F,g,hI,card_filter,f,ind] using
        sum_range_add_sum_Ico f (show 2≤N/d+1 by omega)
    have hlo := mono low
    have hhi := mono high
    rw [blocks,←hF] at hlo
    rw [blocks,←hF] at hhi
    omega
  have hD : 0<d*Q := Nat.mul_pos hd hQ
  have hcoef : (1/((d*Q:ℕ):ℝ))*(C:ℝ) = weight d := by
    have hw : (C:ℝ) * 2^d.bitIndices.length = Q := by exact_mod_cast row_weight h d hlt
    unfold weight
    push_cast
    have hd' : (d:ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    have hq' : (Q:ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
    field_simp
    nlinarith
  have hbase := (div_ratio (d*Q) hD).mul_const (C:ℝ)
  rw [hcoef] at hbase
  have hlo := hbase.sub (tendsto_const_div_atTop_nhds_zero_nat (F 2:ℝ))
  have hhi := hbase.add (tendsto_const_div_atTop_nhds_zero_nat (C:ℝ))
  rw [sub_zero] at hlo
  rw [add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop d] with N hN
    have lo : (m N:ℝ)*C ≤ g N+F 2 := by exact_mod_cast (bounds N hN).1
    change ((m N:ℝ)/(N:ℝ))*C - F 2/(N:ℝ) ≤ (g N:ℝ)/N
    rw [div_mul_eq_mul_div,←sub_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)
  · filter_upwards [eventually_ge_atTop d] with N hN
    have hi : (g N:ℝ) ≤ ((m N:ℝ)+1)*C := by exact_mod_cast (bounds N hN).2
    change (g N:ℝ)/N ≤ ((m N:ℝ)/(N:ℝ))*C + C/(N:ℝ)
    rw [div_mul_eq_mul_div,←add_div]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

end A246600Residues

namespace A246600Fixed

open Finset Filter Topology

private def valid (k c x : ℕ) : Prop := x &&& (k*x+c) = x
private instance (k c x : ℕ) : Decidable (valid k c x) := inferInstanceAs (Decidable (_ = _))

private def tally (k c n : ℕ) := ∑ x ∈ range n, if valid k c x then 1 else 0

private theorem digit_step {k c B s a b : ℕ} (hB : B = 2^s) (hb : b < B)
    (h : valid k c (B*a+b)) : b ≤ (k*b+c)%B ∧ valid k ((k*b+c)/B) a := by
  have hpos : 0 < B := by omega
  have expand : k*(B*a+b)+c = B*(k*a)+(k*b+c) := by ring
  unfold valid at h ⊢
  rw [expand] at h
  have lo := congrArg (fun z : ℕ => z % B) h
  change ((_ &&& _) % B) = _ at lo
  rw [hB, Nat.and_mod_two_pow, ←hB, Nat.mul_add_mod, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hb] at lo
  have hi := congrArg (fun z : ℕ => z >>> s) h
  change ((_ &&& _) >>> s) = _ at hi
  rw [Nat.shiftRight_and_distrib] at hi
  simp only [Nat.shiftRight_eq_div_pow, ← hB,
    Nat.mul_add_div hpos, Nat.div_eq_of_lt hb, Nat.add_zero] at hi
  exact ⟨lo.ge.trans Nat.and_le_right, hi⟩

private theorem carry_lt {k c B b : ℕ} (hc : c < k) (hb : b < B) :
    (k*b+c)/B < k := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < B)).2
  calc k*b+c < k*(b+1) := by rw [Nat.mul_succ]; omega
       _ ≤ k*B := Nat.mul_le_mul_left k hb

/-- The digit with low half zero and high half all ones cannot survive multiplication. -/
private theorem forbidden {k c q : ℕ} (hk : 2 ≤ k) (hq : k < q) (hc : c < k) :
    (k*(q*(q-1))+c) % (q*q) < q*(q-1) := by
  have h1 : 1 ≤ q := by omega
  have hkq : k ≤ q := by omega
  have h1k : 1 ≤ k := by omega
  have hpos : 0 < q := by omega
  have hsplit : k*(q*(q-1))+c = (q*q)*(k-1)+(q*(q-k)+c) := by
    zify [h1, hkq, h1k]
    ring
  have hlt : q*(q-k)+c < q*(q-1) := calc
    q*(q-k)+c < q*((q-k)+1) := by rw [Nat.mul_succ]; omega
    _ ≤ q*(q-1) := Nat.mul_le_mul_left q (by omega)
  have hb : q*(q-1) < q*q := Nat.mul_lt_mul_of_pos_left (by omega) hpos
  rwa [hsplit, Nat.mul_add_mod, Nat.mod_eq_of_lt (hlt.trans hb)]

private theorem radix_sum (B n : ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ range (B*n), f x = ∑ b ∈ range B, ∑ a ∈ range n, f (B*a+b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp only [sum_range_succ, sum_add_distrib]

private theorem tally_pow {k q B : ℕ} (hk : 2 ≤ k) (hq : k < q)
    (hB : B=q*q) (s : ℕ) (hpow : B=2^s) (j : ℕ) :
    ∀ c < k, tally k c (B^j) ≤ (B-1)^j := by
  have hbad : q*(q-1) < B := by rw [hB]; apply Nat.mul_lt_mul_of_pos_left <;> omega
  have hmem : q*(q-1) ∈ range B := mem_range.mpr hbad
  induction j with
  | zero => simp [tally, valid]
  | succ j ih =>
    intro c hc
    rw [pow_succ', tally, radix_sum, ← sum_erase_add _ _ hmem]
    have hz : (∑ a ∈ range (B^j), if valid k c (B*a+q*(q-1)) then 1 else 0) = 0 := by
      apply sum_eq_zero
      intro a _
      apply if_neg
      intro h
      have hlo := (digit_step hpow hbad h).1
      rw [hB] at hlo
      exact (forbidden hk hq hc).not_ge hlo
    rw [hz, add_zero]
    calc
      _ ≤ ∑ _b ∈ (range B).erase (q*(q-1)), (B-1)^j := by
        apply sum_le_sum
        intro b hb
        have hb' := mem_range.mp (mem_of_mem_erase hb)
        apply le_trans _ (ih ((k*b+c)/B) (carry_lt hc hb'))
        unfold tally
        apply sum_le_sum
        intro a _
        by_cases h : valid k c (B*a+b)
        · simp [h, (digit_step hpow hb' h).2]
        · simp [h]
      _ = (B-1)^(j+1) := by simp [card_erase_of_mem hmem, pow_succ']

/-- For a fixed multiplier greater than one the divisors passing the binary mask have density zero. -/
theorem fixed_multiplier_density (k : ℕ) (hk : 2 ≤ k) :
    Tendsto (fun N : ℕ => (((Icc 1 N).filter (fun d => d &&& (d*k) = d)).card : ℝ)/(N:ℝ))
      atTop (𝓝 0) := by
  let q := 2^k
  let B := q*q
  have hq : k < q := Nat.lt_two_pow_self
  have hB : 1 < B := by dsimp [B]; nlinarith
  have hpow : B = 2^(k+k) := by simp [B, q, pow_add]
  have hlog : Tendsto (Nat.log B) atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (B^j)] with N hN
    have hpos : 0 < B^j := pow_pos (by omega) _
    exact (Nat.le_log_iff_pow_le hB (by omega)).2 hN
  let r : ℝ := ((B-1 : ℕ) : ℝ)/(B:ℝ)
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hr₀ : 0 ≤ r := by dsimp [r]; positivity
  have hr₁ : r < 1 := by
    dsimp [r]
    rw [div_lt_one hBr]
    exact_mod_cast (show B-1 < B by omega)
  have hlim : Tendsto (fun N : ℕ => ((B-1 : ℕ) : ℝ)*r^(Nat.log B N)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁).comp hlog).const_mul
      ((B-1 : ℕ) : ℝ)
  apply squeeze_zero' (.of_forall (fun n => by positivity)) _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  let j := Nat.log B N
  have hj₁ : B^j ≤ N := Nat.pow_log_le_self _ (by omega)
  have hj₂ : N < B^(j+1) := Nat.lt_pow_succ_log_self hB _
  have hcount : ((Icc 1 N).filter (fun d => d &&& (d*k) = d)).card ≤ (B-1)^(j+1) := by
    apply le_trans _ (tally_pow hk hq (rfl : B=q*q) _ hpow (j+1) 0 (by omega))
    unfold tally
    rw [← Finset.card_filter]
    apply card_le_card
    intro d hd
    obtain ⟨hd, he⟩ := mem_filter.mp hd
    exact mem_filter.mpr ⟨mem_range.mpr (lt_of_le_of_lt (mem_Icc.mp hd).2 hj₂),
      by simpa [valid, Nat.mul_comm] using he⟩
  have hp : 0 < (B:ℝ)^j := pow_pos hBr _
  calc
    _ ≤ ((B-1 : ℕ) : ℝ)^(j+1)/(B:ℝ)^j := by
      apply div_le_div₀ (by positivity) (by exact_mod_cast hcount) hp (by exact_mod_cast hj₁)
    _ = ((B-1 : ℕ) : ℝ)*r^j := by rw [pow_succ', mul_div_assoc, ← div_pow]

end A246600Fixed

/- Dyadic truncation by the smaller coordinate in the lattice hyperbola. -/

namespace A246600Middle
open Finset

private def box (h u v : ℕ) : Finset (ℕ × ℕ) :=
  ((Ico (u*2^h) ((u+1)*2^h)) ×ˢ (Ico (v*2^h) ((v+1)*2^h))).filter
    (fun p : ℕ × ℕ => p.1 &&& (p.1*p.2) = p.1)

private def layer (N h : ℕ) : Finset (ℕ × ℕ) :=
  if 4^h ≤ N then
    (range (N/4^h+1)).biUnion (fun b => box h 1 b ∪ box h b 1)
  else ∅

private lemma side_sq (h : ℕ) : 4^h = ((2:ℕ)^h)^2 := by
  rw [← pow_mul,Nat.mul_comm, pow_mul]
  norm_num

private lemma place (N h d k : ℕ) (hd : d ∈ Ico (2^h) (2*2^h)) (hp : d*k≤N) :
    k/2^h ∈ range (N/4^h+1) ∧ k ∈ Ico ((k/2^h)*2^h) ((k/2^h+1)*2^h) := by
  have tpos : 0 < (2:ℕ)^h := by positivity
  have hdiv := Nat.div_mul_le_self k (2^h)
  have hb : k/2^h ≤ N/4^h := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    rw [side_sq]
    calc
      _ = 2^h*((k/2^h)*2^h) := by ring
      _ ≤ 2^h*k := Nat.mul_le_mul_left _ hdiv
      _ ≤ d*k := Nat.mul_le_mul_right _ (mem_Ico.mp hd).1
      _ ≤ _ := hp
  exact ⟨mem_range.mpr (by omega),mem_Ico.mpr
    ⟨hdiv,(Nat.div_lt_iff_lt_mul tpos).mp (Nat.lt_succ_self _)⟩⟩

private theorem covered (N H : ℕ) :
    ((Icc (2^H) N ×ˢ Icc (2^H) N).filter
      (fun p : ℕ × ℕ => p.1*p.2≤N ∧ p.1 &&& (p.1*p.2)=p.1)) ⊆
      (Ico H (N+1)).biUnion (layer N) := by
  rintro ⟨d,k⟩ h
  obtain ⟨hin,hp,hb⟩ := mem_filter.mp h
  obtain ⟨hd,hk⟩ := mem_product.mp hin
  obtain ⟨hdH,hdN⟩ := mem_Icc.mp hd
  obtain ⟨hkH,hkN⟩ := mem_Icc.mp hk
  let v := min d k
  let j := Nat.log 2 v
  have hvH : 2^H ≤ v := le_min hdH hkH
  have hv : 0<v := lt_of_lt_of_le (by positivity) hvH
  have ht : 2^j ≤ v := Nat.pow_log_le_self _ hv.ne'
  have hL : v < 2*2^j := by
    simpa only [pow_succ',j] using Nat.lt_pow_succ_log_self (by decide : 1<2) v
  have hvI : v ∈ Ico (2^j) (2*2^j) := mem_Ico.mpr ⟨ht,hL⟩
  have hj : H≤j := (Nat.le_log_iff_pow_le (by decide) hv.ne').mpr hvH
  have hjn : j≤N := (Nat.log_le_self _ _).trans ((min_le_left d k).trans hdN)
  have hsmall : 4^j ≤ N := by
    rw [side_sq,pow_two]
    exact (Nat.mul_le_mul (ht.trans (min_le_left d k)) (ht.trans (min_le_right d k))).trans hp
  apply mem_biUnion.mpr
  refine ⟨j,mem_Ico.mpr ⟨hj,by omega⟩,?_⟩
  rw [layer,if_pos hsmall]
  rcases le_total d k with he | he
  · rw [show v=d from min_eq_left he] at hvI
    obtain ⟨hq,hi⟩ := place N j d k hvI hp
    apply mem_biUnion.mpr
    refine ⟨_,hq,mem_union_left _ (mem_filter.mpr ⟨mem_product.mpr ⟨?_,hi⟩,hb⟩)⟩
    simpa only [one_mul,one_add_one_eq_two] using hvI
  · rw [show v=k from min_eq_right he] at hvI
    obtain ⟨hq,hi⟩ := place N j k d hvI (by simpa only [Nat.mul_comm] using hp)
    apply mem_biUnion.mpr
    refine ⟨_,hq,mem_union_right _ (mem_filter.mpr ⟨mem_product.mpr ⟨hi,?_⟩,hb⟩)⟩
    simpa only [one_mul,one_add_one_eq_two] using hvI

private theorem layer_bound (bh : ∀ h u v, (box h u v).card ≤ 3^h) (N h : ℕ) :
    ((layer N h).card:ℝ) ≤ 4*(N:ℝ)*(3/4:ℝ)^h := by
  by_cases hs : 4^h ≤ N
  · have hon : 1≤N/4^h := (Nat.le_div_iff_mul_le (by positivity)).mpr (by simpa using hs)
    have hnat : (layer N h).card ≤ 4*(N/4^h)*3^h := by
      rw [layer,if_pos hs]
      calc
        _ ≤ ∑ b ∈ range (N/4^h+1), (box h 1 b ∪ box h b 1).card := card_biUnion_le
        _ ≤ ∑ _b ∈ range (N/4^h+1), (2*3^h) := by
          apply sum_le_sum
          intro b _
          have hh := (card_union_le (box h 1 b) (box h b 1)).trans (Nat.add_le_add (bh h 1 b) (bh h b 1))
          omega
        _ = (N/4^h+1)*(2*3^h) := by simp
        _ ≤ (2*(N/4^h))*(2*3^h) := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    have hdiv : (((N/4^h:ℕ):ℝ)) ≤ (N:ℝ)/(4:ℝ)^h := by
      apply (le_div_iff₀ (by positivity)).mpr
      exact_mod_cast Nat.div_mul_le_self N (4^h)
    calc
      _ ≤ 4*((N/4^h:ℕ):ℝ)*(3:ℝ)^h := by exact_mod_cast hnat
      _ ≤ 4*((N:ℝ)/(4:ℝ)^h)*(3:ℝ)^h := by gcongr
      _ = _ := by rw [div_pow]; ring
  · rw [layer,if_neg hs,card_empty,Nat.cast_zero]
    positivity

/-- An aligned-square bound of three choices per binary digit suffices uniformly
for all pairs whose two coordinates are at least the cutoff. -/
theorem of_boxes
    (bh : ∀ h u v : ℕ,
      (((Ico (u*2^h) ((u+1)*2^h)) ×ˢ (Ico (v*2^h) ((v+1)*2^h))).filter
      (fun p : ℕ × ℕ => p.1 &&& (p.1*p.2) = p.1)).card ≤ 3^h)
    (N H : ℕ) :
    (((Icc (2^H) N ×ˢ Icc (2^H) N).filter
      (fun p : ℕ × ℕ => p.1*p.2≤N ∧ p.1 &&& (p.1*p.2)=p.1)).card : ℝ) ≤
      16*(N:ℝ)*(3/4:ℝ)^H := by
  have hb := layer_bound bh N
  have hnat := (card_le_card (covered N H)).trans card_biUnion_le
  have hg := geom_sum_Ico_le_of_lt_one (m:=H) (n:=N+1)
    (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)<1)
  calc
    _ ≤ ∑ h ∈ Ico H (N+1), ((layer N h).card:ℝ) := by exact_mod_cast hnat
    _ ≤ ∑ h ∈ Ico H (N+1), 4*(N:ℝ)*(3/4:ℝ)^h := sum_le_sum (fun h _ => hb h)
    _ = 4*(N:ℝ)* ∑ h ∈ Ico H (N+1), (3/4:ℝ)^h := by rw [mul_sum]
    _ ≤ 4*(N:ℝ)*((3/4:ℝ)^H/(1-3/4)) := by gcongr
    _ = _ := by ring

/-- Uniform truncation error when both the divisor and multiplier are at least a power of two. -/
theorem middle_bound (N H : ℕ) :
    (((Icc (2^H) N ×ˢ Icc (2^H) N).filter
      (fun p : ℕ × ℕ => p.1*p.2≤N ∧ p.1 &&& (p.1*p.2)=p.1)).card : ℝ) ≤
      16*(N:ℝ)*(3/4:ℝ)^H :=
  of_boxes A246600Residues.square_bound N H

end A246600Middle

/- The total reciprocal-popcount mass of all h-bit words is (3/2)^h.
This gives a summable geometric majorant for the weights on dyadic intervals. -/

namespace A246600Summability
open Finset OMA.S_oeis_a246600

private noncomputable def mass (d : ℕ) : ℝ := (1/2:ℝ)^d.bitIndices.length

private theorem mass_nonneg (d : ℕ) : 0 ≤ mass d := by unfold mass; positivity

private theorem even_odd (n : ℕ) :
    ∑ i ∈ range (2*n), mass i = ∑ j ∈ range n, (mass (2*j)+mass (2*j+1)) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ,sum_range_succ,sum_range_succ,sum_range_succ,ih,add_assoc]

theorem mass_range (h : ℕ) : ∑ i ∈ range (2^h), mass i = (3/2:ℝ)^h := by
  induction h with
  | zero => simp [mass]
  | succ h ih =>
    rw [pow_succ',even_odd,show (3/2:ℝ)^(h+1)=(3/2)*(3/2)^h by ring,← ih,mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [mass,Nat.bitIndices_two_mul,Nat.bitIndices_two_mul_add_one,
      List.length_map,List.length_cons,pow_succ]
    ring

private theorem mass_interval (h : ℕ) :
    ∑ i ∈ Ico (2^h) (2^(h+1)), mass i = (1/2:ℝ)*(3/2)^h := by
  have he : (2:ℕ)^h ≤ 2^(h+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have eq := sum_range_add_sum_Ico mass he
  rw [mass_range,mass_range,pow_succ (3/2:ℝ) h] at eq
  linarith

theorem weight_nonneg (d : ℕ) : 0 ≤ weight d := by unfold weight; positivity

theorem weight_interval (h : ℕ) :
    ∑ d ∈ Ico (2^h) (2^(h+1)), weight d ≤ (1/2:ℝ)*(3/4)^h := by
  calc
    _ ≤ ∑ d ∈ Ico (2^h) (2^(h+1)), (1/(2:ℝ)^h)*mass d := by
      apply sum_le_sum
      intro d hd
      have hle : (2:ℝ)^h ≤ (d:ℝ) := by exact_mod_cast (mem_Ico.mp hd).1
      have hr : 0 < (2:ℝ)^h := by positivity
      have hb : 1/(d:ℝ) ≤ 1/(2:ℝ)^h := one_div_le_one_div_of_le hr hle
      have hm := mul_le_mul_of_nonneg_right hb (mass_nonneg d)
      simpa only [weight,mass,one_div,mul_inv_rev, inv_pow, mul_comm] using hm
    _ = _ := by
      rw [← mul_sum,mass_interval]
      calc
        _ = (1/2:ℝ)*((1/2)^h*(3/2)^h) := by rw [div_pow (1:ℝ) 2 h,one_pow]; ring
        _ = _ := by rw [←mul_pow]; norm_num

private theorem dyadic_partial (h : ℕ) :
    ∑ d ∈ range (2^h), weight d ≤ 2*(1-(3/4:ℝ)^h) := by
  induction h with
  | zero => simp [weight]
  | succ h ih =>
    have he : (2:ℕ)^h ≤ 2^(h+1) := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← sum_range_add_sum_Ico weight he,pow_succ (3/4:ℝ) h]
    linarith [weight_interval h]

/-- The desired series of weights on the positive integers converges. -/
theorem weight_summable : Summable (fun k : ℕ => weight (k+1)) := by
  apply summable_of_sum_range_le (c:=2) (fun _ => weight_nonneg _)
  intro n
  have hzero : weight 0 = 0 := by simp [weight]
  have e : ∑ i ∈ range (n+1), weight i = ∑ i ∈ range n, weight (i+1) := by
    rw [sum_range_succ',hzero,add_zero]
  rw [←e]
  have he : n+1 ≤ (2:ℕ)^(n+1) := (n+1).lt_two_pow_self.le
  have hsub := sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr he)
    (fun i _ _ => weight_nonneg i)
  have pos : 0 ≤ (3/4:ℝ)^(n+1) := by positivity
  exact hsub.trans ((dyadic_partial (n+1)).trans (by linarith))

open Filter Topology

/-- The partial masses used in the hyperbola decomposition converge to the full series. -/
theorem weight_partial_limit : Tendsto
    (fun H : ℕ => ∑ d ∈ Ico 1 (2^H), weight d) atTop (𝓝 (∑' k : ℕ, weight (k+1))) := by
  have ht : Tendsto (fun H : ℕ => 2^H-1) atTop atTop := by
    refine tendsto_atTop.mpr (fun b => ?_)
    filter_upwards [eventually_ge_atTop b] with H hH
    have hm := H.lt_two_pow_self
    omega
  have h := weight_summable.hasSum.tendsto_sum_nat.comp ht
  apply h.congr'
  filter_upwards [] with H
  simp only [Function.comp_apply,sum_Ico_eq_sum_range,Nat.add_comm 1]

end A246600Summability

/- Take the cutoff to infinity after evaluating the two finite bands. -/

namespace A246600Finish

open Finset Filter Topology OMA.S_oeis_a246600
open A246600Counts A246600Partition A246600Residues A246600Fixed
open A246600Middle A246600Summability

private noncomputable def lower (H N : ℕ) : ℝ :=
  (∑ d ∈ Ico 1 (2^H), ((divisorRow N d).card : ℝ)) / (N:ℝ)

private noncomputable def side (H N : ℕ) : ℝ :=
  (∑ k ∈ Ico 2 (2^H), ((multiplierRow N k).card : ℝ)) / (N:ℝ)

private noncomputable def properMean (N : ℕ) : ℝ :=
  ((properPairs N).card : ℝ) / (N:ℝ)

private theorem lower_limit (H : ℕ) :
    Tendsto (lower H) atTop (𝓝 (∑ d ∈ Ico 1 (2^H), weight d)) := by
  have ht := tendsto_finsetSum (Ico 1 (2^H))
    (fun d hd => fixed_divisor d (mem_Ico.mp hd).1)
  unfold lower
  simpa only [divisorRow, sum_div] using ht

private theorem side_limit (H : ℕ) : Tendsto (side H) atTop (𝓝 0) := by
  have ht := tendsto_finsetSum (Ico 2 (2^H))
    (fun k hk => fixed_multiplier_density k (mem_Ico.mp hk).1)
  unfold side
  simpa only [multiplierRow, sum_div, sum_const_zero] using ht

private theorem mean_bounds (H : ℕ) :
    ∀ᶠ N in atTop, lower H N ≤ properMean N ∧
      properMean N ≤ lower H N + side H N + 16*(3/4:ℝ)^H := by
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hpos : (0:ℝ) < N := by exact_mod_cast hN
  obtain ⟨hlo,hhi⟩ := bounds N (2^H)
  have htail : ((tailPairs N (2^H)).card : ℝ) / (N:ℝ) ≤ 16*(3/4:ℝ)^H := by
    apply (div_le_iff₀ hpos).mpr
    calc
      _ ≤ 16*(N:ℝ)*(3/4:ℝ)^H := middle_bound N H
      _ = _ := by ring
  constructor
  · unfold lower properMean
    apply div_le_div_of_nonneg_right _ hpos.le
    exact_mod_cast hlo
  · calc
      properMean N ≤ lower H N + side H N + ((tailPairs N (2^H)).card : ℝ) / (N:ℝ) := by
        simp only [properMean,lower,side,←add_div]
        apply div_le_div_of_nonneg_right _ hpos.le
        exact_mod_cast hhi
      _ ≤ _ := add_le_add_right htail _

private theorem proper_limit : Tendsto properMean atTop (𝓝 (∑' k, weight (k+1))) := by
  let a (H : ℕ) := ∑ d ∈ Ico 1 (2^H), weight d
  let e (H : ℕ) : ℝ := 16*(3/4:ℝ)^H
  have ha : Tendsto a atTop (𝓝 (∑' k, weight (k+1))) := weight_partial_limit
  have he : Tendsto e atTop (𝓝 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0:ℝ) ≤ 3/4) (by norm_num : (3:ℝ)/4 < 1)).const_mul 16
    simpa only [e,mul_zero] using hg
  have hae := ha.add he
  rw [add_zero] at hae
  apply tendsto_order.mpr
  constructor
  · intro x hx
    obtain ⟨H,hH⟩ := ((tendsto_order.mp ha).1 x hx).exists
    filter_upwards [(tendsto_order.mp (lower_limit H)).1 x hH,mean_bounds H] with N hN hb
    exact hN.trans_le hb.1
  · intro x hx
    obtain ⟨H,hH⟩ := ((tendsto_order.mp hae).2 x hx).exists
    have ht := ((lower_limit H).add (side_limit H)).add_const (e H)
    rw [add_zero] at ht
    filter_upwards [(tendsto_order.mp ht).2 x hH,mean_bounds H] with N hN hb
    exact hb.2.trans_lt hN

theorem conclusion :
    Tendsto (fun N : ℕ => (∑ k ∈ range N, (term (k+1) : ℝ)) / N)
      atTop (𝓝 (1 + ∑' k : ℕ, weight (k+1))) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add proper_limit
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with N hN
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  change 1 + properMean N = _
  rw [←Nat.cast_sum,←all_pairs_sum,all_pairs_split,Nat.cast_add,add_div,div_self hn] <;> rfl

end A246600Finish

theorem OMA.solution : type_of% @OMA.S_oeis_a246600.main :=
  ⟨A246600Summability.weight_summable,A246600Finish.conclusion⟩
