import OMAStatements.S_oeis_a366562

namespace SquareWeights
open Finset OMA.S_oeis_a366562

noncomputable def atom (p x y : ℕ) : ℚ :=
  if (x : ZMod p)^2 = (y : ZMod p)^2 then 1-(p : ℚ) else 1

noncomputable def weight (n x y : ℕ) : ℚ := ∏ p ∈ n.primeFactors, atom p x y

noncomputable def total (n : ℕ) [NeZero n] : ℚ :=
  ∑ x : ZMod n, ∑ y : ZMod n, weight n x.val y.val

lemma weight_gcd (n x y : ℕ) (hn : n≠0) :
    (A023900 (Int.gcd ((x : ℤ)^2-(y : ℤ)^2) n) : ℚ) = weight n x y := by
  let D : ℤ := (x : ℤ)^2-(y : ℤ)^2
  have hpos := Int.gcd_pos_of_ne_zero_right D (by exact_mod_cast hn : (n : ℤ)≠0)
  have pd (p : ℕ) : (p : ℤ)∣D ↔ (x : ZMod p)^2 = (y : ZMod p)^2 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simp [D,sub_eq_zero]
  have gf : (D.gcd n).primeFactors =
      n.primeFactors.filter (fun p => (x : ZMod p)^2=(y : ZMod p)^2) := by
    ext p
    rw [mem_filter,Nat.mem_primeFactors,Nat.mem_primeFactors]
    constructor
    · rintro ⟨prime,dp,_⟩
      have h : (p : ℤ)∣(D.gcd n : ℤ) := by exact_mod_cast dp
      have hn' := h.trans (Int.gcd_dvd_right D n)
      exact ⟨⟨prime,by exact_mod_cast hn',hn⟩,(pd p).1 (h.trans (Int.gcd_dvd_left D n))⟩
    · rintro ⟨⟨prime,hn',_⟩,hq⟩
      exact ⟨prime,Int.dvd_gcd ((pd p).2 hq) (by exact_mod_cast hn'),hpos.ne'⟩
  change (↑(∏ p ∈ (D.gcd n).primeFactors, (1-(p:ℤ))) : ℚ) = _
  simp only [Int.cast_prod,Int.cast_sub,Int.cast_one,Int.cast_natCast,gf,prod_filter,weight,atom]
  apply prod_congr rfl
  intro p _
  split_ifs <;> push_cast <;> rfl

lemma residue_val {n p : ℕ} [NeZero n] (hp : p ∣ n) (x : ℕ) :
    (((x : ZMod n).val : ℕ) : ZMod p) = x := by
  let f := ZMod.castHom hp (ZMod p)
  have h := congrArg f (ZMod.natCast_zmod_val (x : ZMod n))
  simpa only [map_natCast] using h

lemma weight_cast (n x y : ℕ) [NeZero n] :
    weight n (x : ZMod n).val (y : ZMod n).val = weight n x y := by
  apply prod_congr rfl
  intro p hp
  have h := Nat.dvd_of_mem_primeFactors hp
  simp only [atom,residue_val h]

lemma sum_residues (n : ℕ) [NeZero n] (F : ZMod n → ℚ) :
    ∑ k ∈ Icc 1 n, F (k : ZMod n) = ∑ k : ZMod n, F k := by
  classical
  apply sum_bij (s:=Icc 1 n) (t:=univ (α:=ZMod n)) (f:=fun k : ℕ => F k) (g:=F)
    (fun (k : ℕ) _ => (k : ZMod n)) (by simp)
  · intro a ha b hb eq
    obtain ⟨a1,an⟩ := mem_Icc.mp ha
    obtain ⟨b1,bn⟩ := mem_Icc.mp hb
    have e := congrArg ZMod.val eq
    simp only [ZMod.val_natCast] at e
    by_cases ae : a=n <;> by_cases be : b=n
    · omega
    · rw [ae,Nat.mod_self,Nat.mod_eq_of_lt (by omega : b<n)] at e
      omega
    · rw [be,Nat.mod_self,Nat.mod_eq_of_lt (by omega : a<n)] at e
      omega
    · rwa [Nat.mod_eq_of_lt (by omega : a<n),Nat.mod_eq_of_lt (by omega : b<n)] at e
  · intro t _
    have hn := NeZero.pos n
    have lt := t.val_lt
    by_cases h : t.val=0
    · refine ⟨n,mem_Icc.mpr ⟨hn,le_rfl⟩,?_⟩
      rw [ZMod.natCast_self,← ZMod.natCast_zmod_val t,h,Nat.cast_zero]
    · exact ⟨t.val,mem_Icc.mpr ⟨by omega,lt.le⟩,ZMod.natCast_zmod_val t⟩
  · intros; rfl

theorem from_sequence (n : ℕ) [NeZero n] : (n : ℚ)*a n = total n := by
  classical
  let g (q : ℕ×ℕ) := Int.gcd ((q.1 : ℤ)^2-(q.2 : ℤ)^2) n
  let S := Icc 1 n ×ˢ Icc 1 n
  let f (k : ℕ) : ℚ := A023900 k
  have hn := NeZero.ne n
  have qn : (n : ℚ)≠0 := by exact_mod_cast hn
  have hg (q : ℕ×ℕ) : g q ∈ Icc 1 n := by
    apply mem_Icc.mpr
    have pos := Int.gcd_pos_of_ne_zero_right ((q.1 : ℤ)^2-(q.2 : ℤ)^2)
      (by exact_mod_cast hn : (n : ℤ)≠0)
    have dv : g q ∣ n := by
      unfold g
      have h := Int.gcd_dvd_right ((q.1 : ℤ)^2-(q.2 : ℤ)^2) (n : ℤ)
      exact_mod_cast h
    exact ⟨pos,Nat.le_of_dvd (NeZero.pos n) dv⟩
  have sf : S.filter (fun q => g q ∈ Icc 1 n)=S := filter_true_of_mem (fun q _ => hg q)
  unfold a
  rw [mul_div_cancel₀ _ qn]
  calc
    (∑ k ∈ Icc 1 n, (T n k : ℚ)*A023900 k) =
        ∑ k ∈ Icc 1 n, ∑ q ∈ S with g q=k, f k := by
          apply sum_congr rfl
          intro k _
          simp [S,T,g,f]
    _ = ∑ q ∈ S with g q ∈ Icc 1 n, f (g q) := sum_fiberwise_eq_sum_filter' S _ g f
    _ = ∑ x ∈ Icc 1 n, ∑ y ∈ Icc 1 n, weight n x y := by
          rw [sf,sum_product]
          apply sum_congr rfl
          intro x _
          apply sum_congr rfl
          intro y _
          exact weight_gcd n x y hn
    _ = total n := by
          unfold total
          rw [← sum_residues n]
          apply sum_congr rfl
          intro x _
          rw [← sum_residues n]
          apply sum_congr rfl
          intro y _
          exact (weight_cast n x y).symm


lemma weight_mul (m n x y : ℕ) (hm : m≠0) (hn : n≠0) (h : m.Coprime n) :
    weight (m*n) x y = weight m x y*weight n x y := by
  unfold weight
  rw [Nat.primeFactors_mul hm hn,prod_union h.disjoint_primeFactors]

lemma crt_factor (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n)
    (x y : ZMod (m*n)) :
    weight (m*n) x.val y.val =
      weight m (((ZMod.chineseRemainder h) x).1.val) (((ZMod.chineseRemainder h) y).1.val) *
      weight n (((ZMod.chineseRemainder h) x).2.val) (((ZMod.chineseRemainder h) y).2.val) := by
  let e := ZMod.chineseRemainder h
  have hx (t : ZMod (m*n)) : e t = ((t.val : ZMod m),(t.val : ZMod n)) := by
    have eq := map_natCast e t.val
    rw [ZMod.natCast_zmod_val] at eq
    exact eq
  change _ = weight m (e x).1.val (e y).1.val * weight n (e x).2.val (e y).2.val
  rw [hx x,hx y]
  simp only [weight_cast,weight_mul m n x.val y.val (NeZero.ne m) (NeZero.ne n) h]

theorem total_mul (m n : ℕ) [NeZero m] [NeZero n] (h : m.Coprime n) :
    total (m*n)=total m*total n := by
  classical
  let e := (ZMod.chineseRemainder h).toEquiv
  let prodWeight (x y : ZMod m × ZMod n) :=
    weight m x.1.val y.1.val * weight n x.2.val y.2.val
  calc
    total (m*n) = ∑ x : ZMod (m*n), ∑ y : ZMod (m*n), prodWeight (e x) (e y) := by
      apply sum_congr rfl
      intro x _
      apply sum_congr rfl
      intro y _
      exact crt_factor m n h x y
    _ = ∑ x : ZMod m × ZMod n, ∑ y : ZMod m × ZMod n, prodWeight x y := by
      rw [← e.sum_comp (fun x => ∑ y, prodWeight x y)]
      apply sum_congr rfl
      intro x _
      exact e.sum_comp (prodWeight (e x))
    _ = total m*total n := by
      simp only [Fintype.sum_prod_type,prodWeight]
      calc
        _ = ∑ x : ZMod m, ∑ y : ZMod m, ∑ u : ZMod n, ∑ v : ZMod n,
            weight m x.val y.val * weight n u.val v.val := by
              apply sum_congr rfl
              intro x _
              rw [sum_comm]
        _ = total m * total n := by
              simp only [total,sum_mul]
              simp only [mul_sum]

def target (n : ℕ) : ℚ :=
  if n%2=1 then (n : ℚ)*n.totient*(-1)^n.primeFactors.card else 0

lemma target_mul (m n : ℕ) (hm : m≠0) (hn : n≠0) (h : m.Coprime n) :
    target (m*n)=target m*target n := by
  unfold target
  rw [Nat.mul_mod,Nat.primeFactors_mul hm hn,card_union_of_disjoint h.disjoint_primeFactors,
    Nat.totient_mul h,pow_add]
  have om : m%2=0 ∨ m%2=1 := by omega
  have on : n%2=0 ∨ n%2=1 := by omega
  rcases om with hm | hm <;> rcases on with hn | hn <;> simp [hm,hn] <;> ring

lemma total_one : total 1=target 1 := by
  simp [total,target,weight]

end SquareWeights


open scoped ArithmeticFunction.Moebius
open OMA.S_oeis_a366562

namespace SquaresTail

theorem divisors_oddPart (n : ℕ) (hn : 0 < n) :
    (oddPart n).divisors = n.divisors.filter (fun d => d % 2 = 1) := by
  have hn0 : n ≠ 0 := by omega
  have ho0 : oddPart n ≠ 0 := (Nat.ordCompl_pos 2 hn0).ne'
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hd, _⟩
    have hd' : d ∣ n := dvd_trans hd (Nat.ordCompl_dvd n 2)
    have hodd : ¬ 2 ∣ d := fun h => Nat.not_dvd_ordCompl Nat.prime_two hn0 (dvd_trans h hd)
    have hm := Nat.mod_lt d (by decide : 0 < 2)
    have hmod : d % 2 ≠ 0 := by
      intro hz
      exact hodd (Nat.dvd_of_mod_eq_zero hz)
    exact ⟨⟨hd', hn0⟩, by omega⟩
  · rintro ⟨⟨hd, _⟩, hodd⟩
    exact ⟨Nat.dvd_ordCompl_of_dvd_not_dvd hd (by simpa only [Nat.dvd_iff_mod_eq_zero] using (show d % 2 ≠ 0 by omega)), ho0⟩

theorem sum_odd_totient (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, if d % 2 = 1 then (d.totient : ℚ) else 0) = (oddPart n : ℚ) := by
  rw [← Finset.sum_filter, ← divisors_oddPart n hn]
  exact_mod_cast Nat.sum_totient (oddPart n)

theorem moebius_oddPart (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, (μ (n / d) : ℚ) * (oddPart d : ℚ)) =
      if n % 2 = 1 then (n.totient : ℚ) else 0 := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun d => if d % 2 = 1 then (d.totient : ℚ) else 0)
    (g := fun d => (oddPart d : ℚ))).mp sum_odd_totient n hn
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => (μ x : ℚ) * (oddPart y : ℚ))] at h
  exact h

theorem totient_difference (n : ℕ) :
    2 * (n.totient : ℚ) - ((2 * n).totient : ℚ) =
      if n % 2 = 1 then (n.totient : ℚ) else 0 := by
  by_cases hn : n % 2 = 1
  · rw [if_pos hn, Nat.totient_two_mul_of_odd (Nat.odd_iff.mpr hn)]
    ring
  · have heven : Even n := Nat.even_iff.mpr (by omega)
    rw [if_neg hn, Nat.totient_two_mul_of_even heven]
    push_cast
    ring

end SquaresTail

namespace SquareWeights
open OMA.S_oeis_a366562

theorem total_all (hpp : ∀ p k : ℕ, p.Prime → 0<k → ∀ [NeZero (p^k)], total (p^k) = target (p^k))
    (n : ℕ) [NeZero n] : total n=target n := by
  have every : ∀ n : ℕ, ∀ [NeZero n], total n=target n := by
    apply Nat.recOnPosPrimePosCoprime (motive:=fun n => ∀ [NeZero n], total n=target n)
    · exact hpp
    · intro h
      exact False.elim ((NeZero.ne (0 : ℕ)) rfl)
    · intro _
      exact total_one
    · intro m n hm hn h im inn _
      letI : NeZero m := ⟨by omega⟩
      letI : NeZero n := ⟨by omega⟩
      rw [total_mul m n h,im,inn,target_mul m n (NeZero.ne _) (NeZero.ne _) h]
  exact every n

theorem finish (hpp : ∀ p k : ℕ, p.Prime → 0<k → ∀ [NeZero (p^k)], total (p^k) = target (p^k)) :
    type_of% @OMA.S_oeis_a366562.main := by
  have form (n : ℕ) (hn : 1≤n) :
      a n = if n%2=1 then (n.totient : ℚ)*(-1)^n.primeFactors.card else 0 := by
    letI : NeZero n := ⟨by omega⟩
    have eq := from_sequence n
    rw [total_all hpp,target] at eq
    have nz : (n : ℚ)≠0 := by exact_mod_cast (by omega : n≠0)
    by_cases odd : n%2=1
    · rw [if_pos odd] at eq ⊢
      apply mul_left_cancel₀ nz
      linear_combination eq
    · rw [if_neg odd] at eq ⊢
      exact (mul_eq_zero.mp eq).resolve_left nz
  refine ⟨form,?_,?_,?_,?_⟩
  · intro n hn
    rw [form n hn,SquaresTail.totient_difference]
    split <;> ring
  · intro n hn
    rw [form n hn,SquaresTail.moebius_oddPart n (by omega)]
    split <;> ring
  · intro n hn
    rw [form (2*n) (by omega),if_neg (by omega)]
  · intro n
    rw [form (2*n+1) (by omega),if_pos (by omega),mul_comm]

end SquareWeights

namespace SquareWeights
open Finset
lemma square_roots (p : ℕ) (hp : p.Prime) (x y : ZMod p) :
    x^2=y^2 ↔ y=x ∨ y= -x := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [eq_comm]
  exact sq_eq_sq_iff_eq_or_eq_neg

lemma nonzero_ne_neg (p : ℕ) (hp : p.Prime) (hodd : p≠2) (x : ZMod p) (hx : x≠0) :
    x ≠ -x := by
  letI : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hl := Nat.le_of_dvd (by decide : 0<2) hd
    have := hp.two_le
    omega
  intro h
  have hz : (2 : ZMod p)*x=0 := by rw [two_mul]; exact add_eq_zero_iff_eq_neg.mpr h
  exact mul_ne_zero h2 hx hz

lemma prime_atom_row (p : ℕ) [NeZero p] (hp : p.Prime) (hodd : p≠2) (x : ZMod p) :
    (∑ y : ZMod p, atom p x.val y.val) = if x=0 then 0 else -(p:ℚ) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  have hroot (y : ZMod p) :
      atom p x.val y.val = if y=x ∨ y= -x then 1-(p:ℚ) else 1 := by
    simp only [atom,ZMod.natCast_zmod_val,square_roots p hp]
  simp_rw [hroot]
  by_cases hx : x=0
  · subst x
    simp only [neg_zero,or_self]
    have he (y : ZMod p) : (if y=0 then 1-(p:ℚ) else 1) = 1-(if y=0 then (p:ℚ) else 0) := by split_ifs <;> ring
    simp_rw [he]
    simp [sum_sub_distrib,ZMod.card]
  · rw [if_neg hx]
    have hn := nonzero_ne_neg p hp hodd x hx
    have he (y : ZMod p) : (if y=x ∨ y= -x then 1-(p:ℚ) else 1) =
        1-(if y=x then (p:ℚ) else 0)-(if y= -x then (p:ℚ) else 0) := by
      by_cases hy : y=x
      · subst y; simp [hn]
      · by_cases hy' : y= -x <;> simp [hy,hy',hn,Ne.symm hn]
    simp_rw [he]
    simp [sum_sub_distrib,ZMod.card] <;> ring

lemma prime_atom_sum (p : ℕ) [NeZero p] (hp : p.Prime) (hodd : p≠2) :
    (∑ x : ZMod p, ∑ y : ZMod p, atom p x.val y.val) = -(p:ℚ)*((p:ℚ)-1) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  simp_rw [prime_atom_row p hp hodd]
  have he (x : ZMod p) : (if x=0 then (0:ℚ) else -(p:ℚ)) =
      -(p:ℚ)+(if x=0 then (p:ℚ) else 0) := by split_ifs <;> ring
  simp_rw [he]
  simp [sum_add_distrib,ZMod.card]
  ring

lemma two_atom_sum :
    (∑ x : ZMod 2, ∑ y : ZMod 2, atom 2 x.val y.val) = 0 := by
  decide +kernel

end SquareWeights

namespace SquareWeights
open Finset

lemma finEquiv_val (n : ℕ) [NeZero n] (i : Fin n) : ((ZMod.finEquiv n) i).val = i.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

lemma finEquiv_cast (n : ℕ) [NeZero n] (i : Fin n) :
    (i.val : ZMod n) = (ZMod.finEquiv n) i := by
  simpa only [finEquiv_val] using ZMod.natCast_zmod_val ((ZMod.finEquiv n) i)

lemma sum_lift (m p : ℕ) [NeZero m] [NeZero p] (F : ZMod p → ℚ) :
    (∑ x : ZMod (m*p), F (x.val : ZMod p)) = (m:ℚ)*(∑ x : ZMod p, F x) := by
  classical
  calc
    (∑ x : ZMod (m*p), F (x.val : ZMod p)) =
        ∑ i : Fin (m*p), F (((ZMod.finEquiv (m*p)) i).val : ZMod p) :=
      (Equiv.sum_comp (ZMod.finEquiv (m*p)).toEquiv _).symm
    _ = ∑ ij : Fin m × Fin p,
        F (((ZMod.finEquiv (m*p)) (finProdFinEquiv ij)).val : ZMod p) :=
      (Equiv.sum_comp finProdFinEquiv _).symm
    _ = ∑ ij : Fin m × Fin p, F ((ZMod.finEquiv p) ij.2) := by
      apply sum_congr rfl
      intro ij _
      rw [finEquiv_val]
      change F ((ij.2.val+p*ij.1.val : ℕ) : ZMod p) = _
      rw [Nat.cast_add,Nat.cast_mul,ZMod.natCast_self,zero_mul,add_zero,finEquiv_cast]
    _ = (m:ℚ)*(∑ j : Fin p, F ((ZMod.finEquiv p) j)) := by
      rw [Fintype.sum_prod_type]
      simp [nsmul_eq_mul]
    _ = (m:ℚ)*(∑ j : ZMod p, F j) := by
      congr 1
      exact Equiv.sum_comp (ZMod.finEquiv p).toEquiv F

lemma sum_lift_two (m p : ℕ) [NeZero m] [NeZero p] (F : ZMod p → ZMod p → ℚ) :
    (∑ x : ZMod (m*p), ∑ y : ZMod (m*p), F (x.val : ZMod p) (y.val : ZMod p)) =
      (m:ℚ)^2*(∑ x : ZMod p, ∑ y : ZMod p, F x y) := by
  simp_rw [sum_lift m p]
  rw [← mul_sum]
  have ho := sum_lift m p (fun x => ∑ y : ZMod p, F x y)
  rw [ho]
  ring

lemma atom_lift_sum (m p : ℕ) [NeZero m] [NeZero p] :
    (∑ x : ZMod (m*p), ∑ y : ZMod (m*p), atom p x.val y.val) =
      (m:ℚ)^2*(∑ x : ZMod p, ∑ y : ZMod p, atom p x.val y.val) := by
  simpa only [atom,ZMod.natCast_zmod_val] using
    sum_lift_two m p (fun x y => if x^2=y^2 then 1-(p:ℚ) else 1)

end SquareWeights

namespace SquareWeights
open Finset

lemma atom_sum_congr (n m p : ℕ) [NeZero n] [NeZero m] (h : n=m) :
    (∑ x : ZMod n, ∑ y : ZMod n, atom p x.val y.val) =
      ∑ x : ZMod m, ∑ y : ZMod m, atom p x.val y.val := by
  subst m
  rfl

lemma total_prime_power_succ (p k : ℕ) [NeZero p] (hp : p.Prime) :
    total (p^(k+1)) = if p=2 then 0 else -((p^k : ℕ):ℚ)^2*(p:ℚ)*((p:ℚ)-1) := by
  classical
  simp only [total,weight,Nat.primeFactors_pow_succ,hp.primeFactors,prod_singleton]
  rw [atom_sum_congr (p^(k+1)) (p^k*p) p (pow_succ p k), atom_lift_sum (p^k) p]
  by_cases hp2 : p=2
  · subst p
    rw [two_atom_sum]
    simp
  · rw [prime_atom_sum p hp hp2,if_neg hp2]
    ring


end SquareWeights

namespace SquareWeights
open Finset

lemma prime_target (p j : ℕ) (hp : p.Prime) (hj : 0<j) [NeZero (p^j)] :
    total (p^j)=target (p^j) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  cases j with
  | zero => omega
  | succ k =>
    rw [total_prime_power_succ p k hp]
    unfold target
    rw [Nat.totient_prime_pow_succ hp k,Nat.primeFactors_pow_succ,hp.primeFactors,card_singleton,pow_one]
    by_cases h2 : p=2
    · subst p
      have hdiv : 2 ∣ 2^(k+1) := ⟨2^k,by rw [pow_succ]; ring⟩
      rw [Nat.mod_eq_zero_of_dvd hdiv]
      simp
    · have odd : (p^(k+1))%2=1 := Nat.odd_iff.mp (hp.odd_of_ne_two h2).pow
      rw [if_neg h2,if_pos odd,pow_succ]
      push_cast [Nat.cast_sub hp.one_le]
      ring

end SquareWeights

theorem OMA.solution : type_of% @OMA.S_oeis_a366562.main :=
  SquareWeights.finish SquareWeights.prime_target
