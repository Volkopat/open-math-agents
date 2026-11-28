import FormalConjectures.ErdosProblems.«10»
import Mathlib

/- Gallagher via a second moment on odd integers, with the elementary parts done.
A prime log weight on odd numbers is smoothed by averaging over a family of
short sums of powers of two. The first moment is the prime number theorem for
odd primes (H2). The square of the smoothed weight is expanded; the diagonal
costs at most a log square per shift and is absorbed by a large family, and
each off-diagonal term is bounded by a prime-pair correlation at the gap of
the two shifts (proved below). What remains is the averaged off-diagonal
prime-pair estimate (H1). A variance argument and a parity transfer then give
lower density at least 1 - eps for primes plus boundedly many powers of two. -/
namespace OMA.R_Erdos10_erdos_10_variants_gallagher_R2

open Finset Filter Erdos10
open scoped Classical Topology

lemma shiftedSum (v : ℕ → ℝ) {N u : ℕ} (hu : u ≤ N) :
    (∑ j ∈ range N, (if u≤j then v (j-u) else 0)) = ∑ j ∈ range (N-u), v j := by
  obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le hu
  rw [sum_range_add]
  have hz : (∑ j ∈ range u, if u≤j then v (j-u) else 0)=0 := by
    apply sum_eq_zero
    intro j hj
    simp [not_le.mpr (mem_range.mp hj)]
  simp [hz]

lemma momentSupport {w : ℕ → ℝ} {N : ℕ} {δ : ℝ}
    (low : (1-2*δ)*N ≤ ∑ j ∈ range N, w j)
    (high : (∑ j ∈ range N,(w j)^2) ≤ (1+δ)*N) :
    (1-5*δ)*N ≤ (((range N).filter (fun j => w j≠0)).card:ℝ) := by
  have v : (∑ j ∈ range N, (w j-1)^2) =
      (∑ j ∈ range N,(w j)^2) - 2*(∑ j ∈ range N,w j) + N := by
    simp_rw [show ∀ x : ℝ, (x-1)^2 = x^2-2*x+1 by intro x;ring]
    simp [sum_add_distrib,sum_sub_distrib,mul_sum]
  have small : (((range N).filter (fun j => w j=0)).card : ℝ) ≤ ∑ j ∈ range N,(w j-1)^2 := by
    calc
      _ = ∑ j ∈ (range N).filter (fun j => w j=0), (w j-1)^2 := by
        symm
        calc
          _ = ∑ j ∈ (range N).filter (fun j => w j=0), (1:ℝ) := by
            apply sum_congr rfl
            intro j hj
            simp [(mem_filter.mp hj).2]
          _ = _ := by simp
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun j _ _ => sq_nonneg _)
  have split := card_filter_add_card_filter_not (s:=range N) (p:=fun j => w j=0)
  simp only [card_range] at split
  have rr := congrArg (fun m : ℕ => (m:ℝ)) split
  push_cast at rr
  linarith only [low,high,v,small,rr]

lemma shortShift {k j : ℕ} (t : Multiset ℕ) (hc : t.card ≤ k) (p : ℕ)
    (hp : p.Prime) (eq : p + 2*(t.map (fun i : ℕ => 2^i)).sum = 2*j+1) :
    ∀ b : ℕ, b<2 → 2*j+1+b ∈ sumPrimeAndTwoPows (k+1) := by
  let u := t.map (·+1)
  have e : (u.map (fun i : ℕ => 2^i)).sum = 2*(t.map (fun i : ℕ => 2^i)).sum := by
    suffices h : ∀ T : Multiset ℕ, ((T.map (·+1)).map (fun i : ℕ => 2^i)).sum =
        2*(T.map (fun i : ℕ => 2^i)).sum by exact h t
    intro T
    induction T using Multiset.induction_on with
    | empty => simp
    | cons x T ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,pow_succ,ih]
      ring
  intro b hb
  have hc' : u.card ≤ k := by simpa [u] using hc
  rcases (show b=0 ∨ b=1 by omega) with rfl | rfl
  · exact ⟨p,u,hp,by omega,by simp [e,eq]⟩
  · exact ⟨p,0::ₘu,hp,by simpa using Nat.succ_le_succ hc',by simp [e] at *;omega⟩


lemma translate : ∀ (v : ℕ → ℝ) (s : Multiset ℕ → ℕ) (N : ℕ) (Q : Finset (Multiset ℕ))
    (M : ℝ), (∀ j, 0 ≤ v j) → 0 ≤ M → (∀ j < N, v j ≤ M) →
    (∑ j ∈ range N, (∑ t ∈ Q, if s t ≤ j then v (j-s t) else 0)^2) ≤
      N*Q.card*M^2 + ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j*v (j+Nat.dist (s t) (s u)) := by
  intro v s N Q M hv hM hvM
  have key : ∀ a b : ℕ, a ≤ b →
      ∑ j ∈ range N, (if a ≤ j then v (j - a) else 0) * (if b ≤ j then v (j - b) else 0)
        ≤ ∑ j ∈ range N, v j * v (j + (b - a)) := by
    intro a b hab
    have h1 : ∀ j ∈ range N,
        (if a ≤ j then v (j - a) else 0) * (if b ≤ j then v (j - b) else 0)
          = if b ≤ j then v (j - b) * v (j - b + (b - a)) else 0 := by
      intro j _
      by_cases hb : b ≤ j
      · rw [if_pos (le_trans hab hb), if_pos hb, if_pos hb]
        have : j - a = j - b + (b - a) := by omega
        rw [this, mul_comm]
      · rw [if_neg hb, if_neg hb, mul_zero]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
    calc ∑ j ∈ (range N).filter (fun j => b ≤ j), v (j - b) * v (j - b + (b - a))
        = ∑ i ∈ range (N - b), v i * v (i + (b - a)) := by
          apply Finset.sum_nbij' (fun j => j - b) (fun i => i + b)
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
            omega
          · intro i hi
            simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
            omega
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_range] at hj
            omega
          · intro i _
            simp
          · intro j _
            rfl
      _ ≤ ∑ i ∈ range N, v i * v (i + (b - a)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.range_mono (Nat.sub_le N b)
          · intro i _ _
            exact mul_nonneg (hv _) (hv _)
  have pair : ∀ a b : ℕ,
      ∑ j ∈ range N, (if a ≤ j then v (j - a) else 0) * (if b ≤ j then v (j - b) else 0)
        ≤ ∑ j ∈ range N, v j * v (j + Nat.dist a b) := by
    intro a b
    rcases le_total a b with hab | hab
    · have : Nat.dist a b = b - a := by unfold Nat.dist; omega
      rw [this]
      exact key a b hab
    · have : Nat.dist a b = a - b := by unfold Nat.dist; omega
      rw [this]
      calc _ = ∑ j ∈ range N,
            (if b ≤ j then v (j - b) else 0) * (if a ≤ j then v (j - a) else 0) :=
            Finset.sum_congr rfl fun j _ => mul_comm _ _
        _ ≤ _ := key b a hab
  have hsq : ∀ j, (∑ t ∈ Q, (if s t ≤ j then v (j - s t) else 0)) ^ 2
      = ∑ t ∈ Q, (if s t ≤ j then v (j - s t) else 0) ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t,
          (if s t ≤ j then v (j - s t) else 0) * (if s u ≤ j then v (j - s u) else 0) := by
    intro j
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [← Finset.add_sum_erase Q _ ht, sq]
  have hdiag : ∀ j ∈ range N, ∀ t ∈ Q, (if s t ≤ j then v (j - s t) else 0) ^ 2 ≤ M ^ 2 := by
    intro j hj t _
    rw [Finset.mem_range] at hj
    split_ifs
    · exact pow_le_pow_left₀ (hv _) (hvM _ (by omega)) 2
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact sq_nonneg M
  calc ∑ j ∈ range N, (∑ t ∈ Q, if s t ≤ j then v (j - s t) else 0) ^ 2
      = ∑ j ∈ range N, ∑ t ∈ Q, (if s t ≤ j then v (j - s t) else 0) ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N,
          (if s t ≤ j then v (j - s t) else 0) * (if s u ≤ j then v (j - s u) else 0) := by
        rw [Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.sum_comm]
    _ ≤ ∑ j ∈ range N, ∑ t ∈ Q, M ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j * v (j + Nat.dist (s t) (s u)) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun t ht => hdiag j hj t ht
        · exact Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => pair (s t) (s u)
    _ = N * Q.card * M ^ 2 +
        ∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j * v (j + Nat.dist (s t) (s u)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul]
        ring


open Real in
lemma pairsToMoment : (
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Q : Finset (Multiset ℕ), Q.Nonempty ∧
    (∀ t ∈ Q, t.card ≤ k ∧ (s t:ℝ) ≤ ε*N) ∧ Set.InjOn s (Q:Set (Multiset ℕ)) ∧
    log (2*(N:ℝ)+1)^2 ≤ ε*Q.card ∧
    (∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j*v (j+Nat.dist (s t) (s u))) ≤
      (1+ε)*N*(Q.card:ℝ)^2) → (
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum
  ∀ δ : ℝ, 0<δ → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
    ∃ Q : Finset (Multiset ℕ), ∃ a : Multiset ℕ → ℝ,
      (∀ t ∈ Q, 0 ≤ a t ∧ t.card ≤ k ∧ (s t : ℝ) ≤ δ*N) ∧
      (∑ t ∈ Q, a t)=1 ∧
      (∑ j ∈ range N, (∑ t ∈ Q, a t * (if s t ≤ j then v (j-s t) else 0))^2) ≤ (1+δ)*N) := by
  have translate := translate
  revert translate
  intro translate pairs
  dsimp only
  intro δ d0
  let ε := δ/2
  have e0 : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨k,samples⟩ := pairs ε e0
  refine ⟨k,?_⟩
  filter_upwards [samples] with N H
  obtain ⟨Q,Qp,support,_,diag,off⟩ := H
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  let v (j : ℕ) := if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let M := log (2*(N:ℝ)+1)
  have M0 : 0 ≤ M := Real.log_nonneg (by linarith [Nat.cast_nonneg N (α:=ℝ)])
  have v0 (j : ℕ) : 0 ≤ v j := by dsimp [v]; split <;> positivity
  have vmax (j : ℕ) (hj : j < N) : v j ≤ M := by
    dsimp [v]; split
    · have nj : (j:ℝ) ≤ N := by exact_mod_cast hj.le
      have le : log (2*j+1:ℕ) ≤ M := by
        dsimp only [M]
        apply Real.log_le_log (by positivity)
        push_cast
        linarith
      linarith
    · exact M0
  have h := translate v s N Q M v0 M0 vmax
  have qp : (0:ℝ) < Q.card := by exact_mod_cast Qp.card_pos
  refine ⟨Q,fun _ => (Q.card:ℝ)⁻¹,?_,?_,?_⟩
  · intro t ht
    obtain ⟨tk,ts⟩ := support t ht
    refine ⟨by positivity,tk,ts.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    dsimp [ε]; linarith
  · simp [qp.ne']
  change (∑ j ∈ range N,(∑ t ∈ Q,(Q.card:ℝ)⁻¹*(if s t ≤ j then v (j-s t) else 0))^2) ≤ _
  simp_rw [←mul_sum,mul_pow]
  rw [←mul_sum,inv_pow,←div_eq_inv_mul,div_le_iff₀ (sq_pos_of_pos qp)]
  apply h.trans
  change M^2 ≤ ε*(Q.card:ℝ) at diag
  have d := mul_le_mul_of_nonneg_left diag (show 0 ≤ (N:ℝ)*Q.card by positivity)
  dsimp only [s,v] at h ⊢
  dsimp [ε] at off d
  linarith only [off,d]


lemma momentToTarget : (
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  ∀ δ : ℝ, 0<δ → ∀ᶠ N : ℕ in atTop, (1-δ)*N ≤ ∑ j ∈ range N, v j) → (
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum
  ∀ δ : ℝ, 0<δ → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
    ∃ Q : Finset (Multiset ℕ), ∃ a : Multiset ℕ → ℝ,
      (∀ t ∈ Q, 0 ≤ a t ∧ t.card ≤ k ∧ (s t : ℝ) ≤ δ*N) ∧
      (∑ t ∈ Q, a t)=1 ∧
      (∑ j ∈ range N, (∑ t ∈ Q, a t * (if s t ≤ j then v (j-s t) else 0))^2) ≤ (1+δ)*N) → type_of% @Erdos10.erdos_10.variants.gallagher := by
  classical
  intro primeMean meanSquare ε hε
  let δ : ℝ := min (ε/16) (1/16)
  have d0 : 0<δ := lt_min (by positivity) (by norm_num)
  have d1 : δ≤1/16 := min_le_right .. 
  have de : δ≤ε/16 := min_le_left ..
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t : Multiset ℕ => (t.map (fun i : ℕ => 2^i)).sum
  obtain ⟨k,second⟩ := meanSquare δ d0
  obtain ⟨B,hB⟩ := eventually_atTop.mp (primeMean δ d0)
  let A := sumPrimeAndTwoPows (k+1)
  have bulk : ∀ᶠ m : ℕ in atTop,
      ∃ G ⊆ range m, (1-5*δ)*m ≤ (G.card:ℝ) ∧
      ∀ j ∈ G, ∀ b : ℕ, b<2 → 2*j+1+b ∈ A := by
    filter_upwards [second,eventually_ge_atTop (2*B)] with m hm hmB
    obtain ⟨Q,a,weights,total,h2⟩ := hm
    let w := fun j : ℕ => ∑ t ∈ Q,a t*(if s t≤j then v (j-s t) else 0)
    have part (t : Multiset ℕ) (ht : t ∈ Q) :
        (1-2*δ)*m ≤ ∑ j ∈ range m,(if s t≤j then v (j-s t) else 0) := by
      obtain ⟨_,_,hs⟩ := weights t ht
      change (s t:ℝ) ≤ δ*m at hs
      have htwice : 2 * s t ≤ m := by
        exact_mod_cast (show 2*(s t:ℝ) ≤ m by
          nlinarith only [hs,mul_le_mul_of_nonneg_right d1 (Nat.cast_nonneg m)])
      rw [shiftedSum v (by omega)]
      have le := hB (m-s t) (by omega)
      change (1-δ)*((m-s t:ℕ):ℝ) ≤ ∑ j ∈ range (m-s t),v j at le
      rw [Nat.cast_sub (by omega)] at le
      nlinarith only [le,hs,mul_nonneg d0.le (Nat.cast_nonneg (s t))]
    have low : (1-2*δ)*m ≤ ∑ j ∈ range m,w j := by
      calc
        _ = ∑ t ∈ Q,a t*((1-2*δ)*m) := by rw [←sum_mul,total,one_mul]
        _ ≤ ∑ t ∈ Q,a t*∑ j ∈ range m,(if s t≤j then v (j-s t) else 0) :=
          sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (part t ht) (weights t ht).1)
        _ = _ := by simp only [w,mul_sum]; rw [sum_comm]
    refine ⟨(range m).filter (fun j => w j≠0),filter_subset ..,momentSupport low h2,?_⟩
    intro j hj
    have nz := (mem_filter.mp hj).2
    obtain ⟨t,ht,ht'⟩ := exists_ne_zero_of_sum_ne_zero nz
    have nzt := (mul_ne_zero_iff.mp ht').2
    split_ifs at nzt with hsj
    · have pp : (2*(j-s t)+1).Prime := by
        by_contra hn
        simp [v,hn] at nzt
      apply shortShift t (weights t ht).2.1 _ pp
      change 2*(j-s t)+1+2*s t=2*j+1
      omega
    · exact (nzt rfl).elim
  refine ⟨k+1,?_⟩
  change 1-ε ≤ atTop.liminf (fun n : ℕ => A.partialDensity Set.univ n)
  apply le_liminf_of_le (IsBoundedUnder.isCoboundedUnder_ge (u:=fun n : ℕ => A.partialDensity Set.univ n)
    ⟨1,by simpa only [eventually_map] using (Eventually.of_forall (fun n : ℕ => Set.partialDensity_le_one A Set.univ n) : ∀ᶠ n : ℕ in atTop, A.partialDensity Set.univ n ≤ 1)⟩)
  obtain ⟨B',hb'⟩ := eventually_atTop.mp bulk
  obtain ⟨D,hD⟩ := exists_nat_ge (4/ε)
  filter_upwards [eventually_ge_atTop (2*B'+D+4)] with n hn
  let m := (n-1)/2
  obtain ⟨G,hG,good,hits⟩ := hb' m (by dsimp [m]; omega)
  let T := (range n).filter (·∈A)
  have inj : (G ×ˢ range 2).card ≤ T.card := by
    apply card_le_card_of_injOn (fun z : ℕ × ℕ => 2*z.1+1+z.2)
    · rintro ⟨j,b⟩ hz
      obtain ⟨hj,hb⟩ := mem_product.mp hz
      have jm := mem_range.mp (hG hj)
      have b2 := mem_range.mp hb
      exact mem_filter.mpr ⟨mem_range.mpr (by change 2*j+1+b<n; dsimp [m] at jm;omega),hits j hj b b2⟩
    · rintro ⟨i,a⟩ ha ⟨j,b⟩ hb he
      have a2 := mem_range.mp (mem_product.mp ha).2
      have b2 := mem_range.mp (mem_product.mp hb).2
      dsimp at he
      congr 1 <;> omega
  simp only [card_product,card_range] at inj
  have sub : n ≤ 2*m+2 := by dsimp [m];omega
  have sub' : (n:ℝ) ≤ 2*(m:ℝ)+2 := by exact_mod_cast sub
  have mn : (m:ℝ) ≤ n/2 := by
    rw [le_div_iff₀ (by norm_num)];exact_mod_cast (show m*2≤n by dsimp [m];omega)
  have nn : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have epsN : 4 ≤ ε*(n:ℝ) := by
    have hDn : (D:ℝ) ≤ n := by exact_mod_cast (show D≤n by omega)
    have hh := (div_le_iff₀ hε).mp (hD.trans hDn)
    linarith
  have seteq : A ∩ Set.Iio n = (T:Set ℕ) := by ext j;simp [T,and_comm]
  simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,seteq,Set.ncard_coe_finset,Nat.ncard_Iio]
  rw [le_div_iff₀ nn]
  have inj' : (G.card:ℝ)*2 ≤ T.card := by exact_mod_cast inj
  nlinarith only [inj',good,sub',epsN,mul_le_mul_of_nonneg_left mn d0.le,
    mul_le_mul_of_nonneg_right de nn.le]


/-- Gallagher's off-diagonal prime-pair estimate averaged over binary shifts.
Here Q may be taken to be distinct k-element sums on a short logarithmic
interval of exponents. The inner correlation only uses the nonzero gap. -/
def H1 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  let s : Multiset ℕ → ℕ := fun t => (t.map (fun i : ℕ => 2^i)).sum
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop, ∃ Q : Finset (Multiset ℕ), Q.Nonempty ∧
    (∀ t ∈ Q, t.card ≤ k ∧ (s t:ℝ) ≤ ε*N) ∧ Set.InjOn s (Q:Set (Multiset ℕ)) ∧
    Real.log (2*(N:ℝ)+1)^2 ≤ ε*Q.card ∧
    (∑ t ∈ Q, ∑ u ∈ Q.erase t, ∑ j ∈ range N, v j*v (j+Nat.dist (s t) (s u))) ≤
      (1+ε)*N*(Q.card:ℝ)^2

/-- The prime number theorem, omitting the single even prime. -/
def H2 : Prop :=
  let v := fun j : ℕ => if (2*j+1).Prime then Real.log (2*j+1 : ℕ)/2 else 0
  ∀ δ : ℝ, 0<δ → ∀ᶠ N : ℕ in atTop, (1-δ)*N ≤ ∑ j ∈ range N, v j

theorem main : H1 → H2 → type_of% @Erdos10.erdos_10.variants.gallagher := by
  intro h1 h2
  exact momentToTarget h2 (pairsToMoment h1)

end OMA.R_Erdos10_erdos_10_variants_gallagher_R2
