import FormalConjectures.ErdosProblems.«5»
import Mathlib

/-!
The one-gap case of Hildebrand and Maier, Gaps between prime numbers
(1988), equations (14), (17), and (19). Count consecutive prime pairs in a
primorial matrix in two ways. Many pairs per matrix and a sieve bound per
column pair force a positive fraction of bins to recur arbitrarily late.
Compactness and shrinking neighborhoods turn this into a Lebesgue measure bound.
-/
open Filter MeasureTheory Real Erdos5 Finset
open scoped Topology
namespace OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R2

/-- The matrix construction from the prime supply in the rows and the
distribution of admissible columns. G records a row and two column offsets.
The tolerated two bin widths account for the common logarithmic normalization. -/
def H1 : Prop := ∃ A : ℝ, 0 < A ∧ ∀ᶠ T : ℝ in atTop,
  ∀ M : ℕ, 0 < M → ∀ N : ℕ, ∃ (z R : ℕ) (P : Finset (ℕ × ℕ))
    (G : Finset (ℕ × (ℕ × ℕ))) (bin : ℕ × ℕ → Fin M),
    let q := primorial z
    let W := (q.totient : ℝ) / q * log R
    let L := log (R*q : ℕ)
    2 ≤ z ∧ 2 ≤ R ∧ R ≤ G.card ∧
    (∀ p ∈ P, p.1 < p.2 ∧ p.2-p.1 < z^2 ∧
      ((p.2-p.1 : ℕ):ℝ)/L ≤ T/2 ∧
      |((p.2-p.1 : ℕ):ℝ)/L - ((bin p).val : ℝ)*(T/M)| ≤ T/M) ∧
    (∀ j, (((P.filter (fun p => bin p = j)).card : ℝ) * M ≤ A*W^2)) ∧
    (∀ u ∈ G, u.1 ∈ Ioc R (2*R) ∧ u.2 ∈ P ∧ ∃ n ≥ N,
      Nat.nth Nat.Prime n = u.1*q+u.2.1 ∧
      Nat.nth Nat.Prime (n+1) = u.1*q+u.2.2 ∧
      2 ≤ n ∧ |L / log n - 1| ≤ 1/(M:ℝ))

/-- The two-column specialization of the upper-bound sieve (Lemma 3 in the
paper). The two entries are only required to be prime. -/
def H2 : Prop := ∃ B : ℝ, 0 < B ∧ ∀ z R : ℕ, 2 ≤ z → 2 ≤ R →
    ∀ a b : ℕ, a < b → b-a < z^2 →
      let q := primorial z
      let W := (q.totient : ℝ) / q * log R
      (((Ioc R (2*R)).filter (fun r => (r*q+a).Prime ∧ (r*q+b).Prime)).card : ℝ) * W^2 ≤ B*R

/-- At most one prime per nonempty row is lost when passing from primes to
consecutive pairs. Here the rows are written as intervals of prime indices. -/
theorem adjacent_indices (s : Finset ℕ)
    (h : ∀ a ∈ s, ∀ b ∈ s, ∀ x, a ≤ x → x ≤ b → x ∈ s) :
    s.card ≤ (s.filter (fun i => i+1 ∈ s)).card + 1 := by
  rcases s.eq_empty_or_nonempty with rfl|hn
  · simp
  have sub : s.erase (s.max' hn) ⊆ s.filter (fun i => i+1 ∈ s) := by
    intro i hi
    obtain ⟨hne,his⟩ := mem_erase.mp hi
    have ht : i ≤ s.max' hn := le_max' s i his
    exact mem_filter.mpr ⟨his,h i his (s.max' hn) (max'_mem _ _) (i+1) (by omega) (by omega)⟩
  have hc := card_le_card sub
  rw [card_erase_of_mem (max'_mem _ _)] at hc
  omega

/-- At most one unsieved prime can divide the difference between the column
offsets. Two distinct prime divisors above z would have product above z². -/
theorem exceptional_large_prime {z d : ℕ} (hd : 0 < d) (hsmall : d < z^2) :
    (d.primeFactors.filter (fun p => z < p)).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp r hr
  obtain ⟨hp',hpz⟩ := mem_filter.mp hp
  obtain ⟨hr',hrz⟩ := mem_filter.mp hr
  by_contra neq
  have cop := (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp')
    (Nat.prime_of_mem_primeFactors hr')).mpr neq
  have dvd := cop.mul_dvd_of_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp')
      (Nat.dvd_of_mem_primeFactors hr')
  have le := Nat.le_of_dvd hd dvd
  have bigger := Nat.mul_le_mul hpz hrz
  nlinarith only [hsmall,le,bigger]

/-- For a prime not dividing the modulus, a column removes one residue class
of row indices. Two distinct reduced offsets remove exactly two classes. -/
theorem two_bad_residues {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (q a b : F) (hq : q ≠ 0) (hab : a ≠ b) :
    (univ.filter (fun r : F => r*q+a=0 ∨ r*q+b=0)).card = 2 := by
  have eqv (r t : F) : r*q+t=0 ↔ r = -t/q := by
    rw [eq_div_iff hq]
    constructor <;> intro h <;> linear_combination h
  have he : (univ.filter (fun r : F => r*q+a=0 ∨ r*q+b=0)) = {-a/q,-b/q} := by
    ext r
    simp [eqv]
  have ne : -a/q ≠ -b/q := by
    intro h
    apply hab
    have hh := congrArg (fun x : F => x*q) h
    simpa [div_mul_cancel₀ _ hq] using hh
  rw [he]
  simp [ne]

/-- The product lost by removing primes dividing the primorial is bounded
by the square of q/φ(q), uniformly in the primorial. The estimate holds for
every positive q. -/
theorem euler_loss {q : ℕ} (hq : 0 < q) :
    (∏ p ∈ q.primeFactors, (1 + 2/(p:ℝ))) * ((q.totient : ℝ)/q)^2 ≤ 1 := by
  have euler := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors q)
  push_cast at euler
  have qnz : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have e : (q.totient : ℝ)/q = ∏ p ∈ q.primeFactors, (1 - (p:ℝ)⁻¹) := by
    rw [div_eq_iff qnz]
    simpa only [mul_comm (q:ℝ)] using euler
  rw [e, ← prod_pow, ← prod_mul_distrib]
  apply prod_le_one
  · intro p hp
    positivity
  · intro p hp
    have hp' : (1:ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    have hp0 : 0 < (p:ℝ) := by linarith
    have h := (inv_le_one₀ hp0).mpr hp'
    have hn := mul_nonneg (sq_nonneg (p:ℝ)⁻¹) (sub_nonneg.mpr h)
    rw [div_eq_mul_inv]
    nlinarith only [hn,sq_nonneg (p:ℝ)⁻¹]

/-- A common logarithmic scale for a row can differ from log n. The error
below is uniform across all selected cells, including both endpoints. -/
theorem rescale {x s L t T : ℝ} {M : ℕ} (hM : 0 < M) (hL : 0 < L)
    (hs : 0 < s) (hx : 0 ≤ x) (hxT : x/L ≤ T/2)
    (hc : |x/L-t| ≤ T/M) (he : |L/s-1| ≤ 1/(M:ℝ)) :
    x/s ∈ Set.Icc 0 T ∧ |x/s-t| ≤ 2*(T/M) := by
  have hm : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hm0 : 0 < (M:ℝ) := by linarith
  have ht : 0 ≤ x/L := div_nonneg hx hL.le
  have hT : 0 ≤ T := by linarith
  have hu : 1/(M:ℝ) ≤ 1 := (div_le_iff₀ hm0).mpr (by simpa using hm)
  have hr := (abs_le.mp he).2
  have eq : x/s = x/L*(L/s) := by field_simp
  have herr : |x/s-x/L| ≤ T/M := by
    rw [eq, show x/L*(L/s)-x/L=x/L*(L/s-1) by ring, abs_mul, abs_of_nonneg ht]
    calc
      _ ≤ (x/L)*(1/(M:ℝ)) := mul_le_mul_of_nonneg_left he ht
      _ ≤ T*(1/(M:ℝ)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  constructor
  · refine ⟨div_nonneg hx hs.le,?_⟩
    rw [eq]
    nlinarith only [hxT, mul_nonneg ht (show 0 ≤ 2-L/s by linarith)]
  · have hh := abs_sub_le (x/s) (x/L) t
    linarith

/-- Sum a bound on individual fibers without requiring a uniform integer
rounding convention for the upper bound. -/
theorem count_fibers {X Y : Type*} [DecidableEq Y] (s : Finset X) (t : Finset Y)
    (f : X → Y) (maps : ∀ x ∈ s, f x ∈ t) {w K : ℝ}
    (bound : ∀ y ∈ t, ((s.filter (fun x => f x = y)).card : ℝ)*w ≤ K) :
    (s.card : ℝ)*w ≤ t.card*K := by
  rw [card_eq_sum_card_fiberwise (f:=f) (t:=t) (fun x hx => maps x hx), Nat.cast_sum, Finset.sum_mul]
  calc
    _ ≤ ∑ _y ∈ t, K := sum_le_sum bound
    _ = _ := by simp

/-- The two matrix estimates imply occupation of proportion at least 1/(AB)
of the bins, by actual normalized gaps with indices beyond any chosen cutoff. -/
theorem occupied {A B T : ℝ} (hB : 0 < B) {M : ℕ} (hM : 0 < M)
    (N : ℕ) {z R : ℕ} (hR : 2 ≤ R)
    (P : Finset (ℕ × ℕ)) (G : Finset (ℕ × (ℕ × ℕ))) (bin : ℕ × ℕ → Fin M)
    (hsize : R ≤ G.card) (hcol : ∀ p ∈ P, p.1 < p.2 ∧ p.2-p.1 < z^2)
    (hbin : ∀ j, ((P.filter (fun p => bin p=j)).card : ℝ)*M ≤
      A*((((primorial z).totient : ℝ)/(primorial z))*log R)^2)
    (hrow : ∀ u ∈ G, u.1 ∈ Ioc R (2*R) ∧ u.2 ∈ P ∧ ∃ n ≥ N,
      Nat.nth Nat.Prime n = u.1*primorial z+u.2.1 ∧
      Nat.nth Nat.Prime (n+1) = u.1*primorial z+u.2.2 ∧
      normalizedGap n ∈ Set.Icc 0 T ∧
      |normalizedGap n-((bin u.2).val : ℝ)*(T/M)| ≤ 2*(T/M))
    (sieve : ∀ a b : ℕ, a<b → b-a<z^2 →
      (((Ioc R (2*R)).filter (fun r => (r*primorial z+a).Prime ∧
        (r*primorial z+b).Prime)).card : ℝ) *
        ((((primorial z).totient : ℝ)/(primorial z))*log R)^2 ≤ B*R) :
    ∃ J : Finset (Fin M), (M : ℝ) ≤ J.card*(A*B) ∧
      ∀ j ∈ J, ∃ n ≥ N, normalizedGap n ∈ Set.Icc 0 T ∧
        |normalizedGap n-(j.val : ℝ)*(T/M)| ≤ 2*(T/M) := by
  classical
  let q := primorial z
  let W := (q.totient : ℝ)/q * log R
  let Q := G.image Prod.snd
  let J := Q.image bin
  have hqp : Q ⊆ P := by
    intro p hp
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hp
    exact (hrow u hu).2.1
  have hqpos : 0 < q := primorial_pos z
  have htpos : 0 < q.totient := Nat.totient_pos.mpr hqpos
  have hW : 0 < W := mul_pos (div_pos (by exact_mod_cast htpos) (by exact_mod_cast hqpos))
    (Real.log_pos (by exact_mod_cast (show 1 < R by omega)))
  have hfirst : (G.card : ℝ)*W^2 ≤ Q.card*(B*R) := by
    apply count_fibers G Q Prod.snd (fun u hu => mem_image_of_mem _ hu)
    intro p hp
    have hxy := hcol p (hqp hp)
    let S := G.filter (fun u => u.2 = p)
    let V := (Ioc R (2*R)).filter (fun r => (r*q+p.1).Prime ∧ (r*q+p.2).Prime)
    have hs : S.card ≤ V.card := by
      apply card_le_card_of_injOn Prod.fst
      · intro u hu
        obtain ⟨hgu,he⟩ := mem_filter.mp hu
        obtain ⟨hr,_,n,_,hn,hn',_,_⟩ := hrow u hgu
        refine mem_filter.mpr ⟨hr,?_,?_⟩
        · have hp' := Nat.prime_nth_prime n
          rw [hn] at hp'
          simpa only [← he] using hp'
        · have hp' := Nat.prime_nth_prime (n+1)
          rw [hn'] at hp'
          simpa only [← he] using hp'
      · intro u hu v hv he
        exact Prod.ext he ((mem_filter.mp hu).2.trans (mem_filter.mp hv).2.symm)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hs : (S.card:ℝ) ≤ V.card)
      (sq_nonneg W)).trans (sieve _ _ hxy.1 hxy.2)
  have hsecond : (Q.card : ℝ)*M ≤ J.card*(A*W^2) := by
    apply count_fibers Q J bin (fun p hp => mem_image_of_mem _ hp)
    intro j _
    have h := card_le_card (filter_subset_filter (p:=fun p => bin p=j) hqp)
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg M)).trans (hbin j)
  refine ⟨J,?_,?_⟩
  · have hR' : (0:ℝ) < R := by exact_mod_cast (show 0<R by omega)
    have hM' : (0:ℝ) < M := by exact_mod_cast hM
    have e1 : (R:ℝ)*W^2 ≤ Q.card*(B*R) :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) (sq_nonneg W)).trans hfirst
    have e2 : W^2 ≤ Q.card*B := by
      apply (mul_le_mul_iff_left₀ hR').mp
      nlinarith only [e1]
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hW)).mp
    nlinarith only [mul_le_mul_of_nonneg_right e2 hM'.le,
      mul_le_mul_of_nonneg_right hsecond hB.le]
  · intro j hj
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hj
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hp
    obtain ⟨_,_,n,hn,_,_,hmem,ha⟩ := hrow u hu
    exact ⟨n,hn,hmem,ha⟩

/-- For a fixed mesh the nonrecurrent cells all disappear by one common
cutoff, since there are only finitely many cells. -/
theorem recurrent_cells {M : ℕ} {v : ℕ → ℝ} {T D : ℝ}
    (supply : ∀ N : ℕ, ∃ J : Finset (Fin M), (M : ℝ) ≤ J.card*D ∧
      ∀ j ∈ J, ∃ n ≥ N, v n ∈ Set.Icc 0 T ∧
        |v n-(j.val : ℝ)*(T/M)| ≤ 2*(T/M)) :
    ∃ J : Finset (Fin M), (M : ℝ) ≤ J.card*D ∧
      ∀ j ∈ J, ∃ x ∈ {x | MapClusterPt x atTop v} ∩ Set.Icc 0 T,
        |x-(j.val:ℝ)*(T/M)| ≤ 2*(T/M) := by
  classical
  let K (j : Fin M) := Set.Icc (0:ℝ) T ∩
    Set.Icc ((j.val:ℝ)*(T/M)-2*(T/M)) ((j.val:ℝ)*(T/M)+2*(T/M))
  let hit (j : Fin M) (N : ℕ) := ∃ n ≥ N, v n ∈ K j
  let cut (j : Fin M) := if h : ∃ N, ¬ hit j N then Classical.choose h else 0
  let N := univ.sup cut
  obtain ⟨J,hcount,hJ⟩ := supply N
  refine ⟨J,hcount,?_⟩
  intro j hj
  obtain ⟨n,hn,hm,hd⟩ := hJ j hj
  obtain ⟨hlo,hhi⟩ := abs_le.mp hd
  have hK : v n ∈ K j := ⟨hm,by constructor <;> linarith only [hlo,hhi]⟩
  have hf : ∃ᶠ n in atTop, v n ∈ K j := by
    apply frequently_atTop.mpr
    intro m
    by_contra hh
    have bad : ∃ k, ¬ hit j k := ⟨m,hh⟩
    have hbad : ¬ hit j (cut j) := by
      dsimp [cut]
      simpa only [dif_pos bad] using Classical.choose_spec bad
    exact hbad ⟨n, (le_sup (s:=univ) (f:=cut) (mem_univ j)).trans hn, hK⟩
  have hc : IsCompact (K j) := isCompact_Icc.inter_right isClosed_Icc
  obtain ⟨x,hx,hcluster⟩ := hc.exists_mapClusterPt_of_frequently hf
  refine ⟨x,⟨hcluster,hx.1⟩,?_⟩
  have hpair := hx.2
  rw [abs_le]
  constructor <;> linarith only [hpair.1,hpair.2]

/-- Disjoint half-open mesh intervals fit in a three-width neighborhood of
the compact set as soon as each selected cell has a cluster point nearby. -/
theorem mesh_mass {M : ℕ} {T D : ℝ} (hM : 0 < M) (hT : 0 < T) (hD : 0 < D)
    (K : Set ℝ) (J : Finset (Fin M)) (hcount : (M:ℝ) ≤ J.card*D)
    (hJ : ∀ j ∈ J, ∃ x ∈ K, |x-(j.val:ℝ)*(T/M)| ≤ 2*(T/M)) :
    ENNReal.ofReal (T/D) ≤ volume (Metric.cthickening (3*T/M) K) := by
  classical
  let w := T / (M:ℝ)
  have hm : 0 < (M:ℝ) := by exact_mod_cast hM
  have hw : 0 < w := div_pos hT hm
  let I (j : Fin M) := Set.Ioc ((j.val:ℝ)*w) (((j.val:ℝ)+1)*w)
  have hs : (⋃ j ∈ J, I j) ⊆ Metric.cthickening (3*T/M) K := by
    intro z hz
    obtain ⟨j,hj,hz'⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨x,hx,ha⟩ := hJ j hj
    apply Metric.mem_cthickening_of_dist_le z x _ K hx
    change (j.val:ℝ)*w < z ∧ z ≤ ((j.val:ℝ)+1)*w at hz'
    change |x-(j.val:ℝ)*w| ≤ 2*w at ha
    rw [Real.dist_eq, abs_le, show 3*T/(M:ℝ)=3*w by dsimp [w]; ring]
    obtain ⟨a,b⟩ := abs_le.mp ha
    constructor <;> nlinarith only [a,b,hz'.1,hz'.2,hw]
  have hdis : Set.PairwiseDisjoint (J : Set (Fin M)) I := by
    intro i _ j _ hij
    rcases lt_or_gt_of_ne hij with h|h
    · apply Set.Ioc_disjoint_Ioc_of_le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show i.val+1 ≤ j.val from h)) hw.le
    · apply Disjoint.symm
      apply Set.Ioc_disjoint_Ioc_of_le
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show j.val+1 ≤ i.val from h)) hw.le
  have hvol (j : Fin M) : volume (I j) = ENNReal.ofReal w := by
    rw [show I j = Set.Ioc _ _ from rfl, Real.volume_Ioc]
    congr 1
    ring
  apply le_trans _ (measure_mono hs)
  rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_Ioc)]
  simp_rw [hvol]
  rw [sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  dsimp [w]
  rw [mul_div_assoc', div_le_div_iff₀ hD hm]
  nlinarith only [mul_le_mul_of_nonneg_left hcount hT.le]

theorem main : H1 → H2 → type_of% @Erdos5.erdos_5.variants.hildebrand_maier_measure := by
  rintro ⟨A,hA,ha⟩ ⟨B,hB,hb⟩
  let D := A*B
  have hD : 0 < D := mul_pos hA hB
  refine ⟨1/D,one_div_pos.mpr hD,?_⟩
  filter_upwards [ha,eventually_gt_atTop (0:ℝ)] with T hmatrix hT
  let K := limitPointSet ∩ Set.Icc 0 T
  have hK : IsCompact K := isCompact_Icc.inter_left Erdos5.isClosed_limitPointSet
  have hmesh (M : ℕ) (hM : 0<M) : ENNReal.ofReal (T/D) ≤
      volume (Metric.cthickening (3*T/(M:ℝ)) K) := by
    obtain ⟨J,hJ,hc⟩ := recurrent_cells (M:=M) (T:=T) (D:=D) (v:=normalizedGap) (by
      intro N
      obtain ⟨z,R,P,G,bin,hz,hR,hsize,hcol,hbin,hrow⟩ := hmatrix M hM N
      let q := primorial z
      let L := log (R*q : ℕ)
      have hq : 0 < q := primorial_pos _
      have hL : 0 < L := Real.log_pos (by
        exact_mod_cast (show 1 < R*q by nlinarith only [hR,hq,Nat.mul_le_mul hR hq]))
      apply occupied hB hM N hR P G bin hsize (fun p hp => ⟨(hcol p hp).1,(hcol p hp).2.1⟩)
        hbin _ (hb z R hz hR)
      intro u hu
      obtain ⟨hr,hp,n,hn,ha,hb',hn2,he⟩ := hrow u hu
      refine ⟨hr,hp,n,hn,ha,hb',?_⟩
      have hc := (hcol u.2 hp).2.2
      have eq : primeGap n = u.2.2-u.2.1 := by
        unfold primeGap
        rw [ha,hb']
        omega
      simpa only [normalizedGap, eq] using
        rescale hM hL (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
          (Nat.cast_nonneg _) hc.1 hc.2 he)
    exact mesh_mass hM hT hD K J hJ hc
  have hrad : Tendsto (fun M : ℕ => 3*T/(M:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := (tendsto_measure_cthickening_of_isCompact (μ := (volume : Measure ℝ)) hK).comp hrad
  have h := ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop 1] with M hm using hmesh M hm)
  simpa [div_eq_mul_inv, mul_comm] using h

end OMA.R_Erdos5_erdos_5_variants_hildebrand_maier_measure_R2
