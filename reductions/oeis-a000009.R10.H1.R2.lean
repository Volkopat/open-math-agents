import OMAReductions.R_oeis_a000009_R10

/-!
# A sparse pair criterion for the R10 representation step

Gordon and Ono's divisibility theorem (DOI 10.1023/A:1009711020492) implies
that indices with 2048 ∤ q(n) have density zero. Since q(45) = 2048, these
include all sufficiently large small-divisor sieve survivors. A fixed pair of
candidates per window is compatible with zero density in the index. Only
consecutive cofactor exceptions surviving their clipped entry need comparison.
A kernel-checked prefix covers the original cutoff through q(6400), then native representation intervals extend it to 2*q(7200)-1; both
arithmetic hypotheses below concern only the remaining tail.
-/
namespace OMA.R_oeis_a000009_R10_H1_R2
open OMA.S_oeis_a000009 Finset

/-- Usable arrivals occur arbitrarily late. Immediately before each such arrival
above the starting endpoint, two previously arrived values still survive. -/
def H1 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let start : ℕ := 1679994603391465890567050011123964902522794012673156461548944387
  let birth := fun a : ℕ => (2*a+2)/3
  let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
    ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
  (∀ x, start ≤ x → ∃ c, x < birth c ∧ live (birth c) c) ∧
    ∀ c, start < birth c → live (birth c) c →
      ∃ a b, live (birth c-1) a ∧ live (birth c-1) b ∧ a < b

/-- Among exceptional values still present at their clipped entry, each value
must have expired by the entry of its immediate successor (if any). -/
def H2 : Prop :=
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let exceptional := fun a : ℕ =>
    ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
  let entry := fun a : ℕ => max 1679994603391465890567050011123964902522794012673156461548944387 ((2*a+2)/3)
  let gone := fun x a : ℕ => a < x ∨ ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ x ∧ s ∣ a
  let viable := fun a : ℕ => Q a ∧ exceptional a ∧ ¬ gone (entry a) a
  ∀ a b, viable a → viable b → a < b →
    (∀ c, a < c → c < b → ¬ viable c) → gone (entry b) a

/-- For ordered entry times and irreversible exits, any overlap is witnessed
by a value and its first viable successor, even when entry times coincide. -/
theorem no_overlap_iff_consecutive (candidate : ℕ → Prop) (entry : ℕ → ℕ)
    (gone : ℕ → ℕ → Prop) (ordered : Monotone entry)
    (persist : ∀ {x y a}, x ≤ y → gone x a → gone y a) :
    let viable := fun a => candidate a ∧ ¬ gone (entry a) a
    (∀ a b, candidate a → candidate b → a < b → gone (entry b) a ∨ gone (entry b) b) ↔
    (∀ a b, viable a → viable b → a < b →
      (∀ c, a < c → c < b → ¬ viable c) → gone (entry b) a) := by
  intro viable
  classical
  constructor
  · intro separated a b ha hb ab _
    exact (separated a b ha.1 hb.1 ab).resolve_right hb.2
  · intro neighbors a b ha hb ab
    by_cases deadB : gone (entry b) b
    · exact Or.inr deadB
    left
    by_cases deadA : gone (entry a) a
    · exact persist (ordered ab.le) deadA
    have later : ∃ c, a < c ∧ viable c := ⟨b, ab, hb, deadB⟩
    let c := Nat.find later
    obtain ⟨ac, hc⟩ := Nat.find_spec later
    have cb : c ≤ b := Nat.find_min' later ⟨ab, hb, deadB⟩
    apply persist (ordered cb)
    apply neighbors a c ⟨ha, deadA⟩ hc ac
    intro d ad dc hd
    exact Nat.find_min later dc ⟨ad, hd⟩

/-- The neighboring-value condition is equivalent to the original all-pairs
exception test, including values whose entire lifetime precedes the cutoff. -/
theorem H2_iff_all_pairs : H2 ↔
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let exceptional := fun a : ℕ =>
    ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
  ∀ a b : ℕ, Q a → Q b → a < b → exceptional a → exceptional b →
    let e := max 1679994603391465890567050011123964902522794012673156461548944387 ((2*b+2)/3)
    e ≤ a → ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ e ∧ (s ∣ a ∨ s ∣ b) := by
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  let exc := fun a : ℕ => ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
  let entry := fun a : ℕ => max 1679994603391465890567050011123964902522794012673156461548944387 ((2*a+2)/3)
  let gone := fun (x a : ℕ) => a < x ∨ ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ x ∧ s ∣ a
  have ordered : Monotone entry := by intro a b h; dsimp [entry]; omega
  have persist {x y a} (xy : x ≤ y) (h : gone x a) : gone y a := by
    rcases h with h | ⟨s, big, qs, sq, dv⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨s,big,qs,sq.trans xy,dv⟩
  have bridge := no_overlap_iff_consecutive (fun a => Q a ∧ exc a) entry gone ordered persist
  constructor
  · intro h
    dsimp only
    intro a b qa qb ab ea eb lo
    have check := bridge.mpr (by
      intro u v hu hv uv gap
      exact h u v ⟨hu.1.1,hu.1.2,hu.2⟩ ⟨hv.1.1,hv.1.2,hv.2⟩ uv
        (fun w uw wv hw => gap w uw wv ⟨⟨hw.1,hw.2.1⟩,hw.2.2⟩)) a b ⟨qa,ea⟩ ⟨qb,eb⟩ ab
    change entry b ≤ a at lo
    rcases check with (dead | ⟨s,hs,qs,sq,dv⟩) | (dead | ⟨s,hs,qs,sq,dv⟩)
    · omega
    · exact ⟨s,hs,qs,sq,Or.inl dv⟩
    · omega
    · exact ⟨s,hs,qs,sq,Or.inr dv⟩
  · intro h a b ha hb ab gap
    apply bridge.mp _ a b ⟨⟨ha.1,ha.2.1⟩,ha.2.2⟩ ⟨⟨hb.1,hb.2.1⟩,hb.2.2⟩ ab
      (fun w aw wb hw => gap w aw wb ⟨hw.1.1,hw.1.2,hw.2⟩)
    intro u v hu hv uv
    by_cases lo : entry v ≤ u
    · obtain ⟨s,hs,qs,sq,dv⟩ := h u v hu.1 hv.1 uv hu.2 hv.2 lo
      exact dv.elim (fun d => Or.inl (Or.inr ⟨s,hs,qs,sq,d⟩))
        (fun d => Or.inr (Or.inr ⟨s,hs,qs,sq,d⟩))
    · exact Or.inl (Or.inl (by omega))

/-- Every value lives on one interval of integer window endpoints. A number d
that divides a and is least among its eligible divisors causes the first
sieve loss at d². The geometric upper endpoint a can occur earlier. -/
theorem lifetime_of_least_divisor (Q : ℕ → Prop) {a d : ℕ}
    (big : 1000 ≤ d) (qd : Q d) (divides : d ∣ a)
    (least : ∀ s, 1000 ≤ s → Q s → s ∣ a → d ≤ s) (x : ℕ) :
    (x ≤ a ∧ 2*a ≤ 3*x ∧ ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) ↔
    ((2*a+2)/3 ≤ x ∧ x ≤ a ∧ x < d*d) := by
  constructor
  · rintro ⟨lo,hi,clean⟩
    exact ⟨by omega,lo,lt_of_not_ge (fun sq => clean d big qd sq divides)⟩
  · rintro ⟨lo,hi,small⟩
    refine ⟨hi,by omega,?_⟩
    intro s hs qs sq dv
    have le := least s hs qs dv
    exact (Nat.not_le_of_lt small) ((Nat.mul_le_mul le le).trans sq)

/-- For a finite range of windows the final endpoint takes the place of a
future arrival. Tests just before usable arrivals include simultaneous arrivals
once and use the old witnesses before any new value can be used. -/
theorem pair_on_segment_iff (Q : ℕ → Prop) (start last : ℕ) (order : start ≤ last) :
    let birth := fun a : ℕ => (2*a+2)/3
    let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
    let pair := fun x : ℕ => ∃ a b, live x a ∧ live x b ∧ a < b
    (∀ x, start ≤ x → x ≤ last → pair x) ↔
      pair last ∧ (∀ c, start < birth c → birth c ≤ last → live (birth c) c → pair (birth c-1)) := by
  intro birth live pair
  constructor
  · intro cover
    exact ⟨cover last order le_rfl,fun c lo hi _ => cover _ (by omega) (by omega)⟩
  · rintro ⟨final,checks⟩ x lo hi
    classical
    have next : ∃ e : ℕ, x < e ∧
        (e = last+1 ∨ ∃ c, birth c = e ∧ live e c) :=
      ⟨last+1,by omega,Or.inl rfl⟩
    let e := Nat.find next
    obtain ⟨after,why⟩ := Nat.find_spec next
    change x < e at after
    have limit : e ≤ last+1 := Nat.find_min' next ⟨by omega,Or.inl rfl⟩
    have atEnd : pair (e-1) := by
      rcases why with h | ⟨c,h,hc⟩
      · change e = last+1 at h
        simpa [h] using final
      · change birth c = e at h
        by_cases eq : e = last+1
        · simpa [eq] using final
        · rw [← h]
          exact checks c (by omega) (by omega) (h.symm ▸ hc)
    obtain ⟨a,b,ha,hb,ab⟩ := atEnd
    have back (z : ℕ) (hz : live (e-1) z) : live x z := by
      obtain ⟨qz,left,right,clean⟩ := hz
      have br : birth z ≤ e-1 := by dsimp [birth]; omega
      have born : birth z ≤ x := by
        by_contra! late
        have usable : live (birth z) z :=
          ⟨qz,by omega,by dsimp [birth]; omega,fun s hs qs sq => clean s hs qs (sq.trans br)⟩
        have least := Nat.find_min' next (show x < birth z ∧
          (birth z = last+1 ∨ ∃ c, birth c = birth z ∧ live (birth z) c) from
          ⟨late,Or.inr ⟨z,rfl,usable⟩⟩)
        change e ≤ birth z at least
        omega
      exact ⟨qz,by omega,by dsimp [birth] at born; omega,
        fun s hs qs sq => clean s hs qs (by omega)⟩
    exact ⟨a,b,back a ha,back b hb,ab⟩

/-- It suffices to check pairs just before each usable arrival, provided such
arrivals are cofinal. The two pre-arrival witnesses survive throughout the gap. -/
theorem pair_supply_iff_arrivals (Q : ℕ → Prop) (start : ℕ) :
    let birth := fun a : ℕ => (2*a+2)/3
    let live := fun x a : ℕ => Q a ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a
    let pair := fun x : ℕ => ∃ a b, live x a ∧ live x b ∧ a < b
    (∀ x, start ≤ x → pair x) ↔
      (∀ x, start ≤ x → ∃ c, x < birth c ∧ live (birth c) c) ∧
      (∀ c, start < birth c → live (birth c) c → pair (birth c-1)) := by
  intro birth live pair
  have retreat {x y a : ℕ} (h : live y a) (born : birth a ≤ x) (le : x ≤ y) : live x a := by
    obtain ⟨qa,lo,hi,clean⟩ := h
    dsimp [birth] at born
    exact ⟨qa,le.trans lo,by omega,fun s hs qs sq => clean s hs qs (sq.trans le)⟩
  have atBirth {x a : ℕ} (h : live x a) : live (birth a) a := by
    apply retreat h le_rfl
    have hi := h.2.2.1
    dsimp [birth]; omega
  constructor
  · intro supply
    constructor
    · intro x hx
      obtain ⟨a,_,ha,_,_⟩ := supply (3*(x+1)) (by omega)
      have lo := ha.2.1
      exact ⟨a,by dsimp [birth]; omega,atBirth ha⟩
    · intro c bound _
      exact supply _ (by omega)
  · rintro ⟨cofinal,checks⟩ x hx
    obtain ⟨c,after,usable⟩ := cofinal x hx
    have last := checks c (by omega) usable
    exact (pair_on_segment_iff Q start (birth c-1) (by omega)).mpr
      ⟨last,fun z lower _ hz => checks z lower hz⟩ x hx (by omega)

/-- For a strictly increasing enumeration whose first value reaches start,
two values lie in every window exactly when the initial pair fits and the
value two positions ahead fits the first window after the old value leaves. -/
theorem two_values_iff_spacing (v : ℕ → ℕ) (inc : StrictMono v) (start : ℕ)
    (first : start ≤ v 0) :
    (∀ x, start ≤ x → ∃ i j : ℕ, i < j ∧ x ≤ v i ∧ 2*v j ≤ 3*x) ↔
    (2*v 1 ≤ 3*start ∧ ∀ i, 2*v (i+2) ≤ 3*(v i+1)) := by
  constructor
  · intro cover
    constructor
    · obtain ⟨i,j,ij,_,hi⟩ := cover start le_rfl
      have := inc.monotone (show 1 ≤ j by omega)
      omega
    · intro i
      have h := inc.monotone (Nat.zero_le i)
      obtain ⟨j,k,jk,lo,hi⟩ := cover (v i+1) (by omega)
      have ij : i < j := by
        by_contra! inv
        have := inc.monotone inv
        omega
      have := inc.monotone (show i+2 ≤ k by omega)
      omega
  · rintro ⟨initial,spacing⟩ x hx
    have reaches : ∃ i, x ≤ v i := ⟨x,inc.id_le x⟩
    let j := Nat.find reaches
    have lo : x ≤ v j := Nat.find_spec reaches
    refine ⟨j,j+1,by omega,lo,?_⟩
    cases eq : j with
    | zero => simpa using initial.trans (Nat.mul_le_mul_left 3 hx)
    | succ i =>
      have early : i < Nat.find reaches := by change i < j; omega
      have prev := Nat.find_min reaches early
      have := spacing i
      change 2*v (i+2) ≤ 3*x
      omega

/-- The arrival formulation recovers exactly the original sparse-pair supply. -/
theorem H1_iff_pair_supply : H1 ↔
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  ∀ x : ℕ, 1679994603391465890567050011123964902522794012673156461548944387 ≤ x →
    ∃ a b : ℕ, Q a ∧ Q b ∧ x ≤ a ∧ a < b ∧ 2*b ≤ 3*x ∧
      ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a ∧ ¬ s ∣ b := by
  let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
  have windows := pair_supply_iff_arrivals Q 1679994603391465890567050011123964902522794012673156461548944387
  constructor
  · intro h q x hx
    obtain ⟨a,b,ha,hb,ab⟩ := windows.mpr h x hx
    exact ⟨a,b,ha.1,hb.1,ha.2.1,ab,hb.2.2.1,
      fun s hs qs sq => ⟨ha.2.2.2 s hs qs sq,hb.2.2.2 s hs qs sq⟩⟩
  · intro h
    apply windows.mp
    intro x hx
    obtain ⟨a,b,qa,qb,lo,ab,hi,clean⟩ := h x hx
    exact ⟨a,b,⟨qa,lo,by omega,fun s hs qs sq => (clean s hs qs sq).1⟩,
      ⟨qb,by omega,hi,fun s hs qs sq => (clean s hs qs sq).2⟩,ab⟩

/-- For values that pass the sieve until they leave the window, estimating the
spacing of every second value suffices; intermediate integer windows need no tests. -/
theorem H1_of_clean_spacing (v : ℕ → ℕ) (inc : StrictMono v)
    (first : 1679994603391465890567050011123964902522794012673156461548944387 ≤ v 0) (initial : 2*v 1 ≤ 3*1679994603391465890567050011123964902522794012673156461548944387)
    (spacing : ∀ i, 2*v (i+2) ≤ 3*(v i+1))
    (terms : ∀ i, (∃ m : ℕ, 0 < m ∧ v i = strictPartitionCount m) ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
        s*s ≤ v i → ¬ s ∣ v i) : H1 := by
  apply H1_iff_pair_supply.mpr
  intro q x hx
  obtain ⟨i,j,ij,lo,hi⟩ := (two_values_iff_spacing v inc _ first).mpr ⟨initial,spacing⟩ x hx
  have lt := inc ij
  exact ⟨v i,v j,(terms i).1,(terms j).1,lo,lt,hi,
    fun s hs qs sq => ⟨(terms i).2 s hs qs (sq.trans lo),
      (terms j).2 s hs qs (sq.trans (lo.trans lt.le))⟩⟩

/-- Every subset of {1,...,k} extends to a distinct partition of n by adding
a unique part greater than k. -/
theorem pow_le_strictCount (k n : ℕ) (hn : k*(k+1)/2 + k < n) :
    2^k ≤ strictPartitionCount n := by
  let base := Icc 1 k
  have hc : base.card = k := by simp [base, Nat.card_Icc]
  have weight {s : Finset ℕ} (h : s ∈ base.powerset) : ∑ i ∈ s, i ≤ k*(k+1)/2 := by
    calc ∑ i ∈ s, i ≤ ∑ i ∈ base, i :=
           sum_le_sum_of_subset_of_nonneg (mem_powerset.mp h) (by intros; omega)
         _ = k*(k+1)/2 := by
           have eq : insert 0 base = range (k+1) := by ext i; simp [base]; omega
           have total := Finset.sum_range_id (k+1)
           rw [← eq,sum_insert (by simp [base])] at total
           simpa [Nat.mul_comm] using total
  let pad (s : Finset ℕ) := n - ∑ i ∈ s, i
  have large {s : Finset ℕ} (h : s ∈ base.powerset) : k < pad s := by
    have := weight h
    dsimp [pad]
    omega
  rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_subsetCount, ← hc, ← card_powerset]
  apply card_le_card_of_injOn (fun s => insert (pad s) s)
  · intro s hs
    have hl := large hs
    have hf : pad s ∉ s := fun h => (Nat.not_lt_of_ge (mem_Icc.mp (mem_powerset.mp hs h)).2) hl
    refine mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_⟩
    · intro i hi
      rcases mem_insert.mp hi with rfl | h
      · exact mem_Icc.mpr ⟨by omega, Nat.sub_le ..⟩
      · have := mem_Icc.mp (mem_powerset.mp hs h)
        exact mem_Icc.mpr ⟨this.1, by omega⟩
    · rw [sum_insert hf]
      have := weight hs
      dsimp [pad]
      omega
  · intro s hs t ht he
    have recover {u : Finset ℕ} (hu : u ∈ base.powerset) :
        (insert (pad u) u).filter (· ≤ k) = u := by
      ext i
      have := large hu
      simp only [mem_filter, mem_insert]
      exact ⟨fun ⟨h, hk⟩ => h.resolve_left (by omega),
        fun h => ⟨Or.inr h, (mem_Icc.mp (mem_powerset.mp hu h)).2⟩⟩
    exact (recover hs).symm.trans ((congrArg (fun u : Finset ℕ => u.filter (· ≤ k)) he).trans (recover ht))

/-- All strict partition values below 2^k occur among these first indices. -/
theorem index_bound {n k : ℕ} (h : strictPartitionCount n < 2^k) : n ≤ k*(k+1)/2+k := by
  by_contra hn
  exact (Nat.not_lt_of_ge (pow_le_strictCount k n (by omega))) h

theorem disjoint_band_count (q : ℕ → ℕ) (K r : ℕ) (pool : Finset ℕ)
    (A : ℕ → Finset ℕ)
    (size : ∀ j ∈ Ico K (2*K), r ≤ (A j).card)
    (band : ∀ j ∈ Ico K (2*K), ∀ a ∈ A j, 2^j ≤ a ∧ a < 2^(j+1) ∧ a ∈ pool.image q) :
    K*r ≤ pool.card := by
  let J := Ico K (2*K)
  have dis : (J : Set ℕ).PairwiseDisjoint A := by
    intro i hi j hj ne
    apply Finset.disjoint_left.mpr
    intro a hai haj
    obtain ⟨li,ui,_⟩ := band i hi a hai
    obtain ⟨lj,uj,_⟩ := band j hj a haj
    rcases lt_or_gt_of_ne ne with lt | gt
    · have e := Nat.pow_le_pow_right (by decide : 0 < 2) (show i+1 ≤ j by omega)
      omega
    · have e := Nat.pow_le_pow_right (by decide : 0 < 2) (show j+1 ≤ i by omega)
      omega
  have sub : J.biUnion A ⊆ pool.image q := by
    intro a ha
    obtain ⟨j,hj,h⟩ := mem_biUnion.mp ha
    exact (band j hj a h).2.2
  calc
    K*r = ∑ _j ∈ J, r := by simp [J,Nat.card_Ico]; omega
    _ ≤ ∑ j ∈ J, (A j).card := sum_le_sum size
    _ = (J.biUnion A).card := (card_biUnion dis).symm
    _ ≤ (pool.image q).card := card_le_card sub
    _ ≤ _ := card_image_le

/-- The logarithmic survivor quota forces quadratically many indices missing
the fixed divisor q(45). Gordon--Ono's density-one theorem contradicts this
bound as K tends to infinity. The density theorem itself is external. -/
theorem logarithmic_quota_obstruction (K : ℕ)
    (start : 30020900773769688559070113208459541809716021698140392739697 ≤ 2^K)
    (supply : ∀ x : ℕ, 2^K ≤ x → ∃ A : Finset ℕ, x.log2/32 < A.card ∧
      ∀ a ∈ A, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
        ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → s*s ≤ x → ¬ s ∣ a) :
    let k := 2*K
    K*(K/32+1) ≤ ((range (k*(k+1)/2+k+1)).filter
      (fun m => strictPartitionCount m % 2048 ≠ 0)).card := by
  classical
  let J := Ico K (2*K)
  have witness (j : ℕ) (hj : j ∈ J) := supply (2^j)
    (Nat.pow_le_pow_right (by decide) (mem_Ico.mp hj).1)
  let A (j : ℕ) : Finset ℕ := if h : j ∈ J then (witness j h).choose else ∅
  have spec (j : ℕ) (hj : j ∈ J) := (witness j hj).choose_spec
  apply disjoint_band_count strictPartitionCount K (K/32+1) _ A
  · intro j hj
    have count := (spec j hj).1
    have logeq : (2^j).log2 = j := Nat.log2_two_pow
    have le := (mem_Ico.mp hj).1
    change j ∈ J at hj
    simp only [A,dif_pos hj]
    omega
  · intro j hj a ha
    change j ∈ J at hj
    simp only [A,dif_pos hj] at ha
    obtain ⟨⟨m,_,rfl⟩,lo,hi,clean⟩ := (spec j hj).2 a ha
    have powPos : 0 < 2^j := by positivity
    have upper : strictPartitionCount m < 2^(j+1) := by rw [pow_succ]; omega
    have q45 : strictPartitionCount 45 = 2048 := by
      rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 45 45 le_rfl]; decide +kernel
    have lowPow := Nat.pow_le_pow_right (by decide : 0 < 2) (mem_Ico.mp hj).1
    have avoid := clean 2048 (by decide) ⟨45,by decide,q45.symm⟩ (by omega)
    have index := index_bound (upper.trans_le (Nat.pow_le_pow_right (by decide)
      (show j+1 ≤ 2*K from (mem_Ico.mp hj).2)))
    exact ⟨lo,upper,mem_image.mpr ⟨m,mem_filter.mpr ⟨mem_range.mpr (by omega),
      fun eq => avoid (Nat.dvd_of_mod_eq_zero eq)⟩,rfl⟩⟩

/-- The density-zero consequence needed from Gordon--Ono is a single eventual
bound of one index in 128. Under it, the logarithmic quota is impossible. -/
theorem not_logarithmic_quota
    (sparse : ∃ M : ℕ, ∀ N : ℕ, M ≤ N →
      128*((range N).filter (fun m => strictPartitionCount m % 2048 ≠ 0)).card < N) :
    ¬ (∀ x : ℕ, 30020900773769688559070113208459541809716021698140392739697 ≤ x →
      ∃ A : Finset ℕ, x.log2/32 < A.card ∧ ∀ a ∈ A,
        (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
        ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → s*s ≤ x → ¬ s ∣ a) := by
  rintro allWindows
  obtain ⟨M,upper⟩ := sparse
  let h := M+200
  let K := 32*h
  have Kbig : 200 ≤ K := by dsimp [K,h]; omega
  have base : 30020900773769688559070113208459541809716021698140392739697 ≤ 2^K :=
    (by decide : 30020900773769688559070113208459541809716021698140392739697 ≤ 2^200).trans
      (Nat.pow_le_pow_right (by decide) Kbig)
  have lower := logarithmic_quota_obstruction K base (fun x hx => allWindows x (base.trans hx))
  let N := 2*K*(2*K+1)/2 + 2*K + 1
  have reach : M ≤ N := by dsimp [N,K,h]; omega
  have ub := upper N reach
  change K*(K/32+1) ≤ ((range N).filter _).card at lower
  have bound : N ≤ 128*(K*(K/32+1)) := by
    dsimp only [N,K]
    rw [Nat.mul_div_cancel_left _ (by decide : 0 < 32)]
    have hh : 1 ≤ h := by dsimp [h]; omega
    have frac := Nat.div_mul_le_self (2*(32*h)*(2*(32*h)+1)) 2
    nlinarith [Nat.mul_le_mul_right h hh]
  omega

/-- Earliest common window equals max(start, ceil(2*b/3)). Testing the
small divisors there is equivalent to excluding the pair at every common window. -/
theorem first_common_window_iff (Q : ℕ → Prop) (start a b : ℕ) :
    (∀ x, start ≤ x → x ≤ a → 2*b ≤ 3*x →
      ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ x ∧ (s ∣ a ∨ s ∣ b)) ↔
    (let e := max start ((2*b+2)/3)
     e ≤ a → ∃ s, 1000 ≤ s ∧ Q s ∧ s*s ≤ e ∧ (s ∣ a ∨ s ∣ b)) := by
  constructor
  · intro h e he
    exact h e (le_max_left ..) he (by dsimp [e]; have := le_max_right start ((2*b+2)/3); omega)
  · intro h x hx ha hb
    have le : max start ((2*b+2)/3) ≤ x := max_le hx (by omega)
    obtain ⟨s,hs,qs,sq,div⟩ := h (le.trans ha)
    exact ⟨s,hs,qs,sq.trans le,div⟩

/-- An actual pair of exceptions shares an early window. The geometric and
small-divisor tests by themselves cannot exclude all pairs down to x = 1. -/
theorem early_exception_pair :
    let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
    let exc := fun a : ℕ => ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
    let a := strictPartitionCount 110
    let b := strictPartitionCount 114
    let e := (2*b+2)/3
    a < b ∧ e = 918870 ∧ e ≤ a ∧ exc a ∧ exc b ∧
      ∀ s : ℕ, 1000 ≤ s → e < s*s := by
  intro Q exc a b e
  have q45 : strictPartitionCount 45 = 2048 := by
    rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 45 45 le_rfl]; decide +kernel
  have q46 : strictPartitionCount 46 = 2304 := by
    rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 46 46 le_rfl]; decide +kernel
  have va : a = 1004544 := by
    dsimp only [a]; rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 110 110 le_rfl]; decide +kernel
  have vb : b = 1378304 := by
    dsimp only [b]; rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 114 114 le_rfl]; decide +kernel
  have endpoint : e = 918870 := by dsimp only [e]; omega
  refine ⟨by omega,endpoint,by omega,?_,?_,?_⟩
  · rw [va]; exact ⟨436,by decide,by decide,by decide,by decide,46,by decide,q46.symm⟩
  · rw [vb]; exact ⟨673,by decide,by decide,by decide,by decide,45,by decide,q45.symm⟩
  · intro s hs
    have lower := Nat.mul_le_mul hs hs
    omega

/-- The overlap at indices 110 and 114 persists up to the smaller value
itself. Any proposed cutoff at or below 1004544 retains a violating window. -/
theorem early_overlap_through_last (start : ℕ) (bound : start ≤ 1004544) :
    let Q := fun a : ℕ => ∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m
    let exc := fun a : ℕ => ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k)
    ∃ a b : ℕ, Q a ∧ Q b ∧ a < b ∧ exc a ∧ exc b ∧
      max start ((2*b+2)/3) ≤ a ∧
      ∀ x, max start ((2*b+2)/3) ≤ x → x ≤ a →
        ∀ s : ℕ, 1000 ≤ s → s*s ≤ x → ¬ s ∣ a ∧ ¬ s ∣ b
      := by
  intro Q exc
  obtain ⟨ab,_,_,ea,eb,_⟩ := early_exception_pair
  have va : strictPartitionCount 110 = 1004544 := by
    rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 110 110 le_rfl]; decide +kernel
  have vb : strictPartitionCount 114 = 1378304 := by
    rw [OMA.R_oeis_a000009_R10.strictPartitionCount_eq_rec 114 114 le_rfl]; decide +kernel
  refine ⟨_,_,⟨110,by decide,rfl⟩,⟨114,by decide,rfl⟩,ab,ea,eb,?_,?_⟩
  · rw [va,vb]; omega
  intro x _ hx s hs sq
  rw [va] at hx
  rw [va,vb]
  have small : s < 1003 := by
    by_contra! big
    have := Nat.mul_le_mul big big
    omega
  have cases : s = 1000 ∨ s = 1001 ∨ s = 1002 := by omega
  rcases cases with rfl | rfl | rfl <;> decide

/-- After sieving, a proper partition divisor exists exactly when a short
cofactor gives one. Multiple factorizations of the same value cost one exception. -/
theorem short_cofactor_iff (Q : ℕ → Prop) (x a : ℕ) (hi : 2*a ≤ 3*x)
    (clean : ∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) :
    (∃ s, 1000 ≤ s ∧ Q s ∧ 2*s ≤ a ∧ s ∣ a) ↔
      ∃ k : ℕ, 2 ≤ k ∧ 2*k*k < 3*a ∧ k ∣ a ∧ 1000 ≤ a/k ∧ Q (a/k) := by
  constructor
  · rintro ⟨s,hs,qs,low,d⟩
    have large : x < s*s := by
      by_contra! small
      exact clean s hs qs small d
    obtain ⟨k,rfl⟩ := d
    have hk : 2 ≤ k := by
      by_contra! h
      have h' : k = 0 ∨ k = 1 := by omega
      rcases h' with rfl | rfl <;> simp at low <;> omega
    have prod : s*(2*k) < s*(3*s) := by nlinarith
    have short := Nat.lt_of_mul_lt_mul_left prod
    have sq := Nat.mul_lt_mul_of_pos_right short (by omega : 0 < k)
    have div : s*k/k = s := Nat.mul_div_cancel _ (by omega)
    exact ⟨k,hk,by nlinarith only [sq],dvd_mul_left _ _,by rwa [div],by rwa [div]⟩
  · rintro ⟨k,hk,_,dvd,big,qs⟩
    have h := Nat.div_mul_cancel dvd
    exact ⟨a/k,big,qs,by nlinarith [Nat.mul_le_mul_left (a/k) hk],⟨k,h.symm⟩⟩

/-- A least eligible divisor is primitive. Every test that only uses eligible
divisors below a bound can therefore use the primitive divisors alone. -/
theorem least_primitive_divisor (Q : ℕ → Prop) {a : ℕ}
    (existsDiv : ∃ s, 1000 ≤ s ∧ Q s ∧ s ∣ a) :
    ∃ d, (1000 ≤ d ∧ Q d ∧ d ∣ a) ∧
      (∀ s, 1000 ≤ s → Q s → s ∣ a → d ≤ s) ∧
      ∀ t, 1000 ≤ t → Q t → t < d → ¬ t ∣ d := by
  classical
  let d := Nat.find existsDiv
  have spec : 1000 ≤ d ∧ Q d ∧ d ∣ a := Nat.find_spec existsDiv
  have least (s) (hs : 1000 ≤ s) (qs : Q s) (dv : s ∣ a) : d ≤ s :=
    Nat.find_min' existsDiv ⟨hs,qs,dv⟩
  exact ⟨d,spec,least,fun t ht qt lt dv => (Nat.not_le_of_lt lt) (least t ht qt (dv.trans spec.2.2))⟩

theorem sieve_iff_primitive (Q : ℕ → Prop) (a x : ℕ) :
    (∀ s, 1000 ≤ s → Q s → s*s ≤ x → ¬ s ∣ a) ↔
    (∀ d, 1000 ≤ d → Q d → (∀ t, 1000 ≤ t → Q t → t < d → ¬ t ∣ d) →
      d*d ≤ x → ¬ d ∣ a) := by
  constructor
  · exact fun h d hd qd _ => h d hd qd
  · intro h s hs qs sq dv
    obtain ⟨d,⟨hd,qd,da⟩,least,prim⟩ := least_primitive_divisor Q ⟨s,hs,qs,dv⟩
    have ds := least s hs qs dv
    exact h d hd qd prim ((Nat.mul_le_mul ds ds).trans sq) da

/-- For an increasing sequence starting in the tail, single-value coverage
is equivalent to the first value fitting and each successor fitting at v(i)+1. -/
theorem one_value_iff_spacing (v : ℕ → ℕ) (inc : StrictMono v) (start : ℕ)
    (first : start ≤ v 0) :
    (∀ x, start ≤ x → ∃ i, x ≤ v i ∧ 2*v i ≤ 3*x) ↔
    (2*v 0 ≤ 3*start ∧ ∀ i, 2*v (i+1) ≤ 3*(v i+1)) := by
  constructor
  · intro cover
    constructor
    · obtain ⟨j,_,hi⟩ := cover start le_rfl
      have := inc.monotone (Nat.zero_le j)
      omega
    · intro i
      have := inc.monotone (Nat.zero_le i)
      obtain ⟨j,lo,hi⟩ := cover (v i+1) (by omega)
      have ij : i < j := by
        by_contra! h
        have := inc.monotone h
        omega
      have := inc.monotone (show i+1 ≤ j by omega)
      omega
  · rintro ⟨initial,gaps⟩ x hx
    have reaches : ∃ i, x ≤ v i := ⟨x,inc.id_le x⟩
    let j := Nat.find reaches
    refine ⟨j,Nat.find_spec reaches,?_⟩
    cases eq : j with
    | zero => exact initial.trans (Nat.mul_le_mul_left 3 hx)
    | succ i =>
      have early : i < Nat.find reaches := by change i < j; omega
      have prev := Nat.find_min reaches early
      have := gaps i
      omega

/-- Adding a part of size one injects odd partitions of n into those of n+1. -/
theorem strictCount_monotone : Monotone strictPartitionCount := by
  apply monotone_nat_of_le_succ
  intro n
  let addOne (p : Nat.Partition n) : Nat.Partition (n+1) :=
    ⟨1 ::ₘ p.parts, fun hi => by
      rcases Multiset.mem_cons.mp hi with rfl | h
      · decide
      · exact p.parts_pos h, by simp [p.parts_sum, Nat.add_comm]⟩
  unfold strictPartitionCount
  rw [← Nat.Partition.card_odds_eq_card_distincts, ← Nat.Partition.card_odds_eq_card_distincts]
  apply Finset.card_le_card_of_injOn addOne
  · intro p hp
    change p ∈ Nat.Partition.odds n at hp
    change addOne p ∈ Nat.Partition.odds (n+1)
    simp only [Nat.Partition.odds,Nat.Partition.restricted,Finset.mem_filter,Finset.mem_univ,true_and] at hp ⊢
    intro j hj
    rcases Multiset.mem_cons.mp hj with rfl | h
    · decide
    · exact hp j h
  · intro p _ q _ eq
    have parts := congrArg Nat.Partition.parts eq
    exact Nat.Partition.ext ((Multiset.cons_inj_right 1).mp parts)


/-- Under a bounded successor rule, every target between the first and last
intervals has a witness. Advancing at n = 2*a handles the puncture exactly. -/
theorem walk_to_window (P : ℕ → Prop) (start cap n : ℕ) (seed : P start)
    (enter : start+20301 ≤ n) (finish : n < 2*cap)
    (step : ∀ a, start ≤ a → a < cap → P a →
      ∃ b, P b ∧ a < b ∧ b+20301 ≤ 2*a) :
    ∃ a, P a ∧ a+20301 ≤ n ∧ n < 2*a := by
  have walk (fuel a : ℕ) (room : n-a ≤ fuel) (lo : start ≤ a) (pa : P a)
      (begun : a+20301 ≤ n) : ∃ b, P b ∧ b+20301 ≤ n ∧ n < 2*b := by
    induction fuel generalizing a with
    | zero => exact ⟨a,pa,begun,by omega⟩
    | succ k ih =>
      by_cases done : n < 2*a
      · exact ⟨a,pa,begun,done⟩
      · obtain ⟨b,pb,ab,joined⟩ := step a lo (by omega) pa
        exact ih b (by omega) (by omega) pb (by omega)
  exact walk (n-start) start le_rfl le_rfl seed enter


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- One coefficient table certifies all anchor values and both finite covers. -/
theorem certified_anchors : ∃ anchors : List (ℕ × ℕ),
    (∀ p ∈ anchors, ((∃ m : ℕ, 0 < m ∧ p.2 = strictPartitionCount m) ∧ 1000 ≤ p.2 ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ p.2 → ¬ s ∣ p.2)) ∧
    (∀ x : ℕ, 30020900773769688559070113208459541809716021698140392739697 ≤ x → x ≤ 276023389780623855438063152323965130729038773266014399686920 → ∃ p ∈ anchors, x ≤ p.2 ∧ 2*p.2 ≤ 3*x) ∧
    (6400,276023389780623855438063152323965130729038773266014399686920) ∈ anchors ∧ (7200,1679994603391465890567050011123964902522794012673156461548944386) ∈ anchors ∧
    (∀ p ∈ anchors, 276023389780623855438063152323965130729038773266014399686920 ≤ p.2 → p.2 < 1679994603391465890567050011123964902522794012673156461548944386 →
      ∃ t ∈ anchors, p.2 < t.2 ∧ t.2+20301 ≤ 2*p.2) := by
  let anchors : List (ℕ × ℕ) := [
  (6239,44826794016581556250544938982581728865028321268192943520904),
  (6274,66680318010064817431288052608654976684760184135495679796496),
  (6309,99079160533597511423515637370567450822658831452683296206384),
  (6344,147060341243876743488499752631145710947549132583706573295768),
  (6379,218042565909576324675379726336707731776070644382680502521656),
  (6400,276023389780623855438063152323965130729038773266014399686920),
  (6461,546345860390556982263106684688179216519702820309657455438060),
  (6523,1090019641132984489077292860787142236184947225893943207093248),
  (6585,2167671246712939239161395070722706310871252950329691861237824),
  (6647,4296992874046506441141366858174110924212694826131616423300948),
  (6709,8491163711535472885633896994306974483647094825710104423511890),
  (6772,16910569644576851575910896498245663052745111278858013229064666),
  (6835,33571813503089408858870936848696718708357412961464161793656320),
  (6898,66440935661882795401721933413376140642209214348393150207035790),
  (6962,132505308230651576204643342966177708862571072364318371751038144),
  (7025,260625536886300107736770313340272338444126879718189720507162554),
  (7089,516572727588717496750857457358311137787505905120221588905046048),
  (7154,1031649795851428908646755731957293828797122105492727814485870702),
  (7200,1679994603391465890567050011123964902522794012673156461548944386)]

  let mask := (2^(212*7201)-1)/(2^212-1)*2^211
  let row := Nat.rec (motive := fun _ => ℕ) (2^((211+1)*7200)) (fun k b =>
    let c := b + (b >>> (212*(k+1)))
    if c &&& mask == 0 then c else 0)
  let digit := fun j : ℕ => (row 7200 >>> (212*(7200-j))) % 2^212
  let valid := fun (p : ℕ × ℕ) => decide (1000 ≤ p.2 ∧ 0 < p.1 ∧ p.1 ≤ 7200 ∧ digit p.1 = p.2 ∧ p.2 ≤ digit 7200) &&
    (List.range 7201).all (fun j => decide (1000 ≤ digit j → 2*digit j ≤ p.2 → ¬ digit j ∣ p.2))
  have checked : row 7200 ≠ 0 ∧ anchors.all valid = true := by decide +kernel
  have decode (j : ℕ) (hj : j ≤ 7200) : strictPartitionCount j = digit j :=
    OMA.R_oeis_a000009_R10.strictPartitionCount_of_reverse 211 7200 (by decide) row mask
      (OMA.R_oeis_a000009_R10.guard_mask_eq 212 7201 (2^211) (by decide)).symm
      rfl (fun _ => rfl) checked.1 j hj
  refine ⟨anchors,?_,?_,by decide,by decide,by decide +kernel⟩
  · intro p hp
    have hv := List.all_eq_true.mp checked.2 p hp
    simp only [valid,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hv
    obtain ⟨⟨bigValue,pos,idx,value,cap⟩,test⟩ := hv
    refine ⟨⟨p.1,pos,value.symm.trans (decode _ idx).symm⟩,bigValue,?_⟩
    rintro s big ⟨j,_,rfl⟩ small
    by_cases h : j ≤ 7200
    · rw [decode j h] at big small ⊢
      exact test j (List.mem_range.mpr (by omega)) big small
    · have growth := strictCount_monotone (show 7200 ≤ j by omega)
      rw [← decode 7200 le_rfl] at cap
      omega
  · intro x lo hi
    by_cases h6239 : x ≤ 44826794016581556250544938982581728865028321268192943520904
    · exact ⟨(6239,44826794016581556250544938982581728865028321268192943520904),by decide,by dsimp; omega,by dsimp; omega⟩
    by_cases h6274 : x ≤ 66680318010064817431288052608654976684760184135495679796496
    · exact ⟨(6274,66680318010064817431288052608654976684760184135495679796496),by decide,by dsimp; omega,by dsimp; omega⟩
    by_cases h6309 : x ≤ 99079160533597511423515637370567450822658831452683296206384
    · exact ⟨(6309,99079160533597511423515637370567450822658831452683296206384),by decide,by dsimp; omega,by dsimp; omega⟩
    by_cases h6344 : x ≤ 147060341243876743488499752631145710947549132583706573295768
    · exact ⟨(6344,147060341243876743488499752631145710947549132583706573295768),by decide,by dsimp; omega,by dsimp; omega⟩
    by_cases h6379 : x ≤ 218042565909576324675379726336707731776070644382680502521656
    · exact ⟨(6379,218042565909576324675379726336707731776070644382680502521656),by decide,by dsimp; omega,by dsimp; omega⟩
    exact ⟨(6400,276023389780623855438063152323965130729038773266014399686920),by decide,by dsimp; omega,by dsimp; omega⟩

/-- Six primitive values cover every integer endpoint from the original
R2 cutoff through q(6400), inclusive. -/
theorem primitive_prefix (x : ℕ) (lo : 30020900773769688559070113208459541809716021698140392739697 ≤ x)
    (hi : x ≤ 276023389780623855438063152323965130729038773266014399686920) :
    ∃ a : ℕ, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧
      x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a → ¬ s ∣ a := by
  obtain ⟨_,cert,cover,_,_,_⟩ := certified_anchors
  obtain ⟨p,hp,left,right⟩ := cover x lo hi
  exact ⟨_,(cert p hp).1,left,right,(cert p hp).2.2⟩

/-- Below the first remaining target the native representation intervals are
unconditional, including every target exactly twice an intermediate anchor. -/
theorem finite_native_cover (n : ℕ) (lower : 60041801547539377118140226416919083619432043396280785479393 < n)
    (upper : n < 2*1679994603391465890567050011123964902522794012673156461548944386) :
    ∃ a : ℕ, ((∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ 1000 ≤ a ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a → ¬ s ∣ a) ∧ a+20301 ≤ n ∧ n < 2*a := by
  by_cases early : n < 2*276023389780623855438063152323965130729038773266014399686920
  · obtain ⟨a,qa,lo,hi,prim⟩ := primitive_prefix (n/2+1) (by omega) (by omega)
    exact ⟨a,⟨qa,by omega,prim⟩,by omega,by omega⟩
  obtain ⟨anchors,cert,_,seed,_,links⟩ := certified_anchors
  let P := fun a : ℕ => ∃ p ∈ anchors, p.2 = a
  obtain ⟨a,⟨p,hp,rfl⟩,lo,hi⟩ := walk_to_window P 276023389780623855438063152323965130729038773266014399686920 1679994603391465890567050011123964902522794012673156461548944386 n
    ⟨(6400,276023389780623855438063152323965130729038773266014399686920),seed,rfl⟩ (by omega) upper (by
      rintro a low high ⟨p,hp,rfl⟩
      obtain ⟨t,ht,lt,joined⟩ := links p hp low high
      exact ⟨t.2,⟨t,ht,rfl⟩,lt,joined⟩)
  exact ⟨_,cert p hp,lo,hi⟩

/-- Starting with the last certified anchor, a local successor bound suffices.
For each target the walk terminates after finitely many strict increases. -/
theorem parent_of_local_successors :
    let primitive := fun a : ℕ => ((∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ 1000 ≤ a ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a → ¬ s ∣ a)
    (∀ a : ℕ, 1679994603391465890567050011123964902522794012673156461548944386 ≤ a → primitive a →
    ∃ b, primitive b ∧ a < b ∧ b+20301 ≤ 2*a) → OMA.R_oeis_a000009_R10.H1 := by
  intro primitive step
  apply OMA.R_oeis_a000009_R10.H1_of_intervals
  intro n hn
  have cover : ∃ a, primitive a ∧ a+20301 ≤ n ∧ n < 2*a := by
    by_cases early : n < 2*1679994603391465890567050011123964902522794012673156461548944386
    · exact finite_native_cover n hn early
    · apply walk_to_window primitive 1679994603391465890567050011123964902522794012673156461548944386 (n+1) n
      · obtain ⟨_,cert,_,_,last,_⟩ := certified_anchors
        exact cert (7200,1679994603391465890567050011123964902522794012673156461548944386) last
      · omega
      · omega
      · exact fun a low _ pa => step a low pa
  obtain ⟨a,⟨qa,big,prim⟩,lo,hi⟩ := cover
  exact ⟨a,qa,big,lo,by omega,by omega,prim⟩

/-- In a successor interval below twice the current value, every eligible
proper divisor has partition index strictly below the current index. -/
theorem successor_primitive_iff (m j : ℕ)
    (later : strictPartitionCount m < strictPartitionCount j)
    (near : strictPartitionCount j < 2*strictPartitionCount m) :
    (∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ strictPartitionCount j → ¬ s ∣ strictPartitionCount j) ↔
      ∀ i, 0 < i → i < m → 1000 ≤ strictPartitionCount i →
        ¬ strictPartitionCount i ∣ strictPartitionCount j := by
  constructor
  · intro p i ip im hi dv
    have bound := strictCount_monotone im.le
    obtain ⟨k,eq⟩ := dv
    have two : 2 ≤ k := by
      by_contra! low
      have kle : k ≤ 1 := by omega
      have le := Nat.mul_le_mul_left (strictPartitionCount i) kle
      rw [Nat.mul_one] at le
      omega
    have le := Nat.mul_le_mul_left (strictPartitionCount i) two
    apply p _ hi ⟨i,ip,rfl⟩ (by omega) ⟨k,eq⟩
  · intro test
    rintro s hs ⟨i,ip,rfl⟩ proper
    apply test i ip _ hs
    by_contra! inv
    have := strictCount_monotone inv
    omega

/-- A successor need only avoid divisibility by the finitely many eligible
values at indices before m. There is no separate unboundedness hypothesis. -/
theorem parent_of_index_successors
    (step : ∀ m, 1679994603391465890567050011123964902522794012673156461548944386 ≤ strictPartitionCount m →
      (∀ i, 0 < i → i < m → 1000 ≤ strictPartitionCount i →
        2*strictPartitionCount i ≤ strictPartitionCount m → ¬ strictPartitionCount i ∣ strictPartitionCount m) →
      ∃ j, m < j ∧ strictPartitionCount m < strictPartitionCount j ∧
        strictPartitionCount j+20301 ≤ 2*strictPartitionCount m ∧
        ∀ i, 0 < i → i < m → 1000 ≤ strictPartitionCount i →
          ¬ strictPartitionCount i ∣ strictPartitionCount j) :
    OMA.R_oeis_a000009_R10.H1 := by
  apply parent_of_local_successors
  intro a ha pa
  obtain ⟨m,_,rfl⟩ := pa.1
  obtain ⟨j,mj,lt,joined,test⟩ := step m ha
    (fun i ip _ big small => pa.2.2 _ big ⟨i,ip,rfl⟩ small)
  exact ⟨_,⟨⟨j,by omega,rfl⟩,by omega,(successor_primitive_iff m j lt (by omega)).mpr test⟩,lt,joined⟩

/-- Splice the verified primitive prefix onto any primitive coverage proof
for the remaining windows, then apply the merged representation theorem. -/
theorem parent_of_tail_windows (tail : ∀ x : ℕ, 1679994603391465890567050011123964902522794012673156461548944387 ≤ x →
    ∃ a : ℕ, (∃ m : ℕ, 0 < m ∧ a = strictPartitionCount m) ∧ x ≤ a ∧ 2*a ≤ 3*x ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ a → ¬ s ∣ a) :
    OMA.R_oeis_a000009_R10.H1 := by
  apply OMA.R_oeis_a000009_R10.H1_of_intervals
  intro n hn
  let x := n/2+1
  by_cases early : n < 2*1679994603391465890567050011123964902522794012673156461548944386
  · obtain ⟨a,⟨qa,big,prim⟩,lo,hi⟩ := finite_native_cover n hn early
    exact ⟨a,qa,big,lo,by omega,by omega,prim⟩
  have lo : 1679994603391465890567050011123964902522794012673156461548944387 ≤ x := by dsimp [x]; omega
  obtain ⟨a,qa,left,right,prim⟩ := tail x lo
  exact ⟨a,qa,by omega,by dsimp [x] at right; omega,by dsimp [x] at left; omega,
    by dsimp [x] at left; omega,prim⟩

/-- A single sequence of primitive values can cover the remaining tail. -/
theorem parent_of_primitive_spacing (v : ℕ → ℕ) (inc : StrictMono v)
    (initial : 1679994603391465890567050011123964902522794012673156461548944387 ≤ v 0 ∧ 2*v 0 ≤ 3*1679994603391465890567050011123964902522794012673156461548944387)
    (gaps : ∀ i, 2*v (i+1) ≤ 3*(v i+1))
    (primitive : ∀ i, (∃ m : ℕ, 0 < m ∧ v i = strictPartitionCount m) ∧
      ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) → 2*s ≤ v i → ¬ s ∣ v i) :
    OMA.R_oeis_a000009_R10.H1 := by
  apply parent_of_tail_windows
  intro x hx
  obtain ⟨i,lo,hi⟩ := (one_value_iff_spacing v inc _ initial.1).mpr ⟨initial.2,gaps⟩ x hx
  exact ⟨_,(primitive i).1,lo,hi,(primitive i).2⟩

theorem main : H1 → H2 → OMA.R_oeis_a000009_R10.H1 := by
  intro supply pairs
  let start := 1679994603391465890567050011123964902522794012673156461548944387
  apply parent_of_tail_windows
  intro x hx
  obtain ⟨a,b,qa,qb,lo,ab,hi,clean⟩ := H1_iff_pair_supply.mp supply x hx
  by_contra! missing
  have fail (c : ℕ) (qc : ∃ m : ℕ, 0 < m ∧ c = strictPartitionCount m)
      (lc : x ≤ c) (hc : 2*c ≤ 3*x)
      (safe : ∀ s, 1000 ≤ s → (∃ m : ℕ, 0 < m ∧ s = strictPartitionCount m) →
        s*s ≤ x → ¬ s ∣ c) :=
    (short_cofactor_iff _ x c hc safe).mp (missing c qc lc hc)
  have ea := fail a qa lo (by omega) (fun s hs qs sq => (clean s hs qs sq).1)
  have eb := fail b qb (by omega) hi (fun s hs qs sq => (clean s hs qs sq).2)
  obtain ⟨s,hs,qs,sq,div⟩ := (first_common_window_iff _ start a b).mpr
    (H2_iff_all_pairs.mp pairs a b qa qb ab ea eb) x hx lo hi
  exact div.elim (clean s hs qs sq).1 (clean s hs qs sq).2

end OMA.R_oeis_a000009_R10_H1_R2
