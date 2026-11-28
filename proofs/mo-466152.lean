import OMAStatements.S_mo_466152

/-!
The positive represented values are four times the offsets of the Proth numbers.
Sort these offsets into dyadic intervals. In interval d the possible values have
consecutive high parts of length d / 2 + 1 and a common power-of-two multiplier.
Binary palindromes admit precisely the same ordering by length and high part.

For the permutation, write an odd base x uniquely as 2^m + k with k odd and
k < 2^m. Among the unused entries smaller than its Proth rank, the products
k' * 2^m' are exactly t * 2^(m+1) for 1 ≤ t ≤ k/2. Thus its rank is precisely
the entry that the defining sieve selects.
-/

open OMA.S_mo_466152

namespace ProthEnumeration

private lemma tr_prod {k : ℕ} (hk : Odd k) (m : ℕ) : tr (k * 2^m) = m := by
  have hk' : k ≠ 0 := fun h => by simp [h] at hk
  rw [tr, Nat.factorization_mul hk' (by positivity), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by obtain ⟨v,hv⟩ := hk; omega : ¬ 2 ∣ k),
      Nat.factorization_pow_self Nat.prime_two, zero_add]

private lemma rep_params {k m : ℕ} (hk : Odd k) (hm : 0 < m) (hlt : k < 2^m) :
    Rep (4*(k*2^m)) (2^m+k) (2^m-k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  obtain ⟨u, hu⟩ := hk
  rw [pow_succ] at hlt ⊢
  have he : 2^j*2-k+k=2^j*2 := by omega
  refine ⟨by omega, by omega, ⟨2^j+u, by omega⟩, ⟨2^j-u-1, by omega⟩,
    ⟨j+2, by rw [show j+2=(j+1)+1 by omega, pow_succ,pow_succ]; omega⟩, ?_⟩
  have H : (2^j*2+k)^2 = (2^j*2-k)^2 + 4*(k*(2^j*2)) := by
    nlinarith only [congrArg (fun w : ℕ => w^2) he, congrArg (fun w : ℕ => k*w) he]
  omega

private lemma params_of_rep {v x y : ℕ} (H : Rep v x y) :
    ∃ k m : ℕ, Odd k ∧ 0 < m ∧ k < 2^m ∧ v = 4*(k*2^m) ∧ x = 2^m+k ∧ y = 2^m-k := by
  obtain ⟨hy,hxy,⟨u,hu⟩,⟨w,hw⟩,⟨h,hs⟩,hv⟩ := H
  obtain _ | _ | j := h
  · simp at hs; omega
  · norm_num at hs; omega
  rw [pow_succ,pow_succ] at hs
  let k := x - 2^j*2
  have hx : x = 2^j*2+k := by dsimp [k]; omega
  have hyy : y = 2^j*2-k := by omega
  have hk : Odd k := ⟨u-2^j, by omega⟩
  have hlt : k < 2^(j+1) := by rw [pow_succ]; omega
  have hr := (rep_params hk (by omega : 0 < j+1) hlt).2.2.2.2.2
  refine ⟨k,j+1,hk,by omega,hlt,?_,?_,?_⟩ <;> rw [pow_succ] at *
  · rw [hx,hyy] at hv
    exact hv.trans hr.symm
  · exact hx
  · exact hyy

private lemma rep_unique {v x y X Y : ℕ} (h : Rep v x y) (H : Rep v X Y) : x = X ∧ y = Y := by
  obtain ⟨k,m,hk,_,_,hv,rfl,rfl⟩ := params_of_rep h
  obtain ⟨K,M,hK,_,_,hV,rfl,rfl⟩ := params_of_rep H
  have eq : k*2^m = K*2^M := by omega
  have hm := congrArg tr eq
  rw [tr_prod hk, tr_prod hK] at hm
  subst M
  have := Nat.eq_of_mul_eq_mul_right (by positivity : 0 < 2^m) eq
  simp [this]

private def width (d : ℕ) := 2^(d/2)
private def start (d : ℕ) := (2+d%2)*width d
private def scale (d : ℕ) := d+1-d/2

private lemma start_succ (d : ℕ) : start (d+1) = start d + width d := by
  unfold start width
  rcases Nat.mod_two_eq_zero_or_one d with h | h
  · rw [show (d+1)%2=1 by omega, show (d+1)/2=d/2 by omega,h]
    omega
  · rw [show (d+1)%2=0 by omega, show (d+1)/2=d/2+1 by omega,h,pow_succ]
    omega

private lemma start_mono : StrictMono start := strictMono_nat_of_lt_succ fun i => by
  rw [start_succ]
  exact Nat.lt_add_of_pos_right (by exact Nat.two_pow_pos _)

/-- The zero-based offset within the dyadic interval indexed by d. -/
private structure Block where
  d : ℕ
  i : ℕ
  bound : i < width d

private def Block.idx (b : Block) := start b.d + b.i - 2
private def Block.pre (b : Block) := width b.d + b.i
private def Block.val (b : Block) := b.pre * 2^(scale b.d)

private lemma start_two (d : ℕ) : 2 ≤ start d := start_mono.monotone (Nat.zero_le d)

private lemma idx_plus (b : Block) : b.idx+2=start b.d+b.i := by
  have := start_two b.d
  dsimp [Block.idx]; omega

private lemma idx_onto (i : ℕ) : ∃ b : Block, b.idx=i := by
  have h : ∃ d, i+2 < start (d+1) := ⟨i+2, by exact start_mono.id_le (i+2+1)⟩
  let d := Nat.find h
  have upper : i+2 < start (d+1) := Nat.find_spec h
  have lower : start d ≤ i+2 := by
    cases he : d with
    | zero => simp [start,width]
    | succ k =>
      have := Nat.find_min h (m := k) (by dsimp [d] at he; omega)
      omega
  let b : Block := ⟨d,i+2-start d,by rw [start_succ] at upper; omega⟩
  exact ⟨b,by dsimp [b,Block.idx]; omega⟩

private lemma ordered (a b : Block) (h : a.idx < b.idx) :
    a.d < b.d ∨ (a.d=b.d ∧ a.i < b.i) := by
  have ha := idx_plus a
  have hb := idx_plus b
  have hi := b.bound
  by_cases hd : b.d < a.d
  · have := start_mono.monotone (show b.d+1 ≤ a.d by omega)
    rw [start_succ] at this
    omega
  · by_cases he : a.d=b.d
    · rw [he] at ha; exact Or.inr ⟨he,by omega⟩
    · exact Or.inl (by omega)

private lemma idx_inj (a b : Block) (h : a.idx=b.idx) : a=b := by
  have hlt (x y : Block) (hd : x.d<y.d) : x.idx < y.idx := by
    have h1 := idx_plus x
    have h2 := idx_plus y
    have := start_mono.monotone (show x.d+1 ≤ y.d by omega)
    rw [start_succ] at this
    have := x.bound
    omega
  have hd : a.d = b.d := by
    rcases lt_trichotomy a.d b.d with hh | hh | hh
    · have := hlt a b hh; omega
    · exact hh
    · have := hlt b a hh; omega
  have ha := idx_plus a
  rw [hd] at ha
  have hb := idx_plus b
  have hi : a.i=b.i := by omega
  cases a; cases b; simp_all

private lemma enumerate {p : ℕ → Prop} (f : Block → ℕ)
    (mono : ∀ a b : Block, a.idx < b.idx → f a < f b)
    (range_f : ∀ z, p z ↔ ∃ b, f b = z) (b : Block) : Nat.nth p b.idx = f b := by
  let atIdx (i : ℕ) := Classical.choose (idx_onto i)
  have idxAt (i : ℕ) : (atIdx i).idx=i := Classical.choose_spec (idx_onto i)
  have atIdx_idx (c : Block) : atIdx c.idx=c := idx_inj _ _ (idxAt _)
  have m : StrictMono (fun i => f (atIdx i)) := fun i j hij => mono _ _ (by simpa only [idxAt] using hij)
  have inf : (Set.ofPred p).Infinite := by
    apply (Set.infinite_range_of_injective m.injective).mono
    rintro _ ⟨i,rfl⟩
    exact (range_f _).2 ⟨_,rfl⟩
  have e := Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn (p := p) (fun i => f (atIdx i))
    (by rintro z hz; obtain ⟨c,rfl⟩ := (range_f z).1 hz
        exact ⟨c.idx, fun hf => (inf hf).elim, congrArg f (atIdx_idx c)⟩)
    (fun i _ => (range_f _).2 ⟨_,rfl⟩) (m.strictMonoOn _)
  simpa [atIdx_idx] using (e (x := b.idx) (fun hf => (inf hf).elim)).symm

private lemma pow_two_mono {a b : ℕ} (h : a ≤ b) : 2^a ≤ (2:ℕ)^b :=
  Nat.pow_le_pow_right (by decide) h

private lemma pre_bounds (b : Block) :
    2^(b.d/2) ≤ b.pre ∧ b.pre < 2^(b.d/2+1) := by
  have := b.bound
  dsimp [Block.pre,width] at *
  rw [pow_succ]; omega

private lemma val_bounds (b : Block) :
    2^(b.d+1) ≤ b.val ∧ b.val < 2^(b.d+2) := by
  obtain ⟨h1,h2⟩ := pre_bounds b
  have lo := Nat.mul_le_mul_right (2^(scale b.d)) h1
  have hi := Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos (scale b.d))
  rw [←pow_add] at lo hi
  have h : b.d/2+scale b.d=b.d+1 := by dsimp [scale]; omega
  have H : b.d/2+1+scale b.d=b.d+2 := by omega
  exact ⟨h ▸ lo, H ▸ hi⟩

private lemma val_mono (a b : Block) (h : a.idx<b.idx) : a.val<b.val := by
  rcases ordered a b h with h | ⟨hd,hi⟩
  · exact (val_bounds a).2.trans_le ((pow_two_mono (by omega : a.d+2≤b.d+1)).trans (val_bounds b).1)
  · simp only [Block.val,Block.pre,hd]
    exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

/-- Moving the trailing zeros of the prefix to the exponent recovers the odd Proth factor. -/
private lemma factor_pre (b : Block) :
    ∃ k r, Odd k ∧ b.pre=k*2^r ∧ 0 < scale b.d+r ∧ k<2^(scale b.d+r) ∧
      b.val=k*2^(scale b.d+r) := by
  obtain ⟨lo,hi⟩ := pre_bounds b
  have hpos := Nat.two_pow_pos (b.d/2)
  obtain ⟨r,k,hk,h⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : b.pre ≠ 0)
  rw [Nat.mul_comm] at h
  have hle : k ≤ b.pre := by rw [h]; exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have hs : b.d/2+1≤ scale b.d+r := by unfold scale; omega
  refine ⟨k,r,hk,h,by omega,hle.trans_lt (hi.trans_le (pow_two_mono hs)),?_⟩
  simp only [Block.val,h,pow_add]; ring

private lemma block_of_params {k m : ℕ} (hk : Odd k) (hm : 0 < m) (hl : k<2^m) :
    ∃ b : Block, b.val=k*2^m := by
  have hk0 : k ≠ 0 := fun h => by simp [h] at hk
  let l := Nat.log2 k
  have ⟨lo,hi⟩ := (Nat.log2_eq_iff hk0).1 (show k.log2=l from rfl)
  have hlm : l < m := by
    by_contra! hn; have := pow_two_mono hn; omega
  let d := l+m-1
  let u := k*2^(d/2-l)
  have hd : l ≤ d/2 := by dsimp [d]; omega
  have ulo : width d ≤ u := by
    have h := Nat.mul_le_mul_right (2^(d/2-l)) lo
    rwa [←pow_add,show l+(d/2-l)=d/2 by omega] at h
  have uhi : u < 2*width d := by
    have h := Nat.mul_lt_mul_of_pos_right hi (Nat.two_pow_pos (d/2-l))
    rwa [←pow_add,show l+1+(d/2-l)=d/2+1 by omega,pow_succ,mul_comm _ 2] at h
  let b : Block := ⟨d,u-width d,by omega⟩
  have hp : b.pre=u := by dsimp [b,Block.pre]; omega
  refine ⟨b,?_⟩
  simp only [Block.val,hp, b, u, Nat.mul_assoc, ←pow_add]
  congr 2
  dsimp [scale,d]; omega

private lemma nth_proth (b : Block) : Nat.nth ProthTerm b.idx=b.val+1 := by
  refine enumerate (fun x => x.val+1) (fun x y h => by have := val_mono x y h; omega) ?_ b
  intro z
  constructor
  · rintro ⟨k,m,hk,hm,hl,rfl⟩
    obtain ⟨c,h⟩ := block_of_params hk hm hl
    exact ⟨c,by simp [h]⟩
  · rintro ⟨c,rfl⟩
    obtain ⟨k,r,hk,_,hm,hl,hv⟩ := factor_pre c
    exact ⟨k,_,hk,hm,hl,congrArg (·+1) hv⟩

private lemma nth_rep (b : Block) : Nat.nth (fun v => ∃ x y, Rep v x y) b.idx=4*b.val := by
  refine enumerate (fun x => 4*x.val) (fun x y h => by have := val_mono x y h; omega) ?_ b
  intro z
  constructor
  · rintro ⟨x,y,hr⟩
    obtain ⟨k,m,hk,hm,hl,rfl,_,_⟩ := params_of_rep hr
    obtain ⟨c,h⟩ := block_of_params hk hm hl
    exact ⟨c,by simp [h]⟩
  · rintro ⟨c,rfl⟩
    obtain ⟨k,r,hk,_,hm,hl,hv⟩ := factor_pre c
    rw [hv]; exact ⟨_,_,rep_params hk hm hl⟩

private def half (d : ℕ) := (d+1)/2
private def Block.word (b : Block) := Nat.digits 2 b.pre
private def Block.low (b : Block) := if b.d%2=0 then b.word.tail.reverse else b.word.reverse
private def Block.pal (b : Block) := Nat.ofDigits 2 (b.low++b.word)

private lemma word_len (b : Block) : b.word.length=b.d/2+1 := by
  have ⟨h1,h2⟩ := pre_bounds b
  have := (Nat.digits_length_le_iff (by decide : 1<2) _).2 h2
  have := (Nat.lt_digits_length_iff (by decide : 1<2) _).2 h1
  dsimp [Block.word]; omega

private lemma word_ne (b : Block) : b.word ≠ [] := by
  have := word_len b; rintro hh; rw [hh] at this; simp at this

private lemma low_len (b : Block) : b.low.length=half b.d := by
  dsimp [Block.low,half]
  split <;> simp [word_len] <;> omega

private lemma pal_dig (b : Block) : Nat.digits 2 b.pal=b.low++b.word := by
  apply Nat.digits_ofDigits _ (by decide)
  · intro u hu
    apply Nat.digits_lt_base (by decide : 1<2) (m := b.pre)
    rcases List.mem_append.1 hu with h | h
    · unfold Block.low at h
      split at h <;> simp only [List.mem_reverse] at h
      · exact List.mem_of_mem_tail h
      · exact h
    · exact h
  · intro _
    rw [List.getLast_append_of_ne_nil _ (word_ne b)]
    apply Nat.getLast_digit_ne_zero
    have := (pre_bounds b).1
    have := Nat.two_pow_pos (b.d/2)
    omega

private lemma pal_len (b : Block) : (Nat.digits 2 b.pal).length=b.d+1 := by
  rw [pal_dig,List.length_append,word_len,low_len]
  dsimp [half]; omega

private lemma pal_ok (b : Block) : 0<b.pal ∧ (Nat.digits 2 b.pal).reverse=Nat.digits 2 b.pal := by
  refine ⟨?_,?_⟩
  · have := pal_len b
    by_contra! h
    simp [show b.pal=0 by omega] at this
  · rw [pal_dig]
    unfold Block.low
    split
    · have H := word_ne b
      cases he : b.word with
      | nil => contradiction
      | cons x xs => simp [List.append_assoc]
    · simp

private lemma pal_div (b : Block) : b.pal/2^(half b.d)=b.pre := by
  rw [Nat.self_div_pow_eq_ofDigits_drop _ _ (by decide : 2 ≤ 2)]
  rw [pal_dig,← low_len]
  simp [Block.word,Nat.ofDigits_digits]

private lemma pal_mono (a b : Block) (h : a.idx<b.idx) : a.pal<b.pal := by
  rcases ordered a b h with hd | ⟨hd,hi⟩
  · by_contra! hn
    have := Nat.le_length_digits_le 2 _ _ hn
    rw [pal_len,pal_len] at this
    omega
  · by_contra! hn
    have := Nat.div_le_div_right (c := 2^(half b.d)) hn
    rw [pal_div,←hd,pal_div] at this
    simp only [Block.pre,hd] at this
    omega

/-- A palindrome is determined by its length and its high half, including the middle digit. -/
private lemma eq_pal_of_upper {z y d : ℕ} (hz : (Nat.digits 2 z).reverse=Nat.digits 2 z)
    (hy : (Nat.digits 2 y).reverse=Nat.digits 2 y)
    (lz : (Nat.digits 2 z).length=d+1) (ly : (Nat.digits 2 y).length=d+1)
    (hq : z/2^(half d)=y/2^(half d)) : z=y := by
  rw [Nat.self_div_pow_eq_ofDigits_drop _ _ (by decide : 2≤2),
      Nat.self_div_pow_eq_ofDigits_drop _ _ (by decide : 2≤2)] at hq
  have hd (n : ℕ) (h : (Nat.digits 2 n).length=d+1) :
      ((Nat.digits 2 n).drop (half d)).length = d+1-half d ∧
      ∀ x ∈ (Nat.digits 2 n).drop (half d), x<2 := by
    refine ⟨by simp [h], fun x hx => Nat.digits_lt_base (by decide)
      (List.mem_of_mem_drop hx : x ∈ Nat.digits 2 n)⟩
  have tailEq := (Nat.bijOn_ofDigits (by decide : 1<2) (d+1-half d)).injOn (hd _ lz) (hd _ ly) hq
  have big : half d+(d+1-2*half d)=d+1-half d := by unfold half; omega
  have mid := congrArg (List.drop (d+1-2*half d)) tailEq
  simp only [List.drop_drop,big] at mid
  have front := congrArg List.reverse mid
  rw [←lz,List.take_reverse (xs := Nat.digits 2 z) (i := half d) |>.symm,hz] at front
  rw [lz,←ly,List.take_reverse (xs := Nat.digits 2 y) (i := half d) |>.symm,hy] at front
  exact (Nat.digits.injective 2) <| by
    calc
      _ = _ := (List.take_append_drop (half d) (Nat.digits 2 z)).symm
      _ = _ := congrArg₂ List.append front tailEq
      _ = _ := List.take_append_drop _ _

private lemma nth_pal (b : Block) :
    Nat.nth (fun z => 0<z ∧ (Nat.digits 2 z).reverse=Nat.digits 2 z) b.idx=b.pal := by
  refine enumerate Block.pal pal_mono ?_ b
  intro z
  constructor
  · rintro ⟨hz,hs⟩
    let d := Nat.log2 z
    let u := z/2^(half d)
    have ⟨zl,zh⟩ := (Nat.log2_eq_iff (by omega : z≠0)).1 (show z.log2=d from rfl)
    have lz : (Nat.digits 2 z).length=d+1 := by
      rw [Nat.length_digits _ _ (by decide) (by omega),←Nat.log2_eq_log_two]
    have hl : width d ≤ u := by
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).2
      simpa [width,←pow_add, show d/2+half d=d by unfold half; omega] using zl
    have hu : u < 2*width d := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      rwa [width, ← pow_succ',←pow_add,show d/2+1+half d=d+1 by unfold half; omega]
    let c : Block := ⟨d,u-width d,by omega⟩
    have hp : c.pre=u := by dsimp [c,Block.pre]; omega
    refine ⟨c,eq_pal_of_upper (d := d) (pal_ok c).2 hs (pal_len c) lz ?_⟩
    exact (pal_div c).trans hp
  · rintro ⟨c,rfl⟩; exact pal_ok c

private structure Pair where
  k : ℕ
  m : ℕ
  odd : Odd k
  posm : 0 < m
  lt : k<2^m

private def Pair.prod (x : Pair) := x.k*2^x.m
private def Pair.pos (x : Pair) := (2^x.m+x.k)/2
private noncomputable def Pair.block (x : Pair) := Classical.choose (block_of_params x.odd x.posm x.lt)
private noncomputable def Pair.rank (x : Pair) := x.block.idx+1

private lemma prod_block (x : Pair) : x.block.val = x.prod :=
  Classical.choose_spec (block_of_params x.odd x.posm x.lt)

private lemma prod_inj {x y : Pair} (he : x.prod=y.prod) : x=y := by
  have e := congrArg tr he
  simp only [Pair.prod,tr_prod x.odd,tr_prod y.odd] at e
  have h := he; unfold Pair.prod at h; rw [e] at h
  have k := Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h
  cases x; cases y; simp_all

private lemma rank_lt {x y : Pair} : x.rank<y.rank ↔ x.prod<y.prod := by
  simp only [Pair.rank,Nat.add_lt_add_iff_right,← prod_block]
  constructor
  · exact val_mono _ _
  · intro h
    rcases lt_trichotomy x.block.idx y.block.idx with h' | h' | h'
    · exact h'
    · rw [idx_inj _ _ h'] at h; omega
    · have := val_mono _ _ h'; omega

private lemma rank_inj {x y : Pair} (h : x.rank=y.rank) : x=y := by
  exact prod_inj (by rcases lt_trichotomy x.prod y.prod with hl | he | hl
                     · have := rank_lt.2 hl; omega
                     · exact he
                     · have := rank_lt.2 hl; omega)

private lemma pair_for_block (b : Block) : ∃ x : Pair, x.block=b := by
  obtain ⟨k,r,hk,_,hm,hl,hv⟩ := factor_pre b
  let x : Pair := ⟨k,_,hk,hm,hl⟩
  have he : x.block.val=b.val := (prod_block x).trans hv.symm
  refine ⟨x,idx_inj _ _ ?_⟩
  rcases lt_trichotomy x.block.idx b.idx with h | h | h
  · have := val_mono _ _ h; omega
  · exact h
  · have := val_mono _ _ h; omega

private lemma rank_onto {n : ℕ} (hn : 0<n) : ∃ x : Pair, x.rank=n := by
  obtain ⟨b,hb⟩ := idx_onto (n-1)
  obtain ⟨x,hx⟩ := pair_for_block b
  refine ⟨x,?_⟩; unfold Pair.rank; rw [hx,hb]; omega

private lemma pos_info (x : Pair) :
    x.pos=2^(x.m-1)+x.k/2 ∧ 2^(x.m-1) ≤ x.pos ∧ x.pos<2^x.m ∧
    2*x.pos+1=2^x.m+x.k := by
  have hm := x.posm
  have hp : 2^x.m=2^(x.m-1)*2 := by conv_lhs => rw [show x.m=x.m-1+1 by omega,pow_succ]
  obtain ⟨j,hj⟩ := x.odd
  have := x.lt
  simp only [Pair.pos,hp] at *
  omega

private lemma pos_log (x : Pair) : Nat.log2 x.pos=x.m-1 := by
  obtain ⟨_,h1,h2,_⟩ := pos_info x
  have := Nat.two_pow_pos (x.m-1)
  apply (Nat.log2_eq_iff (by omega)).2
  exact ⟨h1,by rwa [show x.m-1+1=x.m by have := x.posm; omega]⟩

private lemma pos_inj {x y : Pair} (h : x.pos=y.pos) : x=y := by
  have he := congrArg Nat.log2 h
  rw [pos_log,pos_log] at he
  have hm : x.m=y.m := by have := x.posm; have := y.posm; omega
  have h1 := (pos_info x).2.2.2
  have h2 := (pos_info y).2.2.2
  rw [hm] at h1
  have hk : x.k=y.k := by omega
  cases x; cases y; simp_all

private lemma pos_onto {j : ℕ} (hj : 0<j) : ∃ x : Pair, x.pos=j := by
  let s := j.log2
  have ⟨hl,hh⟩ := (Nat.log2_eq_iff (by omega : j≠0)).1 (show j.log2=s from rfl)
  let k := 2*(j-2^s)+1
  have hk : Odd k := ⟨j-2^s,rfl⟩
  have hs : k<2^(s+1) := by rw [pow_succ] at *; unfold k; omega
  refine ⟨⟨k,s+1,hk,by omega,hs⟩,?_⟩
  dsimp [Pair.pos,k]
  rw [pow_succ]; omega

private lemma prod_compare (x y : Pair) (hpos : x.pos ≤ y.pos) (hlt : y.prod<x.prod) :
    x.m < y.m := by
  have h1 := (pos_info x).2.1
  have h2 := (pos_info y).2.2.1
  have hm : x.m ≤ y.m := by
    by_contra! h
    have := pow_two_mono (by omega : y.m≤x.m-1)
    omega
  by_contra! h
  have he : y.m=x.m := by omega
  unfold Pair.prod at hlt
  rw [he] at hlt
  have hk : y.k < x.k := Nat.lt_of_mul_lt_mul_right hlt
  have p1 := (pos_info x).2.2.2
  have p2 := (pos_info y).2.2.2
  rw [he] at p2
  omega

private lemma small_prod {x y : Pair} (hp : x.pos≤y.pos) (hv : y.prod<x.prod) :
    ∃ t, t ∈ Finset.Icc 1 (x.k/2) ∧ y.prod=t*2^(x.m+1) := by
  have hm := prod_compare x y hp hv
  let t := y.k*2^(y.m-(x.m+1))
  have h : y.prod=t*2^(x.m+1) := by
    unfold Pair.prod t
    rw [mul_assoc,←pow_add,show y.m-(x.m+1)+(x.m+1)=y.m by omega]
  rw [h,Pair.prod,pow_succ] at hv
  have hl : 2*t < x.k := Nat.lt_of_mul_lt_mul_right (by nlinarith only [hv] : (2*t)*2^x.m<x.k*2^x.m)
  have hk : 0<y.k := by obtain ⟨a,ha⟩ := y.odd; omega
  refine ⟨t,Finset.mem_Icc.2 ⟨?_,by omega⟩,h⟩
  exact Nat.mul_pos hk (Nat.two_pow_pos _)

private lemma pair_small (x : Pair) {t : ℕ} (ht : t ∈ Finset.Icc 1 (x.k/2)) :
    ∃ y : Pair, x.pos ≤ y.pos ∧ y.prod < x.prod ∧ y.prod=t*2^(x.m+1) := by
  obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.1 ht
  obtain ⟨r,k,hk,h⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : t≠0)
  let m := x.m+1+r
  have hk' : k ≤ t := by rw [h]; exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos r)
  have hl : k<2^m := lt_of_le_of_lt (by omega : k≤x.k) (x.lt.trans_le (pow_two_mono (by dsimp [m]; omega)))
  let y : Pair := ⟨k,m,hk,by dsimp [m]; omega,hl⟩
  have hv : y.prod=t*2^(x.m+1) := by
    dsimp [y,Pair.prod,m]; rw [pow_add,h]; ring
  have hk₂ : 2*t < x.k := by obtain ⟨v,hv⟩ := x.odd; omega
  refine ⟨y,?_,?_,hv⟩
  · have hm : x.m≤y.m-1 := by dsimp [y,m]; omega
    exact (pos_info x).2.2.1.le.trans ((pow_two_mono hm).trans (pos_info y).2.1)
  · rw [hv,Pair.prod,pow_succ]
    calc
      _ = (2*t)*2^x.m := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_right hk₂ (Nat.two_pow_pos _)

/-- Counting unused lower ranks gives the greedy index. -/
private lemma choose_rank (x : Pair) (past : List ℕ)
    (ih : ∀ y : Pair, y.rank ∈ past ↔ y.pos<x.pos) :
    Nat.nth (fun n => 0<n ∧ n ∉ past) (x.k/2) = x.rank := by
  classical
  let p (n : ℕ) := 0<n ∧ n ∉ past
  have hx : p x.rank := ⟨by simp [Pair.rank], fun h => (lt_irrefl _) ((ih x).1 h)⟩
  suffices H : Nat.count p x.rank = x.k/2 by rw [←H]; exact Nat.nth_count hx
  rw [Nat.count_eq_card_filter_range]
  let S := Finset.Icc 1 (x.k/2)
  let y (t : ℕ) (ht : t ∈ S) : Pair := Classical.choose (pair_small x ht)
  have spec (t : ℕ) (ht : t ∈ S) : x.pos ≤ (y t ht).pos ∧
      (y t ht).prod<x.prod ∧ (y t ht).prod=t*2^(x.m+1) := Classical.choose_spec (pair_small x ht)
  have card := Finset.card_bij (s := S) (t := (Finset.range x.rank).filter p)
    (fun i hi => (y i hi).rank)
    (by intro i hi; obtain ⟨hp,hv,_⟩ := spec i hi
        exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (rank_lt.2 hv),
          by exact ⟨Nat.zero_lt_succ _, fun h => (by have := (ih _).1 h; omega)⟩⟩)
    (by intro i hi j hj he
        have hh := congrArg Pair.prod (rank_inj he)
        rw [(spec i hi).2.2,(spec j hj).2.2] at hh
        exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) hh)
    (by intro n hn
        obtain ⟨hl,hn₁,hn₂⟩ := Finset.mem_filter.1 hn
        obtain ⟨z,rfl⟩ := rank_onto hn₁
        have hpos : x.pos ≤ z.pos := by simpa only [ih,not_lt] using hn₂
        obtain ⟨t,ht,he⟩ := small_prod hpos (rank_lt.1 (Finset.mem_range.1 hl))
        exact ⟨t,ht,congrArg Pair.rank (prod_inj ((spec t ht).2.2.trans he.symm))⟩)
  simpa [S] using card.symm

private lemma hist_mem (j : ℕ) : ∀ y : Pair, y.rank ∈ history j ↔ y.pos≤j := by
  induction j with
  | zero =>
    intro y
    have := (pos_info y).2.1
    have := Nat.two_pow_pos (y.m-1)
    simp [history]; omega
  | succ j ih =>
    obtain ⟨x,hx⟩ := pos_onto (j := j+1) (by omega)
    have H := choose_rank x (history j) (fun y => (ih y).trans (by omega))
    have h := (pos_info x).1
    have hidx : j+1-2^(j+1).log2=x.k/2 := by rw [←hx,pos_log]; omega
    intro y
    simp only [history,hidx,H,List.mem_cons,ih]
    constructor
    · rintro (he | he)
      · rw [rank_inj he,hx]
      · omega
    · intro hy
      by_cases he : y.pos=x.pos
      · exact Or.inl (congrArg Pair.rank (pos_inj he))
      · exact Or.inr (by omega)

private lemma perm_pos (x : Pair) : perm x.pos=x.rank := by
  have h := (pos_info x).1
  have hpos : 0<x.pos := by have := Nat.two_pow_pos (x.m-1); omega
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x.pos≠0)
  change x.pos=j+1 at hj
  have H := choose_rank x (history j) (fun y => (hist_mem j y).trans (by omega))
  have hi : j+1-2^(j+1).log2=x.k/2 := by rw [←hj,pos_log]; omega
  simp only [perm,hj,history,hi,H,List.headD_cons]

private lemma idx_log (b : Block) : (b.idx+2).log2=b.d/2+1 := by
  have H := idx_plus b
  have hi := b.bound
  have ht := Nat.two_pow_pos (b.d/2)
  apply (Nat.log2_eq_iff (by omega)).2
  dsimp [start,width] at *
  rw [pow_succ (n := b.d/2),pow_succ]
  rcases Nat.mod_two_eq_zero_or_one b.d with he | he <;> rw [he] at H <;> omega

private lemma idx_mod (b : Block) : (b.idx+2)%width b.d=b.i := by
  rw [idx_plus,start,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt b.bound]

private lemma idx_flag (b : Block) :
    (if 3 * width b.d ≤ b.idx+2 then 1 else 0) = b.d%2 := by
  have H := idx_plus b
  have hi := b.bound
  dsimp [start] at H
  rcases Nat.mod_two_eq_zero_or_one b.d with he | he <;> rw [he] at H ⊢ <;> split <;> omega

private lemma idx_qlog (b : Block) : (2*(b.idx+2)/3).log2=b.d/2+b.d%2 := by
  have H := idx_plus b
  have hi := b.bound
  have ht := Nat.two_pow_pos (b.d/2)
  dsimp [start,width] at *
  apply (Nat.log2_eq_iff (by omega)).2
  rcases Nat.mod_two_eq_zero_or_one b.d with he | he <;> rw [he] at H ⊢ <;>
    simp only [Nat.add_zero,pow_succ] <;> omega

end ProthEnumeration

open ProthEnumeration

theorem OMA.solution : type_of% @OMA.S_mo_466152.main := by
  intro n hn
  obtain ⟨b,hb⟩ := idx_onto (n-1)
  have hN : n=b.idx+1 := by omega
  subst n
  obtain ⟨k,r,hk,hpre,hm,hl,hval⟩ := factor_pre b
  let x : Pair := ⟨k,scale b.d+r,hk,hm,hl⟩
  have hp : proth (b.idx+1)-1 = b.val := by
    simp [proth,nth_proth]
  have h₂ : b₂ (b.idx+1)=scale b.d+r := by rw [b₂,hp,hval,tr_prod hk]
  have h₁ : b₁ (b.idx+1)=k := by
    rw [b₁,hp,h₂,hval,Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  have ha : a (b.idx+1)=4*b.val := by simp [a,nth_rep]
  have hc : c (b.idx+1)=b.pre := by
    simpa [c,nth_pal,pal_len,half] using pal_div b
  have hr : Rep (4*b.val) (2^(scale b.d+r)+k) (2^(scale b.d+r)-k) := by
    rw [hval]; exact rep_params hk hm hl
  have hbx : x.block=b := by
    have H : x.block.val=b.val := (prod_block x).trans hval.symm
    apply idx_inj
    rcases lt_trichotomy x.block.idx b.idx with h | h | h
    · have := val_mono _ _ h; omega
    · exact h
    · have := val_mono _ _ h; omega
  have pm : perm ((2^(scale b.d+r)+k)/2)=b.idx+1 := by
    simpa only [Pair.pos,Pair.rank,hbx,x] using perm_pos x
  dsimp only
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  simp only [show b.idx+1+1=b.idx+2 by omega, idx_log,Nat.add_sub_cancel,
    show 2^(b.d / 2)=width b.d from rfl,idx_mod,idx_flag,h₁,h₂,hc,ha]
  refine ⟨rfl,?_,?_,?_,hr,?_,pm⟩
  · rw [hpre,tr_prod hk,Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rw [hpre,tr_prod hk]; dsimp [scale]; omega
  · rw [idx_qlog,Block.val]
    have he : b.d/2+b.d%2+3 = scale b.d+2 := by dsimp [scale]; omega
    rw [he,pow_add]; ring
  · intro X Y h
    obtain ⟨rfl,rfl⟩ := rep_unique hr h
    exact ⟨le_rfl,le_rfl⟩
