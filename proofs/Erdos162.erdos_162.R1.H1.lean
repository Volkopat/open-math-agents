import OMAReductions.R_Erdos162_erdos_162_R1

/-! A two-colour Ramsey bound and an exponential-moment estimate for random edge colours. -/
open Finset Filter Erdos162
open scoped Topology
namespace BalancedRamsey

private def mono {n : ℕ} (c : Sym2 (Fin n) → Bool) (b : Bool) (H : Finset (Fin n)) :=
  ∀ x ∈ H, ∀ y ∈ H, x ≠ y → c s(x,y) = b

private theorem extend_mono {n : ℕ} {c : Sym2 (Fin n) → Bool} {b : Bool}
    {v : Fin n} {H : Finset (Fin n)} (hm : mono c b H)
    (h : ∀ y ∈ H, c s(v,y) = b) : mono c b (insert v H) := by
  intro x hx y hy hne
  rcases mem_insert.mp hx with hx' | hx'
  · subst x
    rcases mem_insert.mp hy with he | hy'
    · exact (hne he.symm).elim
    · exact h _ hy'
  · rcases mem_insert.mp hy with he | hy'
    · subst y; rw [Sym2.eq_swap]; exact h _ hx'
    · exact hm _ hx' _ hy' hne

private theorem ramsey {n : ℕ} (c : Sym2 (Fin n) → Bool) (a b : ℕ)
    (V : Finset (Fin n)) (hsize : 2^(a+b) ≤ V.card) :
    (∃ H ⊆ V, H.card=a ∧ mono c false H) ∨ (∃ H ⊆ V, H.card=b ∧ mono c true H) := by
  classical
  cases a with
  | zero => exact Or.inl ⟨∅, empty_subset _, rfl, by simp [mono]⟩
  | succ a =>
    cases b with
    | zero => exact Or.inr ⟨∅, empty_subset _, rfl, by simp [mono]⟩
    | succ b =>
      obtain ⟨v,hv⟩ := card_pos.mp (lt_of_lt_of_le (by positivity) hsize)
      let W := V.erase v
      let P := W.filter (fun y => c s(v,y)=false)
      let Q := W.filter (fun y => ¬ c s(v,y)=false)
      have hsum : P.card + Q.card = V.card-1 := by
        rw [← card_erase_of_mem hv]
        exact card_filter_add_card_filter_not _
      have hpow : 2^((a+1)+(b+1)) = 2*2^(a+b+1) := by
        rw [show (a+1)+(b+1) = (a+b+1)+1 by omega, pow_succ, mul_comm]
      have hP : P ⊆ V := (filter_subset _ _).trans (erase_subset _ _)
      have hQ : Q ⊆ V := (filter_subset _ _).trans (erase_subset _ _)
      by_cases hh : 2^(a+b+1) ≤ P.card
      · rcases ramsey c a (b+1) P (by simpa [Nat.add_assoc] using hh) with
          ⟨H,hH,hc,hm⟩ | ⟨H,hH,hc,hm⟩
        · apply Or.inl
          have hvH : v ∉ H := fun h => notMem_erase _ _ ((mem_filter.mp (hH h)).1)
          exact ⟨insert v H, insert_subset hv (hH.trans hP), by simp [hvH,hc],
            extend_mono hm (fun y hy => (mem_filter.mp (hH hy)).2)⟩
        · exact Or.inr ⟨H,hH.trans hP,hc,hm⟩
      · have hh' : 2^(a+b+1) ≤ Q.card := by rw [hpow] at hsize; omega
        rcases ramsey c (a+1) b Q (by simpa [Nat.add_right_comm] using hh') with
          ⟨H,hH,hc,hm⟩ | ⟨H,hH,hc,hm⟩
        · exact Or.inl ⟨H,hH.trans hQ,hc,hm⟩
        · apply Or.inr
          have hvH : v ∉ H := fun h => notMem_erase _ _ ((mem_filter.mp (hH h)).1)
          exact ⟨insert v H, insert_subset hv (hH.trans hQ), by simp [hvH,hc],
            extend_mono hm (fun y hy => Bool.eq_true_of_not_eq_false (mem_filter.mp (hH hy)).2)⟩
termination_by a+b

private theorem lower (n : ℕ) (α : ℝ) (hα : 0 ≤ α) (hn : 0 < n) :
    Real.log n / Real.log 4 < F n α := by
  classical
  let k := F n α
  have hne : {j : ℕ | ∃ c, IsBalancedAbove n α c j}.Nonempty :=
    ⟨n+1, fun _ => true, isBalancedAbove_succ n α _⟩
  obtain ⟨c,hc⟩ := Nat.sInf_mem hne
  change IsBalancedAbove n α c k at hc
  have hlt : n < 4^k := by
    by_contra! hp
    have h2 : 2^(k+k) = 4^k := by rw [← two_mul, pow_mul]; norm_num
    have hR := ramsey c k k univ (by simpa [h2] using hp)
    have absurdMono (H : Finset (Fin n)) (b : Bool) (hH : H.card=k)
        (hmono : mono c b H) : False := by
      have hzero : colourEdgeCount c H (!b) = 0 := by
        rw [colourEdgeCount, card_eq_zero, filter_eq_empty_iff]
        intro e
        induction e using Sym2.inductionOn with | _ x y =>
          intro he hd
          obtain ⟨hx,hy⟩ := mk_mem_sym2_iff.mp he
          have hxy := hmono x hx y hy (by simpa using hd.1)
          cases b <;> simp_all
      have hpos := hc H (by omega) (!b)
      rw [hzero, Nat.cast_zero] at hpos
      exact (not_lt_of_ge (mul_nonneg hα (Nat.cast_nonneg _))) hpos
    rcases hR with ⟨H,_,hs,h⟩ | ⟨H,_,hs,h⟩
    · exact absurdMono H false hs h
    · exact absurdMono H true hs h
  have hx : (n : ℝ) < (4:ℝ)^k := by exact_mod_cast hlt
  have hl := Real.log_lt_log (by exact_mod_cast hn) hx
  rw [Real.log_pow] at hl
  exact (div_lt_iff₀ (Real.log_pos (by norm_num))).mpr hl



private theorem tilted (α : ℝ) (hα : α < 1/2) :
    ∃ t : ℝ, 0 < t ∧ (Real.exp ((α-1)*t) + Real.exp (α*t))/2 < 1 := by
  let f (x : ℝ) := (Real.exp ((α-1)*x) + Real.exp (α*x))/2
  have ha := ((hasDerivAt_id (0:ℝ)).const_mul (α-1)).exp
  have hb := ((hasDerivAt_id (0:ℝ)).const_mul α).exp
  have hd : HasDerivAt f (α-1/2) 0 := by
    have hval : α-1/2 = (Real.exp ((α-1)*id 0)*((α-1)*1) + Real.exp (α*id 0)*(α*1))/2 := by
      norm_num; ring
    rw [hval]
    exact (ha.add hb).div_const 2
  have he := hd.tendsto_slope_zero_right.eventually_lt_const (show α-1/2 < 0 by linarith)
  have hgt : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, h⟩ := (hgt.and he).exists
  change 0 < t at ht
  have hf : f 0 = 1 := by norm_num [f]
  simp only [zero_add, hf, smul_eq_mul] at h
  have hn := neg_of_mul_neg_right h (inv_pos.mpr ht).le
  exact ⟨t,ht,sub_neg.mp hn⟩

private def edges {n : ℕ} (H : Finset (Fin n)) := H.sym2.filter fun e => ¬ e.IsDiag

private theorem edge_card {n : ℕ} (H : Finset (Fin n)) :
    (edges H).card = H.card.choose 2 := by
  rw [edges, sym2_eq_image, Sym2.filter_image_mk_not_isDiag, Sym2.card_image_offDiag]

private def cost {V : Type*} [DecidableEq V] (E X : Finset V) (u v : ℝ) : ℝ :=
  u^(E∩X).card * v^(E\X).card

private theorem mean_cost {V : Type*} [DecidableEq V] [Fintype V] (E : Finset V) (u v : ℝ) :
    (∑ X ∈ (univ : Finset V).powerset, cost E X u v) =
      2^(Fintype.card V) * ((u+v)/2)^E.card := by
  classical
  let f (e : V) := if e ∈ E then u else 1
  let g (e : V) := if e ∈ E then v else 1
  have hprod (X : Finset V) (a : ℝ) :
      (∏ e ∈ X, if e∈E then a else 1) = a^(E∩X).card := by
    rw [prod_ite, filter_mem_eq_inter, inter_comm]
    simp
  have hcompl (X : Finset V) : E ∩ (univ\X) = E\X := by ext; simp
  calc
    _ = ∑ X ∈ (univ : Finset V).powerset, (∏ e ∈ X, f e)*(∏ e ∈ univ\X, g e) := by
      apply sum_congr rfl
      intro X _
      rw [show (∏ e ∈ X, f e)=_ from hprod X u,
          show (∏ e ∈ univ\X, g e)=_ from hprod _ v, hcompl]
      rfl
    _ = ∏ e : V, (f e + g e) := (prod_add f g univ).symm
    _ = ∏ e : V, (if e∈E then (u+v) else 2) := by
      apply prod_congr rfl
      intro e _
      by_cases h : e∈E <;> norm_num [f,g,h]
    _ = _ := by
      rw [prod_ite]
      have hh : (univ.filter fun e : V => e∉E) = univ\E := by ext; simp
      simp only [filter_mem_eq_inter, univ_inter, prod_const, hh, card_sdiff_of_subset
        (subset_univ E), card_univ, div_pow]
      have he := E.card_le_univ
      have hx : 2^Fintype.card V = (2:ℝ)^(Fintype.card V-E.card)*2^E.card := by
        rw [← pow_add, Nat.sub_add_cancel he]
      rw [hx]
      field_simp



private theorem cutoff {r : ℝ} (hr : 0 < r) (hr' : r < 1) {n h : ℕ} (hn : 4 ≤ n)
    (hh : 4 * Real.log n / (-Real.log r) + 1 ≤ (h:ℝ)) :
    r^(h.choose 2) ≤ (1/(4*(n:ℝ)))^h := by
  have hn4 : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn' : (0:ℝ) < n := by linarith
  have hneg := Real.log_neg hr hr'
  have hln := Real.log_le_log (by norm_num : (0:ℝ)<4) hn4
  have he : 4 * Real.log n ≤ ((h:ℝ)-1) * (-Real.log r) :=
    (div_le_iff₀ (neg_pos.mpr hneg)).mp (by linarith)
  apply (Real.log_le_log_iff (pow_pos hr _) (pow_pos (by positivity) _)).mp
  rw [Real.log_pow, Real.log_pow, Nat.cast_choose_two, Real.log_div (by norm_num) (by positivity),
    Real.log_one, Real.log_mul (by norm_num) hn'.ne']
  nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) h) (sub_nonneg.mpr he),
    mul_nonneg (Nat.cast_nonneg (α:=ℝ) h) (sub_nonneg.mpr hln)]

private theorem total_penalty {n k : ℕ} (hn : 4 ≤ n) (hk : 0 < k) {r : ℝ}
    (hb : ∀ h : ℕ, k ≤ h → r^(h.choose 2) ≤ (1/(4*(n:ℝ)))^h) :
    2 * (∑ H ∈ ((univ : Finset (Fin n)).powerset.filter fun H => k ≤ H.card),
      r^(H.card.choose 2)) < 1 := by
  classical
  let x : ℝ := 1/(4*(n:ℝ))
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hx : 0 < x := by dsimp [x]; positivity
  let S := (univ : Finset (Fin n)).powerset
  have hs : S.filter (fun H => k ≤ H.card) ⊆ S.erase ∅ := by
    intro H hH
    obtain ⟨hS, hcard⟩ := mem_filter.mp hH
    exact mem_erase.mpr ⟨by rintro rfl; simp at hcard; omega,hS⟩
  have ha : (∑ H ∈ S.filter (fun H => k ≤ H.card), r^(H.card.choose 2)) ≤
      ∑ H ∈ S.erase ∅, x^H.card := by
    apply le_trans (sum_le_sum fun H hH => hb _ (mem_filter.mp hH).2)
    exact sum_le_sum_of_subset_of_nonneg hs fun H _ _ => (pow_pos hx _).le
  have hsum : (∑ H ∈ S, x^H.card) = (x+1)^n := by
    simpa [S] using sum_pow_mul_eq_add_pow x (1:ℝ) (univ : Finset (Fin n))
  have hem : (∅ : Finset (Fin n)) ∈ S := by simp [S]
  have hm := sum_erase_add S (fun H : Finset (Fin n) => x^H.card) hem
  rw [hsum] at hm
  simp only [card_empty, pow_zero] at hm
  have h1 := Real.add_one_le_exp x
  have hpow : (x+1)^n ≤ Real.exp (1/4) := by
    calc
      _ ≤ (Real.exp x)^n := pow_le_pow_left₀ (by positivity) h1 _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; dsimp [x]; field_simp
  have h2 := Real.exp_bound_div_one_sub_of_interval (by norm_num : 0 ≤ (1:ℝ)/4)
    (by norm_num : (1:ℝ)/4 < 1)
  change 2 * (∑ H ∈ S.filter (fun H => k ≤ H.card), r^(H.card.choose 2)) < 1
  linarith


private theorem exp_penalty (a t : ℝ) (ht : 0 < t) (i j : ℕ)
    (h : (i:ℝ) ≤ a*(i+j)) :
    1 ≤ Real.exp ((a-1)*t)^i * Real.exp (a*t)^j := by
  rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, Real.one_le_exp_iff]
  nlinarith [mul_nonneg ht.le (sub_nonneg.mpr h)]

private theorem penalty_small {n : ℕ} (a t : ℝ) (ht : 0 < t)
    (H : Finset (Fin n)) (X : Finset (Sym2 (Fin n)))
    (hh : cost (edges H) X (Real.exp ((a-1)*t)) (Real.exp (a*t)) +
      cost (edges H) X (Real.exp (a*t)) (Real.exp ((a-1)*t)) < 1) :
    ∀ b, a*(H.card.choose 2 : ℝ) < colourEdgeCount (fun e => decide (e∈X)) H b := by
  classical
  let E := edges H
  have he : (H.card.choose 2 : ℝ) = ((E∩X).card:ℝ)+(E\X).card := by
    exact_mod_cast ((card_inter_add_card_sdiff E X).trans (edge_card H)).symm
  have htrue : colourEdgeCount (fun e => decide (e∈X)) H true = (E∩X).card := by
    apply congrArg card
    ext e
    simp [E, edges, and_assoc]
  have hfalse : colourEdgeCount (fun e => decide (e∈X)) H false = (E\X).card := by
    apply congrArg card
    ext e
    simp [E, edges, and_assoc]
  change Real.exp _^(E∩X).card * Real.exp _^(E\X).card +
    Real.exp _^(E∩X).card * Real.exp _^(E\X).card < 1 at hh
  intro b
  cases b
  · rw [hfalse,he]
    by_contra! h
    rw [add_comm] at h
    have h' := exp_penalty a t ht (E\X).card (E∩X).card h
    linarith [show 0 ≤ Real.exp ((a-1)*t)^(E∩X).card * Real.exp (a*t)^(E\X).card by positivity,
      mul_comm (Real.exp ((a-1)*t)^(E\X).card) (Real.exp (a*t)^(E∩X).card)]
  · rw [htrue,he]
    by_contra! h
    have h' := exp_penalty a t ht (E∩X).card (E\X).card h
    linarith [show 0 ≤ Real.exp (a*t)^(E∩X).card * Real.exp ((a-1)*t)^(E\X).card by positivity]

private theorem select {n k : ℕ} (a t : ℝ) (ht : 0 < t)
    (hh : 2 * (∑ H ∈ ((univ : Finset (Fin n)).powerset.filter fun H => k ≤ H.card),
      ((Real.exp ((a-1)*t) + Real.exp (a*t))/2)^(H.card.choose 2)) < 1) :
    F n a ≤ k := by
  classical
  let u := Real.exp ((a-1)*t)
  let v := Real.exp (a*t)
  let A := (univ : Finset (Sym2 (Fin n))).powerset
  let S := (univ : Finset (Fin n)).powerset.filter fun H => k ≤ H.card
  let C : ℝ := 2^Fintype.card (Sym2 (Fin n))
  let P (H : Finset (Fin n)) (X : Finset (Sym2 (Fin n))) :=
    cost (edges H) X u v + cost (edges H) X v u
  have hP H X : 0 ≤ P H X := by dsimp [P,cost,u,v]; positivity
  have hmean H : (∑ X ∈ A, P H X) = C*(2*((u+v)/2)^(H.card.choose 2)) := by
    dsimp only [P,A,C]
    rw [sum_add_distrib, mean_cost, mean_cost, edge_card, add_comm v u]
    ring
  have hm : (∑ X ∈ A, ∑ H ∈ S, P H X) < ∑ _X ∈ A, (1:ℝ) := by
    rw [sum_comm, sum_congr rfl (fun H _ => hmean H), ← mul_sum, ← mul_sum]
    have hA : (A.card : ℝ) = C := by simp [A,C]
    simp only [sum_const, nsmul_eq_mul, mul_one, hA]
    have hC : 0 < C := by dsimp [C]; positivity
    simpa only [mul_one] using mul_lt_mul_of_pos_left hh hC
  obtain ⟨X,_,hX⟩ := exists_lt_of_sum_lt hm
  refine Nat.sInf_le ⟨fun e => decide (e∈X), ?_⟩
  intro H hH
  apply penalty_small a t ht H X
  exact lt_of_le_of_lt (single_le_sum (fun H _ => hP H X)
    (show H ∈ S by simp [S,hH])) hX

end BalancedRamsey

theorem bnd_local : type_of% @Erdos162.erdos_162.variants.bounds := by
  intro a ha ha'
  obtain ⟨t,ht,hr'⟩ := BalancedRamsey.tilted a ha'
  let r := (Real.exp ((a-1)*t)+Real.exp (a*t))/2
  have hr : 0 < r := by dsimp [r]; positivity
  change r < 1 at hr'
  let D := -Real.log r
  have hD : 0 < D := neg_pos.mpr (Real.log_neg hr hr')
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  let c := (Real.log 4)⁻¹
  have hc : 0 < c := inv_pos.mpr hl4
  refine ⟨c, c + 4/D + 3, hc, by have := div_pos (by norm_num : (0:ℝ)<4) hD; linarith, ?_⟩
  filter_upwards [eventually_ge_atTop 4] with n hn
  have hn0 : 0 < n := by omega
  have hn4 : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hl : 1 < Real.log n := by
    apply Real.lt_log_iff_exp_lt (by positivity) |>.mpr
    exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286:ℝ)<4)).trans_le hn4
  refine ⟨?_,?_⟩
  · simpa [c, div_eq_inv_mul] using BalancedRamsey.lower n a ha hn0
  let q := 4 * Real.log n / D + 1
  have hq : 0 < q := by dsimp [q]; positivity
  let k := ⌈q⌉₊
  have hle : q ≤ (k:ℝ) := Nat.le_ceil _
  have hk : 0 < k := by exact_mod_cast lt_of_lt_of_le hq hle
  have hcut (h : ℕ) (hh : k ≤ h) : r^(h.choose 2) ≤ (1/(4*(n:ℝ)))^h := by
    apply BalancedRamsey.cutoff hr hr' hn
    exact hle.trans (by exact_mod_cast hh)
  have htot := BalancedRamsey.total_penalty hn hk hcut
  have hF := BalancedRamsey.select a t ht htot
  have hup := Nat.ceil_lt_add_one hq.le
  change (k:ℝ) < 4 * Real.log n / D + 1 + 1 at hup
  have hFn : (F n a : ℝ) ≤ k := by exact_mod_cast hF
  rw [show 4 * Real.log n / D = (4/D)*Real.log n by ring] at hup
  nlinarith [mul_pos hc (lt_trans (by norm_num : (0:ℝ)<1) hl)]
theorem OMA.solution : OMA.R_Erdos162_erdos_162_R1.H1 := by
  unfold OMA.R_Erdos162_erdos_162_R1.H1
  intro α h0 h1
  obtain ⟨c₁, c₂, hc, _, hev⟩ := bnd_local α h0 h1
  exact ⟨c₁, hc, hev.mono fun n h => h.1.le⟩
