import OMAStatements.S_mo_485411

namespace OMA.S_mo_485411
open Matrix Finset

private lemma projector_rank {d k} (P : Mat d) :
    Projector k P ↔ Pᵀ=P ∧ P*P=P ∧ P.rank=k := by
  have hr (h : P*P=P) : P.trace=(P.rank:ℝ) := by
    have he : IsIdempotentElem P.mulVecLin := by
      change P.mulVecLin.comp P.mulVecLin=P.mulVecLin
      rw [← Matrix.mulVecLin_mul,h]
    have hh := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    change LinearMap.trace ℝ (Fin d→ℝ) (Matrix.toLin' P)=(P.rank:ℝ) at hh
    simpa only [Matrix.trace_toLin'_eq] using hh
  constructor
  · rintro ⟨hs,h,ht⟩
    exact ⟨hs,h,by exact_mod_cast ((hr h).symm.trans ht)⟩
  · rintro ⟨hs,h,ht⟩
    exact ⟨hs,h,(hr h).trans (congrArg (fun z : ℕ => (z:ℝ)) ht)⟩

private def cut (d k : ℕ) : Mat d :=
  diagonal (fun i : Fin d => if i.val<k then 1 else 0)

private lemma cut_projector {d k : ℕ} (hk : k ≤ d) : Projector k (cut d k) := by
  refine ⟨by simp [cut], ?_, ?_⟩
  · rw [cut,diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases h : i.val<k <;> simp [h]
  · simp [cut,Finset.sum_boole,Fin.card_filter_val_lt,min_eq_right hk]

private lemma perp_proj {d k} {P : Mat d} (hP : Projector k P) :
    (1-P)ᵀ=1-P ∧ (1-P)*(1-P)=1-P := by
  exact ⟨by simp [hP.1],by simp only [sub_mul,mul_sub,one_mul,mul_one,hP.2.1,sub_self,sub_zero]⟩

private lemma diagonals {d} {P : Mat d} (hs : Pᵀ=P) (hp : P*P=P) (i : Fin d) :
    (∑ j, (P i j)^2) = P i i := by
  have h (j : Fin d) : P j i = P i j := congrFun (congrFun hs i) j
  simpa only [Matrix.mul_apply,h,← pow_two] using congrFun (congrFun hp i) i

private lemma proj_zero {d} {P : Mat d} (hs : Pᵀ=P) (hp : P*P=P)
    {i : Fin d} (h : P i i=0) (j : Fin d) : P i j=0 := by
  have hj := Finset.single_le_sum (f:=fun t => (P i t)^2) (fun t _ => sq_nonneg _) (mem_univ j)
  rw [diagonals hs hp,h] at hj
  nlinarith

private def lin {d} (l : Fin d → ℝ) (Q : Mat d) : ℝ := ∑ i,l i*Q i i
private def quad {d} (l : Fin d → ℝ) (Q : Mat d) : ℝ := ∑ i, ∑ j,l i*l j*(Q i j)^2

private def Aligned {d} (l : Fin d → ℝ) (t : ℝ) (P : Mat d) : Prop :=
  (∀ i, t < l i → (1-P) i i = 0) ∧ (∀ i, l i < t → P i i=0)

private lemma lin_gap {d k} (hk : k<d) (l : Fin d → ℝ) (hl : Antitone l) (P : Mat d)
    (hp : Projector k P) :
    let t := l ⟨k,hk⟩
    let T := cut d k
    lin l (1-T) ≤ lin l (1-P) ∧ (lin l (1-T) = lin l (1-P) ↔ Aligned l t P) := by
  let t := l ⟨k,hk⟩
  let T := cut d k
  let Q := (1-P : Mat d)
  let g (i : Fin d) := max (l i-t) 0 * Q i i + max (t-l i) 0 * P i i
  have hpi (i) : 0 ≤ P i i := (diagonals hp.1 hp.2.1 i) ▸ Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hqs,hqp⟩ := perp_proj hp
  have hqi (i) : 0 ≤ Q i i := by change 0 ≤ (1-P) i i; rw [← diagonals hqs hqp]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hgn (i) : 0 ≤ g i := add_nonneg (mul_nonneg (le_max_right _ _) (hqi _))
    (mul_nonneg (le_max_right _ _) (hpi _))
  have hadd (i : Fin d) : l i*Q i i - l i*(1-T) i i = g i + t*(T i i-P i i) := by
    by_cases h : i.val<k
    · have hh : t ≤ l i := hl (show i ≤ ⟨k,hk⟩ from le_of_lt h)
      simp [Q,g,T,cut,h,max_eq_left (sub_nonneg.mpr hh),max_eq_right (sub_nonpos.mpr hh)]
      ring
    · have hh : l i ≤ t := hl (show (⟨k,hk⟩ : Fin d) ≤ i from le_of_not_gt h)
      simp [Q,g,T,cut,h,max_eq_right (sub_nonpos.mpr hh),max_eq_left (sub_nonneg.mpr hh)]
      ring
  have htr : ∑ i, (T i i-P i i)=0 := by
    change (∑ i, (T-P) i i)=0
    change (T-P).trace=0
    rw [Matrix.trace_sub,hp.2.2,(cut_projector hk.le).2.2,sub_self]
  have he : lin l Q-lin l (1-T) = ∑ i,g i := by
    unfold lin
    rw [← Finset.sum_sub_distrib,Finset.sum_congr rfl (fun i _ => hadd i),Finset.sum_add_distrib,
      ← Finset.mul_sum,htr,mul_zero,add_zero]
  have hn := Finset.sum_nonneg (s:=univ) (fun i _ => hgn i)
  change lin l (1-T) ≤ lin l Q ∧ (lin l (1-T) = lin l Q ↔ _)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro eq
    have hz (i) : g i=0 := by
      have hu := Finset.single_le_sum (f:=g) (fun j _ => hgn j) (mem_univ i)
      linarith [hgn i]
    constructor
    · intro i hi
      change t<l i at hi
      have h0 := hz i
      simp [g,max_eq_left (sub_nonneg.mpr hi.le),max_eq_right (sub_nonpos.mpr hi.le)] at h0
      exact h0.resolve_left (sub_ne_zero.mpr hi.ne')
    · intro i hi
      change l i<t at hi
      have h0 := hz i
      simp [g,max_eq_left (sub_nonneg.mpr hi.le),max_eq_right (sub_nonpos.mpr hi.le)] at h0
      exact h0.resolve_left (sub_ne_zero.mpr hi.ne')
  · intro ha
    have hz (i) : g i=0 := by
      rcases lt_trichotomy (l i) t with h|h|h
      · simp [g,ha.2 i h,max_eq_right (sub_nonpos.mpr h.le)]
      · simp [g,h]
      · change _*(1-P) i i + _*P i i = 0
        simp [ha.1 i h,max_eq_right (sub_nonpos.mpr h.le)]
    simp [hz] at he
    linarith

private lemma perp_quad {d} (l : Fin d→ℝ) (P : Mat d) :
    quad l (1-P) = (∑ i,(l i)^2) - 2*lin (fun i => (l i)^2) P + quad l P := by
  have h (i j : Fin d) : l i*l j*((1-P) i j)^2 =
      (if i=j then l i^2-2*l i^2*P i i else 0) + l i*l j*(P i j)^2 := by
    by_cases hh : i=j <;> simp [Matrix.sub_apply,hh]
    all_goals ring
  simp only [quad,h,Finset.sum_add_distrib,Finset.sum_ite_eq,mem_univ,if_true]
  simp only [lin,Finset.sum_sub_distrib, ← mul_assoc, Finset.mul_sum]

private lemma diag_sum {d} (l : Fin d → ℝ) {P : Mat d} (hs : Pᵀ=P) (hp : P*P=P) :
    (∑ i,∑ j,l i*(P i j)^2)=lin l P ∧ (∑ i,∑ j,l j*(P i j)^2)=lin l P := by
  constructor
  · simp_rw [← Finset.mul_sum,diagonals hs hp]
    rfl
  · rw [Finset.sum_comm]
    have sym (i j : Fin d) : P i j=P j i := (congrFun (congrFun hs i) j).symm
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum, ← diagonals hs hp i]
    exact congrArg (l i * ·) (Finset.sum_congr rfl fun j _ => by rw [sym j i])

private lemma sum2_ge_entry {d} (a : Fin d → Fin d → ℝ) (ha : ∀ i j, 0≤a i j) (i j) :
    a i j ≤ ∑ p,∑ q,a p q :=
  (Finset.single_le_sum (s:=univ) (fun k _ => ha i k) (mem_univ j)).trans
    (Finset.single_le_sum (s:=univ) (fun p _ => Finset.sum_nonneg (fun q _ => ha p q)) (mem_univ i))

private lemma quad_base {d k} (l : Fin d → ℝ) (hl : ∀ i,0≤l i) (t : ℝ) (ht : 0≤t)
    {P : Mat d} (hp : Projector k P) :
    let c := fun i => min (l i) t
    let z := (∑ i,c i^2) - t^2*k
    z ≤ quad l (1-P) ∧ (z = quad l (1-P) ↔ Aligned l t P) := by
  let c (i : Fin d) := min (l i) t
  let Q := (1-P : Mat d)
  let z := (∑ i,c i^2)-t^2*k
  let a (i j : Fin d) := (l i*l j - c i*c j)*(Q i j)^2
  let b (i j : Fin d) := (t^2 - c i^2 - c j^2 + c i*c j)*(P i j)^2
  have hc0 (i) : 0 ≤ c i := le_min (hl i) ht
  have hct (i) : c i ≤ t := min_le_right _ _
  have ha (i j) : 0 ≤ a i j :=
    mul_nonneg (sub_nonneg.mpr (mul_le_mul (min_le_left ..) (min_le_left ..) (hc0 _) (hl _))) (sq_nonneg _)
  have hb (i j) : 0 ≤ b i j := by
    refine mul_nonneg ?_ (sq_nonneg _)
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hct i)) (sub_nonneg.mpr (hct j)),
      mul_nonneg (hc0 i) (sub_nonneg.mpr (hct i)), mul_nonneg (hc0 j) (sub_nonneg.mpr (hct j))]
  have hsub : quad l Q-quad c Q=∑ i,∑ j,a i j := by
    simp [quad,a,sub_mul,Finset.sum_sub_distrib]
  have htP : (∑ i, ∑ j,t^2*(P i j)^2) = t^2*k := by
    rw [(diag_sum (fun _ => t^2) hp.1 hp.2.1).1]
    simp only [lin,← Finset.mul_sum]
    change t^2*P.trace=_
    rw [hp.2.2]
  have hqb : quad c Q - z = ∑ i,∑ j,b i j := by
    obtain ⟨hi,hj⟩ := diag_sum (fun i => c i^2) hp.1 hp.2.1
    simp only [b,add_mul,sub_mul,Finset.sum_sub_distrib,Finset.sum_add_distrib,htP,hi,hj]
    change quad c (1-P) - ((∑ i,c i^2)-t^2*k) = _ + quad c P
    rw [perp_quad]
    ring
  have han := Finset.sum_nonneg (s:=univ) (fun i _ => Finset.sum_nonneg (s:=univ) (fun j _ => ha i j))
  have hbn := Finset.sum_nonneg (s:=univ) (fun i _ => Finset.sum_nonneg (s:=univ) (fun j _ => hb i j))
  change z ≤ quad l Q ∧ (z=quad l Q ↔ _)
  refine ⟨by linarith, ?_⟩
  constructor
  · intro he
    constructor
    · intro i hh
      have hz := sum2_ge_entry a ha i i
      have heq : a i i=0 := by linarith [ha i i]
      have hd : 0 < l i*l i-t*t := by nlinarith [mul_pos (sub_pos.mpr hh) (show 0<l i+t by linarith)]
      change (l i*l i-c i*c i)*(Q i i)^2=0 at heq
      rw [show c i=t from min_eq_right hh.le] at heq
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp heq).resolve_left hd.ne')
    · intro i hh
      have hz := sum2_ge_entry b hb i i
      have heq : b i i=0 := by linarith [hb i i]
      have hd : 0<t^2-(l i)^2-(l i)^2+(l i)*(l i) := by
        nlinarith [mul_pos (sub_pos.mpr hh) (show 0<t+l i by linarith [hl i])]
      change (t^2-c i^2-c i^2+c i*c i)*(P i i)^2=0 at heq
      rw [show c i=l i from min_eq_left hh.le] at heq
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp heq).resolve_left hd.ne')
  · intro he
    obtain ⟨hs,hi⟩ := perp_proj hp
    have az (i j) : a i j=0 := by
      by_cases h : t<l i
      · have hz : Q i j = 0 := proj_zero hs hi (he.1 i h) j
        simp only [a,hz,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow,mul_zero]
      by_cases h' : t<l j
      · have hz := proj_zero hs hi (he.1 j h') i
        have hsij : Q i j=Q j i := (congrFun (congrFun hs i) j).symm
        have hzz : Q i j=0 := hsij.trans hz
        simp [a,hzz]
      · simp [a,c,min_eq_left (le_of_not_gt h),min_eq_left (le_of_not_gt h')]
    have bz (i j) : b i j=0 := by
      by_cases h : l i<t
      · simp [b,proj_zero hp.1 hp.2.1 (he.2 i h) j]
      by_cases h' : l j<t
      · have hz := proj_zero hp.1 hp.2.1 (he.2 j h') i
        have hsij : P i j=P j i := (congrFun (congrFun hp.1 i) j).symm
        simp [b,hsij,hz]
      · simp [b,c,min_eq_right (le_of_not_gt h),min_eq_right (le_of_not_gt h'),sq]
    simp [az] at hsub
    simp [bz] at hqb
    linarith

private lemma cut_aligned {d k : ℕ} (hk : k<d) {l : Fin d→ℝ} (hl : Antitone l) :
    Aligned l (l ⟨k,hk⟩) (cut d k) := by
  constructor
  · intro i hi
    have hv : i.val<k := by
      by_contra h
      exact hi.not_ge (hl (show (⟨k,hk⟩ : Fin d) ≤ i from le_of_not_gt h))
    simp [cut,hv]
  · intro i hi
    have hv : ¬i.val<k := fun h => hi.not_ge (hl (show i ≤ (⟨k,hk⟩ : Fin d) from le_of_lt h))
    simp [cut,hv]

private def err {n d} (X : Rect n d) (P : Mat d) : Mat n :=
  X*Xᵀ-(X*P)*(X*P)ᵀ

private lemma err_eq {n d k} (X : Rect n d) {P : Mat d} (hp : Projector k P) :
    err X P=X*(1-P)*Xᵀ := by
  unfold err
  rw [Matrix.transpose_mul,hp.1,Matrix.mul_assoc X P,← Matrix.mul_assoc P P,hp.2.1,
    Matrix.mul_sub,Matrix.mul_one,Matrix.sub_mul,Matrix.mul_assoc]

private lemma err_gram {n d k} (X : Rect n d) {P : Mat d} (hp : Projector k P) :
    err X P=(X*(1-P))*(X*(1-P))ᵀ := by
  obtain ⟨hs,hi⟩ := perp_proj hp
  rw [err_eq X hp,Matrix.transpose_mul,hs]
  calc
    _ = X*((1-P)*(1-P))*Xᵀ := by rw [hi]
    _ = _ := by simp only [Matrix.mul_assoc]

private lemma distance_gram {n d} (X : Rect n d) (i j : Fin n) :
    dsq X i j=(X*Xᵀ) i i+(X*Xᵀ) j j-2*(X*Xᵀ) i j := by
  simp only [dsq,Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

private lemma dist_err {n d} (X : Rect n d) (P : Mat d) :
    distanceLoss X P = ∑ i,∑ j, (err X P i i+err X P j j-2*err X P i j) := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [distance_gram,err,Matrix.sub_apply]
  ring

private lemma dist_nonneg {n d k} (X : Rect n d) {P : Mat d} (hp : Projector k P) :
    0≤distanceLoss X P := by
  rw [dist_err X P,err_gram X hp]
  simp_rw [← distance_gram]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma centered_mul {n d e} (X : Rect n d) (T : Rect d e) (hx : Centered X) :
    Centered (X*T) := by
  intro j
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  calc
    _ = ∑ l : Fin d, (∑ i : Fin n, X i l)*T l j :=
      Finset.sum_congr rfl fun l _ => (Finset.sum_mul ..).symm
    _ = 0 := by simp [show ∀ l : Fin d, (∑ i : Fin n, X i l)=0 from hx]

private lemma dist_trace {n d k} (X : Rect n d) (hx : Centered X) {P : Mat d} (hp : Projector k P) :
    distanceLoss X P = 2*(n:ℝ)*(err X P).trace := by
  have hsum (j : Fin n) : ∑ i, err X P i j=0 := by
    rw [err_eq X hp]
    exact centered_mul (X*(1-P)) Xᵀ (centered_mul X (1-P) hx) j
  rw [dist_err]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul, ← Finset.mul_sum]
  have hz : (∑ i : Fin n, ∑ j : Fin n, err X P i j)=0 := calc
    _ = ∑ j : Fin n, ∑ i : Fin n, err X P i j := Finset.sum_comm
    _ = 0 := by simp [hsum]
  rw [hz]
  unfold Matrix.trace
  simp [Matrix.diag]
  ring

private lemma gram_trace {n d k} (X : Rect n d) {P : Mat d} (hp : Projector k P) :
    gramLoss X P = ((err X P)*(err X P)).trace := by
  have hsym : (err X P)ᵀ=err X P := by rw [err_gram X hp,Matrix.transpose_mul,Matrix.transpose_transpose]
  change (∑ i,∑ j,(err X P i j)^2)=_
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [show err X P j i = err X P i j from congrFun (congrFun hsym i) j,pow_two]

private lemma pca_losses {n d k} (Y : Rect n d) (hy : Centered Y) (l : Fin d→ℝ)
    (hg : Yᵀ*Y=diagonal l) {P : Mat d} (hp : Projector k P) :
    distanceLoss Y P=2*(n:ℝ)*lin l (1-P) ∧ gramLoss Y P=quad l (1-P) := by
  let Q := 1-P
  have hqs : Qᵀ=Q := (perp_proj hp).1
  constructor
  · rw [dist_trace Y hy hp, err_eq Y hp,Matrix.trace_mul_comm, ← Matrix.mul_assoc,hg]
    simp [lin,Matrix.trace,Matrix.diag]
  · rw [gram_trace Y hp,err_eq Y hp]
    change (Y*Q*Yᵀ*(Y*Q*Yᵀ)).trace=_
    calc
      _ = ((Yᵀ*Y)*Q*(Yᵀ*Y)*Q).trace := by
        rw [show Y*Q*Yᵀ*(Y*Q*Yᵀ)=(Y*Q*Yᵀ*Y*Q)*Yᵀ by simp [Matrix.mul_assoc],
          Matrix.trace_mul_comm]
        simp [Matrix.mul_assoc]
      _ = _ := by
        rw [hg]
        apply Finset.sum_congr rfl
        intro i _
        change (∑ j, ((diagonal l * Q)*diagonal l) i j * Q j i) = ∑ j,l i*l j*(Q i j)^2
        simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [show Q j i=Q i j from congrFun (congrFun hqs i) j]
        ring


private def rotate {d} (U P : Mat d) : Mat d := Uᵀ*P*U

private lemma rotate_cancel {d} {U : Mat d} (hh : U*Uᵀ=1) (P : Mat d) :
    rotate Uᵀ (rotate U P) = P := by
  simp only [rotate,Matrix.transpose_transpose]
  calc
    _ = (U*Uᵀ)*P*(U*Uᵀ) := by simp [Matrix.mul_assoc]
    _ = _ := by rw [hh,one_mul,mul_one]

private lemma rotate_proj {d k} {U P : Mat d} (hh : U*Uᵀ=1) (hp : Projector k P) :
    Projector k (rotate U P) := by
  refine ⟨by simp [rotate, Matrix.transpose_mul,hp.1, Matrix.mul_assoc], ?_, ?_⟩
  · dsimp [rotate]
    calc
      _ = Uᵀ*(P*(U*Uᵀ)*P)*U := by simp [Matrix.mul_assoc]
      _ = _ := by rw [hh,mul_one,hp.2.1]
  · rw [rotate,Matrix.trace_mul_comm, ← Matrix.mul_assoc,hh,one_mul,hp.2.2]

private lemma rotate_losses {n d} (X : Rect n d) {U : Mat d} (hh : U*Uᵀ=1) (P : Mat d) :
    distanceLoss (X*U) (rotate U P) = distanceLoss X P ∧
      gramLoss (X*U) (rotate U P) = gramLoss X P := by
  have hx (Z : Rect n d) : (Z*U)*(Z*U)ᵀ=Z*Zᵀ := by
    rw [Matrix.transpose_mul,Matrix.mul_assoc, ← Matrix.mul_assoc U Uᵀ,hh,Matrix.one_mul]
  have hp : X*U*rotate U P=(X*P)*U := by
    calc
      _ = X*(U*Uᵀ)*P*U := by simp [rotate,Matrix.mul_assoc]
      _ = _ := by rw [hh,Matrix.mul_one]
  have herr : err (X*U) (rotate U P)=err X P := by simp only [err,hx,hp]
  constructor
  · simp only [dist_err,herr]
  · change (∑ i,∑ j,(err (X*U) (rotate U P) i j)^2) = ∑ i,∑ j,(err X P i j)^2
    rw [herr]

private lemma spectral {n d} (X : Rect n d) :
    ∃ (U : Mat d) (l : Fin d→ℝ), U*Uᵀ=1 ∧ Uᵀ*U=1 ∧ Antitone l ∧
      (∀ i,0≤l i) ∧ (X*U)ᵀ*(X*U)=diagonal l := by
  classical
  let H : Mat d := Xᵀ*X
  have hpos : H.PosSemidef := by simpa [H] using Matrix.posSemidef_conjTranspose_mul_self X
  let h := hpos.isHermitian
  let V : Matrix.orthogonalGroup (Fin d) ℝ := h.eigenvectorUnitary
  let e : Fin d ≃ Fin d := (finCongr (Fintype.card_fin d).symm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin d))))
  let U : Mat d := (V : Mat d).submatrix id e
  let l (i : Fin d) := h.eigenvalues (e i)
  have hVV : (V : Mat d)*(V : Mat d)ᵀ=1 := V.2.2
  have hVV' : (V : Mat d)ᵀ*(V : Mat d)=1 := V.2.1
  have hU : U*Uᵀ=1 := by
    ext i j
    change (∑ k, (V:Mat d) i (e k)*(V:Mat d) j (e k)) = (1:Mat d) i j
    rw [e.sum_comp (fun k => (V:Mat d) i k*(V:Mat d) j k)]
    exact congrFun (congrFun hVV i) j
  have hU' : Uᵀ*U=1 := by
    ext i j
    change ((V:Mat d)ᵀ*(V:Mat d)) (e i) (e j) = (1:Mat d) i j
    rw [hVV']
    simp [Matrix.one_apply]
  have hspec : (V : Mat d)ᵀ*H*(V : Mat d)=diagonal h.eigenvalues := by
    simpa [V,Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using
      h.conjStarAlgAut_star_eigenvectorUnitary
  have hmul : H*(V:Mat d)=(V:Mat d)*diagonal h.eigenvalues := by
    rw [← hspec,← Matrix.mul_assoc,← Matrix.mul_assoc,hVV,one_mul]
  have hmul' : H*U=U*diagonal l := by
    ext i j
    change (H*(V:Mat d)) i (e j) = _
    rw [hmul]
    simp [Matrix.mul_diagonal,l,U]
  refine ⟨U,l,hU,hU',?_,fun i => hpos.eigenvalues_nonneg (e i),?_⟩
  · intro i j hij
    change h.eigenvalues (e j) ≤ h.eigenvalues (e i)
    simp only [Matrix.IsHermitian.eigenvalues,e,Equiv.trans_apply,Equiv.symm_apply_apply]
    exact h.eigenvalues₀_antitone (show (finCongr (Fintype.card_fin d).symm i) ≤
      finCongr (Fintype.card_fin d).symm j from hij)
  · rw [Matrix.transpose_mul,Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ X]
    change Uᵀ*(H*U)=_
    rw [hmul',← Matrix.mul_assoc,hU',one_mul]


private lemma uncentered :
    ∃ (X : Rect 2 2) (P Z : Mat 2), Minimizes 1 (distanceLoss X) P ∧
      Projector 1 Z ∧ gramLoss X Z < gramLoss X P := by
  let X : Rect 2 2 := !![2,1;2,-1]
  let P : Mat 2 := !![0,0;0,1]
  let Z : Mat 2 := !![1,0;0,0]
  have hp : Projector 1 P := by
    constructor
    · ext i j;fin_cases i <;> fin_cases j <;> rfl
    constructor
    · ext i j;fin_cases i <;> fin_cases j <;> norm_num [P,Matrix.mul_apply,Fin.sum_univ_two]
    · norm_num [P,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  have hz : Projector 1 Z := by
    constructor
    · ext i j;fin_cases i <;> fin_cases j <;> rfl
    constructor
    · ext i j;fin_cases i <;> fin_cases j <;> norm_num [Z,Matrix.mul_apply,Fin.sum_univ_two]
    · norm_num [Z,Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  refine ⟨X,P,Z,⟨hp,?_⟩,hz,?_⟩
  · intro W hw
    have hd : distanceLoss X P = 0 := by
      norm_num [X,P,distanceLoss,dsq,Fin.sum_univ_two,Matrix.mul_apply]
    rw [hd]
    exact dist_nonneg X hw
  · norm_num [X,P,Z,gramLoss,Matrix.mul_apply,Matrix.transpose_apply,Fin.sum_univ_two]

private lemma centered_in_principal {n d k} (hn : 0<n) (hk : k<d) (X : Rect n d) (hx : Centered X)
    {l : Fin d→ℝ} (hg : Xᵀ*X=diagonal l) (hl : Antitone l) (h0 : ∀ i,0≤l i) :
    Minimizes k (distanceLoss X) (cut d k) ∧
      ∀ P, Minimizes k (distanceLoss X) P ↔ Minimizes k (gramLoss X) P := by
  let T := cut d k
  let t := l ⟨k,hk⟩
  have ht : Projector k T:=cut_projector hk.le
  have loc (P : Mat d) (hp : Projector k P) :=
    pca_losses X hx l hg hp
  let z := (∑ i,(min (l i) t)^2)-t^2*(k:ℝ)
  have hqt : z=quad l (1-T) := (quad_base l h0 t (h0 _) ht).2.mpr (cut_aligned hk hl)
  have hmin (P : Mat d) (hp : Projector k P) :
      distanceLoss X T ≤ distanceLoss X P ∧ gramLoss X T ≤ gramLoss X P := by
    obtain ⟨hd,hg⟩ := loc P hp
    rw [hd,hg,(loc T ht).1,(loc T ht).2,← hqt]
    exact ⟨mul_le_mul_of_nonneg_left (lin_gap hk l hl P hp).1 (by positivity),
      (quad_base l h0 t (h0 _) hp).1⟩
  refine ⟨⟨ht,fun Z hz => (hmin Z hz).1⟩, ?_⟩
  intro P
  constructor
  · rintro ⟨hp,h⟩
    have eq := le_antisymm (hmin P hp).1 (h T ht)
    rw [(loc T ht).1,(loc P hp).1] at eq
    have he := (lin_gap hk l hl P hp).2.mp ((mul_right_inj' (by positivity : 2*(n:ℝ) ≠ 0)).mp eq)
    have hq := (quad_base l h0 t (h0 _) hp).2.mpr he
    have hge : gramLoss X T = gramLoss X P := by rw [(loc T ht).2,(loc P hp).2,← hqt];exact hq
    exact ⟨hp,fun Z hz => hge ▸ (hmin Z hz).2⟩
  · rintro ⟨hp,h⟩
    have eq := le_antisymm (hmin P hp).2 (h T ht)
    rw [(loc T ht).2,(loc P hp).2,← hqt] at eq
    have he := (quad_base l h0 t (h0 _) hp).2.mp eq
    have hd := (lin_gap hk l hl P hp).2.mpr he
    have hde : distanceLoss X T = distanceLoss X P := by rw [(loc T ht).1,(loc P hp).1,hd]
    exact ⟨hp,fun Z hz => hde ▸ (hmin Z hz).1⟩

private lemma centered_general {n d k} (hn : 0<n) (hk : k<d) (X : Rect n d) (hx : Centered X) :
    (∃ P, Minimizes k (distanceLoss X) P) ∧
       ∀ P, Minimizes k (distanceLoss X) P ↔ Minimizes k (gramLoss X) P := by
  obtain ⟨U,l,hu,hu',hl,hl₀,hdiag⟩:=spectral X
  let Y:=X*U
  obtain ⟨hmin,heq⟩:=centered_in_principal hn hk Y (centered_mul X U hx) hdiag hl hl₀
  have hut : Uᵀ*(Uᵀ)ᵀ=1 := by simpa using hu'
  have hback (Z : Mat d) : rotate U (rotate Uᵀ Z)=Z := by simpa using rotate_cancel hut Z
  have transfer (f g : Mat d → ℝ) (hfg : ∀ P,g (rotate U P)=f P) (P : Mat d) :
      Minimizes k f P ↔ Minimizes k g (rotate U P) := by
    constructor
    · rintro ⟨hp,h⟩
      refine ⟨rotate_proj hu hp, ?_⟩
      intro Z hz
      rw [hfg, ← hback Z, hfg]
      exact h _ (rotate_proj hut hz)
    · rintro ⟨hp,h⟩
      refine ⟨by simpa only [rotate_cancel hu] using rotate_proj hut hp, ?_⟩
      intro Z hz
      rw [← hfg,← hfg Z]
      exact h _ (rotate_proj hu hz)
  have hd := transfer (distanceLoss X) (distanceLoss Y) (fun P => (rotate_losses X hu P).1)
  have hg := transfer (gramLoss X) (gramLoss Y) (fun P => (rotate_losses X hu P).2)
  refine ⟨⟨rotate Uᵀ (cut d k),(hd _).mpr (?_)⟩, fun P => (hd P).trans ((heq _).trans (hg P).symm)⟩
  rwa [hback]

end OMA.S_mo_485411
open OMA.S_mo_485411
theorem OMA.solution : type_of% @OMA.S_mo_485411.main :=
  ⟨fun _ _ P => projector_rank P, fun _ _ _ X hn hk hx => centered_general hn hk X hx,uncentered⟩
