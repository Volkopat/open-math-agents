import OMAStatements.S_oeis_a384539

/-!
Three consecutive splits around the centre force one linear relation in the
scale `10^(k-1)`. The constant difference is below 10^8, whereas a zero
linear coefficient would make the product of the outer quotients exactly 100.
The two positive central differences require that product to exceed 100.
Thus only finitely many half-lengths remain. The finite checker derives the
possible left half by division and verifies the original split test.
-/


/-! An arithmetic constraint on three consecutive divisible decimal splits. -/

namespace OMA.DecimalSplit

private theorem coefficient_zero {x q r : ℤ} (hq : 0 < q)
    (hr0 : -q < r) (hr1 : r < q) (h : x*q = r) : x = 0 := by
  by_contra hn
  rcases (show x ≤ -1 ∨ 1 ≤ x by omega) with hl | hl
  · have g := mul_le_mul_of_nonneg_right hl hq.le
    rw [h] at g
    linarith
  · have g := mul_le_mul_of_nonneg_right hl hq.le
    rw [h] at g
    linarith

theorem midpoint_bound {A B P Q R a b u v f g : ℤ}
    (hA : A = 10*P+a) (hB : B=b*Q+R) (hc : v*B=u*A)
    (hl : g*P=10*a*Q+B) (hr : f*R=10*A+b)
    (hP : 0 < P) (hQ : 0 < Q) (ha : 0 < a) (ha' : a ≤ 9)
    (hb : 0 < b) (hb' : b ≤ 9) (hu : 0 < u) (hu' : u ≤ 9)
    (hv : 0 < v) (hv' : v ≤ 99) (hf : 0 < f) (hg : 0 < g)
    (hg' : g < 1000) (hfg : f*g < 1000000) :
    Q < 100000000 := by
  let D := v*g-10*u
  let C := f*u-10*v
  have hDP : D*P = a*(10*v*Q+u) := by
    dsimp [D]
    linear_combination v*hl + hc + u*hA
  have hD : 0 < D := by
    have hp : 0 < a*(10*v*Q+u) := by positivity
    by_contra hd
    have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) hP.le
    rw [hDP] at hneg
    omega
  have hDA : D*A = a*v*(100*Q+g) := by
    calc
      D*A = 10*(D*P)+D*a := by rw [hA]; ring
      _ = a*v*(100*Q+g) := by rw [hDP]; dsimp [D]; ring
  have hCA : C*A = b*v*(f*Q+1) := by
    dsimp [C]
    linear_combination -f*hc + f*v*hB + v*hr
  have hApos : 0 < A := by rw [hA]; positivity
  have hC : 0 < C := by
    have hp : 0 < b*v*(f*Q+1) := by positivity
    by_contra hd
    have hneg := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hd) hApos.le
    rw [hCA] at hneg
    omega
  have hcros : C*a*(100*Q+g) = D*b*(f*Q+1) := by
    apply mul_left_cancel₀ hv.ne'
    linear_combination D*hCA - C*hDA
  have hcoeff : (100*C*a - D*b*f)*Q = D*b - C*a*g := by
    linear_combination hcros
  have hD' : D ≤ v*g := by dsimp [D]; linarith
  have hC' : C ≤ f*u := by dsimp [C]; linarith
  have hDb : D*b < 100000000 := by
    have h0 := mul_le_mul_of_nonneg_right hD' hb.le
    have h1 : v*g ≤ 99*1000 :=
      mul_le_mul hv' (le_of_lt hg') hg.le (by decide)
    have h2 := mul_le_mul h1 hb' hb.le (show (0:ℤ) ≤ 99*1000 by decide)
    calc
      D*b ≤ v*g*b := h0
      _ ≤ 99*1000*9 := h2
      _ < 100000000 := by decide
  have hCag : C*a*g < 100000000 := by
    have h0 := mul_le_mul_of_nonneg_right hC' (show 0 ≤ a*g by positivity)
    have h1 : u*a ≤ 81 := by
      simpa using mul_le_mul hu' ha' ha.le (show (0:ℤ) ≤ 9 by decide)
    have h2 := mul_le_mul (le_of_lt hfg) h1 (show 0 ≤ u*a by positivity)
      (show (0:ℤ) ≤ 1000000 by decide)
    calc
      C*a*g = C*(a*g) := by ring
      _ ≤ (f*u)*(a*g) := h0
      _ = (f*g)*(u*a) := by ring
      _ ≤ 1000000*81 := h2
      _ < 100000000 := by decide
  by_contra hlarge
  have hDbpos : 0 < D*b := by positivity
  have hCagpos : 0 < C*a*g := by positivity
  have hzero := coefficient_zero hQ (by omega) (by omega) hcoeff
  have hconstant : D*b = C*a*g := by rw [hzero, zero_mul] at hcoeff; linarith
  have hprod : (C*a)*(100-f*g) = 0 := by
    linear_combination hzero + f*hconstant
  have hCa : 0 < C*a := by positivity
  have h100 : f*g = 100 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact (hCa.ne' h).elim
    · omega
  have l : 10*u < v*g := by dsimp [D] at hD; omega
  have r : 10*v < f*u := by dsimp [C] at hC; omega
  have bad : 10*u*(10*v) < v*g*(f*u) :=
    mul_lt_mul'' l r (by positivity) (by positivity)
  have eq : v*g*(f*u) = 10*u*(10*v) := by
    calc
      v*g*(f*u) = u*v*(f*g) := by ring
      _ = 10*u*(10*v) := by rw [h100]; ring
  exact (ne_of_lt bad) eq.symm

end OMA.DecimalSplit


/-! A large term has three consecutive divisible splits around its centre. -/

namespace OMA.DecimalSplit

open OMA.S_oeis_a384539

private theorem digitTimesBase_lt {a B T : ℕ} (ha : a < 10) (hB : B < T) :
    a*T+B < 10*T := by
  have h := Nat.mul_le_mul_right T (show a ≤ 9 by omega)
  calc
    a*T+B ≤ 9*T+B := Nat.add_le_add_right h _
    _ < 10*T := by omega

private theorem topDigit_remainder (n e : ℕ)
    (h : n / 10^e % 10 ≠ 0) : 10^e ≤ n % 10^(e+1) := by
  let d : ℕ := 10^e
  let a := n/d%10
  let b := n%d
  have hd : 0 < d := by dsimp [d]; positivity
  have ha : 0 < a := Nat.pos_of_ne_zero h
  have ha' : a < 10 := Nat.mod_lt _ (by decide)
  have hb : b < d := Nat.mod_lt _ hd
  have h₀ : n = d*(n/d)+b := (Nat.div_add_mod n d).symm
  have h₁ : n/d = 10*(n/d/10)+a := (Nat.div_add_mod (n/d) 10).symm
  have hrem : a*d+b < d*10 := by simpa [Nat.mul_comm d 10] using digitTimesBase_lt ha' hb
  have h₂ : n = (d*10)*(n/d/10)+(a*d+b) := by
    conv_lhs => rw [h₀,h₁]
    ring
  have he : n%(d*10) = a*d+b := by
    conv_lhs => rw [h₂, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
  rw [pow_succ]
  change d ≤ n%(d*10)
  rw [he]
  exact (by simpa using Nat.mul_le_mul_right d (show 1 ≤ a by omega) : d ≤ a*d).trans
    (Nat.le_add_right _ _)

private theorem larger_dvd {a b : ℕ} (ha : 0 < a) (hab : a < b)
    (h : a ∣ b ∨ b ∣ a) : a ∣ b :=
  h.resolve_right (fun hd => (not_le_of_gt hab) (Nat.le_of_dvd ha hd))

private theorem quotient_lt {p s x m : ℕ} (hsp : s ≤ p)
    (h : x*p < m*s) : x < m :=
  Nat.lt_of_mul_lt_mul_right ((Nat.mul_le_mul_left x hsp).trans_lt h)

private structure Center (n k : ℕ) where
  A : ℕ
  B : ℕ
  u : ℕ
  v : ℕ
  f : ℕ
  g : ℕ
  expansion : n = A*10^k+B
  leftDigitPos : 0 < A%10
  leftPos : 0 < A/10
  rightPos : 0 < B%10^(k-1)
  rightLow : 10^(k-1) ≤ B
  rightHigh : B < 10^k
  middle : v*B=u*A
  left : g*(A/10)=A%10*10^k+B
  right : f*(B%10^(k-1))=10*A+B/10^(k-1)
  fpos : 0 < f
  gpos : 0 < g
  product : f*g < 1000000
  shape :
    (10^(k-1)≤A ∧ A<10^k ∧
      ((u=1 ∧ 0<v ∧ v<10) ∨ (v=1 ∧ 0<u ∧ u<10)) ∧ g<1000) ∨
    (10^k≤A ∧ A<10^(k+1) ∧ u=1 ∧ 1<v ∧ v<100 ∧ g<100)

set_option maxHeartbeats 3000000 in
private theorem extract_center {n k : ℕ} (hk : 2 ≤ k)
    (hLen : Nat.log 10 n + 1 = 2*k ∨ Nat.log 10 n + 1 = 2*k+1)
    (hterm : term n) : Nonempty (Center n k) := by
  obtain ⟨hn, hz, hdiv⟩ := hterm
  have digit (i : ℕ) (hi : i ≤ Nat.log 10 n) : n / 10^i % 10 ≠ 0 :=
    hz i (List.mem_range.mpr (by omega))
  have split (j : ℕ) (hj : 0 < j) (hj' : j ≤ Nat.log 10 n) :
      n / 10^j ∣ n % 10^j ∨ n % 10^j ∣ n / 10^j := by
    have h := hdiv (j-1) (List.mem_range.mpr (by omega))
    simpa only [show j-1+1=j by omega] using h
  let T : ℕ := 10^k
  let Q : ℕ := 10^(k-1)
  let S : ℕ := 10^(k-2)
  have hT : T = 10*Q := by
    dsimp [T,Q]
    conv_lhs => rw [show k=(k-1)+1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have hQ : Q = 10*S := by
    dsimp [Q,S]
    conv_lhs => rw [show k-1=(k-2)+1 by omega]
    rw [pow_succ, Nat.mul_comm]
  have tpos : 0 < T := by dsimp [T]; positivity
  have qpos : 0 < Q := by dsimp [Q]; positivity
  have spos : 0 < S := by dsimp [S]; positivity
  let A := n/T
  let B := n%T
  let P := A/10
  let R := B%Q
  let a := A%10
  let b := B/Q
  have hexp : n = A*T+B := by simpa [A,B,Nat.mul_comm] using (Nat.div_add_mod n T).symm
  have hA : A = 10*P+a := (Nat.div_add_mod A 10).symm
  have hB : B = b*Q+R := by simpa [b,R,Nat.mul_comm] using (Nat.div_add_mod B Q).symm
  have hBlt : B < T := Nat.mod_lt _ tpos
  have hBge : Q ≤ B := by
    have h := topDigit_remainder n (k-1) (digit _ (by omega))
    simpa [T,Q,B,show k-1+1=k by omega] using h
  have hRlt : R < Q := Nat.mod_lt _ qpos
  have hap : 0 < a := Nat.pos_of_ne_zero (digit k (by omega))
  have ha10 : a < 10 := Nat.mod_lt _ (by decide)
  have hb10 : b < 10 := (Nat.div_lt_iff_lt_mul qpos).mpr (hT ▸ hBlt)
  have hlDiv : n/(10*T) = P := by
    rw [Nat.mul_comm 10 T, ← Nat.div_div_eq_div_mul]
  have hlMod : n%(10*T) = a*T+B := by
    have h : a*T+B < 10*T := digitTimesBase_lt ha10 hBlt
    have e : n=(10*T)*P+(a*T+B) := by rw [hexp,hA]; ring
    rw [e,Nat.mul_add_mod, Nat.mod_eq_of_lt h]
  have hrDiv : n/Q = 10*A+b := by
    have e : n = Q*(10*A)+B := by rw [hexp,hT]; ring
    rw [e,Nat.mul_add_div qpos]
  have hrMod : n%Q = R := by
    change n%Q = B%Q
    have e : n = Q*(10*A)+B := by rw [hexp,hT]; ring
    conv_lhs => rw [e,Nat.mul_add_mod]
  have hRge : S ≤ R := by
    have h := topDigit_remainder n (k-2) (digit _ (by omega))
    rw [show k-2+1=k-1 by omega] at h
    change S ≤ n%Q at h
    rwa [hrMod] at h
  have hMiddle : A ∣ B ∨ B ∣ A := split k (by omega) (by omega)
  have hLeft : P ∣ a*T+B ∨ a*T+B ∣ P := by
    have h := split (k+1) (by omega) (by omega)
    rw [show (10:ℕ)^(k+1)=10*T by simp [T,pow_succ,Nat.mul_comm],hlDiv,hlMod] at h
    exact h
  have hRight : 10*A+b ∣ R ∨ R ∣ 10*A+b := by
    have h := split (k-1) (by omega) (by omega)
    change n/Q ∣ n%Q ∨ n%Q ∣ n/Q at h
    rwa [hrDiv,hrMod] at h
  have upper := Nat.lt_pow_succ_log_self (b := 10) (by decide) n
  have lower := Nat.pow_log_le_self 10 (by omega : n≠0)
  have hAbounds :
      (Q≤A ∧ A<T) ∨ (T≤A ∧ A<10*T) := by
    rcases hLen with e | e
    · left
      have l : Nat.log 10 n = (k-1)+k := by omega
      have r : (Nat.log 10 n).succ = k+k := by omega
      rw [l,pow_add] at lower
      rw [r,pow_add] at upper
      exact ⟨(Nat.le_div_iff_mul_le tpos).mpr lower,
        (Nat.div_lt_iff_lt_mul tpos).mpr upper⟩
    · right
      have l : Nat.log 10 n = k+k := by omega
      have r : (Nat.log 10 n).succ = (k+1)+k := by omega
      rw [l,pow_add] at lower
      rw [r,pow_add,pow_succ] at upper
      exact ⟨(Nat.le_div_iff_mul_le tpos).mpr lower,
        (Nat.div_lt_iff_lt_mul tpos).mpr (by simpa only [T,Nat.mul_comm 10] using upper)⟩
  have hAge : Q ≤ A := hAbounds.elim And.left fun h => by omega
  have hAlt : A < 10*T := hAbounds.elim (fun h => by omega) And.right
  have hPge : S ≤ P := (Nat.le_div_iff_mul_le (by decide : 0<10)).mpr (by omega)
  have hp : 0 < P := spos.trans_le hPge
  have hRpos : 0 < R := spos.trans_le hRge
  have hPlt : P < T := (Nat.div_lt_iff_lt_mul (by decide : 0<10)).mpr (by rwa [Nat.mul_comm])
  have tLower : T ≤ a*T := by simpa using Nat.mul_le_mul_right T (show 1 ≤ a by omega)
  have heLeft : P ∣ a*T+B := larger_dvd hp (hPlt.trans_le
    (tLower.trans (Nat.le_add_right _ _))) hLeft
  have aLower : A ≤ 10*A+b := by
    have h : A ≤ 10*A := by simpa using Nat.mul_le_mul_right A (by decide : 1 ≤ 10)
    exact h.trans (Nat.le_add_right _ _)
  have heRight : R ∣ 10*A+b :=
    larger_dvd hRpos (hRlt.trans_le (hAge.trans aLower)) hRight.symm
  obtain ⟨g,hg⟩ := heLeft
  obtain ⟨f,hf⟩ := heRight
  have eqG : g*P = a*T+B := by rw [hg,Nat.mul_comm]
  have eqF : f*R = 10*A+b := by rw [hf,Nat.mul_comm]
  have gp : 0 < g := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h, zero_mul] at eqG
    exact (Nat.ne_of_gt (tpos.trans_le (tLower.trans (Nat.le_add_right _ _)))) eqG.symm
  have fp : 0 < f := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h, zero_mul] at eqF
    exact (Nat.ne_of_gt (qpos.trans_le (hAge.trans aLower))) eqF.symm
  have gHi : a*T+B < 10*T := digitTimesBase_lt ha10 hBlt
  rcases hAbounds with ⟨hA0,hA1⟩ | ⟨hA0,hA1⟩
  · have gBound : g < 1000 :=
      quotient_lt hPge (by rw [eqG]; omega)
    have fBound : f < 1000 :=
      quotient_lt hRge (by rw [eqF]; omega)
    have hfg := Nat.mul_lt_mul_of_lt_of_lt fBound gBound
    rcases hMiddle with ⟨u,hu⟩ | ⟨v,hv⟩
    · have H : 0<u ∧ u<10 := by
        refine ⟨?_,quotient_lt hAge ?_⟩
        · by_contra! e; simp [show u=0 by omega] at hu; omega
        · rw [Nat.mul_comm u, ← hu]
          omega
      refine ⟨⟨A,B,u,1,f,g,hexp,hap,hp,hRpos,hBge,hBlt,?_,eqG,eqF,fp,gp,
        hfg,Or.inl ⟨hA0,hA1,Or.inr ⟨rfl,H⟩,gBound⟩⟩⟩
      simpa [Nat.mul_comm] using hu
    · have H : 0<v ∧ v<10 := by
        refine ⟨?_,quotient_lt hBge ?_⟩
        · by_contra! e; simp [show v=0 by omega] at hv; omega
        · rw [Nat.mul_comm v, ← hv]
          omega
      refine ⟨⟨A,B,1,v,f,g,hexp,hap,hp,hRpos,hBge,hBlt,?_,eqG,eqF,fp,gp,
        hfg,Or.inl ⟨hA0,hA1,Or.inl ⟨rfl,H⟩,gBound⟩⟩⟩
      simpa [Nat.mul_comm] using hv.symm
  · have pBound : Q ≤ P :=
      (Nat.le_div_iff_mul_le (by decide : 0<10)).mpr (by omega)
    have gBound : g < 100 :=
      quotient_lt pBound (by rw [eqG]; omega)
    have fBound : f < 10000 :=
      quotient_lt hRge (by rw [eqF]; omega)
    have hfg := Nat.mul_lt_mul_of_lt_of_lt fBound gBound
    have hba : B ∣ A := larger_dvd (qpos.trans_le hBge) (hBlt.trans_le hA0) hMiddle.symm
    obtain ⟨v,hv⟩ := hba
    have H : 1<v ∧ v<100 := by
      refine ⟨?_,quotient_lt hBge ?_⟩
      · by_contra! e
        have h := Nat.mul_le_mul_left B e
        rw [← hv, mul_one] at h
        exact (not_le_of_gt (hBlt.trans_le hA0)) h
      · rw [Nat.mul_comm v, ← hv]
        omega
    have hA1' : A < 10^(k+1) := by simpa [T,pow_succ,Nat.mul_comm] using hA1
    refine ⟨⟨A,B,1,v,f,g,hexp,hap,hp,hRpos,hBge,hBlt,?_,eqG,eqF,fp,gp,
      hfg,Or.inr ⟨hA0,hA1',rfl,H.1,H.2,gBound⟩⟩⟩
    simpa [Nat.mul_comm] using hv.symm

end OMA.DecimalSplit


namespace OMA.DecimalSplit

private theorem center_small {n k : ℕ} (hk : 2 ≤ k) (c : Center n k) : k ≤ 8 := by
  let Q : ℕ := 10^(k-1)
  let A := c.A
  let B := c.B
  let a := A%10
  let b := B/Q
  have qt : (10:ℕ)^k = 10*Q := by
    conv_lhs => rw [show k=k-1+1 by omega, pow_succ,Nat.mul_comm]
  have qp : 0 < Q := by dsimp [Q]; positivity
  have aL : 0 < a := c.leftDigitPos
  have aH : a≤9 := by have := Nat.mod_lt A (by decide : 0<10); omega
  have bL : 0 < b := by
    have hB : Q ≤ B := c.rightLow
    change 0 < B/Q
    exact Nat.div_pos hB qp
  have bH : b≤9 := by
    have hB := c.rightHigh
    change B < 10^k at hB
    rw [qt] at hB
    have hh : B/Q<10 := (Nat.div_lt_iff_lt_mul qp).mpr hB
    exact Nat.le_of_lt_succ hh
  have uv : 0<c.u ∧ c.u≤9 ∧ 0<c.v ∧ c.v≤99 ∧ c.g<1000 := by
    rcases c.shape with ⟨_,_,(⟨hu,hv,hv'⟩ | ⟨hv,hu,hu'⟩),hg⟩ | ⟨_,_,hu,hv,hv',hg⟩ <;>
      exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  obtain ⟨uL,uH,vL,vH,gH⟩ := uv
  have left : c.g*(A/10)=10*a*Q+B := by
    have h := c.left
    change c.g*(A/10)=a*10^k+B at h
    rw [qt] at h
    calc
      c.g*(A/10) = a*(10*Q)+B := h
      _ = 10*a*Q+B := by ring
  have right : c.f*(B%Q)=10*A+b := c.right
  have intBound :=
    midpoint_bound
      (A := (A:ℤ)) (B := (B:ℤ)) (P := ((A/10 : ℕ):ℤ)) (Q := (Q:ℤ))
      (R := ((B%Q : ℕ):ℤ)) (a := (a:ℤ)) (b := (b:ℤ))
      (u := (c.u:ℤ)) (v := (c.v:ℤ)) (f := (c.f:ℤ)) (g := (c.g:ℤ))
      (by exact_mod_cast (Nat.div_add_mod A 10).symm)
      (by exact_mod_cast (show B=b*Q+B%Q by simpa [b,Nat.mul_comm] using (Nat.div_add_mod B Q).symm))
      (by exact_mod_cast c.middle) (by exact_mod_cast left) (by exact_mod_cast right)
      (by exact_mod_cast c.leftPos) (by exact_mod_cast qp)
      (by exact_mod_cast aL) (by exact_mod_cast aH) (by exact_mod_cast bL) (by exact_mod_cast bH)
      (by exact_mod_cast uL) (by exact_mod_cast uH) (by exact_mod_cast vL) (by exact_mod_cast vH)
      (by exact_mod_cast c.fpos) (by exact_mod_cast c.gpos)
      (by exact_mod_cast gH) (by exact_mod_cast c.product)
  have natBound : Q < 100000000 := by exact_mod_cast intBound
  by_contra! h
  have large : (10:ℕ)^8 ≤ Q := Nat.pow_le_pow_right (by decide) (by omega)
  omega

end OMA.DecimalSplit



namespace OMA.A384539Center

open OMA.S_oeis_a384539

private def firstPart (k u v g a : ℕ) : ℕ :=
  10 * (a * (v * 10^k + u) / (v * g - 10 * u)) + a

private def secondPart (k u v g a : ℕ) : ℕ :=
  u * firstPart k u v g a / v

private def passes (odd : Bool) (k u v g a : ℕ) : Prop :=
  let T := 10^k
  let Q := 10^(k-1)
  let A := firstPart k u v g a
  let B := secondPart k u v g a
  let n := A*T+B
  10*u < v*g →
    (v*g-10*u) ∣ a*(v*T+u) → v ∣ u*A →
    (if odd then T ≤ A ∧ A < 10^(k+1) else Q ≤ A ∧ A < T) →
    Q ≤ B → B < T → (B%Q) ∣ 10*A+B/Q → term n → n ∈ entries

private def CheckEven (k : ℕ) : Prop :=
  ∀ t : Fin 9, ∀ a : Fin 9, ∀ g : Fin 1000,
    passes false k (t.val+1) 1 g.val (a.val+1) ∧
      passes false k 1 (t.val+1) g.val (a.val+1)

private def CheckOdd (k : ℕ) : Prop :=
  ∀ t : Fin 98, ∀ a : Fin 9, ∀ g : Fin 100, passes true k 1 (t.val+2) g.val (a.val+1)

private def checkOne (odd : Bool) (k u v g a : ℕ) : Bool :=
  let T := 10^k
  let Q := 10^(k-1)
  let A := firstPart k u v g a
  let B := secondPart k u v g a
  let n := A*T+B
  let relevant := decide (10*u < v*g) && decide ((v*g-10*u) ∣ a*(v*T+u)) &&
    decide (v ∣ u*A) && decide (if odd then T ≤ A ∧ A < 10^(k+1) else Q ≤ A ∧ A < T) &&
    decide (Q ≤ B) && decide (B < T) && decide ((B%Q) ∣ 10*A+B/Q) && decide (term n)
  !relevant || decide (n ∈ entries)

private theorem checkOne_correct (odd : Bool) (k u v g a : ℕ)
    (h : checkOne odd k u v g a = true) : passes odd k u v g a := by
  unfold passes
  dsimp only
  intro hD hN hDiv hA hB hB' hR hTerm
  simpa [checkOne, hD, hN, hDiv, hA, hB, hB', hR, hTerm] using h

private def checkDigits (odd : Bool) (k u v g : ℕ) : Bool :=
  let possible := decide (10*u < v*g) && decide ((v*g-10*u) ∣ 2520*(v*10^k+u))
  !possible || (List.range 9).all fun a => checkOne odd k u v g (a+1)

private theorem digit_dvd : ∀ i : Fin 9, i.val + 1 ∣ 2520 := by decide +kernel

private theorem checkDigits_correct (odd : Bool) (k u v g : ℕ) (a : Fin 9)
    (h : checkDigits odd k u v g = true) : passes odd k u v g (a.val+1) := by
  intro hD hN
  have hG : (v*g-10*u) ∣ 2520*(v*10^k+u) :=
    hN.trans (Nat.mul_dvd_mul_right (digit_dvd a) (v*10^k+u))
  have hall : (List.range 9).all (fun j => checkOne odd k u v g (j+1)) = true := by
    simpa only [checkDigits, hD, hG, decide_true, Bool.true_and, Bool.not_true, Bool.false_or] using h
  have hOne := List.all_eq_true.mp hall a.val (List.mem_range.mpr a.isLt)
  exact checkOne_correct _ _ _ _ _ _ hOne hD hN

private def runEven (k : ℕ) : Bool :=
  (List.range 9).all fun t => (List.range 1000).all fun g =>
    checkDigits false k (t+1) 1 g && checkDigits false k 1 (t+1) g

private def runOdd (k : ℕ) : Bool :=
  (List.range 98).all fun t => (List.range 100).all fun g =>
    checkDigits true k 1 (t+2) g

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem evenChecked (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8) : CheckEven k := by
  have h : runEven k = true := by
    interval_cases k <;> decide +kernel
  intro t a g
  have ht := List.all_eq_true.mp h t.val (List.mem_range.mpr t.isLt)
  have hg := List.all_eq_true.mp ht g.val (List.mem_range.mpr g.isLt)
  have both := Bool.and_eq_true_iff.mp hg
  exact ⟨checkDigits_correct _ _ _ _ _ a both.1, checkDigits_correct _ _ _ _ _ a both.2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
private theorem oddChecked (k : ℕ) (hk : 2 ≤ k) (hk' : k ≤ 8) : CheckOdd k := by
  have h : runOdd k = true := by
    interval_cases k <;> decide +kernel
  intro t a g
  have ht := List.all_eq_true.mp h t.val (List.mem_range.mpr t.isLt)
  have hg := List.all_eq_true.mp ht g.val (List.mem_range.mpr g.isLt)
  exact checkDigits_correct _ _ _ _ _ a hg

theorem entries_sound : ∀ n ∈ entries, term n := by decide +kernel

theorem entries_nodup : entries.Nodup := by decide +kernel

theorem entries_length : entries.length = 132 := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 20000 in
theorem small_complete {n : ℕ} (hn : n < 1000) (hterm : term n) : n ∈ entries := by
  have h : ∀ i : Fin 1000, term i.val → i.val ∈ entries := by decide +kernel
  exact h ⟨n, hn⟩ hterm

theorem centered_complete {k n A B u v g a : ℕ}
    (hk : 2 ≤ k) (hk' : k ≤ 8) (hn : n = A*10^k+B)
    (haEq : a = A%10) (ha : 0 < a) (_ha' : a < 10)
    (hc : v*B = u*A) (hg : g*(A/10) = a*10^k+B)
    (hr : B%10^(k-1) ∣ 10*A+B/10^(k-1))
    (hB : 10^(k-1) ≤ B) (hB' : B < 10^k)
    (hbnds : (10^(k-1) ≤ A ∧ A < 10^k ∧
        ((u=1 ∧ 0<v ∧ v<10) ∨ (v=1 ∧ 0<u ∧ u<10)) ∧ g<1000) ∨
      (10^k ≤ A ∧ A < 10^(k+1) ∧ u=1 ∧ 1<v ∧ v<100 ∧ g<100))
    (hterm : term n) : n ∈ entries := by
  have hv : 0 < v := by
    rcases hbnds with ⟨_, _, h, _⟩ | ⟨_, _, _, h, _, _⟩
    · rcases h with ⟨_, h, _⟩ | ⟨rfl, _, _⟩ <;> omega
    · omega
  have hA : A = 10 * (A/10) + a := by
    rw [haEq]
    exact (Nat.div_add_mod A 10).symm
  have hbal : (v*g)*(A/10) = (10*u)*(A/10) + a*(v*10^k+u) := by
    calc
      (v*g)*(A/10) = v*(g*(A/10)) := by ring
      _ = v*(a*10^k+B) := by rw [hg]
      _ = v*(a*10^k) + u*A := by rw [mul_add, hc]
      _ = (10*u)*(A/10) + a*(v*10^k+u) := by
        nth_rw 1 [hA]
        ring
  have hm : 0 < a*(v*10^k+u) := by positivity
  have hD : 10*u < v*g := by
    by_contra! h
    have hh := Nat.mul_le_mul_right (A/10) h
    omega
  have hcalc : (v*g-10*u)*(A/10) = a*(v*10^k+u) := by
    rw [Nat.sub_mul, hbal]
    omega
  have hFirst : firstPart k u v g a = A := by
    unfold firstPart
    rw [← hcalc, Nat.mul_div_cancel_left _ (by omega : 0 < v*g-10*u)]
    exact hA.symm
  have hSecond : secondPart k u v g a = B := by
    unfold secondPart
    rw [hFirst, ← hc, Nat.mul_div_cancel_left _ hv]
  have hApply (odd : Bool)
      (hcheck : passes odd k u v g a)
      (hSize : if odd then 10^k ≤ A ∧ A < 10^(k+1) else 10^(k-1) ≤ A ∧ A < 10^k) :
      n ∈ entries := by
    unfold passes at hcheck
    simp only [hFirst, hSecond, ← hn] at hcheck
    exact hcheck hD ⟨A/10, hcalc.symm⟩ ⟨B, hc.symm⟩ hSize hB hB' hr hterm
  let aa : Fin 9 := ⟨a-1, by omega⟩
  have ha0 : aa.val+1 = a := by dsimp [aa]; omega
  rcases hbnds with ⟨hAmin, hAmax, hSides, hgmax⟩ | ⟨hAmin, hAmax, rfl, hvmin, hvmax, hgmax⟩
  · let gg : Fin 1000 := ⟨g, hgmax⟩
    rcases hSides with ⟨rfl, _, hvmax⟩ | ⟨rfl, humin, humax⟩
    · let vv : Fin 9 := ⟨v-1, by omega⟩
      have hv0 : vv.val+1 = v := by dsimp [vv]; omega
      have h := (evenChecked k hk hk' vv aa gg).2
      rw [ha0, hv0] at h
      exact hApply false h ⟨hAmin, hAmax⟩
    · let uu : Fin 9 := ⟨u-1, by omega⟩
      have hu0 : uu.val+1 = u := by dsimp [uu]; omega
      have h := (evenChecked k hk hk' uu aa gg).1
      rw [ha0, hu0] at h
      exact hApply false h ⟨hAmin, hAmax⟩
  · let gg : Fin 100 := ⟨g, hgmax⟩
    let vv : Fin 98 := ⟨v-2, by omega⟩
    have hv0 : vv.val+2 = v := by dsimp [vv]; omega
    have h := oddChecked k hk hk' vv aa gg
    rw [ha0, hv0] at h
    exact hApply true h ⟨hAmin, hAmax⟩

end OMA.A384539Center


namespace OMA.DecimalSplit

open OMA.S_oeis_a384539 OMA.A384539Center

private theorem complete {n : ℕ} (hterm : term n) : n ∈ entries := by
  by_cases small : n < 1000
  · exact small_complete small hterm
  have hlog : 3 ≤ Nat.log 10 n :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 10) (by omega : n ≠ 0)).mpr (by omega)
  let k := (Nat.log 10 n+1)/2
  have hk : 2 ≤ k := by omega
  have hl : Nat.log 10 n+1 = 2*k ∨ Nat.log 10 n+1 = 2*k+1 := by omega
  obtain ⟨c⟩ := extract_center hk hl hterm
  have kbound := center_small hk c
  have hr : c.B % 10^(k-1) ∣ 10*c.A+c.B/10^(k-1) :=
    ⟨c.f, by rw [← c.right, Nat.mul_comm]⟩
  exact centered_complete hk kbound c.expansion rfl c.leftDigitPos
    (Nat.mod_lt _ (by decide)) c.middle c.left hr c.rightLow c.rightHigh c.shape hterm

end OMA.DecimalSplit

theorem OMA.solution : type_of% @OMA.S_oeis_a384539.main := by
  exact ⟨fun n => ⟨OMA.DecimalSplit.complete, OMA.A384539Center.entries_sound n⟩,
    OMA.A384539Center.entries_nodup, OMA.A384539Center.entries_length⟩
