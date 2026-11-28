import OMAStatements.S_oeis_a256587

/-!
# Square shells for the two universality questions of A256587

The odd square attached to an element of S leaves remainder 1 or 9 modulo 16.
The mixed shell for a binary sum has no congruence restrictions on its
representations by two squares. Its existence can thus be tested by factoring.
For r+3t, rotations of u²+3v² let an unrestricted norm representation
supply the required square residues. For an odd median, the adjacent values
of S give a window in which every binary decomposition straddles the median.
The converse at the end proves the three remaining conditions are necessary.
The side lemmas establish local solubility at odd primes and powers of two. The finite base below is
computed by shifts and unions, with a witness-extraction proof for each union.
-/
-- Credit: @Pixelstorm44

namespace OMA.R_oeis_a256587_R1
open OMA.S_oeis_a256587 Polynomial

theorem term_mem :
  let term (i : ℕ) := (i+1)*(i+2)/4
  ∀ (i : ℕ),
  term i ∈ S := by
  intro term i
  exact ⟨i+1, by omega, rfl⟩

theorem term_mono :
  let term (i : ℕ) := (i+1)*(i+2)/4
  Monotone term := by
  intro term
  exact fun i j h => Nat.div_le_div_right (Nat.mul_le_mul (by omega) (by omega))

theorem fromUnion (l : List ℕ) (f : ℕ → ℕ) (n : ℕ)
    (h : (l.foldr (fun i acc => f i ||| acc) 0).testBit n = true) :
    ∃ i ∈ l, (f i).testBit n = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with ha | hl
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨i,hi,hb⟩ := ih hl
      exact ⟨i, List.mem_cons_of_mem a hi, hb⟩

theorem fromLayer :
  let layer (count : ℕ) (shift : ℕ → ℕ) (seed : ℕ) :=
    (List.range count).foldr (fun i acc => (seed <<< shift i) ||| acc) 0
  ∀ {count seed n : ℕ} {f : ℕ → ℕ} (_h : (layer count f seed).testBit n = true),
  ∃ i < count, f i ≤ n ∧ seed.testBit (n-f i) = true := by
  intro layer count seed n f h
  obtain ⟨i,hi,hb⟩ := fromUnion _ _ _ h
  simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact ⟨i,List.mem_range.mp hi,hb⟩

theorem lastBit {n : ℕ} (h : (1:ℕ).testBit n = true) : n = 0 := by
  have e := Nat.testBit_two_pow_sub_one 1 n
  change (1:ℕ).testBit n = _ at e
  rw [e, decide_eq_true_eq] at h
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem smallWeighted :
  let pairs : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,2),(2,3)}
  let weighted (b c n : ℕ) := ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, n = r+b*s+c*t
  ∀ {bc : ℕ × ℕ} (_hp : bc ∈ pairs) {n : ℕ} (_hn : n ≤ 4096),
  weighted bc.1 bc.2 n := by
  intro pairs weighted bc hp n hn
  let term (i : ℕ) := (i+1)*(i+2)/4
  let layer (count : ℕ) (shift : ℕ → ℕ) (seed : ℕ) :=
    (List.range count).foldr (fun i acc => (seed <<< shift i) ||| acc) 0
  let v := layer 128 (fun i => bc.2 * term i)
    (layer 128 (fun j => bc.1 * term j) (layer 128 term 1))
  have allBits : v % 2^4097 = 2^4097-1 := by
    simp only [pairs, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  have h := congrArg (fun k : ℕ => k.testBit n) allBits
  simp [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, show n < 4097 by omega] at h
  obtain ⟨i,_,hi,h⟩ := fromLayer h
  obtain ⟨j,_,hj,h⟩ := fromLayer h
  obtain ⟨k,_,hk,h⟩ := fromLayer h
  have e := lastBit h
  exact ⟨_,term_mem k,_,term_mem j,_,term_mem i,by simp only [term] at *; omega⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem smallOrdered :
  let ordered (n : ℕ) :=
    ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, Odd s ∧ r ≤ s ∧ s ≤ t ∧ n = r+s+t
  ∀ {n : ℕ} (_hn : 1 < n) (_hb : n ≤ 4096),
  ordered n := by
  intro ordered n hn hb
  let term (i : ℕ) := (i+1)*(i+2)/4
  let layer (count : ℕ) (shift : ℕ → ℕ) (seed : ℕ) :=
    (List.range count).foldr (fun i acc => (seed <<< shift i) ||| acc) 0
  let middleBits (j : ℕ) :=
    if term j % 2 = 1 then
      (layer (j+1) term (layer (128-j) (fun k => term (j+k)) 1)) <<< term j
    else 0
  let v := (List.range 128).foldr (fun j acc => middleBits j ||| acc) 0
  have allBits : (v ||| 3) % 2^4097 = 2^4097-1 := by decide +kernel
  have h := congrArg (fun k : ℕ => k.testBit n) allBits
  have low := Nat.testBit_two_pow_sub_one 2 n
  change (3:ℕ).testBit n = _ at low
  simp [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one, show n < 4097 by omega,
    low, show ¬ n < 2 by omega] at h
  obtain ⟨j,_,hj⟩ := fromUnion _ _ _ h
  unfold middleBits at hj
  split at hj
  next ho =>
    simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hj
    obtain ⟨i,hi,hir,h'⟩ := fromLayer hj.2
    obtain ⟨k,_,hkr,h''⟩ := fromLayer h'
    have e := lastBit h''
    exact ⟨_,term_mem i,_,term_mem j,_,term_mem (j+k),by exact ⟨term j / 2, by simp only [term] at *; omega⟩,
      term_mono (by simp only [term] at *; omega),term_mono (by simp only [term] at *; omega),by simp only [term] at *; omega⟩
  next => simp at hj


theorem squareResidue (x : ℕ) :
    x^2%16 = 0 ∨ x^2%16 = 1 ∨ x^2%16 = 4 ∨ x^2%16 = 9 := by
  rw [Nat.pow_mod]
  have h := Nat.mod_lt x (by decide : 0 < 16)
  interval_cases x%16 <;> decide

theorem floorSquare {x : ℕ} (h : x^2%16 = 1 ∨ x^2%16 = 9) : x^2/16 ∈ S := by
  have oddx : x%2 = 1 := by
    have e := Nat.pow_mod x 2 2
    have e' : x%2 < 2 := Nat.mod_lt _ (by decide)
    by_contra! h'
    have z : x%2 = 0 := by omega
    rw [z] at e
    norm_num at e
    omega
  let k := x/2
  have ex : x = 2*k + 1 := by dsimp [k]; omega
  by_cases h0 : k = 0
  · have : x = 1 := by omega
    rw [this]
    exact ⟨1,by decide,by decide⟩
  refine ⟨k,by omega,?_⟩
  have eq : x^2 = 4*(k*(k+1))+1 := by rw [ex]; ring
  omega

theorem mixed :
  let factorTest (m : ℕ) : Prop :=
    ∀ q ∈ (16*m+10).primeFactors, q%4 = 3 → Even (padicValNat q (16*m+10))
  ∀ {m : ℕ} (_h : factorTest m),
  ∃ r ∈ S, ∃ s ∈ S, m = r+s := by
  intro factorTest m h
  obtain ⟨x,y,e⟩ := Nat.eq_sq_add_sq_iff.mpr h
  have hx := squareResidue x
  have hy := squareResidue y
  have hr : x^2%16 = 1 ∨ x^2%16 = 9 := by omega
  have hs : y^2%16 = 1 ∨ y^2%16 = 9 := by omega
  exact ⟨_,floorSquare hr,_,floorSquare hs,by omega⟩

-- The four shells of r+3t; depending on m, a rotation gives both orientations.
theorem rotateResidues :
  let normTarget (m M : ℕ) : Prop :=
    (m%2=0 ∧ M=4*m+7) ∨ (m%2=1 ∧ (M=4*m+1 ∨ M=4*m+3 ∨ M=4*m+9))
  ∀ (u v : ℤ) {m M : ℕ} (_hM : normTarget m M)
    (_h : u^2+3*v^2=(M:ℤ)),
  ∃ a b : ℤ, a^2+3*b^2=4*(M:ℤ) ∧
      (a^2%16=1 ∨ a^2%16=9) ∧ (b^2%16=1 ∨ b^2%16=9) ∧
      a^2%16+3*(b^2%16)=4*(M:ℤ)-16*(m:ℤ) := by
  intro normTarget u v m M hM h
  let A := u+3*v
  let B := u-v
  let C := u-3*v
  let D := u+v
  have left : A^2+3*B^2=4*(M:ℤ) := by dsimp [A,B]; rw [← h]; ring
  have right : C^2+3*D^2=4*(M:ℤ) := by dsimp [C,D]; rw [← h]; ring
  let f (a b : ℤ) (d : ℤ) := (a^2%16=1 ∨ a^2%16=9) ∧
    (b^2%16=1 ∨ b^2%16=9) ∧ a^2%16+3*(b^2%16)=d
  have table : ∀ i j : Fin 16, ∀ d : Fin 37,
      (((i:ℤ)^2+3*(j:ℤ)^2)%8=5 ∧ (d.val=4 ∨ d.val=36)) ∨
      (((i:ℤ)^2+3*(j:ℤ)^2)%8=7 ∧ (d.val=12 ∨ d.val=28)) →
      f ((i:ℤ)+3*j) ((i:ℤ)-j) d.val ∨ f ((i:ℤ)-3*j) ((i:ℤ)+j) d.val := by
    decide +kernel
  let i : Fin 16 := ⟨(u%16).toNat, by omega⟩
  let j : Fin 16 := ⟨(v%16).toNat, by omega⟩
  have hi : (i:ℤ) ≡ u [ZMOD 16] := by change ((u%16).toNat:ℤ)%16 = u%16; omega
  have hj : (j:ℤ) ≡ v [ZMOD 16] := by change ((v%16).toNat:ℤ)%16 = v%16; omega
  have h8 : (i:ℤ)^2+3*(j:ℤ)^2 ≡ (M:ℤ) [ZMOD 8] := by
    rw [← h]
    exact ((hi.pow 2).add ((hj.pow 2).mul_left 3)).of_dvd (by decide)
  change _%8 = (M:ℤ)%8 at h8
  let d : Fin 37 := ⟨4*M-16*m, by rcases hM with ⟨_,rfl⟩|⟨_,h⟩ <;> omega⟩
  have hd : (d.val:ℤ) = 4*(M:ℤ)-16*(m:ℤ) := by
    change ((4*M-16*m:ℕ):ℤ) = _
    rcases hM with ⟨_,rfl⟩|⟨_,h⟩ <;> omega
  have cond : (((i:ℤ)^2+3*(j:ℤ)^2)%8=5 ∧ (d.val=4 ∨ d.val=36)) ∨
      (((i:ℤ)^2+3*(j:ℤ)^2)%8=7 ∧ (d.val=12 ∨ d.val=28)) := by
    rw [h8]
    rcases hM with ⟨_,rfl⟩|⟨_,h⟩ <;> omega
  have aux {a b a' b' : ℤ} (ha : a ≡ a' [ZMOD 16]) (hb : b ≡ b' [ZMOD 16]) :
      f a b d.val → f a' b' d.val := by
    unfold f
    rw [show a^2%16=a'^2%16 from ha.pow 2,show b^2%16=b'^2%16 from hb.pow 2]
    exact id
  rcases table i j d cond with hl|hr
  · refine ⟨A,B,left,?_⟩
    rw [← hd]
    exact aux (hi.add (hj.mul_left 3)) (hi.sub hj) hl
  · refine ⟨C,D,right,?_⟩
    rw [← hd]
    exact aux (hi.sub (hj.mul_left 3)) (hi.add hj) hr

theorem rotatedPair :
  let normTarget (m M : ℕ) : Prop :=
    (m%2=0 ∧ M=4*m+7) ∨ (m%2=1 ∧ (M=4*m+1 ∨ M=4*m+3 ∨ M=4*m+9))
  ∀ {m M : ℕ} (_hd : normTarget m M)
    {u v : ℤ} (_h : u^2+3*v^2=(M:ℤ)),
  ∃ r ∈ S, ∃ t ∈ S, m = r+3*t := by
  intro normTarget m M hd u v h
  obtain ⟨a,b,e,ha,hb,hs⟩ := rotateResidues u v hd h
  have ea : (a.natAbs^2:ℕ) = (a^2).natAbs := by simp
  have eb : (b.natAbs^2:ℕ) = (b^2).natAbs := by simp
  have ca : ((a.natAbs^2:ℕ):ℤ) = a^2 := by rw [ea,Int.natCast_natAbs,abs_of_nonneg (sq_nonneg _)]
  have cb : ((b.natAbs^2:ℕ):ℤ) = b^2 := by rw [eb,Int.natCast_natAbs,abs_of_nonneg (sq_nonneg _)]
  have ra : a.natAbs^2%16=1 ∨ a.natAbs^2%16=9 := by omega
  have rb : b.natAbs^2%16=1 ∨ b.natAbs^2%16=9 := by omega
  exact ⟨_,floorSquare ra,_,floorSquare rb,by omega⟩



theorem branch (p : ℕ) [NeZero p] (x : ZMod p) (L : ℕ) :
    ∃ w ∈ S, L ≤ w ∧ (w : ZMod p) = x*(4*x+1) := by
  let u := x.val + (L+1)*p
  have hu : L < u := by
    have := Nat.le_mul_of_pos_right (L+1) (NeZero.pos p)
    dsimp [u]; omega
  have castu : (u : ZMod p) = x := by simp [u]
  refine ⟨u*(4*u+1),⟨4*u,by omega,?_⟩,?_,?_⟩
  · have eq : 4*u*(4*u+1)=4*(u*(4*u+1)) := by ring
    rw [eq]; omega
  · exact le_trans hu.le (Nat.le_mul_of_pos_right _ (by omega))
  · push_cast
    rw [castu]

/-- Over every odd prime field the first two terms already cover the field
for either value of b in the conjecture. Lower bounds on either term are free. -/
theorem atOddPrime (p : ℕ) [hp : Fact p.Prime] (hodd : p%2=1)
    (b z : ZMod p) (hb : b≠0) (L : ℕ) :
    ∃ r ∈ S, ∃ s ∈ S, L ≤ r ∧ L ≤ s ∧ (r:ZMod p)+b*s=z := by
  have htwo : (2:ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have hle := Nat.le_of_dvd (by decide : 0<2) hd
    have := hp.out.two_le
    omega
  have hfour : (4:ZMod p) ≠ 0 := by
    rw [show (4:ZMod p)=2*2 by ring]
    exact mul_ne_zero htwo htwo
  let f : (ZMod p)[X] := C 4*X^2+C 1*X+C 0
  let g : (ZMod p)[X] := C (4*b)*X^2+C b*X+C (-z)
  obtain ⟨x,y,hxy⟩ := FiniteField.exists_root_sum_quadratic
    (f:=f) (g:=g) (degree_quadratic hfour) (degree_quadratic (mul_ne_zero hfour hb))
    (by simpa only [ZMod.card] using hodd)
  obtain ⟨r,hr,hl,er⟩ := branch p x L
  obtain ⟨s,hs,hl',es⟩ := branch p y L
  refine ⟨r,hr,s,hs,hl,hl',?_⟩
  rw [er,es]
  simp [f,g] at hxy
  linear_combination hxy

/-- The branch k=4u is a permutation polynomial at every power of two.
The parameter in the resulting integer representation may be taken arbitrarily large. -/
theorem dyadic (e L : ℕ) (z : ZMod (2^e)) :
    ∃ w ∈ S, L ≤ w ∧ (w : ZMod (2^e)) = z := by
  let f (x : ZMod (2^e)) := x*(4*x+1)
  have hinj : Function.Injective f := by
    intro x y h
    have hz : (x-y)*(1+2*(2*(x+y)))=0 := by
      unfold f at h
      linear_combination h
    have hn : IsNilpotent (2*(2*(x+y))) := by
      refine ⟨e,?_⟩
      rw [mul_pow, show (2:ZMod (2^e))^e = 0 by exact_mod_cast (ZMod.natCast_self (2^e)), zero_mul]
    exact sub_eq_zero.mp (hn.isUnit_one_add.mul_left_inj.mp (by simpa using hz))
  obtain ⟨x,hx⟩ := (Finite.injective_iff_surjective.mp hinj) z
  let u := x.val + (L+1)*2^e
  have hu : L < u := by
    have := Nat.le_mul_of_pos_right (L+1) (pow_pos (by decide : 0<2) e)
    dsimp [u]; omega
  have castu : (u : ZMod (2^e)) = x := by simp [u]
  refine ⟨u*(4*u+1),⟨4*u,by omega,?_⟩,?_,?_⟩
  · have eq : 4*u*(4*u+1)=4*(u*(4*u+1)) := by ring
    rw [eq]; omega
  · exact le_trans hu.le (Nat.le_mul_of_pos_right _ (by omega))
  · push_cast
    simpa [castu,f] using hx

/-- A square root certificate involving a single free coordinate. The other
coordinate is the square root of the residual. The bounds specify its position
relative to an odd median, or are vacuous in the weighted applications. -/
theorem fromShell :
  let shell (b m p q cap lower : ℕ) : Prop :=
    ∃ y : ℕ, let rest := 16*m+p+b*q-b*y^2
      b*y^2 ≤ 16*m+p+b*q ∧ y^2%16=q ∧ IsSquare rest ∧
        rest%16=p ∧ rest/16 ≤ cap ∧ lower ≤ y^2/16
  ∀ {b m p q cap lower : ℕ} (_hp : p=1 ∨ p=9) (_hq : q=1 ∨ q=9)
    (_h : shell b m p q cap lower),
  ∃ r ∈ S, ∃ t ∈ S, m=r+b*t ∧ r≤cap ∧ lower≤t := by
  intro shell b m p q cap lower hp hq h
  obtain ⟨y,hle,hy,⟨x,hx⟩,hres,hcap,hlo⟩ := h
  rw [← sq] at hx
  have he : x^2+b*y^2=16*m+p+b*q := by omega
  have hxx : x^2%16=p := hx ▸ hres
  have step := congrArg (fun z : ℕ => b*z) (Nat.div_add_mod (y^2) 16)
  simp only [hy, Nat.mul_add] at step
  have equation : 16*(x^2/16)+(x^2%16)+ (16*(b*(y^2/16))+b*q) = 16*m+p+b*q := by
    rw [Nat.div_add_mod, ← he]
    congr 1
    simpa only [Nat.mul_left_comm b 16] using step
  rw [hxx] at equation
  exact ⟨_,floorSquare (hxx ▸ hp),_,floorSquare (hy ▸ hq),by omega,by simpa [hx] using hcap,hlo⟩

theorem index_of_mem :
  let term (i : ℕ) := (i+1)*(i+2)/4
  ∀ {w : ℕ} (_h : w ∈ S),
  ∃ i, w = term i := by
  intro term w h
  obtain ⟨k,hk,h⟩ := h
  obtain ⟨i,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  exact ⟨i,h⟩

theorem orderOfScreen :
  let term (i : ℕ) := (i+1)*(i+2)/4
  let ordered (n : ℕ) :=
    ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, Odd s ∧ r ≤ s ∧ s ≤ t ∧ n = r+s+t
  let factorTest (m : ℕ) : Prop :=
    ∀ q ∈ (16*m+10).primeFactors, q%4 = 3 → Even (padicValNat q (16*m+10))
  let medianScreen (n : ℕ) : Prop :=
    ∃ j m : ℕ, Odd (term (j+1)) ∧ n=term (j+1)+m ∧
      2*term j < m ∧ m < 2*term (j+2) ∧ factorTest m
  ∀ {n : ℕ} (_h : medianScreen n),
  ordered n := by
  intro term ordered factorTest medianScreen n h
  obtain ⟨j,m,ho,hn,hl,hu,hm⟩ := h
  obtain ⟨r,hr,t,ht,he⟩ := mixed hm
  obtain ⟨i,rfl⟩ := index_of_mem hr
  obtain ⟨k,rfl⟩ := index_of_mem ht
  have sort {i k : ℕ} (hik : i ≤ k) (hsum : m=term i+term k) :
      term i ≤ term (j+1) ∧ term (j+1) ≤ term k := by
    constructor
    · by_contra! h'
      have hi : j+2 ≤ i := by
        by_contra! hi
        exact (not_le_of_gt h') (term_mono (by omega))
      have := term_mono hi
      have := term_mono hik
      simp only [term] at *; omega
    · by_contra! h'
      have hk : k ≤ j := by
        by_contra! hk
        exact (not_le_of_gt h') (term_mono (by omega))
      have := term_mono hk
      have := term_mono hik
      simp only [term] at *; omega
  rcases le_total i k with hik|hki
  · obtain ⟨h1,h2⟩ := sort hik he
    exact ⟨_,hr,_,term_mem _,_,ht,ho,h1,h2,by simp only [term] at *; omega⟩
  · obtain ⟨h1,h2⟩ := sort hki (by simp only [term] at *; omega)
    exact ⟨_,ht,_,term_mem _,_,hr,ho,h1,h2,by simp only [term] at *; omega⟩

/-- Remaining angular problem for a binary circle, after the nearest-neighbor sieve. -/
def H1 : Prop :=
  let term (i : ℕ) := (i+1)*(i+2)/4
  let factorTest (m : ℕ) : Prop :=
    ∀ q ∈ (16*m+10).primeFactors, q%4 = 3 → Even (padicValNat q (16*m+10))
  let shell (b m p q cap lower : ℕ) : Prop :=
    ∃ y : ℕ, let rest := 16*m+p+b*q-b*y^2
      b*y^2 ≤ 16*m+p+b*q ∧ y^2%16=q ∧ IsSquare rest ∧
        rest%16=p ∧ rest/16 ≤ cap ∧ lower ≤ y^2/16
  let medianScreen (n : ℕ) : Prop :=
    ∃ j m : ℕ, Odd (term (j+1)) ∧ n=term (j+1)+m ∧
      2*term j < m ∧ m < 2*term (j+2) ∧ factorTest m
  ∀ n : ℕ, 4096<n → ¬medianScreen n →
  ∃ j m p q : ℕ, Odd (term j) ∧ n=term j+m ∧ (p=1 ∨ p=9) ∧ (q=1 ∨ q=9) ∧
    shell 1 m p q (term j) (term j)

/-- In the eight equal-weight families only the two monochromatic circles are
needed once all mixed circles have failed the prime-factor test. -/
def H2 : Prop :=
  let term (i : ℕ) := (i+1)*(i+2)/4
  let factorTest (m : ℕ) : Prop :=
    ∀ q ∈ (16*m+10).primeFactors, q%4 = 3 → Even (padicValNat q (16*m+10))
  let shell (b m p q cap lower : ℕ) : Prop :=
    ∃ y : ℕ, let rest := 16*m+p+b*q-b*y^2
      b*y^2 ≤ 16*m+p+b*q ∧ y^2%16=q ∧ IsSquare rest ∧
        rest%16=p ∧ rest/16 ≤ cap ∧ lower ≤ y^2/16
  let equalWeights : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,1)}
  let equalScreen (a d n : ℕ) : Prop :=
    ∃ i m : ℕ, n=a*m+d*term i ∧ factorTest m
  ∀ ad ∈ equalWeights, ∀ n : ℕ, 4096<n → ¬equalScreen ad.1 ad.2 n →
  ∃ i m p : ℕ, n=ad.1*m+ad.2*term i ∧ (p=1 ∨ p=9) ∧ shell 1 m p p m 0

/-- Exceptional set for the rotations of the form x² + 3y². -/
def H3 : Prop :=
  let term (i : ℕ) := (i+1)*(i+2)/4
  let normTarget (m M : ℕ) : Prop :=
    (m%2=0 ∧ M=4*m+7) ∨ (m%2=1 ∧ (M=4*m+1 ∨ M=4*m+3 ∨ M=4*m+9))
  let shell (b m p q cap lower : ℕ) : Prop :=
    ∃ y : ℕ, let rest := 16*m+p+b*q-b*y^2
      b*y^2 ≤ 16*m+p+b*q ∧ y^2%16=q ∧ IsSquare rest ∧
        rest%16=p ∧ rest/16 ≤ cap ∧ lower ≤ y^2/16
  let normScreen (n : ℕ) : Prop :=
    ∃ i m M : ℕ, n=m+2*term i ∧ normTarget m M ∧ ∃ u v : ℤ, u^2+3*v^2=(M:ℤ)
  ∀ n : ℕ, 4096<n → ¬normScreen n →
  ∃ i m p q : ℕ, n=m+2*term i ∧ (p=1 ∨ p=9) ∧ (q=1 ∨ q=9) ∧ shell 3 m p q m 0

theorem equalCase :
  let equalWeights : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,1)}
  ∀ (_h2 : H2) {a d n : ℕ} (_ha : (a,d) ∈ equalWeights) (_hn : 4096<n),
  ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, n=a*(r+s)+d*t := by
  intro equalWeights h2 a d n ha hn
  let term (i : ℕ) := (i+1)*(i+2)/4
  let factorTest (m : ℕ) : Prop :=
    ∀ q ∈ (16*m+10).primeFactors, q%4 = 3 → Even (padicValNat q (16*m+10))
  let equalScreen (a d n : ℕ) : Prop :=
    ∃ i m : ℕ, n=a*m+d*term i ∧ factorTest m
  by_cases h : equalScreen a d n
  · obtain ⟨i,m,he,hm⟩ := h
    obtain ⟨r,hr,s,hs,hp⟩ := mixed hm
    exact ⟨r,hr,s,hs,_,term_mem i,hp ▸ he⟩
  · obtain ⟨i,m,p,he,hp,hc⟩ := h2 (a,d) ha n hn h
    obtain ⟨r,hr,s,hs,hm,_,_⟩ := fromShell hp hp hc
    simp only [one_mul] at hm
    exact ⟨r,hr,s,hs,_,term_mem i,hm ▸ he⟩

theorem main : H1 → H2 → H3 → type_of% @OMA.S_oeis_a256587.main := by
  let term (i : ℕ) := (i+1)*(i+2)/4
  let pairs : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,2),(2,3)}
  let factorTest (m : ℕ) : Prop :=
    ∀ q ∈ (16*m+10).primeFactors, q%4 = 3 → Even (padicValNat q (16*m+10))
  let normTarget (m M : ℕ) : Prop :=
    (m%2=0 ∧ M=4*m+7) ∨ (m%2=1 ∧ (M=4*m+1 ∨ M=4*m+3 ∨ M=4*m+9))
  let medianScreen (n : ℕ) : Prop :=
    ∃ j m : ℕ, Odd (term (j+1)) ∧ n=term (j+1)+m ∧
      2*term j < m ∧ m < 2*term (j+2) ∧ factorTest m
  let equalWeights : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,1)}
  let normScreen (n : ℕ) : Prop :=
    ∃ i m M : ℕ, n=m+2*term i ∧ normTarget m M ∧ ∃ u v : ℤ, u^2+3*v^2=(M:ℤ)
  intro h1 h2 h3
  constructor
  · intro n hn
    by_cases hb : n ≤ 4096
    · exact smallOrdered hn hb
    by_cases h : medianScreen n
    · exact orderOfScreen h
    obtain ⟨j,m,p,q,ho,he,hp,hq,hc⟩ := h1 n (by omega) h
    obtain ⟨r,hr,t,ht,hm,hl,hu⟩ := fromShell hp hq hc
    simp only [one_mul] at hm
    exact ⟨r,hr,_,term_mem j,t,ht,ho,hl,hu,by omega⟩
  · intro bc hbc n
    change bc ∈ pairs at hbc
    by_cases hb : n ≤ 4096
    · exact smallWeighted hbc hb
    have hn : 4096<n := by omega
    rcases bc with ⟨b,c⟩
    by_cases hb1 : b=1
    · subst b
      have heq : (1,c) ∈ equalWeights := by
        simp [pairs, equalWeights] at hbc ⊢
        tauto
      obtain ⟨r,hr,s,hs,t,ht,he⟩ := equalCase h2 heq hn
      exact ⟨r,hr,s,hs,t,ht,by simpa using he⟩
    have hbc' : (b=2 ∧ c=2) ∨ (b=2 ∧ c=3) := by
      simp only [pairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hbc
      omega
    rcases hbc' with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · obtain ⟨s,hs,t,ht,r,hr,he⟩ := equalCase h2 (show (2,1) ∈ equalWeights by decide) hn
      exact ⟨r,hr,s,hs,t,ht,by dsimp; omega⟩
    · by_cases h : normScreen n
      · obtain ⟨i,m,M,he,hd,u,v,hu⟩ := h
        obtain ⟨r,hr,t,ht,hm⟩ := rotatedPair hd hu
        exact ⟨r,hr,_,term_mem i,t,ht,by dsimp; simp only [term] at *; omega⟩
      · obtain ⟨i,m,p,q,he,hp,hq,hc⟩ := h3 n hn h
        obtain ⟨r,hr,t,ht,hm,_,_⟩ := fromShell hp hq hc
        exact ⟨r,hr,_,term_mem i,t,ht,by dsimp; simp only at *; omega⟩


theorem liftOfMem {s : ℕ} (hs : s ∈ S) :
    ∃ x p : ℕ, (p=1 ∨ p=9) ∧ x^2=16*s+p := by
  obtain ⟨k,_,rfl⟩ := hs
  have eq : (2*k+1)^2=4*(k*(k+1))+1 := by ring
  have evenProd : (k*(k+1))%2=0 := by
    rw [Nat.mul_mod, Nat.add_mod]
    have h := Nat.mod_lt k (by decide : 0<2)
    interval_cases k%2 <;> decide
  refine ⟨2*k+1,(2*k+1)^2%16,by omega,by omega⟩

theorem toShell :
  let shell (b m p q cap lower : ℕ) : Prop :=
    ∃ y : ℕ, let rest := 16*m+p+b*q-b*y^2
      b*y^2 ≤ 16*m+p+b*q ∧ y^2%16=q ∧ IsSquare rest ∧
        rest%16=p ∧ rest/16 ≤ cap ∧ lower ≤ y^2/16
  ∀ {r t b m cap lower x y p q : ℕ}
    (_hp : p<16) (_hq : q<16) (_hx : x^2=16*r+p) (_hy : y^2=16*t+q)
    (_he : m=r+b*t) (_hcap : r≤cap) (_hlo : lower≤t),
  shell b m p q cap lower := by
  intro shell r t b m cap lower x y p q hp hq hx hy he hcap hlo
  have total : 16*m+p+b*q=x^2+b*y^2 := by rw [he,hx,hy]; ring
  refine ⟨y,?_⟩
  dsimp only
  rw [total]
  simp only [Nat.add_sub_cancel]
  exact ⟨by omega,by omega,⟨x,by ring⟩,by omega,by omega,by omega⟩

/-- The residual conditions are necessary as well as sufficient. In particular,
the sieves may miss infinitely many integers without strengthening the conjecture. -/
theorem residualsNecessary (result : type_of% @OMA.S_oeis_a256587.main) : H1 ∧ H2 ∧ H3 := by
  let pairs : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,2),(2,3)}
  let equalWeights : Finset (ℕ × ℕ) := {(1,2),(1,3),(1,4),(1,5),(1,6),(1,8),(1,9),(2,1)}
  obtain ⟨orderedAll, weightedAll⟩ := result
  refine ⟨?_,?_,?_⟩
  · intro n hn _
    obtain ⟨r,hr,s,hs,t,ht,ho,hrs,hst,he⟩ := orderedAll n (by omega)
    obtain ⟨j,rfl⟩ := index_of_mem hs
    obtain ⟨x,p,hp,hx⟩ := liftOfMem hr
    obtain ⟨y,q,hq,hy⟩ := liftOfMem ht
    exact ⟨j,r+t,p,q,ho,by omega,hp,hq,
      toShell (by omega) (by omega) hx hy (by simp) hrs hst⟩
  · rintro ⟨a,d⟩ had n _ noMixed
    have rep : ∃ r ∈ S, ∃ s ∈ S, ∃ t ∈ S, n=a*(r+s)+d*t := by
      by_cases ha : a=1
      · subst a
        have hbc : (1,d) ∈ pairs := by
          simp [pairs] at had ⊢
          tauto
        obtain ⟨r,hr,s,hs,t,ht,he⟩ := weightedAll (1,d) hbc n
        exact ⟨r,hr,s,hs,t,ht,by simpa using he⟩
      · have eq : a=2 ∧ d=1 := by
          simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at had
          omega
        obtain ⟨rfl,rfl⟩ := eq
        obtain ⟨t,ht,r,hr,s,hs,he⟩ := weightedAll (2,2) (by decide) n
        exact ⟨r,hr,s,hs,t,ht,by dsimp at he; omega⟩
    obtain ⟨r,hr,s,hs,t,ht,he⟩ := rep
    obtain ⟨i,rfl⟩ := index_of_mem ht
    obtain ⟨x,p,hp,hx⟩ := liftOfMem hr
    obtain ⟨y,q,hq,hy⟩ := liftOfMem hs
    have eq : p=q := by
      by_contra hne
      apply noMixed
      refine ⟨i,r+s,he,Nat.eq_sq_add_sq_iff.mp ⟨x,y,by omega⟩⟩
    subst q
    exact ⟨i,r+s,p,he,hp,toShell (by omega) (by omega) hx hy (by simp) (by omega) (by omega)⟩
  · intro n _ _
    obtain ⟨r,hr,s,hs,t,ht,he⟩ := weightedAll (2,3) (by decide) n
    obtain ⟨i,rfl⟩ := index_of_mem hs
    obtain ⟨x,p,hp,hx⟩ := liftOfMem hr
    obtain ⟨y,q,hq,hy⟩ := liftOfMem ht
    exact ⟨i,r+3*t,p,q,by dsimp at he ⊢; omega,hp,hq,
      toShell (by omega) (by omega) hx hy rfl (by omega) (by omega)⟩

end OMA.R_oeis_a256587_R1
