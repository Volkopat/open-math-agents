import OMAStatements.S_oeis_a280414

/-!
Proof of Chai Wah Wu's conjectures for OEIS A280414 (Rule 262).
A four-phase moving boundary and preservation of the zero interior imply
that the axis value is 1 at even times and 111 at odd times from time 30.
Finite initial states are verified by explicit transition certificates.
Coefficient extraction gives the generating-function identity.

Source: https://oeis.org/A280414
The registered statement was contributed by clementtrecourt.
-/

namespace Rule262
open OMA.S_oeis_a280414

lemma outside_plus (t : ℕ) (x y : ℤ) (h : (t : ℤ) < x+y) :
    cell 262 t x y = false := by
  induction t generalizing x y with
  | zero => simp only [cell, decide_eq_false_iff_not]; omega
  | succ t ih =>
    have h0 := ih x y (by omega)
    have h1 := ih (x+1) y (by omega)
    have h2 := ih (x-1) y (by omega)
    have h3 := ih x (y+1) (by omega)
    have h4 := ih x (y-1) (by omega)
    simp [cell, h0,h1,h2,h3,h4]

lemma outside_minus (t : ℕ) (x y : ℤ) (h : (t : ℤ) < x-y) :
    cell 262 t x y = false := by
  induction t generalizing x y with
  | zero => simp only [cell, decide_eq_false_iff_not]; omega
  | succ t ih =>
    have h0 := ih x y (by omega)
    have h1 := ih (x+1) y (by omega)
    have h2 := ih (x-1) y (by omega)
    have h3 := ih x (y+1) (by omega)
    have h4 := ih x (y-1) (by omega)
    simp [cell, h0,h1,h2,h3,h4]

lemma mirror_y (t : ℕ) (x y : ℤ) : cell 262 t x (-y) = cell 262 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [show -y+1 = -(y-1) by omega, show -y-1 = -(y+1) by omega]
    rw [ih, ih, ih, ih, ih]
    congr 1
    omega

def out (c e w u d : Bool) : Bool :=
  (262 : ℕ).testBit (c.toNat + 2*(e.toNat+w.toNat+u.toNat+d.toNat))

def band (t : ℕ) (d y : ℤ) : Bool :=
  if d=0 then decide (y=0)
  else if d=1 then decide (t%2=1 ∧ (y = -1 ∨ y=0 ∨ y=1))
  else if d=2 then decide (
    (t%4=2 ∧ (y = -2 ∨ y=2)) ∨
    (t%4=1 ∧ y=0) ∨
    (t%4=3 ∧ (y = -2 ∨ y=0 ∨ y=2)))
  else if d=3 then decide (
    ((t%4=0 ∨ t%4=1) ∧ (y = -1 ∨ y=1)) ∨
    (t%4=3 ∧ (y = -3 ∨ y = -2 ∨ y = -1 ∨ y=1 ∨ y=2 ∨ y=3)))
  else false

lemma band_neg (t : ℕ) (d y : ℤ) (h : d<0) : band t d y = false := by
  simp [band, show d≠0 by omega, show d≠1 by omega, show d≠2 by omega,
    show d≠3 by omega]

lemma band_far (t : ℕ) (d y : ℤ) (h : y < -3 ∨ 3 < y) : band t d y = false := by
  have h0 : y≠0 := by omega
  have h1 : y≠1 := by omega
  have h2 : y≠2 := by omega
  have h3 : y≠3 := by omega
  have hn1 : y≠ -1 := by omega
  have hn2 : y≠ -2 := by omega
  have hn3 : y≠ -3 := by omega
  simp [band,h0,h1,h2,h3,hn1,hn2,hn3]

set_option maxHeartbeats 1600000 in
lemma band_step (t : ℕ) (d y : ℤ) (hd : d ≤ 3) :
    band (t+1) d y = out (band t (d-1) y) (band t (d-2) y)
      (band t d y) (band t (d-1) (y+1)) (band t (d-1) (y-1)) := by
  by_cases hn : d < 0
  · simp (disch := omega) only [band_neg, out]; decide
  · have hd0 : 0 ≤ d := by omega
    by_cases hlo : y < -4
    · simp (disch := omega) only [band_far, out]; decide
    · by_cases hhi : 4 < y
      · simp (disch := omega) only [band_far, out]; decide
      · have hy0 : -4 ≤ y := by omega
        have hy1 : y ≤ 4 := by omega
        have ht : t%4<4 := Nat.mod_lt _ (by decide)
        have hp : (t+1)%4=(t%4+1)%4 := by omega
        have h2 : t%2=(t%4)%2 := by omega
        have h2p : (t+1)%2=((t%4+1)%4)%2 := by omega
        simp only [band, hp, h2, h2p]
        interval_cases d <;> interval_cases y <;> interval_cases h : t%4 <;> decide


lemma depth_off (t : ℕ) (d y : ℤ) (hd : d<0) :
    cell 262 t ((t:ℤ)-d) y = false := by
  by_cases hy : 0≤y
  · exact outside_plus t _ _ (by omega)
  · exact outside_minus t _ _ (by omega)

set_option maxHeartbeats 1600000 in
lemma band_correct : ∀ t : ℕ, 2≤t → ∀ d y : ℤ, d≤3 →
    cell 262 t ((t:ℤ)-d) y = band t d y := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht d y hd
    by_cases hn : d<0
    · rw [depth_off t d y hn, band_neg t d y hn]
    · by_cases hb : t=2
      · subst t
        by_cases hlo : y < -3
        · rw [outside_minus 2 _ _ (by omega), band_far _ _ _ (Or.inl hlo)]
        · by_cases hhi : 3 < y
          · rw [outside_plus 2 _ _ (by omega), band_far _ _ _ (Or.inr hhi)]
          · have hd0 : 0≤d := by omega
            have hy0 : -3≤y := by omega
            have hy1 : y≤3 := by omega
            interval_cases d <;> interval_cases y <;> decide
      · obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show t≠0 by omega)
        have hn2 : 2≤n := by omega
        have ih' := ih n (by omega) hn2
        change out (cell 262 n ((n+1:ℕ)-d) y)
          (cell 262 n (((n+1:ℕ):ℤ)-d+1) y)
          (cell 262 n (((n+1:ℕ):ℤ)-d-1) y)
          (cell 262 n (((n+1:ℕ):ℤ)-d) (y+1))
          (cell 262 n (((n+1:ℕ):ℤ)-d) (y-1)) = band (n+1) d y
        rw [show ((n+1:ℕ):ℤ)-d = (n:ℤ)-(d-1) by push_cast; ring,
          show (n:ℤ)-(d-1)+1 = (n:ℤ)-(d-2) by ring,
          show (n:ℤ)-(d-1)-1 = (n:ℤ)-d by ring]
        rw [ih' (d-1) y (by omega), ih' (d-2) y (by omega),
          ih' d y hd, ih' (d-1) (y+1) (by omega), ih' (d-1) (y-1) (by omega)]
        exact (band_step n d y hd).symm


lemma mirror_x (t : ℕ) (x y : ℤ) : cell 262 t (-x) y = cell 262 t x y := by
  induction t generalizing x y with
  | zero => simp [cell]
  | succ t ih =>
    simp only [cell]
    rw [show -x+1 = -(x-1) by omega, show -x-1 = -(x+1) by omega]
    rw [ih, ih, ih, ih, ih]
    congr 1
    omega

def lookup (a : Array (Array Bool)) (x y : ℕ) : Bool :=
  ((a[x]?).getD #[])[y]?.getD false

def square (N : ℕ) (f : ℕ → ℕ → Bool) : Array (Array Bool) :=
  Array.ofFn fun x : Fin N => Array.ofFn fun y : Fin N => f x y

lemma lookup_square (N x y : ℕ) (f : ℕ → ℕ → Bool) :
    lookup (square N f) x y = if x<N ∧ y<N then f x y else false := by
  by_cases hx : x<N <;> by_cases hy : y<N <;>
    simp [lookup, square, hx, hy]

def prev (x : ℕ) : ℕ := if x=0 then 1 else x-1

def grid : ℕ → Array (Array Bool)
  | 0 => square 1 fun x y => decide (x=0 ∧ y=0)
  | n+1 =>
    let a := grid n
    square (n+2) fun x y =>
      out (lookup a x y) (lookup a (x+1) y) (lookup a (prev x) y)
        (lookup a x (y+1)) (lookup a x (prev y))

lemma cell_nat_prev_x (t x y : ℕ) :
    cell 262 t ((x:ℤ)-1) y = cell 262 t (prev x) y := by
  by_cases hx : x=0
  · subst x; simpa [prev] using mirror_x t 1 y
  · have hx1 : 1≤x := by omega
    simp only [prev, if_neg hx]
    congr 2
    omega

lemma cell_nat_prev_y (t x y : ℕ) :
    cell 262 t x ((y:ℤ)-1) = cell 262 t x (prev y) := by
  by_cases hy : y=0
  · subst y; simpa [prev] using mirror_y t x 1
  · have hy1 : 1≤y := by omega
    simp only [prev, if_neg hy]
    congr 2
    omega

lemma grid_correct (t x y : ℕ) : lookup (grid t) x y = cell 262 t x y := by
  induction t generalizing x y with
  | zero =>
    rw [grid, lookup_square]
    by_cases hx : x=0 <;> by_cases hy : y=0 <;>
      simp_all [cell]
  | succ t ih =>
    rw [grid, lookup_square]
    split_ifs with hb
    · simp only [ih]
      rw [← cell_nat_prev_x, ← cell_nat_prev_y]
      rfl
    · symm
      apply outside_plus
      push_cast
      omega


lemma axis_step (n x : ℕ) :
    cell 262 (n+1) x 0 =
      out (cell 262 n x 0) (cell 262 n (x+1 : ℕ) 0)
        (cell 262 n (prev x) 0) (cell 262 n x 1) (cell 262 n x 1) := by
  change out (cell 262 n x 0) (cell 262 n ((x:ℤ)+1) 0)
    (cell 262 n ((x:ℤ)-1) 0) (cell 262 n x 1) (cell 262 n x (-1)) = _
  have hp := cell_nat_prev_x n x 0
  norm_num only [Nat.cast_zero] at hp
  rw [hp, mirror_y n x 1]
  simp only [Nat.cast_add, Nat.cast_one]

lemma inert (u : Bool) : out false false false u u = false := by
  cases u <;> decide

lemma boundary_block (n : ℕ) :
    out false (band n 2 0) false (band n 3 1) (band n 3 1) = false := by
  have h : n%4<4 := Nat.mod_lt _ (by decide)
  have h2 : n%2=(n%4)%2 := by omega
  simp only [band, h2]
  interval_cases h' : n%4 <;> decide

lemma band_at (n x : ℕ) (y : ℤ) (hn : 2≤n) (h : (n:ℤ)-x≤3) :
    cell 262 n x y = band n ((n:ℤ)-x) y := by
  convert band_correct n hn ((n:ℤ)-x) y h using 1 <;> congr 2 <;> omega

lemma zeros_from30
    (hbase : ∀ x : ℕ, x+3≤30 → cell 262 30 x 0 = false) :
    ∀ n : ℕ, 30≤n → ∀ x : ℕ, x+3≤n → cell 262 n x 0 = false := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn x hx
    by_cases h30 : n=30
    · subst n; exact hbase x hx
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n≠0 by omega)
      have hm : 30≤ m := by omega
      have ih' := ih m (by omega) hm
      by_cases hend : x+2=m
      · rw [band_at (m+1) x 0 (by omega) (by omega)]
        have hd : ((m+1:ℕ):ℤ)-(x:ℤ)=3 := by omega
        rw [hd]
        simp [band]
      · have hc : x+3≤ m := by omega
        have hp : prev x+3≤ m := by
          unfold prev
          split_ifs <;> omega
        rw [axis_step, ih' x hc, ih' (prev x) hp]
        by_cases he : x+3=m
        · have hband2 := band_at m (x+1) 0 (by omega) (by omega)
          have hband3 := band_at m x 1 (by omega) (by omega)
          have hd2 : (m:ℤ)-(x+1:ℕ)=2 := by omega
          have hd3 : (m:ℤ)-(x:ℤ)=3 := by omega
          rw [hband2,hband3,hd2,hd3]
          exact boundary_block m
        · rw [ih' (x+1) (by omega)]
          exact inert _


def mask (n x : ℕ) : Bool :=
  if x=n then true else if x+1=n ∨ x+2=n then decide (n%2=1) else false

lemma axis_pattern
    (hbase : ∀ x : ℕ, x+3≤30 → cell 262 30 x 0 = false)
    (n x : ℕ) (hn : 30≤n) : cell 262 n x 0 = mask n x := by
  by_cases hx : n<x
  · rw [outside_plus n x 0 (by omega)]
    simp [mask, show x≠n by omega, show ¬(x+1=n ∨ x+2=n) by omega]
  · by_cases h0 : x=n
    · subst x
      rw [band_at n n 0 (by omega) (by omega)]
      simp [mask, band]
    · by_cases h1 : x+1=n
      · rw [band_at n x 0 (by omega) (by omega)]
        have hd : (n:ℤ)-(x:ℤ)=1 := by omega
        rw [hd]
        simp [mask,band,h0,h1]
      · by_cases h2 : x+2=n
        · rw [band_at n x 0 (by omega) (by omega)]
          have hd : (n:ℤ)-(x:ℤ)=2 := by omega
          rw [hd]
          simp only [mask,if_neg h0,if_pos (Or.inr h2),band]
          have hr : n%4<4 := Nat.mod_lt _ (by decide)
          have hr2 : n%2=(n%4)%2 := by omega
          rw [hr2]
          interval_cases h : n%4 <;> decide
        · rw [zeros_from30 hbase n hn x (by omega)]
          simp [mask,h0,h1,h2]

lemma mask_sum (n : ℕ) (hn : 2≤n) :
    (∑ x ∈ Finset.range (n+1), if mask n x then (10:ℤ)^(n-x) else 0) =
      if n%2=1 then 111 else 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n=m+2 := ⟨n-2,by omega⟩
  rw [show m+2+1=m+3 by omega, Finset.sum_range_add]
  have hz : (∑ x ∈ Finset.range m,
      if mask (m+2) x then (10:ℤ)^(m+2-x) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' := Finset.mem_range.mp hx
    simp [mask, show x≠m+2 by omega] <;> omega
  rw [hz,zero_add]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  have h0 : m+2-m=2 := by omega
  have h1 : m+2-(m+1)=1 := by omega
  simp [mask, h0,h1]
  split_ifs <;> norm_num

end Rule262

namespace Rule262
open OMA.S_oeis_a280414

def packed (n : ℕ) : ℕ := ([1, 7, 68, 4958, 1048657, 1124345273, 4399120515137, 72907576994976227, 4722366553239463411972, 1241567999648454314789558158, 1298075452573746192583286063125505, 5448507178424410101623110201009226427905, 91343852333514063905230189514660322548816105473, 6131104619559778115173919316975995285539806317408598017, 1645504563451188228454487784356688777471158153213932540854091777, 1766927946675354359494185739970772198356797716181976680937001137577058305, 7588550360256760923265816430464753607871273873283649956568688797088956606582161409, 130371794457013490945347976380745996578650337773534504689826372700448931369801744756591263745, 8958978968841587144715176231794959361981368913995245917030265318724361105883433752049596921492163264513, 2462632432913602025881839346790199941116775460079672038954711731125656255811386969895919660287239268502988202573825, 2707685248164858261894182987140430663913726288061310699505727315015998816238090303912226003616933024253201065300525930551181313, 11908534176501200555538193189179639280762157498775599477607883101324194435561874791806334453767870988479087897616895483569465858314150084609, 209496998905364988206503000497182417904386571861627782296349992528202004351354056897416734420344076938423356972801851386243256033757707357817733304549377, 14742043358041709268640039309810772038285879165025631853459633325574669603266582005554955517348128314336727804400983323640256150098490803333420281704456559436211683329, 4149515568880992958512627537216285331303762790647008508386220318405590149674455527181878886304249982881893586159252841204618293763143226069941873144740932946849031808024914480332801, 4671939401297085924705374339112020376946900900722788827045144227380108185232511538848222969208985129978643112587654986793328069611784382034219336577416795393253936765360645964061247542905704284161, 21040543606193498700903151976648418550761083448405408652801653318367857646287754891240421809818836773952613807696240630014462488319647926426384918845665991627855830553381877530254881691792294491823655077292277761, 379032741614123731733362347928412151223780394100425727896086616498258285274614057961687282294570746950575539821264350947865126076455660655981481581525904060444116462725499942388899438285375656322019512226289738861609097153740801, 27312187117075883106631073287796022035768018755218072341551437796034414123212448209722398969226708276282085449043269903227765840257071265401872972841750754076081422329300631855126270828311183366898560573213614357963542102051834943304750833074177, 7872201988275395564559053648707139702746795212509725484128551563091458078915700786830417709929794368796275865101989986142444974389030907763177476856307498334128890367080003996476053553413243723993077970520873554538464939462466406334975910024339895984941086801923, 9076030935533343897020532643465169016127682122764050314072320672653515629533784520063907773403943579941564194324673625294175449871199049006703641988352190556205548691344178496114279835814764119324931610869451731537425474019295827050705064585262605222735685651827390353200723787776] : List ℕ).getD n 0

def snapshot (n : ℕ) : Array (Array Bool) :=
  square (n+1) fun x y => (packed n).testBit (x*(n+1)+y)

def bit (n x y : ℕ) : Bool :=
  if x<n+1 ∧ y<n+1 then (packed n).testBit (x*(n+1)+y) else false

lemma lookup_snapshot (n x y : ℕ) : lookup (snapshot n) x y = bit n x y := by
  rw [snapshot,lookup_square]
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma transition_bits : ∀ n : Fin 30, ∀ x : Fin (n.val+2), ∀ y : Fin (n.val+2),
    out (bit n x y) (bit n (x+1) y) (bit n (prev x) y)
      (bit n x (y+1)) (bit n x (prev y)) = bit (n.val+1) x y := by
  decide +kernel


lemma transitions : ∀ n : Fin 30,
    square (n.val+2) (fun x y =>
      out (lookup (snapshot n) x y)
        (lookup (snapshot n) (x+1) y)
        (lookup (snapshot n) (prev x) y)
        (lookup (snapshot n) x (y+1))
        (lookup (snapshot n) x (prev y))) = snapshot (n.val+1) := by
  intro n
  change (Array.ofFn fun x : Fin (n.val+2) => Array.ofFn fun y : Fin (n.val+2) =>
      out (lookup (snapshot n) x y)
        (lookup (snapshot n) (x+1) y)
        (lookup (snapshot n) (prev x) y)
        (lookup (snapshot n) x (y+1))
        (lookup (snapshot n) x (prev y))) =
    (Array.ofFn fun x : Fin (n.val+2) => Array.ofFn fun y : Fin (n.val+2) =>
      (packed (n.val+1)).testBit (x.val*(n.val+2)+y.val))
  apply congrArg Array.ofFn
  funext x
  apply congrArg Array.ofFn
  funext y
  simp only [lookup_snapshot]
  calc
    _ = bit (n.val+1) x y := transition_bits n x y
    _ = _ := by
      rw [bit,if_pos (by constructor <;> omega)]

lemma grid_snapshot (n : ℕ) (hn : n≤30) : grid n = snapshot n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [grid, ih (by omega)]
    exact transitions ⟨n,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma base_grid : ∀ x : Fin 28, lookup (grid 30) x 0 = false := by
  rw [grid_snapshot 30 (by decide)]
  decide +kernel

lemma base30 : ∀ x : ℕ, x+3≤30 → cell 262 30 x 0 = false := by
  intro x hx
  have hg := grid_correct 30 x 0
  norm_num only [Nat.cast_zero] at hg
  rw [← hg]
  exact base_grid ⟨x,by omega⟩

lemma a_eventual (n : ℕ) (hn : 30≤n) :
    a n = if n%2=1 then 111 else 1 := by
  unfold a
  simp_rw [axis_pattern base30 n _ hn]
  exact mask_sum n (by omega)

theorem recurrence (n : ℕ) (hn : 32≤n) : (a n : ℚ) = a (n-2) := by
  rw [a_eventual n (by omega), a_eventual (n-2) (by omega)]
  rw [show (n-2)%2=n%2 by omega]


def evaluatedA (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n+1), if lookup (grid n) k 0 then (10:ℤ)^(n-k) else 0

lemma evaluatedA_eq (n : ℕ) : evaluatedA n = a n := by
  simp only [evaluatedA,a,grid_correct,Nat.cast_zero]

def initialValue (n : ℕ) : ℤ := ([1, 11, 1, 111, 10001, 100111, 1000001, 11000111, 1000001, 111000111, 10000000001, 100000000111, 1000000000001, 10000000000111, 100000000000001, 1000000000000111, 10000000000000001, 100000000000000111, 1000000000000000001, 10000000000000000111, 100000000000000000001, 1000000000000000000111, 10000000000000000000001, 100000000000000000000111, 1000000000000000000000001, 10000000000000000000000111, 100000000000000000000000001, 1000000000000000000000000111, 10000000000000000000000000001, 110000000000000000000000000111] : List ℤ).getD n 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initial_grid : ∀ n : Fin 30, evaluatedA n = initialValue n := by
  have h : ∀ n : Fin 30,
      (∑ k ∈ Finset.range (n.val+1),
        if lookup (snapshot n) k 0 then (10:ℤ)^(n.val-k) else 0) = initialValue n := by
    decide +kernel
  intro n
  simpa only [evaluatedA, grid_snapshot n (by omega)] using h n

lemma initial (n : ℕ) (hn : n<30) : a n = initialValue n := by
  rw [← evaluatedA_eq]
  exact initial_grid ⟨n,hn⟩

open PowerSeries

set_option maxHeartbeats 4000000 in
theorem generating_function :
    (PowerSeries.mk (fun n => (a n : ℚ)) * (X ^ 2 - 1 : PowerSeries ℚ) = 110000000000000000000000000000 * X ^ 31 + 10000000000000000000000000000 * X ^ 30 - 109000000000000000000000000000 * X ^ 29 - 9900000000000000000000000000 * X ^ 28 - 990000000000000000000000000 * X ^ 27 - 99000000000000000000000000 * X ^ 26 - 9900000000000000000000000 * X ^ 25 - 990000000000000000000000 * X ^ 24 - 99000000000000000000000 * X ^ 23 - 9900000000000000000000 * X ^ 22 - 990000000000000000000 * X ^ 21 - 99000000000000000000 * X ^ 20 - 9900000000000000000 * X ^ 19 - 990000000000000000 * X ^ 18 - 99000000000000000 * X ^ 17 - 9900000000000000 * X ^ 16 - 990000000000000 * X ^ 15 - 99000000000000 * X ^ 14 - 9900000000000 * X ^ 13 - 990000000000 * X ^ 12 - 99889000000 * X ^ 11 - 9999000000 * X ^ 10 - 100000000 * X ^ 9 - 10900000 * X ^ 7 - 990000 * X ^ 6 - 100000 * X ^ 5 - 10000 * X ^ 4 - 100 * X ^ 3 - 11 * X - 1) := by
  let F := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hp : (110000000000000000000000000000 * X ^ 31 + 10000000000000000000000000000 * X ^ 30 - 109000000000000000000000000000 * X ^ 29 - 9900000000000000000000000000 * X ^ 28 - 990000000000000000000000000 * X ^ 27 - 99000000000000000000000000 * X ^ 26 - 9900000000000000000000000 * X ^ 25 - 990000000000000000000000 * X ^ 24 - 99000000000000000000000 * X ^ 23 - 9900000000000000000000 * X ^ 22 - 990000000000000000000 * X ^ 21 - 99000000000000000000 * X ^ 20 - 9900000000000000000 * X ^ 19 - 990000000000000000 * X ^ 18 - 99000000000000000 * X ^ 17 - 9900000000000000 * X ^ 16 - 990000000000000 * X ^ 15 - 99000000000000 * X ^ 14 - 9900000000000 * X ^ 13 - 990000000000 * X ^ 12 - 99889000000 * X ^ 11 - 9999000000 * X ^ 10 - 100000000 * X ^ 9 - 10900000 * X ^ 7 - 990000 * X ^ 6 - 100000 * X ^ 5 - 10000 * X ^ 4 - 100 * X ^ 3 - 11 * X - 1 : PowerSeries ℚ) =
    C 110000000000000000000000000000 * X ^ 31 + C 10000000000000000000000000000 * X ^ 30 - C 109000000000000000000000000000 * X ^ 29 - C 9900000000000000000000000000 * X ^ 28 - C 990000000000000000000000000 * X ^ 27 - C 99000000000000000000000000 * X ^ 26 - C 9900000000000000000000000 * X ^ 25 - C 990000000000000000000000 * X ^ 24 - C 99000000000000000000000 * X ^ 23 - C 9900000000000000000000 * X ^ 22 - C 990000000000000000000 * X ^ 21 - C 99000000000000000000 * X ^ 20 - C 9900000000000000000 * X ^ 19 - C 990000000000000000 * X ^ 18 - C 99000000000000000 * X ^ 17 - C 9900000000000000 * X ^ 16 - C 990000000000000 * X ^ 15 - C 99000000000000 * X ^ 14 - C 9900000000000 * X ^ 13 - C 990000000000 * X ^ 12 - C 99889000000 * X ^ 11 - C 9999000000 * X ^ 10 - C 100000000 * X ^ 9 - C 10900000 * X ^ 7 - C 990000 * X ^ 6 - C 100000 * X ^ 5 - C 10000 * X ^ 4 - C 100 * X ^ 3 - C 11 * X ^ 1 - C 1 * X ^ 0 := by
    simp only [map_ofNat, map_one]
    ring
  rw [hp,mul_sub,mul_one]
  ext n
  simp only [map_sub,map_add,coeff_mul_X_pow',coeff_C,coeff_mk,F]
  by_cases hn : 32≤n
  · have h := recurrence n hn
    simp (disch := omega) only [if_pos,if_neg]
    linarith
  · interval_cases n <;>
      norm_num [initial, a_eventual, initialValue]

theorem solution : type_of% @OMA.S_oeis_a280414.main :=
  ⟨recurrence,generating_function⟩
end Rule262

theorem OMA.solution : type_of% @OMA.S_oeis_a280414.main := Rule262.solution
