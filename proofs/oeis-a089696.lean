import OMAStatements.S_oeis_a089696

namespace MagnanimousProduct

/-- A list of pair labels selected from disjoint adjacent positions of a word. -/
inductive Strip : List ℕ → List (ℕ × ℕ) → Prop
  | empty : Strip [] []
  | digit (a : ℕ) {w l} : Strip w l → Strip (a::w) l
  | pair (a b : ℕ) {w l} : Strip w l → Strip (a::b::w) ((a,b)::l)

end MagnanimousProduct

namespace MagnanimousProduct

/-- Exactly k marked occurrences remain, and rest lists the unmarked digits. -/
inductive Marked (d e : ℕ) : List ℕ → ℕ → List ℕ → Prop
  | empty : Marked d e [] 0 []
  | digit (a : ℕ) {w k rest} : Marked d e w k rest → Marked d e (a::w) k (a::rest)
  | hit {w k rest} : Marked d e w k rest → Marked d e (d::e::w) (k+1) rest

private theorem mark_none (d e : ℕ) (w : List ℕ) : Marked d e w 0 w := by
  induction w with
  | nil => exact .empty
  | cons a w ih => exact .digit a ih

theorem select_pairs {d e k : ℕ} {w : List ℕ} {l : List (ℕ×ℕ)}
    (h : Strip w l) (hk : k ≤ l.count (d,e)) : ∃ rest, Marked d e w k rest := by
  induction h generalizing k with
  | empty =>
    have he : k=0 := by simpa using hk
    subst k
    exact ⟨[],.empty⟩
  | digit a _ ih =>
    obtain ⟨r,hr⟩ := ih hk
    exact ⟨_,.digit a hr⟩
  | @pair a b w l _ ih =>
    cases k with
    | zero => exact ⟨_,mark_none d e _⟩
    | succ k =>
      by_cases same : (a,b)=(d,e)
      · obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
        have hle : k ≤ l.count (a,b) := by simpa using hk
        obtain ⟨r,hr⟩ := ih hle
        exact ⟨r,.hit hr⟩
      · have hle : k+1 ≤ l.count (d,e) := by simpa [List.count_cons,same] using hk
        obtain ⟨r,hr⟩ := ih hle
        exact ⟨_,.digit a (.digit b hr)⟩

theorem rest_subset {d e k : ℕ} {w rest : List ℕ} (h : Marked d e w k rest) :
    ∀ x ∈ rest, x ∈ w := by
  induction h with
  | empty => simp
  | digit a _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl|h
    · simp
    · exact List.mem_cons_of_mem _ (ih x h)
  | hit _ ih =>
    exact fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih x hx))

def value (w : List ℕ) : ℕ := Nat.ofDigits 10 w.reverse

theorem realize {d e k t : ℕ} {w rest : List ℕ} (h : Marked d e w k rest) (ht : t ≤ k) :
    ∃ bs : List (List ℕ), bs.flatten=w ∧ (∀ c ∈ bs, c≠[]) ∧
      (bs.map value).prod=(10*d+e)^t*(d*e)^(k-t)*rest.prod := by
  have vs (x : ℕ) : value [x] = x := by simp [value]
  have vp : value [d,e] = 10*d+e := by simp [value,Nat.ofDigits, Nat.add_comm]
  induction h generalizing t with
  | empty =>
    have he : t=0 := by omega
    exact ⟨[],by simp [he]⟩
  | digit a _ ih =>
    obtain ⟨bs,hf,hn,hv⟩ := ih ht
    refine ⟨[a]::bs,by simp [hf],?_,?_⟩
    · simpa using hn
    · simp only [List.map_cons,List.prod_cons,vs,hv]
      ring
  | @hit w k r _ ih =>
    by_cases hlow : t ≤ k
    · obtain ⟨bs,hf,hn,hv⟩ := ih hlow
      refine ⟨[d]::[e]::bs,by simp [hf],?_,?_⟩
      · simpa using hn
      · simp only [List.map_cons,List.prod_cons,vs,hv]
        rw [show k+1-t=(k-t)+1 by omega,pow_succ]
        ring
    · have he : t=k+1 := by omega
      subst t
      obtain ⟨bs,hf,hn,hv⟩ := ih (show k ≤ k from le_rfl)
      refine ⟨[d,e]::bs,by simp [hf],?_,?_⟩
      · simpa using hn
      · simp only [List.map_cons,List.prod_cons,vp,hv,Nat.sub_self,pow_zero,pow_succ]
        ring

end MagnanimousProduct

/-! Finite congruence certificates for products of decimal chunks plus one. -/

namespace MagnanimousProduct.Table

/-- These five ordered pairs do not occur in the finite certificate. -/
def good (d e : ℕ) : Bool :=
  match d, e with
  | 1, 8 | 4, 5 | 4, 9 | 9, 6 | 9, 8 => false
  | _, _ => true

/-- Each four-digit window contains an ordered pair with a certificate. -/
theorem window_good {a b c d : ℕ} (ha : a < 10) (hb : b < 10) (hc : c < 10) (hd : d < 10) :
    good a b = true ∨ good b c = true ∨ good c d = true := by
  have all : ∀ a b c d : Fin 10,
      good a b = true ∨ good b c = true ∨ good c d = true := by decide +kernel
  exact all ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩ ⟨d,hd⟩

/-- The first entry is the prime. The six-bit digit at position r in the
second entry gives the number of merges used for the nonzero residue r. -/
private def row (d e : ℕ) : ℕ × ℕ :=
  match d, e with
  | 1, 1 => (13, 0xc1482893470c408b180)
  | 1, 2 => (11, 0x92872c3206085100)
  | 1, 3 => (11, 0x624a0880c71442c0)
  | 1, 4 => (17, 0xc1874034452823492c83ce100)
  | 1, 5 => (17, 0x92c834428e3c7182305403440)
  | 1, 6 => (13, 0x720b244306283142340)
  | 1, 7 => (29, 0x186cb08638415a24f4561d520375731349c51064d280)
  | 1, 9 => (11, 0x81440862c724a0c0)
  | 2, 1 => (59, 0x2d8214d952b19530a1e878dcef20fe5fdd8d056c945deae9b8897d5a09cb25496abb2e49e9ca33b1db0103400)
  | 2, 2 => (17, 0xc38340f14908a44d1c82c6100)
  | 2, 3 => (11, 0x920b1c5282183100)
  | 2, 4 => (17, 0x211118d0c72103cb14e24c280)
  | 2, 5 => (11, 0x52092c7086103280)
  | 2, 6 => (17, 0xd1d044c28e2c318210920f140)
  | 2, 7 => (23, 0x31cd2d04483d750a5493044c6156092380)
  | 2, 8 => (17, 0x818910d1c308a2cf14c44e400)
  | 2, 9 => (13, 0x320b34c10a187142240)
  | 3, 1 => (13, 0x80cc28b1cd144189080)
  | 3, 2 => (17, 0xd2c624a1101cf20c091383140)
  | 3, 3 => (19, 0x415118248a1cc0d04c92cf20e340)
  | 3, 4 => (29, 0x151824db3c910b30a70358844e61a6525dd3454141c0)
  | 3, 5 => (11, 0x82462821c52c40c0)
  | 3, 6 => (11, 0x718914320a10b080)
  | 3, 7 => (11, 0x508b243204187280)
  | 3, 8 => (11, 0x728b0c9108185080)
  | 3, 9 => (37, 0x68c471986254248c6a56d739d7cd2e01494c87a450340f1ca591600)
  | 4, 1 => (11, 0x22c42880c52461c0)
  | 4, 2 => (11, 0xb1051c3202289180)
  | 4, 3 => (17, 0xd1d044c28e2c318210920f140)
  | 4, 4 => (13, 0x80cc28b1cd144189080)
  | 4, 6 => (19, 0x224340628814434e4533c73122c0)
  | 4, 7 => (11, 0xb0890c5288107180)
  | 4, 8 => (11, 0x508b243204187280)
  | 5, 1 => (11, 0x82c210a1491c60c0)
  | 5, 2 => (17, 0xb1463c240425130828738d0c0)
  | 5, 3 => (13, 0xb30334810a087246140)
  | 5, 4 => (11, 0x41421880cb1ca240)
  | 5, 5 => (29, 0xc55d08e2882d25cd4c64435056c91195987103c7680)
  | 5, 6 => (11, 0x91850c708828b100)
  | 5, 7 => (13, 0x81c418b0c914c28d080)
  | 5, 8 => (11, 0x718914320a10b080)
  | 5, 9 => (17, 0x111c634a3080cb40408538f240)
  | 6, 1 => (23, 0x621628708331024f11415738d4952d3440)
  | 6, 2 => (11, 0xa1c61080c92c2140)
  | 6, 3 => (17, 0x1028b10714938644d3cc0c2200)
  | 6, 4 => (13, 0x51891c228420d0cc2c0)
  | 6, 5 => (17, 0x438720344508a3492d03c6300)
  | 6, 6 => (23, 0x101083954970962511942cd3072834cf140)
  | 6, 7 => (41, 0x285991221e168a4157513d321f8179920cc2dc9e3949a6478635b398142500)
  | 6, 8 => (11, 0x82462821c52c40c0)
  | 6, 9 => (11, 0x52092c7086103280)
  | 7, 1 => (11, 0xb20714910a083180)
  | 7, 2 => (11, 0x81ca18424b1420c0)
  | 7, 3 => (17, 0xc38340f14908a44d1c82c6100)
  | 7, 4 => (13, 0x730314420228b246340)
  | 7, 5 => (17, 0x1018d3110cf08a1cb24414e200)
  | 7, 6 => (11, 0x41421880cb1ca240)
  | 7, 7 => (29, 0x100c748a59c15a65b2463dd51734b313388604551080)
  | 7, 8 => (23, 0x32473c635054b3084d758a142444494380)
  | 7, 9 => (13, 0xb18334228420724c140)
  | 8, 1 => (11, 0x720524b184283080)
  | 8, 2 => (17, 0x828730324d3861512c43c2400)
  | 8, 3 => (17, 0x52c24462041cf310389283340)
  | 8, 4 => (23, 0xa40e58d5171924cf1081d130908b0c5540)
  | 8, 5 => (13, 0xc34408914b0c8287180)
  | 8, 6 => (13, 0x83441852432cc287080)
  | 8, 7 => (17, 0x110c814428e1cf18230d40b240)
  | 8, 8 => (17, 0x438f20b24d08a1510d01c6300)
  | 8, 9 => (11, 0x920b1c5282183100)
  | 9, 1 => (17, 0x230d1891cb4080cf44e144280)
  | 9, 2 => (17, 0x1018d3110cf08a1cb24414e200)
  | 9, 3 => (13, 0xc2c82831cd244085180)
  | 9, 4 => (11, 0x81ca18424b1420c0)
  | 9, 5 => (11, 0xa1c61080c92c2140)
  | 9, 7 => (11, 0xb1051c3202289180)
  | 9, 9 => (13, 0x824c2853472c4183080)
  | _, _ => (0,0)

private def exponent (packed r : ℕ) : ℕ := (packed >>> (6*r)) % 64

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
private theorem verified : ∀ a b : Fin 10,
    0 < a.val → 0 < b.val → good a b = true →
    let p := (row a b).1
    let w := (row a b).2
    p.Prime ∧ 10 < p ∧ p ≤ 59 ∧ ∀ r : Fin 59, 0 < r.val → r.val < p →
      let t := exponent w r.val
      2 ≤ t ∧ t ≤ 59 ∧ (((10*a.val+b.val)^t * (a.val*b.val)^(59-t)*r.val + 1) % p = 0) := by
  decide +kernel

/-- For an arbitrary product coprime to the indicated prime, some merge
count between 2 and 59 makes the product-plus-one divisible by it. -/
theorem pair_table {d e : ℕ} (hd0 : 0 < d) (hd10 : d < 10) (he0 : 0 < e) (he10 : e < 10)
    (hg : good d e = true) :
    ∃ p : ℕ, p.Prime ∧ 10 < p ∧ p ≤ 59 ∧ ∀ R : ℕ, ¬p ∣ R →
      ∃ t : ℕ, 2 ≤ t ∧ t ≤ 59 ∧ p ∣ (10*d+e)^t * (d*e)^(59-t)*R + 1 := by
  obtain ⟨hp,hlo,hhi,hrow⟩ := verified ⟨d,hd10⟩ ⟨e,he10⟩ hd0 he0 hg
  let p := (row d e).1
  change p.Prime at hp
  change 10 < p at hlo
  change p ≤ 59 at hhi
  refine ⟨p,hp,hlo,hhi,?_⟩
  intro R hR
  have hr : R%p < p := Nat.mod_lt _ hp.pos
  have hneq : R%p ≠ 0 := fun h => hR (Nat.dvd_iff_mod_eq_zero.mpr h)
  obtain ⟨htl,hth,hmod⟩ := hrow ⟨R%p,by omega⟩ (by simpa using Nat.pos_of_ne_zero hneq) hr
  let t := exponent (row d e).2 (R%p)
  let z := (10*d+e)^t*(d*e)^(59-t)
  change (z*(R%p)+1)%p = 0 at hmod
  refine ⟨t,htl,hth,Nat.modEq_zero_iff_dvd.mp ?_⟩
  have hz : z*(R%p)+1 ≡ 0 [MOD p] := by simpa only [Nat.ModEq, Nat.zero_mod] using hmod
  exact (((Nat.mod_modEq R p).symm.mul_left z).add_right 1).trans hz

private theorem rest_ok {p : ℕ} (hp : p.Prime) (hlo : 10 < p) (rest : List ℕ)
    (hrest : ∀ x ∈ rest, 0 < x ∧ x < 10) : 0 < rest.prod ∧ ¬p ∣ rest.prod := by
  induction rest with
  | nil => simpa using hp.not_dvd_one
  | cons x xs ih =>
    have hx := hrest x (by simp)
    have ⟨hpos,hnd⟩ := ih (fun y hy => hrest y (by simp [hy]))
    refine ⟨by simpa only [List.prod_cons] using Nat.mul_pos hx.1 hpos,?_⟩
    rw [List.prod_cons, hp.dvd_mul]
    exact not_or_intro (Nat.not_dvd_of_pos_of_lt hx.1 (by omega)) hnd

/-- 59 disjoint occurrences of a good adjacent pair force a partition
whose block product plus one is composite. -/
theorem composite_choice {d e : ℕ} (hd0 : 0 < d) (hd10 : d < 10) (he0 : 0 < e)
    (he10 : e < 10) (hg : good d e = true)
    (rest : List ℕ) (hrest : ∀ x ∈ rest, 0 < x ∧ x < 10) :
    ∃ t : ℕ, 2 ≤ t ∧ t ≤ 59 ∧ ¬((10*d+e)^t * (d*e)^(59-t)*rest.prod + 1).Prime := by
  obtain ⟨p,hp,hlo,hhi,hcert⟩ := pair_table hd0 hd10 he0 he10 hg
  obtain ⟨hpos,hnd⟩ := rest_ok hp hlo rest hrest
  obtain ⟨t,htl,hth,hdvd⟩ := hcert _ hnd
  refine ⟨t,htl,hth,fun hprime => ?_⟩
  have hx : 11 ≤ 10*d+e := by omega
  have hlarge : 121 ≤ (10*d+e)^t := calc
    121 = 11^2 := by decide
    _ ≤ (10*d+e)^2 := Nat.pow_le_pow_left hx _
    _ ≤ (10*d+e)^t := Nat.pow_le_pow_right (by omega) htl
  have hrest' : 0 < (d*e)^(59-t)*rest.prod := by positivity
  have hbound := Nat.le_mul_of_pos_right ((10*d+e)^t) hrest'
  rw [← Nat.mul_assoc] at hbound
  have heq := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd
  omega


end MagnanimousProduct.Table

/-! A good pair in every disjoint window of four digits forces a repeated pair. -/

namespace MagnanimousProduct

private def validPair (z : ℕ × ℕ) : Prop :=
  (0 < z.1 ∧ z.1 < 10) ∧ (0 < z.2 ∧ z.2 < 10) ∧ Table.good z.1 z.2 = true

private theorem no_pairs (w : List ℕ) : Strip w [] := by
  induction w with
  | nil => exact .empty
  | cons a _ ih => exact .digit a ih

private theorem windows : ∀ w : List ℕ, (∀ x ∈ w, 0 < x ∧ x < 10) →
    ∃ l : List (ℕ × ℕ), Strip w l ∧ w.length ≤ 4*l.length+3 ∧ ∀ z ∈ l, validPair z
  | [], _ => ⟨[],no_pairs _,by simp,by simp⟩
  | [_], _ => ⟨[],no_pairs _,by simp,by simp⟩
  | [_,_], _ => ⟨[],no_pairs _,by simp,by simp⟩
  | [_,_,_], _ => ⟨[],no_pairs _,by simp,by simp⟩
  | a::b::c::d::w, hd => by
    obtain ⟨l,hs,hlen,hv⟩ := windows w (fun x hx => hd x (by simp [hx]))
    have ha := hd a (by simp)
    have hb := hd b (by simp)
    have hc := hd c (by simp)
    have he := hd d (by simp)
    have addPair (z : ℕ × ℕ) (hz : validPair z) (h : Strip (a::b::c::d::w) (z::l)) :
        ∃ l : List (ℕ × ℕ), Strip (a::b::c::d::w) l ∧
        (a::b::c::d::w).length ≤ 4*l.length+3 ∧ ∀ z ∈ l, validPair z := by
      refine ⟨z::l,h,?_,?_⟩
      · simp only [List.length_cons]
        omega
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | h
        · exact hz
        · exact hv x h
    rcases Table.window_good ha.2 hb.2 hc.2 he.2 with h | h | h
    · exact addPair (a,b) ⟨ha,hb,h⟩ (.pair a b (.digit c (.digit d hs)))
    · exact addPair (b,c) ⟨hb,hc,h⟩ (.digit a (.pair b c (.digit d hs)))
    · exact addPair (c,d) ⟨hc,he,h⟩ (.digit a (.digit b (.pair c d hs)))

/-- A decimal word of at least 23,204 nonzero digits contains 59 mutually
disjoint occurrences of the same ordered pair with a modular certificate. -/
theorem long_strip {w : List ℕ} (hd : ∀ d ∈ w, 0 < d ∧ d < 10) (hl : 23204 ≤ w.length) :
    ∃ l d e, Strip w l ∧ 59 ≤ l.count (d,e) ∧ 0 < d ∧ d < 10 ∧
      0 < e ∧ e < 10 ∧ Table.good d e = true := by
  obtain ⟨l,hs,hlen,hv⟩ := windows w hd
  have hsub : l.toFinset ⊆ (Finset.range 10).product (Finset.range 10) := by
    intro z hz
    have hv' := hv z (List.mem_toFinset.mp hz)
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hv'.1.2,Finset.mem_range.mpr hv'.2.1.2⟩
  have hcard : l.toFinset.card ≤ 100 := by
    simpa using Finset.card_le_card hsub
  have high : ∃ z ∈ l.toFinset, 59 ≤ l.count z := by
    by_contra! h
    have hb : (∑ z ∈ l.toFinset, l.count z) ≤ ∑ _z ∈ l.toFinset, 58 := by
      exact Finset.sum_le_sum (fun z hz => by have := h z hz; omega)
    have htotal : (∑ z ∈ l.toFinset, l.count z) = l.length := by
      simpa only [List.count, Bool.beq_eq_decide_eq] using List.sum_toFinset_count_eq_length l
    rw [htotal] at hb
    have hmax : l.length ≤ l.toFinset.card * 58 := by simpa using hb
    omega
  obtain ⟨⟨d,e⟩,hz,hn⟩ := high
  obtain ⟨⟨hd0,hdb⟩,⟨he0,heb⟩,hg⟩ := hv _ (List.mem_toFinset.mp hz)
  exact ⟨l,d,e,hs,hn,hd0,hdb,he0,heb,hg⟩

end MagnanimousProduct

/-! # Finiteness under every decimal cut product followed by addition of one -/

namespace MagnanimousProduct

def admissible (w : List ℕ) : Prop :=
  ∀ bs : List (List ℕ), bs.flatten=w → (∀ c ∈ bs, c≠[]) → ((bs.map value).prod+1).Prime

private theorem flatten_singles (w : List ℕ) : (w.map (fun a => [a])).flatten=w := by
  induction w with
  | nil => rfl
  | cons x xs ih => simp [List.flatten_cons,ih]

theorem no_zero {w : List ℕ} (h : admissible w) : 0 ∉ w := by
  let bs := w.map (fun a => [a])
  have hf : bs.flatten=w := flatten_singles w
  have hn : ∀ c ∈ bs, c≠[] := by simp [bs]
  have hp := h bs hf hn
  have hmap : bs.map value=w := by simp [bs,List.map_map,Function.comp_def,value]
  rw [hmap] at hp
  intro hz
  have hz' := List.prod_eq_zero hz
  exact Nat.not_prime_one (by simpa [hz'] using hp)

theorem length_lt {w : List ℕ} (ha : admissible w) (hs : ∀ x ∈ w, x<10) :
    w.length < 23204 := by
  by_contra! hl
  have hd : ∀ x ∈ w, 0<x ∧ x<10 := by
    intro x hx
    exact ⟨Nat.pos_of_ne_zero (fun he => no_zero ha (he ▸ hx)),hs x hx⟩
  obtain ⟨l,d,e,hstrip,hcount,hd0,hd10,he0,he10,hg⟩ := long_strip hd hl
  obtain ⟨rest,hm⟩ := select_pairs hstrip hcount
  have hr : ∀ x ∈ rest, 0<x ∧ x<10 := fun x hx => hd x (rest_subset hm x hx)
  obtain ⟨t,_,ht,hbad⟩ := Table.composite_choice hd0 hd10 he0 he10 hg rest hr
  obtain ⟨bs,hf,hn,hval⟩ := realize hm ht
  have hp := ha bs hf hn
  exact hbad (hval ▸ hp)

theorem finite_all_products :
    {n : ℕ | 0 < n ∧ admissible (Nat.digits 10 n).reverse}.Finite := by
  apply (Set.finite_Iio (10^(23204 : ℕ) : ℕ)).subset
  intro n hn
  have hd : ∀ x ∈ (Nat.digits 10 n).reverse, x<10 :=
    fun _ h => Nat.digits_lt_base (by decide) (List.mem_reverse.mp h)
  exact (Nat.digits_length_le_iff (by decide : 1<10) n).mp
    (by simpa using (length_lt hn.2 hd).le)

end MagnanimousProduct

namespace ProductEnumeration
open MagnanimousProduct

def CutProduct (w : List ℕ) (v : ℕ) : Prop :=
  ∃ bs : List (List ℕ), bs.flatten = w ∧ (∀ c ∈ bs, c ≠ []) ∧ (bs.map value).prod = v

private theorem value_append (a b : List ℕ) :
    value (a ++ b) = value b + 10 ^ b.length * value a := by
  simp [value,List.reverse_append,Nat.ofDigits_append]

/-- The trailing block has value divisible by p. All closed blocks have nonzero
product modulo p. A new digit either extends the trailing block or closes it. -/
private theorem split_prefix {p : ℕ} (hp : p.Prime) (pre : List ℕ) :
    ∃ (bs : List (List ℕ)) (z : List ℕ),
      bs.flatten ++ z = pre ∧ (∀ c ∈ bs, c ≠ []) ∧ ¬ p ∣ (bs.map value).prod ∧ p ∣ value z := by
  induction pre using List.reverseRecOn with
  | nil => exact ⟨[],[],rfl,by simp,by simpa using hp.not_dvd_one,by simp [value]⟩
  | append_singleton pre d ih =>
    obtain ⟨bs,z,hf,hn,hu,hz⟩ := ih
    have hh : value (z ++ [d]) = d + 10 * value z := by simp [value,Nat.ofDigits_cons]
    have hz' : p ∣ 10 * value z := dvd_mul_of_dvd_right hz _
    by_cases hd : p ∣ d
    · exact ⟨bs,z++[d],by simp [←hf],hn,hu,hh ▸ dvd_add hd hz'⟩
    · have hz'' : ¬p ∣ value (z++[d]) := by
        rw [hh]
        intro hb
        exact hd ((Nat.dvd_add_iff_left hz').mpr hb)
      refine ⟨bs++[z++[d]],[],by simp [←hf],?_,?_,by simp [value]⟩
      · intro c hc
        rcases List.mem_append.mp hc with hm|hm
        · exact hn c hm
        · obtain rfl : c = z++[d] := by simpa using hm
          simp
      · simpa only [List.map_append,List.map_singleton,List.prod_append,List.prod_singleton,
          hp.dvd_mul,not_or] using And.intro hu hz''

private theorem lift_product {w z : List ℕ} {v p : ℕ} (bs : List (List ℕ))
    (hn : ∀ c ∈ bs, c ≠ []) (hw : w ≠ []) (h : CutProduct w v)
    (hz : ∀ c : List ℕ, c ≠ [] → p ∣ 10 ^ c.length * value z) :
    ∃ t, CutProduct ((bs.flatten ++ z) ++ w) t ∧ (bs.map value).prod * v ≤ t ∧
      t % p = ((bs.map value).prod * v) % p := by
  obtain ⟨cs,hf,hcs,hv⟩ := h
  cases cs with
  | nil => exact (hw (by simpa using hf.symm)).elim
  | cons c cs =>
    have hc := hcs c (by simp)
    let t := (bs.map value).prod * (value (z++c) * (cs.map value).prod)
    refine ⟨t,⟨bs++(z++c)::cs,?_,?_,by simp [t]⟩,?_,?_⟩
    · simp [←hf,List.append_assoc]
    · intro d hm
      rcases List.mem_append.mp hm with hm|hm
      · exact hn d hm
      · rcases List.mem_cons.mp hm with rfl|hm
        · simpa using fun h : z=[] ∧ c=[] => hc h.2
        · exact hcs d (by simp [hm])
    · simp only [List.map_cons,List.prod_cons] at hv
      rw [←hv]
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by rw [value_append]; omega))
    · obtain ⟨j,hj⟩ := hz c hc
      simp only [List.map_cons,List.prod_cons] at hv
      rw [←hv]
      have he : t = (bs.map value).prod * (value c * (cs.map value).prod) +
          p * ((bs.map value).prod * j * (cs.map value).prod) := by
        simp only [t,value_append,hj]
        ring
      simp [he]

private theorem reject {p t : ℕ} {w : List ℕ} (hp : p.Prime) (ht : p ≤ t)
    (hm : (t+1)%p=0) (h : CutProduct w t) : ¬ admissible w := by
  obtain ⟨cs,hf,hn,rfl⟩ := h
  intro ha
  rcases (ha cs hf hn).eq_one_or_self_of_dvd _ (Nat.dvd_of_mod_eq_zero hm) with h|h
  · exact hp.ne_one h
  · omega

theorem blocked_prime {p : ℕ} {w : List ℕ} (hp : p.Prime) (hw : w ≠ [])
    (h : ∀ a : ℕ, 0<a → a<p → ∃ v : ℕ, CutProduct w v ∧ p≤v ∧ (a*v+1)%p=0)
    (pre : List ℕ) : ¬admissible (pre++w) := by
  obtain ⟨bs,z,hf,hn,hu,hz⟩ := split_prefix hp pre
  let a := (bs.map value).prod
  change ¬p ∣ a at hu
  have hpos : 0<a := Nat.pos_of_ne_zero (fun he => hu (by rw [he]; exact dvd_zero _))
  have ham : 0<a%p := Nat.pos_of_ne_zero (fun he => hu (Nat.dvd_of_mod_eq_zero he))
  obtain ⟨v,hv,hle,hm⟩ := h (a%p) ham (Nat.mod_lt _ hp.pos)
  obtain ⟨t,ht,hlt,htm⟩ := lift_product bs hn hw hv (fun c _ => dvd_mul_of_dvd_right hz _)
  have hgood : (t+1)%p=0 := by
    change Nat.ModEq p t (a*v) at htm
    have he := (htm.trans ((Nat.mod_modEq a p).symm.mul_right v)).add_right 1
    exact Eq.trans he hm
  rw [←hf]
  exact reject hp (hle.trans ((Nat.le_mul_of_pos_left v hpos).trans hlt)) hgood ht

theorem blocked_five {w : List ℕ} (hw : w ≠ [])
    (h : ∃ v : ℕ, CutProduct w v ∧ 5≤v ∧ (v+1)%5=0)
    (pre : List ℕ) : ¬admissible (pre++w) := by
  obtain ⟨v,hv,hle,hm⟩ := h
  have hz (c : List ℕ) (hc : c≠[]) : 5 ∣ 10^c.length * value pre := by
    cases c with
    | nil => contradiction
    | cons d ds =>
      simp only [List.length_cons,pow_succ]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by decide : 5∣10) _) _
  obtain ⟨t,ht,hlt,htm⟩ := lift_product [] (by simp) hw hv hz
  simp only [List.map_nil,List.prod_nil,one_mul,List.flatten_nil,List.nil_append] at ht hlt htm
  exact reject (by decide : Nat.Prime 5) (hle.trans hlt)
    (by calc (t+1)%5 = (t%5+1)%5 := by simp
             _ = (v+1)%5 := by rw [htm]; simp
             _ = 0 := hm) ht

end ProductEnumeration

namespace ProductEnumeration
open MagnanimousProduct

/-- Prepend the digit as a singleton, or join it to the first existing block. -/
private def prependCut (a : ℕ) (bs : List (List ℕ)) : List (List (List ℕ)) :=
  ([a] :: bs) :: match bs with
    | [] => []
    | c :: cs => [(a :: c) :: cs]

def allProductCuts : List ℕ → List (List (List ℕ))
  | [] => [[]]
  | a :: w => (allProductCuts w).flatMap (prependCut a)

private theorem mem_allProductCuts {w : List ℕ} {bs : List (List ℕ)} (hf : bs.flatten = w)
    (hn : ∀ b ∈ bs, b ≠ []) : bs ∈ allProductCuts w := by
  induction w generalizing bs with
  | nil =>
    cases bs with
    | nil => simp [allProductCuts]
    | cons b bs =>
      have hb := hn b (by simp)
      simp only [List.flatten_cons, List.append_eq_nil_iff] at hf
      exact (hb hf.1).elim
  | cons a w ih =>
    cases bs with
    | nil => simp at hf
    | cons b bs =>
      have hb := hn b (by simp)
      have hs : ∀ c ∈ bs, c ≠ [] := fun c hc => hn c (by simp [hc])
      cases b with
      | nil => exact (hb rfl).elim
      | cons b rest =>
        simp only [List.flatten_cons, List.cons_append, List.cons.injEq] at hf
        obtain ⟨rfl, hrest⟩ := hf
        apply List.mem_flatMap.mpr
        cases rest with
        | nil =>
          refine ⟨bs, ih (by simpa using hrest) hs, ?_⟩
          simp [prependCut]
        | cons d ds =>
          have htail : ∀ c ∈ (d :: ds) :: bs, c ≠ [] := by
            intro c hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact List.cons_ne_nil _ _
            · exact hs c hc
          refine ⟨(d :: ds) :: bs, ih (by simpa using hrest) htail, ?_⟩
          simp [prependCut]


private theorem allProductCuts_valid {w : List ℕ} {bs : List (List ℕ)}
    (h : bs ∈ allProductCuts w) : bs.flatten=w ∧ ∀ b ∈ bs, b ≠ [] := by
  induction w generalizing bs with
  | nil =>
    simp only [allProductCuts,List.mem_singleton] at h
    subst bs
    simp
  | cons a w ih =>
    obtain ⟨t,ht,hb⟩ := List.mem_flatMap.mp h
    obtain ⟨hf,hn⟩ := ih ht
    cases t with
    | nil =>
      simp only [prependCut,List.mem_singleton] at hb
      subst bs
      simp_all
    | cons c cs =>
      simp only [prependCut,List.mem_cons,List.not_mem_nil,or_false] at hb
      rcases hb with rfl | rfl
      · simp_all
      · refine ⟨congrArg (List.cons a) hf, ?_⟩
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact List.cons_ne_nil _ _
        · exact hn b (List.mem_cons_of_mem _ hb)

def cutValues (w : List ℕ) : List ℕ :=
  (allProductCuts w).map fun bs => (bs.map value).prod

theorem mem_cutValues {w : List ℕ} {v : ℕ} :
    v ∈ cutValues w ↔ ∃ bs : List (List ℕ),
      bs.flatten=w ∧ (∀ c∈bs, c≠[]) ∧ (bs.map value).prod=v := by
  constructor
  · intro h
    obtain ⟨bs,hb,hv⟩ := List.mem_map.mp h
    obtain ⟨hf,hn⟩ := allProductCuts_valid hb
    exact ⟨bs,hf,hn,hv⟩
  · rintro ⟨bs,hf,hn,hv⟩
    exact List.mem_map.mpr ⟨bs,mem_allProductCuts hf hn,hv⟩

def termList : List ℕ :=
  [1,2,4,6,12,16,22,28,36,52,58,66,82,112,136,166,256,352,556,562,586,616,652,658]

end ProductEnumeration

namespace ProductEnumeration
open MagnanimousProduct

def moduli : List ℕ := [2,3,7,11,13,17,19]

/-- Test each possible nonzero multiplier of the suffix product. -/
def covers (p : ℕ) (vs : List ℕ) : Bool :=
  decide (p ≤ vs.length+1) && (List.range (p-1)).all fun j =>
    vs.any fun v => decide (p ≤ v) && ((j+1)*v+1)%p == 0

def five (vs : List ℕ) : Bool :=
  vs.any fun v => decide (5 ≤ v) && (v+1)%5 == 0

def blocked (w : List ℕ) : Bool :=
  let vs := cutValues w
  five vs || moduli.any (fun p => covers p vs)

def divisors : List ℕ := [2,3,5,7,11,13,17,19,23,29]

def compositeWitness (v : ℕ) : Bool :=
  divisors.any fun d => decide (1 < d ∧ d < v+1) && (v+1)%d == 0

def terminal (w : List ℕ) : Bool :=
  termList.contains (value w) || (cutValues w).any compositeWitness

end ProductEnumeration

namespace ProductEnumeration
open MagnanimousProduct

private theorem moduli_prime {p : ℕ} (hp : p ∈ moduli) : p.Prime := by
  simp only [moduli,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem blocked_sound {w : List ℕ} (hw : w ≠ []) (h : blocked w = true)
    (pre : List ℕ) : ¬admissible (pre++w) := by
  rcases Bool.or_eq_true_iff.mp h with hf | hm
  · obtain ⟨v,hv,hh⟩ := List.any_eq_true.mp hf
    have hh' : 5 ≤ v ∧ (v+1)%5=0 := by simpa using hh
    exact blocked_five hw ⟨v,mem_cutValues.mp hv,hh'⟩ pre
  · obtain ⟨p,hp,hc⟩ := List.any_eq_true.mp hm
    apply blocked_prime (moduli_prime hp) hw _ pre
    intro a ha ha'
    have hj : a-1 ∈ List.range (p-1) := List.mem_range.mpr (by omega)
    have hx := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hc).2 _ hj
    obtain ⟨v,hv,hh⟩ := List.any_eq_true.mp hx
    have hh' : p ≤ v ∧ ((a-1+1)*v+1)%p = 0 := by simpa using hh
    rw [show a-1+1=a by omega] at hh'
    exact ⟨v,mem_cutValues.mp hv,hh'⟩

theorem terminal_sound {w : List ℕ} (ht : terminal w = true) (ha : admissible w) :
    value w ∈ termList := by
  rcases Bool.or_eq_true_iff.mp ht with hm | hc
  · simpa using hm
  · obtain ⟨v,hv,hh⟩ := List.any_eq_true.mp hc
    obtain ⟨bs,hf,hn,e⟩ := mem_cutValues.mp hv
    have hprime := ha bs hf hn
    rw [e] at hprime
    obtain ⟨d,_,hd⟩ := List.any_eq_true.mp hh
    have : (1 < d ∧ d < v+1) ∧ (v+1)%d=0 := by simpa using hd
    exact ((Nat.dvd_prime hprime).mp (Nat.dvd_of_mod_eq_zero this.2)).elim
      (fun he => (by omega : False).elim) (fun he => (by omega : False).elim)

end ProductEnumeration

namespace ProductEnumeration
open MagnanimousProduct

def walk (blocked terminal : List ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, w => if blocked w then true else terminal w && false
  | k+1, w => if blocked w then true else terminal w &&
      ([1,2,3,4,5,6,7,8,9] : List ℕ).all (fun d => walk blocked terminal k (d::w))

/-- A closed suffix tree covers every length of prefix, including prefixes longer
than its recursion depth: every path at exhausted fuel must be blocked. -/
theorem walk_sound {blocked terminal : List ℕ → Bool} {terms : List ℕ}
    (hblock : ∀ {w : List ℕ}, w ≠ [] → blocked w = true → ∀ pre, ¬admissible (pre++w))
    (hterm : ∀ {w : List ℕ}, terminal w = true → admissible w → value w ∈ terms)
    (pre : List ℕ) (hd : ∀ d ∈ pre, d ∈ ([1,2,3,4,5,6,7,8,9] : List ℕ)) :
    ∀ (k : ℕ) (w : List ℕ), w≠[] → admissible (pre++w) →
      walk blocked terminal k w = true → value (pre++w) ∈ terms := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro k w hw ha hc
    simp only [List.nil_append] at ha ⊢
    cases hb : blocked w
    · cases k <;> simp [walk,hb] at hc
      exact hterm hc.1 ha
    · exact (hblock hw hb [] (by simpa using ha)).elim
  | append_singleton pre d ih =>
    intro k w hw ha hc
    cases hb : blocked w
    · cases k with
      | zero => simp [walk,hb] at hc
      | succ k =>
        have hh := List.all_eq_true.mp ((Bool.and_eq_true_iff.mp
          (by simpa only [walk,hb,Bool.false_eq_true,if_false] using hc)).2)
        have hd' := hd d (by simp)
        have hpre : ∀ x ∈ pre, x ∈ ([1,2,3,4,5,6,7,8,9] : List ℕ) :=
          fun x hx => hd x (List.mem_append_left _ hx)
        simpa [List.append_assoc] using ih hpre k (d::w) (List.cons_ne_nil _ _) 
          (by simpa [List.append_assoc] using ha) (hh d hd')
    · exact (hblock hw hb _ ha).elim

theorem nat_mem_of_checked_roots {blocked terminal : List ℕ → Bool} {terms : List ℕ}
    (hblock : ∀ {w : List ℕ}, w ≠ [] → blocked w = true → ∀ pre, ¬admissible (pre++w))
    (hterm : ∀ {w : List ℕ}, terminal w = true → admissible w → value w ∈ terms)
    {k : ℕ} (hroots : ∀ d ∈ ([1,2,3,4,5,6,7,8,9] : List ℕ), walk blocked terminal k [d] = true)
    {n : ℕ} (hn : 0<n) (ha : admissible (Nat.digits 10 n).reverse) : n∈terms := by
  have hv : value (Nat.digits 10 n).reverse = n := by simp [value,Nat.ofDigits_digits]
  have hz : 0 ∉ (Nat.digits 10 n).reverse := no_zero ha
  have hd (x : ℕ) (hx : x∈Nat.digits 10 n) : x ∈ ([1,2,3,4,5,6,7,8,9] : List ℕ) := by
    have hlt := Nat.digits_lt_base (by decide : 1<10) hx
    have hne : x ≠ 0 := fun e => hz (List.mem_reverse.mpr (e ▸ hx))
    interval_cases x <;> simp_all
  cases he : Nat.digits 10 n with
  | nil => exact ((Nat.digits_ne_nil_iff_ne_zero.mpr hn.ne') he).elim
  | cons d ds =>
    rw [he,List.reverse_cons] at ha hv
    rw [he] at hd
    apply hv ▸ walk_sound hblock hterm ds.reverse _ k [d] (by simp) ha (hroots d (hd d (by simp)))
    exact fun x hx => hd x (List.mem_cons_of_mem _ (List.mem_reverse.mp hx))

end ProductEnumeration

namespace ProductEnumeration

private theorem allExtensions {k : ℕ} {w : List ℕ}
    (checks : ∀ d : Fin 9, walk blocked terminal k ((d.val + 1) :: w) = true) :
    ([1,2,3,4,5,6,7,8,9] : List ℕ).all (fun d => walk blocked terminal k (d::w)) = true := by
  apply List.all_eq_true.mpr
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  have range : 0 < d ∧ d ≤ 9 := by
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have index : d - 1 + 1 = d := by omega
  simpa only [index] using checks ⟨d - 1, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix1 : walk blocked terminal 7 [1] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions12 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [1,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix12 : walk blocked terminal 6 [1,2] = true := by
  have hb : blocked [1,2] = false := by decide +kernel
  have ht : terminal [1,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix22 : walk blocked terminal 6 [2,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions32 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [3,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix32 : walk blocked terminal 6 [3,2] = true := by
  have hb : blocked [3,2] = false := by decide +kernel
  have ht : terminal [3,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix42 : walk blocked terminal 6 [4,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix152 : walk blocked terminal 5 [1,5,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix252 : walk blocked terminal 5 [2,5,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions352 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [3,5,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix352 : walk blocked terminal 5 [3,5,2] = true := by
  have hb : blocked [3,5,2] = false := by decide +kernel
  have ht : terminal [3,5,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions352

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix452 : walk blocked terminal 5 [4,5,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix552 : walk blocked terminal 5 [5,5,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions652 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [6,5,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix652 : walk blocked terminal 5 [6,5,2] = true := by
  have hb : blocked [6,5,2] = false := by decide +kernel
  have ht : terminal [6,5,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions652

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix752 : walk blocked terminal 5 [7,5,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix852 : walk blocked terminal 5 [8,5,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions952 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [9,5,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix952 : walk blocked terminal 5 [9,5,2] = true := by
  have hb : blocked [9,5,2] = false := by decide +kernel
  have ht : terminal [9,5,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions952

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix52 : walk blocked terminal 6 [5,2] = true := by
  have hb : blocked [5,2] = false := by decide +kernel
  have ht : terminal [5,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix152, suffix252, suffix352, suffix452, suffix552, suffix652, suffix752, suffix852, suffix952, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix162 : walk blocked terminal 5 [1,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix262 : walk blocked terminal 5 [2,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix362 : walk blocked terminal 5 [3,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix462 : walk blocked terminal 5 [4,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions562 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [5,6,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix562 : walk blocked terminal 5 [5,6,2] = true := by
  have hb : blocked [5,6,2] = false := by decide +kernel
  have ht : terminal [5,6,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions562

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix662 : walk blocked terminal 5 [6,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix762 : walk blocked terminal 5 [7,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix862 : walk blocked terminal 5 [8,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix962 : walk blocked terminal 5 [9,6,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix62 : walk blocked terminal 6 [6,2] = true := by
  have hb : blocked [6,2] = false := by decide +kernel
  have ht : terminal [6,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix162, suffix262, suffix362, suffix462, suffix562, suffix662, suffix762, suffix862, suffix962, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix72 : walk blocked terminal 6 [7,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions82 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [8,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix82 : walk blocked terminal 6 [8,2] = true := by
  have hb : blocked [8,2] = false := by decide +kernel
  have ht : terminal [8,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions82

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix192 : walk blocked terminal 5 [1,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix292 : walk blocked terminal 5 [2,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix392 : walk blocked terminal 5 [3,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix492 : walk blocked terminal 5 [4,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix592 : walk blocked terminal 5 [5,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions692 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [6,9,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix692 : walk blocked terminal 5 [6,9,2] = true := by
  have hb : blocked [6,9,2] = false := by decide +kernel
  have ht : terminal [6,9,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions692

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix792 : walk blocked terminal 5 [7,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix892 : walk blocked terminal 5 [8,9,2] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions992 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [9,9,2]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix992 : walk blocked terminal 5 [9,9,2] = true := by
  have hb : blocked [9,9,2] = false := by decide +kernel
  have ht : terminal [9,9,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions992

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix92 : walk blocked terminal 6 [9,2] = true := by
  have hb : blocked [9,2] = false := by decide +kernel
  have ht : terminal [9,2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix192, suffix292, suffix392, suffix492, suffix592, suffix692, suffix792, suffix892, suffix992, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix2 : walk blocked terminal 7 [2] = true := by
  have hb : blocked [2] = false := by decide +kernel
  have ht : terminal [2] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix12, suffix22, suffix32, suffix42, suffix52, suffix62, suffix72, suffix82, suffix92, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix3 : walk blocked terminal 7 [3] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix4 : walk blocked terminal 7 [4] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix5 : walk blocked terminal 7 [5] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions16 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [1,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix16 : walk blocked terminal 6 [1,6] = true := by
  have hb : blocked [1,6] = false := by decide +kernel
  have ht : terminal [1,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix126 : walk blocked terminal 5 [1,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix226 : walk blocked terminal 5 [2,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix326 : walk blocked terminal 5 [3,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix426 : walk blocked terminal 5 [4,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions526 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [5,2,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix526 : walk blocked terminal 5 [5,2,6] = true := by
  have hb : blocked [5,2,6] = false := by decide +kernel
  have ht : terminal [5,2,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions526

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix626 : walk blocked terminal 5 [6,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix726 : walk blocked terminal 5 [7,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix826 : walk blocked terminal 5 [8,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix926 : walk blocked terminal 5 [9,2,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix26 : walk blocked terminal 6 [2,6] = true := by
  have hb : blocked [2,6] = false := by decide +kernel
  have ht : terminal [2,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix126, suffix226, suffix326, suffix426, suffix526, suffix626, suffix726, suffix826, suffix926, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix136 : walk blocked terminal 5 [1,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix236 : walk blocked terminal 5 [2,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix336 : walk blocked terminal 5 [3,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix436 : walk blocked terminal 5 [4,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix536 : walk blocked terminal 5 [5,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions636 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [6,3,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix636 : walk blocked terminal 5 [6,3,6] = true := by
  have hb : blocked [6,3,6] = false := by decide +kernel
  have ht : terminal [6,3,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions636

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix736 : walk blocked terminal 5 [7,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix836 : walk blocked terminal 5 [8,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix936 : walk blocked terminal 5 [9,3,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix36 : walk blocked terminal 6 [3,6] = true := by
  have hb : blocked [3,6] = false := by decide +kernel
  have ht : terminal [3,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix136, suffix236, suffix336, suffix436, suffix536, suffix636, suffix736, suffix836, suffix936, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix46 : walk blocked terminal 6 [4,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix156 : walk blocked terminal 5 [1,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix256 : walk blocked terminal 5 [2,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions356 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [3,5,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix356 : walk blocked terminal 5 [3,5,6] = true := by
  have hb : blocked [3,5,6] = false := by decide +kernel
  have ht : terminal [3,5,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions356

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix456 : walk blocked terminal 5 [4,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions556 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [5,5,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix556 : walk blocked terminal 5 [5,5,6] = true := by
  have hb : blocked [5,5,6] = false := by decide +kernel
  have ht : terminal [5,5,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions556

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix1656 : walk blocked terminal 4 [1,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix2656 : walk blocked terminal 4 [2,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix3656 : walk blocked terminal 4 [3,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix4656 : walk blocked terminal 4 [4,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix5656 : walk blocked terminal 4 [5,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions6656 (d : Fin 9) :
    walk blocked terminal 3 ((d.val + 1) :: [6,6,5,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix6656 : walk blocked terminal 4 [6,6,5,6] = true := by
  have hb : blocked [6,6,5,6] = false := by decide +kernel
  have ht : terminal [6,6,5,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions6656

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix7656 : walk blocked terminal 4 [7,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix8656 : walk blocked terminal 4 [8,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix9656 : walk blocked terminal 4 [9,6,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix656 : walk blocked terminal 5 [6,5,6] = true := by
  have hb : blocked [6,5,6] = false := by decide +kernel
  have ht : terminal [6,5,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix1656, suffix2656, suffix3656, suffix4656, suffix5656, suffix6656, suffix7656, suffix8656, suffix9656, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix756 : walk blocked terminal 5 [7,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix856 : walk blocked terminal 5 [8,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix956 : walk blocked terminal 5 [9,5,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix56 : walk blocked terminal 6 [5,6] = true := by
  have hb : blocked [5,6] = false := by decide +kernel
  have ht : terminal [5,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix156, suffix256, suffix356, suffix456, suffix556, suffix656, suffix756, suffix856, suffix956, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix166 : walk blocked terminal 5 [1,6,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions266 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [2,6,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix266 : walk blocked terminal 5 [2,6,6] = true := by
  have hb : blocked [2,6,6] = false := by decide +kernel
  have ht : terminal [2,6,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions266

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix366 : walk blocked terminal 5 [3,6,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix466 : walk blocked terminal 5 [4,6,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions566 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [5,6,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix566 : walk blocked terminal 5 [5,6,6] = true := by
  have hb : blocked [5,6,6] = false := by decide +kernel
  have ht : terminal [5,6,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions566

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions666 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [6,6,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix666 : walk blocked terminal 5 [6,6,6] = true := by
  have hb : blocked [6,6,6] = false := by decide +kernel
  have ht : terminal [6,6,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions666

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix766 : walk blocked terminal 5 [7,6,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix866 : walk blocked terminal 5 [8,6,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix966 : walk blocked terminal 5 [9,6,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix66 : walk blocked terminal 6 [6,6] = true := by
  have hb : blocked [6,6] = false := by decide +kernel
  have ht : terminal [6,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix166, suffix266, suffix366, suffix466, suffix566, suffix666, suffix766, suffix866, suffix966, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions76 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [7,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix76 : walk blocked terminal 6 [7,6] = true := by
  have hb : blocked [7,6] = false := by decide +kernel
  have ht : terminal [7,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions76

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions86 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [8,6]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix86 : walk blocked terminal 6 [8,6] = true := by
  have hb : blocked [8,6] = false := by decide +kernel
  have ht : terminal [8,6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions86

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix96 : walk blocked terminal 6 [9,6] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix6 : walk blocked terminal 7 [6] = true := by
  have hb : blocked [6] = false := by decide +kernel
  have ht : terminal [6] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix16, suffix26, suffix36, suffix46, suffix56, suffix66, suffix76, suffix86, suffix96, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix7 : walk blocked terminal 7 [7] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix18 : walk blocked terminal 6 [1,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions28 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [2,8]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix28 : walk blocked terminal 6 [2,8] = true := by
  have hb : blocked [2,8] = false := by decide +kernel
  have ht : terminal [2,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions28

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix38 : walk blocked terminal 6 [3,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix48 : walk blocked terminal 6 [4,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions58 (d : Fin 9) :
    walk blocked terminal 5 ((d.val + 1) :: [5,8]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix58 : walk blocked terminal 6 [5,8] = true := by
  have hb : blocked [5,8] = false := by decide +kernel
  have ht : terminal [5,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions58

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix168 : walk blocked terminal 5 [1,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix268 : walk blocked terminal 5 [2,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix368 : walk blocked terminal 5 [3,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix468 : walk blocked terminal 5 [4,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix568 : walk blocked terminal 5 [5,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions668 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [6,6,8]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix668 : walk blocked terminal 5 [6,6,8] = true := by
  have hb : blocked [6,6,8] = false := by decide +kernel
  have ht : terminal [6,6,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions668

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix768 : walk blocked terminal 5 [7,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix868 : walk blocked terminal 5 [8,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix968 : walk blocked terminal 5 [9,6,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix68 : walk blocked terminal 6 [6,8] = true := by
  have hb : blocked [6,8] = false := by decide +kernel
  have ht : terminal [6,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix168, suffix268, suffix368, suffix468, suffix568, suffix668, suffix768, suffix868, suffix968, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix78 : walk blocked terminal 6 [7,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix88 : walk blocked terminal 6 [8,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix198 : walk blocked terminal 5 [1,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix298 : walk blocked terminal 5 [2,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix398 : walk blocked terminal 5 [3,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix498 : walk blocked terminal 5 [4,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix598 : walk blocked terminal 5 [5,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions698 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [6,9,8]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix698 : walk blocked terminal 5 [6,9,8] = true := by
  have hb : blocked [6,9,8] = false := by decide +kernel
  have ht : terminal [6,9,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions698

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix798 : walk blocked terminal 5 [7,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix898 : walk blocked terminal 5 [8,9,8] = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem extensions998 (d : Fin 9) :
    walk blocked terminal 4 ((d.val + 1) :: [9,9,8]) = true := by
  fin_cases d <;> decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix998 : walk blocked terminal 5 [9,9,8] = true := by
  have hb : blocked [9,9,8] = false := by decide +kernel
  have ht : terminal [9,9,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, Bool.true_and]
  exact allExtensions extensions998

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix98 : walk blocked terminal 6 [9,8] = true := by
  have hb : blocked [9,8] = false := by decide +kernel
  have ht : terminal [9,8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix198, suffix298, suffix398, suffix498, suffix598, suffix698, suffix798, suffix898, suffix998, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix8 : walk blocked terminal 7 [8] = true := by
  have hb : blocked [8] = false := by decide +kernel
  have ht : terminal [8] = true := by decide +kernel
  rw [walk,hb]
  simp only [Bool.false_eq_true, if_false, ht, List.all_cons, List.all_nil, suffix18, suffix28, suffix38, suffix48, suffix58, suffix68, suffix78, suffix88, suffix98, Bool.and_self]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem suffix9 : walk blocked terminal 7 [9] = true := by
  decide +kernel

theorem checked_roots : ∀ d ∈ ([1,2,3,4,5,6,7,8,9] : List ℕ),
    walk blocked terminal 7 [d] = true := by
  intro d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact suffix1
  · exact suffix2
  · exact suffix3
  · exact suffix4
  · exact suffix5
  · exact suffix6
  · exact suffix7
  · exact suffix8
  · exact suffix9


end ProductEnumeration

namespace ProductEnumeration
open MagnanimousProduct

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem terms_pass :
    termList.all (fun n => decide (0 < n) &&
      (cutValues (Nat.digits 10 n).reverse).all (fun v => decide (v+1).Prime)) = true := by
  decide +kernel

theorem admissible_of_mem_terms {n : ℕ} (hn : n ∈ termList) :
    0 < n ∧ admissible (Nat.digits 10 n).reverse := by
  have ht := List.all_eq_true.mp terms_pass _ hn
  simp only [Bool.and_eq_true,decide_eq_true_eq] at ht
  refine ⟨ht.1, ?_⟩
  intro bs hf he
  have hv := mem_cutValues.mpr ⟨bs,hf,he,rfl⟩
  exact of_decide_eq_true (List.all_eq_true.mp ht.2 _ hv)

end ProductEnumeration

/-! # All positive decimal integers in OEIS A089696 -/
namespace ProductEnumeration
open MagnanimousProduct

theorem classification (n : ℕ) :
    (0<n ∧ admissible (Nat.digits 10 n).reverse) ↔ n∈termList := by
  refine ⟨?_,admissible_of_mem_terms⟩
  rintro ⟨hn,ha⟩
  exact nat_mem_of_checked_roots blocked_sound terminal_sound checked_roots hn ha

theorem largest_term : IsGreatest {n : ℕ | 0<n ∧ admissible (Nat.digits 10 n).reverse} 658 := by
  refine ⟨(classification _).mpr (by decide +kernel),?_⟩
  have hmax : ∀ n ∈ termList, n ≤ 658 := by decide +kernel
  exact fun n hn => hmax _ ((classification n).mp hn)

theorem number_of_terms : {n : ℕ | 0<n ∧ admissible (Nat.digits 10 n).reverse}.ncard=24 := by
  have he : {n : ℕ | 0<n ∧ admissible (Nat.digits 10 n).reverse} =
      (↑termList.toFinset : Set ℕ) := by
    ext n
    simpa using classification n
  rw [he,Set.ncard_coe_finset]
  decide +kernel

end ProductEnumeration

theorem OMA.solution : type_of% @OMA.S_oeis_a089696.main := by
  apply (Finset.finite_toSet ProductEnumeration.termList.toFinset).subset
  intro n hn
  exact List.mem_toFinset.mpr ((ProductEnumeration.classification n).mp hn)
