import OMAStatements.S_oeis_a384132
import Mathlib

namespace FourCubes
open OMA.S_oeis_a384132
set_option maxRecDepth 16000 in
lemma exclude (k : ℕ) (hk : k∈([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ)) : ¬IsSumOfFourDistinctCubes k := by
  let masks : ℕ → ℕ×ℕ×ℕ×ℕ := Nat.rec (0,0,0,0) (fun n old =>
    let c := (n+1)^3
    (old.1 ||| (1 <<< c), old.2.1 ||| (old.1 <<< c),
     old.2.2.1 ||| (old.2.1 <<< c), old.2.2.2 ||| (old.2.2.1 <<< c)))
  have found (n : ℕ) :
    (∀ x : ℕ, 0<x → x≤n → (masks n).1.testBit (x^3)=true) ∧
    (∀ x y : ℕ, 0<x → x<y → y≤n → (masks n).2.1.testBit (x^3+y^3)=true) ∧
    (∀ x y z : ℕ, 0<x → x<y → y<z → z≤n → (masks n).2.2.1.testBit (x^3+y^3+z^3)=true) ∧
    (∀ x y z w : ℕ, 0<x → x<y → y<z → z<w → w≤n → (masks n).2.2.2.testBit (x^3+y^3+z^3+w^3)=true) := by
    induction n with
    | zero =>
      refine ⟨?_,?_,?_,?_⟩ <;> intros <;> omega
    | succ n ih =>
      obtain ⟨h1,h2,h3,h4⟩ := ih
      refine ⟨?_,?_,?_,?_⟩
      · intro x hx bound
        change ((masks n).1 ||| (_ <<< (n+1)^3)).testBit _ = true
        rw [Nat.testBit_or,Bool.or_eq_true]
        by_cases now : x=n+1
        · subst x
          right
          simp [Nat.testBit_shiftLeft]
        · exact Or.inl (h1 x hx (by omega))
      · intro x y hx hy bound
        change ((masks n).2.1 ||| (_ <<< (n+1)^3)).testBit _ = true
        rw [Nat.testBit_or,Bool.or_eq_true]
        by_cases now : y=n+1
        · subst y
          right
          simp only [Nat.testBit_shiftLeft, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
          exact h1 x hx (by omega)
        · exact Or.inl (h2 x y hx hy (by omega))
      · intro x y z hx hy hz bound
        change ((masks n).2.2.1 ||| (_ <<< (n+1)^3)).testBit _ = true
        rw [Nat.testBit_or,Bool.or_eq_true]
        by_cases now : z=n+1
        · subst z
          right
          simp only [Nat.testBit_shiftLeft, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
          exact h2 x y hx hy (by omega)
        · exact Or.inl (h3 x y z hx hy hz (by omega))
      · intro x y z w hx hy hz hw bound
        change ((masks n).2.2.2 ||| (_ <<< (n+1)^3)).testBit _ = true
        rw [Nat.testBit_or,Bool.or_eq_true]
        by_cases now : w=n+1
        · subst w
          right
          simp only [Nat.testBit_shiftLeft, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
          exact h3 x y z hx hy hz (by omega)
        · exact Or.inl (h4 x y z w hx hy hz hw (by omega))
  have table : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ).all (fun t => !(masks 120).2.2.2.testBit (t^3) && decide (t≤121))=true := by decide +kernel
  have checked : ∀ t ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ), (masks 120).2.2.2.testBit (t^3)=false ∧ t≤121 := by
    simpa using List.all_eq_true.mp table
  obtain ⟨off,small⟩ := checked k hk
  rintro ⟨x,y,z,w,hx,hy,hz,hw,he⟩
  have lim : w≤120 := by
    by_contra! high
    have hle : k≤w := by omega
    have powle := Nat.pow_le_pow_left hle 3
    have pos := Nat.pow_pos hx (n:=3)
    omega
  have hit := (found 120).2.2.2 x y z w hx hy hz hw lim
  exact Bool.noConfusion (off.symm.trans (he ▸ hit))

lemma scale {d k : ℕ} (hd : 0<d) (hk : IsSumOfFourDistinctCubes k) :
    IsSumOfFourDistinctCubes (k*d) := by
  obtain ⟨x,y,z,w,hx,hy,hz,hw,eqn⟩ := hk
  refine ⟨x*d,y*d,z*d,w*d,Nat.mul_pos hx hd,Nat.mul_lt_mul_of_pos_right hy hd,
    Nat.mul_lt_mul_of_pos_right hz hd,Nat.mul_lt_mul_of_pos_right hw hd,?_⟩
  simpa only [mul_pow,←Nat.add_mul] using congrArg (fun a => a*d^3) eqn

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
lemma basis (n : ℕ) (pos : 0<n) (off : n∉([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ))
    (finite : n≤1000 ∨ ∃ a ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ), ∃ b ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ), n=a*b) :
    IsSumOfFourDistinctCubes n := by
  let rows : List (ℕ×ℕ×ℕ×ℕ×ℕ) := [
      (13,1,5,7,12),
      (14,2,3,8,13),
      (18,4,7,8,17),
      (20,11,12,13,14),
      (23,6,14,15,18),
      (24,5,14,16,19),
      (30,13,15,21,23),
      (31,9,13,17,28),
      (32,7,8,17,30),
      (33,3,14,15,31),
      (34,11,13,24,28),
      (35,8,11,12,34),
      (37,6,16,28,29),
      (38,3,5,28,32),
      (41,5,6,21,39),
      (43,15,28,29,31),
      (44,16,24,29,35),
      (45,10,13,14,44),
      (49,2,13,33,43),
      (50,14,30,33,39),
      (51,7,16,29,47),
      (53,3,35,36,39),
      (55,17,19,28,51),
      (57,13,23,28,53),
      (59,21,23,26,55),
      (63,2,15,27,61),
      (67,7,17,43,60),
      (73,22,28,41,66),
      (75,13,23,54,63),
      (77,14,21,34,74),
      (79,7,25,47,72),
      (81,8,21,51,73),
      (83,5,7,39,80),
      (85,7,22,65,69),
      (87,14,39,54,76),
      (89,6,15,35,87),
      (94,5,28,43,90),
      (95,8,23,45,91),
      (97,1,20,42,94),
      (101,12,13,44,98),
      (103,16,20,63,94),
      (107,22,35,36,104),
      (109,14,16,61,102),
      (116,21,48,60,107),
      (119,5,32,37,117),
      (122,21,50,75,108),
      (125,7,26,63,119),
      (127,27,37,63,120),
      (131,6,20,35,130),
      (133,8,40,45,130),
      (137,39,53,77,124),
      (139,14,40,75,130),
      (141,28,36,69,134),
      (142,7,16,66,137),
      (145,13,56,57,139),
      (149,29,42,46,146),
      (151,12,25,49,149),
      (157,6,21,40,156),
      (163,12,64,70,155),
      (167,5,42,45,165),
      (173,19,41,105,158),
      (179,16,42,59,176),
      (181,45,54,84,172),
      (183,9,27,43,182),
      (187,41,52,99,175),
      (191,29,75,79,182),
      (193,44,49,82,186),
      (197,11,69,77,190),
      (199,7,74,118,180),
      (203,14,27,70,200),
      (209,20,84,130,185),
      (211,4,6,51,210),
      (213,4,59,103,203),
      (223,7,67,104,213),
      (226,7,38,46,225),
      (227,14,78,83,220),
      (229,21,26,76,226),
      (233,14,73,74,228),
      (235,22,36,91,230),
      (239,7,32,78,236),
      (241,10,38,49,240),
      (242,77,101,109,225),
      (251,41,47,91,246),
      (257,50,76,105,248),
      (263,56,72,102,255),
      (269,21,40,122,260),
      (271,12,91,111,261),
      (277,16,21,60,276),
      (281,2,18,105,276),
      (283,27,60,112,276),
      (289,37,107,136,273),
      (293,45,107,133,278),
      (305,65,74,75,301),
      (307,7,19,65,306),
      (311,68,111,144,294),
      (313,73,88,98,306),
      (317,54,91,137,305),
      (319,14,34,127,312),
      (323,39,47,53,322),
      (329,44,73,104,324),
      (331,14,16,99,328),
      (337,53,63,85,334),
      (339,59,75,112,333),
      (347,35,114,118,338),
      (349,38,69,121,343),
      (353,29,87,154,341),
      (355,56,61,103,351),
      (359,44,108,127,350),
      (361,44,55,109,357),
      (367,24,71,94,364),
      (373,56,64,93,370),
      (379,16,118,120,371),
      (383,31,66,182,368),
      (389,33,65,84,387),
      (397,21,74,208,376),
      (401,71,79,126,395),
      (409,10,41,169,399),
      (419,20,35,78,418),
      (421,10,21,193,407),
      (427,78,99,150,418),
      (431,39,48,168,422),
      (433,124,146,154,417),
      (439,34,63,66,438),
      (443,11,42,80,442),
      (449,36,132,134,441),
      (457,65,84,100,454),
      (461,56,73,89,459),
      (463,49,51,132,459),
      (467,42,129,143,459),
      (479,21,75,191,468),
      (487,16,42,151,482),
      (491,20,95,169,483),
      (493,19,79,188,483),
      (497,25,26,113,495),
      (499,13,88,93,497),
      (503,30,82,119,500),
      (509,66,77,93,507),
      (517,28,97,131,513),
      (521,81,104,185,511),
      (523,10,91,170,516),
      (541,37,46,117,539),
      (547,52,155,196,534),
      (551,47,54,162,546),
      (557,41,70,113,555),
      (563,3,20,98,562),
      (565,14,61,138,562),
      (569,72,108,182,561),
      (571,3,162,175,561),
      (577,53,55,154,573),
      (587,26,147,191,577),
      (593,89,90,156,588),
      (599,77,93,96,597),
      (601,1,52,98,600),
      (607,29,55,234,595),
      (613,35,127,208,603),
      (617,129,168,176,606),
      (619,72,91,166,614),
      (631,16,71,94,630),
      (641,11,144,189,633),
      (643,6,113,181,637),
      (647,90,170,286,623),
      (653,76,77,176,648),
      (659,11,62,102,658),
      (661,52,61,98,660),
      (671,56,90,223,662),
      (673,9,74,154,670),
      (677,13,84,152,674),
      (683,35,66,135,681),
      (691,24,115,140,688),
      (701,158,165,266,682),
      (709,88,123,231,699),
      (719,149,210,227,703),
      (727,15,119,145,724),
      (733,10,91,135,731),
      (739,28,51,114,738),
      (743,49,123,260,731),
      (751,1,73,144,749),
      (757,13,88,224,750),
      (761,32,45,217,755),
      (769,3,85,105,768),
      (773,19,132,203,767),
      (781,60,115,177,777),
      (787,67,126,318,768),
      (791,23,36,122,790),
      (797,101,130,201,791),
      (799,14,130,223,792),
      (809,23,54,197,805),
      (811,124,195,343,785),
      (821,28,204,338,797),
      (823,14,138,151,820),
      (827,155,168,214,818),
      (829,115,137,217,822),
      (839,23,26,300,826),
      (841,44,49,244,834),
      (853,18,157,209,847),
      (857,34,60,185,854),
      (859,35,190,234,850),
      (863,39,54,270,854),
      (877,78,132,261,868),
      (881,95,159,208,875),
      (883,10,78,123,882),
      (887,49,93,236,881),
      (893,66,77,274,884),
      (907,21,196,315,891),
      (911,18,38,270,903),
      (919,45,91,268,911),
      (929,16,89,230,924),
      (937,59,99,244,931),
      (941,110,133,212,936),
      (947,56,186,259,938),
      (953,53,91,233,948),
      (967,72,100,287,958),
      (971,136,231,407,941),
      (977,38,133,149,975),
      (983,62,175,296,972),
      (991,130,239,280,978),
      (997,129,145,155,994),
      (1037,2,105,227,1033),
      (1159,113,118,235,1155),
      (1207,7,237,338,1195),
      (1243,86,91,148,1242),
      (1331,179,279,406,1313),
      (1349,99,255,315,1340),
      (1363,75,342,400,1344),
      (1769,78,185,342,1764),
      (1921,3,55,280,1919),
      (2059,79,315,456,2049),
      (2147,147,290,410,2140),
      (2209,42,193,332,2206),
      (2867,179,283,357,2864),
      (3277,260,313,525,3271),
      (3337,193,297,322,3335),
      (3721,37,284,609,3715),
      (4331,83,234,350,4330),
      (5041,331,399,655,5036),
      (5311,230,280,823,5304),
      (6893,20,518,1000,6885),
      (8023,261,523,1114,8015),
      (12769,273,462,718,12768)]
  let good (t : ℕ×ℕ×ℕ×ℕ×ℕ) : Prop := let (k,x,y,z,w):=t
    0<x ∧ x<y ∧ y<z ∧ z<w ∧ x^3+y^3+z^3+w^3=k^3
  let goodDec (t) : Decidable (good t) := by dsimp [good]; infer_instance
  let covers (j : ℕ) := rows.any (fun t => decide (t.1∣j))
  have certs : rows.all (fun t => decide (good t))=true := by decide +kernel
  have small : (List.range 1001).all (fun t =>
      decide (t=0 ∨ t∈([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ)) || covers t)=true := by decide +kernel
  have pairs : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ).all (fun a => ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ).all (fun b =>
      decide (a*b ∈ ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ)) || covers (a*b)))=true := by decide +kernel
  have covered : covers n=true := by
    rcases finite with hn|⟨a,ha,b,hb,rfl⟩
    · have h := List.all_eq_true.mp small n (by simp; omega)
      simpa [off,pos.ne'] using h
    · have h := List.all_eq_true.mp (List.all_eq_true.mp pairs a ha) b hb
      simpa [off] using h
  obtain ⟨⟨k,x,y,z,w⟩,mem,dv⟩ := List.any_eq_true.mp covered
  have g : good (k,x,y,z,w) := of_decide_eq_true (List.all_eq_true.mp certs (k,x,y,z,w) mem)
  change 0<x ∧ x<y ∧ y<z ∧ z<w ∧ x^3+y^3+z^3+w^3=k^3 at g
  obtain ⟨d,hd⟩ := of_decide_eq_true dv
  change n=k*d at hd
  subst n
  have hd : 0<d := by cases d with | zero => simp at pos | succ d => omega
  exact scale hd ⟨x,y,z,w,g⟩
lemma classify (large : ∀ p : ℕ, p.Prime → 1000<p → IsSumOfFourDistinctCubes p)
    (n : ℕ) : 0<n → n∉([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ) → IsSumOfFourDistinctCubes n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro pos off
    by_cases small : n≤1000
    · exact basis n pos off (Or.inl small)
    by_cases prime : n.Prime
    · exact large n prime (by omega)
    let a := n.minFac
    let b := n/a
    have ap : a.Prime := Nat.minFac_prime (by omega)
    have alt : a<n := (Nat.not_prime_iff_minFac_lt (by omega)).mp prime
    have divide : a∣n := Nat.minFac_dvd _
    have prod : a*b=n := Nat.mul_div_cancel' divide
    have bp : 0<b := Nat.div_pos (le_of_lt alt) ap.pos
    have blt : b<n := Nat.div_lt_self pos ap.one_lt
    by_cases ma : a∈([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ)
    · by_cases mb : b∈([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ)
      · exact basis n pos off (Or.inr ⟨a,ma,b,mb,prod.symm⟩)
      · simpa [mul_comm,prod] using scale ap.pos (ih b blt bp mb)
    · simpa [prod] using scale bp (ih a alt ap.pos ma)
end FourCubes
namespace OMA.R_oeis_a384132_R2
open OMA.S_oeis_a384132
def H1 : Prop := ∀ p : ℕ, p.Prime → 1000<p → p%3=1 → IsSumOfFourDistinctCubes p
def H2 : Prop := ∀ p : ℕ, p.Prime → 1000<p → p%3=2 → IsSumOfFourDistinctCubes p
theorem main : H1 → H2 → type_of% @OMA.S_oeis_a384132.main := by
  intro h1 h2
  have large (p : ℕ) (hp : p.Prime) (bound : 1000<p) : IsSumOfFourDistinctCubes p := by
    by_cases one : p%3=1
    · exact h1 p hp bound one
    apply h2 p hp bound
    have nz : ¬3∣p := by
      intro dv
      have := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) hp).mp dv
      omega
    have := Nat.mod_lt p (by decide : 0<3)
    omega
  refine ⟨⟨by decide,FourCubes.exclude 121 (by decide)⟩,?_⟩
  intro n hn
  by_contra! high
  have bound : ∀ k∈([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ), k≤121 := by
    have h : ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 19, 21, 22, 25, 27, 29, 47, 58, 61, 71, 113, 121] : List ℕ).all (fun t => decide (t≤121))=true := by decide
    simpa using List.all_eq_true.mp h
  exact hn.2 (FourCubes.classify large n hn.1 (fun mem => (not_le.mpr high) (bound n mem)))
end OMA.R_oeis_a384132_R2
