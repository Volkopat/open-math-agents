import OMAReductions.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1
import Mathlib

/-! Finite verification of the Dusart prime-counting bound from 60,184 to five
million. The segmented sieve from Marcus Buffett's companion five-million
anchor proof (open-math-agents PR 5564) supplies upper bounds for the prime
counts. On each interval we bound the logarithm at the upper endpoint by
the Taylor polynomial for the exponential through degree eight, evaluated
at one thirty-second of the desired bound and raised to the thirty-second power. -/

namespace Sieve930
def period (d : ℕ) : ℕ → ℕ
  | 0 => 1
  | k+1 => let w := period d k; w ||| (w <<< (d * 2^k))

theorem period_sound (d k i : ℕ) (h : (period d k).testBit i = true) : d ∣ i := by
  induction k generalizing i with
  | zero =>
    change (2^0 : ℕ).testBit i = true at h
    rw [Nat.testBit_two_pow, decide_eq_true_eq] at h
    subst i
    exact dvd_zero d
  | succ k ih =>
    simp only [period, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hi,h⟩
    · exact ih _ h
    · have hd := dvd_add (ih _ h) (dvd_mul_right d (2^k))
      rwa [Nat.sub_add_cancel hi] at hd

def bits (a len : ℕ) : List ℕ → ℕ
  | [] => 0
  | d::ds => (if 2 ≤ d ∧ d < a then
      (period d ((len / d + 2).log2 + 1)) >>> (a % d) else 0) ||| bits a len ds

theorem bits_sound {a len i : ℕ} (hp : (a+i).Prime) (ds : List ℕ) :
    (bits a len ds).testBit i = false := by
  induction ds with
  | nil => simp [bits]
  | cons d ds ih =>
    simp only [bits, Nat.testBit_or, ih, Bool.or_false]
    split_ifs with hd
    · simp only [Nat.testBit_shiftRight]
      apply Bool.eq_false_iff.mpr
      intro h
      have hmod := period_sound _ _ _ h
      have hdiv : d ∣ a+i := by
        have h' := dvd_add hmod (dvd_mul_right d (a / d))
        rwa [show a % d + i + d * (a / d) = a+i by
          have := Nat.mod_add_div a d; omega] at h'
      rcases (Nat.dvd_prime hp).mp hdiv with h | h <;> omega
    · simp

def alive (a len : ℕ) (ds : List ℕ) := (2^len - 1) ^^^ ((bits a len ds) % 2^len)

theorem alive_prime {a len i : ℕ} (hi : i < len) (hp : (a+i).Prime) (ds : List ℕ) :
    (alive a len ds).testBit i = true := by
  simp [alive, hi, bits_sound hp ds]

def pc (x n : ℕ) : ℕ := ((Finset.range n).filter (fun i => x.testBit i)).card

theorem pc_split (x n k : ℕ) : pc x (k+n) = pc x k + pc (x >>> k) n := by
  simp only [pc, Finset.card_filter]
  rw [Finset.sum_range_add]
  simp [Nat.testBit_shiftRight]

theorem pc_low (x k : ℕ) : pc x k = pc (x % 2^k) k := by
  unfold pc
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Nat.testBit_mod_two_pow, Bool.and_eq_true,
    decide_eq_true_eq]
  tauto

def nibble : ℕ → ℕ := fun x => (0x4332322132212110 >>> (4*x)) % 16

theorem nibble_ok (x : ℕ) (h : x < 16) : pc x 4 = nibble x := by
  interval_cases x <;> decide

def pop : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n+1, x => nibble (x%16) + pop n (x >>> 4)

theorem pc_pop (x n : ℕ) : pc x (4*n) = pop n x := by
  induction n generalizing x with
  | zero => simp [pc, pop]
  | succ n ih =>
    rw [show 4*(n+1) = 4+4*n by omega, pc_split, pc_low x 4, show (2:ℕ)^4=16 by decide, nibble_ok _ (Nat.mod_lt _ (by decide)), ih]
    rfl

end Sieve930


namespace Sieve930
open Finset

theorem count_le (a len : ℕ) (ds : List ℕ) :
    ((range len).filter (fun i => (a+i).Prime)).card ≤
    pop ((len+3)/4) (alive a len ds) := by
  rw [← pc_pop]
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hp⟩ := Finset.mem_filter.mp hi
  have hin := Finset.mem_range.mp hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), alive_prime hin hp ds⟩

end Sieve930

open Finset Real
namespace Slope930

/-- The numerator of the Taylor polynomial for `exp(x/y)` through degree eight,
with common denominator `8! * y^8`. -/
def E (x y : ℕ) : ℕ :=
  40320*y^8 + 40320*x*y^7 + 20160*x^2*y^6 + 6720*x^3*y^5 +
  1680*x^4*y^4 + 336*x^5*y^3 + 56*x^6*y^2 + 8*x^7*y + x^8

theorem exp_lower (x y : ℕ) (hy : 0<y) :
    (E x y:ℝ)/(40320*(y:ℝ)^8) ≤ exp ((x:ℝ)/y) := by
  have hh := Real.sum_le_exp_of_nonneg (show 0 ≤ (x:ℝ)/y by positivity) 9
  apply le_trans (le_of_eq _) hh
  norm_num [E, Finset.sum_range_succ, Nat.factorial]
  field_simp
  ring

def expTest (a b c : ℕ) : Bool :=
  let x := 10*a+11*c
  let y := 320*c
  decide (0<c ∧ b*(40320*y^8)^32 ≤ (E x y)^32)

theorem logBound {a b c : ℕ} (hb : 0<b) (v : expTest a b c = true) :
    log (b:ℝ) ≤ (a:ℝ)/c + 11/10 := by
  simp only [expTest, decide_eq_true_eq] at v
  let x := 10*a+11*c
  let y := 320*c
  have hc := v.1
  have hy : 0<y := by dsimp [y]; omega
  have hy' : (0:ℝ)<y := by exact_mod_cast hy
  have hc' : (0:ℝ)<c := by exact_mod_cast hc
  apply (Real.log_le_iff_le_exp (by exact_mod_cast hb)).mpr
  have hcast : (b:ℝ)*(40320*(y:ℝ)^8)^32 ≤ (E x y:ℝ)^32 := by
    exact_mod_cast v.2
  have hbnd : (b:ℝ) ≤ ((E x y:ℝ)/(40320*(y:ℝ)^8))^32 := by
    rw [div_pow]
    exact (le_div_iff₀ (by positivity)).mpr hcast
  calc
    _ ≤ _ := hbnd
    _ ≤ (exp ((x:ℝ)/y))^32 := by
      gcongr
      exact exp_lower x y hy
    _ = exp ((a:ℝ)/c+11/10) := by
      rw [← Real.exp_nat_mul]
      congr 1
      dsimp [x,y]
      push_cast
      field_simp
      ring

def S (a c : ℕ) : Prop := Nat.count Nat.Prime a ≤ c ∧
  ∀ k : ℕ, 60184 ≤ k → k < a → (k.primeCounting:ℝ)*(log k-11/10) ≤ k

theorem base : S 2 0 := by
  constructor
  · decide
  · omega

theorem step {a b ca cb n : ℕ} (h : S a ca) (hab : a≤b) (hb : 0<b)
    (hn : ((range (b-a)).filter (fun i => (a+i).Prime)).card ≤ n) (hc : ca+n ≤ cb)
    (ht : b ≤ 60184 ∨ expTest a b cb = true) : S b cb := by
  have hc' : Nat.count Nat.Prime b ≤ cb := by
    calc
      _ = Nat.count Nat.Prime a + Nat.count (fun i => (a+i).Prime) (b-a) := by
        nth_rw 1 [← Nat.add_sub_of_le hab]
        rw [Nat.count_add]
      _ ≤ ca+n := Nat.add_le_add h.1 (by simpa only [Nat.count_eq_card_filter_range] using hn)
      _ ≤ _ := hc
  refine ⟨hc',?_⟩
  intro k hk hkb
  by_cases hka : k<a
  · exact h.2 k hk hka
  rcases ht with he | he
  · omega
  have hpos : 0 < cb := by
    simp only [expTest, decide_eq_true_eq] at he
    exact he.1
  have hlog := logBound hb he
  have hlog' : log (k:ℝ) ≤ log (b:ℝ) :=
    Real.log_le_log (by exact_mod_cast (show 0<k by omega)) (by exact_mod_cast hkb.le)
  have hp : k.primeCounting ≤ cb :=
    (Nat.count_monotone (p:=Nat.Prime) (show k+1 ≤ b by omega)).trans hc'
  have hp' : (k.primeCounting:ℝ) ≤ cb := by exact_mod_cast hp
  calc
    _ ≤ (k.primeCounting:ℝ) * ((a:ℝ)/cb) := by gcongr; linarith
    _ ≤ (cb:ℝ) * ((a:ℝ)/cb) := by gcongr
    _ = (a:ℝ) := by field_simp
    _ ≤ k := by exact_mod_cast (le_of_not_gt hka)
end Slope930


namespace Slope930
open Sieve930

def PR := (List.range 2237).filter fun d => 2 ≤ d && (List.range 48).all fun e => e < 2 || e == d || d % e != 0

def nc (a c δ : ℕ) := c + pop ((δ + 3) / 4) (alive a δ (PR.filter (· ^ 2 < a + δ)))

def run : ℕ → ℕ → List ℕ → ℕ × ℕ
  | a, c, δ :: t => if 0 < a + δ ∧ (a + δ ≤ 60184 ∨ expTest a (a + δ) (nc a c δ)) then run (a + δ) (nc a c δ) t else (0, 0)
  | a, c, _ => (a, c)

theorem rS (l) : ∀ a c, S a c → S (run a c l).1 (run a c l).2 := by
  induction l with
  | nil => exact fun a c h => h
  | cons δ t ih =>
    intro a c h
    simp only [run]
    split_ifs with hc
    · exact ih _ _ (step h (by omega) hc.1 (by simpa using count_le a δ _) le_rfl hc.2)
    · exact ⟨by simp, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩

def dec : ℕ → ℕ → List ℕ
  | n + 1, x => x % 8192 :: dec n (x / 8192)
  | _, _ => []

def C : List ℕ := [0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000, 0xa007002400a005007000c00b00a0008f913889c44e227113889c44e227113889c4400100040010004001000400100040010004, 0x2801480c005401800c809c05403801800b403702080b005c01200c008008401c00f006804402c0180120054030012007803c010, 0x43028815008e05502c01280ae03e01b00b405402d00d805802e01e01280c007204502a010808204101d80cc0640330170084046, 0x6303201a40f607803301740ae05302c014c09604f01c80c004e03b018810406604702781380a805502b814c0b604202080dc070, 0x42025014407404802b012008d04a82e813808e04b02a014807203802180f009604101c80e4078042024812808c042832419c0e2, 0x4502c01400c105d82681800c604c026812009c03f02300f806e03002081180b206302a815c09c04d027013009404801b011408c, 0x3c01880f008202e01b0098032020015806c04c030014008c04203101180d007e03001c80d407203701980c407404502581680a2, 0x6a027012807804302b81940bc05f02b811408604a02d016c088045828414807e04702600fc07f03781c811409804d02100f0060, 0x2101380b404c03301a010606d039023816c0c007103681980a005d02b81600ae04a026014409004e03401500d906e83941ee118, 0x2300b004801c00f0090064036012010808a03301d00f007805002101180cc06203c01a810006603501e011407e03a020810e071, 0x3f01d80e807c05102781200a005502280f009a03401500f007802c01100a40300280120090052029810c07003c02300c8074038, 0x2a016805003801c00d008404a01d00c006404002801980f808c042021012c0a205702b814008c04e028012c07103381f8114092, 0x6603c81dc08203f01b00f407604202f011c0c8068030812808604502b014809004102d016c0ae04e03741660b005702080e0062, 0x8204181fc10007302e01180d8089032014c0da06e03781e00d606203181c40f206f02981380aa04b02a014c0b6074034819c0c0, 0x5402f819c0ea06603001a40ee0790498248104089050021010008203d01d40d807e043820810c08703c81ac0cc08204b0234106, 0x5503281840c407f03a41ba12007803b01940b406402981540cc05d033017c0cc05e030017c0ba06402e415e0c007403601900c0, 0x6603c023810e07702d81b80e606303001640bc06203381e80e607a03781d40ea06f03181440ae05402d016c0c6053023017c0ae, 0x4b02c015c0ba05002a81640ae06402f0100092032024013008a04e026812c08603c01e011009c03f020010408405403b01c40cc, 0x8204601e40fa06f03901980ae058037018409c03c02080e408c035015809405802d016009c060033027011407804602400bc07e, 0x2a01600c408205202d01880c006302a814409605902d01780ac06d037021411e091042018c0e406f04081f80f606903781d40f4, 0x3d022812c08403e02000fc07803001f00fc08c04801980a804603201b80fc05002d012009806803501a00e007203301b00a0066, 0x5b030015c0d607603601c20af05702b81600a0043025810407e03901a81840b6059032014408203c01d005003602101280ec07e, 0xa504d820411a0ab06042ba11208e85042280d105e83401a80e207303a81bc0d006f04802040c005a030019c0c006002a01a00d2, 0x8c84a42b815a0b8068834816f09985202dc1a60f505e82bc15a0b105b82a814609a05802f21870b705402e81aa0d506a8348188, 0x7b045022011a07703381880bc08a03302180bc06e04402701360ab0500264144093051026c1420b305fc36216409b03b81b4106, 0x9204882180f208403b81f411e08c04201600b406603101d40c606903c82300fe09003e82640fc07904501e80ea06c03681e011e, 0xa605203341560c306002f415a0af051026414408c03c02581640a6850426410e084046821010808003a81e410e08a04181e4126, 0x9703d01c011408703d01b00aa045029812c0aa04702781580bc05d022013c0aa06a03901e41020a204381e21230a304b02da17f, 0x9603e023012c09c041024c11609e048021814a09c03a828816f0a785d036c17a0ac05e82e41760a804e023012006403902240f6, 0x5102e810808a04702700e407a04502b015409407303f02040f609805a02bc0f60aa056026412608c04502201300a00480258142, 0xb106903841d00d207183841a40d507b03ca19f0d5864c2cc15008204802641250aa846821010a068034816c0c404f0240158080, 0x9a848026c12c08784ac2f8180080042820412008703f023c11a0af05f82f41440c305c02f01860b5055833a1ab0c906602e8196, 0xe907c839c1c610607a83901c80e106b035a1830c005a02701740c905e02ec166094046822412c0a5051031815008e0550300143, 0xc305a82f01a80b005f82c811e09104501c814809a04b424611a08804d82a012008804c02bc15c09503a82741bc0e606f83d41d2, 0xd005c83601500a2048024c1520c3064030411e0a505002541280ad05e82e21b90d306183201320bb05702cc1660a30498274148, 0xff08b04b027e1640ba052c2aa16c0b2058c282140090850028811e09604ac21f0e687e03741b60d206e039c1fc0f008a04741bc, 0xbe05c830416e0c805f02dc1a20d507703f021f11e88b84c426513b89104ce2731420b204fc26e13308e04e42640f507d044022a, 0xa8055425a10008a048027c13a090052024414e0af057029013409804402641860ae055029412c0af05582d81a40e106a8348174, 0xb905a03181580a505c82dc17a0b4064833c1700c204981f00dc07205102801300a304982b414a0a305282541680b20558286127, 0x6b03e022013409304882180f009f049c29e13e0b105d029414409c05f02b81300a305d02d813e0a805403001680de05182e8144, 0xd4063c33c1ec0da06983801e80e405982940f0076040020812a0a3054024c1720b104c421e0ce05c030015c0e005303081ac0ec, 0x11088ec4cc24c114086847420010a0a1050026c13209d854c26810e08403901940a804f426214a09304e82e81660cf059033819f, 0xfa089845022e0f407903541ca0ed069036c1d411d09604ee27914e0b385bc2d014009004b425013c096051c27b167893850c234, 0x1670b6053c2be16c0cb85a02d615a0cd06782fc1560c105c42f418f0c806a42fa16c0c585342c013e09d851824610807803f0210, 0x12008d84e028613009283f41f20e006f037c1ec10a08c044422e1340a4056c31a15b0d6861c2f818f0b7053a2c71660b945e22be, 0x1a70bc06542be1560a9055c2e716b8b2856c23410307d840225d1490b404d827011d07c03ac1aa0b606203441a60e708404b026e, 0x13309404ec26614309c453227013e09f85842be13509485742ce1750c486002e01810cfc6da33c1ce0f2070833a1d80fc07b834e, 0x1460b284f82e81660b5054426010609384a023c13e0ac84f42a312b89605842e817e0cc05e42b21710b485e82f81900ce8700328, 0x10907b03b420e11e09884ec26c141088848823c1460a384c82841380a005ac3021a40af05a02cc1970b005d02c81650b4857c2b8, 0x19b0d606cc32c1940b584e02a816a0aa05fc2a816d09e85002a0110093857c2c813c08f84a424212c0a3042022411908c04ac23a, 0x1a88ddc7143521b30da87643701e7104880a3a71c70ea076032a1e20c805fc3801c20de05f437c18f0ce45fa3421830c60658300, 0x1790bb86102e616b0b705a02b71338bb86303001a40ca85cc2ca138099047428e1840c4067836e1860d1862e34b1a90dc867c364, 0x15b89f05542641440a504b42260f708584bc29a1628af45482881590a8859c2c61490aa05b82e61540c045da2c817a0c1857431e, 0x23c12008e243521d10508c044c23d134890c45221011086f437e1a40d4871439c1bc0ef07c838a1c40d106183301530a385182df, 0x212101086443c235116884041a2011298a2046c22c118087048c244124894443e20a0fc07fc47223810908f449a24e11d8870432, 0x20411488704b024f10207e03ee2190de072c3981dc0f087dc40a1fe111083c48c23b12e894049820a108080c43623610c893c426, 0x2ad15c0b3453229115e0a5057a2861648abc50924990e88463c91d410507a04261e7108089441220e11388144301e710307c4404, 0x208107887440e24011e08e04bc231129093c46824f13008dc4ec25f13489fa4cf2441240904460238123093046225e13b0a504de, 0x1e00fb07f442a2050ef07503b220d10708ac47424514489384c224f12008f445e231124092a44d1f30fd88f446e2060ed08c8412, 0x20a11108a447824312b08f050628214709d452829a13f89944a223511b89744e524191288da497244118889c42e20d10607d4378, 0x28915789bc4a427711108704561f711488b843222512487e841a22910f08d443621310587e843423611a087049426611d89243fa, 0x24293189d84d627b124889448c24413788804502310fd87dc41622a137099c4b024e1328a284e62880fa87984221e010189104c6, 0x39119d8d806a232d1a40bac5c02ae15c0a805822f1973cc005962cc16e0c1861830a1828a985642a014a0af050c29613208b846f, 0x3631818c305e23021940b905842d296b8b3e5c22df17e8c6c5f42e21808bfe6313031870d006c03381ba8e5870e3ac1d68e7a72d, 0x3e31f68e647203d91f090407f23e11d90ef07f23eb1db102c78e3e91fc8fe88043d41d40f4c76239b1b98ccc69c3501848d0064e, 0x39c1da0f5879e3d71fc8f847743961be0db869c3491a10ddc6fc3679d80e627563341b00c2464731a9830cd86d236d1bd0e5c738, 0x33b16e0ad456a2ac14a0a5050027013b09f053a2841500a745402af1610abc5ec3301a48cf066532298e0c606242fd1818de474e, 0x3b81cb0e0c76a3c51f50eb872c3d5a09d0607d43e01fb8f086f03401ab0d8866835d19a0c3c59130098a8bf46363521bf0dc8660, 0x4171f50fdc8203d81db8f907803d31d58e9c79e3701d80df070e34a19c8dbc72e3781c98df87383711a40cb46723491a50d6c796, 0x452218116c86a40e21011bc9304772299170874460226918885844722d92008303fc1e70fdc84042621e90388463d01cf0ebc718, 0x45b2030f608b242222d11348ee43e22790ae86b45c24513089284f626e934096042420990a484e4201ec0f447083e5220112c8ac, 0x3ee1e30e546ce3981ab8d986d437a1b20e547fa40d2034efa7743e1a08d0a088e41b20a105c8aa4a121191508323e81f19054822, 0x5482a315949dc549276937a98549f25391d097249223b12ac88c447230121492a46c250931c8a646221f514a8dc4391fd8fa2741, 0x5462731440a0055c28694d0b885912ab9414a785702cb9584af8553262928ca0a50427f15f8ab85542ac95f89e05012869430b42, 0x650b35d98cd1067730f1674aa458c2edd8e6c185f03091774bca59f2dc95bcad456e2be147ca6251827994a0ad85642b515a8a64, 0x59c2bb956cade5b22d39730bd660731218d4cc66512f316dcbb25cd32018d8c8a5f32f61830c7c6212f897f4c74691b1cd888c6c, 0x56e2b215eca4457929b93f0a805482a9160cab652b29c9614b4258829b9634b785973019734b085702b395b4b1e58e2b99658b2a, 0x5c631117a8bc45742a3165cacc5342a51578b1a57f2a495b4a7c59f2d99634b9c60f2e61948c6c67432a98a4cc267731597fcb2e, 0x5c431618ccc065bf3089944c746122fa18a8cca61030718b4bf46153099898cf264e303177cc5e62e2f717f0b585952de9638b9c, 0x6b034c9c38e886de3711ad0d566bd3629b30e226df34f1914bf66513449aa4c665fd30018c8c445db2d19810bfa5ed2f91650b40, 0x8193e69eacf66806409a068fdc79c3c31d70ed07593c71d20e166b13379aa0d1865b3581ab8d466a53679868bbe5cd2f71974d58, 0x87a44d229516b8b4c33a2d913889841a210cff97f5c1da1390ec89b454210104a8043e59f810268523ea1ff0fd57cebcb2000fa4, 0x89343122a119a8a9459a31d16485445ca2f90de81c41ea0f905a7f643922f91a08f5466a3dd1ca91145fa15d0a081f434e40b182, 0x9804d9a47929093e48323e91cc960487231517a924469a2f90a6813406e0b705c8484192185116899463a3d51948573f7a034fd4, 0x92a4af64ef1b896048aa3c523c94247ca2fd1aa8e3456227502687341e9f44fa68203e11ed4ffc87441fa0890e085246e23ed2b8, 0x9c44e227113889c44e227113889c44e227113889c44e2271138898e4d0a56d3229c44e225ad34e9c44cba7113889c44c8261129a, 0x907c7f232513c8f648aa4311ee92549c261d3029c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e2271131e9c44c227112d89564d3249d28299a4d6a4251d690f47922c5254912499a3d5285, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44cb25151f48e74aa26b93889c44e22711368, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x9c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388, 0x4ace227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e227113889c44e22711388]

def EP : List (ℕ × ℕ) := [(2, 0), (4, 2), (60337, 6087), (62071, 6239), (65677, 6559), (70687, 7002), (75401, 7429), (80287, 7862), (83557, 8153), (88327, 8564), (93563, 9036), (96167, 9263), (99377, 9537), (102877, 9844), (108041, 10279), (114679, 10845), (122561, 11528), (129049, 12080), (135637, 12636), (140677, 13067), (145513, 13464), (151901, 14016), (155413, 14307), (160231, 14704), (168089, 15345), (179899, 16328), (188953, 17078), (196853, 17723), (206623, 18520), (213943, 19120), (223807, 19923), (231479, 20557), (241951, 21386), (252740, 22260), (265047, 23234), (275911, 24109), (287167, 25004), (305603, 26460), (322549, 27811), (333287, 28661), (343997, 29499), (354383, 30327), (364386, 31092), (379999, 32299), (398539, 33744), (421037, 35468), (441349, 37047), (460477, 38494), (484543, 40357), (506903, 42061), (527803, 43661), (549071, 45250), (576949, 47355), (601283, 49196), (622942, 50828), (653693, 53094), (689219, 55751), (723319, 58288), (760423, 61009), (797887, 63800), (832621, 66361), (869713, 69074), (905659, 71681), (942466, 74375), (989119, 77711), (1040579, 81444), (1101323, 85804), (1158481, 89922), (1205447, 93300), (1262617, 97362), (1321417, 101531), (1389629, 106359), (1459727, 111312), (1523491, 115820), (1598327, 121022), (1683887, 127010), (1777103, 133469), (1875191, 140309), (1964437, 146493), (2059097, 153011), (2157893, 159807), (2262563, 166947), (2377967, 174780), (2512897, 183952), (2653481, 193486), (2795791, 203070), (2937049, 212598), (3095763, 223220), (3251506, 233679), (3406343, 243972), (3564851, 254396), (3724851, 265043), (3884851, 275585), (4044851, 286145), (4204851, 296637), (4364851, 307042), (4524851, 317542), (4684851, 327969), (4844851, 338360), (5000000, 348513)]

abbrev P (i : ℕ) := run (EP.getD i (0, 0)).1 (EP.getD i (0, 0)).2 (dec 32 (C.getD i 0)) = EP.getD (i + 1) (0, 0)

theorem k0 : P 0 := by decide +kernel
theorem k1 : P 1 := by decide +kernel
theorem k2 : P 2 := by decide +kernel
theorem k3 : P 3 := by decide +kernel
theorem k4 : P 4 := by decide +kernel
theorem k5 : P 5 := by decide +kernel
theorem k6 : P 6 := by decide +kernel
theorem k7 : P 7 := by decide +kernel
theorem k8 : P 8 := by decide +kernel
theorem k9 : P 9 := by decide +kernel
theorem k10 : P 10 := by decide +kernel
theorem k11 : P 11 := by decide +kernel
theorem k12 : P 12 := by decide +kernel
theorem k13 : P 13 := by decide +kernel
theorem k14 : P 14 := by decide +kernel
theorem k15 : P 15 := by decide +kernel
theorem k16 : P 16 := by decide +kernel
theorem k17 : P 17 := by decide +kernel
theorem k18 : P 18 := by decide +kernel
theorem k19 : P 19 := by decide +kernel
theorem k20 : P 20 := by decide +kernel
theorem k21 : P 21 := by decide +kernel
theorem k22 : P 22 := by decide +kernel
theorem k23 : P 23 := by decide +kernel
theorem k24 : P 24 := by decide +kernel
theorem k25 : P 25 := by decide +kernel
theorem k26 : P 26 := by decide +kernel
theorem k27 : P 27 := by decide +kernel
theorem k28 : P 28 := by decide +kernel
theorem k29 : P 29 := by decide +kernel
theorem k30 : P 30 := by decide +kernel
theorem k31 : P 31 := by decide +kernel
theorem k32 : P 32 := by decide +kernel
theorem k33 : P 33 := by decide +kernel
theorem k34 : P 34 := by decide +kernel
theorem k35 : P 35 := by decide +kernel
theorem k36 : P 36 := by decide +kernel
theorem k37 : P 37 := by decide +kernel
theorem k38 : P 38 := by decide +kernel
theorem k39 : P 39 := by decide +kernel
theorem k40 : P 40 := by decide +kernel
theorem k41 : P 41 := by decide +kernel
theorem k42 : P 42 := by decide +kernel
theorem k43 : P 43 := by decide +kernel
theorem k44 : P 44 := by decide +kernel
theorem k45 : P 45 := by decide +kernel
theorem k46 : P 46 := by decide +kernel
theorem k47 : P 47 := by decide +kernel
theorem k48 : P 48 := by decide +kernel
theorem k49 : P 49 := by decide +kernel
theorem k50 : P 50 := by decide +kernel
theorem k51 : P 51 := by decide +kernel
theorem k52 : P 52 := by decide +kernel
theorem k53 : P 53 := by decide +kernel
theorem k54 : P 54 := by decide +kernel
theorem k55 : P 55 := by decide +kernel
theorem k56 : P 56 := by decide +kernel
theorem k57 : P 57 := by decide +kernel
theorem k58 : P 58 := by decide +kernel
theorem k59 : P 59 := by decide +kernel
theorem k60 : P 60 := by decide +kernel
theorem k61 : P 61 := by decide +kernel
theorem k62 : P 62 := by decide +kernel
theorem k63 : P 63 := by decide +kernel
theorem k64 : P 64 := by decide +kernel
theorem k65 : P 65 := by decide +kernel
theorem k66 : P 66 := by decide +kernel
theorem k67 : P 67 := by decide +kernel
theorem k68 : P 68 := by decide +kernel
theorem k69 : P 69 := by decide +kernel
theorem k70 : P 70 := by decide +kernel
theorem k71 : P 71 := by decide +kernel
theorem k72 : P 72 := by decide +kernel
theorem k73 : P 73 := by decide +kernel
theorem k74 : P 74 := by decide +kernel
theorem k75 : P 75 := by decide +kernel
theorem k76 : P 76 := by decide +kernel
theorem k77 : P 77 := by decide +kernel
theorem k78 : P 78 := by decide +kernel
theorem k79 : P 79 := by decide +kernel
theorem k80 : P 80 := by decide +kernel
theorem k81 : P 81 := by decide +kernel
theorem k82 : P 82 := by decide +kernel
theorem k83 : P 83 := by decide +kernel
theorem k84 : P 84 := by decide +kernel
theorem k85 : P 85 := by decide +kernel
theorem k86 : P 86 := by decide +kernel
theorem k87 : P 87 := by decide +kernel
theorem k88 : P 88 := by decide +kernel
theorem k89 : P 89 := by decide +kernel
theorem k90 : P 90 := by decide +kernel
theorem k91 : P 91 := by decide +kernel
theorem k92 : P 92 := by decide +kernel
theorem k93 : P 93 := by decide +kernel
theorem k94 : P 94 := by decide +kernel
theorem k95 : P 95 := by decide +kernel
theorem k96 : P 96 := by decide +kernel
theorem k97 : P 97 := by decide +kernel
theorem k98 : P 98 := by decide +kernel

theorem SE : ∀ i ≤ 99, S (EP.getD i (0, 0)).1 (EP.getD i (0, 0)).2
  | 0, _ => base
  | i + 1, h => by
    have : P i := by
      have : i < 99 := by omega
      interval_cases i
      exacts [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12, k13, k14, k15, k16, k17, k18, k19, k20, k21, k22, k23, k24, k25, k26, k27, k28, k29, k30, k31, k32, k33, k34, k35, k36, k37, k38, k39, k40, k41, k42, k43, k44, k45, k46, k47, k48, k49, k50, k51, k52, k53, k54, k55, k56, k57, k58, k59, k60, k61, k62, k63, k64, k65, k66, k67, k68, k69, k70, k71, k72, k73, k74, k75, k76, k77, k78, k79, k80, k81, k82, k83, k84, k85, k86, k87, k88, k89, k90, k91, k92, k93, k94, k95, k96, k97, k98]
    rw [← show _ = EP.getD (i + 1) (0, 0) from this]
    exact rS _ _ _ (SE i (by omega))

end Slope930

theorem OMA.solution : OMA.R_Erdos930_erdos_930_variants_consecutive_integers_R1_H4_R1_H2_R1_H1_R1.H1 := by
  intro k hk hkt _
  exact (Slope930.SE 99 le_rfl).2 k hk hkt
