import OMAReductions.R_oeis_a237721_R1_H2_R1
import Mathlib

namespace A237721Net
def PairAt (R : ℕ) : Prop := ∃ b p q : ℕ, 9*b^3 ≤ R ∧ p.Prime ∧ q.Prime ∧ p<q ∧ q≤R ∧ R≤p+2*b^2
def Covers (a b : ℕ) : Prop := ∀ x, a≤x → x<b → PairAt x
theorem covers_join {a b c : ℕ} (h : Covers a b) (i : Covers b c) : Covers a c := by
  intro x hl hr; by_cases hs : x<b
  · exact h x hl hs
  · exact i x (by omega) hr
end A237721Net

namespace A237721Grid

def anchor (s : ℕ) : ℕ := 9*s^3/4096

def previous (test : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel+1, n => if test n then n else previous test fuel (n-1)

def nearPair (test : ℕ → Bool) (s : ℕ) : ℕ × ℕ :=
  let q := previous test 128 (anchor s)
  (previous test 128 (q-1), q)

def rowOK (test : ℕ → Bool) (s : ℕ) : Bool :=
  let pq := nearPair test s
  let b := s / 16
  test pq.1 && test pq.2 &&
    decide (9*b^3 ≤ anchor s ∧ pq.1 < pq.2 ∧ pq.2 ≤ anchor s ∧
      anchor (s+1) ≤ pq.1+2*b^2+1)

theorem good_row {test : ℕ → Bool} (hp : ∀ n, test n = true → n.Prime)
    {s : ℕ} (ok : rowOK test s = true) : A237721Net.Covers (anchor s) (anchor (s+1)) := by
  intro n hn he
  simp only [rowOK,Bool.and_eq_true,decide_eq_true_eq] at ok
  obtain ⟨⟨h1,h2⟩,h3,h4,h5,h6⟩ := ok
  exact ⟨s/16,(nearPair test s).1,(nearPair test s).2,h3.trans hn,
    hp _ h1,hp _ h2,h4,h5.trans hn,by omega⟩

def gridTest (test : ℕ → Bool) (start len : ℕ) : Bool := (List.range' start len).all (rowOK test)

theorem grid_append {test : ℕ→Bool} {s a b : ℕ}
    (l : gridTest test s a = true) (r : gridTest test (s+a) b = true) :
    gridTest test s (a+b) = true := by
  unfold gridTest at *
  rw [← List.range'_append_1,List.all_append,l,r]; rfl

theorem covered {test : ℕ → Bool} (hp : ∀ n, test n = true → n.Prime)
    {start len : ℕ} (h : gridTest test start len = true) :
    A237721Net.Covers (anchor start) (anchor (start+len)) := by
  induction len generalizing start with
  | zero =>
    intro x hx hx'
    simp only [Nat.add_zero] at hx'
    omega
  | succ k ih =>
    change ((List.range' start (k+1)).all (rowOK test)) = true at h
    rw [List.range'_succ,List.all_cons,Bool.and_eq_true] at h
    have t := ih (start := start+1) h.2
    have mid := A237721Net.covers_join (good_row hp h.1) t
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using mid

def gcdTest (limit sieve n : ℕ) : Bool :=
  decide (1 < n ∧ n ≤ limit^2) && decide (n.gcd sieve = 1)

theorem prime_of_gcd {bound sieve n : ℕ}
    (factors : ∀ q : ℕ, q.Prime → q ≤ bound → q ∣ sieve)
    (h : gcdTest bound sieve n = true) : n.Prime := by
  simp only [gcdTest,Bool.and_eq_true,decide_eq_true_eq] at h
  by_contra hn
  have pr := Nat.minFac_prime (by omega : n≠1)
  have small := Nat.minFac_sq_le_self (by omega : 0<n) hn
  have le : n.minFac ≤ bound := by
    by_contra! larger
    have strict := Nat.pow_lt_pow_left larger (by decide : (2:ℕ) ≠ 0)
    omega
  have dvd := Nat.dvd_gcd (Nat.minFac_dvd n) (factors _ pr le)
  rw [h.2] at dvd
  exact pr.not_dvd_one dvd

end A237721Grid

namespace A237721Grid.B4096
open A237721Grid

def modulus : ℕ := 0x189519ba3a3d2b189e0fd0b76d64af2d82140c50ec5cec70e8aafaa4472571d18850c5e93f1639efff0e8aaab7bafe54ed85a04ceed7cdd164d1c96f3359986786f68dc17f49e7513a5b1210540706e0b98cb204d57245470705cd5e2c4cd2731da544d9d2ced20dbfac45f066dba95185f02e0c395428e0ff07ab633eb7260e671dbd428b1af6aba32e61d8f6e72ea56bb267201dd1383ccf1503d5a84a408d2bd6876ebca88e0ccf8927d8c533a253e416df987fd2447b8761fb8c1d5a54575502956c6b04b47472a2af7891cb92f7b304b35f067add04ba73d0662b77ddbfecd645f647dd739194bcee67c356e7054871bf3fe4bdea1a46890510373df5f5f3c58d7f06983dba571364ab213e04af6c27f4f348ded926d61922bf38183c7bdb13bd34f5a5220a431a04aa9fbcb2f1f23cf519d803317e0272d8526c0914f6924acffd7db19d3c641ae57d96558d063ee4544190af9bc4c306a39255b2af6a40d7319079f1b32aef8e9a6f1b395cedbb2712b1e1656bec685085d2060f4cd157223febf961d5022d1da9359519224fd40f1c898e5cd6ad67058a6407ea96a9ad837a4e3f002220a852dca78c75df803b0dbd4d59c4439c7f2d6190ade51f3492d9655b546f3e856bc6e3740db522c0c158377b7661ca4472afc633b6963bcbc97cac03eb5d61fb1e03f80b4b9f9880fa00b23599cc083fcce2fb74f13141d0649cf114bff5660c854359c8c6385eec39c0f105c3527c7065c29d5aa362c33e9e35289cc7a77fb17885df0201609789b7ba7251efdc131b9f4c36897d9a375201b126d7326717c5a86e20bacc55b0354a13cbe361ae65cb6a88f46ca5d6455a40a687ebd12732f9ecb0c8ca6a7dd3e12d4377c7f9da93e5036e6d3f4992288c2db97bf024da75b07d87152155d101fbd2e235b8f7ce6f1c422bec693786f86ddda2eee1116b05e2d6bc9b12ce167ce6950075a170dfbcc855b154ec2e1a26a97a3267c0bfed32a0a267708d5714885ec9982080144d88b5973117bd9a016f3a5891639000

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem all_divide : ∀ i : Fin 4096, (i.val+1) ∣ modulus := by decide +kernel

private theorem sound (n : ℕ) (h : gcdTest 4096 modulus n = true) : n.Prime := by
  apply prime_of_gcd (n := n) ?_ h
  intro q hq hb
  have hz := all_divide ⟨q-1,by have := hq.pos; omega⟩
  simpa [Nat.sub_add_cancel hq.one_lt.le] using hz

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b384 : gridTest (gcdTest 4096 modulus) 384 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b416 : gridTest (gcdTest 4096 modulus) 416 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b448 : gridTest (gcdTest 4096 modulus) 448 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b480 : gridTest (gcdTest 4096 modulus) 480 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b512 : gridTest (gcdTest 4096 modulus) 512 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b544 : gridTest (gcdTest 4096 modulus) 544 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b576 : gridTest (gcdTest 4096 modulus) 576 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b608 : gridTest (gcdTest 4096 modulus) 608 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b640 : gridTest (gcdTest 4096 modulus) 640 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b672 : gridTest (gcdTest 4096 modulus) 672 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b704 : gridTest (gcdTest 4096 modulus) 704 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b736 : gridTest (gcdTest 4096 modulus) 736 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b768 : gridTest (gcdTest 4096 modulus) 768 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b800 : gridTest (gcdTest 4096 modulus) 800 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b832 : gridTest (gcdTest 4096 modulus) 832 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b864 : gridTest (gcdTest 4096 modulus) 864 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b896 : gridTest (gcdTest 4096 modulus) 896 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b928 : gridTest (gcdTest 4096 modulus) 928 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b960 : gridTest (gcdTest 4096 modulus) 960 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b992 : gridTest (gcdTest 4096 modulus) 992 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1024 : gridTest (gcdTest 4096 modulus) 1024 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1056 : gridTest (gcdTest 4096 modulus) 1056 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1088 : gridTest (gcdTest 4096 modulus) 1088 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1120 : gridTest (gcdTest 4096 modulus) 1120 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1152 : gridTest (gcdTest 4096 modulus) 1152 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1184 : gridTest (gcdTest 4096 modulus) 1184 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1216 : gridTest (gcdTest 4096 modulus) 1216 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1248 : gridTest (gcdTest 4096 modulus) 1248 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1280 : gridTest (gcdTest 4096 modulus) 1280 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1312 : gridTest (gcdTest 4096 modulus) 1312 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1344 : gridTest (gcdTest 4096 modulus) 1344 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1376 : gridTest (gcdTest 4096 modulus) 1376 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1408 : gridTest (gcdTest 4096 modulus) 1408 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1440 : gridTest (gcdTest 4096 modulus) 1440 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1472 : gridTest (gcdTest 4096 modulus) 1472 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1504 : gridTest (gcdTest 4096 modulus) 1504 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1536 : gridTest (gcdTest 4096 modulus) 1536 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1568 : gridTest (gcdTest 4096 modulus) 1568 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1600 : gridTest (gcdTest 4096 modulus) 1600 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1632 : gridTest (gcdTest 4096 modulus) 1632 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1664 : gridTest (gcdTest 4096 modulus) 1664 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1696 : gridTest (gcdTest 4096 modulus) 1696 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1728 : gridTest (gcdTest 4096 modulus) 1728 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1760 : gridTest (gcdTest 4096 modulus) 1760 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1792 : gridTest (gcdTest 4096 modulus) 1792 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1824 : gridTest (gcdTest 4096 modulus) 1824 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1856 : gridTest (gcdTest 4096 modulus) 1856 32 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 80000 in
private theorem b1888 : gridTest (gcdTest 4096 modulus) 1888 32 = true := by decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
private theorem all_rows : gridTest (gcdTest 4096 modulus) 384 1536 = true :=
  (grid_append (s := 384) (a := 768) (b := 768) (grid_append (s := 384) (a := 384) (b := 384) (grid_append (s := 384) (a := 192) (b := 192) (grid_append (s := 384) (a := 96) (b := 96) (grid_append (s := 384) (a := 32) (b := 64) b384 (grid_append (s := 416) (a := 32) (b := 32) b416 b448)) (grid_append (s := 480) (a := 32) (b := 64) b480 (grid_append (s := 512) (a := 32) (b := 32) b512 b544))) (grid_append (s := 576) (a := 96) (b := 96) (grid_append (s := 576) (a := 32) (b := 64) b576 (grid_append (s := 608) (a := 32) (b := 32) b608 b640)) (grid_append (s := 672) (a := 32) (b := 64) b672 (grid_append (s := 704) (a := 32) (b := 32) b704 b736)))) (grid_append (s := 768) (a := 192) (b := 192) (grid_append (s := 768) (a := 96) (b := 96) (grid_append (s := 768) (a := 32) (b := 64) b768 (grid_append (s := 800) (a := 32) (b := 32) b800 b832)) (grid_append (s := 864) (a := 32) (b := 64) b864 (grid_append (s := 896) (a := 32) (b := 32) b896 b928))) (grid_append (s := 960) (a := 96) (b := 96) (grid_append (s := 960) (a := 32) (b := 64) b960 (grid_append (s := 992) (a := 32) (b := 32) b992 b1024)) (grid_append (s := 1056) (a := 32) (b := 64) b1056 (grid_append (s := 1088) (a := 32) (b := 32) b1088 b1120))))) (grid_append (s := 1152) (a := 384) (b := 384) (grid_append (s := 1152) (a := 192) (b := 192) (grid_append (s := 1152) (a := 96) (b := 96) (grid_append (s := 1152) (a := 32) (b := 64) b1152 (grid_append (s := 1184) (a := 32) (b := 32) b1184 b1216)) (grid_append (s := 1248) (a := 32) (b := 64) b1248 (grid_append (s := 1280) (a := 32) (b := 32) b1280 b1312))) (grid_append (s := 1344) (a := 96) (b := 96) (grid_append (s := 1344) (a := 32) (b := 64) b1344 (grid_append (s := 1376) (a := 32) (b := 32) b1376 b1408)) (grid_append (s := 1440) (a := 32) (b := 64) b1440 (grid_append (s := 1472) (a := 32) (b := 32) b1472 b1504)))) (grid_append (s := 1536) (a := 192) (b := 192) (grid_append (s := 1536) (a := 96) (b := 96) (grid_append (s := 1536) (a := 32) (b := 64) b1536 (grid_append (s := 1568) (a := 32) (b := 32) b1568 b1600)) (grid_append (s := 1632) (a := 32) (b := 64) b1632 (grid_append (s := 1664) (a := 32) (b := 32) b1664 b1696))) (grid_append (s := 1728) (a := 96) (b := 96) (grid_append (s := 1728) (a := 32) (b := 64) b1728 (grid_append (s := 1760) (a := 32) (b := 32) b1760 b1792)) (grid_append (s := 1824) (a := 32) (b := 64) b1824 (grid_append (s := 1856) (a := 32) (b := 32) b1856 b1888))))))

theorem certified_interval : A237721Net.Covers 124416 15552000 :=
  covered sound all_rows

end A237721Grid.B4096

namespace A237721Lite

open A237721Net

def anchor (s : Nat) : Nat := 9*s^3/4096

def gridWheel : Nat → Nat → Nat
  | 4, 128 => 0x15317b16ef85f763e056ee39efa17d74a2a0a41a91520362f03c4400a6c2d173cc2f1eb19ff8034549294c084f41cba9da0d5383e49f684f57fd6bb63f4d8b770215933b45d479c648cce6e305435b4a52df7dd2a4173134b00f02f0bc0be5c978b68ed00ca6ad7e00a45a01b49e7e1c7c82d62853c709ad9054c413d587ba3e956fd11334d2ed4bf318f3eba6f23f419914486461c5fd4b5aabb9269323bf77168b7c27dda3c58e8801
  | 4, 256 => 0x134f4dba1338f1f03623d0e66561d93ef8acb93f8cdcbbd3c5964467bb9caedd7039be4cd25aa42539a0e444812f38d0cbe894c95bab9a0bb2623aae1646af29e13b7bb1ba52c0fa4edb68f0292deb2907f987082cb12b23a0627223f2c53ff50c1a18f13ffcfbe5d89a796ab46ce5ce6a8819d9a14ea071624cdbe3c8156babfe63f6748d24f0f9a82edefa6f9fc056826774f8dcb303f3522bfd0330c1a92bf6aaac6ca329d9ec723fe2b81dd3e9fd27f9574a99dac6d0d9629f68e5c3daebe66a4d69883e38ea02eed233e64bfe73fd7086b7c3f2b03fcec2a1b1e177d98378333aba026b54cc1e2a1c80bc2628f96311a6624a4fc6aa9241e6e2e368955702bdc0cd828dcc7f1feb1360627c1dbd8d88f97825748efee6bfc3730fb287565f6f29f674a9016fe92772881d86cec641ba8f2c33010c7892764b818d00cc87073060face539ea4a0f79df4fa25746dbd231a54e501b6ba18451a43db81869b345999a3c2de3e515f934f0c11156d62e51001
  | 5, 64 => 0x112b743a02a49ad389080ac51206055516b6953770cd3e28e47cee19f1c37d6bbdc545df19944891566d161d92f0c545ff0c3d4b82fc3b9db01001e2bf1204c72642a20836bfa5241a435f166848c14fdf655370801
  | 5, 128 => 0x137ad7588a6754e7232831b49bc96da60565aa8d0a265e1ea863ea930c1ac783c42d18c76d14f0626f5922bd6190f1aa3eb39bf014b064792130bc5856ea711ea51cc950ecd14ef6bd6d0d82dfea7a85e192074c0f01c7255a73c1724a6ac7d38764f52babd5f59702e9f7923e77825716a7f4b812c35b4f34ff020d03dcdf21a83342f192816bec2016a79e637d0e4750ab990b2df8c67f439120257082cf16cddb93e6657ee04e10baaa0ec43794a4847d6184462e7a321001
  | 5, 256 => 0x118ed8a592e59e91d44cf5716a9cd1dabe4ad1eca7c1ac20de01cd6da03974208eef32a4e8bab8068523aa8cd1f6748a08587d95283a7d9664f767296e2fb03519db136627f2dbd1ef5795b15fa2eb520e454335dea5aac4fe7a36d9a3cb9128505550c5af283356d863da17e23d8c9d94816223b12b51f99525634709ddc9528a437c8687f03e59389bfc554e78d51992a60b9f32dc7065c16271f2db9f6bebcf4973270011ac52169e7feb05487c8ab84a70082b239d8a80842421b1b1a6f04c6f8370b08f01b783131c997143b2db4b61952509f4d6d899fa79be792a45949d8a49386164fda859ca6ea0701ddc3b31e36823511cbd386a26aad854be7adea76de90949209ac1b0d30ba076d8596057f0ac237dd30bade5d95dc604f2358ab080a6f28b8e5e1c882b287328b19bd679c9d8ff8a3210ad7ff7784d9c2263e05ba80bac754c54084facd6847708c65dc7c512fcc89d40709c19e83d6d4fb966e67a252eb8ec924d55ea61ecd9e7a2b87ce8daa05b13fdb5affc7a2aa6e8c0a2a3eb109022ee7ec6bc8747d4dc59bcb3742001
  | 6, 64 => 0x108c28c8ab2dc029ed62ee2e77bab755dc59760bbfe860263bb42166c00368c9f52a100cf5785f2ce5f27f561b4ca21379f43acc9139a4e692341f951da785569f60b6d4e03e24a09441568f99908b7d271aa9ccd1e56c31d4a54d81001
  | 6, 128 => 0x12ac4e9bc4439b7e464c89eca9115222d4e40c8e9350c72f4412f5d1c0fb85af9c1ceacebef38ca499cd148287d008c3c8620a0a1038ac02fcc5ae40567907147a9d7a304838eddf48cff49ae01e668ac2a9857b544daeec8e4b0c4282198e0cb0a603bdd0cdd9d46aa680ed0695ada936d9779c1207f06902afc43b74667bb71a5da2fc2041c91c2ef3e5545b22e3423fe600fe1331fab7d61d698eb8b8ff74dbc9fc0039db53c7eee1d23c904495e4441714e537ccca9634e263d57aa23b0fe8e15e6ebbfaa8b82001
  | 6, 256 => 0x10bd7c6442f07035fac8cbbd27e72c41f59e3aa47bdfa69f4b1d5957181395e4815796af1a6c1334a7c02ad2544c40ee401ec92b0a047f4becf67cce8a4401778a0bbf37cf56c2c5f559245e81059747e871052d748cdbf58df7cdf8da4093ad589963245ac2981443405773fe18f664d1724f3dae2bfdaef720606a7b3505a2b8ecec412461c43003f21e03981b6df8662cc44278e3dc9b4f7e2788c5c6666c4e203d64f19d7626e3ebdc2772719671d947395ef1389cb9b21cbdeb72ef7cbaeec7b515f0972c0835bbc626a978b785fe20abdfc16195f1c60ef92a260ee55170fd16b759d4d2f0b94f8d1eafacf0db16d0c7040476e9293f855328209896d3513facbefb54f257c7cb51b007f9d02326baa32db9f1ecffd453edfbd24f7a1000d57a72a04cb84f44b1d7a7e09107098a9c077303078de5abde484de225baaea5be8ee10e92f687eefdf90015bb13b419d6b0d44483bd4d538d573fa32f79405678163625557ab6ea8c48d07cc6ef187c3028e817e6485e17ee3dc3dd48272d2b58f0cc7d82eebb5f77e514f21180d202d57fac0276e6c8822ebd5d4a1aa2e3c0dc31687ebc5992f4843aa55d030f4d904001
  | 7, 64 => 0x103e897bd47c89fd2243ee526583f845f211564024831125559269928225c08523ac76ea2d62f4e865d8a64bcc618559ef595286751b207ffc5e611f4318b4ba46eb28e1e330bdc62dc0d16cccbc433146ef0ca36899ea89a6cdb75ca22792b642e53582001
  | 7, 128 => 0x124818dbbcf3c546a0efb71bbf18c70b37d5238929dd802a46996b81de6546aba20892f907554435f75fabac5f93a2c4b2a8fb12db288784f5165d1c4d4474ff1532ad59a6cb6afa93aa6f98fbfb0ec34512149298ff73f372f54b90b4e05c87958df41c970528beed63663ad7d42bc3e7cca3e6ad67c73d182941189d56abbbfec5b858125b5b33e1f86597ebd255e631bcc6914048d5af68a9d57cd8d372f26ad7d9528ac85722dce40f0cda5f4aa82ded89086ae52d93d880fff2810c86325659b061091044c1f1935a50529a9e4487303b000e4aa2c04001
  | 7, 256 => 0x1058561b3f8a947b2e224f8a50fbe1c5352e73c3fd895d26798ca95c728b5c9f43b4d3b0eaee20b5cd7318cf9cc8bbdff7c4a9193035733d23e23b857e09a98ec03d43ca698dd7ccf34a8a90c1d5d5533b800c4428a20694f465608942c57eedf014b80997c91abc61e7c40f793b036e504e2ddf3b3b9c09408a5bb19dd9b89b47a5ecd524d1eb3a09c723348734be909a2d3bf08a89bf42557310671fb526da449747c2b654fbd86192bd8f874d150f48ecab93c135bf7a449e24a8970c2b7dd1a50bf86ba9976f0ab0299ae477a22648997840b33bbe0e0e234a7858d6095152949dacc8e2dab2fc3efca57d66edd8ed9cd84337eb72740bd615be99f64a77572a6d1ac5c3069699c44b858c8ef3354ee52c5f8d96bf59801518d5e373281cbb134fd3257163d444262d8a5093c586955c8e0d29699295918dc1496c9afb0b355a007a90b8fb349590c7bebe9c26a7c053758bf4815c45a72071506e2c42064e58f7b0f429fb85ba03bb0d3351c3d9dd0683283cc92e6f3f493ba5468253b4333bfa8542c793f9225932744454e355c0bc5160c4439a3e6792f3ac9efe5529efc52db8f7c060ab6c04fe0e1bec9fe74f536f7bda4a5d5446cd541093f29ae8f5f67b3bffca13d374356c6fa7cb5535c08001
  | 8, 64 => 0x1018390747f4a61687965daabc88999acc13bac0c8aee0adcabb05091cb601b77ad9dd001a6b24ad063d36d5b426be0aad6bf37fd1ed79028146a395b0e5a77940ccf30ecde7d48319827e008b2c57c390b7c38aebf985a4745fc7e850711cfa9e61f88a1b69f46c0b14d504001
  | 8, 128 => 0x1216bd547f8e53b595d28ad23003527efa59b4d296ae4daef0a9e6c18a67d40611c85ea026036a3f4683d53d00192be5e1ffa78696dfbc39fd54d6c0dd70ae633499be86f72c6f6839eb794498eb55ef975ac7cdbd798d08832abb4a6041d6f0d91840f55397f5e57c3fa8b6190917f9529caa0eb751dab623829a742aa22001faddc1c925c3e790ba03d1bf177bac5153ee7913913f3282168ee830dcd00ed4ee9a5667fac7d4d5ba0c1acfccdc402a928c045f6af93aabacdd5b29189811fa1a939667a4360ff2e7b441de03ec999d20055bf9af9ac842333a1679a64c3d533228017371ca8ac08001
  | 9, 64 => 0x1005304d6d654782a11d83948e28e33e05394358ab6928319766b96aebedd22f87f2c589c0b354c18c40a90b4f9ed58c7c8cc77a8cce1977f9b64bd5955fab62cf561cc6204162fc506981c51aedee307d701daff7d6a5c4f10bbc58a51ccd84f367b02602cdb20846d4b4a60a5256fff8535208001
  | 9, 128 => 0x11fe3edf8f43175b5e14f83df1fd695940b9bac5091c357464cfc64c4862c3df4b8bd8f5614d658cb57d84c9eda8fe9732df91e7ce872f433358937b2dbef5e13a17b933bc4d3d9598e5444fa6c6d470d2145a3d0718625e6961177ad1368304c83c72239d6c28eeefc45613bcb5808df3f7e9eb0913689b0400ae3fecf9f18b56e5d5a4d8d2cff24b2abfacbeb9ecf5ff5e3c174d8f3eca214fad9dc01d730e4b3c1aa7d014e821a027db05afbf8dc41d5b9d43525cf52a8a823464ad69725d4c7d57b3a5008f6756203b58cbcfbc18d12534cb73858bf9032377792f08d385b7e367b1499c729d1030c369cd2bc4dc490ee4cbe62a2a810001
  | 10, 64 => 0xffbb3c72ac6551b52088cd8bc47adb9c939abbaaff6afc577b0364ee73c9ebca2fe8d113372c92818fcb9446d94d374e237185d8bdc32828ebbd95eecfa08b8a17ca92a0bf072933651060a8c800ac357abbdd92e66a3248a87b33d28b65fa76ba507e086b06ce5dc187a35cc852093d4bad9c88126f1fb414d4410001
  | 10, 128 => 0x11f20b67f73faba20195f0b23f73d34c521c4b558b06ba6507e2ed43a50e5fd678556dfc2674910f4deff33ce6a5a001a26569ea5327d09c7d99f7f023fe632101b4fe200e75f6b5cc32fb92f4305e1447ee8ba7b2c78305b40bfef4accf595906286b0c476ead0324a0f5e0d21c6268ba7cfebe3f6b6a3bb0a123e0ed37722ee8dfcf410bb7b3da605c7b5e8ac64db658f3a9da757d6fcdc426db4a73569e5a112d47cbf14eeea1dd348ddb8768db8fcf7b1697c577960606ef37ec8830b4d40a08ae0636206b6ddbcc0236bad4e265a28b5512bf67d0e88a50414d1f900ab38042933c47aed4c40b49102d1483aeb319cefc937e2b1d0c41e7f25b0a4afee9e076f96630a8a9020001
  | 11, 64 => 0xff6f778872aaf66f4e692de572b3e94526140a14faba720fabc2dd4fc4900232e84390218b0ae002bb493e51b1d92a3bc4aee47fae216ca6f501b9a81072de41a462f4cca33f28c9a87b80ce776e7fdfd745b9167f3de601fb08cee295f083ad67763be29f9071d489389b6477861afb9462d1382c423bba6a4d8dcf39b2f9805350820001
  | 11, 128 => 0x11ebf49acc22651a35eb1ee27d8a27643060ae4fadc389c0695d4ed606b6a501117e30ddb5d503d06bee14dd1066cf03c76c74b15b364ddc86d25270a469b69d3f9fbf6b20634a9c3670418a725c19cd93522ac2bcf7eac327749501313ca26891f2eeb7a6677fa8da18de8be5008c066df58e408d26f300bdbd84129a28b30b869a09721a1bea5c82cebf2cefce2db584ed4b83fb9bc7ac5c3b8ba46d03b92ddf808b87d01bd02c8960843e55233b557f7e6eca5bbf5f091fc200ee3496692cbd0a30e55ec3afbc7b7c7ff2c34d12608988c7a645daaf729aa6754fb57e977a38e233a04851e7d945cd605fe0408a25a48fcd8ab1e72b8f0c4e312b7fcb13280b9b4bee1246784198099faf237b7567487cfba782a2a2040001
  | 12, 64 => 0xff499ce2f3c1cdc3a02b190030975e7bede30a963e8f9751c68c275b9742aa80fcecdea3d8b2639ee1d272e4918d0655d52cff27e5ddbfbb2493d15a087955bae058a44b138d3951568736ae7412a0d12ed7116722d93357338cd40438c624bf35dc979d5d7bafa7f53c5043d19524683d50fb5045e5e9b05a56e009b7cb2644624eec3671378b814d41040001
  | 12, 128 => 0x11e8e9ef9c0ce7bb1fdfc8c49b0ddcc17fd81e547beaa3f047b3b598e764c92a8246cad8e5819dc7cb8bd295690891d00654d3d299aa105cb4d5483a7800bc4ce76b33f557e82227e42d4572e5357945ad24933bd7c32480c4d848d987b5c3a24b1288dc6a8dd3babc012dae77acae819a209dfd7d45bd36edd539c7bc2436c284e3e071b471437bbd0b9929962be46ed66b2b504aebddb11a8f9f7d435370651dbfcf1367903032f68b0fcf97b7001e2037fdf8fc7be5b7176d9b94798357ebfa4df0669dee4e4bba57aacc64a9394acc04b0cdeaa58f2b04799848be2201f096475050953d130f09cb59390284112683a2494f1ce429abbc0e4d52218ea0490d5cd16c36d6454ce1adc3bbd2494ce0b9c189ffb3a82ce7dd779a3d643bb76fc93ae4b40a8a84080001
  | 13, 64 => 0xff36b183d0bfe25e5e4bce3c5930796455dd8674a7f2d69ddbf35800c547b8f83fe7356e3e27117028e02853fea0aa16caada7ce0bdf5cec53b14e4d2218b1a453b6430aec06d551c069201a1ef49a91f84eb3e510f130a386aaab005a8280a7df12e4246f1bc4edc47328938c7315ac2c2ab5f14dc2e99cc4b56445ff55b14c0d77a523ec646b7b730a0bc5c3b85a053502080001
  | 13, 128 => 0x11e764c8d50abba497707a18bde8e9f72333707902475976a2310f955ad8f71b9f0123de37d205af4c32df0d70dc1ea7350c946ce0ef366bd59cf5b3a1fc32caec82f305e1d45eea6cd9365559a1a9e9b5038ab4d9e4b668ab5bfeb98a944393b99aa5b6caa57b10ae019f9285e0420b9c399b4b4a66d8bfcef771987224cbb0fe55c163680bb8f4df7b24541be0871709b31c648d96a6913f68a77672bff519446013e61a148df2da8d6ca0501af3e97f5c246a19197c6091bcc19d63b60e868a121c5484d0ba87e4387c5a270ad185706c54dee2b5ebbf4db9e29e636c5662265eeab368989b960514566bba1431bd57b6990b1721e763ee830a580c8d23fa52ec0b5ac57d4be8159fd58bb5f9e1a5d1698708e21e60bd7316ac5ca3af0c41d5aef2b3998918a3bd06fece00a98b25bf079d802a2a08100001
  | 14, 64 => 0xff2d3c511cfb5cbae766686dc9eba60cf89d4929ebedfd86d4be98f107437663a7849765b940803a35da67cefd5a91e90d5a7fe8f78cf94f31b7569a54537bb2b296a3659fd85a4b6a4d3de363b14ce1e0b9dbf1c9e9a6dfa939bee4d10aa8a64e3501f70628b310a7eaf04c7bacff33da9c9f9fdd94cb4938e2416e5891de1a795447a72a87c2204a01cd7e64f0efb8ca61c851bd82c814d404100001
  | 14, 128 => 0x11e6a24124c137d980ce4da2270b5fc1093c97afd8a7aeb7e0de4fd6b662777fc0f5bde1e41d9a75f9d76f2cefb0bc6a385a0de0692ba9ecc8a17ded4441aa3da61530f803485569b478bb6c45ad229c914a2fd68ff986eeaa0f819100feb54300081786de170ea3a31ec110cdae7f923ab35fbdbde9b4b06e8a42ba11652b0719b4bf0e2f62dc5289929c953ffd5f576f3702ae671eaf1e7c5b2a8b9b7fb4818f55ac637256279d97b85b55d1b948e03954bcee93cdb8fc313622d05fb27feec6b44f8a564f3c05d24587130f93269d1633ed36e45b1abac29f4fad149c3a1b3487eb62cfc6483cd8ef6c9926b49898f7c497ae034466fdd1077e5cd1f64756244991946f7a3af0569158aa587b9e8ce786a2242e9b9aa44e8c8af07aaf61dee6801a941831184378b0d9b32291587482a5b2045dcc2008648dc1a080d867894b446b80a8a810200001
  | 15, 64 => 0xff2881d6f95c3fb39da0bf99c64c0e043d9d32e4629de35ccc8903ed8d0138548e2f2e4d930d38a129037e46b65b165d630a35d32ef2bb1244118bd9b90a43452bcc6f1ff25d4b7be0d2075df5d8ced34f2e17c26ac48536f0f6026cdd673b2d62398db7e2ad5a0d4793d0ec12567f0176a6e956794afddaa73e4a3ae0737c629cf61b1d79273e1833ba364283700c3d25b17dbd7c9049b5743e04c7e81620535008200001
  | 16, 64 => 0xff2624a1b4f7fcec225733285f01cfea50a8ab120ab23f75b81ee22abedbb732ea8483f53d87de255bc15ee36db15f4043f2132cc55c98116f926e1d027edced58017b421d56a5f5cd14aa69c4bf67fcb8a92abc13df71d0d5070169dd4e07c76c542e15be8e800c4e61709c6a3bfcb32b5283aed77fa728c605e7bbd7f1b8f2097ef942e3d453e0e618ab806fb46edab6191b1ced313e01bbf6ffd227bdddd6881049df00b0814d4010400001
  | 17, 64 => 0xff24f609061bfed1abe20a90b737bdd6a19b996f52dbc8333d4276fd5be0067bb04a6a2d86bab61497d92ca16ebfcca005b3264fdef093646052b67e890c0fe0a28f03f48dc74c698143ac8df800b8601693a5615e27615a5641b6078a65134c6506e7ffe80ce6885239f74a7e875f590b93d5a1dc91f45603e2df03375a7abbfec99dd6ceb7eea17a13fca3d33e90ed7eabe1ad77a257f82262473ea99a7ff0aa068096f4e586b1070488f4058205350020800001
  | _, _ => 0

def allow (n : Nat) : Bool :=
  (n.gcd 0x4a018bd0f483df4b0f61eadd9c82b1 == 1) &&
  (n.gcd 0x6d931243d1f1eddad141d5ea95372e2024b39d47b1f033537098e40ae50a6a4cbe3e923fb64071c246d8afa57ca7122b3eb2e1be9ad97195ac0bc81993980b3e797948d91f01716030f697cafe52f82567a833cb2b526d3bb412cd716f74cfccb11c391c2fa23a284f236ead6e8a19468a869de6b58a6f726320fdf00e897743054406eb9c56dfb00c7e0a2018b90b5654670bb23bcc7aa10ec4e451ee9 == 1) &&
  (n.gcd 0x5bf35534cc27b8135f0d8d1ea1d0a14ae89fc66d3d2a77dd5ae127df77a4d7c5eb46deed085b4ae39207ee51056d445c7574df0d458c70d8b4cd59935ba3dd530d927ba4ed949583902dd5e2109eae5fda5e5154bb94b6b1f57e68a5f0a23c8b3128d0e7ecbd3de34a7ea287cb71b0c712ca50cbe86900c8752220eeb50e4d7736d1a40f98516867489cf78804ac8df08c019b946cf710e8c84633a938f10986787e9d14520efeab5d4a8aeab044f6abd6d526ca7e2c5b02f56ac82a682021ccf6512f342de648d7864f7aba3d77898022a71ecdd709fc3d67c3b08bcb75407e4fd12190924679bbd64703513b9a2e71e8de35929e93b467ac5b7b8d060221261919d2a55c21d96e2edab230cade6eaf30e30659f404a9d4ea689cea0a13f62dccd2f959465704a718340abb2c036624aa6da8b0a21966b57bdaadf101bbc836b93acba71b71daa04b187cc56eec0c68b46ad6d23b064f5f743dbf5daabf4005839219e636c682f0b4ee2abe4567ecf960b21a710090dc807d33316babfc341342132f7ca2f579c4e5a4e2a94fd957087d692b8e41ae943a381388126489fb570b4383609829775d06d2938d205eb5dda8b5530e8339f7fd93e2fd24fcb05346508ce080b9338cb83c66d4a77a79febdd392a09182e3f3b126ea3f0f14ac3a3b82c5ccaf24004198e8f660b83ff16f15fe4892c6565e987a3eb970b2194744c9760245c2a869f3d5c4f616d3720a22e60eee2fb7be4d0fefef0a954755b115083987ae19f02d90db63bc3be2bd2d88598715a8ceb9b9a030b90a9916e2e4295e0df3f41064e4c94a75669cb3e06a7ebdba5f66e2bd17f2842eaa648c8da83ac8cfa0766ce884f3113d8463bf04237056bc606e211d1f553bf694ca58ad713acaf56e5715f21907b5eacf969bcdbd29ffcdff15eed51b67d340cfdbe6016671ba3f2326cfb3f059e6b207d8b4c7dc47e21b12e0219d6b85e81e9616941cd336b1c05b317340a2e23fb009f0c3676bb1a2967ab4e8c004ff80a86fb92bf9c7198cd75e3a4df6d3f8db95b3161fdcf867193f679bc15535c7008e9d46c6e0623254bf665df92598dad77f9116037cc26cbebaa5cd3a45b3129bf0dbfbc14e508e6630f31ef9541ab54a7c574e82d979d382c08f710a272b9b985038ae8f3c1a37d0ef901d9f292ff97c5c7df361e2c505b8ebbb3352951c2f6f059f958bd0baaedfc14285d83340e6015d4c623cbfdaadf5c72bc935b45ed839e0ec9cc926ffee3c6a06d6b02b3355ae41bae90e8cf56f23694840aa80b8e0263c4cf58132b272fada3501845312abd01742e3f0d263c77f5a576fca459f2d1d0d80f9b251f255c704fed11d782846b6d8ada92eee770384c8924bf0fc1b382d3fbdc8cccba84080724a1d9ac1cc4789b2822e19891fc0af7eef9b8078c91208d0e467aa41a4488f1daedd605ab788f39dfaedc92a6ef21eb49af4a6ae3263136bac4816e7b6b0d83f6cfdf6f24b4c4c9d496a8244b04086f11ffed57192b1b3e8cf1e2698c0f551efab4c08da350ba5a7e9be4c4a2c28a329efd630faeb4433f93004b3e34602b1f33ae20ea68ae19172bdd258d70d4ad85e64f11722465daa0e659bffb98886c79a70db377f09bcf3d2c2ef4b5b54d75cbb3efb932cb79a08de5308329c97a612db36e9513f0ab0ebd23b65b7163bdf894dd1066a55f9a4ba4bb194f9032b765e03a5c05580f1d9358a76376b2b225a4724f15aca634772bafb8ea05e2d848def57aeb0f1f6c85862560ff32b0d606c50d4646b3199f84f29a241ce47e4dc905bbc93 == 1) &&
  (n.gcd 0x76c157034cb4614542965cdf18dd1cdf4c82785577646569414657ece421baf3653f10df8bd055d51a82d9c549ede43454bb4decc066210a96768e29eae775bc742a1f3f80f5f1ed316692c33a806bb03f82adb44ef3264f7bb2c0be2eb494cb97ac634146e1fb19c2861b373dc9326678e59ae5589ee27ee025bd2bff309de634a9ef7ca4720cf0c93f921b36716aa2965e958b03e83fbffc6b2ee8640341f89f1154cbdc58b55f794a6d28c404944dbfb3fe209ed9d1757595c3f753c41b917b20bfe115c3a76f4dc444e57a83ee209c299b63c32d25975291b85eb58d06e93e65184d84424d77ad1c77c7de4cfd05be777b6078032ba04435b9e96dee79610b1578b194c2892bb9fd7d290fc72484b8c5ddb4aad4c611dcc6d66f3320e3a5d4a426fde9df4398dd8d041986da8742145ad7512026c41f3aaf92f24e5e80e14c315baef8de15072f9e7f880c621806ccb6705b8e3c2a9db3f387f15590c9a06ab684673b91120a16697bb8845f144a4ba772991d42bede9562455bf0125c930cf1594fc87cb9ddca22fb4d48fc45f0cace20db21d6d3deca062f158e577b28549df42435e590ad2bad9406e65683f0cab062f99523e9bd51b143b7130fdac3ed3fb5e02064d9e09ba61d7af3cc715ba83f7b9c5f83cd092368447eb5a1934dd37eaea5477c03df7612a8670d3fc346ce8b483b6154661452b22572619cd0ac347369e4d1dcac0125091b84dae3b7954e4a37b5b4a10bc4e0223a5635bd0c2477e3a261453b243625fafcbd30c743a76ac573a9837c618466885f79a42b1d5a5accdca87aa250f94331224cde40e04aa2f65f27c1fc14a7942d9a54a780286b8b72d6b9873baa560fb35f17efec94fb2e5ccd751687f19e6499122a05c7117abeda9196f44bebc2691d0588f80e5940bed1d1442083733f0aac9299c5bc7c3b29a2d0e0bb1fff3976c5ad666c637ed1ff58bcd0df14092acd3459ac763a3b22890601a467cdf834ac8b14724db4814332cc6ea30cb0e914c185426d6191473140b1ae6bd2e9ae166592e9130a55228d1936b458a65b5ac09d84123a25a2a5a91ec1922d19aef58dc04d03de468bda708b0a610c47687efa854e12757a989521dd8317ea48edc8b03264873b678664e4e54c7418f940556c53b4f1de430e01a486cf1e7154ee883e5d48313bdda88207cb0023e53358bdf7487d1565ab5cee7631434a7087a326134eca043b056ab69a5b483762ed2421b17df49e60aa6e10a482544514a9fc2a81976ffeab3d9fa60ca2d0dec1000542df0152e5256cdc3cde5b2028f069305698c1a5a8a3d813c57d098211f559dbce093de2e70dba4e5cf9803ea50cb2690e5fafd2b24bef36748b06061384b91aee54732c39d31c499139995c83de57f15e29271c779596debb57776c492acbf9a960a7281fd41a5ed15290ab505c54dc8dcaca4473169840f4d408c83b695ac0ebc1a274c4e696b060645606c1e10cd4882ffd2ebb75d6655fa82fc2e4a0eb48075c0a38e002d526d460de28fd6ae9903ce754f3368c4f488912ee2fc0de7a1a6b108290f6347ec2af40a475b6e98c2794792ca80d015a9d502810f695e5bf03b9e214a9898f111d594a40a51ea5ae7c3dde9bfca57daeade61afa0dda4f426c9809fec9251ac22ff7591e9dc4e47246fd45adf17008bab7dd8e8e9196c1ae1cfe3f793c986a3753bca42660a6aa978e8a605faf5ba6c294b4a782df8d133f9d6d7f447aeb2e85f67987f9276325f609c5bd23cbf0f618190f4e6a6f1da02de48f0529edcbab60bf6ec42666de5c20685fd97bb2ac6c412ff85dadfa380db716cb1217e0f466d7b45f65290299df3e0ba15b18350e12c0b20ccc82e4b78befa6cd796fc72671e621cf8a385e1c2129609da80b5604f2b33b34a8e035397451591a9b8e7e39c34284cb7e153f60e94e3cf4884061a68b6967e476d65afac7834d5bd812c3807db563db6d24758a52d8915b82b3bc71691f8c35042c0c4dfe2baed9b2d63f3d3a51af1197304ed0dfe8cc616a6223b83cf74af39043d0d6024fe5915b2a17e57f48fcadc651cc4ba9e4ee3aee506c1052433b2b4f93b80e60a50b61cb6341c41790e773da64b83bda32d3cfc7ef5ed5e06833087b36d3bad6802e330e372092af40457c2074cc9d5457ba11237b22d9fe19f7e1e0a1e5491451cc86fc01da6c688c33348c83702a64715a65ea3868f9b10dbefa8ca26316cd6a1402ec942042fe2bc81afc821c96dc86cd78b71773afacacef1615cf5dc6e6a39b54458d11690aa7393ab2440d84985122bf75f51fde1c920a8a481541f8783db6790ec84600a879f56dd716ed9f5735f860597cba40d0abf36ca93c8e4b2c6734efc47b80c852be141d5bed1fa99f3700a9ce78e14c327a4d563d65cfdca85a847cfbde8a05c0c1dffb4162e135c6466201d8b0ffeae9f716cb7715d9c32fba965e5f829913d0a28950422bf9ce6f76b42297ee64eff8b092e10277330965112da96368219f1f500da3fa4c9406ed7d090c4ffe1ce87e20a813fd936d8d090dc344cad6368e6f30652ccec19ff1eab4797a4eb79f4a6e2bdf51a7115cd64db86b1176bbac48de029ab704083bfddd026ba9af7bfffaadfde39626121b6825c63a6c5aaf0076f36ad0bfba48bc79eceb2732406ded7531322a3cc9c13fd42f66b3e5e97c6a594e4f73bf3d40e03aa4355da6c3037a389928f4dca94da3892cac165934273eb980d115f6569ebe6b181e50538f510af52dc2c351a155f6fb539d8a8da55214918ba667fd74e73d15e41275ca7f1ab56acc6c339b6a0f92e1e022c04d9bcddadec7d709d8e77b4f77235191a0abe676742c046aa35b27e9bf08bcefb3b84de1fe13cdc7c3c9a3bd6a103e208cb5216b30961e751f2fe482615c582d1ea5d5b50e69fa30c8c364d3cbb3fe0246be8c71c18ea2f1ae528e89298eb0e6ace43cd145f5e38386a132ac10a8a32737baad13cda73e49dea29b94d033ee54a97a7fdab12e4713dd468a4a0908cb1886fdd77c8aa20f158914782cf574aeb04cb8c689c770426cc84cf9f10b1a31dfec421feb5610c94598f8693f071bd813b755e12df648c2ac114a7c65ffd495d93158a20e4594728d09df01918c0c675bb4393b86c3bc31c238c50c0331f52dfa17b174fa5b2f3cb74762078c7681963111b9c01e564aede1c577d2be6fa799dbdf3fdb5becef25d39397fda21566424c5d364e4c4bc76ed9eb83f5467653fdcb2ed69364a45afde9fe21506699981af25b4e02bb40d85affe37f8de476f3677952a4ab9875ab93a138f4bce9d0d963be853500f817e08a5aec9dd747c05d36f4422223bfeea8cb06e22ecd9c400f5db5d01abeab93384f50501f06a20bbb7e87b42633e5c1e4de5e43b6ed854a813361f9f2c56c77a552ea9f980798af041401e189c8247ee9bc2373ff52c4456832f8011c1c6db26c84a004e83fd049f87301b8b88af139cef282d02df62470000c111783e58b4938d66f333d20d48a78af82d0d50d9a26ea6c3d46e1a48583ffdcd2828bf299320983742951bb120229d3b125a8e117c169404c2db48075854d59ab776bccbafc2837ad0840c34ff941ae1017302e3d13c2c2268131d942d387e3c242fe086b485a4e8bdc910d3fcf9b22e20e1edb67ea4e7e664c25c32f8ad5c8e73985d498ec1234a4fdcd1fd9c2d0aa00ee05f8306130d031abbf89c4a1cf25b34a2e1945f8c49f2cd4257bf75f6ac5e8464ffc22279a478753ae564a4bfa81bddeb43979e82a81f2ba86b1ea2469983c3252035b8294b7ba0464609d9970084c03a8f794ed6c1d95f339a8ea6f2af13ee5088fe57b90de4decd8cf7bf297c655fc5e5740dba0fd9f7d1ba64db3cd142503bd29d547df1344c2f09cb29ed341033347a764f1d164e8c6546b01d5c18541faeec534c61b8c2a4eba30fc516c0e3b62e5caf0dc107c21411b6d107f3e7e2667646eff566e899fcf8022af31c20ff30fbc2b68f89db9f56322046d6e0a262680f7108249f4f304ebdbaa8b30d20f56638b7ceb6bb090f27e642a9f1b5185e5cd0eae3536202a29640efc3597af10a0605c31cb11e1648b2d311384977ffab92ee76be3b53739a60b8b03f3d8a674d535ed783c4b264b4c212051ab78bf0dbb1708d072ac88ded15eca3727df8f511a9d4e3aa0b77e530e27feef462694653635c94fb3dd2857de5f07f49bfccc40344040915df40ae7843693fb39852aa91757252d733aea1b2a374cdd2d448e5d403290d98bc7f75c80ba76937909d52ca2eaf6dea0a787328435414e00d029914f790501694ba5988a80a182881a05d7482b8350230395941d32776387000ecd10ff6566276283b7474513b478daca28e222c3abbd0cbd834db70f956b4f12030d12180298548ee95b564ec33735142fe812b9aab509e7d15b1aec757cce12299c2dc706c986aaef61a0e0c01f797b2032e2f2b95aa66af34b917ceab889a6fb2938b4304b8214f3e702fa972cdc81eeaf117d96d36e9bed172c41ae6be9513730e2740411362f17225165238a6aa1ab21f7ad2d5d9c27bae5058767bc95802ba42d65188f753a72f4d0ed8269c9ac1172a657cebd9adb3c52400b4cf6247c15860eec37462d3a2a2797fdd965b0a311c0379961f53c42d93056da5a1f14062490523783f35026fef96e7f47dfb72c3bf968a84b3ee3f7cb51018ef8a14fe5c9ab34dce5a9804bc33cecd7937bc45fe1dd13f206f8aa82d701419ac34c5a8b671d08b4b1dd24656149abf32b78bf2f4f3181390ce9bcab42e4f987d66ca79459a104ce727cb48daa3e2a8ffc646e0dc4fcf11f1c77ab65a0259bac94104520b00434d2f02af9bb4af2874b0e4f13c186e66836517455e9022d488048e1f529bf023b439d0a87dc1ea7c488192acdf7c9966fbd409b2e1878ef09c9dee86b5e9a2311b65913a63d4aee0f466953697e61835f3535042945d8805cd62954bc822300ec12ce3a90c90ff5fb3556105ebe92c3e8ddf2c9656655f0e033b817d9358fb29e0f4ec6fd69b31df2c12d7348fc8055cf5cccdd9883b0471d4218d58c1d5b5072324a07d79d90653f51358ccd6b2987700fbb9e2d7fb06412dda75fa75ff0b4a0e2b9ecfeb84b6c7df51bd2a69f4e0d34ef6d4157656e9cb0852aa8ee092b381eda98a48174f5067d467795a443d477b4b9d3eaba57ede17c5dea0416af79839fbf2c5d85f21d8259db81f55e5aa0d04b90ca60d649ec1510aa09e991fb100eb478095880ab0f807fc65ea2193981feb134d5fecd046a1924252b392f7ef3893bd0a80b235bb5cef15e63d122daabffb71b93cd89e34680d4fcc7f078375b6304815c1d8e28bb71124793fabec2213049a8fba4961777e6758ac59e18ae2382d624ded5900e788ccb0818cb7f4631adbf3935efd6a4c83b06d2c75ab83fda2de37430cc1372c7bc9fc0377c87d1c48afe49128d7bf5ad54f52fde8e99797795dd9057edcc94c97f4b7b1518f102cb4e1a1e1cf9bd79a8332cb5c7bd7f34168512d2c7efbff292d1b77ec65411f42651fea5ebcf88024e409a483b126ec0ef2d44ef1baa601ad9a76f022797c24962bec87b31cc5db4bdbc8e68a280770485ab8b3daab02d12677d2cc547fb89a5e74814844f9f61d1b250d2d7081d4deaf419acc997bba3d33472ad70290470a5f57e1dcb11c24ef6a1ec2772b2b2ef16e8a54650f611fff8a8c5c464d26190f1665aca795d1296d85b4b4019b2cc1513d4b998fd3f8fc35383fbf40db138480c5afe53310013349d7564acc8a2ff926632a8cca998cfd000b7029d1767766e4dbbf08a8a4c9fc2180a5d0bc106d327105f9944bdd9dc0f73a8e7f9c17a784ab38a71d0ebfee0c3922d5e38c94e9b4939e10904edc52c7850742ebe491a140a2a121c66bf98d9db00be34b2fa4c639a4c5cf3356f30a5172e109e6f61b7ba9c940126d8c1e666609fc9148ac189bc59b3696ea2fd0e286b8d427d6060dbe2c5ba025c3d2b7e66cfed3ae120a0578d0752c10389a070196bd4a003c1b59d42bef98fc668128b586da86bd195b55dd1cb3f6fb7d7546d66ed4899cf61ce5ed4b1ad58bcbc45879123a5d545e7a909b297e0a508d809d54b115043fc60d07bf111f6cf004d70adcf9a4c32f584d953a319b431e8583f7749ae12e0b88f151ab3b4da1d02e00cf5cd8489f8a28407dcfdabf4a949eefce2b == 1)

def trialProgression (n step count : ℕ) : Bool :=
  (List.range' 1 count).all (fun j => decide (¬ (step*j+1) ∣ n))

def coversFactors (step cap w : ℕ) : Bool :=
  (List.range' 1 cap).all (fun j => decide (step*j+1 ∣ w))

theorem covers_zero (step cap : ℕ) : coversFactors step cap 0 = true := by
  simp [coversFactors]

theorem trial_of_coprime {n step cap w : ℕ} (hs : 0 < step)
    (hw : coversFactors step cap w = true) (hg : n.gcd w = 1) :
    trialProgression n step cap = true := by
  apply List.all_eq_true.mpr
  intro j hj
  apply decide_eq_true
  intro hd
  have hfactor : step*j+1 ∣ w := of_decide_eq_true (List.all_eq_true.mp hw j hj)
  have hone := Nat.dvd_gcd hd hfactor
  rw [hg] at hone
  have hjp : 0 < j := (List.mem_range'_1.mp hj).1
  have hpos := Nat.mul_pos hs hjp
  have := Nat.dvd_one.mp hone
  omega

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem gridWheel_valid (e cap : ℕ) :
    coversFactors (2^(e+1)) cap (gridWheel e cap) = true := by
  unfold gridWheel
  split <;> first | exact covers_zero _ _ | decide +kernel

def radixPower (n radix : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | len+1, k =>
    if k = 0 then 1 else
      ((radixPower n radix len (k/radix))^radix * 3^(k%radix)) % n

theorem radixPower_cast (n radix len k : ℕ) (hr : 1 < radix) (hk : k < radix^len) :
    (radixPower n radix len k : ZMod n) = (3 : ZMod n)^k := by
  induction len generalizing k with
  | zero =>
    have h : k = 0 := by simpa using hk
    simp [radixPower, h]
  | succ i ih =>
    by_cases hz : k = 0
    · simp [radixPower, hz]
    simp only [radixPower, if_neg hz, ZMod.natCast_mod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    have hd : k/radix < radix^i := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by simpa [pow_succ] using hk)
    rw [ih _ hd, ← pow_mul, ← pow_add]
    congr 1
    simpa only [Nat.mul_comm] using Nat.div_add_mod k radix

/-- This Euler test uses only a base-three residue. Its prescribed exponent
forces a divisor of the multiplicative order for each prime factor of n. -/
theorem order_factor_of_minus_one {n e radix len : ℕ} (hn : 2 < n) (hodd : n % 2 = 1)
    (hr : 1 < radix) (hsize : (n/(2^(e+1)))*2^e < radix^len)
    (hexp : radixPower n radix len ((n/(2^(e+1)))*2^e) = n-1)
    {r : ℕ} (hp : r.Prime) (hd : r ∣ n) : 2^(e+1) ∣ r-1 := by
  let : NeZero n := ⟨by omega⟩
  let : Fact r.Prime := ⟨hp⟩
  have hr2 : 2 < r := by
    have := hp.two_le
    by_contra! hm
    have : r=2 := by omega
    subst r
    omega
  have hminus : (-1 : ZMod r) ≠ 1 := by
    intro he
    have htwo : (2 : ZMod r) = 0 := by linear_combination -he
    have hdiv : r ∣ 2 := (ZMod.natCast_eq_zero_iff ..).mp htwo
    exact (not_le_of_gt hr2) (Nat.le_of_dvd (by decide) hdiv)
  have hz : (n : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff ..).mpr hd
  have hhalf : ((3:ZMod r)^(n/2^(e+1)))^(2^e) = -1 := by
    have h := congrArg (ZMod.castHom hd (ZMod r))
      (radixPower_cast n radix len ((n/(2^(e+1)))*2^e) hr hsize)
    rw [hexp] at h
    simp only [map_natCast, map_pow, map_ofNat] at h
    rw [← pow_mul, ← h, Nat.cast_sub (by omega), Nat.cast_one, hz, zero_sub]
  have hfull : ((3:ZMod r)^(n/2^(e+1)))^(2^(e+1)) = 1 := by
    let v : ZMod r := (3 : ZMod r)^(n/2^(e+1))
    change v ^ (2^(e+1)) = 1
    have hv : v ^ (2^e) = -1 := hhalf
    rw [pow_succ, pow_mul, hv]
    norm_num
  have hnot : ((3:ZMod r)^(n/2^(e+1)))^(2^e) ≠ 1 := by simpa only [hhalf] using hminus
  have ho := orderOf_eq_prime_pow hnot hfull
  have hunit : (3:ZMod r)^(n/2^(e+1)) ≠ 0 := by
    intro h
    rw [h, zero_pow (by positivity)] at hfull
    exact zero_ne_one hfull
  rw [← ho]
  exact ZMod.orderOf_dvd_card_sub_one hunit

def checkRadix (radix len n e cap : ℕ) : Bool :=
  let k := (n/(2^(e+1)))*2^e
  decide (2 < n ∧ n % 2 = 1 ∧ 1 < radix ∧ k < radix^len ∧
    n < (2^(e+1)*(cap+1)+1)^2 ∧ radixPower n radix len k = n-1 ∧ n.gcd (gridWheel e cap) = 1)

theorem checkRadix_prime {radix len n e cap : ℕ} (h : checkRadix radix len n e cap = true) :
    n.Prime := by
  obtain ⟨hn, hodd, hr, hsize, bound, heuler, hg⟩ := of_decide_eq_true h
  by_contra hnp
  let r := n.minFac
  have hp : r.Prime := Nat.minFac_prime (by omega)
  have hd : r ∣ n := Nat.minFac_dvd n
  have hs : r^2 ≤ n := Nat.minFac_sq_le_self (by omega) hnp
  obtain ⟨j, hj⟩ := order_factor_of_minus_one hn hodd hr hsize heuler hp hd
  have hr2 := hp.two_le
  have hjp : 0 < j := by
    by_contra! hz
    have : j=0 := by omega
    simp [this] at hj
    omega
  have eqr : 2^(e+1)*j+1=r := by omega
  have hjc : j ≤ cap := by
    by_contra! big
    have le : 2^(e+1)*(cap+1)+1 ≤ r := by
      rw [←eqr]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ big) 1
    have := Nat.pow_le_pow_left le 2
    omega
  have trial := trial_of_coprime (pow_pos (by decide : 0 < 2) _) (gridWheel_valid e cap) hg
  have nf := of_decide_eq_true (List.all_eq_true.mp trial j (List.mem_range'_1.mpr (by omega)))
  exact nf (eqr ▸ hd)

def forceNat {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k+1 => f (k+1)

theorem forceNat_eq {α : Type} (n : Nat) (f : Nat → α) : forceNat n f = f n := by
  cases n <;> rfl

def bitUnary (z : Nat) : Nat × Nat :=
  forceNat ((z - (z &&& (z-1))).log2) fun k => (k, z >>> (k+1))

def strictSlots (z : Nat) (f : Nat → Nat → Nat → Nat → Bool) : Bool :=
  let h := bitUnary z
  let r := if h.1 < 32 then (0, h) else (h.1-31, bitUnary h.2)
  let p := bitUnary r.2.2
  f r.1 r.2.1 p.1 p.2

def strictLookup (step : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel+1, k, rank => forceNat k fun k => forceNat (1+k*step) fun n =>
    if allow n then
      if rank = 0 then k else strictLookup step fuel (k-3) (rank-1)
    else strictLookup step fuel (k-3) rank

def strictCell (radix len s d rq rp : Nat) : Bool :=
  forceNat (anchor s) fun u =>
  forceNat (u.log2/2-5-d) fun e =>
  forceNat (2^e) fun f =>
  forceNat ((u-1)/f) fun top =>
  forceNat (strictLookup f 256 (top-((top+3-f%3)%3)) rq) fun kq =>
  forceNat (strictLookup f 256 (kq-3) rp) fun kp =>
  forceNat (1+kp*f) fun p =>
  forceNat (1+kq*f) fun q =>
  checkRadix radix len p (e-1) (64*2^d) && checkRadix radix len q (e-1) (64*2^d) &&
    decide (9*(s/16)^3 ≤ u ∧ p < q ∧ q ≤ u ∧ anchor (s+1) ≤ p+2*(s/16)^2+1)

def strictRun (radix len : Nat) : Nat → Nat → Nat → Bool
  | _, 0, _ => true
  | s, k+1, z => forceNat z fun z => strictSlots z fun d i j rest =>
    strictCell radix len s d i j && strictRun radix len (s+1) k rest

def dropCells : Nat → Nat → Nat
  | 0, z => z
  | n+1, z => forceNat z fun z =>
    let a := bitUnary z
    let rest := if a.1 < 32 then a.2 else (bitUnary a.2).2
    dropCells n (bitUnary rest).2

def chunked (s width : Nat) : Nat → Nat → Prop
  | 0, _ => True
  | count+1, z =>
    strictRun 64 11 s width z = true ∧ chunked (s+width) width count (dropCells width z)

def packedGroups (width count : Nat) : Nat → List Nat → Prop
  | _, [] => True
  | s, z::zs => chunked s width count z ∧ packedGroups width count (s+count*width) zs

theorem strictCell_covers {radix len s d i j : ℕ} (h : strictCell radix len s d i j = true) :
    Covers (anchor s) (anchor (s+1)) := by
  simp only [strictCell, forceNat_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hp,hq⟩,hb,hlt,hlo,hhi⟩ := h
  intro x hx he
  exact ⟨s/16,_,_, hb.trans hx, checkRadix_prime hp, checkRadix_prime hq, hlt, hlo.trans hx, by omega⟩

theorem strictRun_covers {radix len s rows z : ℕ} (h : strictRun radix len s rows z = true) :
    Covers (anchor s) (anchor (s+rows)) := by
  induction rows generalizing s z with
  | zero => intro n hl he; simp only [Nat.add_zero] at he; omega
  | succ k ih =>
    rw [strictRun, forceNat_eq] at h
    simp only [strictSlots, Bool.and_eq_true] at h
    have next := covers_join (strictCell_covers h.1) (ih h.2)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

theorem chunked_covers {s width count z : ℕ} (h : chunked s width count z) :
    Covers (anchor s) (anchor (s+count*width)) := by
  induction count generalizing s z with
  | zero => intro n lo hi; simp at hi; omega
  | succ k ih =>
    have next := covers_join (strictRun_covers h.1) (ih h.2)
    simpa only [Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

theorem packedGroups_covers {s width count : ℕ} {packs : List ℕ}
    (h : packedGroups width count s packs) :
    Covers (anchor s) (anchor (s+packs.length*(count*width))) := by
  induction packs generalizing s with
  | nil => intro n lo hi; simp at hi; omega
  | cons z zs ih =>
    have next := covers_join (chunked_covers h.1) (ih h.2)
    simpa only [List.length_cons, Nat.succ_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

end A237721Lite



namespace A237721Lite.Data

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n0 : packedGroups 16 16 1920 [0x700000000f800000007ff000000007fc00000003ffff800000007c00000003f80000000700000000fe00000001f00000000fffe00000001f00000000700000000ff800000007ffc00000003e00000001fffffffc00000003f800000007fffffffffff00000000e00000001f00000000e00000001ffc00000003800000007c00000003f800000007fff00000000f800000007fffff00000000fe00000001fffc00000003fe00000001f00000000e00000000fe00000001ffffffffc00000003ff800000003fff800000007c00000003ff800000003f800000007fc0000000380000000700000000e00000001c00000003e00000001fff00000000ff800000007ffffffffffffff00000000fffffffff,0xff800000007fffffff00000000ffffffffff800000007f00000000ffffe00000001c00000003f800000003f800000007fff00000000ffe00000001f00000000fff80000000700000000ffffff800000003ffff800000007fffff00000000ffffffffffff800000007ffff00000000f800000007fff00000000ff800000007f00000000fe00000001ffc00000003e00000001c00000003e00000001ffc00000003800000007fffffc00000003ffe00000001fff00000000ffffe00000001c00000003800000007ffffc00000003ff800000007fffff00000000fffffe00000001c0000000380000000700000000f,0x3f800000007ffffff00000000e00000001ffffc00000003fe00000001fffffffff00000000fffffffffffffffffffffffffff80000000700000000e00000001ffffff00000000fffffff800000007ffffffffffffc00000003ffe00000001fffffffff00000000ffffffffe00000001fffffff000000007fffffffffffc00000001ff00000000fffffe00000001ffc00000003,0x1ffffffffffffffffffffc00000003fffffffff800000007ff00000000ffffffffffffff800000007ffffffffc00000003ffff800000007ffffffc00000003ffffffffffffffffffffffffffffffffffff800000007fffffc00000003ffffffffffffffffff,0x3f800000007ffffff00000000fe00000001fffffc00000003ffe00000001ffffffff00000000fe00000001ffffc00000003800000007fc00000003800000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000003ffffff800000007fffffffffc00000003ffffffff,0x1ffc00000003ffffffff800000007ffc00000003fe00000001fffffffffffc00000003fe00000001ffc00000003800000007ffff00000000ffe00000001ff00000000f800000007c00000003fe00000001f00000000fffe00000001fffffff00000000e00000001ffc00000003fffe00000001fffffffffc00000003e00000001ffffffc00000003ff800000007ff00000000e00000001fffff00000000e00000001fc00000003ffffe00000001ffc00000003fffffe00000001c00000003e00000001ffffffc00000003ffffffff800000007fc00000003ff,0x3800000007fffc00000003fff800000003800000007ffffffffc00000003f800000007ffff00000000fff800000007ffc00000003fffffffffffffffffffffffffffff800000007c00000003ff800000007ffffffff000000007fffffffff00000000ff800000003ffffffe00000001f00000000fffffe00000001ffc00000003800000007fffc00000003e00000001f00000000ff800000007ffc00000003fffffe00000000fffffff800000007ffc00000003800000007f00000000,0x7fffff00000000fffffffffffffffffffffffffffffffffe00000001ffc00000003fe00000001ffff00000000f800000007ffffffc00000003fffffffe00000001ffffffffffffffffc00000003fffff800000007fffffc00000003e00000001c00000003ffe00000001fffffffffffffff00000000ffe00000001ffffc00000003fffe00000001ffff00000000ff,0xffffe00000001ff00000000ffffffffffffffffffffffffe00000001ffffffffffffffc00000003fffffe00000001fffffffffffc00000003ffff800000007ffffffffffc00000003ffffffffffff800000007ffffffffffffc00000003ffffffffff800000007ffffffffffff00000000f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000001ffff00000000ffffffffffffffffffffffffffffffffffffffffffffffffff800000007ffff00000000fffffffffffffff,0x7ffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffff800000007fffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffffffff,0x1ffc00000003fffffffffe00000001f00000000fe00000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000ffffffffffffffffffffffffffffffffffff,0x7fffc00000003fffffffffe00000001ffff00000000fff80000000700000000fe00000001ffc00000003e00000001fffffffffffc00000003fffffffffffffffffffffffe00000001ffc00000003fe00000001ff00000000ffff800000007fffffc00000003ffff800000007fffffc00000003ff800000007fff00000000e00000001fc00000003fffffffffffffffff80000000700000000fffffffffffff,0xff800000007f00000000ffffffffffffe00000001f00000000ffffff800000007ff00000000fe00000001f00000000fffff800000007fffffff00000000fe00000001f00000000ffe00000001fffffffffc00000003fffe00000001ffffffff00000000e00000001fffffff00000000fffffffffffffff800000007f00000000ff800000007fff00000000ff800000007ffffffc00000003fffffff800000007fffff00000000f800000007f00000000fffffff,0x1ff00000000fffe00000000fffffffffffffffff800000007ffffffffff00000000fffe00000001fffff00000000e00000001ffff00000000ffffffff800000007ff00000000ffffffe00000001fff00000000ffff800000007fff00000000fffff80000000700000000ffe00000001ffffffffffffffc00000003800000007ffffffffffffffffffffffffffc00000003ffff,0x1ffffffffffffff00000000ffffffffffff800000003fffffffffffffffffffe00000001fc00000003f800000007ffc00000003fffffffffffffffffffffe00000001ffc00000003fffe00000001c00000003800000007fffffc00000003ff800000007f00000000fffffffffff800000007ffffffff00000000ffffff800000007fffc00000003fff800000007ffc00000003] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n1 : packedGroups 16 16 6016 [0x1fffffffffffffffffffff00000000fffe00000001fc00000003fffffffffffffffe00000001fff00000000ffffffffffe00000001fffffffffffc00000003fffffffff800000007ffffffc00000003e00000001ffc00000003fffffffe00000001ffff00000000fffffffffffffffffffffffffffff,0x3ffffffffffffffffffffffffff800000007fffc00000003ffffffff800000007ffffffffffffffffff00000000fffff800000007ffffffffffffffffffff00000000fffffffffffffffffffffe00000001fffffff00000000ffffe00000001ffffff00000000ffffff,0x3fffffffffe00000001ffffffffffffffffffffffffffffffffffff00000000fffffffffffffffffff80000000700000000fffffffffffffffffff800000007fffffffffffc00000003fffffffffffffffffffffffffffffff,0x1fffffffffffffffffffffffffffffffffffffffffffffc00000003ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3e00000001ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000003ffffffffffffffffffffffffffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3fffbfffffdffffffff8000000077fffffff800000007fffffffffff00000000fffffe00000001ff00000000f800000007fffdfe00000001fffffffffc00000003fffff800000007ffffffff00000000ff80000000700000000ffff800000007ffc00000003ffffffffffffffffffffffffffffffffffffffffff,0xf800000007fffffffc00000003fffffffdff00000000ffffffffe00000001fffffbfffffffffffffffffffffffffff7f00000000fffffffffff800000007ffffffc00000003f800000007ffc00000003ffffffffffffffffffffe00000001fffff00000000ff800000007ffc00000003ffffff800000003ffe00000001fc00000003f,0x7ffff00000000ffffe00000001ffeffe00000001fff00000000ffff800000007ffff00000000fffffdffffdff800000007fdffffffffefffffc00000003fffff800000007ffffffffffffc00000003fffffffffe00000001ffff00000000fffffffefff00000000fffffffffffddffffe00000001ffff00000000fffffffff,0xbf7f800000007ffff00000000fffffffb7fffffffffff7fffdffffbefffdfffffffc00000003fffffff800000007fffffbe00000001fff00000000fffffff800000007f00000000fff400000003efffffffffdbfffffbffffffdf00000000fe00000001fffff00000000fffffffffffffffffff,0x7fc00000003ffffffffffffff800000007fffffffffffff7fefefffe00000001ffdfffffffdfffffdffdfffffffdfffffffffd7fff7fffffffefffffffffffffffffcffffbffff7effffbdffffffff00000000,0x3ffffbffbfffffff3ffffffffff800000007a00000001ffffffff00000000ffffff7fffff00000000fffbf7fffff77fdfffffffff00000000f8000000077fbfffffc00000003efffff7ffffffffffffffffff800000007ffffffffc00000003fffff800000007fdffffffff,0x3e000000017fbfff7ffdfffffffffc00000002dffffeffffffff7fffffffffefe7ffdfffffffefefffff7fffffbfff7fffffffffc00000003fffffdfdfffffffffefc00000003ffb00000000ffffffffffffffbfff7fff800000007c00000003,0xffffffff7fffff7f7dfd00000000bfbb7fffff7ff7fffff7fffd800000007f00000000fdfffffbe00000001fdfffffffffffffffff800000007edf7df7fffdf7ffffffffffefbffe00000001fc00000003ffffffbfffbedffefcffffdfc7fffff00000000ff,0xbeffffffffffffffe000000017efffbffdfffdffffdf00000000bffffc00000002ffffffffffffffffefffdffeffff7ffc00000003ffefff7ffdfffffffffeffffffffffffddfeffdf7fffdefeffffffffdfffc00000003f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n2 : packedGroups 16 16 10112 [0x7fffffffebdfdffffffff77f00000000ffdeffffffefffffbffdfdfffffffff7ff7ff800000007bfffffffbffefffffeffeffefc000000037feffefffd7dfffffefeffff7ffffffefdfffffffdfffffff,0x1ffffffdf3fffffff7fff7ffbbfff5ffffbffc00000003ffffffffffefffffffeefff5bfffffffdffffffffddfffebe7ffffff00000000ff7ffffefaebfffffffff5bffefffffef7ffdfffb7f7f,0x7dfbfffffffdfd7f400000003f7ffffffffff900000000efff6ffffffdfffe00000001ff9ff7ebfffffffffffffffeeaffdfffffffffedfffffbfffffdefffffbfeff6fffbfffffbff7fffffffeef7f7ffe,0x73fffefffdffffffff3ffb7eefffdefbfdfdfbfffff7ffff77dfffefff77d5eeffffaffffffffaef7ffffffbaffa800000007ffffffdff3efffffef7dfffffebffffffffffbfdbbdffbfff,0xfbfffffff9fffefffffffeffddffff6fdd7fffbffbffdfcf7ffbfffffbfffcffddabfdffffffdffdffffffe7d7efffdfffdfffff9ffbf7fff7ff7b7ffbfffffedcf8efffdffffe,0xeeffffdffffffef5f7ff7ffffffff9f7dfefeff7ffff7feffffeffffffff3fdffffbbf7ffd77fbfffd7f6edfbdbfff7bb2ffd5efedf7fffffebffdffffefff9fbffffffefbffffb,0x7fffffff7efbfdffbffdfffffffffffeffdfe7fefefedeeff7fffffffffff7ffff7ffff7bfbebef75f6ff7ffbffffefffefeff3fdfffffe5fffffffff7fefffff7ff7ffdbfff,0xf7b67efffd7fffbbfbbffffffffbff7fdfffffefffffffadebdff5dfeffffdfeffdfffffffbfffffffffff7ffeff77fffefdfdffb3fff9ff7ebef3ff7f6efffbffdffffffe67bef,0x17fff7ffefdff5f9bfeefbf6fbffffeff3fcffbdeffbffeeffbf7fff9fffdfffffefdffffffef77f9fdf3bdbfeff7fffffffddefffecffffffffff7ff7fffffffbfffdffffffdff,0x7fdddfff5ff7fffffff7ff400000002fd800000005ffefffffff6f7bfedb75fcbfbef7ffffa00000001fffdb7e7800000007fc00000002fe7f00000000dafffffeec000000037effffffd67bffbffffdff7dffdffffffdfffdbff7effffbff3fff7fffffdf,0x7f00000000f7fe7fefffffb00000000fe00000001fffff7f7efffedd00000000ffcfffffffcffffdeffe000000016febfe7fef5ffa800000007f7fff800000007fc000000037bea000000019f7bfc000000039ff7f00000000eef7fbf800000007df7ffffdfffde7e7b800000007ffffffe77800000007f00000000fe00000001fff7fffd77a00000001eeeffe00000001be500000000f,0xb00000000ffefffeffffff6fdfff7ffcffffff80000000777f00000000fff7f6fffffff7fefffaffdf7f00000000ffbc00000003bcbfffeb5e00000001ff7ff3fbdfffdfdd00000000e00000001ffefffebdffffffffffbffffff7feffebfffad7fdeffffffffff,0xf7efff7feff77fdf7ffff7ffdff7ef400000003fc800000007ffffff7fffff7dfdff00000000ffffffeffefffdde00000001ffbfbbd7ffffbffbffdfbf72faffffffffffdfff5dff6afffff9ffdffefdffdf400000003fffdfdea00000001fef,0x7dd00000000fffffde5fff7fff00000000efffffcefbfff7f7ef77fff5ff2f7fffffefffffffecf775f9ffffedffdfdfff7eefff7bffcffdfff7bef7fffff800000006dffed00000000dcff77fb6ffaf3ffffdfeffbbfdffffd,0x1ff5f7fd00000000ffffcffed77dff7efaeffdffbfffe00000001bffefbfddf2beeffff4efbdffffffff7fdffffbfffdfff9ff77dfd5fdf6fbeef76ef7faffdfb00000000ef7ff77bffffff3ffffffeffffffbfff777,0x3ffbdffb95ffff00000000fcfafaffefdbb7f5fffbeffefdeddefef7feffffe00000001fd400000003f9f7bffd7f7f600000001febf6fdffee776ff7ffdfffff3fec00000002ef3ffdfd7b7ff7ffffdfb76ff9fff7fdeffffebffb5f00000000dfeffff] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n3 : packedGroups 16 16 14208 [0x7fcfdfdfff7ff7ffbffeefffff7ffdef77fffffbbbeffe37affee7fffffff800000007cdf3ffffbffeb73aed9f7ffd65efbffdf3fb2dffeeffdbff7ffbbbfffb7ffffefdbffeefadffff7fef3ff3fc,0x2bfbfbffbf600000001fd7fdfffff5effd7ff7ffddfdf69fff7ff7ddd700000000f9fff800000007bff9ffdbffe7afffff1bf5ffdf4ff5fffaefdf7fdfff77ff7fdffffff7ffdffbcff7fe7e00000001fcffa7fffeffffdfff5ff,0x3f6faff7d7fffcff577fdfffffbef800000007febff7fefffffbff7fff7dfdf7f300000000bcffdf6ffff800000005fbbff5efff7bffcfddfa00000001e77fdffefccbffedbbdfffeffdfdffffffffbffb77babefdffbfff7ffef,0x2aedff7d77ef400000003effdf400000003fe7df7feefffff800000007f7efeffeefffb7ffef4fff7efff7efbfbf77fdeffefffbffe7bfcfffd77e7ff7fff8fdfffbfdbaf777ffbffffffffdcff7c7f9ff7ffbdffdeef7,0xffe6fecf5ff5dfbfffdffbfffffef9feb4df3bfbfdefffd6ff7ffbf7dbf7ffefe7ee5bf200000001dffcfff8fefd6ffffefddd6f79ff7df7ffef57fffdffdf7fefff7ffbfff7800000007ffbb7affeefffdefff,0x7ffbfaf7fe7fffffdffeaffdf6bbffd7affffffbfbbe7fcfffbfddf73ff6feffff7efbc7ffbdef66f7fb77ffd7bd7e00000001ff7dfeff77ddfdfbfdfff77ffbf8fbbff2fffdeebffffffef7fbf7ff,0x1f3f3ffff9e97f7ff6bbffefe7ff5fff5f3f337ff7bffbfdedfffdef9bd7fffebfffdff7fdeff8feefebbfffbebddbfb7e7d5dffdffffffbf7b6f7b7fff37fdffecfbfbb9bfff9dfffffffb72d,0x767fe0a00000001ff7fbbf5fffffbbf5bafdff3ffcbfffffffdfffffff700000000ffffffffeb7effdffe7fdf937fffbf5ffeebfebffddffa7f7ebfbcfefd5dfefbddffdffbffddd3fff5ef7fbeffbfeffff79d,0x57ddff7ed67b6fbffbfef7fee7ffbb7f2fbffbfffb9dfdb5f6fdfef6cff3f7f7ffbf7fbb2fffeffffefeffffff3ffbef6b2cf737f7ffbeffefafff7fbdfbfbff5fff5a2db77bdafc5febefb6f7efd,0x7fbdfefeecc75e7ffffffdfedf3fe1defd5feedefbfff6ebffcbbfbdcfeff6ffddeccbffbfe00000001dfdffd7fffdffbfbf7afffffc6fdfbf5ffb7fefffbff7f3beffffffdfdbffeaf37fbff7bfbdf4bf,0x5efdfefef6dfcffbdafffcaf3ffbff9ffefaff7efebffefdfffc7bff9ff6fe7b776bfdffeb39bfd77f7adf99fcffff17ffdfbe73cfbfc00000003bfffc7afefff7eff77fffcef5ddceb7f7b7fffff7ff7fff,0x1ffd8e5ff5effccfffbfffb9bfdfe777e75fbfffe4beffffedbeeffffbedffbfbfff7bffefdffffbdfdeffff9fbffa7bbff7eefbdfbfeffffbdfeff9fbeffefbdafbfffff7f5ffd7970cff6f1e,0x5dbffdbfdfa7efffede9f9fffcdefefdffbafdefffff7bffffbfbef7e7bf7ffbfeffefdfbfe7bffeddb7efdff3fbbfef7fbdbef9fbe367fde77ffffffbff7fdf9dfbaf676feeb9e7d3efefdfff,0x778fffb7af9ffff6ffffdeffffb97e3f7f6bffdfdbf7effcbdf4fdddb7fcbffffd777ffd6ffd7dbf3cffff7f77bffdfbfeffff9bf37dff4fffbff00000000ebf779b797b7f3efff4dbbfff5f77fffffefdf,0x7affefefbdfb9ffeff7bf7ffedffbffffbfdffbffdfbbaf7cff4feff7df5fe6fddcffd9feffbffdfefffb7daffff7bfffcfdffffff7e9fcfddff4fdfafbefff777dc0ffdaf6ff6f9eddf7bbf75,0x1fffdfedffeffffdf7ebffbf9dffdfffbfbffffff6f77b7fbfdef7f73fc3fff5edf77febfffbf7ffeff76f477fffbbeff3fbbff7fffcb6fddffffebffa7ffbffef7fbffff7efeffdfff9f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n4 : packedGroups 16 16 18304 [0x3bf737fedf67ffff7f6d9ffef7bf00000000f6f9fffff57fffffffbefeffeffcff3ffbf7fbd7fdabfefeffdf5ffedfef3ffdbefd4f4fc577efddf7ffefff7f3beb6d9d9cf3fefc7fdc7f7ffb55d7ffeffdbed,0x74fffefefbdffe6f7febf7ffbbe7e5f77d7fff76ffff3effff5ffbbf6b7fffffd77f7fbfeffe4dff7f3d6dfdfbbdfefffdfae6fbdbeaecdebbbffd2ef9b2ffff7fefdf5ffff3dedfff3fbfffffd,0x1bfdbfdafbfd67fff2ffffdffffcceafef37fffabfbf5fc2efdad7feffff79bf7f777f1e7dfcfebf7ffffffffffffdfffe7febaffffffffcfdffdbf7ffb9afefff7d8ea8df900000000dff76f57de9bfff7b3,0xedb6bfefbfef6d1cfefeffffe5ffdfefdb9fffabfe72f7fff7f5774fbbfbfdfffb155fe9ffb6f7da5d77ff7fd77fbed7ff7ee394ffee9fbfdffedfaddfee8efffebf77b785efffebe7eaedfffdfd9b7eff,0x37fd69ff6bb3fff7effbdffdfeffffbfffbb6febffbef9a9bf7e7c3dffbfeefff5bb7fffffff7ffbf3fc6febfff67fcdefdffd7bfffffcace93f79bf4fffddfb4f777febfffedffbfb7fff7fdf8f,0x2cfbdffefaff9ffbfdbbef79fbefdcd7dbff7efb3fcaff77c6dbf7f7974645a6ffffff5fffabde1bfedffeb9bfffdffffafda7d7fffbb3fffeff7efffbffcbfdffaf7cffbdd3fffed7d4efbefffcffde,0x3ffeeffffecce4b5cffffff37fa7bdf5ffffdeff7bbc00000003fffe00000001a00000001def7fdfbfefff600000001ff60000000179dfeffafdbffffdcf4ec00000003f7f5fe7bbf7fc7f59379fadfffeffaffbbb5fddf7b00000000fdddeecffffae9eeefddfffddbd7eb,0x1ff7fdedcdbe800000005f613f7ff6effdafb5e7a7fbff75ff7f9fffff5fdedfffbff36aedde00000001efffffddafdefffff7ffdf800000007fffffbfff7ffddfff9fffb9dff7e6f9ffb9e99ffe77fb7fe7bfffc7fff7bf8c00000003fa,0x7dff7dfba5c00000003fcfdebfbefdffc7d5ebffcf5fbfebbd9fea800000007ffcefff7fdfb7f9777f3fffdffbffefd7fe5fa73b7fefbcffbffffbfbfbfef7fcefb7fdffed7fef86ffff57be7f77e7f7fefbc100000000fff77bb9,0x13f7faefefdbf7fbeff79f7600000001fd7effeaebffffcf86b7fff2bff7ffdbbfb8edcefbd6fbbf7effefdfffffeb779ffffc7ff07d800000007efff7cebffdffff5efefe7fbe40000000377fe00000001cfdfb7ffffd1efbeb9beffffefd,0xedbeff7ef7bff7edf5fa5f328f5beffffefef76f773ffffc7f9bfbf3dfdf7dfeeffd37600000001d7f7fdf757fdb6feefd37f3e2fbdfffffeaf474f5befbfb67ce52dedbc7bdfbdf500000000f796eff7edffbffedbf3bfb00000000bdff3,0x5acfd777dfffff7b77e7d3ff7fbdbff5f4fd8dae3f7df44fde3ad800000006deffb7fecffeef7efbf7ddbffd7fffd3f7fffdfbbdf800000005dbf69efb7fe9ffe9ffedfdfeefbfefeffffdfae0000000175af57bffdaeffff77e7f5f3,0x16b9a9ffff9fbfff7e00000001ffeffbbfff7ffdf7effbff00000000ffe73fffa7f7ffbdfeddece7bff9bcfbfefd6b7ff5efdf7bffaef4ffcffd800000007cf7bff5adbbeffffbfdfd6fffdbfdbfb6ff9e77ffffff7ff1affff,0xff3ff7abd5eebd97f53ffecd800000007efeffff3fff57f5fffaffbfff5feffa7ffbdbfef7ddaddfbbf2f67f77fffffdfdfe6cffddc7fdbdef7de7df9ffcdeb7be6c00000003ffbefe57ffffdedbf7eefbdfdcf77fdf2de,0x1f1400000003fdfd7ff777ffdfdffd00000000f7ffe76dcb7bffb599b3eebbfde9d67f9fdb5ffffc00000003400000003ef95cabf5d865e75bebfbeeddfe00000001ff7bffd7ddc9cffff7fb74effd7fffb7ff7fefe7efdffbffefbfbf7ffdf77ff9ff3dfd,0x71fffef6ffdb8df7d5ffb5ffffefe9f5efef9aef7fef9fff773fbffffa7ffc6b7ddbbffefcdfff7abfeffdffb7bcdffffd5fffd7d17f75d67fbbb2f77fdbdffdfc7fa6fe1d4fffe7f6bee659fdf7fef7f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n5 : packedGroups 16 16 22400 [0x1fe77b776bf3fdfff77f2feddf37efeefb7ff00000000eddfeff6afeefdbffdf53fefbcfdfbffefaf3d77fffaf87a5feaf3fbbcfffb9bff37f5eff9fe5fdbeefbcbbebf7b4875fef7b9cfeff67e77a3feffa7ffdffee,0x17edffbffbafb79fecfffe7eb1fffffddc800000007fabe9bfbf9efdcf7effd67fdb00000000cb7fe59fdffedbfffbf5efb736fff2f8fff7fdf7cf4fff9f7edfff9fdb5f47ffffa7fbff7f6edc7fefbfffdd2f7ff7ffdfdd,0x3d7dbdebf8b3fffe7efebffbdf2eff7ededffec98fcffeaf97d7eecfe400000003ff5cfefeffffeef9b7f92bbddcefcf7effdfeaf94fdffff2b2073ac567effbfbf77fbf6fbdeef1fff9d63ddeea00000001efdf3a9efbbdb7e800000007fbebd2,0xb7fbb97f32ffdfefdcefffffffdcdff4fdffcdd7b9f7fcfbefbffefbbabfefe7d9dffff3cf3bfbff7ff8dfabfdf7edf77f3fedff6aeefbedd7befef5e9ffff6ff7dbdfbfb6acceffff7fdea57ba777e77,0x1f3f7fdecbffcf4bc5ff9ebfff7fff5f1f96fbaffdefadf9600000001fff7fbfe9df75edfffc57bbf5fffbffb53ffbfffffeefffef7fb1faffe9ff9fb7fdef7fbf37ef77ff7feb2f5f7fffff6ef76fcefb7bb7f,0x7eff6f6b7ffdff9f6fd5f3dfbf1cfdfeffb77df65e9f97ffdffeecfbfaeaf7ef7fb7fbe7feff96fb7fb772ffff6e69fa7ed7faffe77eff2739fdfffd4fdef7ffd7fb5fcfefd33eebd7ff63fbffdffbbfbb,0x1bfdbff9bbfbddfef7f7dfebebdbddcfeff7efefefd7fedf62f6e7be3f6dff2df7fbfff7d4fff9feeeffefef27ffefc3ffe718aae9febfaff7dcfffe7d7eff5d37f75febf4da7eb8fbc7dcbfdff6f9feafef7,0xf47ef9dffdf1ffbffffffefddfeefbeff3fd5febfdb2f3dfffabd7ff5eb7ade753f57efc6fbff7ff3f7f7deefffe9f7fff17becfeffffdff65decb5babdcff82febfbbeebffddc3cc9fffbdcffeddaf9fbf,0x7cbfffbcfdeadfbbff379fbc1bf3f7befff9fafffef5bedbfdfafeeffffcbdda4d5ed7fcaf76dbfd7feff7ffbebf76fdfafffbfffbffeb4cbbf7f3befee73df7e542b967ee00000001ff5bfe7f7dffdffcff9c7fd2ff,0x1efffb0cbfbadfdfefcb3f9ba3dff7bff5bbff75df37fff7e7efbdf7f24fbdfedafb7afbd1fffbfadf78e576fdbfff69aebbe7fc7b7dfad9f37737bfeffe7f7e7b9b7bb7df3ffdf3bffb5efd63fcdffbd8800000004ffdecd,0x275fdfdfbebfff7d7fffffbcbefffbfdbcf3fb69fffdffeffaefbb6efadfb9fefcbfc000000037bfa71fd6fbdaf5fbf55eeb67f735f7fb1ddbffffd6f7fffdfdf7b7dfef7639dfebfbedffdfe7bedf59adef9fe9ff,0x1befdd5df779de82fbeede725fde5daebe3eddecfdff77f97eb9d5bea7b676f3ffffe77fd7bfeff7bce5ffff43cdfe3f9ccff7f1bffdfefe7db6ff7ff0ffdff3febd7e7ffffb7bff5cddfddff3be9bffdfffedf,0xf2e3bddf6fbfdfc7dd7f9df5eff3ffa7e76f7fff3dba9b63ecab96d97254df303fbd9fee93efffdef765e3576b6af7577bff557c77d777f3f7bfff3c7ffbb9efffd7ef7ebff777deafdf79fe3ffa6fe9ffbeeafafbefd,0x6dfff4ff9eca7ffff7fefffbde67f4efdefcf97ff1affb7af2cffdffcf3fbbf59978db7f47cfe75f7fff77ddf6bf4d9ffdffc55bffffffdbfdfffaf7ffafbfefffcbea9b3fd3fff9becbffbaf7bfd76ffef,0x1deceef6ffefd7fecfbefaf73acec77bb6f9f9ff7df63ffff5b45fa5ff39f7fbef7aefb53fbdfef5cffb2b7eb7ecaefeff8ffff5beffff72fffffb7fbfd7f75efe97ff6a7fefff3ffeddf7255c7db5e789757ffb,0x7bbf7bf8bbadfffcdf2b7f9ebdf735fcbeeffe73de58bebfdfbb7addfefa7dfb4f717de6ff15fbf7bbcfdefafffddffbbbdf7bfb77fb3f2fef57dbfddfffbfdffcffee77dfbedf63d7efae277f097effecbd7f73] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n6 : packedGroups 16 16 26496 [0x67edfdeff7fdebeea6efff77bf5d7abbbfc7fffd7e393fffddfdffaffffcfdfd7fbbbedaed1bffdfdb6b3cfefbe87ff67de5dfdffdfffdbfe7fbffbe7787baa7bff7fed14ff4fecf5f61d7cd3dffe3ffd6bf8f,0xd6df77feb7bffaf7af5931efebffaf7e35fda5fffeeef5c5a5e54ebaeeffeebf3a3137f6f9bfeffffbed3fefdd7c72c77ffd76733ce37fcebd976df9ffefefffdfabbfcdcbd5db7d6e57bbbfffc7d7f979fb74f7efee3d,0xbf66fe1b5ddf7f7fff8fffb5bba1d800000007bdedcfaeeefffbf7fbddff4effff5ff367f6f7f38fffbffff77fffecfb7af9fdfff76fdf9d7ecacb9a6fdf86f7aff3f7d5fdfe7dddfff7df5d9fdadbfbfed8ff9f6eebe,0x58f1dbfce776fb3fffffffedbfffaff7faddde37ffff7cfb6fdf2f2adedebebfde57fd2ffeef9ffff4f75effffff7fbfd5fedffbfe5ddff7bf7ffafaca0fb5f86cde7a6eaffd3c677eeefeefb37a7846dccbfee7b,0xf9ffeddbfffbdefff77fbfafddfdbf75fb6fbec4dbdffbb7efbdffa87f6f7fe575ff6dffffdaf77a3fff7ff77f7fdffe9fef57fd7f7fbaff773fb9edfdfd96dfdf6fca737fd79ccfd7dfe7fffceeebfbf,0x35bf4fffdfb5fb3bffffe7db9ebdbf67fdeafdef2f7bbcfcfffebffe7bffedfffb77bb7e3ffc77bffddbfefbffffbfffedff7ffdfe7fdfbde6fbd19f17ff7e9f76ecdfd6dfdfd96fb7efbdfbf6fbfed7,0x7c75f75afefef29fdefec5da571f7be97e68fddbffbfcecff6ffddebfdcfcffb7df7ff375faefe7e8f3fef5ddefefffffb7ffa5e3e96b7b7dfe65df77fde5ffeff5bb7f7ebbefebffae7b7beffebe3dffcfebfe,0x137fbfd99bf9d5df7bd65ffb8ff7fff839f5def5f97d6b4b4ff85ff7dfe7eef7bcfdcbf3f5dbdfbb3f7eefdaf47befdf3bff3efdff7dfffdda5ffef79fffbdfe6ff7fe797bdffb9f5bef75ffff0bbf7f786af77f,0xfed2ffdfabaefd1cfeffff95d9f97cfefe7f977b4fffff5bffe7bfffeff3f7fdf133bffef9ffd7dfbf79a3ee3bb5df6e317bb7bef5e9eccdeff4ff94fbc6773ffbb7bfbdecfbffea73b6dfefcff76fba8f7dd7fab6,0xd73fbbf79f97edd75bcfe7f73fcafffbd7ffaffdeffdea9bdffbf7db5ff83eaffe63bfffff7ffaf95ff7f33f3fdfd797ff3e3cbdb89aec3efcdf291bfeaaefddfdfadfbbfdf7ff3b5fbfffd9fedfad377fead3f69,0xf5dfdcf9f6bf5ec9fcfff7af71f5ff7bd35f337dff3bf23dbf7df84ff37ffe6fde77bf757edb5d3eff6d3f2ab8d3bffbffff7efff7de5f9bdbffbbfef7f7f71e26faf3f7fff175bfbabb5ed3dd97fd7fadf5df3fb73,0x6eb7f707ebbdeffff7ffffbfbead36fc657fdb575cedebebbd7cfabffefe976e59b73ff7723fbf7dbff3e5fff6f97253bfdefcefbfb7effbbf7fff7d7f79bbfff70f7fbef7ff37ec27f97dfdadfdffeb10afecd3ef,0xdf7f13dfbfdeefebba7fe93bbddefbb7fcdfffebfbbfaef57fdfa55e95efffeffadebb379ffbe5fffdfb76bbdffb5dfc7767fffffdffffdf27dfffd6cf7bbcedceeffffde3febd56fffefc65fdfcfd3bab53d,0x177fabddcd1ff7fedfff6b3cf99c3bcfeaefcfdffbeddffdc77e6b175ff23afeef75faff6765ff259dfef33733dfdaf7daaddebfe2ad7f86c76e55fccfeb5d7cdbffafff7f5cb27b9faffef1cfb97fcfae9fbafdd97feffff,0x6fd9f7bfb57cfe7fffafffebbedfdfd2ffefbfeafebb637febeffbdf7f775af7bb6fb70c8ff7fd67df9ff5feff9ffe37ffdf1f2ff7d7fffffd6fcfebfbe7bf539ff6d7feeffbfffbdc3efa5779fde7a75bf7,0x7b5a7f9ef97ed6fcdfcdfdd5d97efffff0befb57effffe72baddcf7fe4ffbfdffcf7f4f57fbfd7beddfbf67db3b2cffffd7d63b7dbd3f97e7b7ff7e5fffafdf76ffbf2ffe5f7ced7bffffefecef5f6f7ffa76f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n7 : packedGroups 16 16 30592 [0x1b7fb6efdfe57c4f1fa7fff7abffcffe7ef59fc1dbd3fa9ddd6efebffd6ef9eff38d4fffff17fae3f9bfbbfefadedbdef797e75ffdffff9feff7eefedbbbffeeedbc9fbffbfb5cf9f7f7ffd17adfe99fbb7437fcb,0x3dfbfec7eed9eb76febf5cd6efbf5bfefedbef9feefefffdbe2f7fffcb7b7fdf7ddbf2f67fc3efceabd39ffef7fefd75de79ff37fbbefb65fffe9ef79e2c8fadf75ffdffd567fcfddffdcbf5df7fbfdb5ffbd73,0x33f6cf7f73fb977eb76bde74e3efaf7fd75fd7de71e5ffd3f1fbfee7be3ee3fbefedff7eddf917e1f3df7ff7eeb62f5fffb7be9cfbeabdf77bffefbdcebf6372d2f7ffb7d7fffffeff7f97bff6f7bbfdfcffc9be7,0x2dfcddde23ff47ddfff3aad9afbfdf7fb5fffdff2e3db7ff6cfbe67f7ffccdf75bfdcff577fdfcfffcfdbfdddcffd3e8cbf756fcdfe7f3fee3f9ff7f5bfefd73bbbfa23efaffbbf38f794bf3a5fcb3f796e7fe9ffef,0x3ae79fb0fbe7cf6dffbdcd7dbfd5f3f8000000061d7fbf7fde7ffffd77ffdffdfbbe7965bbf7ffbf57ffafff8f7ccfffff6cf2fffafcbadff0d8a000000015fffaf3ee7ff338937dfdbffd1efafbf7ddfdf7fcffbefffbffcaa1def,0x1fbdbcff54b74eedb7f0f2b7fd369fcfef7e5fdaffbfb3fe317deff79fff23f67fffed9be8ddcfaffdfb7fbfeff77fffa8f9800000005efe6d63eef6f7bfbffbbb0ffa2b7f5fe3dbf1efd44f7affab1ebbff69cf1f79e52fc800000007b7b977,0xd964f6f3aefaffdb6bbd749c77f3e82f9fbfff2f5ddb200000001fdd7eeeb5fffbf4efcfefdd58ff3f9f65c4fdf7f7dff5ab5efffff751fdffe375fcc0000000377fbfedfeb6d64eedfcbfe5f7bf76fffa7d75fdf9bef0fe96ffeb735adddf,0x16ee7dd3fd7effbfebecedfabb1fd9ff3bbf73bd9e6cf7fc97badbffed687faf6bffdcfdefefdffa800000007e7dfff3fd7ffe59df3fc7fbfbf7e5e76df8ff9f0eff98f3f6ff8aa17bbfafbef5fdeb9deff7fff7bffeca7ffc,0x1afc0cffefefef3bd9d56a67ecffd78ed7ae967f7faff7ebff577b53bb5efff3ff7bdf9ffbf9cdf672f7fed77fd6f7a00000001befdfb4f6dbffffcdfefbfb7dfaefffffdfe7fd4f5f9efdbcffa7fd7ee97f6f6feb9b6debd,0x227e6f3fbffe15dbffde7effadffca5f2ff67a7cbe7ffb86c77eb7b7f7d7fd99bc71f7af5badf9e7ffbe0bfef3bfe7dbdfc2ffc2ffbf1af7ee7feee63e2f25e7f9ffffff2ede27fe79effefffafbfbef5fb00000000ffe73dfb9f,0x7597def6f5bd7edbd7fbfdcb65fe47ffff3f7ffd8d9abefff76f72dbdfef5bbf4f56f5effdf71f33ad5576b9bffdfe75fbffd3cf75da3a6ffa3bfc5ff6e975ffddfbf1f7fbfde56bffdfeef7fefde67fb4fdabfc00000003efb,0xfefeffbffcff7bfe9fff63ffff9fff400000003dff7f77efafdbfd5ff7f9dfdbfeaf9ddc5f7cd4e33feebf7ff352cbffbbaeaeeffeb71fce9fffbdf8e57fd9fef3b3df77effffefffcddfde7757273b6fdce87f29f3aef6,0x39fd353ff3fbf2ee2fd75bea6ffbd3df5cbfbdb489ff99fdb9efdedfefa34e767ebefff7fb74d4fd1ff3fefdbebdbcf2b179f56f6779bdfbfefdba73d2db7f700000000dfd3f9f2bffb95fe7fefb65d87ff77f6adfedffaacffc5fe5f,0x27dd74bdbfbab6bdcc579fdfb9f7fb5facf9f6fdaf7fde7bedfffefbbe5cbe7bb55f7fbfd7ff4f4f7bbdadd0fdcecdded7efdddffd7db579df3d5ecbf7cf1d9fd0c0000000367dd31fb2bdce1a3bdcffafffb7defbf17bf7ebff9c57b8,0x16dc7eef8fefdb95cff7bddb7effef2c6b5f5ab5d5e73bbff0bef33cddfbe9ee37867d5f3fdb75ebeef3ffdf9ff53a53cf9befeb06aff7d77d6fb95771ff667ff5e7baffd23ffbff5b3b77d5ffd567fdddfcdbdb7ae7f9e7f5f,0x2ffecfe7ffffddfc573fbf6fffdfdf56fdd6db59fe7edef3df7ffffbfdeae5fe6edd6ffbfff776d9c00000003eedd9e07b7ea7cffdb7fb83e83efffeaa6f674defddfe5dbf97efc3ee34feaffda91ffdcfffdeeab7bfddeaff5] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n8 : packedGroups 16 16 34688 [0x1f5ffdcb72d66f2bdfcfcff3ffd7cfbb7f7bd3f1bf73ddff3d9f56eb6f7ac9ffef3f670ad3dd593f6dfa95e4fd7bcebe90e7efa1fff7a3ed7ad7c5dbdfcfdedfbfe765fe6abf9fbbf29b5bab977ef3f6ebcabe7fb0dfdff66fdbf,0xbff9f37fb5dbff6db3783e3bf567ff5daefff3ff33f5ff1cedef5ffeaf67abbfa935ebebff7cc7aedaf778dfbfc7eb99b9ff9b3f9faa277b5eff376f3aad79575bfbf760d77ff8cbbdcbcf5a9bfdfde36efd4cce47f9ef3debefe,0x3f73cf7f1ff678df57cf7fafe1fcfdff05bfbefdfecf7f77dcdf33ecbeabfffbb5e6dbb67bfcadffef7fed7fbffffdfff75bbf3ffedef00000000eae7cef3debdfef5fdfff3f3dffff5df7efdcefb7eaf2ffad7edffff,0x17defa5f09fbdeb1e5ff27bdbfdfef77fe66c077fff7dbbfff3fbb0cf9ffde77ff4aedf1b5d9fffe68c7fbef5cbafbd5ddf7bf6f717fa7dfdffffeefbb7d7cfe43e71df4c3ff7fdeff5e7fbff6fefcfecf3ffeec7bb75,0x1ffbbff7fbbe93f6cdf49fdedef5dffb9df5befcdd11d7df3aa4ef4cffa1faa7377d7e53ffd5f2f6fafbfbbde8d3e34bbcf6bbeffbe7edffbdff9b7bffb4bf7fd91af9ffeffdfddfdf7fd7ffd6cbfbfb1dffde3dd67ff,0xdf3ad99fefe7f5efef2fddafebedf05afe9eefe77dfca1ed3eff5d70bdfcf2573edee8cff57de7ee9dff7def778dfdf6fbe6ffb77eff8ffebdd6557f7f16bcd357fb7bfffffedfaf2d537dd7d9bfdbfefbe7dbff7d9e96c,0xdfce97f8ff75fd7fbfab6f6fff5fef9f953f1bbfed4f755eeff7eff5ebf7f7f7bfbbb77ec7aff7dfefeda53f327bf9fe5a6ffb3cb8ffef7bedfa9eeafcfebc37f8fffefdffb7f5e747d76bdfd2f5fff9b3f2f1efedd,0xff7177f7f6dff7ed996f7975fe27fbbb7cfb5cd195dfedefb7ff6ff7eefbfb5e3f614fdf7cfc1e66fbafef35ebbfd7bab9f5df378bffdfff3febff7fa6cdfcd6f8bbb2c2eaedfdfd8f8daf7f57aaf657dcbf9ffde3ee4df2f9,0x3bffff3fb7bcfbd1ffadfbb1eb3dff3feaffa6bbdd3ffbde0efccb9df7aeefffb0ed97ff8d3f55e1ffe7e5f5d2fe7ffcf7ee5ff9fdf75fffeff7bfddecdf9f9dbe8fbf8797fa7d5774edfe7ddf7baf6f3a854d7fbcf7fc,0x365dffcebe8969fadbbc2cd5ecdfd4f9bded695fee17dfe2ffb56f865fd1ffef60fdbdfefbe7ffa7ddaf3777afffafd7efeeebf2fffe7be5eff375dfec67b9f1fa9dfc5a173f75fdf5c777aef73bf772dbfdf96fd73f34d4ed1f9d,0xf0effaa7bb57bfbeaebbf7deffffb65f5ff93fe1f77df9efff87fdfb53ede38fdebfe1ff87fff33fff6f36fb97fd9aec83df8be57fcdbcfc7fbacb7dee6ffdf67eb7f9753bffffff7bfbd4ffff7e77f1fef33fedadc22,0x7d97c0f5d2b6b6fcf84ffd7dff3fab72ff67fdddabefdbf7bd7fff89d7ebef7d3f5b76e7e59b7b5c747fceffafef7abf3fdd7f76fffff73f2eb7fee9d7f9ecfbbd777fe7ffbfecfff6ec8800000006d4cfdc77bd9bfe3f77f7edbb,0xfedf2bffd9a1fdbf3b37dfebf726d963b72f6df6efbfbed9fbfe59c7dcdf5b1fffdf573effeffbfff9b7972ebffbfff134dbd8abbbdeffce78b51ffd6afe6dabed772eeeff1efd3b7ebdebbdff172e7df77befeb75fdeee7,0x3b55f6fa72efe5decdb7373ffb723dbfcc4b5abea1df5f7dfdbddfbff1befdbffcf7f1d7ebaed2edaedeed1df717ffbffeddfebf133dffe7bff8efd74886fcff97f5777389abe7f77737b5abefee6b1afc777bdf3f7d6adc9cfef2,0x3ff9c6f7fbafff7f7ef6f2be325faaffd09a8f55f7eef07d9a9f4ec6f999fdfe3afff7ef7787f9eff7bedfa99af5b37fcee5db3fbafeff7ff7f7fa73f3ffd9fbf7fe62b3cbfd9fbfdd49d9fdfbeceef3fecfdfdfbe4ebf6e,0x49fdf6ebbddfff7bc3ff9feb3bebffff5f9fefb77f7ef9fffdf3ec37fed7fcf7c577dfb97bdefe7b7f775f7b9ffd7fdfdfd9fffff6afff7ebdc76d77dbcd6ef77ef99bfffc9e2dfefebbff5ae7e764d8331f1c79b3] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n9 : packedGroups 16 16 38784 [0x4db5e6dfabcfbfc5ffe7e9dfb96a54ebd9f79ffe7732273db2fe57e50f9ff7a6bf0e6b3dfbfffeaf73fff2ba0000000153d7fe33de9db9feefe731df6febefd77fdf5ffabffc8ddd8cffdaf4cf6efdeb7ebf7ddfd5fed99d6ffeb52ffdbc,0xf7f5feedfcff7fbfffa37bf9a1dcbf7fffdfe9d36ea953f7f377df76dbe6f67ff7fff0ef7bff4ffb0c5b3efdafff7fcda7b7bfe1f13e797d41ef9793bee3fdd7e9debceafe7f6fdb7b8ffebaa3e7f5cfdabffffaf6ada7d,0x5effe7cbfebddfffffdfeaf766dffefbd1c5ee9b8f8ddb7b77f1f89fffefe96c2bd45e7f7b7ffbf97ea5677dd93ed56bebfcf7eab56f7cdce3df969f1bfed7f7576ffbefdf4656df9df97b920d735fcdffef7763ced65ed3ebb6d0,0x51eee35e0b7c7ffe73fcb75cfe9fcf1a7377fbeb1efdfa73367bd7fefffb7efd3b7ba2abd827d35f16a3ffadffcbdfedf3b3adee9c6dfffefab724ff6fcfed3cae1b879dc2fd1f3b5fff75ddcf9df57f8ffdb8dfbfedd7fa9ac3fc39f,0x2f76bba73e6d5fce6efde8ff71acf3f77b6fdb397e3de8fdf2eb6b9deaafff7ffbe6fe97577ffb37ddff73d5283ef776fbf5dfffde2ff5bddff9f7e5bd7b779bf5bedf3d3bcfff7bd7e6f0afdaf6be7e7bffcbbfbeb9deff,0xddeff3d7adf7fd7737affce03b9c73aeffc73ecff5f9f7675def5fc639bffbdbfdf69dabfbfbe756ba7f01fbfaf6df87aa37afcff1d79fdbd7fefbb7f3fcbf47af5ffffffd69afcd6f5f677fefff1ffa3f2fb9fdc7fbd6369,0x3dfff6df37df10fffdfdbfe73aed7bfef97492fb1e9377777bf59d77f4ffbc9ac7fa6b7d6ffe79fdbc9e7d9f377ee3ffbfdebeff7be9f4dbace7b9ffbf76767e7af75ff6fe5bec6d78ac7dfbeaf88f877f7f7b7f7e57db7bed,0x325efebfc3ebbfd77e13e77ffa5dbfefb3f6ff64f73a19c9f3b7f9a6b9eb3ebfd7dfbe9ab42fffd3cfdafde4e3a7edf87fb75f78b4ffe7f4fabff8d57bfff9feb7fbf62dfffcfb5fd9d1ee27f5777cfefc3bff4f6f4ebff7f29b,0x7d74f7f2f7d9efa7d55d9b7dff06adcfdcfefdf7f71ff451f71abbfb7fbfbda7e1fadc5acfb6f7fafddfe326777b5bf56dbbbf378e91b6d7ff73573cb77fc37fffff7d57ccf47f4ffd4bf5bdad3b4f7f1ffffb4ecdb87ffe7edf9,0x397cff7fa9fcf7f4cb7fb3df3f95953f2b3fd7d7efdf6ff3a59f38bedf8fef7b36dd2d8abffea3f857f67fdbfbeef55dfafdabb2a81b7e7ebdedef4afbdefff7b7bfa2fd7ffe7ff1f77af9fd7dfbe1ffbfbffaf9f3eaff4be,0x1a69fff7fa6ff7ffbfefebefffe3c7dff79fbfe7652c7ef79f7e7f97e076f439e64f7ee77f776fd5fadbddf3fb7efbf66fefe3ba8dc3ddd7dad9af7c51ffe56dfa5ffd2fd777fbcaefff6fd65af7de77fec3fffb3f6ff4f,0x2e7a7eafff97f3fb3fedfbf6e2c31ffbff2ba3fba9bfffffb9fffbffdfeebe5fbfc46ffdfff5feefb7d99dffe9b7fbdfb3e7c4b76bfef7cbde75beeedfbef5fd5d96fdbac3aba3f7f6fff776b7ffafe73b9f6f6df9d,0x31fd377defe7ffb9fd9efff73efaff945edff91beff3bf7fafff7db7dff2f7717bdad6b7abfffbad457b7debbff94b2fedee73fd8efd5f938ead6fdb359fff96debdbbdfbf1decd73ff3d7f6f9ddecfe9feaaefff676fed,0x1fade745ef7f06ff22f0fd537ba69bdfe7fd6bf5dfff83dd277fdefb7f6df9df9f7fa9ab8dfedd7f9effbd3d9bb9bfe5beffdf7fecff39eeaffef1ff6b75f6f715af7884dffe77f5baf24fb7fbffdf7f6696f77edf7fdd7de,0xeefebe34fdbba6cf777fbee3a15bf996dfaffeb69cf9f3e3b8dffffffff76efe7f1bf427bf39fdb67d9417fde3bfb369ff6eeafbeefb27af3ffff1df6acf3ff3f2dbdf6efecb627deead7f77ce4b5bfbfafcec7ae55eed782a6fd3,0xbcb5f2e7f3fdada6439d677f9ef7fbaf99ea9f97db7da5bfdf2cfabfccffff1d587f69ddb7c2fff3f13faa59affff79e4ff7b7e5f3b0f347fcf8ffdcf94e7fdadfe12c3f3583f7afcefaff7feef8ffe3fcff9df77fdfb6ffbde6f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n10 : packedGroups 16 16 42880 [0x7f9bbfddfd5b2bfebd33efe58f7bdfcfbbff4eff5fafd9d74bdf7ffddffbfbeefff5b6f38373fb9ff767df5feffdebfe61f76bbe7fdee7fffcdebabf67aeedbf7c5bf5efbeff7576ffeffbbb5ed39f1f7eb777df7,0x13e8afaf7ebff4bee32c738ebd74bc6bf31bca79b0cee555db4efe7bdf3d50fbbfedfbf0ffc7d9d5937f67d7efffe79fffff757feeff7ebeeffd1a4dff7d7dd9bcb8de3edb83c57ddefdbe5bdfdc4beff75a4cebc7b6ea6beb719f1fb5c6,0x25c5e4fad3f5effffbfed7b5dfbfbf7fd6ff3ef9743b0dbf3b37fc7fabd7defd6dfbf79e1bdff1f7acfffff1ffffd387ecff55cd7ff3e1f7f5b393b21e6be3bff733edf476ffed31fcddc971de4eae7f6bbea6edef29be7ff8ff,0x357df7f7e36eedbe1e975f232afe96e7fb7bd6d3efffdc15afe3fecbd7ef3f57e3b2f77e9cfe77f9dfde9f3fbffd66d78dcfc79ef9b7edfb54effe7a7dfc72bf2cf2d13bcdef70dae4e4effffa9797ebeeed9c557bfc9ff7b515f5fd7,0xfff5fd97757bcbd4e76fbbf5edba797bb4be7bdfda77fe6bb7e71ffbffe7fee77ee711aec5fedabd3f67fedef7ffffffb3dffde6d9f3fefc7bdf2e3afdf73efbbf776fd57fdbbfd9b7e695acbf7ff2eea5f6af55f76f7b,0x3f72fb33d771fb57e5b6f577fdbedfacceefbbf71ffbebb7b23fdefe3becffdf4fb566f9dcb7bbb58ad29bfc7da5ff77bbfafee7b7ee9fd1f464be7efdfd1fcfdfdeffee3fbafbbf7e4b7d171d97477e6db7fa7a34dda3ffdf6fb,0xcd7fdafb5bfabfbbb9ff15a7bea4fdff23ffe8bfbba74ecf9fbbafcf9fcc3074fca8dfb7a3eddfbda47fffd03b5f75edd9befefa74bd3ffeb9a85515956fefc6fb4f53faf9fedfe97e7effd5b0fbfe9efff6dd9f6afbfffdff7d73,0x17eeffa7effbeb3f372ffefef7fff4d8fdbeb3bd96cfbcf7e1d53fdcb3b7fdfcbeff9dfb5b5eefd5d7b6b756d6f7fccff17f37bdffdf2b5f7fea7bfcedbe7feb9eb9f5f7cf46bbb5bffef1fbe7ff94d6b7a5dfd15fdc95ff,0xeded3eb7bfeed62d6fdf6dfe7b74f089f3fef6e3dbfbefd5df3e783fdffa6f8cd7d7cfdddeff958fe95af7f71bbed4f57f7f2d6fe7bf6e2d79df6ddb3bcfbe35febf578eedfdbefbed51367ddfd3ff173dfdd9c99dfdf9f3b36dcb,0xc7abb9f6f82f7ffd56efacff5770bbf97ff4f7ff4cf5b65ec69e77ff2af775b5fde7f27a9d7ffeedfef3f9c9bfef7fdfbefbfbffbae7f7f6d7ffb3feb2cf97c37e85eed6f7fe23d7dd3eed557aeff6dc2fd78fdd957ef71d7726,0x5ffff3df5ddffcfafcbfa3e3e6be9ff42e73efe9edbaf6fdbffdfbfdf7fbad69ffd76bdece7e77bdefff77f978afb9bfbe7f1c2f9ff3af6efdcf8772bdfbfdf4efcea7ffefff3bff77f2cfb97fffdf7e677f82f98dfe,0x1dffe2fc7a55febc9fb63d55efff57ba7df9ef4ff67effdeff7ef4eb5ff5ff5febbdee9ee63fdfc7a7fbfdbb9cf9ceebff755f7edeffb533e7edbfbdfbd8bc30fcddebd5ff94fe3fe50e7fdf6fdd7ffdfe3b1f27d9f8db3f5,0x1bd8d6af5c769d7fe6ff7fdf7bbafd47cd97e1f6cc83bfff3dabe97eeb4fb8fdcabdffeffbf7ffe7dafffb75fffb6d8fdb59bdf2f8ffdef1ab773fefcd757bdbc9fef9ff9ffffe6f16fefbffcf99aaf776feb6d56f1f8f9bd,0xdde4fd7faf473bdf6d6fdc9e3bfbbfd8f48eddbdfdf677e77fb73baded6df1a8bebfeb777df7efffeeffcbdffedf7cd50eefb76bfe7dc7fb2dfd94e667fdbbcfbf97df7fce89f6fe474aa371d3caff5dffe9ebfffffefee3b2,0x1fcfefbd67bd595bbd6275f73b49f7f1c7bedf9fde62fffb6577d1483cfb85bdffeffefffd3f9edb8ffddfc9f9bffbc7f3f7fbdabfef2c8dcbbff7d5fff79dfeefff9cfc213aff5334b5eabd3ffdd3376eeaf7df3b5fcbf773df,0x1bff97ff9f6fe7b60cfc337fdfb3fb7f5b5ffecf9397aa7a9fef74eb7dd6eca7defbe77e9af3f4a0cbd259fed6decc5dfff9f790ddfadf8aff416fb962f3efd5c4facddd3ffbd9d5ef6f7337abe73ffafd77f779565bfeffbd7fadff] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n11 : packedGroups 16 16 46976 [0xafd3f0efffa6fa1dec877ff7ff2f07b573fff377fffff7fb7f97b975f5eefe7fbeacefb3b209be95227f3abdf78bd1f6f28dfad61feef7ddeebcdae7767fbbfb3f9fcbbf7fff767fb3fdcef6bf7ebedbb7cd677f717f37e7ff,0xf9eaef3df7777f3a6efdb7fbffe6fefaf5d1bfffbf67ff5ec2bbe83d53d6ce7ff9bcecffff0ebeff7b5b6a6f6e9bc957a7e8f6f9c69d1f3c7c6fffbbeffa7f9cffedea2a7edadd79fdc5ecfe7bc7cfe7dfd7f7ebcff9dc9afbf,0x8e3cf7f3eded277db72fab7eaf7e8a7e5f8beffa3fc7ff665c1f5ffb9fdcf76f6f9d3efcd5b95bf9eb8ef79ed5bdbdcedc2fdcbdfd79c57bd2d7e0e5ced6faf3eb6eff5eeaf1fad5ffee78fedb9d4c34fb7db3edaeefdc4eb79c7863d60bd7,0xdb5fb6bdf59d5bfe7ff6b36232fef7f9f5d47bbfbbefdffbf5cd9d7ff1f6f19fedfde4fefcf6ff979bfceef67bfeeff7fafeff5cf7eb6f5ff77bf2bb7769fd8f3dcfef6eed8ffbaf355e75fe37a4dfb7cef4efa1eb5cbb5cd,0xfd7f999f92df9fcd77e34bae8d6766e367ff95fcac6778bd39bc72777bddbdfbfe6aaefaff7ffb6bf52d2bbf5b7f57fec7fcf76fbafbb6efdf85adbdef6f9befe7d96dffc1f7fa4e1ffd7ffd43fedfbe7fedefe7e566597fffdba,0x5dbd6ef3f6dffbf13fffae6dbdf7b3abfaeb0fffddeff4ebdfff5426ffbf792263c7f3cfff2dec6febdeaf2fffedb51df776cfffebf76fdff7ffe73ebfafefe77ddf8fb5ebd95dbbffe5ffefdf7bbdf4beff75fbf77,0x17edd79edbdf1edfbf7ff3bf6e5fff7fff33be7ca7ffffeaf5bfcfeec7ff1bfbe5fbff17d9f7fffdfdfbcbe87f74e7ffa77bc5fffbfbc73b5ffffa17b7f9fbfc6ef97bbe260fdfbffffe2efebff1d7b5f1effffd4,0x16fef9cbffffb55bfddf74dffbfafe67ee70ae1bff9f66b62f4b2d6ef2efb739b7c87b9bfbfbb7dbdd3b54ef1ecb559b4fdd6b75fdb1bbeb7dff5debd77637ffabd736dffb36b3fd1fffde8faefbeeeea9fce3766e8df4ddb557ffc7,0xd4edf7adecd7f9bbfff5f4fd5d765df586ff3e7f4ffdcf755bf7fb3fe573bdfea1063b77f17b1bd29d5f7efaff6d7da3fbbef26f7bedb5cb755fff1bfbbecf9ff7d6df0b9ffe79ddfaf393ff6feeeffddef6b4ff63b37c76e5aba,0x36ce0bade9c3ffbafbf5ff4ffdb7ed71ebf6f7e107e7eb1fef7ccf7bfaee5fd7dcbd5f6df8aba9f9dfa5dbff69a3fb1d0aaf3bfcffb86dcbebc9dd79f8deddffa7fffbeeceff6d9fbcf6fbe9969fdbfefebdc9ddfc5f3d75db27f9d,0x3df9bcfffbccf7f5f3aff89cfdf973edfbf74f8cf7afaff9f7e2fffbfffdd71fdfe0a4fef7ff4f77aff3dffcffefbff2d7ee9eeefdff5ef7f5e237ffb83bff9b549daff4eb4fe71dbb67cedddddfbbbae917fd1f48c5de9ee,0x375cfbbba3bfcb7dfeffb7e8f3cdef23e93aff3ddf9fefbfbfffe5a7dbbf3f6cd7893d2aad6ffb77b7e9bf7dbf7475d668f4f3d7ccbf76f7f1274e7f63df7fcfff68fde7dcbef7bdfd7d7b7d7a6ebcdfffc7fdf1977ffff6dd,0x16ebdbbebf4650dffdf0dd7557fdabfecfdfddf5f9efbfdbbfb6f74effb6a7eae7a929efef655f5bf276de7d6fcbffff36bfcee6f9fff6bf7dfdeceeefef3fe9ca3ffb7dbfb591ff0dcd37bce9f7ffdebbebfce02ffaaca6ff7,0x5f5524f3beab397edbfdb77fb71ff5bea6ffbf7bfaaddae2b4dfd7f5dabf7f999e72be5fff5d751febee3d7c3edeeaf3f1974ad9afffd7fa77ffeaa9a7bcabec999c3f3eff9bd00000000fecb57aadbc7f63a47deca6db76affee0fe7f5a2bfeff6,0xdbd7f8cbe5ad547efce3bfbc27fecf5f2efae9e6b9edb6e7fdbfd9b3c27bf3fff7dde2f7ce8e37af3df7a8fb7fff2ebec6beefdc2b078deaf66efdd1f29cfe6bedfdedf5953f3137fb8fa7f7de25b75edcdd53b9b3feaf64fd6e3d97d72bf,0xdf2ff3acfcfecd7c9d9affed75bfc0cbe679d1fbfd2f59de256aeef797bcef75b37c7b676ff6f7b772bfef5fffbaffeff6cee7cbfb8aff5ffaed2f9dd7fffeae3cf7758be12df3befefd7eaffcfa9bfdaeb57fb2fa77fe4fb3f4d] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n12 : packedGroups 16 16 51072 [0x23fff81efdffedd3fad5daaf7ffbc71a085ffb7ff77e9ef65ffb2afe99f7eafba812b79d5d63d63d78cfdce3ffedbeffebfd7e346feff7b65f273ab2ffb7eff7ffb7364235db4800000007cf1ebf9bb3edd73ef9baf35a5f52ffbfffe5e6d1f7e,0x1fef449f8dff7d79f7fed79da55e755fcef7af9faffebc7ffbd7a7cffb0dfbb6ef6bffebbfb7ec8fbde9bc3fec3fcfbe53fd7dff1cfe4fefddbff34fce787b7599bd97e6b4d7f5dffbe7d7e97fd4bbe2175ffe9b8ffcdffffc5,0x57dd6cfdaff2edbfefa6efdf7dfbfa9bfffd7bdaf1be1c00000003fe8c20000000177cb8b78ffbb5b1bebcdc56fbfee77d6ed53bc7f219cdbb9eefffcff3cdbb96fb9ebafdbbaf9e7ef792bfeaffd47c6f7fef46d7fc1c63dfeefbd07ff7e7bfddff3,0x16d88fff7c7dbbb7fe70753e6dce9757f59bcd3cbdd753ff2efdec77fbbefbf63f5d7fafbac5ffd7cf7b31faf7bbeffb9be5f73f3ebbbfd8db7fffbbbafa2feffe4d7f7e5cd7bcbfbf979d09fff2ff0fd6f5eedc77fed6efedf,0x3ed5edb7a5fe6ee7fef4cded8bbfed7f6ecd6ff5ceffbbdfeb5bdb9edf6f7dade1f1f9f8cbfc1affff047bdfd4f7fdbb4b8ea3badcdfce6ce61bbbeffde418e0beecb9e7fde4fb6d5bd3afce500000000e9cffdffefb2c79d75ebb67ff8d2ff7ed,0xbb6b7f6397d64fff14bfffe87ff8cccf77fff6eebb8bc57f3733f55f36c5472df3ff5777fe1fe9f1cda9dfdfe14e7beaf7f7f65ccd71fb7e026efcfcf7eff797ebebfbfec2fbcdc6efcbe7dba7bdf8beffdd1ff5feef70fcd3ffe7e,0x3f7efd9c6e54fdbcadf57ff5cbf8df6d77bea8fbaf9776fff72f73e1dcbc77fdf5efe0b79bf502de74fb3e3bfea555adfbd7fd63dfffdfdd7f636fa4ff1b53f5fd94c6f7aca5d7f8ffecb66f27dffbbf597b5c4a3ebfdf2fef61fecb25d,0x2f7f9f39af0c7d586dfcf76a679bfecdf4ef839e57455eff78f6b3f9bfee8eebbefce9f375d7b7ccb639d675ed6b7ef0fcfce5f377e7f66d9fbee61ce9db2d2ffc9be6f3f8fddcd7fd57b6fe9de97fdf9b7a563ef6f7b15fdb0fb5ffe5bff,0x1dafbf9bdbf7eb9df13af7df7bf262fadb76ffddfe6b1f25e87eff45571ff2bcf3c9ffffcb9b4d9967efe8ff8e27bfb5b65e7bcec670378cf5b3f6ff5feea1df5f5fd3f7da7b5cb737d5ffdded57f9dffcff5777df244fb95ffb71fff,0x55c2ff8de8af7dbffc7fe5af39f7ffccddbd3dc2d37d7e7eba00000001bc77ef7d7fdb79ebde597d2feff2feaff361fa7f759cf9ffcfbf7f800000007bfca3f55f7d4ff8fffdd4b2dcce787f7fdfa7ef42fbffdadbf7cefe9c5fed577dcf3b9a7e6f1,0x16bcbd7b936977cf5cefea4cef1efdd5c85f7d3df7bb2fbd1f46efefbf6cc1fba7fcc6abc783fae966285f3febb7db75bf8eb6b95f16cdffe7b7ffa7b33ffdfdf669cebeff67552cebea19ff6e74f72ffcfc7fe793757ff27ee60fdfde36f17,0x3ebae7feaf8f1dfcb7a271dbfbc05bdfd4e3af6ced5dd8bbc2372c41d3b3ff87eaa1ab895d7a709fe7ebed79f2fcfa7ff7cedaabd79effdebff5e773ca3d9ea7f57acfe2cfdfefedea7c7fe41fd3e77bfefcbf1fdc7f53f7bdefb3bfb39d71f,0x3e5abd1e8abf7b56dbfe9f2ff2df90f115fb7fcabedfed7771fd1479daeadbbfbbcffbc17f6ff9b5b7578ecedff9cbeeff7dfc7f4dbbf93afefdc89fba3a7f5deaefcbe0fc9be977df4e5ffe9d2ab469db1d9ebffeff71f7db7fdf1c7f6,0x8ffb83fd4ffdef7fe9772b6acf569eedafbfa3bc651dfd7fee9ddddfe73eb7deed65bd00000000b8a16ff076ff534e5bdcdf77fae2ceee3fb69ef0cc406000000017ab8eb8dedebfe57ffbf7fdfe89bf2a7d7bffc6fdb76efffabfe79b437bdbefb7daffd7,0x717ad3cafba37dbf6a7ffbf77cf22cfafd5379ee33fd71f396ffbfabb9fecfdf5937df7fffffdbf7a739dbe3bdddefff77bffff3f37c3adffffbbff5f6b39f5fe9e5df373df5673fbdaaf65aefedaefdfbd86d7e329c43babf5,0x5fda504f6ff5e945cc48fffafbd7f6ccbff3dabfc3e773f57eafc5590f7bab469795b7ba3fdf7dff3f9fcc5fdf5ae2e77f693eff5f7f7c4ffef35dffdffb7ffaffd7e5f7feddaacff72f25fffe7df1d3fd7bbc7ef790f8ebebfff] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n13 : packedGroups 16 16 55168 [0xdd7a864edff75a7fac7b7d8e2ecffff7f0edb34fdfe6bef2af75df6b9bdfffa93f77be7f1efce7ed77aefebdeffef1b74fbb6fefb75f9772ecf796d6ff79527d6eb1a5a5b2fff3cc38d674fb1b477c9fffebe6fd53f7f9f6bff6fdf,0x1ede13beddffb53c7fff3ec3b87adb9eb7fcbe76e7beadfcc53fa7c9e7effeefdeea439fdb87cf7be6fcefbdd4ff36fbebffaec6e57c3e1dea5b2fff7cdbe7bfb7ffc6b64ffd56cf7febd7ddbf34fd40db7feedfa79dcddfb94ad6f7,0xbcfdb4effffef851bf3ba75fbbbf7f29657e1cfd4aa63f35fe36f8fe5fde79cecebddf5f787d9f3dfb3ebeedd78bf3b7ffe77dfcffee1bafbdf5ae5f4dafbde1eff9ac5fbfb636f1365dea57ff85c55dfcfc56fde7d9db6de79dfc83fc,0x19ef99fbcf3631c7f7edadd651fbd77eff78af6f2bff7fee47f7ff7bf77fedc7fdcd7b7fef7fb6a2f7777fc1e53efeb1e07cdaebe72ef25bbac799fff75ff83ff3bef7f9d6b7e79eff0bfdf77de377ff6ed75fd7f6dfeef31f45,0x7eb9b5ebb25b65141fea8f3d747fbdde697ffd9befbebdbf6f532fdbd35cd78bdfcfbbdfbb5b3abde44efdfcd76df7e4f7bd7ebfdfcadfdb9d3db3babfacddff53af6fb59e51ffebffdeb9bd5f800000005e77fbdf5ccbcffec6d07fab8d82fbd9,0x1ff8f8df9e6c6fd1fbfdf46fbd3ff7dfff3d80bfb3ffba3f10baffd9e4d76d78ff4b4cf147effb3fede5a579b3feeef6b64dbfcb56dfe479bc8a6baed9fefb9efff260579fc8f3bbdb56df8cecb77f61fdc6f5f507366778edca7ef3ff31bf1d8,0x7ebddffb3f3fe7b7c73fdb9fffffd7daea2b6ffc7b5affdcff82d3df7ebb7e6d55ef7f1b9fbd5bf5d6ef6ab559e5ef977ff53bfc97262ddb57d73ee8dfbafbafed3fee3febda69e4d7fcb7eacff73eeff9fb9ff23a7f9d7eee6f,0x77795bfcfcf35b6767df6f5d7d3bfffa6f2feaaf7ae67bfab2d35f6f7dff77766effbe9dbeb9fccff538fdff465a576e4fee9dedfd7da6ff3dbf77fdee7f99f37db88f879b7ef5730f9eaf76dfeeefff7fee4f32fbfe5eb2d97b7,0x1ffe3fbfb2497c757bf53fa1df7fbbf9f7adfa1636fe7f52ceb1e7b67d17bfa37bfff9def8c7d7dbde56a9ff5ee2ffeef7fdffffde9f8dd66795ebd5a7f5ffee5f5efe47fdf63bf5feeffffe6fabf5fd57abbfafecefdad6bf0,0x2f738fd3e4f94ff4bf9f7dffb7ab3d6fdcdd4b62df5b19eff98fe7bdefe7ddbfffffc77f6d6f4edfef7f9bddfedbfffba5fb13ec4eabdffebfefede7ee8fc9adf76ee9f2ef0fdd52e3a53fddb1f774ff21120f9ade6dbb7d7f738afe,0x189fbf5228f367b56cf777fdfdfe7cfecf5eefa7f8854ffda55de5fd9fbc00000002f7f5a49f29bd66ede91d8efaf5779dbfdebabae5f7ffbfadbc6db979eeb9c3bddd9b1f6fb7bfbaedbf7efdffb7cedaae32dffedf7c7ff9f0579d79cfbdfcf,0x2fc7f6ff8f7bf2fcfcf49635cf4d2ff9bdafbeb4bbaffa75dff1eab7677eafb5b9985f18f77dbfa7e4dbf3f3bf8eaefb7dedf46f56fe3ad9ab47f7affbdabcf5c3ebef6e5fee7f6af7eefcfb7e7c941fff6ad2e2e2fbff67f31ebe665b0d,0xe7dfdd7faa39bb1fafabfad08edf6f9fb1b7bfa75ef99beaf3694dfbbe57f6f37df8ded7757fa4ffdeedffdf7b33defe4b7ee73a8fbe26bedf38f7f91ebc9edfe57e6ffeba2fd7a8d6ec24edcfdfbfd70e3c63ffe7fffeeff73fbef,0x197fdddef737afaff635dfdfccab876dff6f6fb05efb6fdf55ef55dfff8f9c6bf1bf3e7cbe72bdeeadcef7febbf43de6ff04efff5e4cf5b6b013d6c4fff6cee77d365a7cefdeeddd9b7df9ffcdf6f6ffdeeb3d79fbfdff7bead5fb,0x7bfe5f194b6fffeb9dedf6ead1750af5a7dd977ffdceed7b2556d3fddcbdf66bf17f9f7f6b7fe7e78a7e8f19b9cfef75e75c79fe7fe56fe3f365a4774d9efef738b3d77fb1f6bffcfbffe6bf7f3d3b98e0cd8bfc6fb9cbd7f7e7e21fedf,0xd6cfeb3e776d12ff3a5d37c7bbfd514ed9397f1517ef1e0e6e33ffed93f55bec98bf5f75bfcd99cef32d72fcfeeeff7ed6157b5ceced12bbf8694f6df706ff2ef5dee7ffec656ef9a7dfbfbfa94d6b77f3eb8db8ec4e7eb5eeeef3becabd0fbfff] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n14 : packedGroups 16 16 59264 [0x199bdfebe0f97d677d277d6dfee7c812bd50f65ddf66d7e6ff6cdaff9ffddedd9556ae52fdf4d2ed70bf97f19fda77bfd6b16fdfd9ffff2502fb4ebdfed9d79fcaf733d7f352bac8fa5ebbda45a9bb3fddbfefeacdbe773fefa39aee317b2acfe6,0xcf879977a7fd6eebfffa39373bae9b7eff621eebdb7ccfd84dbf8b761fdbf6ffb2169ff4efa3fcf6b7cbeb27c1fe82ffff6277bf96fb6ef25bdbfdf9cef5fc16fefd343d6bd7b1ddfeffcfe371fcfda9f0d95b6b2e5afffb696a7977e3ff7,0x1137bfbdeedde64dabbb83eff3eeee73bef2df2e39bdfbffe22af29ff787aa5fb7dbdd29fbce3e33b7e09df39ef7fb9f5db2a5efbfb2593c7f8ffb5f677fb3ff7c8dbb9efdf7ff3fac5e739b5d4097f6d1a6edebfbe7ee57759172d37efd2f9,0x5eb7cb70aafbfde7f7f7a3a7df7fbe5e67efe3bf71cd77f7bbb7fe12dff7bf3c6ffbfbbcce6bf75ef7d9deb976b623283dab7bf7bfd6bcbefeb6fe9d19769fd1bd9ecd173f29bef3f5effbb391eacaba7eb91e95f67f8fbedee7ff4eaf,0x8f3bbd9cd0dec9ff2d9c384ec7f5fa677ed5be1ffffeff73bf97b97dfeb4f6edff269962f2d947dedda38ef47bff9bb37da9eed3eaed9cd373e82873bdbfbcfb2fb764ccbee7c7b67ef53d5f7fcfee2b1f700dfe7dffebf3defd3fbc6aebd767,0x3beefb4d7fa9dbf7edfe7d7ffbee79cffab7f87f65bcebfbffd7ecffe5faf3e8ffbdd3a267f73df6b77cf7ebbd9bcefdabdee7ffff5e4f38d34d7c8a6bbc77fe77f4bb7f51de5db579e2e97fb92ddaeebfddf7f9ec8eff7975657,0x37a79fc77b816efaffa6e8f4ff7e8d28d7fff98f3c6ea87be72cab27d05e5defffe36d7ef69af6efeb5efe36fefd2317ff1b5bebeef4db79ffbffbe73afe7dfb5a4ef15abbf66f7e8f971ef8ff71c54eb769433feedb9ffd7dfff93f7759b,0x752beb75dc6c2e7bbfebe7fe253eecf58ce8f3bf27f43ee7fdf5efffefefbf3e57e7ff7febfa99f91ba7ede9ffe69ebb9db3cbadf74daf0eea1e374f5cf3f1fe7f7eaff6661bff67ee6fa45534f3a57c7dd54ef76ddfdbd7a72ef53af77e,0x7cc4bbffe867def5ff1dffff2db72fbbbbff7f7bff7bef46fcfa9ffcaeb61bef0ea79bf57fabf5e754f7f87fe9f73bf722d7ecffeefc7fdb7f7757ea5eaf37ee9b6dbecb7e3bffe6625ff31f7bb486fb76b67ab7d3de79d3c2dcc35d,0x1e5b3d6f9ffe99f76fbebdb3a7f75dfdd9bdf545905bf7d57f768e77cdfcd7dff7e74167758782bf5d0fbff3bf7305d791dfa55bfb1e7ebc67eff21f9fff25c56599f0ef8ef0ae9b965deee9fe7d2ff8ab5ea3abbd782fdbffd67fbff43ffc3dd,0xe7141ebedf1a96be4bb5de29ac0be5d3fc57ef1faa3adcffc7d765f8e905f98d7fbc9f5d2cfcdafee9aff9fdddd9e83e7f6a5ee61fff5f6ef75ffd3ecf7a7aaed5b7c47effe5dd575bf17853d7ff3eb13947f5614f8ff9cfb4bbb24b7c6faf5afdfda,0x374ad9ddfbdfefff26dc7c73b71d7137df7fe7daf7b6fdfdf6b6779585badcefb72f3effe6cf785b5d7ffcc1ffd3faebfd574cf36abfffff366db376b377aff765fff84afbdde5faefcebb67d95f73b7e3b95fdd3bdf3ccf6746e56fa,0x3c7ffb3fa7fd8988fc4f14bd8e7fe4d9c0ecffe7fdffbdaeadfdce79e6e67b9dedd6d0c77ecd63f6ebc7fec0b75bbf67fff37ddfff7f86bbf9da81efca7f6bc17ffdbd6cfef794154e76a9ecbec7f344ddf4faffabfc5bdcea6f6fedfe9fed,0x1393bbf9eedc7fffb6bbedf3eb35fa35d9f27f9f6f379d6e7b1be3c6d3fbdbf7ff6bfdf6f557fde49e3f7db686efabb6e2f7dacdf9fef5de09a4dffff77fcf74bd4ffff7fefbecf235b425ff6f9df873d77cbddcebb3fd567f2a7bb7,0xf2ff5f947f894bd999bbf5c772eadf7dfe0a7cfecf9b56fe7fe58f3b1a8b7fffe55693aedafbd9eee7be5ed4f7effb6c5be6973f75737d69425915d9f7b77abfbdd6feefbabffedf3c5df8f6e29b43d67f76ffedf9d733e9f95cddbfdf5fe,0x3bfff5adf8feaf37affdbb9eff53b9c84fdf282fa976e97bfbd6aeeaeb17eaf73febcff9b1518e94bbb3f67613bbdc6d7b5b7cdf17f42316eeba779fbe16dec3f7df6f5ed72daf5e742ebdeff2fc9ff6f5afb87fbd5fbdff6b766bce58ded7f01] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n15 : packedGroups 16 16 63360 [0x4d6fbcea7f7df33db67666efabf23deb667959ffd77553efb1756e9f7b11b9eeb19cafb6bff6be7aa3dfadbd5fe3be6437fc6d45ab2dfbffdb5bf763f663a3618b79eefbec67efb83e9eff8bbabd16ef2528db7777ef55d05ab8ea7bf7745eb4b2ae5f,0x1fee2d9ade617e6bf75f3f7bd63d4efd7f15feadde86be777bf5bdbae097ff677f3465cbcf7deffabdeb92f99f6dffbcee2dba55befffa4fe30aff2de74f79f33f738794a4f9effdfd179df6eb1fa7af5fcffdfaf7fafb1471dbf6bbb7ee,0x77fcddfaa6f0cbeff6ffd8f3be3efc2ca897bf7bfdf2e25cef6c793f77fba9ffd6ddf5f478c95efc7e2b52fbde7ef2ff0fff5ff99af77ff67f57d7bd5fc9acf77fbaf7df55fcf7ba929f977d35bdecb93be915fa732eb15dcebfbec6fcf,0x5e6456afd7ecfffb2fcedffed7d8e3f3dfdcb4a679e5ffbeefbb7b6772fffefefd54bd6baf86b9f7f9effc99cfefefde57ad477de6f99c2376fffdffd7adf9f6dfbfefb2e593bdd6fd6dedbcf195fcf8fdbdb51ff757796fd9e477,0xcd5fff94ffb2f76c79f7e2af45ceae37ea2fe0f47cfff757d8fcef6fca78f79f3a57cfffe2fa94c9bf577e456fdddd9ff96effcd9ff49ada7ecedeae9f4bf37a97cf6fd63bbb9d238a7ebd37af9f7674f357553d4fc8378d66b07ffb146f45eb7cf9,0x1b4f1a6436591fd9d3ff36f4d3eb7379766bdd1addbe0fba47e5fbd9f4eb3fe3be594e2bff3e21f2bef5b6fee7fffbf8db597fdb64f7bcfdc9f38deb2f12fb7557b22bf72bebded276bdfffae31f7fceee7fddffb260da8a5feb359f9f75fa5fbab,0x7eff586fefb3ff757df7e7ffdbef3737f3ee553776f6dbbf9b267b819bffbbd773b66d35ee2c6e777f1fce6cf5c556bb9c634def2bbdefd95c5f7bffbe75cdede97ef7b4f54e4ec9f5ef3f6f7c2fb4b72fe5ee99be7eebbadf7f3a7fff,0x3dd78fedf1637fdbbdf0de5f93b9ed75b49b2bbaab7f553af3e57e4f7bc4eeca057f6e0e837fd54a7ff7ffdf3f926f31eeaf5f326e17fdbacf9f76b43f764b66c79fcf9ff6abbd9ffd90ef773ef5ffefdb3c6f779eceba6bfc7dd8bb2eebb1f27b,0x176dffb7b7f7beefbf2cf8efaf79a67e655b9967c7df9c53f9647d9b6f3fc8f6c39ff6770e7b85a75137e7e2bd1f5ee87dd544beac7fe87a2df5ffbff3bfa547577f9f7e4d95ded6ae15bf3dd5ce77b9ecfbef25ff9be124f8fedcf9efded3bbdf,0x3bedbafdbadbfe91f7a99eff4efff9ee3b7ebee8f7efef7cbf77f27fb3cdfff67de78eb9dbea48cf9ab79fb3fad8eafe2f2f5b30be6d7b7784d57e6ff956e62ef5b7ff778d3dcbbcfe8b1cffe9ea6e44beece33df88bbb52b9daaf7efeff45,0x4ffff136b2bf725dc3bb3b92c38ee6aafdab1bbbff15e6f77e5ff2dff7cf5ff422bff23dfd73e9b6fc9bbd2f7de5f3ee96efbfb9f747edbf8fbf3fb28dfaf95cb29ce77f7acf93c976b9fadd6cfdc5ba1eb9fdfedef7aed7fff73c58bdc563c,0x17e7ffefc97f8aba2767e6fcff71d5fe4eff3d7fd219cdc5dfef57dffce0e1ffc7cc5be7e7dfeec0d4e5bfefe67eab2d1b9e52ef2ca6758e16ff39e79dde36dea877bbafbf6edeed6bc57e87bdee71bbafbdbf194ffa3f5a9f73eff38135af2f7d,0xdddefadfbd5bf56ebfdf376ddab5d3dcb3def371be37efeafeb47ffa0f9dfe5ffdc7b63ffc9dcc79fdfd98dfce7fbba06e9e18c737a376ede9c6be9b597a7f4bbef1e252ed3ae6577ef5b05fffd36a53fdf7cbfeffaeb6cb7f5b796e0f1bff,0x79c29eeff8f3efdd5c8c46adbd464bb137a7f5cf58dfdbd75b6d79fdde744e73da65deba5f6ebbcfbf9bffe7c7e857ffaba9e66a3b5f736bd38df7b77ef9ffeecfbbfeffe66d9b547d97d76f65b2f62b5fdc9f6e9e40ddd3626eff26fbd2af8125fd,0x15c55b50d34967faff69a43befe92ffea7dffc77aeb3db51fcef5db26fffce177ff97bccdfff53a7d7189eac757390ffebf57c437271ffbfafcf4bfd9fe13f3fdbbe8feffe7f3b3eee4fd7fedffffbe9f3bb6b116dbbfffef7bee57b63d,0x1efbbff7c9f59d52fbb59adebed31f59efa8f9793e9e9d6e9fcbf59affeaf755b4fdfdde7fd7f3fdf677e8e37667b9fb9d5aba626b78f2779eab7c56ba89fefeb6f1abdf71f8bcb8ecef8f9e6bf00faaeeee6c51dbef6e8dfdfdef5fdd26d6f79] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n16 : packedGroups 16 16 67456 [0x3eed8ebd7f77ffd7acef63fdda9f6afbf79d5eebb2b77fbf2b27b7fba54f7fcfb7be3c3739ebddf9bfbf7f4a7f6befe7fe5afcbfbfffe43ffa3d293edffcc75e9fdba0ff6ff94bfcfd4d343fdf6ddfd99ecfff87ee6fd558f542eec,0x294dbf9efd5fdc64bbffdf3e5fdcfeb7625e5ca57edb7b97eb8afdff335d7bfb8facf9f17c7e7db3f32ed7b57b3fc6e5de6cbfbad6d53bd8f8b9f0ff2aeffc2a59f9ecb3dc7d5cbf4d99d22fab355cde79fc897636fd7c72b7bddbdfaeb1b5f788be,0xdd9ed54dbffa1987a3475de063fe97376d3f748ed7941b267ffb4cbd9e56de6fb91e6f26f68feb6fbf7efed27d94a2dfe4f9ce9f7d7e6affbbe27f0f369e58dd6d7e3d8f2bde683bcf6f574a4bd1c7cf74c7dbc7fcb37efecd477dd4cea0fb1de3b6f3ed1b34,0xcbff7e6bf6cfcf55dff3d19f69d05053d49a6beb2de6fdeebe9a7f3af7f7da26cebe09f977397e3e7f141adce76bfa542fd2e9ebdbf79fe75feafcfe7fdea7a74ee6fdff66fece55c5dafc7d903cf2ee75faa9eb7b1e7ed76b3fbec6ef82d577bbba,0x3d77589cee9ad706fabb6ffe9abbefefff7717aeeef925fd31767ad7efec7af4f37eaeff6f3f0d5acc443f874ffdf722b3dcf9ffdfdbbebfbbbdba7ff8e84394eb7bdbfeffdbfacee3feed6bc87cfc9dfec3f775f7e282d7750e6bd0f17dc7b3,0x59cefbfc69cdee4f974ff637721deef6eb69fffa7f7d2c4955edf9d7b3f7df3d7b9edebaaaff6efffafdff7dbaf99f051b7efbf5f63e62db3eb3fceffb7769bffedeeffdfe3dff7ebdffeefc5e77bff9fb77f6c6a31bbe47ff8d4,0x3fdceefeff9d5893d5d27afdebfd999eaeb6bfc1b7ce79e591fafd9dddebfb7fffff7ff7e3fdb77fcefb6f4febc7fdbc1fdefade077ba5edf965e3e6fa1fbefedf3fffe467bff1bdb45d3bfc5bfccf91adff9f56799e87f7f52e7f2,0x9ffd1966ffff7f9f7c5d8c147abbd8b7647a3fbddc1afebcbdbcebdbbcaedb87ef6efe3b53381f61708bd5776e4ff7e5bb97f2dfba52f1e47e9d0f9ad57bedfb9236b6d4bf7d5ffcfeff7f536caed7dfd6e7bf61ad6ffb8fedda72abbdd7f7be63,0x3bda8e6937fbdff77fd3f9af6fffd74ead7fafd26a79ff77bbfd275fcabf4b85f1c3594adeb7d3fcde173777aefbdb6e4c73ea7ff09ad1dd13fb7b04efef63f4de363d86e976f464ff98caffd1c5b7ba3cabeecee9bd07fff3dcf62ec97defdfff,0x2dcfdefdffef5dedfba375ad4ebf9ed8ee51d70574d5b5f79ee9e5ff8de9feabbf56fb7fe65f6ff3de9fdfbcdcf554e4baf7bf6f0f2da8a71aa7fcfb8dbeffffd7d6530783f5ff27cfa2f6f607ff8f6d87666b8aeebdf8f357737f7ef5ffd9,0x36ab79eb5d7ff30cd9fc2fc3fffeee67be5e6ae67fbbd7fb8eff525cf7abff7bbb1ec52fa5195ffbd6e889bdf7fd7d9f74aef3fc1e2bcefe35f5e17efdfe64c5c7bf70b57ebed7fdc7937466fcead9ffde4e8fd7d7d6db9697efbdd7eb5dfe,0xf5fdbf5c7b7f9e5ef6fbb257f19c49cedf74e679ff9ff3b5dba8cf2f79e2f9af52ef6baeffbfebfedfbd6fe7dea1beb9f8778df6bffc7c7a979f19abff5ced1e7fdeffee7ffde71bd3ffbdfe7c645e7f77b6d5f6077bf1ee9fedca3f,0x1f3dbeb3e57deaf98dea7669de99cbddcdbaefbd76ff576e979c4ffa9ffe5f55fc26bcd46826ddef0abf9cfbf1ca77d3fe7fa86ffb6eb4aae4e18dbf45f8fe7789ef778f7d7f94d4ccebb1973c32bf4fc787e76f2e05fcbafe37dfbf3bf21c6f76ffcf,0x7f47bd5b7f4f5da278de48332efdbc6fdf7efefb2faaed6ada67bfadbfddb8ac7ff52af47efc7ad7f9fbde7f6161fbc4d7d9ed267fd57665bdfbdebeb296dc5baeddd8b7ffc3cdb2ad7dac0a4f8ef3dfe1fb6ff75f49cde7fdf11d7f3fa67889ff,0x399fe71e6eccbd41a0d30d7ff7fea1d6b9d3a7dfd276f7e7f5eebbf51e3dbfb9aef9fcb22b7b77ffbff7a8b699b3eb74e6ae76f7fcedafd6d4ed8f4b74fd3ee6e6fd79773bbb0e379a77e9b642cfbebe7d93fcfb16f37b7ddaeb55fb3dfbb7dfb,0x3fb97af2d2518feba980fb1f155cf94f9741336f1be7277b8ddf56e8c6ef7feee95ef14357af7acff7b8dd9dd4ffaee7d79f4f1bcfde69bcfad7af37f8afca35aefd572fb7f6b91debfb5c7ffb5d1bbfeb1f73f68d7fe707d97b7de5de1be7b17cff5] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n17 : packedGroups 16 16 71552 [0xfff797bfe5bed549adedee53ef7efadb43beb77f776c5deebefefe56ff5d616c4bd08f6eb777ea5957d9a70e95ff7cd13d49f123fb55bd9ed9d1aab2f937f47bfbd70afafd77dede53fcffbf37c3174877eb5dceb7af869cfff7dc3769e66ae778f,0x1bcaffe2bf7ffbf4ffbb677ff9197fbc5d7c4fadebe7fb5fbfcfed4a8abbf733c79877ffbafdfacfdebee0cbcc015f7efef7e19eb7fc7ec4cfff77373f33cebfdfc70b3ab2e67c3f5bf9ff1fe695ff2ef7f7ec5b7fdfbff3aef75ee8c,0x33b5bf7f2874ff475ee6aed6733170fefffef33bebd7ffbf3bfcdc7cbedfeb9dea7feddb0fffd9ed5fa4e6b64cdf7b5f5ed1e936fedeeeeef2ecadaaf165d1bb3f6bf61ab53f4ead4d8ffd743b38cef35bad7edeef97cfbbed76570eeb5fac7e,0x79f2fcbffe7bc89f5d8f759fae393ffe8f23e2fb5dbffaebfbd6ffdfde3dffbb7d7d8255733fb3ebbf9bf26f47ebf6399ecfcf243ebdbf316cc739cea5dfbe676ffe9ff4bfedf5b8f52d7bbd77f7369ffadffd39be5df4dffed94ffd841,0xfd7c73dbf8cf4ff7f5e7de3f77b76dbf48bffdfeb775d7bfffdcfd3e3bd4dfa7df7765b4a5a0fd69ef799fefff79777a4af6cbfadec514dbacf7baef7ee74dffffc6b7fffaf72ed5ddebedd63d7ff55ff55f5ffaf7ffb7576cd2,0x29b37f5d3abfb7faa35cf7cddf5fd7fc6e8c3946984f7657abd1fcffd9cbadfad8f9a694edde9dbddae2faee77a7e32de5ff6f3fbcfbaff9c3d3f3d5d73dbc6eda16f77677ebb9bd9e8bd0b0cd431ffef6bf7f0eefa9fb79f5dbfd9bcfe3fda3ee,0xddbec6fc24c296d7e9ff1a4e7bc8bc80cbe5fce8feafee39dfbfdf896d4dfead6733fe66cff34d65a659d9986b9efb9c85cca2e6cf7afc676f561f995cd7ba9d6d6fcc6f0c38bbb3b3ff49fd24def5e36efcdc5bdc58eaef98fefefb757f7f71cafffbcd5f3,0x3ec59fba76a776807dd7761bfe9895335f67f39ee1cfcfdacd8e2fbdd77e79bef09bbdfe6fbf2bfa76b6df3bdbe6efc665f8ef8a3b7ef77e3138f777fd376fbdfbbdb4f5de429fdb54fee777bfdb917f7fa79c97aeb69ddf97dfbde17d7e3f839,0x3f6cf0affafefff3befdbd3f9c59aef915fdebdd9df373070f6e9fdbecddd6e7aefbe0ecd4b6de17decf1b2ce5a693f0d5c7b16abb5bf3fffe9683f8eef2b3dc331dcbcff7f5f5eb1bea97dbbcb5f6b75df4ff7cedbd75ffef9cafefd6b4decf,0xbff8ff7e328fd7ddffeaafffa4f1fac771d26fb5ade7f9fff3bb9ad771f3f85ade93dea3df9eeef77efa7be27fd5ed737cfa3bfedf35f0e5ef8df0c5b69df0fbef7b9a7efcf77ee99f15ff536f2fd97fa7fd5b39e37365ddd67ea54dc77e0,0x7b5967cf7c3f2f9a7dffeffe5fb3baf9bd4e76957577bcdfa16667d9f9babf868ffe605b1e8cf1fa52ac78574f7b3cdfd7ffdf376b7221f485e78b72ab08f1d7dfbd2bd2fbef1f3cf6ffdc67fc7cbefbd3fcdafece5b7b7f3a0f5dbf7addf53d1a3bc,0x2fb9baf8fa5d876ab618d4fbb7fe668ffd5f294fc53f9c3957f8a6ab9b9ee377fffaeda2ffeddf675dfe59cf3fbfd74bd7ef6f7755f7cb8fd9bfdd7247cfa79ceffababee77fd73eee61fa43e5fa77e9df71efb3fed6feafbd3a5c37badcdea,0x1f34aedf9bf6dddbcff6fff6ce662fe4ed7f7b2fbff279cdf5bf2aadbbf5efdee75e75757d3de05ecf4676c59ff7fc67c973e5efbf5a7fff7ce5b9bfa7bdbe1791c73ea70ae477b7778fff7afd92187d6b7c4eef7b09fef9aadfe4c5eeb13cafa,0x263d969bd812ee9f1cffae71afdca0eeb2ffc3fe51def3df9b745f10fba752ceb6bfd6b77ddf3dfdeb4f1f7f474dffb9aaa977bf9e2f3f4b9f573bb7fcdf3a147bf33d6e8def9cacb7beffe04649ff365fe7eff9f7e70f66f7fbfe3ff5d6fbc7f2,0x234f64d96c6d46ff76f49ebbb89cfd7cebc82b8b771f5f7dcceb58fc56f9b68f72af3c69dc7aedeff1bbabcfd627e8e7fcd99f3739fe94fb7f9f8e6e837cff6aee97f79aeed495c6aa8cdfb37ff9f4f537bfc7d7aa6cfe9fef777c6dcb7dbbae1dcbdea,0xd1676dd52a1df6be4af74769df5f0d7f7dffbc78f6d56bdcfb7f065bdbfdbf3047f5fa5bbfffdbfd6195f3bffee3f767b75f1221cfbffc5777b5fe777333f5abf969b3fcd365d9da7f5d67674c3dedafa9b1b99f95677fefbdf9defbfbbed6c] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n18 : packedGroups 16 16 75648 [0x1d38bf5ddb177fb106a8ddaf79df1df5de52a163dffdfeacd52041d9fe279ffd7adc38fecb1f73d7779f4dfde4e9e0d3df2aff97fbc95f5fff9674a9d1277cb13fbd59afece74fedfcfebf6a2baff1e43f2bdf5cff97cbdeb7e77fff84d6d6f17adbcc,0x2df7f3ca9f6fe1bdc9366bfeceecb79531efdf7a35f6dc5bbbf7bff74cf3d3697df44ec4fbebbffa767e9f039d21bdaff57c16bc69f7b74e670cbf97b7bbaf3c7ad8bdb6cc6a6fbefa7fbdbff4efecfef3febfd99df6f927ce535ab7a20fc73fbd,0x2bb8cd60fb3557faaccdfc0fdfed7d743f7fefd3bfeff8141df9ed96c9ecbeb7f3afb7febce48fdfebbedf9af754657f79c3cb8dedfe6c47736ebc7cfee7fff2dcdd75ffad3ed5f49d7532d7f1fcf9bcf79b90bacf579bff7ff4fa97b7705be7,0x59f5d5673d57e7bffd8f777cbfce77fffdfdeaf307d453755f3dd7a77d1c6fa775defbff9492f2f7ddbd59aa109dfdc48b6d5f2ffaffdfeee7feeb89fcd1feafeff6dfbefdffad9aff2b3fffe7a91e7febfbe3def8af6a372e3ddecfb,0x7f173feff35fd5fc228f9ff3ff6fdfd35cbd7f83ef7277b6ff1f970c589e7fd7fbf47f443eeefbb3bf7cae7ffef78bd75ea55ea670f9aebce92fdebfdb7ff1bfdca16f2f0efff7aabce7f2ffdbfe7ffca6f77ed01dd4d6dce4f6fd8979de,0x9fffbbbe455f57b79ffbaed51bdf9bfdbef35ffbedd58aeaffb9be30bbf35cbf1db657dcd8e6ff6dfc9f7baff0d2fc535c677ffcf7fec9f6fde73baafcbbfbff62f25be499858bfbcb9cefaaffd466e6fd12d77abf7feff2e21f3ad2fd929b,0x3f82cd75cf38df23898e7d6bfbd2ebaf547f5cdb0bffed6eaf7e6b7b7fafba2bc6b24c347fde8ff7fdafb12f7ffff759efabba69d47ff49a9f7f8dc7bed5b4bffc1f6e8efdaf9e581dded2deef6f79d52f99d9bebd87bac477afe2c1843c6fdf6b577c,0x17f0bfbd0f1dffeebbe5bff13ae2dd1aeeaafaadf986ab1fbfddfdffbfffbef6efbef84f37e49feaf75b7776bf34aa7e92dff3ff7bdbffed3b5cb0cd6fef1f1b9ffefffe8df2366a8fdf5f24ecf34dcefc5f66afffdacbdce3f2b433fef,0x1ff5edf33b5bfc96629279a6bdbc7faffa59fa3e7ceb76c75c0fb7acf6be675af9e5fe7fcfeb70bedefe2de71eb96dbf577dcb2f77f7ed9f2f39c9b7ded3edf9e563fe3eda739615feec6f7d6d19bfecacfdf7fdf79ff77cbaa37e6f9dadcfa,0x4c7b3eb7ffb3e9edd1f7ffb7ef3dfbe52f79cd83c7c3d7857d73da8bef50dcf5c96ffe113dfbd79fc57f5ba4aae3afe79b9977f3f532ffbaf6debf64eaaffbbfaffebdd4052be64bfdbf75ffaddbc7775927dcf6adeb343bd9074e49ef3fe8ffbc,0x35b79edce3f2bfd3fd72065e7cddab7282faace4fdf79f73509ff7e9b9745bef3fe2f5dc587e9f33ed757fe247f5fcd7bde5b7bf6bde2ab53feebbad25af5f8f5f2cfae771de3ebd6bee99ff77bef7fe95f76fdcbf867f2b7fdeff7b7905ecf7,0x76cf5566c535ff7f4fed75bbfe4bfe7f43bee5effcdfbdfe3cd3f4d585b3b45ffd8dc3ff0f3a4b77bf753e156f85ffde5d4c577cc63ccfeff6c6f3fff3dfb7fff328b3bc79a7b766bffcfe993facdcbbbffb03bbefbef5b5def71c37d2bff,0x14d3679ef3c8fd1236fffbfb57c4ff7ff5f479fb2de073ef79f946f7a31f1ff6fff9f5cd3b177f5c52adee752fedff6b11fed67beeb55193e43834b23df74abafc37afe7ffdbf9bdfa9e8f026ff6159b976bf1e1aa7f4752e55f0a55c6f8f36effcd82a323d,0x17eaf3e5a7d7b84fdeaffecfa45b7aa7fb1873eb5aa6d87adccff2eaadd7bd3f78ee3e7b1e2ebfb36b7fd8f1f7e5f7bfa7eeeeadd9f6de5d5e5ae8f9d2ef3dfc1c59d94e9a61fad77fbc6de67f3fcb3ff6fd41d9acf87cdba6feb3b3f27edff8c1f15,0x3fbb8dfff8f3ead7ebafef7f1ef1ece168fadfcd6fef3dff4e5eef5a965fac91ed7bdfff6effea7f9f1beb50ff6fbfbcedbcedd4b76c6fd5ef79f77dff87ebdd63bf91dfb9cc9fd75e6a746eddbd73fc6bca3673e13ff9cf6eff8bbe5e,0x3eeece29ddd5fc7af5fb6fccfd4ff7f63697eb477c33fdfe6bfc9f316a75cb738e96ff7b5ef331bb46aa7bbefc713bf3dffcfecd8976f6bb9efdd17fc5392cf8c6f8f7bdb17b7ffd23eabbff9af623bddfeec7eef4df5df0feefb7d1d0f45fcf] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n19 : packedGroups 16 16 79744 [0x1f9ffbf7e6fda17a7f45ad3e65f6ee77a8ded273ffeb9e727586c676f47237bc83f6d887ed46e8eaf94ccf73d7ad2fc57bfcfeb7bfaed7dfdf2ef7accf77175fc78bbf5eced2f6c38f2b67aeecf67bfcbbf5fbffffb2bc6ab9d7b7fbfdfdf6dc,0xbde68deeaace95f37b9edb9eff0be3af377bae7ff5ad7f7d45d7e55fb333578bdace7af93d15f37b966b35dd4b1ee375f5ff89f7abe7bf2d8cc7aecbffbdfbf8c7efe0aef3447be01e79a41a5da53dddff6def7b79f6cfb5dd2b3bc9cfdcf555fb25e6,0x1de4ee07affe7edfaf1fb67d6af31bcfde677b3df1f5f6978eadfdb7ff3b7deb7533d9d7a9fcb57bf9d579c9ddbcfefe1d7df6bafdd77fdaee778df6d8c4df5bb767fffb3f5aeb5fe19f785affdbf65f3fadff7b6b32672de3ee257375e9,0x1ba9def75fe7ebdeb76b6dfede6ffcce3dc1bffab3f7c5f65d768ee3f1fdefcff5bfbbdb3fcd74ff779e67fe7ab63fdb5fdf9f3fe5f7f9f34e05bd1a7e11ccfffbf71f75e37cdbffadbffb4337792296f47f2be7efeba73d9dd6f98f992,0x2777aff4bd3f3e76c8edcf8b4de954c74e7affec7ff7ddefbdadf49ffe79b18db6dea20bebeef52ffeffee5bd3cbfff32fd9cfff5d6387f7476be5bdefdff8fcb0f279ddfce0f71f1d3f97fc7feefa9af9d693fc71777e7dfd5c7957fe75e,0xac14d37f1b7fd9bdaeeae237b7fffd3bfbffd7571c6a3fffb0b766de4ddfdb4f3f7714bfcbe7de77b737025fe7599de7132df1bc6d5aaf598bf139ffa167d2ecb27e7d7bb5938ece8af5b77e00000001feaf6fff5bf335ff4c37fb55efcafcfe7b8db3ddb5a,0x71cef7ffabd66dfefff0b595fdb549edfce1693e7ff77c72cc5418fd78367ee179e5de5f9ff3f5fffef2f9b87855ab69ffa7ece8fc7cccdf6743fc77fbfdf65eb2d6bce3fb7a6f57e4f779cdf7f5ff1f5dcfed78c99bbffd6abc6ebe3dff3f,0x3db3e6775f8af7d1affebf2efdfaff29e5cede95ff95af533cc9e48fbd9df6cad74fd8666c3b78abdf7ffffcf50eff9f77fffab965436b3fff97fc97f13f6cfbfdc6d5fc1f41fcddbfaebd2728e7d79965f7b65da656ce325db4af9b3c817ebdf7e,0xef9e031d5f61bd73dabdf6eacd8fd64a57eb7fcddafb583fdf6f9effe6836de771d3009ff0fa9f5ff6cfcfdfa52ffba5379d6edf1efaf2fdeed7fed7b37f7fbfe30995abfbcfbbc7f5e5cbefb35cb09de9f4bef2e3d9aab5ebbd6737bbfddfe0d,0x4e27719e598fb46cbae57aa1d8fb4c333ef3d9bd53b2fffff5f157af3edcee6e65f1fcb3dcfdd4da9dd5fc3fedfdfe5c99fefffcbb7f99dfcadde7ffff753dd275dbadabd6dd57dfe5eef8a7fe6962a2f3df1fff9faef795766dfd2efb7cd79,0x5f23fe3a72875a94dd7b3affff78cb84bdfd6ffe61f35ddfbfe5e5fafebec993dcaedb66fedffffb9fbae4f07f5f9fdbff5b6eddc9ffdde307ffcf800f48b57e2ad9f5b1e7f7fb25f7e9746bb2fcbcb34fcc9df7ae9ef5bfb6db2cab95eff8cd6,0x1ce95ff1cffefccf3ec4b67badd595d589ea6afecff7b8054f7fb5b96b3e5b0737a8ff9fbffda6ae97fd7269dfdd7979b76bdee35653f7dcdffeeec3ffb3f903fbf7792c97dfbd3ffb7b92c5eb27fb8f9cfb7ee7d0ff444d67eb90aba75a1abf97ba3,0x136ccf8f6b3e6f35aad2fa6e3f7dfb5f63a5717ecfb9bdca7fd2f0f6d6fdefbfbebdf98aefe965055eb3ec5d46fd9d7fefeea7d97495dba7fab22e74afdc7ded3f98fff5fea7b7eeb666fdf69779f3ff8fd5723cce9cfa62d7fdbfff777fdbd1,0x3df8b79c728fcdec1bd7ffed1a67113fdf3cf5feda957e15e98bfbbab68ec32dda0c6bc07f3a7cbdb3fe7fde4fff77fdeefbf9ffeeface9a33e9f7ff2fc268efefa5fb3d2feffe0f3dcce7475fee7b94261b77a1c86c7e7c5be9bc9fb25efb5cb55737,0xd83fdebfef1dfeedcf9fd887d3755fdbf2c3ef7be2f49e9df5abb8f2bdb7c8599777f3ff7e06bd6b5ecd60a997dc6efea6fe66aef3b59af5cff997be5f4bf0ed73ffefb2fdbb5df5b32f3fc3b9dd8cfcd07d6b337cf5f4c92ddffb7ae1ce476cea9328,0x1fcf7cf9eb0064000000033b327e2c9f7f3b1f265b3e7fe2fb5fbd4d5addfd76775e8fad9dbfce1db768bfe297ff5fddfee6e65ef79eef956ff7fb5afff8cb8e73cde3ef7b3ebafc17fbfe1e7eb88efc75f7afddee18972fd5acdbb5c182eed23f7ddbfbb03] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n20 : packedGroups 16 16 83840 [0x3dfe3bd4523ae9d224f1dfdc7ec7fefbb62bebcf9f7fed3e56cdfdf521e4f83c579fb1cdba3fe71add7efafcaca73ee7ff5377fd5ad1d9fb2daed4f3b438ac1fdff3678ef752e7edb75e3ca7ef5ef6778def32933bfa3dafbf6f79f8774babe93cfdd,0xecebb3b7ee9bbfa0287b7c18c7da5dbaeeefa5565979fe3def94f9ed39c9efb733f19bee77bf873ddd487a47035255fbfbd8e2ffffa1cee347ab79d66e5f70bf7b241341d3c6d9a8b73bfe8f7bdffae7e1bbbe445feeafd93c6a6fbb1eaa5daf76ffb7a6335f,0x1f4edcdefdbe7feeb9ffa7dbcdeb0e69ededfa9ea97a1a61953b7c77e7b9e96ff4d7eb24bfffaab79d9ef593529da7b69d3d5cefdda64699dcfe862f48cdf7bd549de6ad5bc1bcfa0bdb5cb72ccba1b5add37ca1f3e54a97d1c5ff793ab5b7ffbf45489b5edfa,0x66cfc1f9bfb3f6512c8bd636bdfead2ceda3ddeee7e2b5f0ad66577faebbbe7e9f7fd96cbfb7d35efafe9d1d76d417c3f5ee25f8f79efeb3b7ff65dcf9dfa0ccbe4f78f75e7fe762ed60ebeff7bffc84f78b3abd9b3235c927ee5aeacb06ad3bf7146f7b,0x8853dc37bcec2d63d7dee7d464ffef7818b58c6d51ca747dda2aa9f33edf7b7e5566fbf1fb3bcdcdfa12ffa0fabcccb97a7daefdaf3bea7e4acd2e7ef3e2b7c2e6dc89029a9ffe71bdefcb7a7e3755f9b771e3fffaf996cdf2adeadb357f23b96ce57bd2ffb5b,0x51fdfd6758ceb8fe6e38ef74fffcbac4bb24f7d4cfeb59d5ff8eee7e4937fd31e67f7f0cb9dcffffdcf7f7d35cf53a5dedd3a413ecde9bffc7cd99a77ebbf32cff9f3ff9de317c3c7f87f29bc213f9db5ffbe7f3f093a5a0b3bf5bf0ffbd409eba76aa,0x1cbdffbcab7d31f6a7fde7ff373bfcafe6dcbfc7ce36fbbeddeff7604cab3ffe7deb5e17ea1fb7bf9df3e68eddde88db480fcfcf7bbfa6fbfef776b7679dcf9fdaf7dfbd39df75ef91e7ebf20eadf9cbf958a7fcffabf7df3cadad6ea8bb0,0x1e5f07936c694ce7b13de9939c5b49ecb6fba6577b3dbbff667efafeaf7b6ddf33abf0c33e958bc03e2dfbf7edf1be5719bfde7e5d4edb67dff9fffede4a2fa6c7e7b0d3b516ef47363fffadff9aaf69fbbb56ddae4eec568d67e78beb5c4bdd2197f8bf26,0xf2df1e475f34a4fff35eb9ffe3f7fffebffe2b93c6e0876fa779fdcffd78ff0b7caa55ff7ebf8fb9cc7fb7f1768afcfb8dfdb287c5f6bd1de96efdfebab96224dbdfafefcef7bdaf52cfdd3b69b9fbf6b3e69bd9e9fcffb334ddc57b0aad3bae,0x15bdd04e53edcbf9e85f9bdf5c4e57bb5f735eb177d8d6f7f8e63d7debfee6a586e7abfc77def1e8ffd3c57cb6b57fed8e9f3de1beb247a5f8ff57f2ebe3f6f3e0bf1cdabdea8ea6e36bded9af7f3cb739fd0cd2ffefe6cbbe896f7bdefedeb9e7a3a,0x67e603639ff667cb9cebebbf7bd762e7978fb3d177e967e117ac7ea7efdd477b7f31693ebffd8aeff85fff77cceeb71f66cebf52e3feefe95ad0fabb3fded3e8e6fd5f7affd96da3cbb3051fbf557aff7672bf08553f92f39772daf7fae75e7bfa2f,0x1fed9db8d2eb8bab8aecdd2a7b28deedb7cbf7c283ffe7d7d227ff2e029db76762caf87f1f15e8f2fc6affe70c676bfdb7fe9f76f5f76d735a5e6b751cb2577cb2678d9e0fffbfa76a4db7abd0cfbbf571f6619d18fff0ee3f38abfbf73eb6f7e396f5f7de,0xf7bf77afcfcb13bdea322fb1bf5f61afff26afff75bf7e35dbef1787dd39906bf351a1109eb4adbed77ddfbcb7e52e46e9eb6e847bfef0eb7fed4f679ff6da7e7ebc33eb5d1f3f3f4cf5788f65ec73ffd33cffe5dfbda2b7f8b37bfefdcf31ed93f,0x3cffefb8d7ffeed2bf38f64497d11daf847901fe0ff4ececf23b7e6ebda1ebdcab6fffdd15ff9bfd7f6766f6df793ff4e7d8b37ce9edaf97efedbff1f677f76df383eee9f4c4b97dfa7e754c8b6f569599b3ae72ee6df1fefdb57d567f7ef997d5,0x1b19df9df42ffb7bef477b97efceffff7e0debf7ef59b4386de24be4f2ebee364ed7ba69b6bc5caecb6ff64915c82d63fdf5bb2787b5cb5a75cea55bdee7f6929bfb9bbfdbfd8dfdf897ff2fd5ff8d0df5f77c178ffd3dbfbccb79fff1bd9c7f7f,0x787dbb1aabcb1dded7bff9dff963cc9bfffe5b3e5e2e7e348aaf37cd37ffdfbafcb869c3bc7e9eefba9e77cd7e45ccfca271ffb3e7b7cfe7f6d47fb3aa3be623b329aeefccfd38faf3efdde5d09375382e5cc7ff2bdf7ebb69bfd0eb9b69533af5864c2f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n21 : packedGroups 16 16 87936 [0x1f2ce3f7f7d64e5a1fddefdbde85de8a989f2d13bfbdd9eda0f4d69f9d7fae7d57efde5d52adbefc95ba8ffd7ffe3bc4f7f7fc1cfdb3596bd21553dfb74aee8fc52592cfe3c515ccbf6fe1df8afc3557ea67ff8f8fef8badefff787ccd98f3d66daa277f,0x1bc7f516875b7cbf9efe9fe91efe3f5fafdde5bd1dbcab8f55f90a359ffe51ded9fc34a3eee376932f9fffac757eb5f161bde0baee1ef7e1d37477ba6df1f9f3fcefd5ff2d7a38faefeef7fd5f983afdffa6dfbdffdfdb7ff9c573d2dace453e71,0x5fde59b736de1ad5f7fc7fa5fa7bb8bdbeab3ef1949bbdebff915dc2695ebb72fbbaeea2434bd7d2516e70325c7ed174baef9cfb97a6e37b1536d6f37ef9696aaadf7bbc56fb7f1b7edfabc95f3fcde839ededd753d7fa90f7aee89fbb6b7dec7e47dfff,0x14b9bbb75df6d35933bdd2e8ecf3972cddf716d4a096e98af7affbeeded7eefd6e9decd30fbedcac837957fda7dbeafdbba5f3d16febf39cd7af3331bf9b655783207f979fb5aeea30e782d9dde7fb7dd8d787c19119fde75d8331fee7f9d7d77efeaa79ee059,0x2f1bdb41cb1af9dc7f79400000003bf745e7796b7c4a57eebf9eff34f63a879a26517df94cf1d7ff1ed8feff6fffb367bf2f2e7b7bebfc743863b4957b73ff9c59ffeee7b6d5ecbdb3cafacfe1fb43d8b8f573fee78febfaabdabfbb7ffcd7ff4d1f97a2db14,0xef137c525de37b97dff57dec77889e97adcdd3efff677958ff276e61b97e69f4d7eda34fc5b95e10eb3bcfee40bf14ff5c26a7e7b65b7d8df65f9fb0fddf9f783e9f573fbd9cfafcef693773eb65e2e9dd2a2b735b9e2f9b1ff7f8dd1fe337ef92767dd4e,0x765aa69b3c37fbff7ff7fe77fb99ffd7663badceba93fabd7f7fddcb3aeafbfcbe9a93b92f77627bdafbf3fe3dd36579d5ff133e7edd6f7dff371bf76fd6f3e7f9bed3e5f582c7ff3ffaffd5e7bd77e31b72def4eb547febab7de85a3d,0x39bd55fdc99deeedfafe3ed1d785d68eff7be39bdf264ad69ec5767fafefddffcefdd5cdf8f07fb66b57ba5fd1fff207699d5b94a274f1ff673b37bffddff3bfe660a7bf3bafd733bb1fb57d5bbcaf65fffacb75ffb1c2c6e74adbbbb6f6c28dbd,0x1aa37dadfbdfafb5f17ddbbf3fdb4fdfbf1951ffe2dbb63291dfbf9fcc6ebf13cffd5c1697ec6f9bff3ed3f9abf7dcdb55c8f18bd97be22379c3adffcb6e433cb53697659f8cbed707ecf1dedf76bbe966dc0ffe86fbfdd3673e3da54c3e9bb77ddeb29,0x33e9ff582e33fecedf1a15da7ff666733ab6bbbff376c7cddec73aafeffd7baefdc6777ef9e5fb1f5839b3584dcfc45cc9f3ee3feeb6e21d67cd737c4864fcd0abfcbff72e7c99263424dfb3bddc5bfe6da6a76beba7cbd78791be17633df1dd62e5cbb6f3fe,0x7bad7a767ef9afb6ff4f67efef5a71f3aa7dffbe7ebb06f6ef73b7f37d31776ef773b9ba6db2dfef9e6b779f3afc7794ead9db67f3e73fbddfeb4b17c4a99ae96bb67ef1f785ef2fae373ee6e7fed8c0f2f347fcedf7bda6bc64f99eea5f500ff,0x37e77cb7c3fd6bec13bb2ac31b7d7bf9f9ecf38f4bfebf77c9bb8fcaf414df79928bba6b6ffebfbc678d967c5f9ec3f3edff2dfcbd3ab7dabce5877e9be96f5bdf89b63fdfb5fedeb9fcbc3997feaab93b64fa5db7ef0ade771e5615abb51952fd6a5ef,0x48ad477ff59e563d48f2ae7d6e0ba33e7ece5be672dfc653ef747ae6dbf6fd7f9c0f576bfef3f7afc56cdffde3772f15f8f2ef5fe1fffb6ea7b157dfbbbf605f7e65bbcd5f6ba7edfdfef9ffbefe6c5f7f3b3a8f6bf5bf79c77edfaf5fb9073,0xfd736fb5de3c126c35bb5d7f7e8b7542d6e796eae6987b1db3d6ec72d1da5a1659de7fcfebb79e75afc776abada86c35f59dd4dffafb2a5d35917fbfedb76aff7de5f56c37bb1ef26ed2dce4fd5cdfbfff9ddb9bfe8d950e8fd7f96e2fe6db5ef7bcdf7,0x577f9f7e5a67b99c8c5b557cd7c6f5b6b6ff9e6e9659efae3463ef5cbdccb93b1502ddfaefe49edbdcd5a7e577ffb3fbfbc9fd5fffbdfedff341bbccefaf5f7f9331ff9ba1ee9ce8fb9414df723fde72ff5dedeeeaeef02177792cff52c5b3e8f58d5b0,0x7b7f7f5f2cfc951b96e7f97f1fefe97f372a7badf32bf5ef7b677c84a7acd6db97917fef6667d5a7eb3af6feaa95ff08f3ee9feafff3a3feefa4795b9e9deae52b3dfa827df856bb706ebfcf7d7d996db6a9d9f9bde7d841b3feff1a7f70d5fe75b6] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n22 : packedGroups 16 16 92032 [0x1bfd138faf6e15d1bbf0050fb38d673b6e9769ff13b73bd976a45beef7dad2c8e4fd869a4e8fb7965f9cca5e7fbdfdd7ed2fcbd51b82b5d33ebef39f7b5f3d3627f3ccfeff17fffa5391ff9faf5da5b1c3a3ff715df359e17fb346df626cbdb57fb7fcdac731,0x2e84b7eb877e9b83baf98ef27f07fafcac3dad865791ebeeb3fa7ffe3bd3bfa3f7f03b9277def6fbe1f41f79bff0fe8b7d931bffadeac273f6e746eff7ffe47b0b7cb5af20fbf17fe8678c6fbffb614f9cb9a066df70b99ecb57d3fdb2cb7feedb7d316f,0x6f27fc7ea8e7674ddbc800000006b5bdb817bb7b8ed7e5d7e82b47b2f75ff73db3a627ff8763ae6713b3bb57e4fce76ff191feab419ef710efd4e63abfebfdff6e76befeffaffbe307c397eefdc5edf3f6758e9faeb3915899df733f4cf6f70ffff7d2dfd3af,0xf9dfbe1bdbade777febe6e7d4ccf9d9debdb5fed4aadccfeb12dffba2a6bdb7baefbfb9e95a9bff99121aff55a00b4074e83efd3cb87e7dfacfeeac8d7f79aa97fabc6ee614e1df27cd47df7ae67dd9f2edbc9f277d7bbecce2fe7dafe5b49f6e9fbbf,0x4a92df7b9b8407eaeb36357b7df64dcb9a3e6ccf67f2f87d9e930deca16f4efe2cf5c7bbdf1fefff6bff98fbcd77fefff7777e71efd7cd676da5fff7b97f6e6313e9fffecbc75feebeffb79cc1ab3b452feb791b4b57ae78de6c3d3bceedf6e7fe,0x1fff7ada6727ddcff72c73a5dc11f7a6ff8f7f9dff5764ffbb27b7c31f94f55644dbffe0375cbb76ebae17c7b5aecfbf6f7ff4fea8c775797db9764b61532339fdffdaac751af7bffef73ee550acacfff7ceedeeffbf6c4f325e57a46f8aef7f70fd,0xf1bb8777a3f722f67f35f7f1efbfeb98b6debffbd5f92a21ff32efe3a7fbf316ae93274aed8371bffdbdf9fb1eb39dfbabddcbdba4bf3ea7f2ffaab97f97fdb793ea9dc63c17ffdede7afeeabadd9fd1dc6fef8bf5196b7f54e7e37f6743ad7f8,0x31797f31bdbf5fbe6fd9d2e2b6bcff9becd1d72771ebac7cb322dcdf74bfefbffde87728fdfd7a8f1fefd6f1cab7be730c7796b368f638bfdf6b3392dcd87ef83dbef3f599ef42bcc7f9f1d2feffc5e1c13c7b77fd7cfa74bd92dbee38abcffadef9db,0x17f7fedd7bce5adfb9f70f3fdbb6a3e29bdf5cc74f2fffe336cdfe2fcffedeec3dd37debfabf9e229d3df0c42eedabac9fae4fed3943edae872fbfefb3fa15e0f43cdfbee39dabf79fd6cd7f8d5546fe3dfcf0f979ff9f3cf1bdbd93fbdfcdedb,0x3de8ed366d5b9bdcfadeebf1b1ff5f5b9e25d341b1d7a7e9ef8f68c1f729ab7adfb7abffcf2ef2db64d7c4d3f1ff7ff4ef12fc5257bdacb9eabfdf3fe7ce47d39f1b47c6e62b1bf2e2ede377a6ebe371f139e4ff9d67ff58fff7ccaf67fffa6febf1b,0x4ef461a9d7fe9cfed3b3fc37fcd093cf3bff9ce0933d9b9c9df1dffdfb6efc5d7fffeb8daa6ecdeb5f3f7ade7da3e4bb717fef5f97d714f592ae69beff57b5b6c7fcedf3c65a3b59cef2d9556f69cb6fffba31bef9d97adbd5f7d56a4afa8ecabbeb4,0x55f657e779a64f774cba7e2e37f327d7fc7fffdfdc45118bab1355fbf5b7d60ff93cff75fa773d37ae779585adfd45bf3fcf8b29cfcff1ca73d9f7df0fcb2354d66f6f755736ff69e59ef6eb3774b736769d1bff3c4b6a6d437fc1fda6959fde36e15ff4f,0x39db372bfbbfd7926ffb2c7df5b129367b7963f8d11b5bb4d5ffbbf9dabe99e9cf7d97f2f46dc5af57f44c7e7f73af7c9a95dd67d7bbf510ecf8ffd49a97d85ff7847e0b54bddf8feafff56b834466963fd9749911ceffb87bff8f2e7affbf3dffeb6e5812,0xed05eec52ee64e7e0c75db3db7a04acd92e4ffbfbfef7c73abdf4d657bad2b79f7547e5afd8b7ea67dfa958c8ff1b4215221b25ff7f275fc9863dcf6cbd77db25dcd93ada7b9efdffe7f69baefafffef57b8dbbdcdcfffb7bbca60ef37c97b3fffcc3e75,0xedb3addb6bfc9fdfe7fd7ab6fffb85ccaf7fafcfab35d53b7dafc7c2fb2fcff9d8c3bed58fc2fbb23c991d213fc8f6b3f7cfa89abff7575efafeeb6e47f88abfbe6ef2fffef169dc27bbcd4d7d9f89bef95bed8dc95f7ffead3f7f6ed1ef717c8,0xd917d1b7fe1ed6071dffbbeb6a7af27fe7a5feed57ff2bef7cf7bee5eb6f87bbc0cf7d77fe7cdefd7f8aa65fed3cc32209ce3b5ef1c4ffaf1ff1dfe4333e9c7fbbd3fb73e3eba9a3fd34c7fbf3feffe3d3bf135afecdf2ff865f77bece8fda8f4] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n23 : packedGroups 16 16 96128 [0x35e7bffad3fb07cbb52162df7f43cfff3fe2d366dee7e6f58344ba6a7ffdfeddbff697cf8bebafc701aaeb6dc7e95e96d7465f59bbf976639d95ed89f5e762da66799f7c1fe37ad5d27cc364fffd3e4f97fefbbe1cbcf7eff76767559be34e3efa2549ee8,0x19fdbfe3553737f54ecfaf6a71cf3a5ffac5975361fbfd5f5d1b9ffd61fce7fcd42ee7ec67b8f5e3efaad3ddfed7cf43fa46e9e77ebe2bdf03bded96d4cd2791f127f38fd41df5112f2f7f5bda31727aee9e7bfee6b5fe9cb3cbcdfbbffd3dde3fc4dd7,0x7f7f3fc2c2a9ef4ac6f6ffb65edbedf47f6bf2757b8d527fcda69fff96afaf1fda53a8edacf3d9e6bf4faeab9e7b1d3fccbcae9915e8a3df1dc2cddbe7f7d31a1f9fdd0b75cc367bf373d1cdfff32f57aae37b07cbfdfdbeadfdc7e389e984bf57ed83fa,0x387e466adf9fbe1b3ff56e14c5fab7bb7775e3daef3d11ba57777bf7c3fdfff6ebf03f3f77bcd9f7737ea0c08ecdf17b9ff93fcf93ebefd7bf8ffbdbd7e4d5cfd4d23f05aaf6973673b9fbf95d35fe3e6966ffed7dee858957cfc3f9ff4ffaffe,0x6437eef3b296df21787deedaee77bfc2ab7b1edc2476db72fd17efb11b5b5fcd77ba07796fbe6f75b2858effdd9b9947f4e85ed90a7ef9c17edfde7774f6afdf4b6bff375495f7ebb56d7adb2f79be8bba16e4d77aefd96cb955b862acbe57ffa79cb2ce45637,0x70e68d92f8df1b1966a54c6f4b4ef6b0feba6bff38ce1cd637a6f7efa89d1d97fe56f05de7f1755e976ea5ebbdeaa5bfb7febe6d5792d3f73fdfc59fb7fe8ffbf2b95fff7f77ca3af5dee63ed3ba3579de9b2f7faf2e9e8e505cf99b9f59cfd74bf5bd73,0x2f12dbb5fff3f67defbcfbe98311dbe2fffcb37ff3f8bbb3fd574ffacf1e7f347bfcc6fbfdfd77e9a9512bcdbadbaedbf7bddc9f3f73f5f7ffeff0ce17d1e95f6fedeecbbdb2dbd1e4f87bee79fae9f5f31f5ebf75f5ea2ee3c63eb876bd62,0xf522bdc773de91fee65fb19fef7d5e43b63c56d57fba36243ac7f6cf9be3f97df3de59ee40be9e737b777efd56ba7fbb653dab783fd76552f85dfad63bf7f6bdfdffeffb9f5f7feffed402e62dcf57df903ca89b37cfbe1f76db95e1dfc9a9a9797a97,0xb3bcf02d7dd779b61ce74f74e9e7fcea6f5d660354d74e7e6dbba1dc87275f127d7f85ffaf6f6db34eedcd2f5fdffdd3d5faee90ce7ebba9ad259c5ff5326bf7e97f9100fe0f3eefbd7f8bfdffe73e9eba78d56bce4b6777eb7bd47fedae6fff75e5eb9,0x1fdfdee9b5adde38d53712fc6fcc7defefcb3935b9edb79bf3fe1273d6f5ced4899dfdf975d47e55ff8bde7ffb5ed130093b971f2efb7b25596fd5eff5e353f5e98f725dfbfc527f9efa9bea7fff3773fd5fe8fbb6d49f3bdfbb76fd1f9e7f25db1,0xf304bb3d64df6ecbf13cbeeb29adef17a28fddf29344af2fbfbb9b875eeff8a4f77b7eb2be77f73fbdfd9ad6b5bfdbbfffdeedd501fcd5dffb19573fe45efbd7f475569db0f7e1f7c07f963f56bdd34b00bd752c1ff9ff1aff2576f8dfd4833cbb1c3d4fa,0xef495c75bdb2f6e9fdffc1b3f3d27ffc850ab702ee61e6c9997f7fb8ef5649fda3effbb3fdac4bfe673bfaff59e7be9f8d45da534a6fb3d73d462a4f57e76b3ff57ee8b3c0ac9fe7fe33adf7e2ffdb9bb27ff7fece892c046cd477f3bff6711221fdd7b7dd,0x2cd7d503cca7d3327b5de73647efad9dffefebbb4a8be1bdd3ee3c205aded15943ba33fc57377df6d724bbf6672a3c5bbb53f329d1ff05a7ee65eed92ebd7d1c7ffeb7ffdd93d2b3b76db92d61b957ff39cdf57fffbdb7cf76097bbe37482b8ef7b74ba7ef3b,0x38f9cd47ad7cba9dae513cf848fa8b7eda56e0f4fc433f77f9d4977fdbf3e0aed4f8d7b55ca9056ec7cdfef7aa6565afb3273b476b67fd9ab7e796dbd8bf7e5e4bfb46fc9ade9ede1bede6f93c3953c71b56b16ea49feff3765b9ebeb5bde8ff763d4ecfab9b8be,0x21d6d23f36462b41faf6877f223fcded5bf568dd6a7eff7fd9cdbf374fa867dff5f29df0debf6a8b9ad5f13e1f481b5bffdba5c3f6e79e9bec2ffe7e3f5d548dfdd4c14f76cd4cfacfc848df75f8fbeaf1372ed93e6ebc3237831ff9e39bf7b7541698ef7ef35e6,0x3e97b9bf9eb7f79fe86f63af47fe1bb54ffbdb523eb274ab27edd791bdf7fa2f0d65dfd2da23fef1ad33cbfdecc42b91f7ca3eebeffed35d96f109f757bd56cd4f79cdcba272dd1d7bc789aaeafd4f5fcf57aebfc5309995aeefc31bebff7d6fe0b4cc45d3fc] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n24 : packedGroups 16 16 100224 [0x3bce667eb7c58a1cf59dbf2697f03de4bab8c64381e27ab77fd871bc9f5bbbfcf13bdef6fb53fa6d753e9d5476ddfbb57d3cdf5adffefed95ef4f8ab4c789fe1c2e9af8b6c3b3cdfeb3edf4899df9fb8effab8d286972ffdf969c7fd60ff7765fa767da7ff,0x3f69c5f33567be1d732bfaabbffcbef55fff7f5667bb627d6c6b5f73f788771ff74fcd3f7d4a37db9e4df1ec763e5ded751faca765af9c673774cd67db58ee7f4feefbdbe7f4fa7fd6a8ba1beceb5b4449f37677efd9fcd1d095c7f6159eafefedf7f,0xbcd3b66ef37ffbc77f5661b1722c99c76ffb0ecffe6aefc9adde6fae4c5da5c9bb5ae7bdb65eebeb69a3f23fbfa977dfed63cdfb7da6b3cbcff67d34531675ef3f4f96bdff07fb74bf7acf9b6d37e1fcbcfe7ef4b397eb90bb1e76dfeb59b1f6dcff,0x3154bff47be3be7fc95dff175e97fffc507eef1f72d52fc4fb6d49aad7dfdf4f8cdcb8dcf9be28b69b45fa6567e7c87565a0b33faaffdf77431e987f6fbdd4e55bbedec17ded0d70af57cffff39df6979f719cd9bb829f7bffa5e4941e5fbcfe7fa255183a3f,0xfeedf9534dfd7b6998f5feccaf1df78b3fd5bc4be7effd56a0e334ff5737ef73ab222df5dfe9f203f9bbf7d9ec8b75d1ecf936b2beee519dccaf7b56369a51bb7b7a1f398defdec9ed7664dacc1535ba10f5b0bfcbae9beed63bbed29551bcd5b9a7bfd5674e59d,0x1d25fcaddfbfff76fbff67bbbdf8b7b857fe92fbd3397746fdda5cd9ca3fb1f7fdfeba9b62c9a5ea8a6bf79ecfeaed5fef91997aafc1feec11e3dd4f987efd6a57575ddf87df746847898d6938e95e32453f2f7e8acdfc7eef9febe73e5f5cf4fbfffc,0x39e3bfcdbbaf6b9f5d35de1fc953d9edf5cffffece77f4f6edf8dfa3fd3e3c7fef92d8ff3385ee2dd09b399ed5c7cba3b77f1e756f152efe6baf7fbbfdcddee717bb5efbb2f9eebd2ae77efdffccdff3a346f7b3f8f3bfec09deb8baf1f597f,0xafec22f9ef15ae3cd9a6a40d057b65feffa6e9d7ef963fcedffe2faeffb3d72c7acc5b7dded7fff5373f9c3e2a8edd75125e1933dd7ce2d0feab57b7acef7f8b31e7f5dafa6ccad5bbf9fdfdfdf7ebfb6f9dd98576e7eedfdf9f57e9e5ede687578b1,0xebf2f691fbdb9e7adfdcebddfaf57a9b1dfc93bfd1f7d47ff5d45bd145efa6daf65b6bbb09d9ecd2f3ed277b27939cf677466ffdb3b3e2bdbaf1f60658bca12d39f3ffbf507fc6d76acb74b1eb78ee9ed707d777f9148b37ae6bdf5adbd6d73c76f1db41b6f,0x6b4f815fa225c767ff96a3cc9569e77178dfbbff95a9e9bed1facdedefe67c4e274d3cd975dfbaff73ef7d0f97bedfd99435c6bf4e1f76e1c5edfcffe935ec3979beddedffde1a3f377fee7daafba5d5defc8fdb74fde0dafddfffcb1f33d2fcaa95b,0x1e6ff7f1a78cef1771b4bbf2645ee7cff8ffddf5f065f874cb9faee97faaaf7f772292ed61c73bd9ef8bb3afaee71fe957587679e529d487de7d3fda8f0f4be5d3de2f8ca6ddb7df3a22bedf1aee364fff72dfbae357e9d777b7fffc4bd343df5667f35db,0x49fb74fb57ee9370a0e4f276d7037cdfd7defe6b6ecef9501b3579538a8eca3bfb7cdef78fedb07fd3bb5fdcb535cf76e7d6113dfee4cb591dd80cbde796eb87529dbb54ef5bd16a7db8d5d8ff8ba2f857ecdfc58d5f4efce6bf67feabfaf3f56c3389ed07babadb,0x57d65db6dfdef499f57e70affff5fb374b475c5ffa19f7905b9ddfe6b6f9989d6dff87df69ffe4bbbde6e32c0f33f57edeb8fea685d5d78f3dcbc7ecfdaf7fd1e3455e5ffd9bdecd722bde2f9fd9667f8b8ffb253e51ff153cb35f3fed7fdfe6bf34,0x197d35ffdfd7efa4f835f3dbf3df35cbdf4bdef76fee6fd6cf3eea044c39eafdf83f1fc23fde9e77effa2cb5f6ceff9bde7bdef35ff1bffdfee6537feb6e6af8e70b7f65c7fe4ebd829573f7d678affb966b3ac3f9bee0f161b1b0f3f77f6f874d,0x177ffd3b9a07a98f3cea3d70fdc45d7ef8dfda72a88ba6fdfbf78627950fa7e2cff93bf4bf763ae2db77ad93e751dfe9fe6f08a3e75efbb89f5fcedae3ef9f8e33c54bdb57ffd745ff6dfb7dfd846f3b9aefa3fef5db35f3b89ebee3b5fbfdd58cae7992,0x6afff5608dedf595df168f529783a896ee49bfe4effbfe6b594d968febed9fb7feaf9df9cf5e708ff0079eefb51f597ed6ed8762ed3ff75277669c8e57efc86fc1f7a4d45a599b2dc3fb3c8ef9ff7679dcef630b46a578f27fe0d9ee57dd3bec7c321cdedaa8e5e838] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n25 : packedGroups 16 16 104320 [0x2f5f0df2cfa1aecfc789bd71efbfc7b57a7afeaeaf39ffe239fffd1be93f9fa3ed2befefdc36dcd4cfd672c80bda4fcfdef5b7b6f7ee7babf7cf75b8e3edb82762e7c5d8effe7f78497f57d6a320d6abff5fa9df36518ac7dc533bee77cebef57c5fd9,0x1f7d7607eed49abde09b7206efe8ebbe7ff7f1d6e78bc97d2fc9fadeff2db4fe87f74e36fff56fabef57edaf972efcef6e8ff671366b361bbdbbdc7ffcefbff520f6f1eadffb747dd7f957fdcb37faf3db9937bbdefdbfa3cbbdede5a3f34dd,0x13db7c93485e4d0eee8936b8d07bc7a0f6f61774bd6f78bdcb9266f3c0fbd873787d8133cd6f5cff2500e99a6d8379778e1f99fd78a8fc8d7fa8a7efdf99c626330ee5bfdce7ca557f6d6dfa3c87bd9495c767c7cae11acddfd6a7fdf889f47557ff7383d9c3b49b784293f5fef4,0x6e3d6fff3b2e3f53a0557daffdddcfb6e9c5df6f15aad2cfe3bbfbdf62fff57119f5e6edfdb5757c5739a89ff6fbcdde5bb4ef1d9fedf89073eddc8afe7e33e359dfd36eff98e532dfc87b77fdfcf73e4d692de6eabeeab7f7ffbdfbe7e78b4fb,0x1b02a7d6f3ea73cf928cec76cf179f63e9255bedfe1372ecf3cffe7db7b94d5afeec39bfbcf584d9dfe678f7f7daccf113abd7da67409f49f825329b39074cb6eb1791b5ea1e54dffff732b67feb375625eb4a37fd66aa57fbfceb387fd56bfadaf972ef837e5ecf2,0x37dcc3dc1c4ddf5f22ff1e5eb61cf8d8fefff7e3fec7bbbac27debb671c1c67af06eceffcbcb7cbfae23bdeaefd1e3cdfdfd5d3f73a345bf15bfe81cbf67dd273c3c1d4feafabdce9b7d3bdf61c7e7ebea32ddd7d3e0db6fdffd36edf14530de7e46f6f7,0x1152f777f65d534537b6be5f7d74ed1aecbf74d4622e5677959bbabbdef6eaaec7d2e677edbf37e5b8c52fbfa95bbc2d1b078f270f3d03feff96fcadf6eaefbab7f58bcfe2d9ee33dfeecba77ff97f7f37ebfd2f7794bf2cb57dd0f4feed5b5669e7195e91,0x15dce54d36fb48b6e5c45ed9ffff4fd8a76beb9c73d957e607e65bdeddf3f2e47987be7edae6d3fbb2ddf1fdaf7b1ff4996a33d3e28e77bf600f116f8f6a3f82eae17d3c89cda5bafeff71ea8ff7f7f7ef04dfb4deb7c9bf95aaf07c9ba4f48bbf6fb7f8b223ae,0xfba5fdcf5d38fc189d7b4fd5bf77abdbe3aecffd27cff3f2fff9ad81f6f7116ffdf01780acffbc98166179ff63ffd92a5b77de6fffb3db7af9fb59dfad896af0ddf5dbfbbeed1d3778e37f2fde14331cef7f33b5e3ac45a75f26facce9efcf555fafa9,0xf67a23e97e8ffa85defeb6b9fdf605efffa69fd734df01fee72efcf439679f8afed5f8feadee71e147e3f7f782eeecfbef7d5e15fd699cb69962bdebab1c2ebc4f9f9eb2a7f79de7f0fd7b7cfee9ffebb4a17df99e1baf73ad6dfbb7cc76b2ecf4df4,0x4e79a4c5e9a7bc6d5e9cff4550efedf7b58e4162baddea9f7bbfe5b6dbbb706cfbdbf51eceef1efdffb9ef69bf6aa45b537cbbf6326fe87c7a65e99b57fffee74be5bef6fefec9aadb5516eff9afba4f239dcfe6b17a6aa2d1fe7b6d651fef25fd77f97,0xdf5f7ec6d1ac6efbcf7e8c6fe6d3ff0d3b66d7f98d58b1e9857f6f66fd7df6b6877fdb9f7be63bfff7cfc85ae8c929b3f2df466fe27d6fdf51abcaae894b52fc9fbf76fa5a5f1e5adf688b7edfa5e6fbfc98ed07fbff1cf5d896f39f7c95bce754cf7fe,0x3284778affe53d87f21c59efb7eb1dfbb390f6bf5fb7e97a77c51dbecf9ed7ffc7fe715b75ff72d4fedd71f4f6f3bb1bfdf76dcb15f7740f671f7dbe977757531b863ff65f3fbfcbd9cd96f839dd7668df9633375f2f69eb97efb13bd3eb0c6e7d3be482,0x9d5f4e7fae717db4ad275cfff5f93ffbfdafadc5ff9e5f3e9dde9daab1aacd9afa8900c7d6b15ed83dfd5fa8fed1f6bbeed807fdfca43f2e36d6c4d7eae67e08bbf6b35d6bb3159bc2b14971b3af655f7be2eb9d56bf6e3d2f7a799af54915dbdf637bb5efdb31,0x11d7f3698ed95caf4efee7dfbdfd98d6894ae1bf39bfb7f7d8fff899dfb8b3ff7aaebbd53f1bb7a99de6bf6d0e531aa5fec8ffe2c3d0b3bde7bd577577d56c73fde35317ef3f7f5fedf7fcf7dfc64f95ddf84d77bf3adb7cbc7eb7679f7efbd47c,0x287cad2db243fcde903e679c66ce96adf1306ff6ad63af35679efdadd2bfac115ad9e965eea7ddbfc3bfcba75a753aa654f1cdcc8af8d28ee7de9bebf6fdc53b9cafff7fafa4f1f6e3f6b731afa0f5b9b833cc862e3f9ff6f75aeaeff6c585eacdcbd0fceebff58fb] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n26 : packedGroups 16 16 108416 [0x3ebf97f8cbe3f5fb5f3ae7bffca00fedcfbfbfac1e53ff7ef62d8f4f3e59da8df5c3704ebb3fbc9fddb37bf63ddf7fe3adab6de729e6ff70cdfc44385bcde6dfe70e91cdd3f73c7dd3bf3d4fcf78e72e25da9fff09fccbbd86fafe3bd13a3e68f73f3b,0x70fbfe346bb9b6713f79ad6ce77ff0177b2fde2bebdcaff7fb08fd4fafd575ae7161dc1b538936d6ffff7dbecabb18da62e9bf9ef5de5e2874f7e02d2e1fa9f7e1bfee27b11bfecfa7bde9ef7ff77edf0e7abd090bb7ffdefdfd4fde66efdc78ff09fc0,0x4cefdfe1dedddfddffdff7547dcdcef5e9f167eff3fb42553fbfc73bc9cedfe7a9cdbdde5d8ea91afdcdf39b6cfb19fdbb42bfbbbc3edf5176e89b039cc8adc8e38e8f9d3f8addef10fd4e7decf13a6dffc9fefda7e599d3a87ce7996e9fb4b7330fbfd,0x3dbda83ffbfafecfd917a4a8ae71b32793bbf6bfd63feebfeb0d7e57ba63a2f635bf2fb9c541bface5f9f0fcd6f5bee41f9abfeb7a396abdbbeafa9cddccacaff75d7d01c994963e52e13d3ad675ac55fe26f274db605ca6700b52f73e4fca8cfa36bb39eee7bcf2b246,0x1f7f1f6f5f4bfcdf237e260bbf9fa5ff6b3facf97abf3bab93cf7f2eedf69fad34cf5ff3336f0fce85aeefcbef9efd07ffb7f75c3a7d7f776c9959ff5d5feef678f57d745edbb2ff5a3daffe6589fbfbfcff3ce3e646ec5cf75cd2f03b78a7fd,0x3fb6fb7ef71efbbf1cef715c51771ad7ffce5191fffda81c0f7de2d3e9fadff6feafefe95dfddfa11753e97d4fb4edcf4f76e5ebf3f5cc72bacf4ef894ffca7ecaf543dffffaddb1b3574cf974e6e9825df1f0afd7f3bf8fffdb6fd953bbccd48cbe,0x19d267ddfcafeffdd73eb7df4617cfdcdf3345d3af60bf7afb9d7f2f2bfa39ff535b70b76d9badceb6eeebfababfadf32bfb6d692e5bbc2edfe8c37f1cb0e6fe19bec8efd6e7ebed3337e7cf4a084b8ef75efef9edef27e0e3e3de95eb3fedb44bc27a2b1,0x7be175770f61579cdfdadbb3fe0d3e651fb1e5f0dad7d366af935da57ffd67aabfca94cf754546daf7e3e73c3c9a2f3edc7dd7cd7d8fab5453a8efd46f71ea5ad79b94bbc9a1f06b77cf189e94333d2ca3bddaffd3be92a87276fed3df17dd89b4ddaaf833f33fe7fd,0x1ebd17bf7ebf2f9affdd278f547df24cf1fab7ee0eef722cf58be743c137e3f7ecdbae5b6efddfea6fefcacbf1dcb0b83a174eaf15c16b5ebd5bdb58a9c5ad6a58f77c47bd6fffbe87aeadaf652a7bf9cf9b53b3ae5c9df3bbe5f64dfac312fae73dff6eff,0xdff65f371df7d679b255edb1e5fbf7d36c88febb55c77713f5ce49828caa37c2fa195fcef0ef77e1cb16fcfdedcd2b6fae9c161ff97dfa33a767cfce9377f7b6c2f71d53db5cab2defd3fddf90ebbb07bfcbf3f15eddfe6551e37eefffbbde6af2fa67fc,0xbb51456fdfe7393fd3c01bfdee47ebb93fadbf74fcfe7094cc7e15b5fecd75fd69dfde1f77f58ce773976b515fcdde5b48def6dccecf5677f6f61bf0bd7e70aa77fbc57de7faffcbea8ed5654d59dfef7b3f4757cb8fe66ddd6ce8fbedfb8dcd6f71e81,0x77b3cebe1de7ffd9f32cdbffcbaef2e5a5bcefa7d03fa7ddaa2bff58779465b5eb059ccb7f332e2d7dd6f57ba0f5e91d168ee666fdbfcdddccf8fe8bd9e87f49bfb9f6cefac1f8eb867e7bf185f7f0aec87bafaa7bbb74e04de69fed17ddf57f7899cb196d9d,0xaff8eebd3eb68a2f655383fbff9799fe37ffd77aefbdbd395f9d7ed1ec657cebefd458b3e3bf89648c9adf4bf9fdabf54e97f3df96dfcfeeadffecfad5dff838dbed7c153d9ce5e9eeffafbebfee92aeda76ceb737efefb8eddf17faa6d3ede6,0x2cf66cfbc057dfa8bec26fcd1f5ff76ebf5f4bbea3eecff69c356b3d3f9e826eec4c97bbfce5d999f418b243baf756bf77ffb78fb976f7abb9327ab32fcf76827ccc7bbe77901ffd1df797c8ffcd5cdfd5d696ce9eaef933986e0fa07fabbfdecbf580ebf4f7,0x49ff2e31f9f38fb71abf4efb6b422dbf6df76cf947f43a54e67e9b93f6f2f3f9de73f9bbc85fd7e7b7a277f7ebf52cc678bb63c64b47db3237c618b767fba3b5f5e7efa5e9ed3fd0c437357bb6f3e77cb8bfbd9af6a3a5926ffddc9d9fc272d8f8db5a3bc5ff,0x576b233f6fd69f3e9cbd687f8fd98dfbd7d4077d6dcf27bc6bafcbffaadfeb3aafad58b0dcba7bb05e5ef3a73e8ff4758677bdb79aefeeff23d3efaebdacf5abf9dece6e7e5e4b3ddf7dfc7f6b97d8d2173a9f9bdbf6fbadbbb85e4399bbb34bb5bfe4] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n27 : packedGroups 16 16 112512 [0x5fefcddb7579b669b3433fbe67edceffc3ba5bbaf0f161ff96ce6b6589e72d3c9afafb1a9877ed6dbde52e5ff6f79f67f8ba9e97f3b39ccd2f79d0337574fddbb9ff9ef59b559d1da7f9cde5d7b6e76c7e85a72dbb72ee82b77df8e91dbcdeb8abd9bf3df,0x390dc27bbf5db533d97e1d777fdecde1e6fedff6dcef8f1fac64c7d5f3993de76ffe8e9771f896df7a3497bfe213a6f2b8bd5777f7fe96cee059dcc3f8eb826fbd7da359e225f9fd9d4f7abbf57ff71892dff5f4b67a8f5fcdffe36523ea47ff4f578bedd,0x11677fe9bb6f5e39cb7f9beaf33f535b6adfa4fef1a5fbe772cdafbf7e4ba57bfcfb5ffd5b2bc50cf87d1e5cbdd19c7f5619ffe3c56b3fe07bd021efde78fb5dfdca7efd98e6fdcecbcf1b7ddf5b3d95d7a73fff5b1aae3fe9ccffebb8fdf6fcfb6,0x55903f3a129d3eb4d804dbb335f9cbefed9b8e8830ff79bbbd6b1e1bbfdb2f93fefee63be77af2cadf755ead9c5f3d7f1b55147e13eb9ff8e3477f62edd5bdf6b22d38dffbf1d37cce5e36ddea17b44e4ba1eb4dc8eb0fcfeeeedcdfedc3f92d3cedfef2edff0e2,0x18d7d77a3efe7154fd679be2db997936bf8eaefc2ab5e3f7cff4f86df27873fdf13fb09838cd7b690ed6fcfef3f7c8def71f92b50f2a7aff74f45cffee8bb2ed8577fbb90b9677f57f79dda7306a5576d9d143dfbffbf8b7cffe6e7f5df1eebd4802d3dfdf,0xb8917bdcbf7b71376db9ef22d167bedf2afe59c92c64bb06fffb5df2aff7a539794121dbe8cdbf6cb78b7bbc698faf792dccdf4de3af7bd7bf2cffeed5b34354fa5e95f7dcff71ba96bbf8e333b721bba1bfd67f3c86f20e8ea7b3c82b1f6bcd69ff662f7bb8db34,0xf7cc4ff93edfb96b9a7e4c78de89e79f47fab9f93e379bd5bbff67aedfc8ff9c7cfeffeade6e3f97eefedad26bdb69f583eee76fb5fd9ebf73cdde06fd7e8eefeb63fafff1c4e2f1dfffb748fdfe7fda54dbbce739fbcff7fabe3925fbbd,0x21773bbd2f6768fbf57ade16fdef7e0916a7ae4edd994f3759be5b9e0f31d7deeefbf9c629dbffd8ffbc4237ed77d1e7febf8b17ffeb33dce4e5d5d78323ef69c6d2ff973d3c941974caf89e3b07e9ff75fa79a3d0bb7f73628ad1ff7a6fd7efffb37d1dbd,0x6f9ce3f4eee7b54e6e074cbb7689f6d7ab4be5fb9d4bdf6bf75dec9debaeefc3e3fd3df7ffbe25fa07a274a3f5dc8693755f7ae6faee3c3ceb6afb7efffe6c6c9f7d15e2997fdaeefe5edfc1d6f72b0b8f1e9f16f337367f9f5bbec5df797de7996fcb,0x1b7cbdcf7c3ad647dfff4be487bbf6ddebd70cfce567447fdd8979bf2e9fe0b99e06eff7986c8fbf0a57d581e1b76fe8f77a3f37deeec7a5d4e9edeee6ddd7f8fd7ce55fcf2f563e315f3d59d36f7d2d7ff45ab7eceeb39ff4eecbb38ee2e79977abbd6f2,0xd97ebfbfef8fefa23cf5fe39e5f43f5fdc1999cbdf770a7fc6beeacda9fb8fffebcfabe7fbf21def95bdb99c7a6f836b3eb3f5312bf5cbee3eed5bebbe1f03abaccebad27b36f5f73f87ff3f98ed4f998bf70d9e598919b73ad970dd3d8a6bb5ee9c3eb7,0x1ae6bd1750835438ee2bfc9b7b2dd57fe7ffa3e5ed971ff3af33b5bd3884d1cb6b87f792ebabdfd3247cdfd5312b51a388503de57d99ff52fab71f772f4ca66ed7d97e723edb6e5dd6dda7aa16eb8ea1aeb27cd2937d167fceff3f5b7135b5fd49dc6b7de7abc535173ee,0xbfefedacf3d737ff8c3beff92cb2bfeddaf1ff1a679fce973f58fa748553eb312afbfdd532d553afd91727bae73d3ed583337da5fecdabf6faeff7e7b3f7effd7e8e97db7efceae3d7bababa6b8f92ceff1326ef432df9f6bdbe7ebd5bdedd95fb,0x2ccbebffe793caddaf5eaaededff8625fedfffbe6f86f12171bdb3edffa1d0e767edd72f9d5eb6292f756b07972faf61b7f677ebf8537fc9fd32f4f7bbeefdd29c5deacf7df9f9641f17fab6dbffbbff88b8ce78cf30890e9b64a7fbf6d759a11fbe7df,0x87bef8adff775d39b3eff9f4b50f16797b6efe4167fccfacfb66d9baad0ef1ffbd6deb39af7cffbd1f8f2b7fefc99cd5d9bb1eae467d6d7af6ebf7a9eedcfd8ddf9fe9745befaee57a6b985f7abd77aeacedb971c8beffe5f7afbbfbfeacffcc,0x17bf62ade3d6f9ea3579757fdcf7e0eed62f71cee190d7e5a91d544ce97fd5b9a165d55dceebd3ec9dff7767ab1f57fce37703f4fbbbd324ecf3d5b713fbc0ef8e8cdab1d9d5b76fdb9ef5f2fbffe8797c79b2bef94be4f726bceffe57cddfdfd74ff7ef] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n28 : packedGroups 16 16 116608 [0x8e6fece7fcdc4b0df966d7ffffe7135e41fdae1fd4266e52d6bf587fa7ed7f4ef6cfbbb771377eef558df4faffeff95dbbdb953b67cf9ca37afc2f9671bf6db740eedfeb7a7efe33df8dbcdc2d2a26d6faf3ee8bfb7f2cb62fcd77be1696fcef6f3f,0x2f244bf7c750689ee7b8c77a1e39beefffaac3b1fc39f95b69b7b3ef75cbfd9fba27d3aa78db3735927b75dfddf7f5f7d5fe1f089b6e0ffc31fbdff80b7db75ff5fb7b440db5555f9ea177e5af843f39cd36b6f9a7fc2f27bcb93ebc06eee5736fff2b0cddfb,0x6af46afa5efbcf6fddf77f27baf607ea76d5c8ddecf3ff6f6a817bbc9367c2f5f8cf6d733d63f1d73fffc103ec6ffdf566d5beebff78f6ebf3e73defcf13d7ae5fe4767bd3338dffbdf2cb5ed7aff36fbdf4dbbf4bfbb5de9cccb4a2b1b6fd8777,0x2d31fde64abe77bda7fefc69b63e6fc7fd7ee384efc92c9718ddf93ff59667b1b6fdf3b96e1f6dcafb4ff64fbd7e7dfdf3bdffcf9b67be26c8766f576b57d237e8179607aed744bcd76effbcf6f5f27ebb5afcfbbbbe78fab5794e71cb617e358eedfd,0x7ef73f7cb58fe6eb1759683a70bc259de0b3a93f48f99b58b7e1feafe7ff3d5fbfab4b286ed341be5f5ca8773be2b7bfedde7bdf49e9da7242ff7e91f1fef3c1baf56fbb25d9bbac5767ef5b3b1f37fb03abd3b4a6f1bdc6b17fbd6bfea6cbab08ff33a768f7f,0x4b7b6edf96cffdeefdeb7752ca17e1fed5ff74fab3d26eb7bbeeceaabe79feb4b998a5ff7f8cbfedb69fed03fe5bbfde7eff477f1cd2eb17fb569abbdffb2baadf5bf769effbfd65cbfffff036f6d7d9fb3fdfd7ede68c7e287cff3fbf,0x2af7a0e6e0f25fed724dfbd7750e73e1e4b505fc92d9b7fdd834bbf2d9edefa46f21faee1fcad691d788ff6ed787ee9cc793e5befefdd97f6cf3fc5ed4f5cd3dbfd7a9f8cf157f03beecf1c57fa9eeefcc6bfbc7dd7d7f7f721fb8dd1ff3bae7d73f94f17,0x5ffefaeb9fc326d569f6afe96c756ad68b8c1a159f2edf6a40dbff599fbedf53075dea90fedffb763f5b15a6a587fdffe7d677b2ff768e3cf6f5dbbfff9e6d75d7f5e7afe43dc95a3bfaf7e7a8acfefc5cdfeed23bf7df9fe4e13a7f3c920d95b9be373,0x1b55fcb8bb3eef3ffd4a66bbffc9f9a0daf78aad6b58ae57b4ea75da2c8937f68bfceef13e68e465ef379efef1bf16dba8e594fdf3ffbabd68f5253e9ffc8b87f4ef1eae7fd79bcbf9afea9bfefc9865ff651f6fbafe7c8e55e3ec776ff7ff618c960c096b71,0x7e9fd8959fdfdbb667ffff74cde73f34efdcfb6bbe8bfe7bcbebfbc3baa5fdd9addf8cc7ffe5d9fcbf737fab1bdd6376e98cf9f2bffd25fdd6a3f7f4acef36d9d791c6bf5ff1de745e5feeac73fb7af87fecb798afe57f4eb5cb1a6c93f2b9f,0x2aa3f9c4addfcdf3db67767dee7d60bf6e5296854cec74beb6e7db9dbfa5f93e77d3920dbbafc9cd71b07bf43193fc47a1df97ebf5acf74fee2762568ebdf42ecbd473defe3beed3afeedf11adf75743a197f3f1cf0a3f35bbced7fb1fdfbbf5f7ddb86adb88d,0x7be3b5b6feecf59ff3e878769feecffbc67cfceaaaf79fdf6c9bf0eb9be9b5ef77bd6d756fb6614e76b633dcd493cfddb6c1feff3bbab70ed3bf78b7fb55cde91ff7f198f6ae2859bfec513a9778fef32139473e725f30eededeef5abffbbcbd7ffe4,0x15a53ddfde55f779e9cbfce4a7ca1ff56daf4e3b22f2403f3ad125e5f747e73ffdd13c6f5bdabfff7e797c476fb68befcfcaf78f31ffd7d1b6f29d4ef3ed3cf06772716cfacfad96d58fdcbd3cfb5af9fa58272f43f12f9cb6977df3376cc3dabf21f36f72ead,0x4d1e3ebdcf38b8defbf3879f37bf95f80ed7fcffeeb76bbef5da98f6e26b9393bacfaae04ff74db3f3b6779d76d452f39d762b76fbbb9fdfcdb3a7ffb0d4def8ba3f1fa6f77e04d87efafeef60debcaffe9bb3a2d6a17bf1d37716f56277f5a7b66fef6,0x1bf6ede7cbdbe5907ae66806c6d4a64f73663e511d31779130b503ff5a97e68ac27e7ace33a333ad8bf3c9c1213dd578f1bed93febd5e48db8bbe771f6fc45cff22f1b69ef17b9ebfb9bdbea68fdcbcd7ffb7fffb3c8d2fccc07e3fae7f152eb3e5b4733022f77aef9fbdd,0x3db92dcc7fad8ffebeebd1db7dea430ab757df3bbdffdf58448e5a4bd3f6ab1cb3757ed63b6affe7afd5d9f67fd4d876d75dbffba1b74fb49436dec74d5ecf7c8d8bf7bfd5576f0d45467bd627fb7f3789fb1bf77f153dffbd775b85dd58db7dd3febf] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n29 : packedGroups 16 16 120704 [0x377eee2eb8cc7ff96fb34b27e3c35dfed95eee39e93ffc9df47e6ef7ddbfbbe5a53d279789dfbce5fdc0d67733f9ab4ecfec6bf9df29c71f6c7bc7bef10f51dda2fcfb27efde403cfdc71ee79f83b73badfdeba97cd31e66bff94ce1b47fdf776decfa7,0x4b5bb0b85d27a55f69a55fdeacfec37b66789ffa2cd7f312b1ff9fec8dfdfa3f0345d7e9c70fc7b5d4db7c84f5aec8173ff56637697b9907f7387d36fad893eb4f3c748dc5bb71a509776cbf7c9c1d43fe613e8b4eff960fabaf1ffe7cbeff09f6d1ba0e2293def516fdfc,0x1bed3da5f523e3f7fcaf5ffaefebdd7bfcef6eeb295c367cedd3dbcc9bfedbe9d5bfff73afe7436c7fb6f99dac57b66efffee636bf35cfbdbc9fc7f7b0e9fdfd75cfdedf8bdedcf3bb3eb9edffe7ec7e9f6e9efebf5fef9ffbfc796,0x29e4cf3ff7ce8fd6e12f3e2b63eefed42d6e3df47ed3f7666e26e797bbef5d1ded96af5df9e13d67f14dce2ed68a6ccfe46f47f7e107cebfcadbbf5f91fbb6d86ff6a152ddc57dcfc6bdefd0b1ceff0eabeebaef8679bf2fef3ff3deed9daafa48bf692d76,0x121d79b6d96adf3bfb9ee2dfb5bdedbb779bff2c42793f6f7acc7672b90b7d8ffc6fe2f04295bfffdbbbfdf4c1fcff94dfabecbc8e3d812ec99eff1bd307578ecbb75c3d2d5299b8e27f169fa4fff895ab5bfcf917dedf793c07a452e9bb8ce9dd8021f7cfafe780ab,0x5cff14e7f1defa921faa64477e5370c6cdf5556548f5cbdeea6ceea4b97dff7b537e19e42d272ef1fdeee7af472193335bdaf582b949778717933d5bbedb52d129a6e93361dd53617171fdd6c5fa6ad67dd2df18fc1dfe9f9fa07b73ee35ec5f0f6b7f7177e61edd377d32d4,0x30d0b7f2a9729d8e9f83dbd624c9c63e2c7b5da9922cc9b2c76e0a4de7fddeafb76e3e9bfedf32edfd5dbefcff9477ca9fbe1c536f7abd5f7193f99fcf77b9f57ceb9da6e15ce93f917af56bf4e55fc3ffc6e1d3c6f4b7fabb137cbaf923f7312fb5daf34bd9fe9,0x77f45397cd977decef39d6f0e0f6e532b3f969f9b7afb77eefb59e3946f1fcebeeb670dd2955147fed07d7efbe6b5d5e6d9d9b5cddbb6a6db6e1ead0755d4074db1f1f87fe7778bbd5f74e2ee7fbbf15e15e9abf31596625bfe7cdfabb627dd7413b31ebfba7f,0x6a727fdb5765ef2ff6f5f7ab570e74f677f4bead9f626facbfdfdd865fcc875ebb5ffe1aa8bda96fff6df6a5fd15dff7fbc7f171ffe9c71e05caf7d67be6b56beef21bcf5f1d5444b79877efce6f5532641f62df9639dab51d5b75afddee83bff76a7fd0,0x87d4f7f4e7ec0edceaebcf978f9a77bfd67fe51d7dfaf47ef85dbfdcf15a5c6b8f6d5dacbbfec97fe3ebdff28ffab4692b4fde5fd3bf15a6ddad1d3ff5daed3f39dd99a5193f5bf978cf5cf577ed62e11dfb7d6237eebbf79acfe7fd7952ef7cf9de,0x44afb99b6f21eb8307ef507e36246f16efeeebdc97d77df94a57ef538f475cbdcfebef631bfde1b99ddfef5c93ab3adb7d7d481f9fe2fe80fcbde0d441ade3628e65fefcf6efe9ea7efbe23fe967daff9def6bbed2bed5c1fe374f374fb5facfaa2a45fc77789,0x176aae6a873bde77dd586fedcfefdb6b4dffd6afaf8f6dcaf92ee7a6fef6fbe3e1a5bdccdf7b76bb83aaf7ded53fb54b733a7ee9fa1bf2d7959d0b4f9fa3ba1f56f37dd9eeed97b7e6d571a29dfc5735084e87f9208fb998d5b9eb72ee81bace38f9eefefda3,0x9f33fde3df1abfbf5ee5b58aaf78bf0dc793fe45be11fdfbf63bdfea7b7bebfbd8f745cacd4dd7e166f9d7b06744abff5ecff77fff12f7b9d91fbdaadef9f6d7d0f7bafab7cde36fda1f373ffa22729de29d594ba6a0ec24beb6be387f3dc9e4f8fc2beb,0x5f1dbf3276a27ea47f6f30fef73591476f50aabeaedfec1dc37b8fc4f9fadaedde2ef7b9a3a64be80ffe7394eccdbffea3c9ef2bafc4dbfbffe1f5f6db14a95543790797bc68d5d4ef7bfbfb54eece6faeb503dfdecf7f53c3b80eb7bdbaf4af1cddf8ff99636,0x63cfe97beef713da9aeb69d3ef937d1b953259f997fb1def7ffffcf8bc3f29fed86fbf4b7f36708d3b6de3faeb5fabb32e80d327d6f33f526ead070a13f07dd19ff8650cdad9aacf7dfcdb4f58ca97ecba8eec25bd3af49eb2de8f27fbb5ed77435ccbeccc77c4fc9,0x1d75f192ef99d7e37715737f3bbb4fdf346531fb6d7662e1c3eac3f7c79bf07d6643db90967abbee5de35b983ef56f5a7b6add22dc6cc28b29ffb5a77bc3fe5ecfa95eb1eedefbf5e31711bcfebd16defcb73ef694b536796f87366beae26b7abe82e85c5f3353a8f3f] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 80000 in
set_option maxHeartbeats 0 in
theorem n30 : packedGroups 16 16 124800 [0x37a7e3fde3ab3ddfecf67dd66b7e69ffbb6afeebc94c8376bfde173ff9f69667ae7b94effde79138d5ff6cba9ddd776bf4cfe339af5e8fedd19056437d5e437debfa72afbdc9bee75d7cff4e1db655d2615a89ff3cb5939ca5fc572bfb24feaca9be5f16f5,0x17e34fb28f4fdfb7cb1fee7d5f90d6ff207d53f4e8adc3f0b9eae4feec877779493c98ddae656565c15fdd67d7a7bffe2a7cbff7fb33adfc39f73fe7c5f3dfab1ef7b8f7fb7b1db48e46b530ad7ddfbfb38dffb66753bfb2b2628f389f3fd91d7e5fdf1fd,0xf6bbfbd976ea2cf7113de7b576b7e7d6ff9a6118e7a7d77ffedaa54bb9ff4e5fe2655ef12bee255ff3477d1c3f7d6efae04d7ab5f9965f5b0b7fac07cf6dce7bfb80f51ff98ffd43dee2d3cf7d8d9fe9d7973f3f677e730ffc6cfd72ea35ce7dfa2ba538b60,0x1ed9ed9abefafe9bd9adb9f91ffed1e9fd3d7fbfe6f1fffecbfeb13fdaefaff2cc3d3e797a33cebd1a1fe1d63be7a23a6fbf9fb1dcfde8e7e1b3fa7f275fecb33eefebe12e9fc6ff2cfece5ddabb3db1fa3b10d637d8fd1dbae7269735bd13369fdc6,0x7ea27bfb51f7a7f1de4c80e21a6beb0fb4f93f3f95fff8eb9bbfbfd67befdf13f6e5f925b07afa8cd7d9b7dcddf5d7e7fb270c9e747b975f6fadc3f4d6ba396add15b75fdf64f9f86234b3ff6b7a6d773debfb7324a569820b62fd4ff76ca67f0fbf50e6bff,0x1acb1733e9a63bed07b5ffc86ef36d2d939fe6b3f9cff2bcd93c0fadf7ff26f36fef9eb3f9fe67b0ef2d678af4b97fbe63bc79edbfb33b56048f741de57bee975b3be957273ffbe67fef60a7feb7f3d22dfef3efedfc4add5fbdbb7ff2644ee757f1378,0x1dc8ff96d9857f2dbfcdce97b9fedfd987e548ddce535bcf8d39fdde1eab4eefffdbee6e72d48f957ef69f5fe0572fe5ed1f0fff8a3127c39bdcbdfd1dae6fa5b9dff41eaf6e37f46bf03e0bec98b9b4afdbd7a220ef3cbfc7172a897ed3f6bbd510fd549b5dfb,0x2db6ab9d17f9da9a8bf207cf8b5b1677266fe3f7db6f09d2aab9d9c54f6b9ddffa3e1f5e729a9bbb9fce39dbebbb69ff1573966ffe65edfd173d4fb3e7db7ebdf0d79a2e7bf4c8ab386e9fcf686ffeb6f83735cebe1f550f1ca99aff59be87fcbfcefa7f7ee,0x35b31673c9f9cfedda96f7d17bb43adc79dde17ff28bdcadffe7f5e659a6385b1125b87bff49d437d0ff6ffb17f4588dac219a9f58871f676cf91927fbddb1e7973e37b0dfec3eb5aa1adb22cd93b66de59bf9f7edbfe4ebd9736ca27f4f6c6d87aa38d9effe267da76,0x987e8d5532f3cd948c94dd1fb4c6991e9a5049dad77ace79bf937eddf47fdcb5eac3153fe3ef34e7e76ceff5bf7f7ac5ebf7781dd63c52b3dedf4bf13ee0cad03b4f10aff4ef8a00000001d97fdb6bb9f611ffafa7fe64d365ff46f4c5ebff39f90b3aff3dfef9720f869f79,0x1e8ca45af9d9a89d869fcc07d7d79b1ed9ebc3a6d32763a6bfe77bff56fabf57afb733fd7ff5523394266f6c752ecd7336fbb0756a64647ea8ff14edce755e9ddf2d6d1db7fcbcb7efa2c05abbb389adfadb9b5f40f7bfeba6ffa5d7def3672fa1353aa62fdfe29dd,0x7f83493cfa6d70c3e5ffe36fde34f78ad31ff59bf9e4fb97795b80df9adf6eedeff7b2a7ed55f7e95b7d8fe47fef80fd9fbe75a407f9eaad3f5bfb79fbe6f435ec57f57eedf59d36db4cfafc07a2bbf76e6d9abbfc5a67e9d7c3fd1ffe3fbbaf2c383e,0x35318ffb1ddf4aa606bcff7e7f9e319cb7cfa2c78df68dfd6e72fad7577e24dd0faf9faae79d75e2ebf72b7d3d6feb39edfda63ff4cfd73fd643f5126e7cfbe9efeeb5bcabe5ffd574fb7faa517ac2bcbb6b58fd920feda47dd26de7eeff32a97be7afbc,0x14ddbe8f74d6f5edbbcea965fbcfad5ec9ddd5f8ca4be477cd2ed53de4eeffdfddddaf576d4d787b33e31ab2c5b3ab34db925a35db636eefbdfcdcb154b9eab7eca95b709733fdd45bff7e5739ee7ff81f7eefd2bdff0fe57e8efd9d97dbdd96a7bd1af067,0x777ffff6eade8bf7d761e667d8fe5f1b2b574fbfbd7ed6b5b2faa33e1827ff634bf68ccd0d3bcbc3af9dbecb7b7fcfb4e75dd53ffcf352248edafce239eefabd28beffff1f7f92fdcdd384a65a9c70e6ee3e3969be56b36c1f760dbe22c58f38ff7eaff8ef5,0xd78b17b9d7da9916e3baf7bfd5536f0ecef7bcfb7f33ac4f7f5b1b2e72cadf73423fbcd4da53bf71d27adcfc5df4bf6f5f6dbcfb7d61f95bd2880bef975e5b7fbf7aebf4edeb4dfa047afa5ef7156f9c5aa137af97fe7f39f9ffe7aeff9aede7fd52f9] := by
  simp only [packedGroups, chunked]
  repeat' apply And.intro
  all_goals decide +kernel

end A237721Lite.Data

namespace A237721Lite

open A237721Net

private theorem slab : Covers (anchor 1920) (anchor 128896) :=

  (covers_join (covers_join (covers_join (covers_join (packedGroups_covers Data.n0) (covers_join (packedGroups_covers Data.n1) (packedGroups_covers Data.n2))) (covers_join (covers_join (packedGroups_covers Data.n3) (packedGroups_covers Data.n4)) (covers_join (packedGroups_covers Data.n5) (packedGroups_covers Data.n6)))) (covers_join (covers_join (covers_join (packedGroups_covers Data.n7) (packedGroups_covers Data.n8)) (covers_join (packedGroups_covers Data.n9) (packedGroups_covers Data.n10))) (covers_join (covers_join (packedGroups_covers Data.n11) (packedGroups_covers Data.n12)) (covers_join (packedGroups_covers Data.n13) (packedGroups_covers Data.n14))))) (covers_join (covers_join (covers_join (covers_join (packedGroups_covers Data.n15) (packedGroups_covers Data.n16)) (covers_join (packedGroups_covers Data.n17) (packedGroups_covers Data.n18))) (covers_join (covers_join (packedGroups_covers Data.n19) (packedGroups_covers Data.n20)) (covers_join (packedGroups_covers Data.n21) (packedGroups_covers Data.n22)))) (covers_join (covers_join (covers_join (packedGroups_covers Data.n23) (packedGroups_covers Data.n24)) (covers_join (packedGroups_covers Data.n25) (packedGroups_covers Data.n26))) (covers_join (covers_join (packedGroups_covers Data.n27) (packedGroups_covers Data.n28)) (covers_join (packedGroups_covers Data.n29) (packedGroups_covers Data.n30))))))

end A237721Lite

theorem OMA.solution : OMA.R_oeis_a237721_R1_H2_R1.H1 := by
  intro R lo hi
  by_cases small : R < 15552000
  · exact A237721Grid.B4096.certified_interval R (by omega) small
  · have h : A237721Net.Covers 15552000 4705446956544 := A237721Lite.slab
    exact h R (by omega) (by omega)
