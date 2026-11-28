import OMAReductions.R_OeisA218585_conjecture_2_R1

/-! Quadratic prime witnesses in the finite interval. -/

namespace OMA.QuadraticPrimeWitness

private def coversHeads (P : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | a, width+1 => decide (a.gcd P ≠ 1) && coversHeads P (a+1) width

private theorem coversHeads_sound (P a width : ℕ) (h : coversHeads P a width = true) :
    ∀ d, a ≤ d → d < a+width → d.gcd P ≠ 1 := by
  induction width generalizing a with
  | zero => omega
  | succ width ih =>
    change (decide (a.gcd P ≠ 1) && coversHeads P (a+1) width) = true at h
    simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at h
    intro d lo hi
    by_cases heq : d = a
    · exact heq ▸ h.1
    · exact ih (a+1) h.2 d (by omega) (by omega)

private theorem coversJoin {P a b c : ℕ}
    (left : ∀ d, a ≤ d → d < b → d.gcd P ≠ 1)
    (right : ∀ d, b ≤ d → d < c → d.gcd P ≠ 1) :
    ∀ d, a ≤ d → d < c → d.gcd P ≠ 1 := by
  intro d lo hi
  by_cases hm : d < b
  · exact left d lo hm
  · exact right d (by omega) hi

private theorem prime_of_covers {P b n : ℕ}
    (hcover : ∀ d, 2 ≤ d → d < b+1 → d.gcd P ≠ 1)
    (hn : 2 ≤ n) (hb : n < (b+1)^2) (hcop : n.gcd P = 1) : n.Prime := by
  by_contra h
  let d := n.minFac
  have hd : d.Prime := Nat.minFac_prime (by omega)
  have hsq : d^2 ≤ n := Nat.minFac_sq_le_self (by omega) h
  have hbound : d < b+1 := by
    by_contra! hbad
    have hh : (b+1)^2 ≤ d^2 := Nat.pow_le_pow_left hbad 2
    omega
  have hdiv : d ∣ P := by
    by_contra hnd
    exact hcover d hd.two_le hbound (hd.coprime_iff_not_dvd.mpr hnd)
  have hdg := Nat.dvd_gcd (Nat.minFac_dvd n) hdiv
  rw [hcop] at hdg
  exact hd.ne_one (Nat.dvd_one.mp hdg)

private def product128 : ℕ := 0x2bf2f5f313b1784cac2b5cf9532aa6cfa27dfc0f2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range128_2Checked : coversHeads product128 2 127 = true := by decide +kernel

private theorem range128_2 : ∀ d, 2 ≤ d → d < 129 → d.gcd product128 ≠ 1 :=
  coversHeads_sound product128 2 127 range128_2Checked

private theorem cover128 : ∀ d, 2 ≤ d → d < 129 → d.gcd product128 ≠ 1 :=
  range128_2

private def product2048 : ℕ := 0x16564585b08dd5f22877a1318f86bdba7b0fc51815d34d06aafad397b90dcc208983465ef092dd5f060702d33a48c43ff82bfd1c2f3bd33339f9247351e6078ca7f3ce6091e985f04906d8dbd8431850a0ddbf985616af93522af8c99800a2aa0f5d0f3e2203ecc7cf46f27af897650509ee941d6c42f9f8052df7a69aa96f5d6f66c88bca6912855f86bc161e55552cc57a4a876094b64f0e4c61e60b9135466d35e4b21b8ba5382e3f149ce485384228cdff62f1f4e5426551974970db8cd22db8b45094fe86a3fc3225c4f2ec4efa418df4919e5a3bb3530f0fc3c6ebd6520d06dfa1bfc32147ed43d5a6242769f88c2e1c7dd3f74b6b3a8c88e7583b03b870ab7a661d32f204ea77715a9bbe7469cbfb0938d24eed9f79b3de4951c4841251853c4ad4f52e1c3cfcb4e492e9eda056d47b307234379669155a17ecf4da5cb78f5cdc320ba63682aa99ba22a7eaf50eb8a4bada77ffc26c26ecbcb997d4e2793fb4fefa23e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range2048_2Checked : coversHeads product2048 2 400 = true := by decide +kernel

private theorem range2048_2 : ∀ d, 2 ≤ d → d < 402 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 2 400 range2048_2Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range2048_402Checked : coversHeads product2048 402 400 = true := by decide +kernel

private theorem range2048_402 : ∀ d, 402 ≤ d → d < 802 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 402 400 range2048_402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range2048_802Checked : coversHeads product2048 802 400 = true := by decide +kernel

private theorem range2048_802 : ∀ d, 802 ≤ d → d < 1202 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 802 400 range2048_802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range2048_1202Checked : coversHeads product2048 1202 400 = true := by decide +kernel

private theorem range2048_1202 : ∀ d, 1202 ≤ d → d < 1602 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 1202 400 range2048_1202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range2048_1602Checked : coversHeads product2048 1602 400 = true := by decide +kernel

private theorem range2048_1602 : ∀ d, 1602 ≤ d → d < 2002 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 1602 400 range2048_1602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range2048_2002Checked : coversHeads product2048 2002 47 = true := by decide +kernel

private theorem range2048_2002 : ∀ d, 2002 ≤ d → d < 2049 → d.gcd product2048 ≠ 1 :=
  coversHeads_sound product2048 2002 47 range2048_2002Checked

private theorem cover2048 : ∀ d, 2 ≤ d → d < 2049 → d.gcd product2048 ≠ 1 :=
  (coversJoin (coversJoin range2048_2 (coversJoin range2048_402 range2048_802)) (coversJoin range2048_1202 (coversJoin range2048_1602 range2048_2002)))

private def product20000 : ℕ := 0x207dc0f5ff86fd1be4eab851b9a588e0aad9c7b10b490a4b875a347241366dd05e3b7d719472ad173acdf01346915023a83f5da517634366f698fc302722db142fd7219e4dfd93d0e57cdd31414baf080f440da983fa56b87b72747d565eff54eff89905340d3d23591c5542dd467f5adf863e36ef77f8c40801fc6151bb19176ff69c523dff909df50e55d88767d290255d798b656068589f303b7c5cc39b40baeb2d1f2d208740ea9211d2d19e293abda344a24a146fdadba62f998ae678b9c1839a3402991faa27565521dddf7e6fc2a683933d41e2bb12d18902d3b62215f1fadc1f02f9e3a82ddebd15a0a0987330633a9839f8e05d99c36e08e0034e0af4ea484b961ac1f5379867d24ad7f596ab4cdb5f5a717814cf365db32072c5e99f70741fe42331b03b9869dc9ea6d5d0bec3ed1512bbde6317df6ba8e1f74f36311987bf1ba65d2bdf60679840dded7f1ad403149df616c79faed9f66974568c00884e4a9cf122b648627bfc3a93f6ee09fa356efe3a52dcb802738fe641c3b48698719f6182d091a2d840a0572d8c2b33ecb7d1a0c24ec90127cc38627f50d971375b374bcbfaf411fe988ec78cef5c7ffd398cfd6dc505af43b6507057bcdd39af00768d46f4dfa702899773ecfc819dbac3725f829be4cf09435c2a19bd04f9f4bad2803e7a3886ad9b78ebf8002a666f7588ce366aaea3863b3347548f440435e0173f61396e0aaf14fc895d5e1298df8c5588f6dcd9fbd0e6aa641de4058c2e8f5c10361ff7e2523b5b109cd8500d2657c9de230f013b6ffdf54a8112d0913f2996d13690375a94e8c52fec3b8ad6813aa6e5ca2ac42f69aa602f79fd4fba60e0e4258ca7bf8fedeb244f95c309f20c37b3d58d1850e38e32222c2995a6b42437206eeed9b495acec4e60554f7f3aa9d2a5d9c1dcb510bd5e3ffc098cd741d23115c4aacef20896b34b026133d4102fea14295bc4467c10a63688a29fe3dc8bb8c60ab09fecb0730ffdb5b0c379b34518b7b2fd2d5553ebaab2abeb9e68cdc3280cc41f4b344fe7204cdc8c5787f9ee2d521589673c5cbbcf2d9292f7925069556a54618a11971b8db55aad01d6791e6ba6bef20cb5d7efc338b1d3f2ea2992db65fc84e79f5afe3af01684cc148c944ed5ec1ee57a61668f114260a3128a967ff0cc01613dd3cb654867c5697887cbed2859f3be68edc013c5537ff50a00619a6091a5548463f83413b65a0a09f0d98dfdfc735cecd2b51b6c774c778a0604c7cb59725517f543201055d7928b862f69c122e90ca2fd05b016977a951e26eadf8a681f161915620d779856ffc0d45fe0fdd3963cb4197e2e54307b66edd773f68d15687f3fc51f1f06a10c373b36fc6715429603ffca4efac4e4d05391c0f031df03a4caa4edf06a4c49630c4bcdba39c5ca19be448fbfb3629bcae7e91a162c8c13fb4174613b421914e323e74952060367691acbf4a0c36eb47d8b5ea7b70654d38414a3c11f8705a8b11140875e17da1cb27bff3238de2e31740e8152c32ba7775475793db3ebd2d8799006351f69cb256f92bfaa31a296acbefbc0c98cad109d89ef35d79ed0fad381669fa74cff480d4f953cfc1816fab0746ae91dfc592683ba9bd2a30ca3120892ac0278e2855392fb0575dce3dad3badc1edf2e962c299ea5b8bebebc1b2ac8ec65d25f44f2250b51bc1706e35428fed5e7646cddd7887d3254f311decbb2737cfbbface64fcd8edc161b4071686c954d923c80dd8fae123deae9840074aec9e6dde3e69737eee5eb77ceab237672efb0d79d2b7efbecde40b110c8c67db273f40c8883fe778506c209117c0154f019fea9d73ac46a01f72908b2b72fe0cf7500b66189ed277cd5051f39844760d404b8d574d427540ffb6ec16582a9752587033e2605b5ae4a23d402758c65b6a6912ce85c4f6730023163f9586956f27e77ba86331640d08064e4d3d04b2c158eea7dea032b8bec39644f9a65e707b7a5feafbce756857d19ea19a8b8da68945ca504acaa9d2e8750b255128d92dcf17f75bd6e25fff979ea002a0a5f35f1c5f084af73093f1b841b448c60b308056b175d846c5e1dc5ed4980a571073f12835a426f74ec60480d3b46d7b292867e2196ce0037670070722b276d247873dac6e64c3e3234b3544815228b9bf8a550b8c3a281bd5e23d2995f3115292fe53586e5ed4a227f26011aefd5bb780e2544de2b0e97fa2314324f81e508adfbdf76c897e1b11b40ff362fdb2e90ed1e087f83f5d9019ce5d8e1d1a7c8704f7ead1eb12e3b94321826c41ff066e2eb2e4ecc76c6fce2cdf7f92d134412947fc183364aaafa12a034017dadb5fcf738f5786f4a71e71d20aea17926e7dfbfd450d0ce3c40762e1b4cc082874d6bfa91bbe065e6e4840a63bc0939a6f2900c2d34cd68973c972349579f0de44af35a4e4524d16df6806b79b5132c467a4ed8e1578b1f7eef3894a78b3ceef575701b3099390aa38db8ec369ba98943c3652766fc56186eb0a8faff5125f129cdd4e0055342f7f46113f63373d9c79b671a2528ff69e3e65d2d3998c6bff33905826a7f52a850ebdaddc7935b7d3502a84ad044bdc238c3b5c1541ca3c535957d0e5f7a9902b64845dcdd5e5d03f150b1118b151ecea753a77ea477192cf40d4dc13e91b2c311261c61bb8ef327bdf017ae5bc18e417d0cc4dff58fd76786efab5083946e15671194eea5de395e697b79ff6d871d387db0f1e7b239078480714adf28ecfdd03492a36bdd912a2123a0d6529c5e9905a03ee3392de008e676d0a560dbcad873fa2eca690522d03aeb7f0bc2a310ed9e4157bac7b1faf20eb4a76ab9c386ed4c7bc29f901c4cca3b1ced047581ff8e5ad7c14ba399f5895e75fd82606b8284bd32c2d67d5bd048f70c91b4567b5ce48b0a369e552ee9ee9eca654e7bd8cc7b9ce14f30e3cd2703a2b48a0210e313c7b836d008fdf4d1932313368db895bcc4f5ac57376701c603fb0c2f891f0e6dd17a9ca24fd9d603816a845cf48691ed6a3774f2af0d73c1d89c3565716798fe3e92cf48c3be31038c750b843fb10737b38a96cc935c9f68ba7f8e8a7aa8d20083f6f6e04e37f6354c9b17aeba085ad314018f0fa908020cf3ffe7e4345d4b0cb326fdbe827be02b6ba15d1baac35f8a537814454cd02568c9c0667bd52b889e961e8fb3245c69a0213b975e700c91d335494baf6900f09fb6af650a277ab371aba423cea2a14537368a8c04319ba28df082ae5e8d0a9d4b6f930f42379a4a239ff3c69a2422ff403bcb240766ed1a9d007b58a377cb9d103d17119a03e49d9fcf2febc29bb3149401f478282a57aa0ec94b114d4894c5ddc42d45a9b13602665326ad1e0e4dd29f432b3a76546348b5b6862caaa2fd4b90e68d7cf58d419f9f1e5662673c02ed8e57c01516cf5ac0114c4e488803170e89136c5cd6e4908a680e18858494fc5b438bc93f876bdaaf20e21b8f4d3d83de83ec1579edcf6d8709b160e6655f5a9930cf345f673abe6b09c4acb49e91f889104331b537a6bdf8acf8ab66794bd11bf0de1c5c129dd367ea3b45c812457fcc7ed407011ea6b89eef5117ca212c7fcc2f595515de577db08ae5d6189031c3fe5a6876a49677d7a93e408110fd5c607ef0deb24948211e6b0808c14ce18a75797f28de317a70797f19f47aca8912fca56fa2e84dcb4ef87a61c75f7820531611177654bde0533b86caf007891be3b415073e106f0be55ff69866e787996584717cb57c282a4d3f1fc352821eeebedec70392e7e034d583def8f4b1ddbd56d7de78908be36e77ff23faccc4971cb982746b6aaefbd7988de1fbc1d1fd1800bc37c30b95a64d5953daf8dd21f2b01379aa016c095e752a9c6856c75b6e0f4513ce0e62fccbd61362548bb336108271f33a443bb4877e184e4881010ab5bf2ca936705903e961d79403cea4b685401fb6cfa7a55cb56472478f400d59c53794fd59a87df5e90adf9915a57c14dd209170abf27276deb8d3a4b5deddc1f95f79bfcac9e8a5fc4826a757c5fb3b173baaf7fda40fae344540dfd137a32f24a22e9d93e9478f145f0bde0c90acc962fb1d2a3eee71daa05b546e2e4c7d5bb07d0db48e6cb52faa4836a73a62f74a50e4473e9d684ba83e32ce2fc66cc778579a775999dab76a00bb3d96c9360f67138653bde134e3df4abaf613678afb95da20837030a626f3ad4267ee55fadafd1e04bf4e3ae2183be5583d65697d52d2a066e01f92bd39d68ff50bb72a45e22258fe20de77b979cc060c4d321dcfcb6fe12d590750b4eb0ceb3214fe702be56c2c4d336c25658d845816d3522292526c44ffdd04abd05b773ff707fa69d94f29a2a5525eff1c6865e404db483fad160f8e15b0af7130040df19e93e6fbf06bfb6063d87d469ae732deeba24e1040a7841e5b10405d680e3a52d958c9043d44ad187dc5704ce5f396fef9c0eaaf893a24d71ff8b38693ce62f4386fde6e99cb550ee2b0e25368f0764397a50f35ae37cb73f7d65d2c75c55e62468fe022047e10b1b39dce9283fe4b08199da3880e23fd7dd8fa60ea535b832340e5173b711b22d4ed66b810a9bc877c4cb353622a544e806a42d3b30cefbe9c28cb9d027cd6636273f3a7d16b2746ab6bdac6420b65b53a5b6b6bbb4faf3e33dcc571c528f5cfa96ad3c25ab255fce10f524ea00e74510f77c73f9419c3e37368a823faaffdaa0432cd6a69b0d44b51543a14cd0ac88d443894dc4ddaebb607ade54a312aa24dd9344e1010eec9b858f11322b1eeb75338879453ddd2ed38e6008c3478c8c47ab71421c3152448301d375bcacd4364241cca6450166b2b53abab0fdf87acfbd430e3e0c94e456a4a84241ef01ed2d1f217153c05a1359a4b3c76383edac29a0d52a00010d9cf99b5233bde385aae76d60d384594b8300fecdb8537c202b28bef0049f980811ba8d02a5d1332e28c684675aeeaa805c836d5174eac1993ecc856bb7f63bfa3bb96af53f6f9f8daaea5f04f2e4e41216156f61f8ff2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_2Checked : coversHeads product20000 2 400 = true := by decide +kernel

private theorem range20000_2 : ∀ d, 2 ≤ d → d < 402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 2 400 range20000_2Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_402Checked : coversHeads product20000 402 400 = true := by decide +kernel

private theorem range20000_402 : ∀ d, 402 ≤ d → d < 802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 402 400 range20000_402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_802Checked : coversHeads product20000 802 400 = true := by decide +kernel

private theorem range20000_802 : ∀ d, 802 ≤ d → d < 1202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 802 400 range20000_802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_1202Checked : coversHeads product20000 1202 400 = true := by decide +kernel

private theorem range20000_1202 : ∀ d, 1202 ≤ d → d < 1602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 1202 400 range20000_1202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_1602Checked : coversHeads product20000 1602 400 = true := by decide +kernel

private theorem range20000_1602 : ∀ d, 1602 ≤ d → d < 2002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 1602 400 range20000_1602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_2002Checked : coversHeads product20000 2002 400 = true := by decide +kernel

private theorem range20000_2002 : ∀ d, 2002 ≤ d → d < 2402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 2002 400 range20000_2002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_2402Checked : coversHeads product20000 2402 400 = true := by decide +kernel

private theorem range20000_2402 : ∀ d, 2402 ≤ d → d < 2802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 2402 400 range20000_2402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_2802Checked : coversHeads product20000 2802 400 = true := by decide +kernel

private theorem range20000_2802 : ∀ d, 2802 ≤ d → d < 3202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 2802 400 range20000_2802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_3202Checked : coversHeads product20000 3202 400 = true := by decide +kernel

private theorem range20000_3202 : ∀ d, 3202 ≤ d → d < 3602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 3202 400 range20000_3202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_3602Checked : coversHeads product20000 3602 400 = true := by decide +kernel

private theorem range20000_3602 : ∀ d, 3602 ≤ d → d < 4002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 3602 400 range20000_3602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_4002Checked : coversHeads product20000 4002 400 = true := by decide +kernel

private theorem range20000_4002 : ∀ d, 4002 ≤ d → d < 4402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 4002 400 range20000_4002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_4402Checked : coversHeads product20000 4402 400 = true := by decide +kernel

private theorem range20000_4402 : ∀ d, 4402 ≤ d → d < 4802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 4402 400 range20000_4402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_4802Checked : coversHeads product20000 4802 400 = true := by decide +kernel

private theorem range20000_4802 : ∀ d, 4802 ≤ d → d < 5202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 4802 400 range20000_4802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_5202Checked : coversHeads product20000 5202 400 = true := by decide +kernel

private theorem range20000_5202 : ∀ d, 5202 ≤ d → d < 5602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 5202 400 range20000_5202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_5602Checked : coversHeads product20000 5602 400 = true := by decide +kernel

private theorem range20000_5602 : ∀ d, 5602 ≤ d → d < 6002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 5602 400 range20000_5602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_6002Checked : coversHeads product20000 6002 400 = true := by decide +kernel

private theorem range20000_6002 : ∀ d, 6002 ≤ d → d < 6402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 6002 400 range20000_6002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_6402Checked : coversHeads product20000 6402 400 = true := by decide +kernel

private theorem range20000_6402 : ∀ d, 6402 ≤ d → d < 6802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 6402 400 range20000_6402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_6802Checked : coversHeads product20000 6802 400 = true := by decide +kernel

private theorem range20000_6802 : ∀ d, 6802 ≤ d → d < 7202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 6802 400 range20000_6802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_7202Checked : coversHeads product20000 7202 400 = true := by decide +kernel

private theorem range20000_7202 : ∀ d, 7202 ≤ d → d < 7602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 7202 400 range20000_7202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_7602Checked : coversHeads product20000 7602 400 = true := by decide +kernel

private theorem range20000_7602 : ∀ d, 7602 ≤ d → d < 8002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 7602 400 range20000_7602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_8002Checked : coversHeads product20000 8002 400 = true := by decide +kernel

private theorem range20000_8002 : ∀ d, 8002 ≤ d → d < 8402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 8002 400 range20000_8002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_8402Checked : coversHeads product20000 8402 400 = true := by decide +kernel

private theorem range20000_8402 : ∀ d, 8402 ≤ d → d < 8802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 8402 400 range20000_8402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_8802Checked : coversHeads product20000 8802 400 = true := by decide +kernel

private theorem range20000_8802 : ∀ d, 8802 ≤ d → d < 9202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 8802 400 range20000_8802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_9202Checked : coversHeads product20000 9202 400 = true := by decide +kernel

private theorem range20000_9202 : ∀ d, 9202 ≤ d → d < 9602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 9202 400 range20000_9202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_9602Checked : coversHeads product20000 9602 400 = true := by decide +kernel

private theorem range20000_9602 : ∀ d, 9602 ≤ d → d < 10002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 9602 400 range20000_9602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_10002Checked : coversHeads product20000 10002 400 = true := by decide +kernel

private theorem range20000_10002 : ∀ d, 10002 ≤ d → d < 10402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 10002 400 range20000_10002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_10402Checked : coversHeads product20000 10402 400 = true := by decide +kernel

private theorem range20000_10402 : ∀ d, 10402 ≤ d → d < 10802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 10402 400 range20000_10402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_10802Checked : coversHeads product20000 10802 400 = true := by decide +kernel

private theorem range20000_10802 : ∀ d, 10802 ≤ d → d < 11202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 10802 400 range20000_10802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_11202Checked : coversHeads product20000 11202 400 = true := by decide +kernel

private theorem range20000_11202 : ∀ d, 11202 ≤ d → d < 11602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 11202 400 range20000_11202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_11602Checked : coversHeads product20000 11602 400 = true := by decide +kernel

private theorem range20000_11602 : ∀ d, 11602 ≤ d → d < 12002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 11602 400 range20000_11602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_12002Checked : coversHeads product20000 12002 400 = true := by decide +kernel

private theorem range20000_12002 : ∀ d, 12002 ≤ d → d < 12402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 12002 400 range20000_12002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_12402Checked : coversHeads product20000 12402 400 = true := by decide +kernel

private theorem range20000_12402 : ∀ d, 12402 ≤ d → d < 12802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 12402 400 range20000_12402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_12802Checked : coversHeads product20000 12802 400 = true := by decide +kernel

private theorem range20000_12802 : ∀ d, 12802 ≤ d → d < 13202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 12802 400 range20000_12802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_13202Checked : coversHeads product20000 13202 400 = true := by decide +kernel

private theorem range20000_13202 : ∀ d, 13202 ≤ d → d < 13602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 13202 400 range20000_13202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_13602Checked : coversHeads product20000 13602 400 = true := by decide +kernel

private theorem range20000_13602 : ∀ d, 13602 ≤ d → d < 14002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 13602 400 range20000_13602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_14002Checked : coversHeads product20000 14002 400 = true := by decide +kernel

private theorem range20000_14002 : ∀ d, 14002 ≤ d → d < 14402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 14002 400 range20000_14002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_14402Checked : coversHeads product20000 14402 400 = true := by decide +kernel

private theorem range20000_14402 : ∀ d, 14402 ≤ d → d < 14802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 14402 400 range20000_14402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_14802Checked : coversHeads product20000 14802 400 = true := by decide +kernel

private theorem range20000_14802 : ∀ d, 14802 ≤ d → d < 15202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 14802 400 range20000_14802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_15202Checked : coversHeads product20000 15202 400 = true := by decide +kernel

private theorem range20000_15202 : ∀ d, 15202 ≤ d → d < 15602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 15202 400 range20000_15202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_15602Checked : coversHeads product20000 15602 400 = true := by decide +kernel

private theorem range20000_15602 : ∀ d, 15602 ≤ d → d < 16002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 15602 400 range20000_15602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_16002Checked : coversHeads product20000 16002 400 = true := by decide +kernel

private theorem range20000_16002 : ∀ d, 16002 ≤ d → d < 16402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 16002 400 range20000_16002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_16402Checked : coversHeads product20000 16402 400 = true := by decide +kernel

private theorem range20000_16402 : ∀ d, 16402 ≤ d → d < 16802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 16402 400 range20000_16402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_16802Checked : coversHeads product20000 16802 400 = true := by decide +kernel

private theorem range20000_16802 : ∀ d, 16802 ≤ d → d < 17202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 16802 400 range20000_16802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_17202Checked : coversHeads product20000 17202 400 = true := by decide +kernel

private theorem range20000_17202 : ∀ d, 17202 ≤ d → d < 17602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 17202 400 range20000_17202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_17602Checked : coversHeads product20000 17602 400 = true := by decide +kernel

private theorem range20000_17602 : ∀ d, 17602 ≤ d → d < 18002 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 17602 400 range20000_17602Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_18002Checked : coversHeads product20000 18002 400 = true := by decide +kernel

private theorem range20000_18002 : ∀ d, 18002 ≤ d → d < 18402 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 18002 400 range20000_18002Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_18402Checked : coversHeads product20000 18402 400 = true := by decide +kernel

private theorem range20000_18402 : ∀ d, 18402 ≤ d → d < 18802 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 18402 400 range20000_18402Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_18802Checked : coversHeads product20000 18802 400 = true := by decide +kernel

private theorem range20000_18802 : ∀ d, 18802 ≤ d → d < 19202 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 18802 400 range20000_18802Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_19202Checked : coversHeads product20000 19202 400 = true := by decide +kernel

private theorem range20000_19202 : ∀ d, 19202 ≤ d → d < 19602 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 19202 400 range20000_19202Checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem range20000_19602Checked : coversHeads product20000 19602 399 = true := by decide +kernel

private theorem range20000_19602 : ∀ d, 19602 ≤ d → d < 20001 → d.gcd product20000 ≠ 1 :=
  coversHeads_sound product20000 19602 399 range20000_19602Checked

private theorem cover20000 : ∀ d, 2 ≤ d → d < 20001 → d.gcd product20000 ≠ 1 :=
  (coversJoin (coversJoin (coversJoin (coversJoin (coversJoin range20000_2 (coversJoin range20000_402 range20000_802)) (coversJoin range20000_1202 (coversJoin range20000_1602 range20000_2002))) (coversJoin (coversJoin range20000_2402 (coversJoin range20000_2802 range20000_3202)) (coversJoin range20000_3602 (coversJoin range20000_4002 range20000_4402)))) (coversJoin (coversJoin (coversJoin range20000_4802 (coversJoin range20000_5202 range20000_5602)) (coversJoin range20000_6002 (coversJoin range20000_6402 range20000_6802))) (coversJoin (coversJoin range20000_7202 (coversJoin range20000_7602 range20000_8002)) (coversJoin (coversJoin range20000_8402 range20000_8802) (coversJoin range20000_9202 range20000_9602))))) (coversJoin (coversJoin (coversJoin (coversJoin range20000_10002 (coversJoin range20000_10402 range20000_10802)) (coversJoin range20000_11202 (coversJoin range20000_11602 range20000_12002))) (coversJoin (coversJoin range20000_12402 (coversJoin range20000_12802 range20000_13202)) (coversJoin range20000_13602 (coversJoin range20000_14002 range20000_14402)))) (coversJoin (coversJoin (coversJoin range20000_14802 (coversJoin range20000_15202 range20000_15602)) (coversJoin range20000_16002 (coversJoin range20000_16402 range20000_16802))) (coversJoin (coversJoin range20000_17202 (coversJoin range20000_17602 range20000_18002)) (coversJoin (coversJoin range20000_18402 range20000_18802) (coversJoin range20000_19202 range20000_19602))))))

private def fastPrime (p : ℕ) : Bool :=
  if 2 ≤ p then
    if p < (128 + 1)^2 then p.gcd product128 == 1 else
    if p < (2048 + 1)^2 then p.gcd product2048 == 1 else
    if p < (20000 + 1)^2 then p.gcd product20000 == 1 else
    false
  else false

private theorem fastPrime_sound {p : ℕ} (h : fastPrime p = true) : p.Prime := by
  unfold fastPrime at h
  split at h
  · rename_i hp
    split at h
    · exact prime_of_covers cover128 hp (by assumption) (eq_of_beq h)
    · split at h
      · exact prime_of_covers cover2048 hp (by assumption) (eq_of_beq h)
      · split at h
        · exact prime_of_covers cover20000 hp (by assumption) (eq_of_beq h)
        · contradiction
  · contradiction

private def good (n : ℕ) : Prop :=
  ∃ x : ℕ, 0 < x ∧ 3 * x < n ∧ Nat.Prime (n * x + (n - x)^2)

private def checkWitness (n x : ℕ) : Bool :=
  decide (0 < x ∧ 3 * x < n) && fastPrime (n * x + (n - x)^2)

private theorem checkWitness_sound {n x : ℕ}
    (h : checkWitness n x = true) : good n := by
  simp only [checkWitness, Bool.and_eq_true_iff, decide_eq_true_eq] at h
  exact ⟨x, h.1.1, h.1.2, fastPrime_sound h.2⟩

private def checkRows (a word : ℕ) : ℕ → Bool
  | 0 => true
  | width+1 => checkWitness a (word % 128) && checkRows (a+1) (word / 128) width

private theorem checkRows_sound (a word width : ℕ) (h : checkRows a word width = true) :
    ∀ n, a ≤ n → n < a+width → good n := by
  induction width generalizing a word with
  | zero => omega
  | succ width ih =>
    change (checkWitness a (word % 128) && checkRows (a+1) (word / 128) width) = true at h
    obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp h
    intro n lo hi
    by_cases heq : n = a
    · exact heq ▸ checkWitness_sound head
    · exact ih (a+1) (word / 128) tail n (by omega) (by omega)

private theorem joinRows {a b c : ℕ}
    (left : ∀ n, a ≤ n → n < b → good n)
    (right : ∀ n, b ≤ n → n < c → good n) :
    ∀ n, a ≤ n → n < c → good n := by
  intro n lo hi
  by_cases hm : n < b
  · exact left n lo hm
  · exact right n (by omega) hi

private def rows13Data : ℕ := 0x1852a188820e344891a204820a040821a0818326244810a1c2850208889160c4840a0c3832a04583020c48412180830605184020c38706102861a042810e240810a283831e1c1870e08181120c0820610a81020c1812a040821a0818602080850a043850208183020c082160428306084830208184121c28306088840214087160c282020418a0a0808d062808302101830a08182120408c06102870a1838116040820208583020808512042820e04283020c084120428206044840a141840a1008306042840e0c087060c38202141810e08081060c0850204181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows13Checked : checkRows 13 rows13Data 250 = true := by decide +kernel

private theorem rows13 : ∀ n, 13 ≤ n → n < 263 → good n :=
  checkRows_sound 13 rows13Data 250 rows13Checked

private def rows263Data : ℕ := 0xa890e0838a0a1c5862a0418c0e0c08d1210586021488f1a0848a0a183831e041833e08382123438e0610a8722141822a04086021c5860e180852e0c5890e097830e2c0810a282821a105812608187121098512045811a0c38a2a0c28202042811624a81062808312042830e2ca85121008302104811a1438b061038302085830a08187061c98902082860e14082360428f06044810a08494160458306045890214382120c5821a201840a086811e0c58502101835e0818816106820e10287020c38116040820e1c1860a200812a242821e042870e0c381120c883

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows263Checked : checkRows 263 rows263Data 250 = true := by decide +kernel

private theorem rows263 : ∀ n, 263 ≤ n → n < 513 → good n :=
  checkRows_sound 263 rows263Data 250 rows263Checked

private def rows513Data : ℕ := 0x940e1458d0220382361d585020849302181882a40682022c18322149810604b831a1c4812218a840a1c28806088892e08682121c0824a144810e087880a0d2850e0478622446842a0c0820e1c58602149812a10e8306145830e3818d0a0c282121488c220c48112042882a091830208385161868612048810e080820628582061c1810a2c08a062408602082831a20184120c9850e104861a141810a043820228b830a18481061c5820204d833a3048112286833204b840218f850a1c2860608181160c0850618082020488422240820a0c58342045830e20381

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows513Checked : checkRows 513 rows513Data 250 = true := by decide +kernel

private theorem rows513 : ∀ n, 513 ≤ n → n < 763 → good n :=
  checkRows_sound 513 rows513Data 250 rows513Checked

private def rows763Data : ℕ := 0x87121008326101810208387220c286020448122080825e1858302348870e24981160c682021c2840a90482220408236141842620181062428c1e101830e1498b5218995061c4893a300870a406850e041810e20082120c0881220d830e2469006600850210d811a08a811228283122c5841614181061c0820628784160818812042820e04d8c02300840a1c38e0614b810e098840a1c0830e04890160c387161808b02391925e240811e0cb86120418c0e0c1821618386021c4810a14384060438906081860208481520c585120818c0214a8206042830e10781

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows763Checked : checkRows 763 rows763Data 250 = true := by decide +kernel

private theorem rows763 : ∀ n, 763 ≤ n → n < 1013 → good n :=
  checkRows_sound 763 rows763Data 250 rows763Checked

private def rows1013Data : ℕ := 0x4813e30a812204c860e141830a181870628685120818332387880a0438b1a14786260c087121809406382843a08085161c2821a044810e24481221808302201831a20d9012040940e102840a18688061c38f06141870208f87120c2821a08a83220c0810a0488826044830e315850a100860e04d840e0c0904618b88120418116084842a0ce8602342831a08a822a040862a1c581021818436105830608b843a2c08a0a046883604886021808d16343980604d860a081841e1c586062108446080870648c86061c1830a1408d2a1c3831e041810e083812e0c985

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows1013Checked : checkRows 1013 rows1013Data 250 = true := by decide +kernel

private theorem rows1013 : ∀ n, 1013 ≤ n → n < 1263 → good n :=
  checkRows_sound 1013 rows1013Data 250 rows1013Checked

private def rows1263Data : ℕ := 0x585122c287020ca87060c98606581811a24385060c08c12044860e083841624082022c289260c690161c386260848726087811211a85020418d3a480810a04888063878146147871210083062088102086821e0c0881e38184220838d060c585021c1830e24c8216042864a10e811a184822a04e820e28a83022018a061038202042870e0c0880a0c3821a04486021448a1634085060668c163c69306180824e282830a08085061cb8302102810e08a822a0438c06342901620197061008806347861624185520c38502201830e2c0811204682061c4860a08084

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows1263Checked : checkRows 1263 rows1263Data 250 = true := by decide +kernel

private theorem rows1263 : ∀ n, 1263 ≤ n → n < 1513 → good n :=
  checkRows_sound 1263 rows1263Data 250 rows1263Checked

private def rows1513Data : ℕ := 0x1872210086261d38c0a384810a042881e1478d6a3048812182820608e830a307871218c850e042814a44382061008602142830e200813a0c38302113812e38984120c0830610a84160c4810a106862a45a84260808d121c58502048874654a821e048830604a810a08485121828e060818132146822a0c38226381810e784810a0cb8502081874a0c68e2a242850e1c5810a1848106045821a345840220085061cc851240d870e60a810a048820e0518102141841e109831a1c581021478e160c38602157810a08a88061c0852a044860e0868116108830210786

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows1513Checked : checkRows 1513 rows1513Data 250 = true := by decide +kernel

private theorem rows1513 : ∀ n, 1513 ≤ n → n < 1763 → good n :=
  checkRows_sound 1513 rows1513Data 250 rows1513Checked

private def rows1763Data : ℕ := 0x8810e0c682121c98b6604b843e48c810a1d1a60e20b813e20c8136118820268781020c1814210e850e441830e08987060489a1a041873a2c382063468e06213830a096842e0409a06445891a08087120c38812141950a08791221c5854e1c2811a0818512180834e1048922144810a105880e144840e08787460c285121108a0e0c08412306830e08783020cf8512040880e1018c02201874e1c28b0604a84162c381060c3831e1c58182089812a2408202145810a0c1820604b850e3858346181850604582120828c0e0c98d061d18b06404811a0c0841e18283

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows1763Checked : checkRows 1763 rows1763Data 250 = true := by decide +kernel

private theorem rows1763 : ∀ n, 1763 ≤ n → n < 2013 → good n :=
  checkRows_sound 1763 rows1763Data 250 rows1763Checked

private def rows2013Data : ℕ := 0x385020878a026c18a0a0c98202107830e0c082120488806087830a24a851e18583420828c160838712102860634a84222c081061808c0e2c1830a081822e183820e7c4860214688061c3821a081830221281221c5890204a83020c08806191890e113840a1408716046830e05181160c9871e1008b3e508832608385060c08c0e10481260c385121809b061c787160c6821631282021cb84562008e660c2820208887022c0820a1cf820e10a811a08384420429a06041840e140872e10c82021448a1a087823a1c08c26081870e381821204e821210a810218d8e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows2013Checked : checkRows 2013 rows2013Data 250 = true := by decide +kernel

private theorem rows2013 : ∀ n, 2013 ≤ n → n < 2263 → good n :=
  checkRows_sound 2013 rows2013Data 250 rows2013Checked

private def rows2263Data : ℕ := 0x82121c3821e1c1830a20a81220c08e02084831a0868236040853234a811a0c4842a1c08206084840220085121c5850e042830e0c08112183833e0878156081872a1809a36081810230185160c38912281830a2c782462808c020818c0a243811e6158902384860a0c3812a64083021c1860a192852a1c28e020428d0e387820a0468f0e05f83260878d0a102830e0828c0208685224c0921e144841608a8a0624586560458d0e38381120c283021c584020c1820624083023858a0a086872e3c3821214186762c48406046880e045840224c8b2a106830e04581

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows2263Checked : checkRows 2263 rows2263Data 250 = true := by decide +kernel

private theorem rows2263 : ∀ n, 2263 ≤ n → n < 2513 → good n :=
  checkRows_sound 2263 rows2263Data 250 rows2263Checked

private def rows2513Data : ℕ := 0x4835e2049d06706820e21f83221438e3604f88063858102083851e0408e0e28584020c082160c5821a042841a204811e0ce83021c1861a38c811218282062858116181812204386061c18a0e0808e061cf88120828c020ca8212043833e1cd8902300842a049865a0828f021478e2e0c394062848122140840618e854a041860e606853610689021048116201825e30085064488c2e18085060c8891a142832e0c387060488b2a084815e081871e040832a0488102186852a1898f06141831a140812218b83020858d0a2c1844610298022c5955e183840624086

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows2513Checked : checkRows 2513 rows2513Data 250 = true := by decide +kernel

private theorem rows2513 : ∀ n, 2513 ≤ n → n < 2763 → good n :=
  checkRows_sound 2513 rows2513Data 250 rows2513Checked

private def rows2763Data : ℕ := 0x9226141a53e24a821e0d58602041860e08c8e164838212104815220384061c6830644486021898106248881e148830218088060c3820e047841a300850a5458306041a41614985121038202216810a0868a062888e120828c1a089812a24f910e14a810a38681164c0823e281860218087220c5822a10183020c08116042883604a810a241851e406881210d840214687221d5860204184222c493061d2831204b838244d851e4948c06102811a14690161c38b0e4c4830e3c9871210582022c289020c0820a342832a084840a241930a1008536082841a08a97

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows2763Checked : checkRows 2763 rows2763Data 250 = true := by decide +kernel

private theorem rows2763 : ∀ n, 2763 ≤ n → n < 3013 → good n :=
  checkRows_sound 2763 rows2763Data 250 rows2763Checked

private def rows3013Data : ℕ := 0xf87060c59d02048890218a821e286882604b840e1418a0a042830e381842e0c68d161008206141870a240810a1cfa70e1c18126209813a0c086021c4843a0c98a0a3cc8226281931618485460458212054830e0c3870a1c6891a3858322080843a4858506081810214190160c088023448416843810a6c383261cd860e083842a049862a6858902389820a10083025c88326080852a283881a0878c0e1838e520c6820e10d830a380871254b86361058f1a18182121c0820604d811a08690061c08b02204830e241823a0438902105811a189812240c85061c183

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows3013Checked : checkRows 3013 rows3013Data 250 = true := by decide +kernel

private theorem rows3013 : ∀ n, 3013 ≤ n → n < 3263 → good n :=
  checkRows_sound 3013 rows3013Data 250 rows3013Checked

private def rows3263Data : ℕ := 0x18152684840a1cc8c021c18a1a0c3841e040863e1028d02604811610083061448c0238981221c59d56048890e540810a306830610d8402144840a040832610a810214f901230395121ca8416380881e18083021c1930e0c6852a0c082024c58f220cd810a1c08206087831618187064038902048870e143882e1cf820640483620c3842a10b830e0819c0e0818d121c586021c1840a20081061888e26082812220982120ce91061c4871a0c4810a10586061c48a0e089810a1c38c020418c2e1448e720428e261048302783850a1c59142281813a0c18d1e0c282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows3263Checked : checkRows 3263 rows3263Data 250 = true := by decide +kernel

private theorem rows3263 : ∀ n, 3263 ≤ n → n < 3513 → good n :=
  checkRows_sound 3263 rows3263Data 250 rows3263Checked

private def rows3513Data : ℕ := 0x2920e141890e0ca82060c6880e044810a1808d12100865a08181320c387060c59d1a217812220a881e0c08502348860e243875224283062c28d0a0c481223c583021c183822cd932a1c3820e0888602443881e182821a0878a0e0818412045850e085840e0c08d466c58602041840a204911e2408332045960a086873a282833e2cb8f023c3812204b82021418c0e089881204f891220e8c02144870654389261118152540841e10b830608293020808d1218088060418446080822a1c38b02041810e609871e04882121ce8726143820611a821a401860238687

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows3513Checked : checkRows 3513 rows3513Data 250 = true := by decide +kernel

private theorem rows3513 : ∀ n, 3513 ≤ n → n < 3763 → good n :=
  checkRows_sound 3513 rows3513Data 250 rows3513Checked

private def rows3763Data : ℕ := 0x384060d28b12084811a2098112040971238e86026c3810a303830e141830a18087420c385360818c020c7840a0c88306105815208c8a2e406830e081870e240871e0cb886e341841a080881e4c3951e041812e08181123c3890e1c2870230382065808b0e344842e080852a042880204187021808d12342832a051831a44a8512102980e08d8c320808d12345823614a811608081760c0864a042810e0d3842e049820e1c29b26381820a10c911a14186160868e067c88902117861618381160c38306111840208184163cb850620dab0e0c082161c38f261c181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows3763Checked : checkRows 3763 rows3763Data 250 = true := by decide +kernel

private theorem rows3763 : ∀ n, 3763 ≤ n → n < 4013 → good n :=
  checkRows_sound 3763 rows3763Data 250 rows3763Checked

private def rows4013Data : ℕ := 0xa8602480870a186830e08a830a0808e3a1068526041810230685121898b0638a811a2078206180910e2c787223c682160c6860214b86020c9814e100830e084832e0908106103850e0428a020c9840a1c38206107831a241853a04083062018702086904e18bb806041812620381062458b421018c1a08687120c682026828d0a184907e045860208583022048506103851a0908a0e2c0871e0c29532044a20e0879912046852a40181022c682162808e1a148810e30c820a0c38c025909f1a093962a1828c0668a86020c18122400880e087862e0808e0a9c385

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows4013Checked : checkRows 4013 rows4013Data 250 = true := by decide +kernel

private theorem rows4013 : ∀ n, 4013 ≤ n → n < 4263 → good n :=
  checkRows_sound 4013 rows4013Data 250 rows4013Checked

private def rows4263Data : ℕ := 0x852a2058162203854e186854a147871a2018a061d48306447830a2cf87220c382022d08d4a2c087060c6820e10a8a220c1843a1c2853e045810e18085060c382021c2900a080812a543831e0478d0a08a81661028e0e4c786021818136046830e3448a0a2c081361c6820228a9b024438b0a049831a1c4810a1878712180850e20287022408512103883204a812225384420e08b1e044830a2c9841e3468512107811a181870a114821a1caa202180881204f821204189225038e0a2868e32387810e0808a1204c851a10d8c0e0c082065429506042871a25282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows4263Checked : checkRows 4263 rows4263Data 250 = true := by decide +kernel

private theorem rows4263 : ∀ n, 4263 ≤ n → n < 4513 → good n :=
  checkRows_sound 4263 rows4263Data 250 rows4263Checked

private def rows4513Data : ℕ := 0x7a91618b820e10483021408a3a240880e088872e1818e160c08e02288840a14c8106180852608b870a090813a0c8850214aa42214a84220558c023878326081881254f820e041870e1838d060cb8f3e2ca890a14a8d2a240861204a871a08082060c5883238d891a083812a243910e38281260c18812040820e68484023018e0a1058206444830a18981521c2827e0819f32187820a0d4890e20a811a2408e5e18885060418c0e2ca87061c2890620a811a240818a0cc8512044862e2cf842a349850214481020d28406046830e141830e2c488120c5890208193

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows4513Checked : checkRows 4513 rows4513Data 250 = true := by decide +kernel

private theorem rows4513 : ∀ n, 4513 ≤ n → n < 4763 → good n :=
  checkRows_sound 4513 rows4513Data 250 rows4513Checked

private def rows4763Data : ℕ := 0xb811a08382721808c3e2c4842e0ed873640586060a88a2638085120438f1a06283023878d120c2832a04b8c260d5841e105832604d890e0818a224828b02044920e2c397360cc850e08e860e08a823a0c6850e282810a2108206585860208a840e246812a04289124ca900218781121828e2604b8f020c4872a1088606102844a240821e2858206148870a14382360c08c0e0418c0e4439a124038206284841631884061038b02081870e380930a0518e3604183463008106183830e047840e380843a102851a7c584020c68a220c2888604481160878d360c383

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows4763Checked : checkRows 4763 rows4763Data 250 = true := by decide +kernel

private theorem rows4763 : ∀ n, 4763 ≤ n → n < 5013 → good n :=
  checkRows_sound 4763 rows4763Data 250 rows4763Checked

private def rows5013Data : ℕ := 0x28206113810a180872a0408506041841a0809706105882604b8a0a146811e6cb8c0210181620cc851e10985021058132383821624683021448a1624687463da8b1209787220c08822043823e085860e0ca842e1009a0e04a8c022038e120c386121c48326147820630b8302085810a209822a043830e10b873e14387063008802081870e081915e0c38e1234283161808806046950e40a8302240840a048833e211870e08782224c98206150815e48d822a34c8c021018d220c384160c2980214484021568a9610b850614b830e200870a243883604186320c381

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows5013Checked : checkRows 5013 rows5013Data 250 = true := by decide +kernel

private theorem rows5013 : ∀ n, 5013 ≤ n → n < 5263 → good n :=
  checkRows_sound 5013 rows5013Data 250 rows5013Checked

private def rows5263Data : ℕ := 0x3822a18e850e34289020c3910a10388061c1842e080852e043820e1488a2e14784161c8880e14a89220938a12340860e10a960208182160c0821e2029e0a243882a0d88656044830e48a821230e830614589166c18442243850208193021848706048821208d830e60a81220c983260848122181870a1cc860608d920e0c0872a6059b0670a811a2008806280831208b8a262498516054832a1c481160c18b0610682064088c320848a2a585821a681870e1838212043881a08d84221478d12042881a442870218082220de8f1e041950a14c852a1c086021c88a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows5263Checked : checkRows 5263 rows5263Data 250 = true := by decide +kernel

private theorem rows5263 : ∀ n, 5263 ≤ n → n < 5513 → good n :=
  checkRows_sound 5263 rows5263Data 250 rows5263Checked

private def rows5513Data : ℕ := 0x783020c3993a04088062ac814a0cf87461838b360418a0e483842224383022018d2220d8712048910238b860a181840a103884208184620848106043850214889460c984060c6821a085830a3819946052860e64184021438d6618586064c88a22140881e54b8302044810e0c18536342850615090023899d06100832a087830e21e8506043853208e8602180842e351983e04586222418e2e1128c1a58184160c1871655588020418416146881e1c08342201931a08181120c08306382840a306821604e860e405950e240882a0438e0e041893e0c4810a05183

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows5513Checked : checkRows 5513 rows5513Data 250 = true := by decide +kernel

private theorem rows5513 : ∀ n, 5513 ≤ n → n < 5763 → good n :=
  checkRows_sound 5513 rows5513Data 250 rows5513Checked

private def rows5763Data : ℕ := 0xe853e28281024419c0a32d8226084830218f88221cc880e04a86160c08d1e0c8883214b89020838416342830e214841a20f931e1c086061c4843e20381061cf8e0e0448c0a20988123d1860e1028d1668182364c38b02087840e18081120e68b0e08d87561498106349890e11989220c1870a348883e042870e48087121c08b02381830a086822218c83260448f2644a88160c8853e7c48116209812a1c69a72287833219585122888502047871630c844e1c6822a04e8622093851e106862a048843a50190061028232057810e08681361888b0e5c281220c188

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows5763Checked : checkRows 5763 rows5763Data 250 = true := by decide +kernel

private theorem rows5763 : ∀ n, 5763 ≤ n → n < 6013 → good n :=
  checkRows_sound 5763 rows5763Data 250 rows5763Checked

private def rows6013Data : ℕ := 0x1871210285120948c0208f852e1028e1e1c2921614084061c383020848f0a2c98e1e055890210581520c1882a9469a020818d4618481221c2921234d8316493880629188261048c3e1408b0a1808f4a0458c1a08393120c988065018116087841e25d850e1c1860e0c3827e2808e122c4841a14681064cb82363858a3a2408a4604282022018d022c4872e049912a14481020838b2a046a32a29387460a282060c0891a1c28a0a15282064008302202871a201841618689021048602389822a045850e407834a480930a49485122c189021498212043830604484

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows6013Checked : checkRows 6013 rows6013Data 250 = true := by decide +kernel

private theorem rows6013 : ∀ n, 6013 ≤ n → n < 6263 → good n :=
  checkRows_sound 6013 rows6013Data 250 rows6013Checked

private def rows6263Data : ℕ := 0x2811a2068a0630585068c1860218087060c2890208d863e0c781360c8881a1518d0a0878d3a249832a2c2813208082161c0861a3448126300813a1858e02041870a081811e10e86121c4810a18487060458f0214183268048e420468b4a082833a19382060518e0e08d8302144871e11a857e1018102301902e1808812041840a2408d0628f8c0e105811a2ca816a0438212884870214987061e9881a085831620681060438212414890e14c84121c38e361078102180940a1068e06082931a0818d120c292025818a3e08682222438b56041831a0c6851e30395

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows6263Checked : checkRows 6263 rows6263Data 250 = true := by decide +kernel

private theorem rows6263 : ∀ n, 6263 ≤ n → n < 6513 → good n :=
  checkRows_sound 6263 rows6263Data 250 rows6263Checked

private def rows6513Data : ℕ := 0x83062858f0e0c18d123408206208840a08681060c8831e04e8c0e20d88660c0822a285810220187224c6821e1c4830a3c69a12043822a0818a320d0810a3c39106084861a08084421d2832a08d842e080904e357821a382831a08d820a180834a1c58622206811e186893e104811a0c3811640b82024418332804882e242850e04886163838416282833604483021449112100851a05a8f0e1868e221898202708810e2c084220c08502102870a0c18216246822a342810215082221c3821e14a8c021808d220c39a0e148831638384121918806387863e24784

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows6513Checked : checkRows 6513 rows6513Data 250 = true := by decide +kernel

private theorem rows6513 : ∀ n, 6513 ≤ n → n < 6763 → good n :=
  checkRows_sound 6513 rows6513Data 250 rows6513Checked

private def rows6763Data : ℕ := 0x6842a103831a1c1830a244850a2488b026818c22140810a343830e085835614a841e10285060419e3a0c087161d78b1e041810a207852a4c39b12042866220682126c386061428452183820a586830214a830208081361038b02081950244a881e6c3830e104840a0c1852a0528306041813218d8216300ca3e4ca8326383850a243867e2c48326446961e342832a505860a204812248b83021c886025418e06114921e207870e0d58406049885a045813a4408e2e18e853610a81562068d2e1c0823e0488716307820a78e83261cb816e206844e48086064c489

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows6763Checked : checkRows 6763 rows6763Data 250 = true := by decide +kernel

private theorem rows6763 : ∀ n, 6763 ≤ n → n < 7013 → good n :=
  checkRows_sound 6763 rows6763Data 250 rows6763Checked

private def rows7013Data : ℕ := 0xd930e743851e3008206141890e153910a0c3860e0418d0a2d88e2a0c083062848d026c4812230e830e08583562d38a2e0c892020878602183812e1888b1a05a841a2538716040880e1c1891630691220c5921a20d811a14781061c08312082810a0cf841210f8902107865214982161c3821a1c4937a181880604c851a04d930244981060488826044830e1438a164858c12201840230d871e10c8b021ca811a243825e0c88c4a084831a0ca974610291021cb8f0a183900649485021c4872e1868d061c6820e042890e0ca940a046b93e144833a083a05e04083

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows7013Checked : checkRows 7013 rows7013Data 250 = true := by decide +kernel

private theorem rows7013 : ∀ n, 7013 ≤ n → n < 7263 → good n :=
  checkRows_sound 7013 rows7013Data 250 rows7013Checked

private def rows7263Data : ℕ := 0x38202141840208081061c3821e108873a5448e12348820e091811a0808a12245883e082872e24082461c28206044982614c910a1d28b0e053833e0c3871e10694061478616303814e1c08502381860a3818512242880e081830e3838d220d1820608483020cc841e04683060518f1a0c782064c98b12381873e09982720c58b021028a0e2418112040835a1c4863e2018b06040891e144870e207812e3c2851a2018d320cc991e0c38236085810a24084423c2830611f8c0220182063408232156891a243810a1838e122c1862208a81123c0864a14486160c187

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows7263Checked : checkRows 7263 rows7263Data 250 = true := by decide +kernel

private theorem rows7263 : ∀ n, 7263 ≤ n → n < 7513 → good n :=
  checkRows_sound 7263 rows7263Data 250 rows7263Checked

private def rows7513Data : ℕ := 0x82221c58f12041810a20481061c0831e1c1861a44381162428e1e11f810a1448b06312910e1c4830e08f8a2a1058502090870e180811218f892604b90220c3870a112913e1c5870e18087061828b1a041841a3cd84060c08512082872208c81160c3951e144861614d880658b861e8818c32209880a0d18812417870215094061c2882608a920a140870a109860639d840e0c6901634e86061c4a41a204812a248910e341810e2068266243970610289160c69c0a2438b5638a840224088123c28b0228a83220c48e223c3890e04b810e0e4933a34586060419c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows7513Checked : checkRows 7513 rows7513Data 250 = true := by decide +kernel

private theorem rows7513 : ∀ n, 7513 ≤ n → n < 7763 → good n :=
  checkRows_sound 7513 rows7513Data 250 rows7513Checked

private def rows7763Data : ℕ := 0xa8a1674188421c5880e0418a2e447825a0c2822a40b810a1809316105861a04592022008212100881a1c4a51a08a880a1cb8b3208481220868812114954a10a8116203880a04c82024478602249812e109822a4429b3a14c8b120488e1a1c484020d2843a340910e0828102306a5126c0921a141832208790060c086021048a5e5c388160408c02285891a0c381521008c020848c160848a0a2828b0e281890e0c788164c8820e1458c3a081840a0458c1a08a8c6a0838706343821a144840e38082062408602081830e201a0a618289323478402304875a30682

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows7763Checked : checkRows 7763 rows7763Data 250 = true := by decide +kernel

private theorem rows7763 : ∀ n, 7763 ≤ n → n < 8013 → good n :=
  checkRows_sound 7763 rows7763Data 250 rows7763Checked

private def rows8013Data : ℕ := 0x982022028a462068d2a1cf830208293220c98516180890e1029202181842a04c821a34186560808552111850e04889221478466042830e04584023048516248884a0818c0e0cd82060c9823204187162e781461858b1e084830e7438512180824a153811a20487060438372084860e1878106058891a082836a0d884060468326045833a083930a0468e1a1cd960e18782065408832362810a14381060c38302053870e38a8116046831210e814a38981061c08606388830224085065898e1e048863e0c7811e1c2911a08a83020c49a0a109881a38881160c782

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows8013Checked : checkRows 8013 rows8013Data 250 = true := by decide +kernel

private theorem rows8013 : ∀ n, 8013 ≤ n → n < 8263 → good n :=
  checkRows_sound 8013 rows8013Data 250 rows8013Checked

private def rows8263Data : ℕ := 0x1081120c2850e0819b02183883a051912a0878a3a08a873a04e863605781160c09a0610589021c1950a080821e0c38312102832225e882e6c3820e1118f223108a161c0881a145860e1898a0a0c8824e10d890e1a182060d28b1a053831a303850a048851211190023018a2e3008602042840e0808b3631183022018a0e2c1812a249820e344860a44f84061068326401870e381880a0c68c1a14a8d3a0c784163c68e0e04481020958d161008c0e1d3899e087821670e8e3e048831a20488361858b5604d831a2438212280823e1ca952e0c98222040910608887

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows8263Checked : checkRows 8263 rows8263Data 250 = true := by decide +kernel

private theorem rows8263 : ∀ n, 8263 ≤ n → n < 8513 → good n :=
  checkRows_sound 8263 rows8263Data 250 rows8263Checked

private def rows8513Data : ℕ := 0x481160808136300852a1058176081816a10082121448f163838206063820208ea70e20781420429e022078322149821218289260448a5e0cf870a10e880620881160818d2a10094062819e268408a060c08c0e088810a20a853a054850634489020c6882a040831e1c1920e5018a0a0c2823611783020c0813634282061c7893e0c1870a546865a20884020808a2a1d7881234284222438b2a1838c0e082835220c852a0c6821e444810a5038116043830244b870a80481121058c321018d023008172302834e5cd830e09c856a1c09512041841a08085460d282

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows8513Checked : checkRows 8513 rows8513Data 250 = true := by decide +kernel

private theorem rows8513 : ∀ n, 8513 ≤ n → n < 8763 → good n :=
  checkRows_sound 8513 rows8513Data 250 rows8513Checked

private def rows8763Data : ℕ := 0x38b0e04a83160c08106043823604a93560808e42042863e09193020818d1210986120418322083841e340834e08483262c9811e24f8c1210781020cf81061c3831a341860e2cf812205888022c2830e0c982061838b0610a811a307840a1868f06045873218782061828236201811668085420c58e32205860e209972e0c28206685840a0c38a2a1c3830614b843a2018e220c385123578c161808d061c8823614481023078412109860e1c289021878a16100823e4c1810a206820a1cb860e38b931a20a82660c689061c48f0214681361068362281832608781

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows8763Checked : checkRows 8763 rows8763Data 250 = true := by decide +kernel

private theorem rows8763 : ∀ n, 8763 ≤ n → n < 9013 → good n :=
  checkRows_sound 8763 rows8763Data 250 rows8763Checked

private def rows9013Data : ℕ := 0x8d2a0cb8502104981a2018182186822a10a813e143843625185021c1840e0869a7e3cf820e04183622d28b064de8e2a099810a1848712049857a091840208a8a4e482a002204812620081061c8830208d8f26241812e24386021c7810a0d89d52495880e28587022cf8a120c6970e0418a0e44a8212048880608e8a3a0c0840a040950e0888f0244093120c286024c4830e2e78a2a24e831204b87222d0841210289ae4ce8102143814610c88021538402087850a548851a06b86221879c0a048831a1479802080840a046880e0829c2e14785060d7891a58187

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows9013Checked : checkRows 9013 rows9013Data 250 = true := by decide +kernel

private theorem rows9013 : ∀ n, 9013 ≤ n → n < 9263 → good n :=
  checkRows_sound 9013 rows9013Data 250 rows9013Checked

private def rows9263Data : ℕ := 0x7834a0c78d0a04f832a119830e3008d42886837a101841620687061178906157960e54a91421838502084810e2068716109820e38486165098206a80821a0858332086b10a1d185121018a0e2c38e1e0cb8b0639f830a0848516109882a04289023c08a220d2821a8c48422204991e18392261cd830a0818e125838c063448126186814e04b88021c48d26480871210c820e04786165438eba18982261478a7650a8a0a1c08f1a04a813a08da21e103860204a811a0838a364d58b12082831a0819c2a042852a2c4875218d823648b860614a835e209880a0c289

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows9263Checked : checkRows 9263 rows9263Data 250 = true := by decide +kernel

private theorem rows9263 : ∀ n, 9263 ≤ n → n < 9513 → good n :=
  checkRows_sound 9263 rows9263Data 250 rows9263Checked

private def rows9513Data : ℕ := 0x59b0e204810e24388360408602142890214488524ce831ebc1870a244850a485890204d8702543820a1db820e1dc8426080841e04b85622c28f0218187121c08f26051810e08381360c38c1e204810e79084360c68332102811a30381060408636166830208087063d18b0e0888c3a2c4900a1c3830e04b8346084851210b8c121c8810214382460c0894238b811a206811e2488612205830e093971e10091022c5810220d902a054850e1488c46500810624682020a28a2e5048b06182821a404810e152841218086064018f164438d120c0864e141810e91590

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows9513Checked : checkRows 9513 rows9513Data 250 = true := by decide +kernel

private theorem rows9513 : ∀ n, 9513 ≤ n → n < 9763 → good n :=
  checkRows_sound 9513 rows9513Data 250 rows9513Checked

private def rows9763Data : ℕ := 0x8b22054832a105891a1808a0a046833e0859902095851e302821a44d833208088061808b26087811a20681720498202385845650681223008b0e0878d0e1818d2e0c28212147862e1438e22042880610d811a0c78b820548cba041931608382061c08f0228b830a08782060c58302342811a81888120c08c4e68287160c9811604582023818a165479a0a3da851a041890218381060c38b3e091830a0838e7204288067418c1a14185060c3824244a89162cd90224c0831204b830e2018e1218f83021ca84860d08b0a04b820614486461818806046923645198

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows9763Checked : checkRows 9763 rows9763Data 250 = true := by decide +kernel

private theorem rows9763 : ∀ n, 9763 ≤ n → n < 10013 → good n :=
  checkRows_sound 9763 rows9763Data 250 rows9763Checked

private def rows10013Data : ℕ := 0x1861a08d8816242820228b920a544811604382021c1832e08185122498e0e04890020c3942218b8236104810e4418b46040831a04189020c185220c589061d0840a203900a18e830e207870a203841e34f851e1d0842e3cd816a04682063818a026c18d220c28c0e2c1860e14382060d1833e5c5810e140870a040830e5c581162c98a823408902288840a09385361cba02a2c2811a0818212048833e14a861a30484061039a42141930a3c681064028b02101871644494060dd88321cb830a24193123c5850607a870e1408722105863220284262d388060c38b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows10013Checked : checkRows 10013 rows10013Data 250 = true := by decide +kernel

private theorem rows10013 : ∀ n, 10013 ≤ n → n < 10263 → good n :=
  checkRows_sound 10013 rows10013Data 250 rows10013Checked

private def rows10263Data : ℕ := 0x8980e044830a192841234e851a04284022c0826a0cc821a34b810e800930a18e91021c1861a093811240f943e10e841a38f8806305921a0858302180880a249820204e830e1808212052822a38b841a241848e240a60608d844a0d08a060c588027088122147845e3488b12044860a08384120c3861e2878d161438b360458f06444930e086812a1c2a71e11798163898206702830e10d861a0c1842a042852a28d8f46180851e600824e041810a2008d2a0c0831e041810e08f811e30886061c787020c18216705890e088860a1848d0a042852a08a86026c082

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows10263Checked : checkRows 10263 rows10263Data 250 = true := by decide +kernel

private theorem rows10263 : ∀ n, 10263 ≤ n → n < 10513 → good n :=
  checkRows_sound 10263 rows10263Data 250 rows10263Checked

private def rows10513Data : ℕ := 0x19316115830288481260c38106103830e29693260808a060c285360418c3a39082220c28e0605c811a25594161859812041901a1839a120c08b06044810e2048b221858c2a342814a0cd9312264850234b892e0c1900a4d888060848a3a901811224585120428916383813a348831a1ca8402601843a4029506051816a44382061c38f1220d960e3008406288862a1078d0a249872e0c0890e1078d021419c4e3c38c065ca870a18d870a103821220d890e689820a051880e05f83020818b120458e06042a11a08a85221928b1a34884221598d0618085265c886

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows10513Checked : checkRows 10513 rows10513Data 250 = true := by decide +kernel

private theorem rows10513 : ∀ n, 10513 ≤ n → n < 10763 → good n :=
  checkRows_sound 10513 rows10513Data 250 rows10513Checked

private def rows10763Data : ℕ := 0x139002381840a109831208d8102200871e0c092563428416540815a0c5831e050830a0c3822e0c0834e1028702141870a32086021ce84262c09406048880e1418c46300810a0c288261cd840e0879a1204f8512641811a0809f120da8b1e348870e215852a1c086021c4951a381822a34f91024ca901614a810a1038302088861618688222888b2a087870e2c98106042882620b833a0929f1e24091121058f520c08a1e0c08e0214b897a080973a183854a0418d260c3824e046850e1c2811a38181160458306401830224693460c3820e0888c020d281061898b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows10763Checked : checkRows 10763 rows10763Data 250 = true := by decide +kernel

private theorem rows10763 : ∀ n, 10763 ≤ n → n < 11013 → good n :=
  checkRows_sound 10763 rows10763Data 250 rows10763Checked

private def rows11013Data : ℕ := 0x38606351812e181842a24b86420848302541852a5488556063861618a826a306823658d81020cc87160409b0e293890214182060c989021489516086822a1c885021028c0e0c18b2a046850e1ca81023068b0a046820e08b840e48f88065828e1a1148a16495820a0d48936047891a384841e340830e648934a20085223039712042810a0838a06183832604b8f2e7438e2a042852a28e840a0c1902a103820e1c49502484930a0c6891214d83322c7813a542915a105863a0838712185830e38189020c69022105863e281810a08481221c08602353812e48982

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows11013Checked : checkRows 11013 rows11013Data 250 = true := by decide +kernel

private theorem rows11013 : ∀ n, 11013 ≤ n → n < 11263 → good n :=
  checkRows_sound 11013 rows11013Data 250 rows11013Checked

private def rows11263Data : ℕ := 0x842a3528c2608284161408e120c588324d1951a15b84360c885262c48626241963a043824e1c281022018b6a1c58f0235a860a20781061028c5610893022c48112709830608a8602241854e0428e1a113891a08090121d186021c1833e24082060c58c1e101860e08a873a308914a10e89160c9840640082260969216800850a48582020888a4a0c38e06309822608b960e0c08a3a552880604184462078e221c286020418f26206850a2888326201832e0838b1604082322ce960a0d690161c58c0e28b8632215813664f8c0e04a890e30482163c3822a05484

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows11263Checked : checkRows 11263 rows11263Data 250 = true := by decide +kernel

private theorem rows11263 : ∀ n, 11263 ≤ n → n < 11513 → good n :=
  checkRows_sound 11263 rows11263Data 250 rows11263Checked

private def rows11513Data : ℕ := 0x2811a20d815a4cb830e28883562c98e12283922a0479b1648c8d062898e1a1cd810e0958712100863e04d87160c190164c0821e144811614682060c08e021058626098812a10697067c4810a0ca82161058b024078c0a78687220c282022c1831614087061c88b0e04a817a087851e4028c2a088870208aa222180861a28d9032380842a0c0941e1029f2e54381160c2834a1c7867a0c1822a58b8206147980e080880a045883209c87025008d2e048890610489020cc840a2408f3e05f870208082720c389261c18a522d38a0a1c38302042814a381871210283

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows11513Checked : checkRows 11513 rows11513Data 250 = true := by decide +kernel

private theorem rows11513 : ∀ n, 11513 ≤ n → n < 11763 → good n :=
  checkRows_sound 11513 rows11513Data 250 rows11513Checked

private def rows11763Data : ℕ := 0xc8f06705810e1898d061838f2620a870a306885e0c08502204872654385722808606387874a0d8960a3058206085863a0868106108883604287760c384120c6912a14481021848416100851a2018102083871e105a76e8c2811614385421c38332063860a08382160429a0610e89160c4960a040820e1c5842608d8106049821e041860e189823634f821a4cd8c026878a2a1808c0e10a812e0c6901e28586121d0870a24a8506180830e502810e0c3876a0d5823e342811a184882a04b82067c19502081850605a880e04d860214a884e1c9832a4c4810e1808b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows11763Checked : checkRows 11763 rows11763Data 250 = true := by decide +kernel

private theorem rows11763 : ∀ n, 11763 ≤ n → n < 12013 → good n :=
  checkRows_sound 11763 rows11763Data 250 rows11763Checked

private def rows12013Data : ℕ := 0xf8416103831e34484025f0870a0c3821a1488a0e3008d063038f0e05389020d59c1e1ce85061d0991a2098d12317890604a810e1408406183832670b8d4a54987a228091123848f1620a810a100830e0848716380872a0c58e0208d8d3a0c38e0a3c8883e0878602503852e102881204887020c1824e1098802a02890e15b82066c08502204830a0838116588820e10e992244f82163c391020818402189852a0c98802401890e0d88e1204688062058f0e45285461869d06117902e3ca91120c389361418f0e08388221c09112041871a443822e04083121c586

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows12013Checked : checkRows 12013 rows12013Data 250 = true := by decide +kernel

private theorem rows12013 : ∀ n, 12013 ≤ n → n < 12263 → good n :=
  checkRows_sound 12013 rows12013Data 250 rows12013Checked

private def rows12263Data : ℕ := 0x19516181851210c82022ab830a24a90361c59556042812e44690122488e0e14795023818a0604c831a08193022008a460c5892a2c787021598206186921a1da81260809a1e1828e3e1dd921a180872e0c9864e142839a08688061cb861e2018126086822a28e8302147843a446820a1058302404870a1808d120c3a112141890e2c7820a043833e1048d620c18d12885830e051842e08082160c3821a1c2871a303850618b981e404951a2418212100860e10784160c98816485821e445860248485121069e0e08289760c48706043821a14784020c7872a04285

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows12263Checked : checkRows 12263 rows12263Data 250 = true := by decide +kernel

private theorem rows12263 : ∀ n, 12263 ≤ n → n < 12513 → good n :=
  checkRows_sound 12263 rows12263Data 250 rows12263Checked

private def rows12513Data : ℕ := 0x11880e1418a0e180812a1dd820250193160c9810630b8b0e20484021448a0a0488c0e105810e0c3821e0c38f02148845e080827e28383562c8810a201841e248830610e86020c18a224c3820608884265468e060438212208860e18088160cb823e14d89020ca8712100884a0419c16186904e0cb9d12141831a5c6902218086021028d222c18512283ac1234b84024528b2a0468206381830e2498d2a04c820e141862e303a006183820620a84260848b1218085061cd903a08f82122808642048833e207850a0d1830e041831a2c3812a182834a147a7520c181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows12513Checked : checkRows 12513 rows12513Data 250 = true := by decide +kernel

private theorem rows12513 : ∀ n, 12513 ≤ n → n < 12763 → good n :=
  checkRows_sound 12513 rows12513Data 250 rows12513Checked

private def rows12763Data : ℕ := 0x38d061828e02202831a24a82360c08c12101861a0c6814e246820e1c489160c98116043830e345832608f9c460cf820e04d832e3098216048827a085890e095871e409831a741870e186824e1c28e0604b830e1409722183980238b98220c19d2e10885024c286561898416040890e081860e3d2810a0c69212402950e144841e0c3822a14b833a0ca870a04b862605f89860cfb44e1958926142870a08c853624b9502044860a098886a1838c1e1048f2619b8216240831a348830e09093060cc853610289024899636046830e10a830a2408a16242832a20187

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows12763Checked : checkRows 12763 rows12763Data 250 = true := by decide +kernel

private theorem rows12763 : ∀ n, 12763 ≤ n → n < 13013 → good n :=
  checkRows_sound 12763 rows12763Data 250 rows12763Checked

private def rows13013Data : ℕ := 0x48c1618087221038932150863a44082061c29e1a047862218384121c09106597840e0c3854e0c5821a04b8322200820628b95022c183523ca842a402820e113891a0cf820a1c382061c1831618088420c589022818d0238382220518806084843e78a852a106831a0458c163d88a3a0cb86062088746084903a18e8b421018f2e20f812a0c0820e2d3870a141902a30085021ca8602180882e0468b1e142891630087120d29d06044890a081842a2498f061d095620c785061d58206044811a144842a1c5834e081810a48a85460d48e32102811a0c1840a10c85

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows13013Checked : checkRows 13013 rows13013Data 250 = true := by decide +kernel

private theorem rows13013 : ∀ n, 13013 ≤ n → n < 13263 → good n :=
  checkRows_sound 13013 rows13013Data 250 rows13013Checked

private def rows13263Data : ℕ := 0x98206281840a203812a240862634b980e20184360c0831e350860a14d840a0458802344830208191360c9850204d870e14781160c388ae5d18a0a2418b7e105860e2ca813208085062828242381901a30a8a220c0a00e104814a0c98412489851e1dc81aa31e82220468362281860e486875e10389022c7832e1408436289834e08a8d1a180842e0489506281870e08982161838e26219810e14688220c08c02504987624981520c0830234b811618381761c68c0e381840e3c0812a042820e2018a16144813660b83261c4903e08091121c28306085810e30987

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows13263Checked : checkRows 13263 rows13263Data 250 = true := by decide +kernel

private theorem rows13263 : ∀ n, 13263 ≤ n → n < 13513 → good n :=
  checkRows_sound 13263 rows13263Data 250 rows13263Checked

private def rows13513Data : ℕ := 0x188120c589660488c0e49c90063099206105830224a840a106831a041810e08187161038912284830e48082060c58c26107812209084123068c06460860a381841604586021c7934a80c9a06103880e2c88c922c482121c3974e4048302383850a40b940e101843a0c6822e1829502214812224384221cc8b1e1c487220c18e1e180821244584260c48e4630583066998a022c08506248820e4c2832251284060c2832a04d8c4630a84121008e1a285893a2068716100861a204810a20082363438526088860a243842a3488202291840a196a3063008b0e3858c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows13513Checked : checkRows 13513 rows13513Data 250 = true := by decide +kernel

private theorem rows13513 : ∀ n, 13513 ≤ n → n < 13763 → good n :=
  checkRows_sound 13513 rows13513Data 250 rows13513Checked

private def rows13763Data : ℕ := 0x108a6a2048206183830211495763c681120498206144843244188163c0850e5c4a10a201817e0c3820e3419822152820a1c3893e15393020c0840a10c86061139002201930634088420419f0a080820a0c88b42042810a201812a043850210e811a2018216114831e44e872638781060c5880e0818932315840630f8e0e105811a0c3845e3d28306045903a2018722182970204a813e14693762458b120818a0e2c9843610685022848122503810604c880e684830a6c187061c5853208e860230c8b060c3830e044833e30385461098c4a101870e0ca8e169cb82

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows13763Checked : checkRows 13763 rows13763Data 250 = true := by decide +kernel

private theorem rows13763 : ∀ n, 13763 ≤ n → n < 14013 → good n :=
  checkRows_sound 13763 rows13763Data 250 rows13763Checked

private def rows14013Data : ℕ := 0x3822a10a90466808d2e18682320478c0a0c48512182831a10a843224d871e1058806041841a14088221c09162e97812609f872a0c8823e1c48f162068b0a0408c02141930e247872e04288025d4862e0c087663488306594920e0c38a1604c8f1210181460c08e1e1c3973e1c8810a540810a0c08e2a1e0930a206822e04386564c28126381a606251820e1ca831618c812a1c2820214883022c3812e3c6820604a980a0c19196706851204184161818a061118b0268d841a0838822315831e0418726081821e048830211f810220d8e06400860228b870a08085

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows14013Checked : checkRows 14013 rows14013Data 250 = true := by decide +kernel

private theorem rows14013 : ∀ n, 14013 ≤ n → n < 14263 → good n :=
  checkRows_sound 14013 rows14013Data 250 rows14013Checked

private def rows14263Data : ℕ := 0xa81222408c024018d220868212100954a1ce951a386822a1d186263418a0a204810a114822a09789220c3871e043821a1448462083842a10e850e10a84320818d2a1c089324cb8f2608388220d8830210b8d1a98a872a043860610590220c18e461158802281860224fa22e10c8902108863e1808216057833e1058402141841e042940e2c884320839f060c3824220d810e30784060c08326205873e2418112046823e1048d0a0c187362439d021c78c5e200813604c851a08d87022caa212182820e045810a447870a240850e088870208182220c0861e1c18f

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows14263Checked : checkRows 14263 rows14263Data 250 = true := by decide +kernel

private theorem rows14263 : ∀ n, 14263 ≤ n → n < 14513 → good n :=
  checkRows_sound 14263 rows14263Data 250 rows14263Checked

private def rows14513Data : ℕ := 0x187222c482126c2820614489226c78b12482860e10187020c0a21e1058602041817a2d582421c88312205831a2ca97121008c021c28d16203810a4838656141860e5c18136102850e102834a2d584060cb892a0448622303842a4888326082811a0c0821e10c8e06042875230484523458b0208e8c263c18e16103854a81a810a38188063d585023418c2e20081060438f72048830ea499622042822a14583920c49f12042851a08187321898d1e18c821204b870e383913a300831e108982e0cc871210382062c784320c187061ce86362818602081810a0c385

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows14513Checked : checkRows 14513 rows14513Data 250 = true := by decide +kernel

private theorem rows14513 : ∀ n, 14513 ≤ n → n < 14763 → good n :=
  checkRows_sound 14513 rows14513Data 250 rows14513Checked

private def rows14763Data : ℕ := 0xc830e102810a08688167b2a1021d09002303815230088061ca830a2048d06042822a101831619382063118b2a093830e0cc9312040857e28a871a200851e280860620d815e483842224c85721cd862e09e811225495062c281160c38416046820e145a10e080880a043890208289160c78116043881a114861a0818a3a3c08e0608d89020c687160c28802054891a144820a5488312045831a20681123c3834e142841a20381520438f021c587160898506103851a047a532180992e3d4820e08783260ca87121d4a40610a8c1a14191123028912042811a08481

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows14763Checked : checkRows 14763 rows14763Data 250 = true := by decide +kernel

private theorem rows14763 : ∀ n, 14763 ≤ n → n < 15013 → good n :=
  checkRows_sound 14763 rows14763Data 250 rows14763Checked

private def rows15013Data : ℕ := 0x381060c38e261138d02601851640c8306051811a08f903a10b881a201832608781460c08e260818a265c38236180822a1448426181914e103a426381860e2098a121c2820e0418722144820a1cf8906059810a140841218f8612041870e19085763008b121449f16092813a2808c12208872e2d384120408e121449216183874e1c09d0240498021879a123c5974a14287020c496360529d061cb830a51385163c083122c1811a0818e06109821a041877608782221888e0e08d8a0e3cd8b2a10383021cb89020c3825a48685021448c0e9cd81361cf850245089

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows15013Checked : checkRows 15013 rows15013Data 250 = true := by decide +kernel

private theorem rows15013 : ∀ n, 15013 ≤ n → n < 15263 → good n :=
  checkRows_sound 15013 rows15013Data 250 rows15013Checked

private def rows15263Data : ℕ := 0x2810e209841e04f8e02163810a0c987424038302147840208081220d88e0e34186166848706043952a2058d0a14084160428c0e048811a0c7871248b82361418126307820a6c0830e1c28d0e2c18166609950614a8d02201916a7008c0239c8c560808836106893204893160c38882042820608a890a543871278083120418c3a181871e309861a202810e746845e0cb831e7048f2208f844e18989021c4842e1418a5e543862a441840e200870a48685022c187863038b1e4d78226044892218f8712188850e10581021408d16282920205483a6304812a0ce92

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows15263Checked : checkRows 15263 rows15263Data 250 = true := by decide +kernel

private theorem rows15263 : ∀ n, 15263 ≤ n → n < 15513 → good n :=
  checkRows_sound 15263 rows15263Data 250 rows15263Checked

private def rows15513Data : ℕ := 0x18823e151810a601842a3468c1a1c1934608687066008b1e210870a08088061918c021c28d3e246811e0c886062ce813214f880a1c585021c1860224081122438c1e3418332309826a1c3952a20d8d0e14087121028326082890224082121808802141900a54a8422240850e0458126458841e28383021c2950220a874e100822a5c1842620685120c3881240d83223878d0a8988206114920a08f870a1068e1209387020c382160c08806351840e38681361c8832a202811a08f8b2a0488212105861a1868a161c0892608183023c69c0a042950235c8a220d982

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows15513Checked : checkRows 15513 rows15513Data 250 = true := by decide +kernel

private theorem rows15513 : ∀ n, 15513 ≤ n → n < 15763 → good n :=
  checkRows_sound 15513 rows15513Data 250 rows15513Checked

private def rows15763Data : ℕ := 0x3856604085061048416303810a04b882a285870e3c09346043822a28a86e618c810a04383061078146240871210883261c18c021498522102821a041890a386851e4cb8c12201961a241811e0c0820615f872220a8e22240821a0a0870e09e8512043821a202830218982123c9830604b9302612932a340833e102810e18087060c289121cd876a08781061c0850e044830e3838116106852a68b890254484161069b2a35183022c68a52605950e10783160c482161828b1a6848a02396874210583064418c520809012183861a141842224085061839a2a08d86

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows15763Checked : checkRows 15763 rows15763Data 250 = true := by decide +kernel

private theorem rows15763 : ∀ n, 15763 ≤ n → n < 16013 → good n :=
  checkRows_sound 15763 rows15763Data 250 rows15763Checked

private def rows16013Data : ℕ := 0x58a521408e120429506085810e0868d061cb8206581891a086820a1c0861e085812e201873a0d7834e2c286160d081060468602384873a5098142c4588360418a2e300840a1c382061c4840a0809412048913e1c1873a4478a160c28e06041872614a853a0c38c32107810e2468212043820e359860a306824624e83060818602200810a106851a047952e440884e04289060878622a818512408881a041842e3d88e221808e12041832208388460ce86025c1830a08c97163408306807811618d87063c08902087870e093870a0c382022028c0e0c7872204392

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows16013Checked : checkRows 16013 rows16013Data 250 = true := by decide +kernel

private theorem rows16013 : ∀ n, 16013 ≤ n → n < 16263 → good n :=
  checkRows_sound 16013 rows16013Data 250 rows16013Checked

private def rows16263Data : ℕ := 0x9838628484165468a0648b821a29383263c68e760c2891e0819c020c08b5a4d1955a68d81260959a2e04085262c189323c19c0610c89062829946203840a0c58e02205810a08984160c28502382860218481161c3821a28183261848106543821a04e86222c48b120c3830e10a840a08a8d161c09406085841a08087120c086021c88946686850a1858e1e04183222098512103825a28a8d1a0c18e0a10382060858716084812e106820204a860e54a87122889d421d38102080871e1088e660858f1a08787061009b0235481262c3822218e950e060870e0c181

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows16263Checked : checkRows 16263 rows16263Data 250 = true := by decide +kernel

private theorem rows16263 : ∀ n, 16263 ≤ n → n < 16513 → good n :=
  checkRows_sound 16263 rows16263Data 250 rows16263Checked

private def rows16513Data : ℕ := 0x187120468c0e04281022408a12189821e14184165cc8a0a54e860e1da832e08384120c3833e519813a0c997061cb86060858c269018712042aa0e0828702395821205e920610486024478d66185830609389021808e22840941a041873e2c4820a1cb860e2c7860a0c6853a183830e1c5862268d81062408c26144952e1908822042820234887024448212183821a10581a60c0840a1c083062c1871a3018e2e6029d1204a870a092810624b92020858c0e0cd962e040820610a901a446820a31a820e0878c022c0872a04389022018902549822e4c6833204783

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows16513Checked : checkRows 16513 rows16513Data 250 = true := by decide +kernel

private theorem rows16513 : ∀ n, 16513 ≤ n → n < 16763 → good n :=
  checkRows_sound 16513 rows16513Data 250 rows16513Checked

private def rows16763Data : ℕ := 0x48d220c9812204b880e1c58a266c088060428936107890238084160c8820e051840a14387122648f12054840e486873a0c982020418116084842a0cb8502101ad0a541902e0518e0e1518f022048206103821a085840a20787063c38c1a042860254a884e0c3880e584865e140842e0498e3605d890e2019312105921a04b811a083820618b830e04d870a7628b36403850e34284160c6840a043820208a860e2418a121c98c124c8830230096064cb8e0e087831a1928a0a3c58e36094ab0e0c387064c28806441890a24a93220cc911e0428122203881230986

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows16763Checked : checkRows 16763 rows16763Data 250 = true := by decide +kernel

private theorem rows16763 : ∀ n, 16763 ≤ n → n < 17013 → good n :=
  checkRows_sound 16763 rows16763Data 250 rows16763Checked

private def rows17013Data : ℕ := 0x5831204d8f021838546103891e34883520938b3a18c850e104aa1a2418816186823e6828f1a50181220469d024418326200872a111824a1079b1619281220c38206044811a143875e3c0a14a402810250185220c3861a060810e2c68206c45921e08e8346089844e24397124d7890219b8142405850e34186022c78a2a1c882021018a2255587221c3880e0458a62240850a0428f261d3899a1838e163428b12154920e74682060d2850e756870efc181160c682061078722618810a480820208798163818722706851a1418a0e2c0900604f8906051860208185

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows17013Checked : checkRows 17013 rows17013Data 250 = true := by decide +kernel

private theorem rows17013 : ∀ n, 17013 ≤ n → n < 17263 → good n :=
  checkRows_sound 17013 rows17013Data 250 rows17013Checked

private def rows17263Data : ℕ := 0x38e36303830234783263898d12057820e28e8ab62d881360428b061058902198870a3428c422088c020c687060ce861e042980e5c6817e255940e2c1860e246842e114910e28a8916143974624388060848c1620488422428202281860e0c38d0a1c3822a085830208a8d421cc9b1a1c284020d59a220c086561448116203823a7cf830250d860a2cc882e3438202282813e20188161c6820614483021809312048892a108863e0d581063028e0e1ce890e453850a0498e4a1d381160c097120cb86060488326306840630385120858c0e09f882e242820268281

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows17263Checked : checkRows 17263 rows17263Data 250 = true := by decide +kernel

private theorem rows17263 : ∀ n, 17263 ≤ n → n < 17513 → good n :=
  checkRows_sound 17263 rows17263Data 250 rows17263Checked

private def rows17513Data : ℕ := 0x148702081851e1828e060448416384811e4038b02101952208987123c683122938d0a3cd8206043891e085930a3848746402880e2c883160c9840604388260458f029848d0a90288060548716610870648b821a716873e0868a220c88502a41861a5498716302861210484164418416243850e14b87021868d0a543821a3578376189960a197830e05c830250c85b21008826748892e0c087166558812284830e084812a1c0860e041869e2068e3a04f9a2a10b962e0c981061d485023448c023808506246821a35490022c9820a0488232387833e4418a1234585

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows17513Checked : checkRows 17513 rows17513Data 250 = true := by decide +kernel

private theorem rows17513 : ∀ n, 17513 ≤ n → n < 17763 → good n :=
  checkRows_sound 17513 rows17513Data 250 rows17513Checked

private def rows17763Data : ℕ := 0x852a70a8c0e3808806103881a09c873a14481368468306384960a0c08a16045950e226811a181852e300820221787260838406303947e041813e2189d16194a906102840214182063da820238b830a1899f2a042890214e8a3a453810a1828e0604a811a0c0870a10583124018f2e2c38512117821e681ae0a3038222188a912342813e2c384160558202144965e203810a10686061449b02204b12a109921a041867648384360d2891a068860a0938b126ce8806208810208d822a0c2825a201811a247820619585021058c260c187162868202107950a0c182

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows17763Checked : checkRows 17763 rows17763Data 250 = true := by decide +kernel

private theorem rows17763 : ∀ n, 17763 ≤ n → n < 18013 → good n :=
  checkRows_sound 17763 rows17763Data 250 rows17763Checked

private def rows18013Data : ℕ := 0x18e0610082124c4870a084843a1c5862a107839224a881624689121458d1618384161c5881a081950a196812228f9a6e10186224988d16046830e104830a081850a185830e0828702083851e1c5820614d984624a8206251830e047835e0d0851e0408602104871a143872a1c68602385830e2418d2204f9512142a24a0c08112582892608d810238784161c09112202956a18a850628089064c4813e2038a2a2439502045813e083843a3c08c0215a8d1a384825a105860e284842624681061c38f2a1109b3e189810a186820608a811a0c485b205588921c589

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows18013Checked : checkRows 18013 rows18013Data 250 = true := by decide +kernel

private theorem rows18013 : ∀ n, 18013 ≤ n → n < 18263 → good n :=
  checkRows_sound 18013 rows18013Data 250 rows18013Checked

private def rows18263Data : ℕ := 0x487b62c08106702c82a04a86020c988160668342045810218785165929a12081810e1908a225409712042920a38a82463058b0e10b862e0c981524158506113813e50187223c6862a284830a080850a5438b0e04e870e0ca872218888622ca890208a8412045951a042890e1838d161c28212381980a1438406192860210b8f0e086881e25d853e1c4845e0c3841605a88024ca840a20991360438c12041833a143840a308831a145837614391161028606293814608191124c59b06144870a30c81360d5834234181262c1811e0409a0e1c5860214184421008c

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows18263Checked : checkRows 18263 rows18263Data 250 = true := by decide +kernel

private theorem rows18263 : ∀ n, 18263 ≤ n → n < 18513 → good n :=
  checkRows_sound 18263 rows18263Data 250 rows18263Checked

private def rows18513Data : ℕ := 0x820205990162408436252941e0878d0e0c9842a4098c022c286020c9873610c9d72287874a200870a1068532090a80e60781060cf8b060848322095851610583121c1930e24685160cb8832442810e09282221cb830e2d0831a2c6821204082327c4892e143811604c82fe14a8a026c1852a2868c36041981618396120c6830e045841a0ca841e10b9806114891a180875a0c2820604a870e5c3842a2408512345810a0818e2a243824a7ce81162018a06045825a45c830a3c0882e04f9a4e05183221408d12542880615a8402300845e1c88f06388810e08187

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows18513Checked : checkRows 18513 rows18513Data 250 = true := by decide +kernel

private theorem rows18513 : ∀ n, 18513 ≤ n → n < 18763 → good n :=
  checkRows_sound 18513 rows18513Data 250 rows18513Checked

private def rows18763Data : ℕ := 0x18112491854a11483160c384361898b0e205890e080841224c8626041811a44791229c9821214d840a08690064c3866208e835220a885204082064c7860a3c6810a486831a085834a20f8a120c5850e5c88a0e604814e0c3827e04b811a0c19916040830e3818152080854e0d7a41a4ca840e14682061c0861e105871a3c18736402831e1e38d220c69c5e480833e0818a0a252870655882021028c0e2d281121888f32094861a0818512186a1422cd810e0c990664cc8226148890a20484521c583262cd810a0c3821e11d8c021049502383811671183260878a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows18763Checked : checkRows 18763 rows18763Data 250 = true := by decide +kernel

private theorem rows18763 : ∀ n, 18763 ≤ n → n < 19013 → good n :=
  checkRows_sound 18763 rows18763Data 250 rows18763Checked

private def rows19013Data : ℕ := 0x2812614488420c08b0208b810a24681120428c061048616683812a3c5831e285ae2e08087360d892120968c020c381060468206044865e08a87822428612088816a1839a3a1da9212144830a083810a2488612344811a203823a109893210b86020c3813610686024ce830e24681121c682126418a021848216302832a1d1810208a851e048864a082873218a822e312824a581817a2048d221988632041867a20a812e10983021ca841a3818446103851a085842e5cf81120488212042833238a82060428e2604e810a08185122408c7a1c1920e18687060c0a0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows19013Checked : checkRows 19013 rows19013Data 250 = true := by decide +kernel

private theorem rows19013 : ∀ n, 19013 ≤ n → n < 19263 → good n :=
  checkRows_sound 19013 rows19013Data 250 rows19013Checked

private def rows19263Data : ℕ := 0x28f4a042863a1899416043920609a816e0ca87163c283363829602440854e1808806704830e843810a185832a0488122081818a042824a1c2876e30484462408b0214e950a55081060498c1a08886322ca821e04b832a145890e0808a2a4808342105892e083822e28e881a042871690a811e0c386121108c220c9822a186820ec4a89263e4827e300831e08e8c2624485060c58f0e09c870e0c0820a0498e0e105830e313852a1808c3604a90160c9851229e86024c2830e2c68b222858b020828d623ca874e180891e119860a0ca810a0409126085920209b9a

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows19263Checked : checkRows 19263 rows19263Data 250 = true := by decide +kernel

private theorem rows19263 : ∀ n, 19263 ≤ n → n < 19513 → good n :=
  checkRows_sound 19263 rows19263Data 250 rows19263Checked

private def rows19513Data : ℕ := 0x812a180850e20e832248a8212100825a102841a186810a414850e1448426180a95204c892a10187165409c12288823e2c5840214a852e10f8306202812e2418a06285863e204a50e140882224b860205083260c18b36880833e39c99224448706040862a281830e1928706103890e11086020c38d2e2828832047863e0c4850a1058f2a0548f2e0c7a206298861a341991a246811e1c09526108870a0c6933648e8c02107891a0c1880a31a9d3e285830e184911204c8802201870e384811e283821a0858a220838a3a0498306081841a2c085160c9920644a81

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows19513Checked : checkRows 19513 rows19513Data 250 = true := by decide +kernel

private theorem rows19513 : ∀ n, 19513 ≤ n → n < 19763 → good n :=
  checkRows_sound 19513 rows19513Data 250 rows19513Checked

private def rows19763Data : ℕ := 0x4812218f872a100830e1c1811a200852a0c0893e202891a206818e54086021c7952e2418816040891e285811a18384221c08206344860ec8c872a246827208d832e4448b1230683262cd810e5c08412055851a085875620a854e1839d1a5818f3e08690061c385120848126203812e24f836614a900a30382063038b2a38484262c081420c68f122c7834a3a89406046831a14a811a303850a554880e2c5810e1478dba1c394361ca83163a2840a35d8502082832e0c3824e0c08312107873a20384061c083064c883161818e1205188

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
private theorem rows19763Checked : checkRows 19763 rows19763Data 238 = true := by decide +kernel

private theorem rows19763 : ∀ n, 19763 ≤ n → n < 20001 → good n :=
  checkRows_sound 19763 rows19763Data 238 rows19763Checked

private theorem allRows : ∀ n, 13 ≤ n → n < 20001 → good n :=
  (joinRows (joinRows (joinRows (joinRows (joinRows (joinRows rows13 rows263) (joinRows rows513 (joinRows rows763 rows1013))) (joinRows (joinRows rows1263 rows1513) (joinRows rows1763 (joinRows rows2013 rows2263)))) (joinRows (joinRows (joinRows rows2513 rows2763) (joinRows rows3013 (joinRows rows3263 rows3513))) (joinRows (joinRows rows3763 rows4013) (joinRows rows4263 (joinRows rows4513 rows4763))))) (joinRows (joinRows (joinRows (joinRows rows5013 rows5263) (joinRows rows5513 (joinRows rows5763 rows6013))) (joinRows (joinRows rows6263 rows6513) (joinRows rows6763 (joinRows rows7013 rows7263)))) (joinRows (joinRows (joinRows rows7513 rows7763) (joinRows rows8013 (joinRows rows8263 rows8513))) (joinRows (joinRows rows8763 rows9013) (joinRows rows9263 (joinRows rows9513 rows9763)))))) (joinRows (joinRows (joinRows (joinRows (joinRows rows10013 rows10263) (joinRows rows10513 (joinRows rows10763 rows11013))) (joinRows (joinRows rows11263 rows11513) (joinRows rows11763 (joinRows rows12013 rows12263)))) (joinRows (joinRows (joinRows rows12513 rows12763) (joinRows rows13013 (joinRows rows13263 rows13513))) (joinRows (joinRows rows13763 rows14013) (joinRows rows14263 (joinRows rows14513 rows14763))))) (joinRows (joinRows (joinRows (joinRows rows15013 rows15263) (joinRows rows15513 (joinRows rows15763 rows16013))) (joinRows (joinRows rows16263 rows16513) (joinRows rows16763 (joinRows rows17013 rows17263)))) (joinRows (joinRows (joinRows rows17513 rows17763) (joinRows rows18013 (joinRows rows18263 rows18513))) (joinRows (joinRows rows18763 rows19013) (joinRows rows19263 (joinRows rows19513 rows19763)))))))

end OMA.QuadraticPrimeWitness

theorem OMA.solution : OMA.R_OeisA218585_conjecture_2_R1.H1 := by
  intro n lo hi
  exact OMA.QuadraticPrimeWitness.allRows n (by omega) (by omega)