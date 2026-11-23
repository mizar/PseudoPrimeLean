/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Shared trial-divisor base for direct theta estimates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- Scalar least common multiple of the integers from one through 4096. -/
def thetaDivisorBase4096 : ℕ :=
  let n : ℕ := 0x189519ba3a3d2b189e0fd0b76d64af2d82140c50ec
  let n := (n <<< 240) + 0x5cec70e8aafaa4472571d18850c5e93f1639efff0e8aaab7bafe54ed85a0
  let n := (n <<< 240) + 0x4ceed7cdd164d1c96f3359986786f68dc17f49e7513a5b1210540706e0b9
  let n := (n <<< 240) + 0x8cb204d57245470705cd5e2c4cd2731da544d9d2ced20dbfac45f066dba9
  let n := (n <<< 240) + 0x5185f02e0c395428e0ff07ab633eb7260e671dbd428b1af6aba32e61d8f6
  let n := (n <<< 240) + 0xe72ea56bb267201dd1383ccf1503d5a84a408d2bd6876ebca88e0ccf8927
  let n := (n <<< 240) + 0xd8c533a253e416df987fd2447b8761fb8c1d5a54575502956c6b04b47472
  let n := (n <<< 240) + 0xa2af7891cb92f7b304b35f067add04ba73d0662b77ddbfecd645f647dd73
  let n := (n <<< 240) + 0x9194bcee67c356e7054871bf3fe4bdea1a46890510373df5f5f3c58d7f06
  let n := (n <<< 240) + 0x983dba571364ab213e04af6c27f4f348ded926d61922bf38183c7bdb13bd
  let n := (n <<< 240) + 0x34f5a5220a431a04aa9fbcb2f1f23cf519d803317e0272d8526c0914f692
  let n := (n <<< 240) + 0x4acffd7db19d3c641ae57d96558d063ee4544190af9bc4c306a39255b2af
  let n := (n <<< 240) + 0x6a40d7319079f1b32aef8e9a6f1b395cedbb2712b1e1656bec685085d206
  let n := (n <<< 240) + 0x0f4cd157223febf961d5022d1da9359519224fd40f1c898e5cd6ad67058a
  let n := (n <<< 240) + 0x6407ea96a9ad837a4e3f002220a852dca78c75df803b0dbd4d59c4439c7f
  let n := (n <<< 240) + 0x2d6190ade51f3492d9655b546f3e856bc6e3740db522c0c158377b7661ca
  let n := (n <<< 240) + 0x4472afc633b6963bcbc97cac03eb5d61fb1e03f80b4b9f9880fa00b23599
  let n := (n <<< 240) + 0xcc083fcce2fb74f13141d0649cf114bff5660c854359c8c6385eec39c0f1
  let n := (n <<< 240) + 0x05c3527c7065c29d5aa362c33e9e35289cc7a77fb17885df0201609789b7
  let n := (n <<< 240) + 0xba7251efdc131b9f4c36897d9a375201b126d7326717c5a86e20bacc55b0
  let n := (n <<< 240) + 0x354a13cbe361ae65cb6a88f46ca5d6455a40a687ebd12732f9ecb0c8ca6a
  let n := (n <<< 240) + 0x7dd3e12d4377c7f9da93e5036e6d3f4992288c2db97bf024da75b07d8715
  let n := (n <<< 240) + 0x2155d101fbd2e235b8f7ce6f1c422bec693786f86ddda2eee1116b05e2d6
  let n := (n <<< 240) + 0xbc9b12ce167ce6950075a170dfbcc855b154ec2e1a26a97a3267c0bfed32
  let n := (n <<< 240) + 0xa0a267708d5714885ec9982080144d88b5973117bd9a016f3a5891639000
  n

private theorem covers (m : ℕ) (hm : 2 ≤ m) (hb : m ≤ 4096) : m ∣ thetaDivisorBase4096 := by
  have h : divisorBase 12 1 = thetaDivisorBase4096 := by decide +kernel
  rw [← h]
  exact dvd_divisorBase 12 1 m ((by decide : 1 ≤ 2).trans hm) (Nat.lt_succ_of_le hb)

/-- A checked count and rational endpoints certify a closed theta interval with trial divisors
through 4096. -/
theorem thetaTile4096 (a b t d k r j : ℕ) (e f q u : ℚ) (ha : 1000000 ≤ a)
    (hb : b < (4096 + 1) * (4096 + 1)) (he : a + 2 ^ (t + d) = b)
    (hc : tiledPrimeCount thetaDivisorBase4096 200560490130 t d a = k) (hs : r ^ 2 ≤ a)
    (hl : PseudoPrime.Analysis.rationalLogIntervalCheck a j 20 q u = true) (hf : f ≤ e + k * q)
    (hw : (b : ℚ) ≤ e + 5 * r) : ThetaLowerSegment a b e f := by
  apply theta_segment_of_count covers a b t d k 200560490130 r e f q ha hb he hc hs _ hf hw
  simpa only [Rat.cast_natCast] using (PseudoPrime.Analysis.rationalLogIntervalCheck_sound hl).1

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
