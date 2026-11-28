/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186Far
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleEndpointCheck
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186TailTransfer

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness

/-! # Scalar K186 comparison at the direct cutoff -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The compensated forward Mangoldt contribution at the K186 cutoff. The
two finite sums are the arithmetic input of the direct scalar comparison. -/
noncomputable def k186ForwardValue (X : ℝ) : ℝ :=
  let B := fun m : ℕ ↦
    let v := 5 - Real.log ((m : ℝ) / X)
    ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) *
      Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * v) *
      HighGaussianKernel.k186.realProfile.eval v
  4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
    4 * highCompensationBound .k186 X

/-- The K186 loss apart from the right Euler tail, including the conductor
reflection, common contour and fixed zero mass terms. -/
noncomputable def k186DirectBaseLoss (L X : ℝ) : ℝ :=
  let z := 5 + Real.log X
  2 * L * Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * z) *
          HighGaussianKernel.k186.realProfile.eval z +
        highReflectedBudget .k186 z +
        3 * highCommonContour .k186 X -
      94173 / 1250 +
    3 * HighGaussianKernel.k186.xiMass.re

/-- The complete K186 loss with the Euler envelope evaluated at the tested cutoff. -/
noncomputable def k186DirectLoss (L X : ℝ) : ℝ :=
  k186DirectBaseLoss L X + 4 * k186TailCost X

/-- If all prime bases pass, the K186 forward value cannot exceed the
central conductor term plus the direct loss. The zero terms cancel. -/
theorem k186_direct_inequality_of_pass
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n p q r : ℕ} [NeZero p]
    [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)]
    [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) {X : ℝ} (hX : 1000000 ≤ X)
    (hl : 30 ≤ Real.log X) (hz : (profileCorrectionStart .k186 : ℝ) ≤ 5 + Real.log X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    k186ForwardValue X ≤ 3 / 8 * Real.log n + k186DirectLoss (Real.log n) X := by
  have hlo := gaussian_high_zero_score_costs hGRH .k186 hn ho hu hprod hp hq hr hX hz hpass
  have hpos : 0 < X := (by norm_num only : (0 : ℝ) < 1000000).trans_le hX
  have hup := k186_zero_upper hn ho hu hprod hp hq hr hGRH hpos hl hpass
  dsimp only [k186ForwardValue, k186DirectLoss, k186DirectBaseLoss] at ⊢
  dsimp only at hlo hup
  rw [gaussianPairZeroScore] at hlo
  linarith only [hlo, hup]

/-- The scalar comparison can use a single right Euler budget across all
cutoffs above its anchor, with all other losses still evaluated at the tested cutoff. -/
theorem k186_direct_inequality_from (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {A X : ℝ} (hX : 1000000 ≤ X) (hA : 0 < A) (ha : 30 ≤ Real.log A) (hAX : A ≤ X)
    (hz : (profileCorrectionStart .k186 : ℝ) ≤ 5 + Real.log X)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    k186ForwardValue X ≤
      3 / 8 * Real.log n + k186DirectBaseLoss (Real.log n) X + 4 * k186TailCost A := by
  have hlo := gaussian_high_zero_score_costs hGRH .k186 hn ho hu hprod hp hq hr hX hz hpass
  have hup := k186_zero_upper_from hn ho hu hprod hp hq hr hGRH hA ha hAX hpass
  dsimp only [k186ForwardValue, k186DirectBaseLoss] at ⊢
  dsimp only at hlo hup
  rw [gaussianPairZeroScore] at hlo
  linarith only [hlo, hup]

/-- At the K186 direct cutoff the analytic lower cutoffs already hold
at the end of the verified middle input range. -/
theorem k186_direct_cutoff_domain {L : ℝ} (hL : 7000000 ≤ L) :
    let X := (gaussianK186FarScale * L) ^ 2
    1000000 ≤ X ∧ 30 ≤ Real.log X := by
  intro X
  have hρ : 0 < gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have hr : (3300000 : ℝ) ≤ gaussianK186FarScale * L :=
    (by norm_num only [gaussianK186FarScale] : (3300000 : ℝ) ≤ gaussianK186FarScale * 7000000).trans
      (mul_le_mul_of_nonneg_left hL hρ.le)
  have hpos := (by norm_num only : (0 : ℝ) < 3300000).trans_le hr
  have h₀ : (1000000 : ℝ) ≤ X := by
    exact
      (by norm_num only : (1000000 : ℝ) ≤ 3300000 ^ 2).trans
        (pow_le_pow_left₀ (by norm_num only) hr 2)
  have he : Real.exp 15 ≤ 3300000 := by
    have h :=
      (middle_exp_upper_le 1200).trans
        (Rat.cast_le.mpr (by decide +kernel : middleExpUpper 1200 ≤ 3300000))
    simpa only [Rat.cast_ofNat, Nat.cast_ofNat, show (1200 : ℝ) / 80 = 15 by norm_num only] using h
  have hl := (Real.le_log_iff_exp_le hpos).mpr (he.trans hr)
  refine ⟨h₀, ?_⟩
  rw [show X = (gaussianK186FarScale * L) ^ 2 from rfl, Real.log_pow, Nat.cast_ofNat]
  linarith only [hl]

/-- A strict scalar K186 comparison at the direct cutoff supplies a
rejecting prime under GRH. This is the common entry for finite and far comparisons. -/
theorem uniform_k186_of_direct_comparison {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 7000000 ≤ Real.log n)
    (hcmp :
      let L := Real.log n;
      let X := (gaussianK186FarScale * L) ^ 2
      3 / 8 * L + k186DirectLoss L X < k186ForwardValue X) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  let L := Real.log n
  let X := (gaussianK186FarScale * L) ^ 2
  have hd := k186_direct_cutoff_domain hL
  have hz : (profileCorrectionStart .k186 : ℝ) ≤ 5 + Real.log X := by
    simp only [profileCorrectionStart, Rat.cast_ofNat, X, L]
    linarith only [hd.2]
  have hw : HasRejectingPrime n X := by
    apply uniform_gaussian_witness_from_factors hn ho hu
    intro p q r _ _ _ _ _ _ _ _ _ _ hprod hp hq hr
    by_contra h
    have hpass (l : ℕ) (hl : l.Prime) (hle : (l : ℝ) ≤ X) :
      PrimeTest.StrongMillerRabinPass n (l : ZMod n) :=
      Classical.byContradiction (fun hf ↦ h ⟨l, hl, hle, hf⟩)
    exact
      (not_lt_of_ge
          (k186_direct_inequality_of_pass hGRH hn ho hu hprod hp hq hr hd.1 hd.2 hz hpass))
        hcmp
  exact hw.mono (gaussian_k186_far_cutoff ((by norm_num only : (2000000 : ℝ) ≤ 7000000).trans hL))

/-- On the far half-line the existing monotonic comparison discharges the
strict scalar inequality from a forward coefficient and a total loss cap. -/
theorem uniform_k186_far_of_costs {n : ℕ} {α : ℝ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 10 ^ 12 ≤ Real.log n) (hα : 0.7216056623106 ≤ α)
    (hf :
      let y := gaussianK186FarScale * Real.log n
      α * y ≤ k186ForwardValue (y ^ 2))
    (hc :
      let y := gaussianK186FarScale * Real.log n
      k186DirectLoss (Real.log n) (y ^ 2) ≤ 61 / 1000 * Real.log y ^ 2 + 500) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply
    uniform_k186_of_direct_comparison hn ho hu hGRH
      ((by norm_num only : (7000000 : ℝ) ≤ 10 ^ 12).trans hL)
  have h := gaussian_k186_far_comparison hα hL hc
  dsimp only at hf h ⊢
  linarith only [hf, h]

/-- The two parts of the K186 Euler tail are exponential-polynomial terms
in the logarithmic cutoff, ready for the same interval checks as the other losses. -/
theorem k186_tail_cost_exp (t : ℝ) :
    let P := k186MassPoly
    let Q := Polynomial.X ^ 2 * (Polynomial.C (13 / 4) * P - P.derivative)
    k186TailCost (Real.exp t) =
      Real.exp (-(9 / 4 : ℝ) * t) * (eulerMomentPoly P (9 / 4)).eval t +
        Real.exp (-(11 / 4 : ℝ) * t) *
            ((Polynomial.X ^ 2 * P + eulerMomentPoly Q (11 / 4)).eval t) /
          24 := by
  intro P Q
  simp only [k186TailCost, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos t),
    euler_moment_poly_eval, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X, P, Q]
  rw [mul_comm t (-(9 / 4 : ℝ)), mul_comm t (-(11 / 4 : ℝ))]

/-- At the far input anchor, a fixed Euler tail evaluation at log cutoff
53 already applies. The same evaluation applies at every larger input. -/
theorem k186_far_tail_anchor {L : ℝ} (hL : 10 ^ 12 ≤ L) :
    Real.exp 53 ≤ (gaussianK186FarScale * L) ^ 2 := by
  have he : Real.exp (53 / 2) ≤ 400000000000 := by
    have h :=
      (middle_exp_upper_le 2120).trans
        (Rat.cast_le.mpr (by decide +kernel : middleExpUpper 2120 ≤ 400000000000))
    simpa only [Rat.cast_ofNat, Nat.cast_ofNat,
      show (2120 : ℝ) / 80 = 53 / 2 by norm_num only] using h
  have hρ : (0 : ℝ) ≤ gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have hy : (400000000000 : ℝ) ≤ gaussianK186FarScale * L :=
    (by norm_num only [gaussianK186FarScale] :
          (400000000000 : ℝ) ≤ gaussianK186FarScale * 10 ^ 12).trans
      (mul_le_mul_of_nonneg_left hL hρ)
  have hs : Real.exp (53 / 2) ^ (2 : ℕ) = Real.exp 53 := by
    rw [← Real.exp_natCast_mul]
    norm_num only [Nat.cast_ofNat]
  exact hs ▸ pow_le_pow_left₀ (Real.exp_pos _).le (he.trans hy) 2

end PseudoPrime.PrimeTestBounds.MillerRabin
