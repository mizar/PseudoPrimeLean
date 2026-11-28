/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCriterionAssembly
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EulerTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Raw
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131RawZero
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Zero
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPairCharacterData
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleConductors

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EulerTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131TailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Raw

/-! # Reduction of the K131 witness to its analytic comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Prime triviality for the three K131 pair characters forces their
combined zero sum to dominate the principal comparison with square recovery. -/
theorem k131_pair_zero_lower_sharp {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hn : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpq : 2 ≤ p * q) (hpr : 2 ≤ p * r)
    (hqr : 2 ≤ q * r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let y := gaussianBridgeScale (Real.log n)
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    a.IsPrimitive →
      b.IsPrimitive →
      c.IsPrimitive →
      a ≠ 1 →
      b ≠ 1 →
      c ≠ 1 →
      a.Even →
      b.Even →
      c.Even →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → a l = 1 ∧ b l = 1 ∧ c l = 1) →
      k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
              25329 / 1000000 -
              k131PrincipalRem y +
            (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
              (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) +
            3 *
              (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                  k131CentralMoment (-(19 / 32 : ℝ)) z /
                2) -
          (2 * Real.log n - 6 + 3 * Real.log (2 * Real.pi)) * k131MellinProfile x⁻¹ ≤
        -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c x ρ).re := by
  intro a b c y x z ha hb hc ha₁ hb₁ hc₁ hea heb hec hsmall
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hlow :=
    k131_euler_formula_lower hGRH.riemann hL a b c ht (fun l hl hle ↦ (hsmall l hl hle).1)
      (fun l hl hle ↦ (hsmall l hl hle).2.1) (fun l hl hle ↦ (hsmall l hl hle).2.2)
  have hhigh :=
    k131_pair_euler_upper hp hq hr hpq hpr hqr hGRH hL ha hb hc ha₁ hb₁ hc₁ hea heb hec hsmall
  have hy : 1 ≤ y :=
    (by norm_num only : (1 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have hR := k131_conductor_profile hy
  have hlog := pair_level_log_sum hn
  rw [hlog] at hhigh
  simp only [gaussian_k131_inverse_eval] at hlow
  have hR' := congrArg (fun t : ℝ ↦ 3 * Real.log (2 * Real.pi) * t) hR
  dsimp only [y] at hR'
  dsimp only [y, x, z] at hhigh ⊢
  have h := hlow.trans hhigh
  dsimp only [a, b, c] at h ⊢
  nlinarith only [h, hR']

/-- Prime triviality for the three K131 pair characters forces their
combined zero sum to dominate the principal comparison with square recovery. -/
theorem k131_pair_zero_lower {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] (hn : n = p * q * r)
    (hp : Odd p) (hq : Odd q) (hr : Odd r) (hpq : 2 ≤ p * q) (hpr : 2 ≤ p * r) (hqr : 2 ≤ q * r)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let y := gaussianBridgeScale (Real.log n)
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    a.IsPrimitive →
      b.IsPrimitive →
      c.IsPrimitive →
      a ≠ 1 →
      b ≠ 1 →
      c ≠ 1 →
      a.Even →
      b.Even →
      c.Even →
      (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → a l = 1 ∧ b l = 1 ∧ c l = 1) →
      k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
              25329 / 1000000 -
              k131PrincipalRem y +
            (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
              (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) +
            3 *
              (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                  k131CentralMoment (-(19 / 32 : ℝ)) z /
                2) -
          2 * Real.log n * k131MellinProfile x⁻¹ ≤
        -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c x ρ).re := by
  intro a b c y x z ha hb hc ha₁ hb₁ hc₁ hea heb hec hsmall
  have h :=
    k131_pair_zero_lower_sharp hn hp hq hr hpq hpr hqr hGRH hL ha hb hc ha₁ hb₁ hc₁ hea heb hec
      hsmall
  have hy : 1 ≤ y :=
    (by norm_num only : (1 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have hcost := k131_conductor_absorb (L := Real.log n) hy
  dsimp only [y, x, z, a, b, c] at h hcost ⊢
  linarith only [h, hcost]

/-- If every prime up to the squared K131 radius passes Miller–Rabin for an
odd uniform Korselt triple, its pair-character zero sum must meet the principal bound. -/
theorem k131_zero_lower_of_pass {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let y := gaussianBridgeScale (Real.log n)
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
      k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
              25329 / 1000000 -
              k131PrincipalRem y +
            (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
              (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) +
            3 *
              (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                  k131CentralMoment (-(19 / 32 : ℝ)) z /
                2) -
          2 * Real.log n * k131MellinProfile x⁻¹ ≤
        -(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b x ρ).re -
          (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c x ρ).re := by
  intro a b c y x z hpass
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr x hpass
  exact
    k131_pair_zero_lower hprod hp hq hr hpq hpr hqr hGRH hL ha.1 hb.1 hc.1 ha.2.1 hb.2.1 hc.2.1
      ha.2.2.2 hb.2.2.2 hc.2.2.2 hsmall

/-- On the K131 bridge, if all tested primes pass for an odd uniform Korselt
triple, the principal lower bound must fit below the Euler, pole, and Gram upper bound. -/
theorem k131_comparison_of_pass {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let y := gaussianBridgeScale (Real.log n)
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
      k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
              25329 / 1000000 -
              k131PrincipalRem y +
            (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
              (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) +
            3 *
              (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                  k131CentralMoment (-(19 / 32 : ℝ)) z /
                2) -
          2 * Real.log n * k131MellinProfile x⁻¹ ≤
        k131PoleConductor (2 * Real.log n) 0 + k131GramMix (k131PoleConductor (2 * Real.log n)) +
              21 / 10000 -
            (k131ShiftedGram a (Real.log n) + k131ShiftedGram b (Real.log n) +
              k131ShiftedGram c (Real.log n)) +
          4 * Real.exp (-(19 / 16 : ℝ) * Real.log x) *
            (k131MomentPoly (gaussianK131Fourier + k131GramEulerPoly) (19 / 16) 0).eval
              (Real.log x) +
          Real.exp (-(27 / 16 : ℝ) * Real.log x) *
              (Real.log x ^ 2 * (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log x) +
                (k131MomentPoly
                      (Polynomial.X ^ 2 *
                        (Polynomial.C (35 / 16 : ℝ) * (gaussianK131Fourier + k131GramEulerPoly) -
                          (gaussianK131Fourier + k131GramEulerPoly).derivative))
                      (27 / 16) 0).eval
                  (Real.log x)) /
            6 := by
  intro a b c y x z hpass
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr x hpass
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hlo :=
    k131_pair_zero_lower hprod hp hq hr hpq hpr hqr hGRH hL ha.1 hb.1 hc.1 ha.2.1 hb.2.1 hc.2.1
      ha.2.2.2 hb.2.2.2 hc.2.2.2 hsmall
  have hhi :=
    k131_three_zero_upper ha hb hc hpq hpr hqr hGRH hL (fun l hl hle ↦ (hsmall l hl hle).1)
      (fun l hl hle ↦ (hsmall l hl hle).2.1) (fun l hl hle ↦ (hsmall l hl hle).2.2) ht
  dsimp only at hlo hhi
  rw [pair_level_log_sum hprod] at hhi
  dsimp only [x, y, z, a, b, c] at hhi ⊢
  linarith only [hlo, hhi, k131_core_le_poles hGRH.riemann (2 * Real.log n)]

/-- On the K131 bridge, if all tested primes pass for an odd uniform Korselt
triple, the full comparison includes the shifted conductor, pole, and reflection terms. -/
theorem k131_scalar_comparison_of_pass {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale (Real.log n)
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    (∀ l : ℕ, l.Prime → (l : ℝ) ≤ x → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) →
      k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                  4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
                25329 / 1000000 -
                k131PrincipalRem y +
              (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
                (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) +
              3 *
                (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                    k131CentralMoment (-(19 / 32 : ℝ)) z /
                  2) -
            (2 * Real.log n - 6 + 3 * Real.log (2 * Real.pi)) * k131MellinProfile x⁻¹ +
          k131ShiftPrincipal (2 * Real.log n) (Real.log n) +
          logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
          logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
        k131PoleConductor (2 * Real.log n) 0 + k131GramMix (k131PoleConductor (2 * Real.log n)) +
          27 / 10000 +
          4 * Real.exp (-(19 / 16 : ℝ) * Real.log x) *
            (k131MomentPoly (gaussianK131Fourier + k131GramEulerPoly) (19 / 16) 0).eval
              (Real.log x) +
          Real.exp (-(27 / 16 : ℝ) * Real.log x) *
              (Real.log x ^ 2 * (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log x) +
                (k131MomentPoly
                      (Polynomial.X ^ 2 *
                        (Polynomial.C (35 / 16 : ℝ) * (gaussianK131Fourier + k131GramEulerPoly) -
                          (gaussianK131Fourier + k131GramEulerPoly).derivative))
                      (27 / 16) 0).eval
                  (Real.log x)) /
            6 := by
  intro y x z hpass
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr x hpass
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hlo :=
    k131_pair_zero_lower_sharp hprod hp hq hr hpq hpr hqr hGRH hL ha.1 hb.1 hc.1 ha.2.1 hb.2.1
      hc.2.1 ha.2.2.2 hb.2.2.2 hc.2.2.2 hsmall
  have hhi :=
    k131_three_zero_upper ha hb hc hpq hpr hqr hGRH hL (fun l hl hle ↦ (hsmall l hl hle).1)
      (fun l hl hle ↦ (hsmall l hl hle).2.1) (fun l hl hle ↦ (hsmall l hl hle).2.2) ht
  have hshift := k131_shift_gram_scalar_lower ha hb hc hGRH.riemann hL hsmall ht
  dsimp only at hlo hhi hshift
  rw [pair_level_log_sum hprod] at hhi hshift
  dsimp only [x, y, z, a, b, c] at hhi hshift ⊢
  linarith only [hlo, hhi, hshift, k131_core_le_poles hGRH.riemann (2 * Real.log n)]

/-- On the K131 log interval, a comparison that bounds the scalar gap
by zero under all prime passes yields a rejecting prime at the affine cutoff.
The certified scalar gap supplies the contradiction. -/
theorem gaussian_k131_witness_of_comparison {n : ℕ} (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hcompare :
      (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ gaussianBridgeScale (Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        gaussianK131Gap (gaussianBridgeScale (Real.log n)) ≤ 0) :
    HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2) := by
  by_contra h
  have hpass (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ gaussianBridgeScale (Real.log n) ^ 2) :
    PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  exact
    (not_lt_of_ge (hcompare hpass))
      ((by norm_num only : (0 : ℝ) < 1 / 200).trans (gaussian_k131_gap hL))

/-- On the affine bridge, prime passes cannot force the scalar gap below the
three-character xi correction plus a residual budget of 29/10000. -/
theorem k131_witness_of_xi_comparison {n : ℕ} (hRH : RiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hcompare :
      (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ gaussianBridgeScale (Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        gaussianK131Gap (gaussianBridgeScale (Real.log n)) ≤
          |3 * (k131CosineXi 0 + k131GramMix (fun s ↦ k131CosineXi |s|))| + 29 / 10000) :
    HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2) := by
  by_contra h
  have hpass (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ gaussianBridgeScale (Real.log n) ^ 2) :
    PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  linarith only [hcompare hpass, k131_xi_gram_cap hRH, gaussian_k131_gap hL]

/-- The Gaussian assembly can use the K131 analytic comparison directly.
The scalar certificates discharge the bridge positivity requirement. -/
theorem gaussian_criterion_of_k131_comparison {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (hcompare :
      UniformKorseltTriple n →
        Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000 →
        (∀ p : ℕ,
          p.Prime →
            (p : ℝ) ≤ gaussianBridgeScale (Real.log n) ^ 2 →
            PrimeTest.StrongMillerRabinPass n (p : ZMod n)) →
        gaussianK131Gap (gaussianBridgeScale (Real.log n)) ≤ 0)
    (htail :
      UniformKorseltTriple n →
        8000 ≤ Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  apply gaussian_criterion_of_uniform hn ho hGRH hcell _ htail
  intro hu hl hr
  exact gaussian_k131_witness_of_comparison ⟨hl, hr⟩ (hcompare hu ⟨hl, hr⟩)

/-- Under GRH, an odd uniform Korselt triple on the affine K131 bridge
has a rejecting prime at or below the squared bridge radius. -/
theorem uniform_k131_gaussian_witness {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    HasRejectingPrime n (gaussianBridgeScale (Real.log n) ^ 2) := by
  by_contra h
  have hpass (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ gaussianBridgeScale (Real.log n) ^ 2) :
    PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  obtain ⟨p, q, r, hp, hq, hr, _, _, hnprod⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := ⟨q * r, hnprod.trans (Nat.mul_assoc _ _ _)⟩
  have hqD : q ∣ n := ⟨p * r, hnprod.trans (by ac_rfl)⟩
  have hrD : r ∣ n := ⟨p * q, hnprod.trans (by ac_rfl)⟩
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  have hc := k131_scalar_comparison_of_pass hn ho hu hnprod hpO hqO hrO hGRH hL hpass
  have hg := k131_gap_le_of_comparison hL hc
  linarith only [hg, gaussian_k131_gap hL]

/-- The Gaussian criterion with the K131 bridge discharged. The intermediate
compressed cells and the final half-line witness are the remaining inputs. -/
theorem gaussian_criterion_of_cells_tail {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hcell :
      UniformKorseltTriple n →
        2657 / 4 < Real.log n →
        ∀ i : Fin 166,
          gaussianCompressedLeft i ≤ Real.log n →
            Real.log n ≤ gaussianCompressedRight i →
            HasRejectingPrime n ((gaussianCompressedScale i * Real.log n / 2) ^ 2))
    (htail :
      UniformKorseltTriple n →
        8000 ≤ Real.log n →
        HasRejectingPrime n
          (max 2
            (max ((1 / 4 : ℝ) * Real.log n ^ 2)
              ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
                8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2))))) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ gaussianWitnessCutoff (Real.log n) →
          PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  exact
    gaussian_criterion_of_uniform hn ho hGRH hcell
      (fun hu hlo hhi ↦ uniform_k131_gaussian_witness hn ho hu hGRH ⟨hlo, hhi⟩) htail

/-- All prime Miller–Rabin passes below the squared radius force the raw K131 comparison. -/
theorem k131_raw_comparison_of_pass {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n]
    [Fact p.Prime] [Fact q.Prime] [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)]
    (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p)
    (hq : Odd q) (hr : Odd r) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ}
    (hy : 1 < y) (h100 : 100 ≤ y) (hcut : (1250000 : ℝ) ≤ y ^ 2) (hlog : 14 ≤ 2 * Real.log y)
    (hz : 16 ≤ 9 / 4 + Real.log (y ^ 2))
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ y ^ 2 → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    K131RawComparison n y := by
  let x := y ^ 2
  let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
  let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
  let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
  obtain ⟨hpq, hpr, hqr, ha, hb, hc, hsmall⟩ :=
    pair_data_of_uniform_pass hn ho hu hprod hp hq hr x hpass
  have ht (k : ℕ) : -1 ≤ (a k).re + (b k).re + (c k).re := by
    simpa only [a, b, c, Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  have hlo :=
    k131_raw_pair_zero_lower hprod hp hq hr hpq hpr hqr hGRH hy hcut hz ha.1 hb.1 hc.1 ha.2.1 hb.2.1
      hc.2.1 ha.2.2.2 hb.2.2.2 hc.2.2.2 hsmall
  have hhi :=
    k131_raw_zero_scalar_upper ha hb hc hpq hpr hqr hGRH h100 hlog
      (fun l hl hle ↦ (hsmall l hl hle).1) (fun l hl hle ↦ (hsmall l hl hle).2.1)
      (fun l hl hle ↦ (hsmall l hl hle).2.2) ht
  dsimp only at hlo hhi
  rw [pair_level_log_sum hprod] at hhi
  dsimp only [K131RawComparison, x, a, b, c] at hhi ⊢
  linarith only [hlo, hhi, k131_core_le_poles hGRH.riemann (2 * Real.log n)]

/-- A strict raw K131 gap yields a prime Miller–Rabin witness at the squared radius. -/
theorem uniform_k131_raw_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 1 < y)
    (h100 : 100 ≤ y) (hcut : (1250000 : ℝ) ≤ y ^ 2) (hlog : 14 ≤ 2 * Real.log y)
    (hz : 16 ≤ 9 / 4 + Real.log (y ^ 2)) (hgap : ¬K131RawComparison n y) :
    HasRejectingPrime n (y ^ 2) := by
  by_contra h
  have hpass (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) ≤ y ^ 2) :
    PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  obtain ⟨p, q, r, hp, hq, hr, _, _, hnprod⟩ := uniformKorselt_ordered_factors hu
  have hpD : p ∣ n := ⟨q * r, hnprod.trans (Nat.mul_assoc _ _ _)⟩
  have hqD : q ∣ n := ⟨p * r, hnprod.trans (by ac_rfl)⟩
  have hrD : r ∣ n := ⟨p * q, hnprod.trans (by ac_rfl)⟩
  have hpO := Odd.of_dvd_nat ho hpD
  have hqO := Odd.of_dvd_nat ho hqD
  have hrO := Odd.of_dvd_nat ho hrD
  have hp2 : p ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hpO)
  have hq2 : q ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hqO)
  have hr2 : r ≠ 2 := fun h ↦ (by decide : ¬Odd (2 : ℕ)) (h ▸ hrO)
  let : NeZero n := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hn)⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero r := ⟨hr.ne_zero⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm hq2)⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm hr2)⟩
  exact
    hgap (k131_raw_comparison_of_pass hn ho hu hnprod hpO hqO hrO hGRH hy h100 hcut hlog hz hpass)

/-- The squared tail scale stays below the old quadratic branch even with the
exponential correction replaced by its maximum. -/
theorem k131_tail_scale_sq_le {L : ℝ} (hL : 8000 ≤ L) :
    gaussianK131TailScale L ^ 2 ≤
      (9090 / 33659 : ℝ) * L ^ 2 - 8 * L * Real.exp (-(L / 1000000) ^ 2) := by
  have hsq := sq_nonneg L
  have hexp := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg (L / 1000000)))
  have he := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 8 * L by linarith only [hL])
  unfold gaussianK131TailScale
  nlinarith only [hL, hsq, he]

/-- The raw K131 interval maps to rational radius endpoints used for its
scalar estimates. -/
theorem k131_tail_scale_mem {L : ℝ} (hL : L ∈ Set.Icc (8000 : ℝ) 42410) :
    gaussianK131TailScale L ∈ Set.Icc (518674 / 125 : ℝ) (1101568717 / 50000) := by
  unfold gaussianK131TailScale
  exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩

/-- From log 8000 onward, the tail scale meets the radius and logarithm
requirements of the raw K131 comparison. -/
private theorem k131_tail_scale_admissible {L : ℝ} (hL : 8000 ≤ L) :
    let y := gaussianK131TailScale L
    1 < y ∧ 100 ≤ y ∧ 1250000 ≤ y ^ 2 ∧ 14 ≤ 2 * Real.log y ∧ 16 ≤ 9 / 4 + Real.log (y ^ 2) := by
  intro y
  have h4 : 4000 ≤ y := by
    unfold y gaussianK131TailScale; linarith only [hL]
  have hpos : 0 < y := by linarith only [h4]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4000 12 12 8 9 = true by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlo
  have hlog := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 4000) h4)
  refine ⟨by linarith only [h4], by linarith only [h4], ?_, by linarith only [hlog], ?_⟩
  · nlinarith only [h4, sq_nonneg (y - 4000)]
  · rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]

/-- A strict raw K131 comparison at the rational affine scale produces a
rejecting prime within the old envelope used by the Gaussian assembly. -/
theorem k131_tail_witness_of_gap {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 8000 ≤ Real.log n)
    (hgap :
      let y := gaussianK131TailScale (Real.log n)
      27 / 10000 < 12020425 / 1000000 - 228016 / 1000000000 * y + gaussianK131TailRemainder y) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  obtain ⟨hy, h100, hcut, hlog, hz⟩ := k131_tail_scale_admissible hL
  have hcomp : ¬K131RawComparison n (gaussianK131TailScale (Real.log n)) := fun h ↦
    (not_lt_of_ge (k131_tail_gap_le_of_comparison hL h))
      (hgap.trans_le (k131_tail_gap_affine_lower (zero_le_one.trans hy.le)))
  exact
    (uniform_k131_raw_witness hn ho hu hGRH hy h100 hcut hlog hz hcomp).mono
      ((k131_tail_scale_sq_le hL).trans ((le_max_right _ _).trans (le_max_right _ _)))

private theorem k131_log_sub_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log b - Real.log a ≤ b - a := by
  have ha₀ := zero_lt_one.trans_le ha
  have hb₀ := ha₀.trans_le hab
  rw [← Real.log_div hb₀.ne' ha₀.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos hb₀ ha₀)
  have hd : (b - a) / a ≤ b - a := div_le_self (sub_nonneg.mpr hab) ha
  exact h.trans (by rwa [sub_div, div_self ha₀.ne'] at hd)

private theorem k131_log_cost_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a * (a - Real.log a) ≤ b * (b - Real.log b) := by
  have h := k131_log_sub_le ha hab
  have ha₀ := zero_lt_one.trans_le ha
  have hn : 0 ≤ a - Real.log a := by linarith only [Real.log_le_sub_one_of_pos ha₀]
  exact mul_le_mul hab (by linarith only [h]) hn (ha₀.trans_le hab).le

/-- The signed principal RH error decreases as the radius grows once the
doubled logarithm reaches one. -/
theorem k131_principal_error_antitone {c a b : ℝ} (hc : 0 ≤ c) (ha : 1 < a)
    (hl : 1 ≤ 2 * Real.log a) (hab : a ≤ b) : k131PrincipalError c b ≤ k131PrincipalError c a := by
  have hlog := Real.log_le_log (zero_lt_one.trans ha) hab
  have h := k131_log_cost_mono hl (mul_le_mul_of_nonneg_left hlog (by norm_num only))
  exact mul_le_mul_of_nonpos_left h (neg_nonpos.mpr hc)

/-- A lower bound for the six power terms on a radius interval can be
combined with the principal error and affine contribution at its right endpoint. -/
theorem k131_tail_cell_lower {y b m : ℝ} (hy : 1 < y) (hl : 1 ≤ 2 * Real.log y) (hb : y ≤ b)
    (hm : m ≤ gaussianK131TailPowers y) :
    12020425 / 1000000 - 228016 / 1000000000 * b + m + k131PrincipalError gaussianK131RhCoeff b ≤
      12020425 / 1000000 - 228016 / 1000000000 * y + gaussianK131TailRemainder y := by
  have he := k131_principal_error_antitone gaussian_k131_rh_coeff_mem.1 hy hl hb
  dsimp only [gaussianK131TailRemainder]
  linarith only [hb, hm, he]

/-- A polynomial lower bound on a positive radius interval gives a lower
bound on its product with a nonincreasing real power. The smaller endpoint
product handles both signs of the polynomial lower bound. -/
theorem k131_tail_power_cell_lower {P : Polynomial ℝ} {e a b y m : ℝ} (he : e ≤ 0) (ha : 0 < a)
    (hy : y ∈ Set.Icc a b) (hm : m ≤ P.eval (2 * Real.log y)) :
    min (a ^ e * m) (b ^ e * m) ≤ logPowerPoly e P y := by
  have hpos := ha.trans_le hy.1
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hpos.le e))
  by_cases h : 0 ≤ m
  · exact
      (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_nonpos hpos hy.2 he) h)
  · exact
      (min_le_left _ _).trans
        (mul_le_mul_of_nonpos_right (Real.rpow_le_rpow_of_nonpos ha hy.1 he) (le_of_not_ge h))

/-- A certified lower bound for the power terms in one radius interval,
with a strict endpoint budget, supplies the rejecting prime at the old cutoff. -/
theorem k131_tail_witness_of_cell {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 8000 ≤ Real.log n)
    {b m : ℝ} (hb : gaussianK131TailScale (Real.log n) ≤ b)
    (hm : m ≤ gaussianK131TailPowers (gaussianK131TailScale (Real.log n)))
    (hgap :
      27 / 10000 <
        12020425 / 1000000 - 228016 / 1000000000 * b + m +
          k131PrincipalError gaussianK131RhCoeff b) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  obtain ⟨hy, _, _, hl, _⟩ := k131_tail_scale_admissible hL
  exact
    k131_tail_witness_of_gap hn ho hu hGRH hL
      (hgap.trans_le (k131_tail_cell_lower hy ((by norm_num only : (1 : ℝ) ≤ 14).trans hl) hb hm))

/-- On the raw K131 interval, only the four variable polynomial terms
require a cell-specific lower bound. The two constant power terms supply
a common positive allowance. -/
theorem k131_tail_witness_of_variable {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8000 : ℝ) 42410) {b m : ℝ}
    (hb : gaussianK131TailScale (Real.log n) ≤ b)
    (hm : m ≤ gaussianK131TailVariable (gaussianK131TailScale (Real.log n)))
    (hgap :
      27 / 10000 <
        12020425 / 1000000 - 228016 / 1000000000 * b + (m + 3 / 1000) +
          k131PrincipalError gaussianK131RhCoeff b) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  have hy := k131_tail_scale_mem hL
  have h :=
    k131_tail_powers_lower ((by norm_num only : (4000 : ℝ) ≤ 518674 / 125).trans hy.1)
      (hy.2.trans (by norm_num only : (1101568717 / 50000 : ℝ) ≤ 22032))
  exact
    k131_tail_witness_of_cell hn ho hu hGRH hL.1 hb
      ((add_le_add hm (le_refl (3 / 1000 : ℝ))).trans h) hgap

private theorem k131_power_concave {p a b : ℝ} {P : Polynomial ℝ} (ha : 0 < a)
    (hc : ∀ y ∈ Set.Ioo a b, logPowerPoly (-p) (logPowerCurvature p P) y ≤ 0) :
    ConcaveOn ℝ (Set.Icc a b) (logPowerPoly (-p) P) := by
  have h :=
    log_power_sum_concave ({()} : Finset Unit) (fun _ ↦ p) (fun _ ↦ P) ha (R := fun _ ↦ 0) (R' :=
      fun _ ↦ 0) (R'' := fun _ ↦ 0) (fun y _ ↦ hasDerivAt_const y 0)
      (fun y _ ↦ hasDerivAt_const y 0)
      (fun y hy ↦ by simpa only [Finset.sum_singleton, mul_zero, add_zero] using hc y hy)
  simpa only [Finset.sum_singleton, add_zero] using h

/-- The sum of the two reflected terms on a radius cell is bounded below
by the smaller of its two endpoint values. -/
theorem k131_tail_reflection_cell_lower {a b y : ℝ} (ha : 0 < a) (hl : 141 / 10 ≤ 2 * Real.log a)
    (hy : y ∈ Set.Icc a b) :
    let R := fun t ↦
      logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 t +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher t
    min (R a) (R b) ≤ R y := by
  intro R
  have hlog (t : ℝ) (ht : t ∈ Set.Ioo a b) : 141 / 10 ≤ 2 * Real.log t :=
    hl.trans (mul_le_mul_of_nonneg_left (Real.log_le_log ha ht.1.le) (by norm_num only))
  have h₁ :=
    k131_power_concave (b := b) ha fun t ht ↦
      gaussian_k131_poly23_curvature (ha.trans ht.1)
        ((by norm_num only : (14 : ℝ) ≤ 141 / 10).trans (hlog t ht))
  have h₂ :=
    k131_power_concave (b := b) ha fun t ht ↦
      gaussian_k131_poly_higher_curvature (ha.trans ht.1) (hlog t ht)
  have hab := hy.1.trans hy.2
  exact (h₁.add h₂).min_le_of_mem_Icc ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hy

private theorem k131_mono_of_concave_cells {f : ℝ → ℝ} {a : ℝ}
    (hc : ∀ b, ConcaveOn ℝ (Set.Icc a b) f) (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    MonotoneOn f (Set.Ici a) := by
  intro x hx y _ hxy
  rcases hxy.lt_or_eq with hxy | rfl
  · by_contra! hn
    let d := (f y - f x) / (y - x)
    have hd : d < 0 := div_neg_of_neg_of_pos (sub_neg.mpr hn) (sub_pos.mpr hxy)
    have hbound : ∀ᶠ z in Filter.atTop, (-1 : ℝ) < f z :=
      hf.eventually (lt_mem_nhds (by norm_num only : (-1 : ℝ) < 0))
    obtain ⟨z, hfz⟩ := (Filter.eventually_atTop.mp hbound)
    let w := max z (y + (|f y| + 2) / (-d) + 1)
    have hq : 0 ≤ (|f y| + 2) / (-d) :=
      div_nonneg (by linarith only [abs_nonneg (f y)]) (neg_nonneg.mpr hd.le)
    have hright : y + (|f y| + 2) / (-d) + 1 ≤ w := le_max_right _ _
    have hyw : y < w := by linarith only [hright, hq]
    have hs :=
      (hc w).slope_anti_adjacent ⟨hx, (hxy.trans hyw).le⟩ ⟨hx.trans (hxy.trans hyw).le, le_rfl⟩ hxy
        hyw
    have hout : f w - f y ≤ d * (w - y) := (div_le_iff₀ (sub_pos.mpr hyw)).mp hs
    have hmul :=
      mul_le_mul_of_nonpos_left (show (|f y| + 2) / (-d) ≤ w - y by linarith only [hright]) hd.le
    have hcancel : d * ((|f y| + 2) / (-d)) = -(|f y| + 2) := by
      rw [div_neg, mul_neg, ← mul_div_assoc, mul_comm d, mul_div_cancel_right₀ _ hd.ne]
    rw [hcancel] at hmul
    linarith only [hfz w (le_max_left _ _), hout, hmul, le_abs_self (f y)]
  · exact le_rfl

/-- The reflected terms are nondecreasing once the doubled logarithm is
at least 141/10. Their left endpoint therefore suffices on every tail cell. -/
theorem k131_tail_reflection_mono {a : ℝ} (ha : 0 < a) (hl : 141 / 10 ≤ 2 * Real.log a) :
    MonotoneOn
      (fun y ↦
        logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
          logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y)
      (Set.Ici a) := by
  apply k131_mono_of_concave_cells
  · intro b
    have hlog (t : ℝ) (ht : t ∈ Set.Ioo a b) : 141 / 10 ≤ 2 * Real.log t :=
      hl.trans (mul_le_mul_of_nonneg_left (Real.log_le_log ha ht.1.le) (by norm_num only))
    exact
      (k131_power_concave ha fun t ht ↦
            gaussian_k131_poly23_curvature (ha.trans ht.1)
              ((by norm_num only : (14 : ℝ) ≤ 141 / 10).trans (hlog t ht))).add
        (k131_power_concave ha fun t ht ↦
          gaussian_k131_poly_higher_curvature (ha.trans ht.1) (hlog t ht))
  · simpa only [add_zero] using
      (k131_power_tendsto_zero (by norm_num only : (0 : ℝ) < 23 / 4) gaussianK131Poly23).add
        (k131_power_tendsto_zero (by norm_num only : (0 : ℝ) < 27 / 4) gaussianK131PolyHigher)

/-- The two reflection costs together lose at most 151/25000000
throughout the raw K131 radius range. -/
theorem k131_tail_reflection_lower {y : ℝ} (hy : 1036273 / 250 ≤ y) :
    -(151 / 25000000 : ℝ) ≤
      logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y := by
  let a : ℝ := 1036273 / 250
  have ha : 0 < a := by norm_num only [a]
  have hl : 141 / 10 ≤ 2 * Real.log a := by linarith only [k131_right_log_bounds.1]
  have h := k131_tail_reflection_mono ha hl (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hy) hy
  have h23 := k131_right_reflect23_lower
  have h27 := k131_right_reflect27_lower
  change
    -(6 / 1000000 : ℝ) ≤
      (a ^ (1 / 8 : ℝ)) ^ (-46 : ℤ) * gaussianK131Poly23.eval (2 * Real.log a) at h23
  change
    -(4 / 100000000 : ℝ) ≤
      (a ^ (1 / 8 : ℝ)) ^ (-54 : ℤ) * gaussianK131PolyHigher.eval (2 * Real.log a) at h27
  rw [← k131_rpow_eighth ha.le, show ((-46 : ℤ) : ℝ) / 8 = -(23 / 4 : ℝ) by norm_num only] at h23
  rw [← k131_rpow_eighth ha.le, show ((-54 : ℤ) : ℝ) / 8 = -(27 / 4 : ℝ) by norm_num only] at h27
  dsimp only [logPowerPoly] at h ⊢
  linarith only [h, h23, h27]

/-- On the raw K131 interval, lower bounds on the two main terms and a
strict endpoint budget suffice for the least-prime witness comparison. -/
theorem k131_tail_witness_of_main {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8000 : ℝ) 42410) {b m : ℝ}
    (hb : gaussianK131TailScale (Real.log n) ≤ b)
    (hm : m ≤ gaussianK131TailMain (gaussianK131TailScale (Real.log n)))
    (hgap :
      27 / 10000 <
        12020425 / 1000000 - 228016 / 1000000000 * b + (m - 151 / 25000000 + 3 / 1000) +
          k131PrincipalError gaussianK131RhCoeff b) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  have hy :=
    (by norm_num only : (1036273 / 250 : ℝ) ≤ 518674 / 125).trans (k131_tail_scale_mem hL).1
  have hr := k131_tail_reflection_lower hy
  exact
    k131_tail_witness_of_variable hn ho hu hGRH hL hb
      (by
        dsimp only [gaussianK131TailVariable]; linarith only [hm, hr])
      hgap

/-- A rational enclosure of the doubled logarithm and a lower eighth-root
bound give the main-term hypothesis of the K131 tail witness theorem. -/
theorem k131_tail_witness_of_cap {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8000 : ℝ) 42410) {a b r : ℚ} {u : ℝ} (ha : 0 ≤ a) (hr : 0 < r)
    (hroot : (r : ℝ) ≤ gaussianK131TailScale (Real.log n) ^ (1 / 8 : ℝ))
    (hlog : 2 * Real.log (gaussianK131TailScale (Real.log n)) ∈ Set.Icc (a : ℝ) (b : ℝ))
    (hupp : gaussianK131TailScale (Real.log n) ≤ u)
    (hgap :
      27 / 10000 <
        12020425 / 1000000 - 228016 / 1000000000 * u +
          (-(k131RawTailCap a b r : ℝ) - 151 / 25000000 + 3 / 1000) +
          k131PrincipalError gaussianK131RhCoeff u) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  have hy := (by norm_num only : (0 : ℝ) ≤ 518674 / 125).trans (k131_tail_scale_mem hL).1
  exact
    k131_tail_witness_of_main hn ho hu hGRH hL hupp (k131_raw_tail_cap_sound hy ha hr hroot hlog)
      hgap

/-- A raw K131 radius box with rational logarithm and eighth-power bounds
supplies the prime witness once its rational budget is strict. -/
theorem k131_tail_witness_of_box {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (8000 : ℝ) 42410) {l u a b r c cost : ℚ}
    (hy : gaussianK131TailScale (Real.log n) ∈ Set.Icc (l : ℝ) (u : ℝ)) (ha : 0 < a) (hr : 0 < r)
    (hp : r ^ 8 ≤ l) (hl : (a : ℝ) ≤ 2 * Real.log (l : ℝ)) (hupp : 2 * Real.log (u : ℝ) ≤ (b : ℝ))
    (hc : (c : ℝ) ≤ Real.log (2 * Real.log (u : ℝ)))
    (hcap :
      let y := gaussianK131TailScale (Real.log n)
      0 ≤ y →
        (r : ℝ) ≤ y ^ (1 / 8 : ℝ) →
        2 * Real.log y ∈ Set.Icc (a : ℝ) (b : ℝ) → -(cost : ℝ) ≤ gaussianK131TailMain y)
    (hgap : 27 / 10000 < k131TailBudget u b c cost) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  let y := gaussianK131TailScale (Real.log n)
  have hl₀ : (0 : ℝ) < (l : ℝ) := Rat.cast_pos.mpr ((pow_pos hr 8).trans_le hp)
  have hy₀ : 0 < y := hl₀.trans_le hy.1
  have hlog : 2 * Real.log y ∈ Set.Icc (a : ℝ) (b : ℝ) :=
    ⟨hl.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hl₀ hy.1) (by norm_num only)),
      (mul_le_mul_of_nonneg_left (Real.log_le_log hy₀ hy.2) (by norm_num only)).trans hupp⟩
  have hpos : 0 < 2 * Real.log (u : ℝ) :=
    (Rat.cast_pos.mpr ha).trans_le
      (hlog.1.trans (mul_le_mul_of_nonneg_left (Real.log_le_log hy₀ hy.2) (by norm_num only)))
  have hpow : (r : ℝ) ^ (8 : ℕ) ≤ y := by
    have h := (Rat.cast_le (K := ℝ)).mpr hp
    rw [Rat.cast_pow] at h
    exact h.trans hy.1
  have hroot :=
    Real.rpow_le_rpow (pow_nonneg (Rat.cast_nonneg.mpr hr.le) 8) hpow
      (by norm_num only : (0 : ℝ) ≤ 1 / 8)
  rw [← Real.rpow_natCast_mul (Rat.cast_nonneg.mpr hr.le)] at hroot
  rw [show (↑(8 : ℕ) : ℝ) * (1 / 8) = 1 by norm_num only, Real.rpow_one] at hroot
  exact
    k131_tail_witness_of_main hn ho hu hGRH hL hy.2 (hcap hy₀.le hroot hlog)
      (k131_raw_tail_budget_sound hpos hupp hc hgap)

/-- Under GRH the last raw K131 cell supplies a rejecting prime within the
old Gaussian envelope for odd uniform triples with log in [42409.99, 42410]. -/
theorem k131_raw_last_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ∈ Set.Icc (4240999 / 100 : ℝ) 42410) :
    HasRejectingPrime n
      (max 2
        (max ((1 / 4 : ℝ) * Real.log n ^ 2)
          ((9090 / 33659 : ℝ) * Real.log n ^ 2 -
            8 * Real.log n * Real.exp (-(Real.log n / 1000000) ^ 2)))) := by
  obtain ⟨hp, hl, hb, hc⟩ := k131_raw_last_box
  refine
    k131_tail_witness_of_box hn ho hu hGRH ⟨by linarith only [hL.1], hL.2⟩ (cost :=
      k131RawTailCap (2000044517 / 100000000) (2000044565 / 100000000) (349044 / 100000)) ?_
      (by norm_num only) (by norm_num only) hp hl hb hc ?_ ?_
  · norm_num only [Rat.cast_div, Rat.cast_ofNat, gaussianK131TailScale]
    exact ⟨by linarith only [hL.1], by linarith only [hL.2]⟩
  · exact fun hy hr hx ↦ k131_raw_tail_cap_sound hy (by norm_num only) (by norm_num only) hr hx
  · decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
