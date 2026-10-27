/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaLinearCutoffBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianStarClassification

/-! # Complete all-input Gamma index-100 witness bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm at least 330 has a prime
strong-MR witness below the Gamma index-100 cutoff. The subgroup-index split
and its residual uniform Korselt triple are discharged internally. -/
theorem exists_prime_witness_le_gammaIndex100 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  let : NeZero n := ⟨hn0⟩
  have hn142 := gammaIndex100_log_ge_decimal142 hL
  have hnlarge : 20000 ≤ n := by
    have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
    exact h20000.trans hn142
  rcases
    exists_prime_witness_le_gammaIndex100_or_uniform_korselt_triple_of_odd_composite hnOdd hcomp
      hGRH hL with
    hw | htriple
  · exact hw
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    exact
      exists_prime_witness_le_gammaIndex100_of_uniform_korselt_triple_card hnOdd hsf hc hK hU
        hnlarge hGRH hL

/-- The least prime rejecting strong MR inherits the Gamma index-100 cutoff
for every odd composite at logarithmic scale at least 330. -/
theorem exists_least_prime_witness_le_gammaIndex100 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ := exists_prime_witness_le_gammaIndex100 hnOdd hcomp hGRH hL
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, (Nat.find_spec hex).2,
      fun q hq hqReject ↦ Nat.find_min' hex ⟨hq, hqReject⟩⟩

/-- The least prime rejecting strong MR is bounded by the two-prefix `U₁₀₀`
envelope for every odd composite with logarithm at least 240. -/
theorem exists_least_prime_witness_le_gammaIndex100PrefixUpper {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_le_gammaIndex100PrefixUpper hnOdd hcomp hGRH hL
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, (Nat.find_spec hex).2,
      fun q hq hqReject ↦ Nat.find_min' hex ⟨hq, hqReject⟩⟩

/-- The index-100 radius lies below either retained-prefix root from `L = 330`
onward. The three scalar coefficients all make the old gap negative at the new
root, so each old positive root is strictly larger. -/
theorem gammaIndex100Radius_lt_gammaClippedPrefixRoot {L C : ℝ} (hL : 330 ≤ L)
    (hC : C = 203 / 50 ∨ C = 28493 / 5000) :
    gammaIndex100Radius L < gammaClippedPrefixRoot L C := by
  let r := gammaIndex100Radius L
  have hr := gammaIndex100Radius_properties hL
  have hrpos : 0 < r := by
    dsimp only [r]
    exact hr.1
  have hD : 0 ≤ 143420077 / 11856000 - 2 * C := by
    rcases hC with hC | hC
    · rw [hC]
      norm_num only
    · rw [hC]
      norm_num only
  have hmulid :
    gammaClippedPrefixGap L C r * r =
      ((87069 / 98800 : ℝ) - 91 / 100) * r ^ 2 +
        (1057 / 2500 - (143420077 / 11856000 - 2 * C)) * r +
        (61 - 190 / 3) := by
    rw [gammaClippedPrefixGap]
    dsimp only [r] at *
    field_simp [hr.1.ne']
    nlinarith only [hr.2]
  have hgap : gammaClippedPrefixGap L C r < 0 := by
    rcases hC with hC | hC
    · rw [hC] at hmulid ⊢
      have hcoeff : (87069 / 98800 : ℝ) - 91 / 100 < 0 := by norm_num only
      have hconst : 1057 / 2500 - (143420077 / 11856000 - 2 * (203 / 50 : ℝ)) < 0 := by
        norm_num only
      have hlast : (61 : ℝ) - 190 / 3 < 0 := by norm_num only
      have hsq : 0 < r ^ 2 := sq_pos_of_pos hrpos
      have hprod : gammaClippedPrefixGap L (203 / 50) r * r < 0 := by
        rw [hmulid]
        nlinarith only [hcoeff, hconst, hlast, hsq, hrpos]
      calc
        gammaClippedPrefixGap L (203 / 50) r = (gammaClippedPrefixGap L (203 / 50) r * r) / r := by
          field_simp [hrpos.ne']
        _ < 0 := div_neg_of_neg_of_pos hprod hrpos
    · rw [hC] at hmulid ⊢
      have hcoeff : (87069 / 98800 : ℝ) - 91 / 100 < 0 := by norm_num only
      have hconst : 1057 / 2500 - (143420077 / 11856000 - 2 * (28493 / 5000 : ℝ)) < 0 := by
        norm_num only
      have hlast : (61 : ℝ) - 190 / 3 < 0 := by norm_num only
      have hsq : 0 < r ^ 2 := sq_pos_of_pos hrpos
      have hprod : gammaClippedPrefixGap L (28493 / 5000) r * r < 0 := by
        rw [hmulid]
        nlinarith only [hcoeff, hconst, hlast, hsq, hrpos]
      calc
        gammaClippedPrefixGap L (28493 / 5000) r =
            (gammaClippedPrefixGap L (28493 / 5000) r * r) / r :=
          by field_simp [hrpos.ne']
        _ < 0 := div_neg_of_neg_of_pos hprod hrpos
  have hL120 : 120 ≤ L := by linarith only [hL]
  have hroot : gammaClippedPrefixRoot L C ≤ r → False := by
    intro hroot
    have hnonneg := gammaClippedPrefixGap_nonneg_of_root_le hL120 hD hroot
    linarith only [hgap, hnonneg]
  exact lt_of_not_ge hroot

/-- Each retained-prefix Gamma envelope is strictly above the new index-100
bound on its full common range. -/
theorem gammaIndex100Bound_lt_gammaClippedPrefixBound {L b C : ℝ} (hL : 330 ≤ L)
    (hC : C = 203 / 50 ∨ C = 28493 / 5000) :
    gammaIndex100Bound L < gammaClippedPrefixBound L b C := by
  have hr := gammaIndex100Radius_properties hL
  have hroot := gammaIndex100Radius_lt_gammaClippedPrefixRoot hL hC
  have hrad : gammaIndex100Radius L < gammaClippedPrefixRadius L b C :=
    lt_of_lt_of_le hroot (le_max_right _ _)
  have hupperpos : 0 < gammaClippedPrefixRadius L b C := by
    exact
      lt_of_lt_of_le
        (gammaClippedPrefixRoot_pos (by linarith only [hL])
          (by
            rcases hC with hC | hC
            · rw [hC]
              norm_num only
            · rw [hC]
              norm_num only))
        (le_max_right _ _)
  have hsq : (gammaIndex100Radius L) ^ 2 < (gammaClippedPrefixRadius L b C) ^ 2 :=
    (sq_lt_sq₀ hr.1.le hupperpos.le).2 hrad
  dsimp only [gammaIndex100Bound, gammaClippedPrefixBound]
  exact (mul_lt_mul_of_pos_left hsq (by norm_num only : (0 : ℝ) < 99 / 40))

/-- The new Gamma bound is strictly below both retained-prefix bounds, hence
strictly below their pointwise minimum, for every `L ≥ 330`. -/
theorem gammaIndex100Bound_lt_gammaClippedUpper {L : ℝ} (hL : 330 ≤ L) :
    gammaIndex100Bound L < gammaClippedUpper L := by
  have h1000 :=
    gammaIndex100Bound_lt_gammaClippedPrefixBound hL (b := 1000) (C := 203 / 50) (Or.inl rfl)
  have h50000 :=
    gammaIndex100Bound_lt_gammaClippedPrefixBound hL (b := 50000) (C := 28493 / 5000) (Or.inr rfl)
  change gammaIndex100Bound L < min (gammaClippedBound1000 L) (gammaClippedBound50000 L)
  exact lt_min h1000 h50000

/-- The index-100 radius exceeds the affine comparison radius used by the
6/5 Gaussian estimate from `L = 500` onward. -/
theorem gammaIndex100Radius_ge_affine {L : ℝ} (hL : 330 ≤ L) :
    ((11783423 / 25000000 : ℝ) / (91 / 100)) * L + 14 / 5 ≤ gammaIndex100Radius L := by
  let t := ((11783423 / 25000000 : ℝ) / (91 / 100)) * L + 14 / 5
  have hr := gammaIndex100Radius_properties hL
  have hA : 0 < (11783423 / 25000000 : ℝ) * L + 1057 / 2500 := by nlinarith only [hL]
  have hfactor :
    0 <
      (91 / 100 : ℝ) * (t + gammaIndex100Radius L) -
        ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) := by
    dsimp only [t]
    nlinarith only [hr.1, hL]
  have hpoly :
    (91 / 100 : ℝ) * t ^ 2 - ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) * t -
        ((7 / 6 : ℝ) * L + 61) <
      0 := by
    dsimp only [t]
    nlinarith only [hL]
  have hdiff :
    ((91 / 100 : ℝ) * t ^ 2 - ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) * t -
          ((7 / 6 : ℝ) * L + 61)) -
        ((91 / 100 : ℝ) * (gammaIndex100Radius L) ^ 2 -
          ((11783423 / 25000000 : ℝ) * L + 1057 / 2500) * gammaIndex100Radius L -
          ((7 / 6 : ℝ) * L + 61)) =
      (t - gammaIndex100Radius L) *
        ((91 / 100 : ℝ) * (t + gammaIndex100Radius L) -
          ((11783423 / 25000000 : ℝ) * L + 1057 / 2500)) := by
    ring
  by_contra hnot
  have hle : gammaIndex100Radius L ≤ t := le_of_not_ge hnot
  have hprod :
    0 ≤
      (t - gammaIndex100Radius L) *
        ((91 / 100 : ℝ) * (t + gammaIndex100Radius L) -
          ((11783423 / 25000000 : ℝ) * L + 1057 / 2500)) :=
    mul_nonneg (sub_nonneg.mpr hle) hfactor.le
  rw [hr.2] at hdiff
  linarith only [hpoly, hdiff, hprod]

/-- The 6/5 Gaussian radius is below the `287/200` multiple of the affine
lower bound for the index-100 Gamma radius from `L = 500` onward. -/
theorem gaussianMR6FifthsRadius_lt_gammaIndex100Comparison {L : ℝ} (hL : 500 ≤ L) :
    PseudoPrime.Analysis.gaussianMR6FifthsRadius L <
      (287 / 200 : ℝ) * ((11783423 / 25000000 : ℝ) / (91 / 100) * L + 14 / 5) := by
  let R0 := (287 / 200 : ℝ) * ((11783423 / 25000000 : ℝ) / (91 / 100) * L + 14 / 5)
  let s := PseudoPrime.Analysis.gaussianMR6FifthsRoot L
  let r := PseudoPrime.Analysis.gaussianMR6FifthsRadius L
  let A :=
    (639999 / 1000000 : ℝ) * (287 / 200) * ((11783423 / 25000000 : ℝ) / (91 / 100)) -
      (161 / 400 : ℝ) -
      (257 / 500 : ℝ) * (39 / 1000)
  let B := (639999 / 1000000 : ℝ) * (287 / 200) * (14 / 5)
  have hLpos : 0 < L := by linarith only [hL]
  have hspos : 0 < s := PseudoPrime.Analysis.gaussianMR6FifthsRoot_pos hL
  have hsq : r = s ^ 2 := by dsimp only [r, PseudoPrime.Analysis.gaussianMR6FifthsRadius, s]
  have hradius := PseudoPrime.Analysis.gaussianMR6FifthsRadius_lower hL
  have hroot17 : 17 ≤ s := by
    have h17 : (17 : ℝ) ≤ Real.sqrt r := by
      apply Real.le_sqrt_of_sq_le
      dsimp only [r] at hradius ⊢
      nlinarith only [hL, hradius]
    rw [show Real.sqrt r = s by rw [hsq, Real.sqrt_sq hspos.le]] at h17
    exact h17
  have hRpos : 0 < R0 := by
    dsimp only [R0]; positivity
  have hR0upper : Real.sqrt R0 ≤ (39 / 1000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · dsimp only [R0]
      nlinarith only [hL]
  have hD : (639999 / 1000000 : ℝ) ≤ PseudoPrime.Analysis.gaussianMR6FifthsD := by
    norm_num only [PseudoPrime.Analysis.gaussianMR6FifthsD,
      PseudoPrime.Analysis.gaussianMR6FifthsIndex, PseudoPrime.Analysis.gaussianMR6FifthsMass,
      PseudoPrime.Analysis.gaussianMR6FifthsEndpoint]
  have hBeta : PseudoPrime.Analysis.gaussianMR6FifthsBeta ≤ (257 / 500 : ℝ) := by
    norm_num only [PseudoPrime.Analysis.gaussianMR6FifthsBeta,
      PseudoPrime.Analysis.gaussianMR6FifthsIndex, PseudoPrime.Analysis.gaussianMR6FifthsMass]
  have hApos : 0 < A := by norm_num only [A]
  have hA500 : 0 < A * 500 + B - 29 := by norm_num only [A, B]
  have hlinear : 0 < A * L + B - 29 := by
    have hL' : 0 ≤ L - 500 := by linarith only [hL]
    have hstep := mul_nonneg hApos.le hL'
    dsimp only [A, B] at hstep hA500 ⊢
    nlinarith only [hstep, hA500]
  have hmargin :
    0 <
      PseudoPrime.Analysis.gaussianMR6FifthsD * R0 -
        PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta * Real.sqrt R0 -
        29 := by
    have hDscaled := mul_le_mul_of_nonneg_right hD (le_of_lt hRpos)
    have hbetascaled :=
      mul_le_mul hBeta hR0upper (Real.sqrt_nonneg R0) (by norm_num only : (0 : ℝ) ≤ 257 / 500)
    have hDcon : (161 / 400 : ℝ) = PseudoPrime.Analysis.gaussianMR6FifthsConductor := by
      norm_num only [PseudoPrime.Analysis.gaussianMR6FifthsConductor]
    dsimp only [R0, A, B, PseudoPrime.Analysis.gaussianMR6FifthsConductor] at *
    nlinarith only [hDscaled, hbetascaled, hlinear, hDcon]
  have hEq := PseudoPrime.Analysis.gaussianMR6FifthsRadius_equation hL
  have hfactorpos :
    0 <
      PseudoPrime.Analysis.gaussianMR6FifthsD -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s) := by
    have hsum : 17 ≤ Real.sqrt R0 + s := by
      have hsqrt0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      linarith only [hsqrt0, hroot17]
    have hmul :
      (639999 / 1000000 : ℝ) * 17 ≤
        PseudoPrime.Analysis.gaussianMR6FifthsD * (Real.sqrt R0 + s) := by
      calc
        (639999 / 1000000 : ℝ) * 17 ≤ PseudoPrime.Analysis.gaussianMR6FifthsD * 17 := by
          nlinarith only [hD]
        _ ≤ PseudoPrime.Analysis.gaussianMR6FifthsD * (Real.sqrt R0 + s) :=
          mul_le_mul_of_nonneg_left hsum
            (PseudoPrime.Analysis.gaussianMR6Fifths_coefficients_pos.1.le)
    have hquot :
      PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s) <
        PseudoPrime.Analysis.gaussianMR6FifthsD :=
      (div_lt_iff₀ (by linarith only [hsum])).2 (by nlinarith only [hmul, hBeta])
    exact sub_pos.mpr hquot
  have hsumpos : 0 < Real.sqrt R0 + s := add_pos (Real.sqrt_pos.2 hRpos) hspos
  have hsqrtSq : (Real.sqrt R0) ^ 2 = R0 := Real.sq_sqrt (le_of_lt hRpos)
  have hsqrtDiff : Real.sqrt R0 - s = (R0 - s ^ 2) / (Real.sqrt R0 + s) := by
    field_simp [hsumpos.ne']
    nlinarith only [hsqrtSq]
  have hidentity :
    PseudoPrime.Analysis.gaussianMR6FifthsD * R0 -
        PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta * Real.sqrt R0 -
        29 -
        (PseudoPrime.Analysis.gaussianMR6FifthsD * r -
          PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
          PseudoPrime.Analysis.gaussianMR6FifthsBeta * s -
          29) =
      (R0 - r) *
        (PseudoPrime.Analysis.gaussianMR6FifthsD -
          PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) := by
    rw [hsq]
    calc
      _ =
          PseudoPrime.Analysis.gaussianMR6FifthsD * (R0 - s ^ 2) -
            PseudoPrime.Analysis.gaussianMR6FifthsBeta * (Real.sqrt R0 - s) :=
        by ring
      _ =
          (R0 - s ^ 2) *
            (PseudoPrime.Analysis.gaussianMR6FifthsD -
              PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) :=
        by
        rw [hsqrtDiff]
        ring
  have hactual :
    PseudoPrime.Analysis.gaussianMR6FifthsD * r -
        PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta * s -
        29 =
      0 := by
    dsimp only [r, s]
    linarith only [hEq]
  have hdiffpos : 0 < R0 - r := by
    by_contra hnot
    have hle : R0 - r ≤ 0 := le_of_not_gt hnot
    have hprod :
      (R0 - r) *
          (PseudoPrime.Analysis.gaussianMR6FifthsD -
            PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) ≤
        0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hfactorpos.le
    have hId := hidentity
    rw [hactual, sub_zero] at hId
    rw [hId] at hmargin
    exact (not_lt_of_ge hprod) hmargin
  have hout : r < R0 := by linarith only [hdiffpos]
  dsimp only [r, R0] at hout ⊢
  exact hout

/-- The constant-18 Gaussian radius lies below the scaled index-100 Gamma
comparison radius from logarithmic scale 330 onward. -/
theorem gaussianMR18Radius_lt_gammaIndex100Comparison {L : ℝ} (hL : 330 ≤ L) :
    PseudoPrime.Analysis.gaussianMR18Radius L <
      (287 / 200 : ℝ) * ((11783423 / 25000000 : ℝ) / (91 / 100) * L + 14 / 5) := by
  let R0 := (287 / 200 : ℝ) * ((11783423 / 25000000 : ℝ) / (91 / 100) * L + 14 / 5)
  let s := PseudoPrime.Analysis.gaussianMR18Root L
  let r := PseudoPrime.Analysis.gaussianMR18Radius L
  let A :=
    (639999 / 1000000 : ℝ) * (287 / 200) * ((11783423 / 25000000 : ℝ) / (91 / 100)) -
      (161 / 400 : ℝ) -
      (257 / 500) * (507 / 10000)
  let B := (639999 / 1000000 : ℝ) * (287 / 200) * (14 / 5)
  have hLpos : 0 < L := by linarith only [hL]
  have hspos : 0 < s := PseudoPrime.Analysis.gaussianMR18Root_pos (by linarith only [hL])
  have hsq : r = s ^ 2 := by dsimp only [r, PseudoPrime.Analysis.gaussianMR18Radius, s]
  have hradius := PseudoPrime.Analysis.gaussianMR18Radius_lower (by linarith only [hL])
  have hroot15 := PseudoPrime.Analysis.gaussianMR18Root_lower_15 (by linarith only [hL])
  have hRpos : 0 < R0 := by
    dsimp only [R0]; positivity
  have hR0upper : Real.sqrt R0 ≤ (507 / 10000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · dsimp only [R0]
      nlinarith only [hL]
  have hD : (639999 / 1000000 : ℝ) ≤ PseudoPrime.Analysis.gaussianMR6FifthsD := by
    norm_num only [PseudoPrime.Analysis.gaussianMR6FifthsD,
      PseudoPrime.Analysis.gaussianMR6FifthsIndex, PseudoPrime.Analysis.gaussianMR6FifthsMass,
      PseudoPrime.Analysis.gaussianMR6FifthsEndpoint]
  have hBeta : PseudoPrime.Analysis.gaussianMR6FifthsBeta ≤ (257 / 500 : ℝ) := by
    norm_num only [PseudoPrime.Analysis.gaussianMR6FifthsBeta,
      PseudoPrime.Analysis.gaussianMR6FifthsIndex, PseudoPrime.Analysis.gaussianMR6FifthsMass]
  have hApos : 0 < A := by norm_num only [A]
  have hA330 : 0 < A * 330 + B - 18 := by norm_num only [A, B]
  have hlinear : 0 < A * L + B - 18 := by
    have hL' : 0 ≤ L - 330 := by linarith only [hL]
    have hstep := mul_nonneg hApos.le hL'
    dsimp only [A, B] at hstep hA330 ⊢
    nlinarith only [hstep, hA330]
  have hmargin :
    0 <
      PseudoPrime.Analysis.gaussianMR6FifthsD * R0 -
        PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta * Real.sqrt R0 -
        18 := by
    have hDscaled := mul_le_mul_of_nonneg_right hD (le_of_lt hRpos)
    have hbetascaled :=
      mul_le_mul hBeta hR0upper (Real.sqrt_nonneg R0) (by norm_num only : (0 : ℝ) ≤ 257 / 500)
    have hDcon : (161 / 400 : ℝ) = PseudoPrime.Analysis.gaussianMR6FifthsConductor := by
      norm_num only [PseudoPrime.Analysis.gaussianMR6FifthsConductor]
    dsimp only [R0, A, B, PseudoPrime.Analysis.gaussianMR6FifthsConductor] at *
    nlinarith only [hDscaled, hbetascaled, hlinear, hDcon]
  have hEq := PseudoPrime.Analysis.gaussianMR18Radius_equation (by linarith only [hL])
  have hfactorpos :
    0 <
      PseudoPrime.Analysis.gaussianMR6FifthsD -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s) := by
    have hsum : 15 ≤ Real.sqrt R0 + s := by
      have hsqrt0 : 0 ≤ Real.sqrt R0 := Real.sqrt_nonneg _
      linarith only [hsqrt0, hroot15]
    have hmul :
      (639999 / 1000000 : ℝ) * 15 ≤
        PseudoPrime.Analysis.gaussianMR6FifthsD * (Real.sqrt R0 + s) := by
      calc
        (639999 / 1000000 : ℝ) * 15 ≤ PseudoPrime.Analysis.gaussianMR6FifthsD * 15 := by
          nlinarith only [hD]
        _ ≤ PseudoPrime.Analysis.gaussianMR6FifthsD * (Real.sqrt R0 + s) :=
          mul_le_mul_of_nonneg_left hsum
            (PseudoPrime.Analysis.gaussianMR6Fifths_coefficients_pos.1.le)
    have hquot :
      PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s) <
        PseudoPrime.Analysis.gaussianMR6FifthsD :=
      (div_lt_iff₀ (by linarith only [hsum])).2 (by nlinarith only [hmul, hBeta])
    exact sub_pos.mpr hquot
  have hsumpos : 0 < Real.sqrt R0 + s := add_pos (Real.sqrt_pos.2 hRpos) hspos
  have hsqrtSq : (Real.sqrt R0) ^ 2 = R0 := Real.sq_sqrt (le_of_lt hRpos)
  have hsqrtDiff : Real.sqrt R0 - s = (R0 - s ^ 2) / (Real.sqrt R0 + s) := by
    field_simp [hsumpos.ne']
    nlinarith only [hsqrtSq]
  have hidentity :
    PseudoPrime.Analysis.gaussianMR6FifthsD * R0 -
        PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta * Real.sqrt R0 -
        18 -
        (PseudoPrime.Analysis.gaussianMR6FifthsD * r -
          PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
          PseudoPrime.Analysis.gaussianMR6FifthsBeta * s -
          18) =
      (R0 - r) *
        (PseudoPrime.Analysis.gaussianMR6FifthsD -
          PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) := by
    rw [hsq]
    calc
      _ =
          PseudoPrime.Analysis.gaussianMR6FifthsD * (R0 - s ^ 2) -
            PseudoPrime.Analysis.gaussianMR6FifthsBeta * (Real.sqrt R0 - s) :=
        by ring
      _ =
          (R0 - s ^ 2) *
            (PseudoPrime.Analysis.gaussianMR6FifthsD -
              PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) :=
        by
        rw [hsqrtDiff]
        ring
  have hactual :
    PseudoPrime.Analysis.gaussianMR6FifthsD * r -
        PseudoPrime.Analysis.gaussianMR6FifthsConductor * L -
        PseudoPrime.Analysis.gaussianMR6FifthsBeta * s -
        18 =
      0 := by
    dsimp only [r, s]
    linarith only [hEq]
  have hdiffpos : 0 < R0 - r := by
    by_contra hnot
    have hle : R0 - r ≤ 0 := le_of_not_gt hnot
    have hprod :
      (R0 - r) *
          (PseudoPrime.Analysis.gaussianMR6FifthsD -
            PseudoPrime.Analysis.gaussianMR6FifthsBeta / (Real.sqrt R0 + s)) ≤
        0 :=
      mul_nonpos_of_nonpos_of_nonneg hle hfactorpos.le
    have hId := hidentity
    rw [hactual, sub_zero] at hId
    rw [hId] at hmargin
    exact (not_lt_of_ge hprod) hmargin
  have hout : r < R0 := by linarith only [hdiffpos]
  dsimp only [r, R0] at hout ⊢
  exact hout

/-- From logarithmic scale 330 onward, the constant-18 Gaussian witness bound
is strictly below the index-100 Gamma bound. -/
theorem gaussianMR18Bound_lt_gammaIndex100Bound {L : ℝ} (hL : 330 ≤ L) :
    PseudoPrime.Analysis.gaussianMR18Bound L < gammaIndex100Bound L := by
  have hrad18 := gaussianMR18Radius_lt_gammaIndex100Comparison hL
  have hgamma := gammaIndex100Radius_ge_affine hL
  have hrad :
    PseudoPrime.Analysis.gaussianMR18Radius L < (287 / 200 : ℝ) * gammaIndex100Radius L := by
    have hmul := mul_le_mul_of_nonneg_left hgamma (by norm_num only : (0 : ℝ) ≤ 287 / 200)
    exact hrad18.trans_le hmul
  have hLpos : 0 < L := by linarith only [hL]
  have hr18pos : 0 < PseudoPrime.Analysis.gaussianMR18Radius L := by
    have hr18lower := PseudoPrime.Analysis.gaussianMR18Radius_lower (by linarith only [hL])
    nlinarith only [hr18lower, hL]
  have hGammaPos := (gammaIndex100Radius_properties hL).1
  have hsq :
    (PseudoPrime.Analysis.gaussianMR18Radius L) ^ 2 <
      ((287 / 200 : ℝ) * gammaIndex100Radius L) ^ 2 :=
    (sq_lt_sq₀ hr18pos.le (mul_nonneg (by norm_num only) hGammaPos.le)).2 hrad
  have hcoeff : (6 / 5 : ℝ) * (287 / 200) ^ 2 < 99 / 40 := by norm_num only
  have hscale :
    (6 / 5 : ℝ) * (PseudoPrime.Analysis.gaussianMR18Radius L) ^ 2 <
      (99 / 40 : ℝ) * (gammaIndex100Radius L) ^ 2 := by
    have hleft := mul_lt_mul_of_pos_left hsq (by norm_num only : (0 : ℝ) < 6 / 5)
    nlinarith only [hleft, hcoeff, sq_nonneg (gammaIndex100Radius L)]
  simpa only [PseudoPrime.Analysis.gaussianMR18Bound, gammaIndex100Bound] using hscale

/-- For `L ≥ 500`, the 6/5 Gaussian witness bound is strictly below the
index-100 Gamma bound. The comparison uses the analysis12 rational scale
`287/200` and its strict coefficient inequality. -/
theorem gaussianMR6FifthsBound_lt_gammaIndex100Bound {L : ℝ} (hL : 500 ≤ L) :
    PseudoPrime.Analysis.gaussianMR6FifthsBound L < gammaIndex100Bound L := by
  have hrad6 := gaussianMR6FifthsRadius_lt_gammaIndex100Comparison hL
  have hgamma := gammaIndex100Radius_ge_affine (by linarith only [hL])
  have hrad :
    PseudoPrime.Analysis.gaussianMR6FifthsRadius L < (287 / 200 : ℝ) * gammaIndex100Radius L := by
    have hmul := mul_le_mul_of_nonneg_left hgamma (by norm_num only : (0 : ℝ) ≤ 287 / 200)
    exact hrad6.trans_le hmul
  have hLpos : 0 < L := by linarith only [hL]
  have hr6pos : 0 < PseudoPrime.Analysis.gaussianMR6FifthsRadius L := by
    exact
      lt_of_lt_of_le (mul_pos (by norm_num only : (0 : ℝ) < 5 / 8) hLpos)
        (PseudoPrime.Analysis.gaussianMR6FifthsRadius_lower hL)
  have hGammaPos := (gammaIndex100Radius_properties (by linarith only [hL])).1
  have hsq :
    (PseudoPrime.Analysis.gaussianMR6FifthsRadius L) ^ 2 <
      ((287 / 200 : ℝ) * gammaIndex100Radius L) ^ 2 :=
    (sq_lt_sq₀ hr6pos.le
          (mul_nonneg (by norm_num only)
            (gammaIndex100Radius_properties (by linarith only [hL])).1.le)).2
      hrad
  have hcoeff : (6 / 5 : ℝ) * (287 / 200) ^ 2 < 99 / 40 := by norm_num only
  have hscale :
    (6 / 5 : ℝ) * (PseudoPrime.Analysis.gaussianMR6FifthsRadius L) ^ 2 <
      (99 / 40 : ℝ) * (gammaIndex100Radius L) ^ 2 := by
    have hleft := mul_lt_mul_of_pos_left hsq (by norm_num only : (0 : ℝ) < 6 / 5)
    nlinarith only [hleft, hcoeff, sq_nonneg (gammaIndex100Radius L)]
  simpa only [PseudoPrime.Analysis.gaussianMR6FifthsBound, gammaIndex100Bound] using hscale

end PseudoPrime.PrimeTestBounds.MillerRabin
