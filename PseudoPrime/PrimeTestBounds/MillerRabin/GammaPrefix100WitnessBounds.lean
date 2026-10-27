/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaLinearCutoffBounds
public import PseudoPrime.LLS.GammaCheckpoint1000
public import PseudoPrime.LLS.GammaCheckpoint50000
public import PseudoPrime.LLS.RiemannOneSidedCheckpoint

/-! # Retained-prefix index-100 Gamma witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The 50000-prefix radius grows at least as `L / 2 + 15 / 2` from
logarithmic scale 270. This lower bound keeps the prefix applicability
threshold inside the radius-based cutoff. -/
theorem gammaPrefix100Radius_lower_seven_half {L : ℝ} (hL : 270 ≤ L) :
    L / 2 + 15 / 2 ≤ gammaPrefix100Radius L (28493 / 5000) := by
  let A : ℝ := (11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * (28493 / 5000 : ℝ))
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let a : ℝ := 91 / 100
  let t : ℝ := L / 2 + 15 / 2
  have hF : a * t ^ 2 - A * t - S ≤ 0 := by
    dsimp only [A, S, a, t]
    nlinarith only [hL, sq_nonneg (L - 270)]
  have hpos : 0 ≤ 2 * a * t - A := by
    dsimp only [A, a, t]
    nlinarith only [hL]
  have hrad : (2 * a * t - A) ^ 2 ≤ A ^ 2 + 4 * a * S := by
    dsimp only [a] at hF ⊢
    nlinarith only [hF]
  have hsqrt : 2 * a * t - A ≤ Real.sqrt (A ^ 2 + 4 * a * S) := Real.le_sqrt_of_sq_le hrad
  have hden : 0 < 2 * a := by norm_num only [a]
  have hroot :
    gammaPrefix100Radius L (28493 / 5000) = (A + Real.sqrt (A ^ 2 + 4 * a * S)) / (2 * a) := by
    dsimp only [gammaPrefix100Radius, A, S, a]
  rw [hroot]
  apply (le_div_iff₀ hden).2
  dsimp only [a, t] at hsqrt ⊢
  linarith only [hsqrt]

/-- A prefix lower bound and the matching positive root make the signed
index-100 Gamma budget strictly smaller than the normalized main term. -/
theorem gammaPrefix100_signed_budget_gap {n : ℕ} [NeZero n] (hRH : RiemannHypothesis) {L C b : ℝ}
    (hlog : Real.log n = L) (hL : 240 ≤ L) (hD : 0 ≤ 591 / 50 - 2 * C)
    (hprefix : C ≤ ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k) :
    gammaSignedPrefixMRBudget n n (gammaPrefix100Radius L C ^ 2) b <
      (91 / 100 : ℝ) * gammaPrefix100Radius L C - 1 - 14 / gammaPrefix100Radius L C := by
  let r : ℝ := gammaPrefix100Radius L C
  let x : ℝ := r ^ 2
  have hrprop := gammaPrefix100Radius_properties hL hD
  have hr : 0 < r := by
    dsimp only [r]; exact hrprop.1
  have hrhalf : L / 2 ≤ r := by
    dsimp only [r]
    exact gammaPrefix100Radius_lower_half hL hD
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hrhalf, hL]
  have hsqrt : Real.sqrt x = r := by
    dsimp only [x]
    rw [Real.sqrt_sq hr.le]
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x b
  rw [hlog] at hu
  have hscaled := mul_le_mul_of_nonneg_left hprefix (by norm_num only : (0 : ℝ) ≤ 2)
  have hbudget :
    gammaSignedPrefixMRBudget n n x b <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget] at hu ⊢
    linarith only [hu, hscaled]
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only at hx ⊢; exact hx)
  have htail := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
  have htail' : 43 * x ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    calc
      _ ≤ 43 * (1 / r) := by simpa only [hsqrt, one_mul] using htail
      _ = 43 / r := by ring
  have hrecip : ((7 / 6 : ℝ) * L + 4) / r + 43 / r = ((7 / 6 : ℝ) * L + 47) / r := by
    rw [← add_div]
    ring
  have hbudget' :
    gammaSignedPrefixMRBudget n n x b <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 47) / r := by
    rw [hsqrt] at hbudget
    have htailLoss :
      ((7 / 6 : ℝ) * L + 4) / r + 43 * x ^ (-9 / 16 : ℝ) ≤ ((7 / 6 : ℝ) * L + 47) / r := by
      calc
        _ = 43 * x ^ (-9 / 16 : ℝ) + ((7 / 6 : ℝ) * L + 4) / r := by ring
        _ ≤ 43 / r + ((7 / 6 : ℝ) * L + 4) / r := add_le_add_left htail' _
        _ = ((7 / 6 : ℝ) * L + 4) / r + 43 / r := by ring
        _ = _ := hrecip
    linarith only [hbudget, htailLoss]
  have hroot := gammaPrefix100Radius_budget_eq hL hD
  have hroot' :
    (91 / 100 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - (591 / 50 - 2 * C) -
        ((7 / 6 : ℝ) * L + 61) / r =
      0 := by
    simpa only [r] using hroot
  have hconstant : 541 / 50 - 2 * C = (591 / 50 - 2 * C) - 1 := by ring
  have hpole : ((7 / 6 : ℝ) * L + 47) / r + 14 / r = ((7 / 6 : ℝ) * L + 61) / r := by
    rw [← add_div]
    ring
  nlinarith only [hbudget', hroot', hconstant, hpole]

/-- A retained-prefix budget remains valid at every radius at least its
positive root. The common cost decreases with the radius, while the normalized
index-100 margin increases. -/
theorem gammaPrefix100_signed_budget_gap_of_radius {n : ℕ} [NeZero n] (hRH : RiemannHypothesis)
    {L C b r : ℝ} (hlog : Real.log n = L) (hL : 240 ≤ L) (hD : 0 ≤ 591 / 50 - 2 * C)
    (hprefix : C ≤ ∑ k ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight k)
    (hr : gammaPrefix100Radius L C ≤ r) :
    gammaSignedPrefixMRBudget n n (r ^ 2) b < (91 / 100 : ℝ) * r - 1 - 14 / r := by
  let r0 : ℝ := gammaPrefix100Radius L C
  let x : ℝ := r ^ 2
  have hr0pos : 0 < r0 := by
    dsimp only [r0]
    exact (gammaPrefix100Radius_properties hL hD).1
  change r0 ≤ r at hr
  have hrpos : 0 < r := hr0pos.trans_le hr
  have hrhalf : L / 2 ≤ r := by exact (gammaPrefix100Radius_lower_half hL hD).trans hr
  have hx : 1 ≤ x := by
    dsimp only [x]
    nlinarith only [hrhalf, hL]
  have hsqrt : Real.sqrt x = r := by
    dsimp only [x]
    rw [Real.sqrt_sq hrpos.le]
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hRH n n x b
  rw [hlog] at hu
  have hscaled := mul_le_mul_of_nonneg_left hprefix (by norm_num only : (0 : ℝ) ≤ 2)
  have hbudget :
    gammaSignedPrefixMRBudget n n x b <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget] at hu ⊢
    linarith only [hu, hscaled]
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only at hx ⊢; exact hx)
  have htail := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
  have htail' : 43 * x ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    calc
      _ ≤ 43 * (1 / r) := by simpa only [hsqrt, one_mul] using htail
      _ = 43 / r := by ring
  have hbudget' :
    gammaSignedPrefixMRBudget n n x b <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 47) / r := by
    rw [hsqrt] at hbudget
    have htailLoss :
      ((7 / 6 : ℝ) * L + 4) / r + 43 * x ^ (-9 / 16 : ℝ) ≤ ((7 / 6 : ℝ) * L + 47) / r := by
      calc
        _ = 43 * x ^ (-9 / 16 : ℝ) + ((7 / 6 : ℝ) * L + 4) / r := by ring
        _ ≤ 43 / r + ((7 / 6 : ℝ) * L + 4) / r := add_le_add_left htail' _
        _ = ((7 / 6 : ℝ) * L + 4) / r + 43 / r := by ring
        _ = _ := by
          rw [← add_div]; ring
    linarith only [hbudget, htailLoss]
  have hroot := gammaPrefix100Radius_budget_eq hL hD
  have hroot' :
    (91 / 100 : ℝ) * r0 - (11783423 / 25000000 : ℝ) * L - (591 / 50 - 2 * C) -
        ((7 / 6 : ℝ) * L + 61) / r0 =
      0 := by
    dsimp only [r0]
    exact hroot
  have hrecip : 1 / r ≤ 1 / r0 := one_div_le_one_div_of_le hr0pos hr
  have hA : 0 ≤ (7 / 6 : ℝ) * L + 61 := by nlinarith only [hL]
  have hmargin :
    (91 / 100 : ℝ) * r0 - ((7 / 6 : ℝ) * L + 61) / r0 ≤
      (91 / 100 : ℝ) * r - ((7 / 6 : ℝ) * L + 61) / r := by
    have hlinear := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 91 / 100) (sub_nonneg.mpr hr)
    have hpole := mul_nonneg hA (sub_nonneg.mpr hrecip)
    have hid :
      ((91 / 100 : ℝ) * r - ((7 / 6 : ℝ) * L + 61) / r) -
          ((91 / 100 : ℝ) * r0 - ((7 / 6 : ℝ) * L + 61) / r0) =
        (91 / 100 : ℝ) * (r - r0) + ((7 / 6 : ℝ) * L + 61) * (1 / r0 - 1 / r) := by
      field_simp [hr0pos.ne', hrpos.ne']
      ring
    apply sub_nonneg.mp
    rw [hid]
    exact add_nonneg hlinear hpole
  have hconstant : 541 / 50 - 2 * C = (591 / 50 - 2 * C) - 1 := by ring
  have hpole : ((7 / 6 : ℝ) * L + 47) / r + 14 / r = ((7 / 6 : ℝ) * L + 61) / r := by
    rw [← add_div]
    ring
  have hmargin' :
    (11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C) + ((7 / 6 : ℝ) * L + 47) / r ≤
      (91 / 100 : ℝ) * r - 14 / r := by
    nlinarith only [hmargin, hpole, hroot']
  have hbudget'' :
    gammaSignedPrefixMRBudget n n x b <
      (11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C) - 1 + ((7 / 6 : ℝ) * L + 47) / r := by
    linarith only [hbudget', hconstant]
  have hmargin'' :
    (11783423 / 25000000 : ℝ) * L + (591 / 50 - 2 * C) - 1 + ((7 / 6 : ℝ) * L + 47) / r ≤
      (91 / 100 : ℝ) * r - 1 - 14 / r := by
    linarith only [hmargin']
  exact hbudget''.trans_le hmargin''

/-- From logarithmic scale 240, the 1000-term Gamma prefix gives an
index-100 witness below its retained-prefix curve for every subgroup of
index at least one hundred containing all strong-MR passes. -/
theorem exists_prime_witness_le_gammaIndex100Prefix1000_of_subgroup {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 1000 ((99 / 40 : ℝ) * gammaPrefix100Radius (Real.log n) (203 / 50) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hQ : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 46000 := by omega
    have hnltR : (n : ℝ) < 46000 := by exact_mod_cast hnlt
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn0) hnltR
    linarith only [hlog, Analysis.log_46000_lt_eleven, hL]
  let r := gammaPrefix100Radius (Real.log n) (203 / 50)
  have hD : 0 ≤ (591 / 50 : ℝ) - 2 * (203 / 50) := by norm_num only
  have hL240 : 240 ≤ Real.log n := hL
  have hrpos : 0 < r := (gammaPrefix100Radius_properties hL240 hD).1
  have hr120 : 120 ≤ r := by
    have hhalf := gammaPrefix100Radius_lower_half hL hD
    dsimp only [r]
    linarith only [hhalf, hL]
  have hr : 1 ≤ r := by linarith only [hr120]
  have hx : 2 ≤ r ^ 2 := by nlinarith only [hr120, sq_nonneg (r - 120)]
  have hcut : (1000 : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 := by
    have hsquare : (120 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith only [hr120, sq_nonneg (r - 120)]
    norm_num only at hsquare ⊢
    nlinarith only [hsquare]
  have hprefix := LLS.gamma_prefix1000_lower_halfline hGRH.riemann (le_refl (1000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hprefix' :
    (203 / 50 : ℝ) ≤ ∑ k ∈ Finset.Ioc 0 ⌊(1000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    norm_num only [Nat.floor_ofNat]
    exact hprefix
  have hgap :=
    gammaPrefix100_signed_budget_gap (n := n) hGRH.riemann (L := Real.log n) (C := 203 / 50) (b :=
      (1000 : ℝ)) rfl hL hD hprefix'
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_of_gamma_index100_gap hn hnOdd hGRH hQ H hidx hHpass hr hx
      (by norm_num only) hcut hgap
  refine ⟨p, hp, ?_, hreject⟩
  exact hbound.trans (le_max_right _ _)

/-- From logarithmic scale 270, the retained 50000-term Gamma prefix gives an
index-100 witness below its own clipped curve for every pass-containing
subgroup of index at least one hundred. -/
theorem exists_prime_witness_le_gammaIndex100Prefix50000_of_subgroup {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hL : 270 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 50000 ((99 / 40 : ℝ) * gammaPrefix100Radius (Real.log n) (28493 / 5000) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hlog20000 : Real.log (20000 : ℝ) < 11 := by
    exact (Real.log_lt_log (by norm_num only) (by norm_num only)).trans Analysis.log_46000_lt_eleven
  have hQ : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 20000 := by omega
    have hnltR : (n : ℝ) < 20000 := by exact_mod_cast hnlt
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn0) hnltR
    linarith only [hlog, hlog20000, hL]
  let r := gammaPrefix100Radius (Real.log n) (28493 / 5000)
  have hD : 0 ≤ (591 / 50 : ℝ) - 2 * (28493 / 5000) := by norm_num only
  have hL240 : 240 ≤ Real.log n := by exact le_trans (by norm_num only : (240 : ℝ) ≤ 270) hL
  have hrpos : 0 < r := (gammaPrefix100Radius_properties hL240 hD).1
  have hr : 1 ≤ r := by
    have hhalf := gammaPrefix100Radius_lower_half hL240 hD
    dsimp only [r]
    linarith only [hhalf, hL]
  have hr142 : (285 / 2 : ℝ) ≤ r := by
    have hlower := gammaPrefix100Radius_lower_seven_half hL
    linarith only [hlower, hL]
  have hx : 2 ≤ r ^ 2 := by nlinarith only [hr142, sq_nonneg (r - 285 / 2)]
  have hcut : (50000 : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 := by
    nlinarith only [hr142, sq_nonneg (r - 285 / 2)]
  have hprefix := LLS.gamma_prefix50000_lower_asymmetric hGRH.riemann (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hprefix' :
    (28493 / 5000 : ℝ) ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    norm_num only [Nat.floor_ofNat]
    exact hprefix
  have hgap :=
    gammaPrefix100_signed_budget_gap (n := n) hGRH.riemann (L := Real.log n) (C := 28493 / 5000)
      (b := (50000 : ℝ)) rfl hL240 hD hprefix'
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_of_gamma_index100_gap hn hnOdd hGRH hQ H hidx hHpass hr hx
      (by norm_num only) hcut hgap
  refine ⟨p, hp, ?_, hreject⟩
  exact hbound.trans (le_max_right _ _)

/-- From logarithmic scale 240, the 50000-term Gamma prefix gives a witness
below its clipped retained-prefix curve. If the positive root lies below the
cutoff radius, use that cutoff radius in the signed budget. -/
theorem exists_prime_witness_le_gammaIndex100Prefix50000_clipped_of_subgroup {n : ℕ} [NeZero n]
    (hn : 1 < n) (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 50000 ((99 / 40 : ℝ) * gammaPrefix100Radius (Real.log n) (28493 / 5000) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hQ : 20000 ≤ n := by
    by_contra hnot
    have hnlt : n < 46000 := by omega
    have hnltR : (n : ℝ) < 46000 := by exact_mod_cast hnlt
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr hn0) hnltR
    linarith only [hlog, Analysis.log_46000_lt_eleven, hL]
  let r0 : ℝ := gammaPrefix100Radius (Real.log n) (28493 / 5000)
  let cutoff : ℝ := Real.sqrt ((2000000 : ℝ) / 99)
  let r : ℝ := max r0 cutoff
  have hD : 0 ≤ (591 / 50 : ℝ) - 2 * (28493 / 5000) := by norm_num only
  have hL240 : 240 ≤ Real.log n := hL
  have hr0pos : 0 < r0 := by
    dsimp only [r0]
    exact (gammaPrefix100Radius_properties hL240 hD).1
  have hcutoffpos : 0 < cutoff := by
    dsimp only [cutoff]
    exact Real.sqrt_pos.2 (by norm_num only)
  have hcutoffsq : cutoff ^ 2 = (2000000 : ℝ) / 99 := by
    dsimp only [cutoff]
    rw [Real.sq_sqrt (by norm_num only)]
  have hrroot : r0 ≤ r := by
    dsimp only [r]; exact le_max_left _ _
  have hrcutoff : cutoff ≤ r := by
    dsimp only [r]; exact le_max_right _ _
  have hrpos : 0 < r := hr0pos.trans_le hrroot
  have hrLhalf : Real.log n / 2 ≤ r := by
    exact (gammaPrefix100Radius_lower_half hL240 hD).trans hrroot
  have hr120 : 120 ≤ r := by linarith only [hrLhalf, hL]
  have hx : 2 ≤ r ^ 2 := by nlinarith only [hr120, sq_nonneg (r - 120)]
  have hcutoffSqLe : cutoff ^ 2 ≤ r ^ 2 := by nlinarith only [hrcutoff, hcutoffpos, hrpos]
  have hcut : (50000 : ℝ) ≤ (99 / 40 : ℝ) * r ^ 2 := by
    rw [hcutoffsq] at hcutoffSqLe
    nlinarith only [hcutoffSqLe]
  have hprefix := LLS.gamma_prefix50000_lower_asymmetric hGRH.riemann (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hprefix' :
    (28493 / 5000 : ℝ) ≤
      ∑ k ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight k := by
    norm_num only [Nat.floor_ofNat]
    exact hprefix
  have hgap :=
    gammaPrefix100_signed_budget_gap_of_radius (n := n) hGRH.riemann (L := Real.log n) (C :=
      (28493 / 5000 : ℝ)) (b := (50000 : ℝ)) (r := r) rfl hL240 hD hprefix'
      (by
        dsimp only [r, r0]; exact le_max_left _ _)
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_of_gamma_index100_gap hn hnOdd hGRH hQ H hidx hHpass
      (by linarith only [hrLhalf, hL]) hx (by norm_num only) hcut hgap
  refine ⟨p, hp, ?_, hreject⟩
  have hcurve : max 50000 ((99 / 40 : ℝ) * r ^ 2) = max 50000 ((99 / 40 : ℝ) * r0 ^ 2) := by
    rcases le_total r0 cutoff with hsmall | hlarge
    · have hrEq : r = cutoff := by
        dsimp only [r]; exact max_eq_right hsmall
      have hs : r0 ^ 2 ≤ cutoff ^ 2 := by nlinarith only [hsmall, hr0pos, hcutoffpos]
      have hsmallCurve : (99 / 40 : ℝ) * r0 ^ 2 ≤ 50000 := by
        rw [hcutoffsq] at hs
        nlinarith only [hs]
      have hcutCurve : (99 / 40 : ℝ) * cutoff ^ 2 = 50000 := by
        rw [hcutoffsq]
        norm_num only
      rw [hrEq, hcutCurve, max_self, max_eq_left hsmallCurve]
    · have hrEq : r = r0 := by
        dsimp only [r]; exact max_eq_left hlarge
      rw [hrEq]
  calc
    (p : ℝ) ≤ max 50000 ((99 / 40 : ℝ) * r ^ 2) := hbound.trans (le_max_right _ _)
    _ = max 50000 ((99 / 40 : ℝ) * r0 ^ 2) := hcurve
    _ = _ := by dsimp only [r0]

/-- For every pass-containing subgroup of index at least 100, one of the two
retained Gamma prefixes supplies a witness below their minimum envelope. -/
theorem exists_prime_witness_le_gammaIndex100PrefixUpper_of_subgroup {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let upper1000 := max 1000 ((99 / 40 : ℝ) * gammaPrefix100Radius (Real.log n) (203 / 50) ^ 2)
  let upper50000 := max 50000 ((99 / 40 : ℝ) * gammaPrefix100Radius (Real.log n) (28493 / 5000) ^ 2)
  by_cases hcmp : upper1000 ≤ upper50000
  · obtain ⟨p, hp, hbound, hreject⟩ :=
      exists_prime_witness_le_gammaIndex100Prefix1000_of_subgroup hn hnOdd hGRH H hidx hHpass hL
    refine ⟨p, hp, ?_, hreject⟩
    change (p : ℝ) ≤ min upper1000 upper50000
    rw [min_eq_left hcmp]
    exact hbound
  · have hcmp' : upper50000 ≤ upper1000 := le_of_not_ge hcmp
    obtain ⟨p, hp, hbound, hreject⟩ :=
      exists_prime_witness_le_gammaIndex100Prefix50000_clipped_of_subgroup hn hnOdd hGRH H hidx
        hHpass hL
    refine ⟨p, hp, ?_, hreject⟩
    change (p : ℝ) ≤ min upper1000 upper50000
    rw [min_eq_right hcmp']
    exact hbound

/-- The local finite-index envelope `0.3 L²` is below both clipped
Gamma prefix bounds from scale 240 onward, hence below their minimum. -/
theorem local_three_tenths_le_gammaIndex100PrefixUpper {L : ℝ} (hL : 240 ≤ L) :
    (3 / 10 : ℝ) * L ^ 2 ≤ gammaIndex100PrefixUpper L := by
  have hD0 : 0 ≤ (591 / 50 : ℝ) - 2 * (203 / 50) := by norm_num only
  have hD1 : 0 ≤ (591 / 50 : ℝ) - 2 * (28493 / 5000) := by norm_num only
  have hr0 := gammaPrefix100Radius_lower_half hL hD0
  have hr1 := gammaPrefix100Radius_lower_half hL hD1
  have hbound0 :
    (3 / 10 : ℝ) * L ^ 2 ≤ max 1000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (203 / 50) ^ 2) := by
    have hs : (L / 2) ^ 2 ≤ gammaPrefix100Radius L (203 / 50) ^ 2 := by nlinarith only [hr0, hL]
    have hquad : (3 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * gammaPrefix100Radius L (203 / 50) ^ 2 := by
      nlinarith only [hs]
    exact hquad.trans (le_max_right _ _)
  have hbound1 :
    (3 / 10 : ℝ) * L ^ 2 ≤
      max 50000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (28493 / 5000) ^ 2) := by
    have hs : (L / 2) ^ 2 ≤ gammaPrefix100Radius L (28493 / 5000) ^ 2 := by nlinarith only [hr1, hL]
    have hquad :
      (3 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * gammaPrefix100Radius L (28493 / 5000) ^ 2 := by
      nlinarith only [hs]
    exact hquad.trans (le_max_right _ _)
  exact le_min hbound0 hbound1

/-- The finite-index classification yields a witness below the `U₁₀₀`
candidate or a uniform Korselt triple. The local branch is absorbed by the
two clipped retained-prefix curves. -/
theorem finite_index_witness_or_uniform_korselt_triple_gammaIndex100Prefix {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ)
    (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  rcases finite_index_witness_or_uniform_korselt_triple_log240 hnOdd hcomp H hH hi hGRH hL with
    hlocal | htriple
  · obtain ⟨p, hp, hbound, hfail⟩ := hlocal
    exact Or.inl ⟨p, hp, hbound.trans (local_three_tenths_le_gammaIndex100PrefixUpper hL), hfail⟩
  · exact Or.inr htriple

/-- Under GRH, every odd composite with logarithm at least 240 either has a
prime witness below the two-prefix `U₁₀₀` curve or is a uniform Korselt
three-prime remainder. Split on the Fermat subgroup index. -/
theorem exists_prime_witness_le_gammaIndex100PrefixUpper_or_uniform_korselt_triple {n : ℕ}
    (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hn0 : 0 < n := by
    by_contra hnot
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hnz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hnlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
  have hn1 : 1 < n := by
    have hn1R : ((1 : ℕ) : ℝ) < (n : ℝ) := by
      norm_num only [Nat.cast_one]
      linarith only [hL, hnlog]
    exact Nat.cast_lt.mp hn1R
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · exact
      finite_index_witness_or_uniform_korselt_triple_gammaIndex100Prefix hnOdd hcomp
        (PrimeTest.fermatSubgroup n) le_rfl hi hGRH hL
  · have hindex : 100 ≤ (PrimeTest.fermatSubgroup n).index := by
      have hlarge := (lt_of_not_ge hi).le
      norm_num only at hlarge
      exact le_trans (by norm_num only) hlarge
    have hHpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      exact PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
    exact
      Or.inl
        (exists_prime_witness_le_gammaIndex100PrefixUpper_of_subgroup hn1 hnOdd hGRH
          (PrimeTest.fermatSubgroup n) hindex hHpass hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
