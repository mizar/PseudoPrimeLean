/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaSeedPairedBounds
public import PseudoPrime.LLS.ClippedAffineWitnessBounds
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.LLS.GammaCheckpoint1000
public import PseudoPrime.LLS.MidscaleEndpointComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaClippedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaIndex100GaussianClosure
public import PseudoPrime.PrimeTest.MillerRabin.SignSubgroupIndex
public import PseudoPrime.Analysis.GaussianGammaKernel
public import PseudoPrime.LLS.RelativeGaussianSubgroupComparison
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics

/-! # An MR-specific affine cutoff from the retained signed Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The coefficient-0.282924 finite-index witness is below the Gamma index-100
bound throughout its domain. The positive root exceeds `(3/8)L`, whose squared
coefficient is already larger than `282924/1000000`. -/
theorem gammaIndex100Bound_ge_0283 {L : ℝ} (hL : 330 ≤ L) :
    (282924 / 1000000 : ℝ) * L ^ 2 ≤ gammaIndex100Bound L := by
  have hmu : (3 / 8 : ℝ) < (11783423 / 25000000 : ℝ) / (91 / 100 : ℝ) := by norm_num only
  have hA : (0 : ℝ) < (11783423 / 25000000 : ℝ) * L + 1057 / 2500 := by nlinarith only [hL]
  have hroot :
    (11783423 / 25000000 : ℝ) * L + 1057 / 2500 ≤
      Real.sqrt
        (((11783423 / 25000000 : ℝ) * L + 1057 / 2500) ^ 2 +
          4 * (91 / 100 : ℝ) * ((7 / 6 : ℝ) * L + 61)) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hL, sq_nonneg ((11783423 / 25000000 : ℝ) * L + 1057 / 2500)]
  have hr : (3 / 8 : ℝ) * L ≤ gammaIndex100Radius L := by
    unfold gammaIndex100Radius
    have hden : 0 < 2 * (91 / 100 : ℝ) := by norm_num only
    apply (le_div_iff₀ hden).2
    nlinarith only [hroot, hmu, hA, hL]
  have hscale_nonneg : 0 ≤ 3 / 8 * L := mul_nonneg (by norm_num only) (by linarith only [hL])
  have hsquare := mul_le_mul_of_nonneg_left hr hscale_nonneg
  have hcoef : (282924 / 1000000 : ℝ) < (99 / 40) * (3 / 8) ^ 2 := by norm_num only
  dsimp only [gammaIndex100Bound]
  nlinarith only [hsquare, hcoef, sq_nonneg (gammaIndex100Radius L)]

/-- On `L ≥ 330`, the radius already contains the cutoff required by the
50000-term retained prefix. -/
theorem gammaIndex100Radius_prefix50000 {L : ℝ} (hL : 330 ≤ L) :
    50000 ≤ (99 / 40 : ℝ) * (gammaIndex100Radius L) ^ 2 := by
  let A : ℝ := (11783423 / 25000000 : ℝ) * L + 1057 / 2500
  let S : ℝ := (7 / 6 : ℝ) * L + 61
  let a : ℝ := 91 / 100
  have hA : 0 < A := by
    dsimp only [A]
    nlinarith only [hL]
  have hS : 0 < S := by
    dsimp only [S]
    nlinarith only [hL]
  have ha : 0 < a := by norm_num only [a]
  have hrad : 0 ≤ A ^ 2 + 4 * a * S :=
    add_nonneg (sq_nonneg A) (mul_nonneg (by norm_num only [a]) hS.le)
  have hroot : A ≤ Real.sqrt (A ^ 2 + 4 * a * S) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith only [hS, ha]
  have hA143 : 143 * a ≤ A := by
    dsimp only [A, a]
    nlinarith only [hL]
  have hbound : 143 ≤ A / a := (le_div_iff₀ ha).2 hA143
  have hsum : 2 * A ≤ A + Real.sqrt (A ^ 2 + 4 * a * S) := by linarith only [hroot]
  have ha2 : 0 < 2 * a := mul_pos (by norm_num only) ha
  have hscaled := mul_le_mul_of_nonneg_right hsum ha2.le
  have hscale : (2 * A) / (2 * a) ≤ (A + Real.sqrt (A ^ 2 + 4 * a * S)) / (2 * a) :=
    (div_le_div_iff₀ ha2 ha2).2 (by nlinarith only [hscaled])
  have heq : A / a = (2 * A) / (2 * a) := by field_simp [ha.ne']
  have hradius : A / a ≤ gammaIndex100Radius L := by
    unfold gammaIndex100Radius
    rw [heq]
    exact hscale
  have hlarge : 143 ≤ gammaIndex100Radius L := hbound.trans hradius
  have hsq : (143 : ℝ) ^ 2 ≤ (gammaIndex100Radius L) ^ 2 := by
    nlinarith only [hlarge, sq_nonneg (gammaIndex100Radius L - 143)]
  norm_num only at hsq ⊢
  nlinarith only [hsq]

/-- With a pass-containing subgroup of index at least one hundred, the new
50000-prefix radius yields a rejecting prime below `gammaIndex100Bound`. The
finite prefix and the positive-root equation close the exact budget. -/
theorem exists_prime_witness_le_gammaIndex100_of_subgroup {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let r : ℝ := gammaIndex100Radius (Real.log n)
  let x : ℝ := r ^ 2
  have hrprop := gammaIndex100Radius_properties hL
  have hr : 0 < r := by
    dsimp only [r]
    exact hrprop.1
  have hsqrt : Real.sqrt x = r := by
    dsimp only [x]
    rw [Real.sqrt_sq hr.le]
  have hprefixBound : (50000 : ℝ) ≤ (99 / 40 : ℝ) * x := by
    dsimp only [x, r]
    exact gammaIndex100Radius_prefix50000 hL
  have hx : 2 ≤ x := by
    dsimp only [x] at hprefixBound ⊢
    nlinarith only [hprefixBound]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hprefix :=
    LLS.gamma_prefix50000_lower_asymmetric hGRH.riemann (b := 50000) (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hGRH.riemann n n x 50000
  norm_num only [Nat.floor_ofNat] at hu
  dsimp only [gammaSignedPrefixMRBudget] at hu
  have hbudget :
    gammaSignedPrefixMRBudget n n x 50000 <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * (28493 / 5000 : ℝ) +
        ((7 / 6 : ℝ) * Real.log n + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget]
    linarith only [hu, hprefix]
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact (by nlinarith only [hx] : 1 ≤ x))
  have htail := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
  rw [hsqrt] at htail
  have htail' : 43 * x ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    calc
      _ ≤ 43 * (1 / r) := by simpa only [one_mul] using htail
      _ = 43 / r := by ring
  have hbudgetUpper :
    gammaSignedPrefixMRBudget n n x 50000 <
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * (28493 / 5000 : ℝ) +
        ((7 / 6 : ℝ) * Real.log n + 47) / r := by
    rw [hsqrt] at hbudget
    have hpole :
      ((7 / 6 : ℝ) * Real.log n + 4) / r + 43 / r = ((7 / 6 : ℝ) * Real.log n + 47) / r := by ring
    linarith only [hbudget, htail', hpole]
  have hconstant : 541 / 50 - 2 * (28493 / 5000 : ℝ) + 1 = 1057 / 2500 := by norm_num only
  have hrecip :
    ((7 / 6 : ℝ) * Real.log n + 47) / r + 14 / r = ((7 / 6 : ℝ) * Real.log n + 61) / r := by
    field_simp [hr.ne']
    ring
  have hendpoint :
    (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * (28493 / 5000 : ℝ) +
        ((7 / 6 : ℝ) * Real.log n + 47) / r =
      (91 / 100 : ℝ) * r - 1 - 14 / r := by
    have hroot := gammaIndex100Radius_budget_eq hL
    change
      (91 / 100 : ℝ) * r - (11783423 / 25000000 : ℝ) * Real.log n - 1057 / 2500 -
          ((7 / 6 : ℝ) * Real.log n + 61) / r =
        0 at hroot
    have hconstant' :
      (11783423 / 25000000 : ℝ) * Real.log n + 541 / 50 - 2 * (28493 / 5000 : ℝ) =
        (11783423 / 25000000 : ℝ) * Real.log n + 1057 / 2500 - 1 := by
      linarith only [hconstant]
    have hrecip' :
      ((7 / 6 : ℝ) * Real.log n + 61) / r - 14 / r = ((7 / 6 : ℝ) * Real.log n + 47) / r := by
      linarith only [hrecip]
    rw [hconstant', ← hrecip']
    linarith only [hroot]
  have hgap : gammaSignedPrefixMRBudget n n x 50000 < (91 / 100 : ℝ) * r - 1 - 14 / r := by
    exact lt_of_lt_of_eq hbudgetUpper hendpoint
  have hr1 : 1 ≤ r := by nlinarith only [hr, hx, sq_nonneg (r - 1)]
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_of_gamma_index100_gap hn hnOdd hGRH hQ H hidx hHpass hr1 hx
      (by norm_num only) hprefixBound hgap
  refine ⟨p, hp, ?_, hreject⟩
  dsimp only [gammaIndex100Bound, r, x]
  exact hpbound

/-- The least prime rejecting base inherits the index-100 Gamma bound whenever
the supplied pass-containing subgroup has index at least one hundred. -/
theorem exists_least_prime_witness_le_gammaIndex100_of_subgroup {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hQ : 20000 ≤ n)
    (H : Subgroup (ZMod n)ˣ) (hidx : 100 ≤ H.index)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_le_gammaIndex100_of_subgroup hn hnOdd hGRH hQ H hidx hHpass hL
  let hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, (Nat.find_spec hex).2,
      fun q hq hqReject ↦ Nat.find_min' hex ⟨hq, hqReject⟩⟩

/-- The finite-index classification is the low-index consumer for the new
Gamma branch. For a subgroup of index below one hundred, return either its
coefficient-0.282924 witness or the squarefree uniform Korselt triple that
requires the separate Gaussian closure. -/
theorem gammaIndex100_low_index_classification {n : ℕ} [NeZero n] (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hidx : H.index < 100)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn142 : 10 ^ 142 ≤ n) :
    (∃ r : ℕ,
        r.Prime ∧
          (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
          ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  exact
    coefficient_0283_witness_or_uniform_korselt_triple hnOdd hcomp H hH
      (Nat.le_trans (Nat.le_of_lt hidx) (by norm_num only)) hGRH hn142

/-- A logarithmic scale of at least 330 forces the input beyond the finite
classification's decimal threshold. Compare logarithms with the exact powers
of ten and use `log 10 < 231/100`. -/
theorem gammaIndex100_log_ge_decimal142 {n : ℕ} [NeZero n] (hL : 330 ≤ Real.log n) :
    10 ^ 142 ≤ n := by
  by_contra hn142
  have hnlt : (n : ℝ) < (10 : ℝ) ^ 142 := by exact_mod_cast (Nat.lt_of_not_ge hn142)
  have hlog := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hnlt
  rw [Real.log_pow] at hlog
  norm_num only at hlog
  have h10 : Real.log (10 : ℝ) < 231 / 100 := by
    rw [show (10 : ℝ) = 2 * 5 by norm_num only,
      Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)]
    linarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hten := mul_lt_mul_of_pos_left h10 (by norm_num only : (0 : ℝ) < 142)
  have h328 : 142 * (231 / 100 : ℝ) < 330 := by norm_num only
  linarith only [hlog, hten, hL, h328]

/-- Split every odd composite with `log n ≥ 330` by the index of the canonical
pass-containing subgroup. Index at least one hundred uses the new Gamma bound;
lower index consumes the finite classification and leaves only its uniform
Korselt triple for the dedicated Gaussian closure. -/
theorem exists_prime_witness_le_gammaIndex100_or_uniform_korselt_triple_of_odd_composite {n : ℕ}
    (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hn0 : n ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  let : NeZero n := ⟨hn0⟩
  have hnQ : 20000 ≤ n := by
    by_contra hnQ
    have hnlt : (n : ℝ) < 20000 := by exact_mod_cast (Nat.lt_of_not_ge hnQ)
    have hlog := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hnlt
    have h20 : Real.log (20000 : ℝ) < 330 := by
      rw [show (20000 : ℝ) = 2 ^ 5 * 5 ^ 4 by norm_num only,
        Real.log_mul (pow_ne_zero 5 (by norm_num only : (2 : ℝ) ≠ 0))
          (pow_ne_zero 4 (by norm_num only : (5 : ℝ) ≠ 0)),
        Real.log_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [Real.log_two_lt_d9, Real.log_five_lt_d9]
    linarith only [hL, hlog, h20]
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 20000) hnQ
  have hn9 : n ≠ 9 := by
    intro heq
    rw [heq] at hnQ
    norm_num only at hnQ
  obtain ⟨H, hidx, hH, hHpass⟩ :=
    PrimeTest.exists_index_ge_four_subgroup_containing_passes_with_fermat hn1 hnOdd hcomp hn9
  by_cases hbig : 100 ≤ H.index
  · exact
      Or.inl (exists_prime_witness_le_gammaIndex100_of_subgroup hn1 hnOdd hGRH hnQ H hbig hHpass hL)
  · rcases
      gammaIndex100_low_index_classification hnOdd hcomp H hH (Nat.lt_of_not_ge hbig) hGRH
        (gammaIndex100_log_ge_decimal142 hL) with
      hw | ht
    · obtain ⟨p, hp, hbound, hreject⟩ := hw
      exact Or.inl ⟨p, hp, hbound.trans (gammaIndex100Bound_ge_0283 hL), hreject⟩
    · exact Or.inr ht

/-- At index below one hundred, consume the finite classification and transfer
its local witness to the Gamma index-100 bound. The uniform Korselt triple is
returned for the remaining Gaussian argument. -/
theorem exists_prime_witness_le_gammaIndex100_or_uniform_korselt_triple {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ)
    (hH : H ≤ PrimeTest.fermatSubgroup n) (hidx : H.index < 100)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn142 : 10 ^ 142 ≤ n)
    (hL : 330 ≤ Real.log n) :
    (∃ r : ℕ,
        r.Prime ∧
          (r : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
          ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  rcases gammaIndex100_low_index_classification hnOdd hcomp H hH hidx hGRH hn142 with hw | ht
  · obtain ⟨r, hr, hb, hfail⟩ := hw
    exact Or.inl ⟨r, hr, hb.trans (gammaIndex100Bound_ge_0283 hL), hfail⟩
  · exact Or.inr ht

/-- For the 1000-term Euler prefix, the affine radius `287 * L / 500 + 9` makes
the signed-budget comparison positive for every `L >= 100`. The rational identity
at `L = 100` and a positive slope prove the claim on the whole half-line.
Role: support a lower-entry MR branch using the existing 1000-term prefix. -/
theorem gamma_cutoff_1000_margin (L : ℝ) (hL : 100 ≤ L) :
    0 <
      (133 / 160 - 231 / 24700 : ℝ) * ((287 / 500 : ℝ) * L + 9) - (11783423 / 25000000 : ℝ) * L -
            7417297 / 3952000 -
            541 / 50 +
          2 * (203 / 50) -
        ((7 / 6 : ℝ) * L + 70) / ((287 / 500 : ℝ) * L + 9) := by
  let r : ℝ := (287 / 500 : ℝ) * L + 9
  let r0 : ℝ := 332 / 5
  have hr : r0 ≤ r := by
    dsimp only [r, r0]
    nlinarith only [hL]
  have hr0pos : 0 < r0 := by norm_num only [r0]
  have hrpos : 0 < r := by linarith only [hr, hr0pos]
  have hdelta : 0 ≤ L - 100 := by linarith only [hL]
  have hslope : 0 < (133 / 160 - 231 / 24700 : ℝ) * (287 / 500 : ℝ) - 11783423 / 25000000 := by
    norm_num only
  have hidentity :
    (133 / 160 - 231 / 24700 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 7417297 / 3952000 -
            541 / 50 +
          2 * (203 / 50) -
        ((7 / 6 : ℝ) * L + 70) / r =
      ((133 / 160 - 231 / 24700 : ℝ) * (287 / 500 : ℝ) - 11783423 / 25000000) * (L - 100) +
        ((133 / 160 - 231 / 24700 : ℝ) * r0 - (11783423 / 25000000 : ℝ) * 100 - 7417297 / 3952000 -
              541 / 50 +
            2 * (203 / 50) -
          ((7 / 6 : ℝ) * 100 + 70) / r0) +
        (742 / 25 : ℝ) * (L - 100) / (r * r0) := by
    dsimp only [r, r0]
    have hr' : (287 / 500 : ℝ) * L + 9 ≠ 0 := by
      have hpos : 0 < (287 / 500 : ℝ) * L + 9 := by nlinarith only [hL]
      exact ne_of_gt hpos
    field_simp [hr']
    ring_nf
  have hbase :
    (133 / 160 - 231 / 24700 : ℝ) * r0 - (11783423 / 25000000 : ℝ) * 100 - 7417297 / 3952000 -
            541 / 50 +
          2 * (203 / 50) -
        ((7 / 6 : ℝ) * 100 + 70) / r0 =
      6424450723 / 123006000000 := by
    dsimp only [r0]
    norm_num only
  change
    0 <
      (133 / 160 - 231 / 24700 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 7417297 / 3952000 -
            541 / 50 +
          2 * (203 / 50) -
        ((7 / 6 : ℝ) * L + 70) / r
  rw [hidentity, hbase]
  have hlinear :
    0 ≤ ((133 / 160 - 231 / 24700 : ℝ) * (287 / 500 : ℝ) - 11783423 / 25000000) * (L - 100) :=
    mul_nonneg hslope.le hdelta
  have hreciprocal : 0 ≤ (742 / 25 : ℝ) * (L - 100) / (r * r0) := by positivity
  linarith only [hlinear, hreciprocal]

/-- For `L ≥ 258`, the index-four signed-prefix budget with radius
`r = 107L/200 + 24/5` has a positive rational margin. Bound `L/r` by `1/a`
and `1/r` by the reciprocal of the initial radius; the affine slope and the
value at `L = 258` are both positive. -/
theorem gamma_cutoff_index_four_margin {L : ℝ} (hL : 258 ≤ L) :
    0 <
      (261143 / 296400 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) - (11783423 / 25000000 : ℝ) * L -
            (7417297 / 3952000 + 47 / 10) / 3 -
            541 / 50 +
          2 * (28493 / 5000) -
        (7 / 6 : ℝ) * (L / ((107 / 200 : ℝ) * L + 24 / 5)) -
        (164 / 3) / ((107 / 200 : ℝ) * L + 24 / 5) := by
  let a : ℝ := 107 / 200
  let d : ℝ := 24 / 5
  let K : ℝ := 261143 / 296400
  let μ : ℝ := 11783423 / 25000000
  let s : ℝ := 7417297 / 3952000
  let r : ℝ := a * L + d
  have ha : 0 < a := by norm_num only [a]
  have hr0 : (14283 / 100 : ℝ) ≤ r := by
    dsimp only [r, a, d]
    nlinarith only [hL]
  have hrpos : 0 < r := by linarith only [hr0]
  have hratio : L / r ≤ 1 / a := by
    apply (div_le_iff₀ hrpos).mpr
    dsimp only [r]
    nlinarith only [ha]
  have hinv : (1 : ℝ) / r ≤ 100 / 14283 := by
    rw [div_le_iff₀ hrpos]
    nlinarith only [hr0]
  have hratioInv : L / r ≤ a⁻¹ := by simpa only [one_div, one_mul] using hratio
  have hinvInv : r⁻¹ ≤ 100 / 14283 := by simpa only [one_div, one_mul] using hinv
  have hslope : 0 < K * a - μ := by norm_num only [K, a, μ]
  have hbase :
    0 <
      (K * a - μ) * 258 + K * d - (s + 47 / 10) / 3 - 541 / 50 + 2 * (28493 / 5000 : ℝ) -
        (7 / 6 : ℝ) * a⁻¹ -
        (164 / 3 : ℝ) * (100 / 14283) := by
    norm_num only [K, a, d, μ, s]
  have hlinear : 0 ≤ (K * a - μ) * (L - 258) := mul_nonneg hslope.le (sub_nonneg.mpr hL)
  have hmain : (K * a - μ) * 258 + K * d ≤ K * r - μ * L := by
    dsimp only [r, a, d]
    nlinarith only [hL]
  have hratio' : (7 / 6 : ℝ) * (L / r) ≤ (7 / 6 : ℝ) * a⁻¹ :=
    mul_le_mul_of_nonneg_left hratioInv (by norm_num only : (0 : ℝ) ≤ 7 / 6)
  have hinv' : (164 / 3 : ℝ) * r⁻¹ ≤ (164 / 3 : ℝ) * (100 / 14283) :=
    mul_le_mul_of_nonneg_left hinvInv (by norm_num only : (0 : ℝ) ≤ 164 / 3)
  have htarget :
    0 <
      K * r - μ * L - (s + 47 / 10) / 3 - 541 / 50 + 2 * (28493 / 5000) - (7 / 6 : ℝ) * (L / r) -
        (164 / 3 : ℝ) * r⁻¹ := by
    dsimp only [K, a, d, μ, s] at hmain hratio' hinv' hbase
    calc
      0 <
          (261143 / 296400 * (107 / 200) - 11783423 / 25000000) * 258 + 261143 / 296400 * (24 / 5) -
                (7417297 / 3952000 + 47 / 10) / 3 -
                541 / 50 +
              2 * (28493 / 5000) -
            (7 / 6 : ℝ) * (107 / 200)⁻¹ -
            (164 / 3 : ℝ) * (100 / 14283) :=
        hbase
      _ ≤
          261143 / 296400 * r - 11783423 / 25000000 * L - (7417297 / 3952000 + 47 / 10) / 3 -
                541 / 50 +
              2 * (28493 / 5000) -
            (7 / 6 : ℝ) * (L / r) -
            (164 / 3 : ℝ) * r⁻¹ :=
        by linarith only [hmain, hratio', hinv']
  change
    0 <
      K * r - μ * L - (s + 47 / 10) / 3 - 541 / 50 + 2 * (28493 / 5000) - (7 / 6 : ℝ) * (L / r) -
        (164 / 3) * r⁻¹
  exact htarget

/-- Under GRH, every odd composite above logarithmic scale 240 has a prime
strong-Miller--Rabin rejecting base at most the displayed quadratic expression.
The proof combines the signed MR budget, the 50000-term Euler prefix, and the
corrected principal lower bound, then verifies one rational linear margin.
Role: improve the all-input MR envelope below the four-fifths branch. -/
theorem exists_prime_witness_le_gamma_linear_cutoff_log_240 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((287 / 500 : ℝ) * Real.log n + 9 / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  let L : ℝ := Real.log n
  let a : ℝ := 287 / 500
  let d : ℝ := 9 / 2
  let r : ℝ := a * L + d
  let x : ℝ := r ^ 2
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have hn : 1 < n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hnle
    have hlog := Real.log_le_sub_one_of_pos hn0
    linarith only [hlog, hL, hnR]
  have hL' : 240 ≤ L := hL
  have hr : 142 ≤ r := by
    dsimp only [r, a, d, L]
    nlinarith only [hL]
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hr]
  have hsqrt : Real.sqrt x = r := by
    dsimp only [x]
    rw [Real.sqrt_sq hr0.le]
  have hq : 20000 ≤ n := by
    by_contra hq
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast (show n ≤ 46000 by omega)
    have hl := Real.log_le_log hn0 hnR
    dsimp only [L] at hL'
    linarith only [hl, Analysis.log_46000_lt_eleven, hL']
  have hrCutoff : (711 / 5 : ℝ) ≤ r := by
    dsimp only [r, a, d, L]
    nlinarith only [hL']
  have hbX : (50000 : ℝ) ≤ (99 / 40 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hrCutoff, sq_nonneg (r - 711 / 5)]
  have hprefix := LLS.gamma_prefix50000_lower_asymmetric hGRH.riemann (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hGRH.riemann n n x 50000
  norm_num only [Nat.floor_ofNat] at hu
  dsimp only [gammaSignedPrefixMRBudget] at hu
  have hbudget :
    gammaSignedPrefixMRBudget n n x 50000 <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * (28493 / 5000) +
        ((7 / 6 : ℝ) * L + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget, L]
    linarith only [hu, hprefix]
  have hh : 0 < x / 20 := by
    dsimp only [x]
    positivity
  have hhx : x / 20 ≤ x := by
    dsimp only [x]
    nlinarith only [hr]
  have hpowAnchor : (43 / 39 : ℝ) ^ (16 : ℕ) ≤ x := by
    dsimp only [x]
    have hnum : (43 / 39 : ℝ) ^ (16 : ℕ) ≤ (142 : ℝ) ^ 2 := by norm_num only
    have hr2 : (142 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 142)]
    exact hnum.trans hr2
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 43 / 39) (by norm_num only)
      hpowAnchor
  have htail39 : 43 * x ^ (-9 / 16 : ℝ) ≤ 39 / r := by
    have hs := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
    rw [hsqrt] at hs
    have heq : 43 * (1 / ((43 / 39 : ℝ) * r)) = 39 / r := by
      field_simp (disch := exact hr0.ne')
      norm_num only
    rw [heq] at hs
    exact hs
  have htail : 43 * x ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    have hscale : (39 : ℝ) / r ≤ 43 / r := div_le_div_of_nonneg_right (by norm_num only) hr0.le
    exact htail39.trans hscale
  have hratio : L / r ≤ 1 / a := by
    apply (div_le_iff₀ hr0).mpr
    dsimp only [r]
    have ha : 0 < a := by norm_num only [a]
    dsimp only [a, d]
    nlinarith only [hL', sq_nonneg (L - 250)]
  have hmargin :
    0 <
      (133 / 160 - 231 / 24700 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 7417297 / 3952000 -
            541 / 50 +
          2 * (28493 / 5000) -
        (7 / 6 : ℝ) * (L / r) -
        70 / r := by
    have hslope : 0 < (133 / 160 - 231 / 24700 : ℝ) * a - 11783423 / 25000000 := by
      norm_num only [a]
    have hbase :
      0 <
        ((133 / 160 - 231 / 24700 : ℝ) * a - 11783423 / 25000000) * 250 +
                (133 / 160 - 231 / 24700 : ℝ) * d -
              7417297 / 3952000 -
              541 / 50 +
            2 * (28493 / 5000) -
          7 / (6 * a) -
          70 / 148 := by
      norm_num only [a, d]
    by_cases hL300 : L ≤ 300
    · have hratioLow : L / r ≤ 17 / 10 := by
        apply (div_le_iff₀ hr0).mpr
        dsimp only [r, a, d]
        nlinarith only [hL', hL300]
      have hrecLow : 70 / r ≤ 70 / 142 := by
        apply (div_le_div_iff₀ hr0 (by norm_num only : (0 : ℝ) < 142)).mpr
        nlinarith only [hr]
      have hbaseLow :
        0 <
          ((133 / 160 - 231 / 24700 : ℝ) * a - 11783423 / 25000000) * 240 +
                  (133 / 160 - 231 / 24700 : ℝ) * d -
                7417297 / 3952000 -
                541 / 50 +
              2 * (28493 / 5000) -
            7 / 6 * (17 / 10) -
            70 / 142 := by
        norm_num only [a, d]
      have hslopeL := mul_nonneg hslope.le (sub_nonneg.mpr hL')
      dsimp only [r]
      rw [div_eq_mul_inv]
      dsimp only [a, d] at hslopeL hbaseLow ⊢
      nlinarith only [hL', hratioLow, hrecLow, hslopeL, hbaseLow]
    · have hL250 : 250 ≤ L := by linarith only [hL300]
      have hrecHigh : 70 / r ≤ 70 / 148 := by
        apply (div_le_div_iff₀ hr0 (by norm_num only : (0 : ℝ) < 148)).mpr
        dsimp only [r, a, d]
        nlinarith only [hL250]
      have hbaseHigh :
        0 <
          ((133 / 160 - 231 / 24700 : ℝ) * a - 11783423 / 25000000) * 250 +
                  (133 / 160 - 231 / 24700 : ℝ) * d -
                7417297 / 3952000 -
                541 / 50 +
              2 * (28493 / 5000) -
            7 / (6 * a) -
            70 / 148 := by
        norm_num only [a, d]
      have hslopeL := mul_nonneg hslope.le (sub_nonneg.mpr hL250)
      dsimp only [r]
      rw [div_eq_mul_inv]
      dsimp only [a, d] at hratio hslopeL hbaseHigh ⊢
      nlinarith only [hL250, hratio, hrecHigh, hslopeL, hbaseHigh]
  have hcap := LLS.clippedShiftError_twentieth_width_cap hr0
  have hcapDiv := div_le_div_of_nonneg_right hcap hr0.le
  rw [add_div] at hcapDiv
  have hcapEq :
    ((231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27) / r =
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 27 / r := by
    field_simp (disch := exact hr0.ne')
  rw [hcapEq] at hcapDiv
  have herr :
    (LLS.clippedShiftPrincipalErrorNumerator x (x / 20) +
          Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
        r ≤
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 23 / r := by
    dsimp only [x]
    have hsum : 4 / r + 23 / r = 27 / r := by ring
    linarith only [hcapDiv, hsum]
  have hmass := LLS.clippedShiftPrincipalLower_ge_mass133 x (x / 20)
  rw [hsqrt] at hmass
  have hprincipal :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      LLS.clippedShiftPrincipalLower x (x / 20) := by
    linarith only [hmass, herr]
  have hactual :=
    LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx
  have hactualLower :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re :=
    hprincipal.trans hactual
  have hpoleEq : ((7 / 6 : ℝ) * L + 4) / r = (7 / 6 : ℝ) * (L / r) + 4 / r := by ring
  rw [hsqrt, hpoleEq] at hbudget
  have htailLoss : 27 / r + 43 * x ^ (-9 / 16 : ℝ) ≤ 70 / r := by
    calc
      27 / r + 43 * x ^ (-9 / 16 : ℝ) = 43 * x ^ (-9 / 16 : ℝ) + 27 / r := by ring
      _ ≤ 43 / r + 27 / r := add_le_add htail (le_refl _)
      _ = 70 / r := by ring
  have hgap :
    gammaSignedPrefixMRBudget n n x 50000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    have hsum : 23 / r + 4 / r = 27 / r := by ring
    linarith only [hbudget, hactualLower, hmargin, htailLoss, hsum]
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only) hbX hgap
  refine ⟨p, hp, ?_, hreject⟩
  dsimp only [x, r, a, d, L] at hpbound ⊢
  exact hpbound

/-- Under GRH, every odd composite above logarithmic scale 210 has a prime
strong-Miller--Rabin rejecting base at most the displayed quadratic expression.
The proof combines the signed MR budget, the 1000-term Euler prefix, and the
corrected principal lower bound, then verifies one rational linear margin.
Role: improve the all-input MR envelope below the four-fifths branch. -/
theorem exists_prime_witness_le_gamma_linear_cutoff_log_210 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 210 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((287 / 500 : ℝ) * Real.log n + 9) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  let L : ℝ := Real.log n
  let a : ℝ := 287 / 500
  let d : ℝ := 9
  let r : ℝ := a * L + d
  let x : ℝ := r ^ 2
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have hn : 1 < n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hnle
    have hlog := Real.log_le_sub_one_of_pos hn0
    linarith only [hlog, hL, hnR]
  have hL' : 210 ≤ L := hL
  have hr : 125 ≤ r := by
    dsimp only [r, a, d, L]
    nlinarith only [hL]
  have hr0 : 0 < r := by linarith only [hr]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hr]
  have hsqrt : Real.sqrt x = r := by
    dsimp only [x]
    rw [Real.sqrt_sq hr0.le]
  have hq : 20000 ≤ n := by
    by_contra hq
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast (show n ≤ 46000 by omega)
    have hl := Real.log_le_log hn0 hnR
    dsimp only [L] at hL'
    linarith only [hl, Analysis.log_46000_lt_eleven, hL']
  have hbX : (1000 : ℝ) ≤ (99 / 40 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hr, sq_nonneg (r - 125)]
  have hprefix := LLS.gamma_prefix1000_lower_halfline hGRH.riemann (le_refl (1000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hGRH.riemann n n x 1000
  norm_num only [Nat.floor_ofNat] at hu
  dsimp only [gammaSignedPrefixMRBudget] at hu
  have hbudget :
    gammaSignedPrefixMRBudget n n x 1000 <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * (203 / 50) +
        ((7 / 6 : ℝ) * L + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget, L]
    linarith only [hu, hprefix]
  have hh : 0 < x / 20 := by
    dsimp only [x]
    positivity
  have hhx : x / 20 ≤ x := by
    dsimp only [x]
    nlinarith only [hr]
  have hpowAnchor : (43 / 39 : ℝ) ^ (16 : ℕ) ≤ x := by
    dsimp only [x]
    have hnum : (43 / 39 : ℝ) ^ (16 : ℕ) ≤ (125 : ℝ) ^ 2 := by norm_num only
    have hr2 : (125 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 125)]
    exact hnum.trans hr2
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 43 / 39) (by norm_num only)
      hpowAnchor
  have htail39 : 43 * x ^ (-9 / 16 : ℝ) ≤ 39 / r := by
    have hs := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
    rw [hsqrt] at hs
    have heq : 43 * (1 / ((43 / 39 : ℝ) * r)) = 39 / r := by
      field_simp (disch := exact hr0.ne')
      norm_num only
    rw [heq] at hs
    exact hs
  have htail : 43 * x ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    have hscale : (39 : ℝ) / r ≤ 43 / r := div_le_div_of_nonneg_right (by norm_num only) hr0.le
    exact htail39.trans hscale
  have hmargin0 := gamma_cutoff_1000_margin L (by linarith only [hL'])
  have hmargin :
    0 <
      (133 / 160 - 231 / 24700 : ℝ) * r - (11783423 / 25000000 : ℝ) * L - 7417297 / 3952000 -
            541 / 50 +
          2 * (203 / 50) -
        (7 / 6 : ℝ) * (L / r) -
        70 / r := by
    have heq : ((7 / 6 : ℝ) * L + 70) / r = (7 / 6 : ℝ) * (L / r) + 70 / r := by
      field_simp (disch := exact hr0.ne')
    rw [heq] at hmargin0
    dsimp only [r, a, d] at hmargin0 ⊢
    linarith only [hmargin0]
  have hcap := LLS.clippedShiftError_twentieth_width_cap hr0
  have hcapDiv := div_le_div_of_nonneg_right hcap hr0.le
  rw [add_div] at hcapDiv
  have hcapEq :
    ((231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27) / r =
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 27 / r := by
    field_simp (disch := exact hr0.ne')
  rw [hcapEq] at hcapDiv
  have herr :
    (LLS.clippedShiftPrincipalErrorNumerator x (x / 20) +
          Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
        r ≤
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 23 / r := by
    dsimp only [x]
    have hsum : 4 / r + 23 / r = 27 / r := by ring
    linarith only [hcapDiv, hsum]
  have hmass := LLS.clippedShiftPrincipalLower_ge_mass133 x (x / 20)
  rw [hsqrt] at hmass
  have hprincipal :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      LLS.clippedShiftPrincipalLower x (x / 20) := by
    linarith only [hmass, herr]
  have hactual :=
    LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx
  have hactualLower :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re :=
    hprincipal.trans hactual
  have hpoleEq : ((7 / 6 : ℝ) * L + 4) / r = (7 / 6 : ℝ) * (L / r) + 4 / r := by ring
  rw [hsqrt, hpoleEq] at hbudget
  have htailLoss : 27 / r + 43 * x ^ (-9 / 16 : ℝ) ≤ 70 / r := by
    calc
      27 / r + 43 * x ^ (-9 / 16 : ℝ) = 43 * x ^ (-9 / 16 : ℝ) + 27 / r := by ring
      _ ≤ 43 / r + 27 / r := add_le_add htail (le_refl _)
      _ = 70 / r := by ring
  have hgap :
    gammaSignedPrefixMRBudget n n x 1000 <
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    have hsum : 23 / r + 4 / r = 27 / r := by ring
    linarith only [hbudget, hactualLower, hmargin, htailLoss, hsum]
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_of_signed_prefix_gap hn hnOdd hnComposite hGRH hq (le_refl n) hx
      (by norm_num only) hbX hgap
  refine ⟨p, hp, ?_, hreject⟩
  dsimp only [x, r, a, d, L] at hpbound ⊢
  exact hpbound

/-- The former 250-entry API follows by specializing the 240-entry result.
Role: preserve existing clients while exposing the lower entrance. -/
theorem exists_prime_witness_le_gamma_linear_cutoff_log_250 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((287 / 500 : ℝ) * Real.log n + 9 / 2) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_witness_le_gamma_linear_cutoff_log_240 hnOdd hnComposite hGRH (by linarith only [hL])

/-- Under the same hypotheses, the least prime MR witness satisfies the affine
cutoff. Choose a witness from the preceding theorem and minimize the rejecting
prime predicate. Role: supply the least-witness form used by the comparison table. -/
theorem exists_least_prime_witness_le_gamma_linear_cutoff_log_240 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((287 / 500 : ℝ) * Real.log n + 9 / 2) ^ 2 ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_le_gamma_linear_cutoff_log_240 hnOdd hnComposite hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hpbound, fun q hq hqreject ↦
      Nat.find_min' hex ⟨hq, hqreject⟩⟩

/-- Under the same hypotheses, the least prime MR witness satisfies the affine
cutoff. Choose a witness from the preceding theorem and minimize the rejecting
prime predicate. Role: supply the least-witness form used by the comparison table. -/
theorem exists_least_prime_witness_le_gamma_linear_cutoff_log_210 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 210 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((287 / 500 : ℝ) * Real.log n + 9) ^ 2 ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_le_gamma_linear_cutoff_log_210 hnOdd hnComposite hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hpbound, fun q hq hqreject ↦
      Nat.find_min' hex ⟨hq, hqreject⟩⟩

/-- The least-witness API at logarithmic scale 250 follows by specialization.
Role: preserve existing table references. -/
theorem exists_least_prime_witness_le_gamma_linear_cutoff_log_250 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((287 / 500 : ℝ) * Real.log n + 9 / 2) ^ 2 ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q :=
  exists_least_prime_witness_le_gamma_linear_cutoff_log_240 hnOdd hnComposite hGRH
    (by linarith only [hL])

/-- Under GRH, every odd composite with `log n ≥ 258` has a prime
strong-Miller–Rabin rejecting base at most
`(99/40) * ((107/200) * log n + 24/5)^2`. Preserve the index-four subgroup
bound in the signed-prefix comparison, use the 50000-term prefix, and combine
the paired ramp error with the corrected principal lower bound. -/
theorem exists_prime_witness_le_gamma_index_four_log_258 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 258 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((107 / 200 : ℝ) * Real.log n + 24 / 5) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  let L : ℝ := Real.log n
  let a : ℝ := 107 / 200
  let d : ℝ := 24 / 5
  let r : ℝ := a * L + d
  let x : ℝ := r ^ 2
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have hn : 1 < n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hnR : (n : ℝ) ≤ 1 := by exact_mod_cast hnle
    have hlog := Real.log_le_sub_one_of_pos hn0
    linarith only [hlog, hL, hnR]
  have hL' : 258 ≤ L := hL
  have hq : 20000 ≤ n := by
    by_contra hq
    have hnR : (n : ℝ) ≤ 46000 := by exact_mod_cast (show n ≤ 46000 by omega)
    have hl := Real.log_le_log hn0 hnR
    dsimp only [L] at hL'
    linarith only [hl, Analysis.log_46000_lt_eleven, hL']
  have hn9 : n ≠ 9 := by
    intro h
    subst n
    norm_num only at hq
  have hr : (14283 / 100 : ℝ) ≤ r := by
    dsimp only [r, a, d, L]
    nlinarith only [hL]
  have hrpos : 0 < r := by linarith only [hr]
  have hx : 2 ≤ x := by
    dsimp only [x]
    nlinarith only [hr]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hsqrt : Real.sqrt x = r := by
    dsimp only [x]
    rw [Real.sqrt_sq hrpos.le]
  have hprefixBound : (50000 : ℝ) ≤ (99 / 40 : ℝ) * x := by
    dsimp only [x]
    nlinarith only [hr, sq_nonneg (r - 142)]
  have hprefix := LLS.gamma_prefix50000_lower_asymmetric hGRH.riemann (le_refl (50000 : ℝ))
  norm_num only [Nat.floor_ofNat] at hprefix
  have hu := gammaSignedPrefixMRBudget_lt_precise_common_cost hGRH.riemann n n x 50000
  norm_num only [Nat.floor_ofNat] at hu
  dsimp only [gammaSignedPrefixMRBudget] at hu
  have hbudget :
    gammaSignedPrefixMRBudget n n x 50000 <
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * (28493 / 5000) +
        ((7 / 6 : ℝ) * L + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
    dsimp only [gammaSignedPrefixMRBudget, L]
    linarith only [hu, hprefix]
  have hscaleFactor : (79 / 50 : ℝ) ≤ Real.sqrt (5 / 2 : ℝ) := by
    apply (Real.le_sqrt (by norm_num only) (by norm_num only)).mpr
    norm_num only
  have hseedL : 225 ≤ Real.sqrt (5 / 2 : ℝ) * r := by
    have hp := mul_le_mul_of_nonneg_right hscaleFactor hrpos.le
    norm_num only at hp
    nlinarith only [hp, hr]
  have hscaleEq : (2 / 5 : ℝ) * (Real.sqrt (5 / 2 : ℝ) * r) ^ 2 = x := by
    have hrootSq : (Real.sqrt (5 / 2 : ℝ)) ^ 2 = 5 / 2 := Real.sq_sqrt (by norm_num only)
    dsimp only [x]
    rw [mul_pow, hrootSq]
    ring
  have hseed := LLS.gamma_seed_paired_nearSquare_budgets hseedL
  have hseedErr :
    LLS.gammaRampPairedErrorNumerator x / Real.sqrt x ≤ Real.sqrt x / 200 + 47 / 20 := by
    simpa only [hscaleEq] using hseed.1
  have hmass : (293 / 320 : ℝ) ≤ ∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u := by
    have hm := Analysis.gamma_ramp_mass_lower
    linarith only [hm]
  have hT := LLS.gamma_ramp_sum_lower_paired hGRH.riemann hx1
  rw [hsqrt] at hT hseedErr
  have hmassR := mul_le_mul_of_nonneg_right hmass hrpos.le
  have hTLower :
    (293 / 320 : ℝ) * r - r / 200 - 47 / 20 ≤
      AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / r := by
    nlinarith only [hT, hmassR, hseedErr]
  have hcap := LLS.clippedShiftError_twentieth_width_cap hrpos
  have hcapDiv := div_le_div_of_nonneg_right hcap hrpos.le
  rw [add_div] at hcapDiv
  have hcapEq :
    ((231 / 24700 : ℝ) * r ^ 2 + (7417297 / 3952000 : ℝ) * r + 27) / r =
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 27 / r := by
    field_simp (disch := exact hrpos.ne')
  rw [hcapEq] at hcapDiv
  have herr :
    (LLS.clippedShiftPrincipalErrorNumerator x (x / 20) +
          Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
        r ≤
      (231 / 24700 : ℝ) * r + 7417297 / 3952000 + 23 / r := by
    dsimp only [x]
    have hsum : 4 / r + 23 / r = 27 / r := by ring
    linarith only [hcapDiv, hsum]
  have hmassPrincipal := LLS.clippedShiftPrincipalLower_ge_mass133 x (x / 20)
  rw [hsqrt] at hmassPrincipal
  have hprincipal :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      LLS.clippedShiftPrincipalLower x (x / 20) := by
    linarith only [hmassPrincipal, herr]
  have hh : 0 < x / 20 := by
    dsimp only [x]
    positivity
  have hhx : x / 20 ≤ x := by
    dsimp only [x]
    nlinarith only [hr]
  have hactual :=
    LLS.clippedShiftPrincipalLower_le_actual hGRH.riemann (by linarith only [hx]) hh hhx
  have hactualLower :
    (133 / 160 - 231 / 24700 : ℝ) * r - 7417297 / 3952000 - 23 / r ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' k : ℕ,
            LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re := by
    exact hprincipal.trans hactual
  have hpowAnchor : (43 / 39 : ℝ) ^ (16 : ℕ) ≤ x := by
    dsimp only [x]
    have hnum : (43 / 39 : ℝ) ^ (16 : ℕ) ≤ (142 : ℝ) ^ 2 := by norm_num only
    have hr2 : (142 : ℝ) ^ 2 ≤ r ^ 2 := by nlinarith only [hr, sq_nonneg (r - 142)]
    exact hnum.trans hr2
  have hpow :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 43 / 39) (by norm_num only)
      hpowAnchor
  have htail39 : 43 * x ^ (-9 / 16 : ℝ) ≤ 39 / r := by
    have hs := mul_le_mul_of_nonneg_left hpow (by norm_num only : (0 : ℝ) ≤ 43)
    rw [hsqrt] at hs
    have heq : 43 * (1 / ((43 / 39 : ℝ) * r)) = 39 / r := by
      field_simp (disch := exact hrpos.ne')
      norm_num only
    rw [heq] at hs
    exact hs
  have htail : 43 * x ^ (-9 / 16 : ℝ) ≤ 43 / r := by
    have hscale : (39 : ℝ) / r ≤ 43 / r := div_le_div_of_nonneg_right (by norm_num only) hrpos.le
    exact htail39.trans hscale
  have hmargin := gamma_cutoff_index_four_margin hL
  have hmargin' :
    0 <
      (261143 / 296400 : ℝ) * r - (11783423 / 25000000 : ℝ) * L -
            (7417297 / 3952000 + 47 / 10) / 3 -
            541 / 50 +
          2 * (28493 / 5000) -
        (7 / 6 : ℝ) * (L / r) -
        (164 / 3 : ℝ) / r := by
    dsimp only [L, r, a, d] at hmargin ⊢
    exact hmargin
  rw [hsqrt] at hbudget hactualLower
  have hfour :
    (261143 / 296400 : ℝ) * r - (7417297 / 3952000 + 47 / 10) / 3 - 23 / (3 * r) ≤
      (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) /
        3 := by
    dsimp only [x] at hTLower hactualLower
    rw [hsqrt]
    have hdiv : 23 / (3 * r) = (23 / r) / 3 := by field_simp (disch := exact hrpos.ne')
    rw [hdiv]
    nlinarith only [hTLower, hactualLower]
  have hgap :
    gammaSignedPrefixMRBudget n n x 50000 <
      (4 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
          (∑' k : ℕ,
              LLS.PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x k).re) /
        3 := by
    have hsum : 23 / (3 * r) + 4 / r + 43 / r = (164 / 3 : ℝ) / r := by
      field_simp (disch := exact hrpos.ne')
      ring
    have hpole : ((7 / 6 : ℝ) * L + 4) / r = (7 / 6 : ℝ) * (L / r) + 4 / r := by ring
    linarith only [hbudget, hfour, hmargin', htail, hsum, hpole]
  obtain ⟨p, hp, hpbound, hreject⟩ :=
    exists_prime_witness_of_signed_prefix_gap_all_inputs hn hnOdd hnComposite hn9 hGRH hq hx
      (by norm_num only : (0 : ℝ) ≤ 50000) hprefixBound hgap
  refine ⟨p, hp, ?_, hreject⟩
  dsimp only [x, r, a, d, L] at hpbound ⊢
  exact hpbound

/-- The least prime rejecting base satisfies the same `B₄` upper bound.
Minimize the unbounded rejection predicate and inherit the explicit bound from
`exists_prime_witness_le_gamma_index_four_log_258`. -/
theorem exists_least_prime_witness_le_gamma_index_four_log_258 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 258 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((107 / 200 : ℝ) * Real.log n + 24 / 5) ^ 2 ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ :=
    exists_prime_witness_le_gamma_index_four_log_258 hnOdd hnComposite hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, fun q hq hqReject ↦
      Nat.find_min' hex ⟨hq, hqReject⟩⟩

theorem gammaLinearCutoff_lt_midscale_sq {L : ℝ} (hlo : 240 ≤ L) :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      (LLS.PaperStatements.midscaleEndpointRadius L) ^ 2 := by
  have hbranch :
    LLS.PaperStatements.midscaleEndpointRadius L = (12800 / 12927 : ℝ) * (L - 83 / 20) := by
    unfold LLS.PaperStatements.midscaleEndpointRadius
    have h₁ : ¬L ≤ 703 / 20 := by linarith only [hlo]
    have h₂ : ¬L ≤ 10367 / 200 := by linarith only [hlo]
    have h₃ : ¬L ≤ 1706 / 25 := by linarith only [hlo]
    have h₄ : ¬L ≤ 6671 / 50 := by linarith only [hlo]
    simp only [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃, ite_eq_right h₄]
  have hr : 0 < (287 / 500 : ℝ) * L + 9 / 2 := by nlinarith only [hlo]
  have hcoef : (99 / 40 : ℝ) < (8 / 5 : ℝ) ^ 2 := by norm_num only
  have hr2 : 0 < ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := sq_pos_of_pos hr
  have hR : (8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) < (12800 / 12927 : ℝ) * (L - 83 / 20) := by
    nlinarith only [hlo]
  have hscaled :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      ((8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2)) ^ 2 := by
    calc
      _ = (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := by ring
      _ < (8 / 5 : ℝ) ^ 2 * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := mul_lt_mul_of_pos_right hcoef hr2
      _ = _ := by ring
  have hscaledPos : 0 < (8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) := by positivity
  have hEndpointPos : 0 < (12800 / 12927 : ℝ) * (L - 83 / 20) := lt_trans hscaledPos hR
  have hsq := (sq_lt_sq₀ hscaledPos.le hEndpointPos.le).mpr hR
  rw [hbranch]
  exact hscaled.trans hsq

/-- From logarithmic scale 210 onward, compare the 1000-term affine radius with
the final branch of the five-piece midscale radius. The branch identity and a
rational root comparison prove strict domination throughout its overlap. -/
theorem gammaLinearCutoff1000_lt_midscale_sq {L : ℝ} (hL : 210 ≤ L) :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9) ^ 2 <
      (LLS.PaperStatements.midscaleEndpointRadius L) ^ 2 := by
  have hbranch :
    LLS.PaperStatements.midscaleEndpointRadius L = (12800 / 12927 : ℝ) * (L - 83 / 20) := by
    unfold LLS.PaperStatements.midscaleEndpointRadius
    have h₁ : ¬L ≤ 703 / 20 := by linarith only [hL]
    have h₂ : ¬L ≤ 10367 / 200 := by linarith only [hL]
    have h₃ : ¬L ≤ 1706 / 25 := by linarith only [hL]
    have h₄ : ¬L ≤ 6671 / 50 := by linarith only [hL]
    simp only [ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃, ite_eq_right h₄]
  have hroot :
    (15733 / 10000 : ℝ) * ((287 / 500 : ℝ) * L + 9) < (12800 / 12927 : ℝ) * (L - 83 / 20) := by
    nlinarith only [hL]
  have hcoef : (99 / 40 : ℝ) < (15733 / 10000 : ℝ) ^ 2 := by norm_num only
  have hbase : 0 < (287 / 500 : ℝ) * L + 9 := by nlinarith only [hL]
  have hbase2 : 0 < ((287 / 500 : ℝ) * L + 9) ^ 2 := sq_pos_of_pos hbase
  have hscaled :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9) ^ 2 <
      ((15733 / 10000 : ℝ) * ((287 / 500 : ℝ) * L + 9)) ^ 2 := by
    calc
      _ = (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9) ^ 2 := by ring
      _ < (15733 / 10000 : ℝ) ^ 2 * ((287 / 500 : ℝ) * L + 9) ^ 2 :=
        mul_lt_mul_of_pos_right hcoef hbase2
      _ = _ := by ring
  have hscaledPos : 0 ≤ (15733 / 10000 : ℝ) * ((287 / 500 : ℝ) * L + 9) := by positivity
  have hrightPos : 0 ≤ (12800 / 12927 : ℝ) * (L - 83 / 20) := by linarith only [hroot, hscaledPos]
  have hsq := (sq_lt_sq₀ hscaledPos hrightPos).mpr hroot
  rw [hbranch]
  exact hscaled.trans hsq

/-- For L >= 240 the 50000-term radius is below the 1000-term radius. The
linear terms differ by a positive constant, so their positive squares preserve
the strict comparison. Role: retain the former branch in the envelope above 240. -/
theorem gammaLinearCutoff_50000_lt_1000_sq {L : ℝ} (hL : 240 ≤ L) :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9) ^ 2 := by
  have hroot : (287 / 500 : ℝ) * L + 9 / 2 < (287 / 500 : ℝ) * L + 9 := by nlinarith only
  have hpos : 0 < (287 / 500 : ℝ) * L + 9 / 2 := by nlinarith only [hL]
  have hsq := (sq_lt_sq₀ hpos.le (by linarith only [hroot, hpos])).mpr hroot
  exact mul_lt_mul_of_pos_left hsq (by norm_num only)

/-- From the end of the midscale interval to L=300, the new radius is below
the adaptive radius. Use the existing analytic lower bound for the adaptive
radius and ln L <= ln 300 <= 23/4, so the comparison holds on the whole interval. -/
theorem gammaLinearCutoff_lt_adaptive_sq {L : ℝ} (hlo : 26269 / 100 ≤ L) (hhi : L ≤ 300) :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      (Analysis.adaptivePart2CutoffRoot L) ^ 2 := by
  have hlog : Real.log L ≤ 23 / 4 := by
    calc
      Real.log L ≤ Real.log 300 := Real.log_le_log (by linarith only [hlo] : (0 : ℝ) < L) hhi
      _ ≤ 23 / 4 := LLS.clippedAffine_log_three_hundred_le
  have hY := LLS.PaperStatements.midscale_adaptive_lower (by linarith only [hlo])
  have hr : 0 < (287 / 500 : ℝ) * L + 9 / 2 := by nlinarith only [hlo]
  have hcoef : (99 / 40 : ℝ) < (8 / 5 : ℝ) ^ 2 := by norm_num only
  have hr2 : 0 < ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := sq_pos_of_pos hr
  have hR : (8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) < L - 2 * Real.log L + 91 / 20 := by
    nlinarith only [hlo, hlog]
  have hscaled :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      ((8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2)) ^ 2 := by
    calc
      _ = (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := by ring
      _ < (8 / 5 : ℝ) ^ 2 * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := mul_lt_mul_of_pos_right hcoef hr2
      _ = _ := by ring
  have hroot : (8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) < Analysis.adaptivePart2CutoffRoot L :=
    lt_of_lt_of_le hR hY
  have hrootPos : 0 < Analysis.adaptivePart2CutoffRoot L := lt_trans (by positivity) hroot
  have hsq :=
    (sq_lt_sq₀ (by positivity : 0 ≤ (8 / 5 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2)) hrootPos.le).mpr
      hroot
  exact hscaled.trans hsq

/-- For L>=250 the new affine root is below the clipped-affine root, hence
the corresponding common-factor 99/40 bound is smaller wherever the latter
theorem applies. -/
theorem gammaLinearCutoff_lt_clippedAffine_sq {L : ℝ} (hL : 250 ≤ L) :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      (99 / 40 : ℝ) * (LLS.clippedAffineRoot L) ^ 2 := by
  have hroot : (287 / 500 : ℝ) * L + 9 / 2 < LLS.clippedAffineRoot L := by
    dsimp only [LLS.clippedAffineRoot]
    nlinarith only [hL]
  have hpos : 0 < (287 / 500 : ℝ) * L + 9 / 2 := by nlinarith only [hL]
  have hsq := (sq_lt_sq₀ hpos.le (by linarith only [hroot, hpos])).mpr hroot
  exact mul_lt_mul_of_pos_left hsq (by norm_num only)

/-- On 240<=L<=11255, the new MR cutoff is smaller than the previously
available (199/250)(L+216)^2 branch. Compare rational square-root envelopes
and use the interval endpoints for the affine comparison. -/
theorem gammaLinearCutoff_lt_plus216_sq {L : ℝ} (hlo : 240 ≤ L) (hhi : L ≤ 11255) :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 < (199 / 250 : ℝ) * (L + 216) ^ 2 := by
  have hrootW : (787 / 500 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) < (892 / 1000 : ℝ) * (L + 216) := by
    nlinarith only [hlo, hhi]
  have hbase : 0 < (287 / 500 : ℝ) * L + 9 / 2 := by nlinarith only [hlo]
  have hcoefW : (99 / 40 : ℝ) < (787 / 500 : ℝ) ^ 2 := by norm_num only
  have hbase2 : 0 < ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := sq_pos_of_pos hbase
  have hW :
    (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 <
      ((787 / 500 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2)) ^ 2 := by
    calc
      _ = (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := by ring
      _ < (787 / 500 : ℝ) ^ 2 * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 :=
        mul_lt_mul_of_pos_right hcoefW hbase2
      _ = _ := by ring
  have hcoef216 : (892 / 1000 : ℝ) ^ 2 < 199 / 250 := by norm_num only
  have hplus : 0 < L + 216 := by linarith only [hlo]
  have hplus2 : 0 < (L + 216) ^ 2 := sq_pos_of_pos hplus
  have h216 : ((892 / 1000 : ℝ) * (L + 216)) ^ 2 < (199 / 250 : ℝ) * (L + 216) ^ 2 := by
    calc
      _ = (892 / 1000 : ℝ) ^ 2 * (L + 216) ^ 2 := by ring
      _ < (199 / 250 : ℝ) * (L + 216) ^ 2 := mul_lt_mul_of_pos_right hcoef216 hplus2
      _ = _ := by ring
  have hsq :=
    (sq_lt_sq₀ (by positivity : 0 ≤ (787 / 500 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2))
          (by positivity : 0 ≤ (892 / 1000 : ℝ) * (L + 216))).mpr
      hrootW
  exact hW.trans (hsq.trans h216)

/-- For `L ≥ 258`, the index-four Gamma radius improves the public linear
cutoff `W(L)`. Both bounds carry the factor `99/40`, so it suffices to compare
their positive affine radii. This is the first direct envelope comparison for
the new all-input index-four witness theorem. -/
theorem gamma_index_four_lt_linear_cutoff_sq {L : ℝ} (hL : 258 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 <
      (99 / 40 : ℝ) * ((287 / 500 : ℝ) * L + 9 / 2) ^ 2 := by
  have hroot : (107 / 200 : ℝ) * L + 24 / 5 < (287 / 500 : ℝ) * L + 9 / 2 := by nlinarith only [hL]
  have hpos : 0 < (107 / 200 : ℝ) * L + 24 / 5 := by nlinarith only [hL]
  have hsq := (sq_lt_sq₀ hpos.le (by linarith only [hroot, hpos])).mpr hroot
  exact mul_lt_mul_of_pos_left hsq (by norm_num only)

/-- A rational square-root proxy for the index-four Gamma bound. This isolates
the coefficient comparison used by the later envelope lemmas. -/
private theorem gamma_index_four_lt_proxy {L : ℝ} (hL : 258 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := by
  have hb : 0 < (107 / 200 : ℝ) * L + 24 / 5 := by nlinarith only [hL]
  have hc : (99 / 40 : ℝ) < (787 / 500 : ℝ) ^ 2 := by norm_num only
  have hs :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 <
      ((787 / 500 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5)) ^ 2 := by
    calc
      _ = (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by ring
      _ < (787 / 500 : ℝ) ^ 2 * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 :=
        mul_lt_mul_of_pos_right hc (sq_pos_of_pos hb)
      _ = _ := by ring
  have hr : (787 / 500 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by
    nlinarith only [hL]
  have hfactor : 0 ≤ (787 / 500 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) :=
    mul_nonneg (by norm_num only) hb.le
  have hsq := mul_self_le_mul_self hfactor hr
  exact lt_of_lt_of_le hs (by nlinarith only [hsq])

/-- For every `L ≥ 258`, `B₄(L)` is below the classical `(4/5)L²` branch. -/
theorem gamma_index_four_lt_four_fifths_log_sq {L : ℝ} (hL : 258 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < (4 / 5 : ℝ) * L ^ 2 := by
  have hp := gamma_index_four_lt_proxy hL
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ (89 / 100 : ℝ) * L := by nlinarith only [hL]
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor hr
  have hc : (89 / 100 : ℝ) ^ 2 < 4 / 5 := by norm_num only
  have hz : 0 < L ^ 2 := sq_pos_of_pos (by linarith only [hL])
  calc
    _ < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := hp
    _ ≤ (89 / 100 : ℝ) ^ 2 * L ^ 2 := by nlinarith only [hsq]
    _ < (4 / 5 : ℝ) * L ^ 2 := mul_lt_mul_of_pos_right hc hz

/-- For `L ≥ 34971`, `B₄(L)` is below the shifted rational branch with shift 117. -/
theorem gamma_index_four_lt_199_div_250_plus_117_sq {L : ℝ} (hL : 34971 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < (199 / 250 : ℝ) * (L + 117) ^ 2 := by
  have hp := gamma_index_four_lt_proxy (by linarith only [hL] : 258 ≤ L)
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ (89 / 100 : ℝ) * (L + 117) := by nlinarith only [hL]
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor hr
  have hc : (89 / 100 : ℝ) ^ 2 < 199 / 250 := by norm_num only
  have hz : 0 < (L + 117) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  calc
    _ < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := hp
    _ ≤ (89 / 100 : ℝ) ^ 2 * (L + 117) ^ 2 := by nlinarith only [hsq]
    _ < (199 / 250 : ℝ) * (L + 117) ^ 2 := mul_lt_mul_of_pos_right hc hz

/-- For `L ≥ 34971`, `B₄(L)` is below the shifted logarithmic branch with shift 29. -/
theorem gamma_index_four_lt_four_fifths_plus_29_sq {L : ℝ} (hL : 34971 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < (4 / 5 : ℝ) * (L + 29) ^ 2 := by
  have hp := gamma_index_four_lt_proxy (by linarith only [hL] : 258 ≤ L)
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ (89 / 100 : ℝ) * (L + 29) := by nlinarith only [hL]
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor hr
  have hc : (89 / 100 : ℝ) ^ 2 < 4 / 5 := by norm_num only
  have hz : 0 < (L + 29) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  calc
    _ < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := hp
    _ ≤ (89 / 100 : ℝ) ^ 2 * (L + 29) ^ 2 := by nlinarith only [hsq]
    _ < (4 / 5 : ℝ) * (L + 29) ^ 2 := mul_lt_mul_of_pos_right hc hz

/-- For `L ≥ 46330`, `B₄(L)` is below the shifted quadratic branch. -/
theorem gamma_index_four_lt_four_fifths_minus_two_sq {L : ℝ} (hL : 46330 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < (4 / 5 : ℝ) * (L - 2) ^ 2 := by
  have hp := gamma_index_four_lt_proxy (by linarith only [hL] : 258 ≤ L)
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ (89 / 100 : ℝ) * (L - 2) := by nlinarith only [hL]
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor hr
  have hc : (89 / 100 : ℝ) ^ 2 < 4 / 5 := by norm_num only
  have hz : 0 < (L - 2) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  calc
    _ < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := hp
    _ ≤ (89 / 100 : ℝ) ^ 2 * (L - 2) ^ 2 := by nlinarith only [hsq]
    _ < (4 / 5 : ℝ) * (L - 2) ^ 2 := mul_lt_mul_of_pos_right hc hz

/-- For `L ≥ 50880`, `B₄(L)` is below the logarithmically shifted square branch. -/
theorem gamma_index_four_lt_four_fifths_minus_log_sq {L : ℝ} (hL : 50880 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < (4 / 5 : ℝ) * (L - Real.log L) ^ 2 := by
  have hp := gamma_index_four_lt_proxy (by linarith only [hL] : 258 ≤ L)
  have hlog : Real.log L ≤ L / 300 + 19 / 4 := by
    calc
      Real.log L ≤ Real.log 300 + (L - 300) / 300 :=
        Analysis.log_le_log_add_sub_div (by norm_num only) (by linarith only [hL])
      _ ≤ L / 300 + 19 / 4 := by linarith only [LLS.clippedAffine_log_three_hundred_le]
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ (89 / 100 : ℝ) * (L - Real.log L) := by
    nlinarith only [hL, hlog]
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor hr
  have hc : (89 / 100 : ℝ) ^ 2 < 4 / 5 := by norm_num only
  have hz : 0 < (L - Real.log L) ^ 2 := sq_pos_of_pos (by nlinarith only [hL, hlog])
  calc
    _ < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := hp
    _ ≤ (89 / 100 : ℝ) ^ 2 * (L - Real.log L) ^ 2 := by nlinarith only [hsq]
    _ < (4 / 5 : ℝ) * (L - Real.log L) ^ 2 := mul_lt_mul_of_pos_right hc hz

/-- The index-four Gamma bound is below the adaptive cutoff for every `L ≥ 258`. -/
theorem gamma_index_four_lt_adaptive_sq {L : ℝ} (hL : 258 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 <
      (Analysis.adaptivePart2CutoffRoot L) ^ 2 := by
  have hlog : Real.log L ≤ L / 300 + 19 / 4 := by
    calc
      Real.log L ≤ Real.log 300 + (L - 300) / 300 :=
        Analysis.log_le_log_add_sub_div (by norm_num only) (by linarith only [hL])
      _ ≤ L / 300 + 19 / 4 := by linarith only [LLS.clippedAffine_log_three_hundred_le]
  have hY := LLS.PaperStatements.midscale_adaptive_lower (by linarith only [hL])
  have hp := gamma_index_four_lt_proxy hL
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ L - 2 * Real.log L + 91 / 20 := by
    nlinarith only [hL, hlog]
  have hstrict : (843 / 1000 : ℝ) * L + 38 / 5 < L - 2 * Real.log L + 91 / 20 := by
    nlinarith only [hL, hlog]
  have hroot : (843 / 1000 : ℝ) * L + 38 / 5 < Analysis.adaptivePart2CutoffRoot L :=
    lt_of_lt_of_le hstrict hY
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor (le_of_lt hroot)
  have hrootPos : 0 < Analysis.adaptivePart2CutoffRoot L := lt_trans (by nlinarith only [hL]) hroot
  have hright : 0 < (Analysis.adaptivePart2CutoffRoot L) ^ 2 := sq_pos_of_pos hrootPos
  exact lt_of_lt_of_le hp (by nlinarith only [hsq])

/-- The index-four bound also dominates the older shift-216 candidate wherever
that candidate is defined. -/
theorem gamma_index_four_lt_199_div_250_plus_216_sq {L : ℝ} (hL : 258 ≤ L) :
    (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 < (199 / 250 : ℝ) * (L + 216) ^ 2 := by
  have hp := gamma_index_four_lt_proxy hL
  have hr : (843 / 1000 : ℝ) * L + 38 / 5 ≤ (89 / 100 : ℝ) * (L + 216) := by nlinarith only [hL]
  have hfactor : 0 ≤ (843 / 1000 : ℝ) * L + 38 / 5 := by nlinarith only [hL]
  have hsq := mul_self_le_mul_self hfactor hr
  have hc : (89 / 100 : ℝ) ^ 2 < 199 / 250 := by norm_num only
  have hz : 0 < (L + 216) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  calc
    _ < ((843 / 1000 : ℝ) * L + 38 / 5) ^ 2 := hp
    _ ≤ (89 / 100 : ℝ) ^ 2 * (L + 216) ^ 2 := by nlinarith only [hsq]
    _ < (199 / 250 : ℝ) * (L + 216) ^ 2 := mul_lt_mul_of_pos_right hc hz

/-- From `L = 350000` onward, the Gaussian `16/25` branch is strictly below
the index-four Gamma branch. -/
theorem gaussian_relative_lt_gamma_index_four_sq {L : ℝ} (hL : 350000 ≤ L) :
    (16 / 25 : ℝ) * L ^ 2 < (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
  have hroot : (4 / 5 : ℝ) * L < (157 / 100 : ℝ) * ((107 / 200 : ℝ) * L) := by nlinarith only [hL]
  have hscaled : ((4 / 5 : ℝ) * L) ^ 2 < ((157 / 100 : ℝ) * ((107 / 200 : ℝ) * L)) ^ 2 :=
    (sq_lt_sq₀ (by positivity) (by positivity)).mpr hroot
  have hbase : 0 ≤ (107 / 200 : ℝ) * L := by positivity
  have hbaseShift : (107 / 200 : ℝ) * L ≤ (107 / 200 : ℝ) * L + 24 / 5 := by nlinarith only
  have hfactor : 0 ≤ (157 / 100 : ℝ) * ((107 / 200 : ℝ) * L) := mul_nonneg (by norm_num only) hbase
  have hsq :=
    mul_self_le_mul_self hfactor
      (mul_le_mul_of_nonneg_left hbaseShift (by norm_num only : (0 : ℝ) ≤ 157 / 100))
  have hcoef : (157 / 100 : ℝ) ^ 2 < 99 / 40 := by norm_num only
  have hshift : 0 < ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := sq_pos_of_pos (by nlinarith only [hL])
  have hbound :
    ((157 / 100 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5)) ^ 2 <
      (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
    calc
      _ = (157 / 100 : ℝ) ^ 2 * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by ring
      _ < (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := mul_lt_mul_of_pos_right hcoef hshift
      _ = _ := by ring
  calc
    (16 / 25 : ℝ) * L ^ 2 = ((4 / 5 : ℝ) * L) ^ 2 := by ring
    _ < ((157 / 100 : ℝ) * ((107 / 200 : ℝ) * L)) ^ 2 := hscaled
    _ ≤ ((157 / 100 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5)) ^ 2 := by nlinarith only [hsq]
    _ < (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
