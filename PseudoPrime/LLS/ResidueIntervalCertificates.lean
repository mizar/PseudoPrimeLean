/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ResidueIntervalGeometry
public import PseudoPrime.LLS.ResidueIntervalNumerics

/-! Rational interval certificates for the least prime in a unit residue. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Checked data for a modulus interval with at most W distinct prime factors.
The rational endpoints bound the modulus logarithm, totient, radius and cutoff
logarithm. Guards enforce their signs, the totient ratio and exponent cutoff;
logarithm, odd-root and gap checks supply the remaining analytic inputs.
The common soundness theorem yields the least-prime bound under GRH. -/
structure ResidueIntervalCertificate where
  /-- Lower modulus endpoint. -/
  lower : ℕ
  /-- Upper modulus endpoint. -/
  upper : ℕ
  /-- Upper number of distinct prime factors. -/
  W : ℕ
  /-- Upper prime-power exponent. -/
  K : ℕ
  /-- Binary scaling exponent for the lower modulus logarithm. -/
  ja : ℕ
  /-- Binary scaling exponent for the upper modulus logarithm. -/
  jb : ℕ
  /-- Binary scaling exponent for the upper radius squared. -/
  jx : ℕ
  /-- Number of terms in each logarithm certificate. -/
  n : ℕ
  /-- Lower bound on the modulus logarithm. -/
  lo : ℚ
  /-- Upper bound on the modulus logarithm. -/
  hi : ℚ
  /-- Lower bound on the totient. -/
  h₀ : ℚ
  /-- Lower bound on the totient-log radius. -/
  s₀ : ℚ
  /-- Upper bound on the radius. -/
  S : ℚ
  /-- Upper bound on the cutoff logarithm. -/
  T : ℚ
  /-- Natural upper bounds on the odd roots of the lower cutoff. -/
  roots : ℕ → ℕ
  /-- Natural upper bounds on the square roots of the odd-root bounds. -/
  squareRoots : ℕ → ℕ
  /-- Domain, sign, endpoint consistency and exponent inequalities. -/
  guards :
    64 ≤ lower ∧
      upper ≤ 20000 ∧
      1 ≤ W ∧
      W ≤ 5 ∧
      0 ≤ NumberTheory.totientPrimeCountLowerRatio W ∧
      0 ≤ lo ∧
      h₀ = NumberTheory.totientPrimeCountLowerRatio W * lower ∧
      s₀ = h₀ * lo ∧
      S = upper * hi ∧
      2 ≤ h₀ ∧
      0 < s₀ ∧
      65536 ≤ s₀ ^ 2 ∧
      1719 / 1000 ≤ lo ∧ 1 + 23 / 40 ≤ T ∧ T < (K + 1) * (6931471803 / 10000000000 : ℚ)
  /-- Kernel-checkable logarithm bounds at both endpoints and the upper cutoff. -/
  logChecks :
    Analysis.rationalLogIntervalCheck lower ja n lo hi = true ∧
      Analysis.rationalLogIntervalCheck upper jb n lo hi = true ∧
      Analysis.rationalLogIntervalCheck (S ^ 2) jx n 0 T = true
  /-- Power inequalities for all odd exponents from 3 through K. -/
  rootChecks :
    ∀ k ∈ (Finset.Icc 3 K).filter Odd, s₀ ^ 2 ≤ (roots k : ℚ) ^ k ∧ roots k ≤ squareRoots k ^ 2
  /-- Strict rational comparison of the normalized majorant with 1.719. -/
  gapCheck :
    decide (residueParityIntervalMajorantRat lower h₀ s₀ hi T W K roots squareRoots < 1719 / 1000) =
      true

/-- For a modulus in the certified interval with the certified prime-count bound,
the logarithm, totient and radius lie within their endpoints. Apply the common
endpoint estimates and the certificate's rational consistency identities.
These bounds supply the geometric input for the GRH least-prime theorem. -/
theorem ResidueIntervalCertificate.geometry (c : ResidueIntervalCertificate) {q : ℕ}
    (hl : c.lower ≤ q) (hu : q ≤ c.upper) (hw : q.primeFactors.card ≤ c.W) :
    (c.lo : ℝ) ≤ Real.log q ∧
      Real.log q ≤ c.hi ∧
      (c.h₀ : ℝ) ≤ q.totient ∧
      (c.s₀ : ℝ) ≤ (q.totient : ℝ) * Real.log q ∧ (q.totient : ℝ) * Real.log q ≤ (c.S : ℝ) := by
  rcases c.guards with ⟨hl64, _, hw1, hw5, hr, hlo, heh, hes, heS, _⟩
  have hg :=
    totientLogRadius_bounds_of_endpoint_checks ((by decide : 0 < 64).trans_le hl64) hl hu hw1 hw5 hw
      ((Rat.cast_nonneg (K := ℝ)).mpr hr) hlo c.logChecks.1 c.logChecks.2.1
  have hh := congrArg (fun r : ℚ ↦ (r : ℝ)) heh
  have hs := congrArg (fun r : ℚ ↦ (r : ℝ)) hes
  have hS := congrArg (fun r : ℚ ↦ (r : ℝ)) heS
  simp only [Rat.cast_mul, Rat.cast_natCast] at hh hs hS
  exact ⟨hg.1, hg.2.1, hh.symm ▸ hg.2.2.1, hs.symm ▸ hh.symm ▸ hg.2.2.2.1, hS.symm ▸ hg.2.2.2.2⟩

/-- Under GRH, every unit residue for a modulus satisfying this certificate has
a least prime below the squared totient-log radius. Derive the cutoff and sign
guards from the endpoint data, cast the root inequalities to the reals and apply
the common prime-free comparison. Each interval uses this single analytic proof. -/
theorem ResidueIntervalCertificate.leastPrime (c : ResidueIntervalCertificate) {q : ℕ} [NeZero q]
    (a : (ZMod q)ˣ) (hl : c.lower ≤ q) (hu : q ≤ c.upper) (hw : q.primeFactors.card ≤ c.W)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      IsLeast {n : ℕ | n.Prime ∧ (n : ZMod q) = (a : ZMod q)} p ∧
        (p : ℝ) ≤ ((q.totient : ℝ) * Real.log q) ^ 2 := by
  rcases c.guards with ⟨hl64, hu20, _, _, _, _, _, _, _, hh0, hs0, hx0, hL0, hT0, hK0⟩
  have hg := c.geometry hl hu hw
  have hx :=
    totientLogCutoff_bounds_of_radius_checks hs0 hg.2.2.2.1 hg.2.2.2.2 hx0 c.logChecks.2.2 hK0
  have hh0R : (2 : ℝ) ≤ c.h₀ := by exact_mod_cast hh0
  have hh := hh0R.trans hg.2.2.1
  have hL0R : (1719 / 1000 : ℝ) ≤ c.lo := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using (Rat.cast_le (K := ℝ)).mpr hL0
  have hL := hL0R.trans hg.1
  have hs0R := (Rat.cast_pos (K := ℝ)).mpr hs0
  have hs := hs0R.trans_le hg.2.2.2.1
  have hT0R : (1 + 23 / 40 : ℝ) ≤ c.T := by
    simpa only [Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr hT0
  have hT := (by norm_num only : (0 : ℝ) ≤ 1 + 23 / 40).trans hT0R
  have hpow : ∀ k ∈ (Finset.Icc 3 c.K).filter Odd, (c.s₀ : ℝ) ^ 2 ≤ (c.roots k : ℝ) ^ k := by
    intro k hk
    have hb := (Rat.cast_le (K := ℝ)).mpr (c.rootChecks k hk).1
    simpa only [Rat.cast_pow, Rat.cast_natCast] using hb
  have hsq : ∀ k ∈ (Finset.Icc 3 c.K).filter Odd, (c.roots k : ℝ) ≤ (c.squareRoots k : ℝ) ^ 2 := by
    intro k hk
    exact_mod_cast (c.rootChecks k hk).2
  have hC :=
    residueParityIntervalCoefficient_nonneg hh ((by norm_num only : (0 : ℝ) < 65536).trans_le hx.1)
      hL hT
  have hR := residueParityReciprocalCorrection_nonneg hs hT0R
  have hq0 : (0 : ℝ) < c.lower := Nat.cast_pos.mpr ((by decide : 0 < 64).trans_le hl64)
  exact
    exists_least_prime_in_residue_le_of_interval_power_certificates a (hl64.trans hl)
      (hu.trans hu20) hGRH hh ((by norm_num only : (0 : ℝ) < 2).trans_le hh0R) hg.2.2.1 hs0R
      hg.2.2.2.1 hq0 (Nat.cast_le.mpr hl) rfl hx.1 hL hg.2.1 hT hx.2.1 hw hx.2.2
      (fun k ↦ (c.roots k : ℝ)) (fun k ↦ (c.squareRoots k : ℝ)) (fun k _ ↦ Nat.cast_nonneg _)
      (fun k _ ↦ Nat.cast_nonneg _) hpow hsq hC hR
      (by simpa only [Rat.cast_natCast] using residueParityIntervalGap_of_rational_check c.gapCheck)

end PseudoPrime.LLS.PaperStatements
