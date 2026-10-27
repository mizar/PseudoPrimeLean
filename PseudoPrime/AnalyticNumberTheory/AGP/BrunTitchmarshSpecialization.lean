/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionCounting
public import PseudoPrime.AnalyticNumberTheory.AGP.CoarseProgressionSieve

/-! # Totient cases for the AGP Brun–Titchmarsh specialization

The AGP progression estimate uses the modulus `d*r*m`. Its totient relative
to `d*m` differs according to whether the prime `r` divides `d`. These lemmas
package both cases for the later analytic specialization.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: real parameters `X ≥ 16` and `1 ≤ r ≤ X`.

Claim: the logarithm of the scale ratio `X^3 / (4*r)` is at least
`(3/2) * log X`.

Proof: expand the logarithm of the quotient and product; use `r ≤ X` and
`log 16 = 2 * log 4` to absorb the constant factor `4`.

Role: this verifies the logarithmic denominator needed when applying
Brun–Titchmarsh to the modulus `4*d*r` at the fifth-power scale.
-/
theorem agp_log_ratio_lower_bound {X r : ℝ} (hX : 16 ≤ X) (hr : 1 ≤ r) (hrX : r ≤ X) :
    (3 / 2 : ℝ) * Real.log X ≤ Real.log (X ^ 3 / (4 * r)) := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) hX
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) hr
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (le_trans (by norm_num only : (1 : ℝ) ≤ 16) hX)
  have hlog4 : Real.log 4 ≤ (1 / 2 : ℝ) * Real.log X := by
    have hlog16 := Real.log_le_log (by norm_num only : (0 : ℝ) < 16) hX
    have hidentity : Real.log 16 = 2 * Real.log 4 := by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num only, Real.log_pow]
      norm_num only
    nlinarith only [hlog16, hidentity]
  have hlogr : Real.log r ≤ Real.log X := Real.log_le_log hrpos hrX
  have hratio : Real.log (X ^ 3 / (4 * r)) = 3 * Real.log X - (Real.log 4 + Real.log r) := by
    rw [Real.log_div (ne_of_gt (pow_pos hXpos 3))
        (mul_ne_zero (by norm_num only : (4 : ℝ) ≠ 0) (ne_of_gt hrpos)),
      Real.log_pow, Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (ne_of_gt hrpos)]
    norm_num only
  nlinarith only [hlog4, hlogr, hratio]

/--
Inputs: a prime `r` dividing `d` and an arbitrary modulus factor `m`.

Claim: multiplying `d*m` by `r` multiplies its totient by `r`.

Proof: rewrite `d*r*m` as `r*(d*m)` and use `Nat.totient_mul_of_prime_of_dvd`.

Role: this is the totient case needed when the bad prime factor already divides
the AGP divisor.
-/
theorem agp_totient_drm_eq_r_mul_totient_dm_of_dvd {d r m : ℕ} (hr : Nat.Prime r) (hrd : r ∣ d) :
    Nat.totient (d * r * m) = r * Nat.totient (d * m) := by
  have hfactor : d * r * m = r * (d * m) := by
    calc
      d * r * m = d * (r * m) := Nat.mul_assoc d r m
      _ = r * (d * m) := Nat.mul_left_comm d r m
  rw [hfactor]
  exact Nat.totient_mul_of_prime_of_dvd hr (dvd_mul_of_dvd_left hrd m)

/--
Inputs: a prime `r` that divides neither `d` nor `m`.

Claim: the totient of `d*r*m` is `(r-1)` times the totient of `d*m`.

Proof: primality reduces divisibility of `d*m` to the two excluded cases;
then use `Nat.totient_mul_of_prime_of_not_dvd`.

Role: this is the complementary totient case in the AGP
Brun–Titchmarsh specialization.
-/
theorem agp_totient_drm_eq_r_sub_one_mul_totient_dm_of_not_dvd {d r m : ℕ} (hr : Nat.Prime r)
    (hrd : ¬r ∣ d) (hrm : ¬r ∣ m) : Nat.totient (d * r * m) = (r - 1) * Nat.totient (d * m) := by
  have hnot : ¬r ∣ d * m := by
    intro h
    rcases hr.dvd_mul.mp h with hrd' | hrm'
    · exact hrd hrd'
    · exact hrm hrm'
  have hfactor : d * r * m = r * (d * m) := by
    calc
      d * r * m = d * (r * m) := Nat.mul_assoc d r m
      _ = d * (m * r) := by rw [Nat.mul_comm r m]
      _ = (d * m) * r := (Nat.mul_assoc d m r).symm
      _ = r * (d * m) := Nat.mul_comm (d * m) r
  rw [hfactor]
  exact Nat.totient_mul_of_prime_of_not_dvd hr hnot

/--
Inputs: a prime `r` coprime to `4` and a natural number `d`.

Claim: `φ(d*r*4)` is at least `(r-1) * φ(d*4)`.

Proof: split according to whether `r` divides `d`; the two totient formulas
proved above give equality in the second case and the stronger factor `r` in
the first case.

Role: supplies the totient lower bound for the coefficient comparison.
-/
theorem agp_totient_d4_lower_bound {d r : ℕ} (hr : Nat.Prime r) (hr4 : Nat.Coprime r 4) :
    (((r - 1) * Nat.totient (d * 4) : ℕ) : ℝ) ≤ (Nat.totient (d * r * 4) : ℝ) := by
  by_cases hrd : r ∣ d
  · rw [agp_totient_drm_eq_r_mul_totient_dm_of_dvd hr hrd]
    norm_cast
    exact Nat.mul_le_mul_right (Nat.totient (d * 4)) (Nat.sub_le r 1)
  · have hrnot4 : ¬r ∣ 4 := hr.coprime_iff_not_dvd.mp hr4
    rw [agp_totient_drm_eq_r_sub_one_mul_totient_dm_of_not_dvd hr hrd hrnot4]

/--
Inputs: nonnegative `Y`, `r ≥ 3`, positive `A`, `LX`, and `Lr`, with
`Lr ≥ (3/2) * LX` and `phiQ ≥ (r - 1) * A`.

Claim: the Brun–Titchmarsh quotient with denominator `phiQ * Lr` is at most
the coefficient `40/3` expression used by the AGP progression estimate.

Proof: compare denominators using the two lower bounds, then clear the positive
denominators and use `r ≤ 2 * (r - 1)`.

Role: this isolates the numerical coefficient step for the specialization.
-/
theorem agp_brun_titchmarsh_coefficient_comparison {Y r A LX Lr phiQ : ℝ} (hY : 0 ≤ Y) (hr : 3 ≤ r)
    (hA : 0 < A) (hLX : 0 < LX) (hLr : 0 < Lr) (hLratio : (3 / 2 : ℝ) * LX ≤ Lr)
    (hphi : (r - 1) * A ≤ phiQ) :
    2 * Y / (phiQ * Lr) ≤ (40 / 3 : ℝ) * r⁻¹ * (Y / A / (5 * LX)) := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 3) hr
  have hphiPos : 0 < phiQ := lt_of_lt_of_le (mul_pos (sub_pos.mpr (by linarith only [hr])) hA) hphi
  have hdenPos : 0 < phiQ * Lr := mul_pos hphiPos hLr
  have htargetPos : 0 < A * (5 * LX) := by positivity
  have hmain : r ≤ 2 * (r - 1) := by linarith only [hr]
  have hdenom : (r - 1) * A * ((3 / 2 : ℝ) * LX) ≤ phiQ * Lr := by
    calc
      (r - 1) * A * ((3 / 2 : ℝ) * LX) ≤ ((r - 1) * A) * Lr :=
        mul_le_mul_of_nonneg_left hLratio (mul_nonneg (by linarith only [hr]) hA.le)
      _ ≤ phiQ * Lr := mul_le_mul_of_nonneg_right hphi hLr.le
  have hcoef : (10 : ℝ) * r * A * LX ≤ (40 / 3 : ℝ) * phiQ * Lr := by
    have hscale :=
      mul_le_mul_of_nonneg_right hmain
        (show 0 ≤ (10 : ℝ) * A * LX from mul_nonneg (mul_nonneg (by norm_num only) hA.le) hLX.le)
    have hscale' : (10 : ℝ) * r * A * LX ≤ 20 * (r - 1) * A * LX := by
      calc
        10 * r * A * LX = r * (10 * A * LX) := by ring
        _ ≤ (2 * (r - 1)) * (10 * A * LX) := hscale
        _ = 20 * (r - 1) * A * LX := by ring
    have hden' : 20 * (r - 1) * A * LX ≤ (40 / 3 : ℝ) * (phiQ * Lr) := by
      calc
        20 * (r - 1) * A * LX = (40 / 3 : ℝ) * ((r - 1) * A * ((3 / 2 : ℝ) * LX)) := by ring
        _ ≤ (40 / 3 : ℝ) * (phiQ * Lr) :=
          mul_le_mul_of_nonneg_left hdenom (by norm_num only : (0 : ℝ) ≤ 40 / 3)
    nlinarith only [hscale', hden']
  rw [div_le_iff₀ hdenPos]
  field_simp [ne_of_gt hrpos, ne_of_gt hA, ne_of_gt hLX]
  have hcoefY := mul_le_mul_of_nonneg_left hcoef hY
  nlinarith only [hcoefY]

/--
Inputs: a nonnegative sieve coefficient `C`, nonnegative scale `Y`, `r ≥ 3`,
and positive denominator data with `Lr ≥ (3/2) LX` and
`phiQ ≥ (r - 1) A`.

Claim: `C * Y / (phiQ * Lr)` is at most the AGP expression with coefficient
`20 C / 3`.

Proof: compare the denominators, use `r ≤ 2(r - 1)`, and clear positive
denominators.

Role: transports a pointwise progression bound with arbitrary coefficient
into the fixed-scale divisor average.
-/
theorem agp_coarse_progression_coefficient_comparison {C Y r A LX Lr phiQ : ℝ} (hC : 0 ≤ C)
    (hY : 0 ≤ Y) (hr : 3 ≤ r) (hA : 0 < A) (hLX : 0 < LX) (hLr : 0 < Lr)
    (hLratio : (3 / 2 : ℝ) * LX ≤ Lr) (hphi : (r - 1) * A ≤ phiQ) :
    C * Y / (phiQ * Lr) ≤ (20 * C / 3 : ℝ) * r⁻¹ * (Y / A / (5 * LX)) := by
  have hrpos : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 3) hr
  have hphiPos : 0 < phiQ := lt_of_lt_of_le (mul_pos (sub_pos.mpr (by linarith only [hr])) hA) hphi
  have hdenPos : 0 < phiQ * Lr := mul_pos hphiPos hLr
  have htargetPos : 0 < A * (5 * LX) := mul_pos hA (mul_pos (by norm_num only) hLX)
  have hmain : r ≤ 2 * (r - 1) := by linarith only [hr]
  have hdenom : (r - 1) * A * ((3 / 2 : ℝ) * LX) ≤ phiQ * Lr := by
    calc
      (r - 1) * A * ((3 / 2 : ℝ) * LX) ≤ ((r - 1) * A) * Lr :=
        mul_le_mul_of_nonneg_left hLratio
          (mul_nonneg (sub_nonneg.mpr (by linarith only [hr])) hA.le)
      _ ≤ phiQ * Lr := mul_le_mul_of_nonneg_right hphi hLr.le
  have hcoef : 5 * C * r * A * LX ≤ (20 * C / 3 : ℝ) * phiQ * Lr := by
    have hscale :=
      mul_le_mul_of_nonneg_right hmain
        (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hC) (mul_nonneg hA.le hLX.le))
    have hden' : 4 * C * ((r - 1) * A * ((3 / 2 : ℝ) * LX)) ≤ 4 * C * (phiQ * Lr) :=
      mul_le_mul_of_nonneg_left hdenom (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hC)
    nlinarith only [hscale, hden']
  rw [div_le_iff₀ hdenPos]
  field_simp [ne_of_gt hrpos, ne_of_gt hA, ne_of_gt hLX]
  have hcoefY := mul_le_mul_of_nonneg_left hcoef hY
  nlinarith only [hcoefY]

/--
Inputs: the standard Brun–Titchmarsh estimate, a fifth-power scale `X ≥ 16`,
a positive divisor `d`, a prime `r ≤ X` coprime to `4`, and an admissible
residue class modulo `d*r*4`.

Claim: at `Y = d*X^3` and `Q = d*r*4`, the progression count is at most
`(40/3) * r⁻¹ * Y / (φ(d*4) * log(X^5))`.

Proof: establish `1 ≤ Q < Y`, cancel `d` in the logarithmic ratio, use the
totient lower bound above, and apply the coefficient comparison.

Role: this converts the standard Brun–Titchmarsh input to the estimate used
by the fixed-scale AGP prime-count construction.
-/
theorem agp_brun_titchmarsh_bound_of_input (hBT : AGPBrunTitchmarshInput) {d X r a : ℕ}
    (hX : 16 ≤ X) (hd : 0 < d) (hr : Nat.Prime r) (hrX : r ≤ X) (hr4 : Nat.Coprime r 4)
    (hcop : Nat.Coprime a (d * r * 4)) :
    (primeCountInProgression (d * X ^ 3) (d * r * 4) a : ℝ) ≤
      (40 / 3 : ℝ) * (r : ℝ)⁻¹ *
        (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hrnot4 : ¬r ∣ 4 := hr.coprime_iff_not_dvd.mp hr4
  have hrge3 : 3 ≤ r := by
    by_contra h
    have hrle2 : r ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
    have hrEq2 : r = 2 := Nat.le_antisymm hrle2 hr.two_le
    subst r
    exact hrnot4 (by norm_num only : 2 ∣ 4)
  have hQpos : 0 < d * r * 4 := Nat.mul_pos (Nat.mul_pos hd hr.pos) (by norm_num only)
  have hQone : 1 ≤ d * r * 4 := Nat.succ_le_of_lt hQpos
  have hQltY : d * r * 4 < d * X ^ 3 := by
    have hXpos : 0 < X := lt_of_lt_of_le (by norm_num only) hX
    have hXsq : 5 ≤ X ^ 2 := by
      exact le_trans (by norm_num only : 5 ≤ 16 ^ 2) (Nat.pow_le_pow_left hX 2)
    have hbase : r * 4 < X ^ 3 := by
      calc
        r * 4 = 4 * r := Nat.mul_comm r 4
        _ ≤ 4 * X := Nat.mul_le_mul_left 4 hrX
        _ < X * X ^ 2 := by
          have hmul :=
            Nat.mul_lt_mul_of_pos_left (lt_of_lt_of_le (by norm_num only : 4 < 5) hXsq) hXpos
          simpa only [Nat.mul_comm X 4] using hmul
        _ = X ^ 3 := by
          rw [Nat.mul_comm X (X ^ 2)]
          norm_num only [pow_succ]
    simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_left hbase hd
  have hBT' := hBT (d * X ^ 3) (d * r * 4) a hQone hQltY hcop
  have hXreal : (16 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.pos
  have hrXreal : (r : ℝ) ≤ (X : ℝ) := by exact_mod_cast hrX
  have hlogratio := agp_log_ratio_lower_bound hXreal hrreal hrXreal
  have hratio : ((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ) = (X : ℝ) ^ 3 / (4 * (r : ℝ)) := by
    norm_cast
    field_simp [ne_of_gt (Nat.cast_pos.mpr hd)]
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring
  have hLratio :
    (3 / 2 : ℝ) * Real.log (X : ℝ) ≤ Real.log (((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ)) := by
    rw [hratio]
    exact hlogratio
  have hLXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num only) hX))
  have hLrpos : 0 < Real.log (((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ)) :=
    lt_of_lt_of_le (by nlinarith only [hLXpos]) hLratio
  have hApos : 0 < (Nat.totient (d * 4) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos hd (by norm_num only)))
  have hphiNat := agp_totient_d4_lower_bound (d := d) hr hr4
  have hphiNatReal :
    ((r - 1 : ℕ) : ℝ) * (Nat.totient (d * 4) : ℝ) ≤ (Nat.totient (d * r * 4) : ℝ) := by
    exact_mod_cast hphiNat
  have hphi : ((r : ℝ) - 1) * (Nat.totient (d * 4) : ℝ) ≤ (Nat.totient (d * r * 4) : ℝ) := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hr.pos)] at hphiNatReal
    simpa only [Nat.cast_one] using hphiNatReal
  have hlogX5 : Real.log ((X ^ 5 : ℕ) : ℝ) = 5 * Real.log (X : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only
  rw [hlogX5]
  exact
    le_trans hBT'
      (agp_brun_titchmarsh_coefficient_comparison (by exact_mod_cast Nat.zero_le (d * X ^ 3))
        (by exact_mod_cast hrge3) hApos hLXpos hLrpos hLratio hphi)

/--
Inputs: a fifth-power scale `X ≥ 32`, a positive divisor `d`, a prime `r ≤ X`
coprime to `4`, and an admissible residue class modulo `d*r*4`.

Claim: at `Y = d*X^3` and `Q = d*r*4`, the progression count is at most
`(640/3) * r⁻¹ * Y / (φ(d*4) * log(X^5))`.

Proof: apply the unconditional coefficient-32 progression estimate at scale
`Y/Q ≥ 256`, then use the logarithmic-ratio and totient lower bounds to
compare denominators.

Role: replaces the conditional Brun–Titchmarsh input in the fixed-scale
AGP prime-count construction.
-/
theorem agp_coarse_sieve_bound {d X r a : ℕ} (hX : 32 ≤ X) (hd : 0 < d) (hr : Nat.Prime r)
    (hrX : r ≤ X) (hr4 : Nat.Coprime r 4) (hcop : Nat.Coprime a (d * r * 4)) :
    (primeCountInProgression (d * X ^ 3) (d * r * 4) a : ℝ) ≤
      (640 / 3 : ℝ) * (r : ℝ)⁻¹ *
        (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) := by
  have hrnot4 : ¬r ∣ 4 := hr.coprime_iff_not_dvd.mp hr4
  have hrge3 : 3 ≤ r := by
    by_contra h
    have hrle2 : r ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge h)
    have hrEq2 : r = 2 := Nat.le_antisymm hrle2 hr.two_le
    subst r
    exact hrnot4 (by norm_num only : 2 ∣ 4)
  have hXreal : (32 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hrreal : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.pos
  have hrXreal : (r : ℝ) ≤ (X : ℝ) := by exact_mod_cast hrX
  have hXpos : 0 < (X : ℝ) := lt_of_lt_of_le (by norm_num only) hXreal
  have hrpos : 0 < (r : ℝ) := lt_of_lt_of_le (by norm_num only) hrreal
  have hXsq : (1024 : ℝ) ≤ (X : ℝ) ^ 2 := by nlinarith only [hXreal]
  have hratio : ((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ) = (X : ℝ) ^ 3 / (4 * (r : ℝ)) := by
    norm_cast
    field_simp [ne_of_gt (Nat.cast_pos.mpr hd)]
    simp only [Nat.cast_mul, Nat.cast_pow]
    ring
  have hratioLower : (256 : ℝ) ≤ ((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ) := by
    rw [hratio]
    have hxstep : (X : ℝ) ^ 2 / 4 ≤ (X : ℝ) ^ 3 / (4 * (r : ℝ)) := by
      apply
        (div_le_div_iff₀ (by norm_num only : (0 : ℝ) < 4)
            (mul_pos (by norm_num only : (0 : ℝ) < 4) hrpos)).2
      have hmul := mul_le_mul_of_nonneg_right hrXreal (sq_nonneg (X : ℝ))
      nlinarith only [hmul]
    calc
      256 ≤ (X : ℝ) ^ 2 / 4 :=
        (le_div_iff₀ (by norm_num only : (0 : ℝ) < 4)).2 (by nlinarith only [hXsq])
      _ ≤ (X : ℝ) ^ 3 / (4 * (r : ℝ)) := hxstep
  have hQpos : 0 < d * r * 4 := Nat.mul_pos (Nat.mul_pos hd hr.pos) (by norm_num only)
  have hcoarse := primeCountInProgression_le_thirty_two (a := a) hQpos hratioLower
  have hXreal16 : (16 : ℝ) ≤ (X : ℝ) := le_trans (by norm_num only) hXreal
  have hlogratio := agp_log_ratio_lower_bound hXreal16 hrreal hrXreal
  have hLratio :
    (3 / 2 : ℝ) * Real.log (X : ℝ) ≤ Real.log (((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ)) := by
    rw [hratio]
    exact hlogratio
  have hLXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num only) hX))
  have hLrpos : 0 < Real.log (((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ)) :=
    lt_of_lt_of_le (by nlinarith only [hLXpos]) hLratio
  have hApos : 0 < (Nat.totient (d * 4) : ℝ) := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.mul_pos hd (by norm_num only)))
  have hphiNat := agp_totient_d4_lower_bound (d := d) hr hr4
  have hphiNatReal :
    ((r - 1 : ℕ) : ℝ) * (Nat.totient (d * 4) : ℝ) ≤ (Nat.totient (d * r * 4) : ℝ) := by
    exact_mod_cast hphiNat
  have hphi : ((r : ℝ) - 1) * (Nat.totient (d * 4) : ℝ) ≤ (Nat.totient (d * r * 4) : ℝ) := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt hr.pos)] at hphiNatReal
    simpa only [Nat.cast_one] using hphiNatReal
  have hlogX5 : Real.log ((X ^ 5 : ℕ) : ℝ) = 5 * Real.log (X : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only
  have hcomparison :=
    agp_coarse_progression_coefficient_comparison (C := 32) (Y := ((d * X ^ 3 : ℕ) : ℝ)) (r :=
      (r : ℝ)) (A := (Nat.totient (d * 4) : ℝ)) (LX := Real.log (X : ℝ)) (Lr :=
      Real.log (((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ))) (phiQ :=
      (Nat.totient (d * r * 4) : ℝ)) (by norm_num only) (by exact_mod_cast Nat.zero_le (d * X ^ 3))
      (by exact_mod_cast hrge3) hApos hLXpos hLrpos hLratio hphi
  calc
    (primeCountInProgression (d * X ^ 3) (d * r * 4) a : ℝ) ≤
        32 * ((d * X ^ 3 : ℕ) : ℝ) /
          ((Nat.totient (d * r * 4) : ℝ) *
            Real.log (((d * X ^ 3 : ℕ) : ℝ) / ((d * r * 4 : ℕ) : ℝ))) :=
      hcoarse
    _ ≤
        (20 * 32 / 3 : ℝ) * (r : ℝ)⁻¹ *
          (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / (5 * Real.log (X : ℝ))) :=
      hcomparison
    _ =
        (640 / 3 : ℝ) * (r : ℝ)⁻¹ *
          (((d * X ^ 3 : ℕ) : ℝ) / (Nat.totient (d * 4) : ℝ) / Real.log ((X ^ 5 : ℕ) : ℝ)) :=
      by
      rw [hlogX5]; norm_num only

end PseudoPrime.AnalyticNumberTheory.AGP
