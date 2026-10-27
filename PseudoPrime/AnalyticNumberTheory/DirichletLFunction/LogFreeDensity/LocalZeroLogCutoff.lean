/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroPowerSums

/-! # Logarithmic remote-tail cutoffs for completed zero detection -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a real mass factor and an exponent above its logarithmic ceiling, the
geometric ratio absorbs that factor. Compare logarithms with the positive reciprocal
base and cancel the two powers. This replaces the linear remote-tail threshold. -/
theorem geometric_remote_ratio_le_one_of_log_cutoff (A : ℝ) (m : ℕ)
    (hm : Nat.ceil (Real.log (max A 1) / Real.log (8 / 3 : ℝ)) ≤ m) : A * (3 / 8 : ℝ) ^ m ≤ 1 := by
  have hmax : (0 : ℝ) < max A 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlog : 0 < Real.log (8 / 3 : ℝ) := Real.log_pos (by norm_num only)
  have hceil := (Nat.le_ceil (Real.log (max A 1) / Real.log (8 / 3 : ℝ))).trans (Nat.cast_le.mpr hm)
  have hlogbound := (div_le_iff₀ hlog).mp hceil
  have hpower : max A 1 ≤ (8 / 3 : ℝ) ^ m := by
    apply (Real.log_le_log_iff hmax (pow_pos (by norm_num only) m)).mp
    rw [Real.log_pow]
    exact hlogbound
  calc
    A * (3 / 8 : ℝ) ^ m ≤ (8 / 3 : ℝ) ^ m * (3 / 8 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hpower) (pow_nonneg (by norm_num only) m)
    _ = 1 := by
      rw [← mul_pow]; norm_num only [one_pow]

/-- For a nonnegative scale, the logarithmic cutoff makes the remote mass bound
smaller than the matching power scale. Factor off two powers and apply geometric
absorption. This is the scalar input to the actual completed-zero tail estimate. -/
theorem geometric_remote_tail_matching_scale_log_cutoff (η N S : ℝ) (k : ℕ) (hη : 0 ≤ η)
    (hk : 2 ≤ k)
    (hcut : Nat.ceil (Real.log (max (72 * N * S * η ^ 2) 1) / Real.log (8 / 3 : ℝ)) + 2 ≤ k) :
    8 * N * S * (3 * η) ^ k ≤ (8 * η) ^ (k - 2) := by
  have hsmall :=
    geometric_remote_ratio_le_one_of_log_cutoff (72 * N * S * η ^ 2) (k - 2)
      (Nat.le_sub_of_add_le hcut)
  have heq :
    8 * N * S * (3 * η) ^ k = (72 * N * S * η ^ 2 * (3 / 8 : ℝ) ^ (k - 2)) * (8 * η) ^ (k - 2) := by
    conv_lhs => rw [← Nat.sub_add_cancel hk, pow_add]
    rw [mul_assoc (72 * N * S * η ^ 2), ← mul_pow]
    rw [show (3 / 8 : ℝ) * (8 * η) = 3 * η by ring]
    ring
  rw [heq]
  have hpow : 0 ≤ (8 * η) ^ (k - 2) := pow_nonneg (mul_nonneg (by norm_num only) hη) _
  exact (mul_le_mul_of_nonneg_right hsmall hpow).trans_eq (one_mul _)

/-- For conductor, shift, height, mass scale, and a requested minimum order, define
the logarithmic remote-tail cutoff. Take the ceiling of the logarithm of the
scaled inverse-square mass, add two, and retain the minimum order. This controls
the same remote power sum as the earlier linear cutoff. -/
noncomputable def completedGenusRemoteTailLogCutoff (q : ℕ) (η t N : ℝ) (Kmin : ℕ) : ℕ :=
  max
    (Nat.ceil
        (Real.log
            (max
              (72 * N *
                ((1 / η) *
                  (4 / η + completedGenusMassShiftConstant * (Real.log (4 + |t|) + 1) + Real.log q +
                    4 +
                    completedGenusMassCenterConstant * (Real.log 4 + 1))) *
                η ^ 2)
              1) /
          Real.log (8 / 3 : ℝ)) +
      2)
    Kmin

/-- The logarithmic remote-tail cutoff is at least two for all inputs. Its first
maximum argument contains the two required base powers. This validates the genus
moment estimate at every order above the cutoff. -/
theorem completedGenusRemoteTailLogCutoff_ge_two (q : ℕ) (η t N : ℝ) (Kmin : ℕ) :
    2 ≤ completedGenusRemoteTailLogCutoff q η t N Kmin :=
  (Nat.le_add_left 2 _).trans (le_max_left _ _)

/-- For a primitive nonprincipal character, positive shift at most one half,
positive mass scale, and a remote zero set, bound every power sum above the explicit
logarithmic cutoff at its matching inverse-power scale. Combine the unconditional
inverse-square mass estimate with logarithmic geometric absorption. This improves
the order budget used by local zero detection without a bounded conductor-height assumption. -/
theorem completed_genus_remote_power_le_log_cutoff {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) (S : Set ℂ)
    [DecidablePred fun ρ : ℂ ↦ ρ ∈ S] {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1 / 2) (t : ℝ) {N : ℝ}
    (hN : 0 < N) (Kmin k : ℕ) (hk : completedGenusRemoteTailLogCutoff q η t N Kmin ≤ k)
    (hremote : ∀ ρ ∈ S, 8 * η ≤ ‖(((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ‖) :
    ‖∑' ρ : ℂ,
          ((if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0 : ℝ) :
              ℂ) *
            (if ρ ∈ S then ((((1 + η : ℝ) : ℂ) + Complex.I * t) - ρ)⁻¹ else 0) ^ k‖ ≤
      (1 / (8 * N)) * (1 / (3 * η)) ^ k := by
  let s : ℂ := ((1 + η : ℝ) : ℂ) + Complex.I * t
  have hs : 1 < s.re := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith only [hη]
  obtain ⟨A, B, hAeq, hBeq, _, _, hglobal⟩ :=
    exists_completed_genus_inverse_square_mass_le_uniform_bound hq hχ hp hinv hη hη1 t
  let M := (1 / η) * (4 / η + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 + B * (Real.log 4 + 1))
  have hMass :=
    (completed_genus_inverse_square_subset_mass_le hq hχ hp hinv S hs).trans
      (show
        ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 ≤ M
        from hglobal)
  have hkTwo := (completedGenusRemoteTailLogCutoff_ge_two q η t N Kmin).trans hk
  have hcut : Nat.ceil (Real.log (max (72 * N * M * η ^ 2) 1) / Real.log (8 / 3 : ℝ)) + 2 ≤ k := by
    have hmax :=
      le_max_left (Nat.ceil (Real.log (max (72 * N * M * η ^ 2) 1) / Real.log (8 / 3 : ℝ)) + 2) Kmin
    apply hmax.trans
    simpa only [completedGenusRemoteTailLogCutoff, M, hAeq, hBeq] using hk
  have hsmallM := geometric_remote_tail_matching_scale_log_cutoff η N M k hη.le hkTwo hcut
  have hsmall :
    8 * N *
        (∑' ρ : ℂ,
          (if ρ ∈ S then (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) else 0) *
            ‖if ρ ∈ S then (s - ρ)⁻¹ else 0‖ ^ 2) *
        (3 * η) ^ k ≤
      (8 * η) ^ (k - 2) := by
    have hscaled :=
      mul_le_mul_of_nonneg_left hMass (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8) hN.le)
    exact
      (mul_le_mul_of_nonneg_right hscaled
            (pow_nonneg (mul_nonneg (by norm_num only) hη.le) k)).trans
        hsmallM
  exact
    norm_tsum_completed_genus_remote_reciprocal_power_le_matching_scale hq hχ hp hinv S hs hη hN
      hremote k hkTwo hsmall

/-- For a nonprincipal completed L-function, center, scale, and order, sum the
reciprocal-distance powers over its finite local divisor support, with analytic
multiplicity. This is the near-zero contribution in the genus moment identity. -/
noncomputable def completedLFunctionLocalReciprocalMoment {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (c : ℂ) (η : ℝ) (m : ℕ) : ℂ :=
  ∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
    ((MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v : ℤ) : ℂ) *
      (c - v)⁻¹ ^ m

/-- For a completed L-function, center, scale, and order, sum reciprocal-distance
powers over zeros at distance at least `80η`, retaining divisor multiplicity.
The complementary near terms are zero. This is the remote contribution controlled
by the logarithmic cutoff. -/
noncomputable def completedLFunctionRemoteReciprocalMoment {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (c : ℂ) (η : ℝ) (m : ℕ) : ℂ :=
  ∑' v : ℂ,
    ((if 80 * η ≤ ‖c - v‖ then (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℝ) else 0 :
          ℝ) :
        ℂ) *
      (if 80 * η ≤ ‖c - v‖ then (c - v)⁻¹ else 0) ^ m

/-- For a primitive nonprincipal character and a right-of-one center, bound the
actual remote reciprocal moment at every order above the logarithmic cutoff.
Identify the affine center and apply the remote-set estimate. This supplies the
tail in the same center convention as local zero detection. -/
theorem completedLFunction_remote_moment_le_log_cutoff {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1 / 2) {c : ℂ} (t : ℝ) (hcre : c.re = 1 + η) (hcim : c.im = t) {N : ℝ}
    (hN : 0 < N) (Kmin k : ℕ) (hk : completedGenusRemoteTailLogCutoff q η t N Kmin ≤ k) :
    ‖completedLFunctionRemoteReciprocalMoment χ c η k‖ ≤ (1 / (8 * N)) * (1 / (3 * η)) ^ k := by
  classical
  have hcenter : c = ((1 + η : ℝ) : ℂ) + Complex.I * t := by
    apply Complex.ext
    · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hcre
    · simpa only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, zero_add, one_mul] using hcim
  let S : Set ℂ := {v | 80 * η ≤ ‖c - v‖}
  have hremote : ∀ v ∈ S, 8 * η ≤ ‖(((1 + η : ℝ) : ℂ) + Complex.I * t) - v‖ := by
    intro v hv
    rw [← hcenter]
    exact (by linarith only [hη] : 8 * η ≤ 80 * η).trans hv
  have htail :=
    completed_genus_remote_power_le_log_cutoff hq hχ hp hinv S hη hη1 t hN Kmin k hk hremote
  simpa only [completedLFunctionRemoteReciprocalMoment, hcenter, S, Set.mem_ofPred_eq] using htail

/-- For an actual near-one zero and a small positive scale, choose the local
multiplicity cap and logarithmic remote cutoff, then select a common power order.
The local contribution survives the remote tail with an explicit positive lower
bound. Reuse the rectangle cap, select a new local block, and apply the reverse
triangle inequality. This removes the earlier linear remote-cutoff cost. -/
theorem exists_completedLFunction_local_remote_moment_log_cutoff {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin) {c ρ : ℂ}
    (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ C K m : ℕ,
      C =
          Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
        K = completedGenusRemoteTailLogCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
        Kmin ≤ K ∧
        2 ≤ K ∧
        K ≤ m ∧
        m ≤ K * C ∧
        (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m ≤
          ‖completedLFunctionLocalReciprocalMoment χ hχ c η m +
              completedLFunctionRemoteReciprocalMoment χ c η m‖ := by
  obtain ⟨_, _, _, _, C, _, _, _, _, _, hmass, _, _, hCeq⟩ :=
    exists_completedLFunction_local_zero_block_with_remote_tail_matching_scale hq hχ hp hinv hη
      hηsmall Kmin hKmin hcre hcim hρre hzero hc
  let K := completedGenusRemoteTailLogCutoff q η ρ.im ((C : ℝ) + 1) Kmin
  obtain ⟨C', _, hblock, hC'eq⟩ :=
    exists_completedLFunction_local_zero_power_sum_block_of_near_one_zero hq hχ hp hinv hη hηsmall
      hcre hcim hρre hzero hc K
  have hCC : C' = C := hC'eq.trans hCeq.symm
  rw [hCC] at hblock
  obtain ⟨hmasspos, m, hmK, hmKC, hlocal⟩ :=
    exists_completedLFunction_local_zero_block_on_finite_support χ hχ K C hblock
  let M :=
    ∑ v ∈ (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset,
      (MeromorphicOn.divisor χ.completedLFunction (Metric.ball c |80 * η|) v).toNat
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hmasspos
  have hMle : (M : ℝ) ≤ C := hmass
  have hcoeff : 1 / (4 * ((C : ℝ) + 1)) ≤ 1 / (4 * (M : ℝ)) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num only) hMpos)
      (mul_le_mul_of_nonneg_left (hMle.trans (le_add_of_nonneg_right zero_le_one))
        (by norm_num only))
  let A := 1 / (4 * ((C : ℝ) + 1)) * (1 / (3 * η)) ^ m
  have hmain : A ≤ ‖completedLFunctionLocalReciprocalMoment χ hχ c η m‖ :=
    (mul_le_mul_of_nonneg_right hcoeff
          (pow_nonneg (one_div_nonneg.mpr (mul_nonneg (by norm_num only) hη.le)) m)).trans
      hlocal
  have htail :=
    completedLFunction_remote_moment_le_log_cutoff hq hχ hp hinv hη (by linarith only [hηsmall])
      ρ.im hcre hcim (add_pos_of_nonneg_of_pos (Nat.cast_nonneg C) zero_lt_one) Kmin m hmK
  have htailhalf : ‖completedLFunctionRemoteReciprocalMoment χ c η m‖ ≤ (1 / 2 : ℝ) * A := by
    convert htail using 1
    dsimp only [A]
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  have hcombined := norm_add_ge_half_of_main_and_tail _ _ A hmain htailhalf
  refine
    ⟨C, K, m, hCeq, rfl, le_max_right _ _,
      completedGenusRemoteTailLogCutoff_ge_two q η ρ.im ((C : ℝ) + 1) Kmin, hmK, hmKC, ?_⟩
  convert hcombined using 1
  dsimp only [A]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- For positive derivative order at a center right of one, the derivative norm
is its factorial times the norm of the local-plus-remote reciprocal moment.
Factor the finite and complementary genus sums and use the unit norm of the sign.
This transfers an actual moment detector to a logarithmic-derivative detector. -/
theorem norm_completedLFunction_logDeriv_eq_local_remote_moment {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {η : ℝ}
    (hη : 0 < η) {c : ℂ} (hc : 1 < c.re) (n : ℕ) (hn : 0 < n) :
    ‖iteratedDerivWithin n (fun z : ℂ ↦ logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} c‖ =
      (n.factorial : ℝ) *
        ‖completedLFunctionLocalReciprocalMoment χ hχ c η (n + 1) +
            completedLFunctionRemoteReciprocalMoment χ c η (n + 1)‖ := by
  let S := (completedLFunction_local_zero_support_finite χ hχ c (80 * η)).toFinset
  let A : ℂ := (-1 : ℂ) ^ n * (n.factorial : ℂ)
  have hsplit :=
    iteratedDerivWithin_logDeriv_eq_local_divisor_sum_add_complement hq hχ hp hinv hc (80 * η) n hn
  have hlocal := completedLFunction_local_divisor_power_sum_factorization χ hχ (c := c) (80 * η) n
  have hcomplement :
    (∑' (v : { v : ℂ // v ∉ S }),
        (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) *
          ((-1 : ℂ) ^ n * (n.factorial : ℂ) * (c - v) ^ (-1 - (n : ℕ) : ℤ))) =
      A *
        ∑' (v : { v : ℂ // v ∉ S }),
          (MeromorphicOn.divisor χ.completedLFunction Set.univ v : ℂ) * (c - v)⁻¹ ^ (n + 1) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro v
    have hexp : (-1 : ℤ) - (n : ℤ) = Int.negSucc n := by
      rw [Int.negSucc_eq]
      ring
    rw [hexp, zpow_negSucc, inv_pow]
    dsimp only [A]
    ring
  have hremote := completedLFunction_local_support_complement_eq_remote_power_sum χ hχ c hη (n + 1)
  rw [hsplit, hlocal, hcomplement, hremote, ← mul_add, norm_mul]
  have hAnorm : ‖A‖ = (n.factorial : ℝ) := by
    simp only [A, norm_mul, norm_pow, norm_neg, norm_one, Complex.norm_natCast, one_pow, one_mul]
  change ‖A‖ * _ = _
  rw [hAnorm]
  rfl

/-- For a nonzero scale and any real signal coefficient, factorial normalization
turns the reciprocal scale into `3^(-m)`. Cancel the positive natural factorial and
the nonzero scale. This computes the completed detector signal exactly. -/
theorem factorial_normalized_reciprocal_signal (η a : ℝ) (n m : ℕ) (hη : η ≠ 0) :
    (η ^ m / (n.factorial : ℝ)) * (a * (1 / (3 * η)) ^ m * (n.factorial : ℝ)) =
      a * (1 / 3 : ℝ) ^ m := by
  have hF : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hscale : η * (1 / (3 * η)) = (1 / 3 : ℝ) := by
    calc
      _ = (η * η⁻¹) * (1 / 3 : ℝ) := by
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ = _ := by rw [mul_inv_cancel₀ hη, one_mul]
  calc
    _ = a * (η * (1 / (3 * η))) ^ m * ((n.factorial : ℝ) / n.factorial) := by
      rw [mul_pow]
      ring
    _ = _ := by rw [hscale, div_self hF, mul_one]

/-- For a nonprincipal completed L-function nonzero at a center right of one,
within and ordinary iterated derivatives of its logarithmic derivative agree.
Use analyticity at the center and the open half-plane. This exposes ordinary
iterates to the downstream Euler-series detector interface. -/
theorem completedLFunction_logDeriv_iteratedDerivWithin_eq {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {c : ℂ} (hcre : 1 < c.re)
    (hc : χ.completedLFunction c ≠ 0) (n : ℕ) :
    iteratedDerivWithin n (fun z : ℂ ↦ logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} c =
      iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.completedLFunction z) c := by
  have hU : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hF := (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt c
  have hlog : AnalyticAt ℂ (fun z : ℂ ↦ logDeriv χ.completedLFunction z) c := hF.deriv.div hF hc
  exact iteratedDerivWithin_eq_iteratedDeriv hU.uniqueDiffOn hlog.contDiffAt hcre

/-- For an actual near-one zero, retain its scale-dependent local multiplicity cap
and select the explicit logarithmic remote cutoff. A positive ordinary iterate of
the completed logarithmic derivative has normalized signal at least
`3^(-m)/(8(C+1))`, with `K ≤ m ≤ KC`. Combine the same-order moment detector and
factorial identity. No bounded scaled conductor-height hypothesis is required;
the remaining fixed-multiple block cost is recorded in the order range. -/
theorem exists_completedLFunction_normalized_detector_log_cutoff {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin) {c ρ : ℂ}
    (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : χ.completedLFunction ρ = 0) (hc : χ.completedLFunction c ≠ 0) :
    ∃ C K m n : ℕ,
      C =
          Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
        K = completedGenusRemoteTailLogCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
        Kmin ≤ K ∧
        2 ≤ K ∧
        0 < n ∧
        n + 1 = m ∧
        K ≤ m ∧
        m ≤ K * C ∧
        (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.completedLFunction z) c‖ := by
  obtain ⟨C, K, m, hC, hK, hKmin', hKtwo, hmK, hmKC, hmoment⟩ :=
    exists_completedLFunction_local_remote_moment_log_cutoff hq hχ hp hinv hη hηsmall Kmin hKmin
      hcre hcim hρre hzero hc
  have hmTwo : 2 ≤ m := hKtwo.trans hmK
  let n := m - 1
  have hn : 0 < n := Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 2) hmTwo)
  have hnm : n + 1 = m := Nat.sub_add_cancel ((by decide : 1 ≤ 2).trans hmTwo)
  have hcRight : 1 < c.re := by
    rw [hcre]; linarith only [hη]
  have hnorm :=
    norm_completedLFunction_logDeriv_eq_local_remote_moment hq hχ hp hinv hη hcRight n hn
  rw [completedLFunction_logDeriv_iteratedDerivWithin_eq hχ hcRight hc n, hnm] at hnorm
  have hbound := mul_le_mul_of_nonneg_left hmoment (Nat.cast_nonneg n.factorial)
  rw [← hnorm] at hbound
  have hscaled :=
    mul_le_mul_of_nonneg_left hbound (div_nonneg (pow_nonneg hη.le m) (Nat.cast_nonneg n.factorial))
  refine ⟨C, K, m, n, hC, hK, hKmin', hKtwo, hn, hnm, hmK, hmKC, ?_⟩
  rw [hnm]
  calc
    _ =
        (η ^ m / (n.factorial : ℝ)) *
          ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ)) :=
      (factorial_normalized_reciprocal_signal η _ n m (ne_of_gt hη)).symm
    _ ≤ _ := by simpa only [mul_comm (n.factorial : ℝ)] using hscaled

/-- For a nonnegative gamma bound, positive multiplicity scale, and sufficiently
small shift, a logarithmic order threshold makes the normalized gamma correction
at most half the variable-cap detector signal. Compare `12η` with `3/8` and apply
geometric absorption. This removes the fixed-cap restriction from gamma subtraction. -/
theorem normalized_gamma_le_half_variable_cap_signal (η N G H : ℝ) (n : ℕ) (hη : 0 ≤ η)
    (hηsmall : 12 * η ≤ 3 / 8) (hN : 0 < N) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hn : Nat.ceil (Real.log (max (48 * N * η * G * H) 1) / Real.log (8 / 3 : ℝ)) ≤ n) :
    η * G * H * (4 * η) ^ n ≤ 1 / (16 * N * (3 : ℝ) ^ (n + 1)) := by
  have hA : 0 ≤ 48 * N * η * G * H :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hN.le) hη) hG) hH
  have hsmall :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg (by norm_num only) hη) hηsmall n)
          hA).trans
      (geometric_remote_ratio_le_one_of_log_cutoff (48 * N * η * G * H) n hn)
  apply (le_div_iff₀ (mul_pos (mul_pos (by norm_num only) hN) (pow_pos (by norm_num only) _))).mpr
  convert hsmall using 1
  rw [pow_succ, mul_pow, mul_pow]
  rw [show (12 : ℝ) = 3 * 4 by norm_num only, mul_pow]
  ring

/-- For a gamma majorant and any derivative order, factorial normalization leaves
`η G H (4η)^n`. Factor the natural factorial and cancel it. This expresses the
ordinary-function transfer error at the same normalization as the zero detector. -/
theorem factorial_normalized_gamma_correction (η G H : ℝ) (n : ℕ) :
    (η ^ (n + 1) / (n.factorial : ℝ)) * ((n.factorial : ℝ) * G * H / (1 / 4 : ℝ) ^ n) =
      η * G * H * (4 * η) ^ n := by
  have hF : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  calc
    _ = η * G * H * (4 * η) ^ n * ((n.factorial : ℝ) / n.factorial) := by
      simp only [pow_succ, div_eq_mul_inv, one_mul, inv_pow, inv_inv, mul_pow]
      ring
    _ = _ := by rw [div_self hF, mul_one]

/-- There is one absolute gamma constant such that every primitive near-one zero
at an admissibly small positive shift yields a positive normalized ordinary
L-function logarithmic-derivative signal. The explicit multiplicity cap is retained;
both the remote and gamma order thresholds are logarithmic in their mass factors.
Choose the gamma threshold before applying the completed detector and absorb half
its signal. No bounded scaled conductor-height assumption is used. The remaining
order cost is the product `KC`, which must be improved for the full density target. -/
theorem exists_ordinary_LFunction_normalized_detector_log_cutoff :
    ∃ G : ℝ,
      0 ≤ G ∧
        ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q},
          2 ≤ q →
            χ ≠ 1 →
            χ.IsPrimitive →
            χ⁻¹ ≠ 1 →
            ∀ {η : ℝ},
              0 < η →
                η ≤ 1 / 1288 →
                ∀ (Krequested : ℕ),
                  2 ≤ Krequested →
                    ∀ {c ρ : ℂ},
                      c.re = 1 + η →
                        c.im = ρ.im →
                        |ρ.re - 1| ≤ η →
                        χ.completedLFunction ρ = 0 →
                        χ.completedLFunction c ≠ 0 →
                        ∃ C Kmin K m n : ℕ,
                          C =
                              Nat.ceil
                                (completedZeroLocalLogBoundConstant *
                                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
                            Kmin =
                              max
                                (Nat.ceil
                                    (Real.log
                                        (max
                                          (48 * ((C : ℝ) + 1) * η * G *
                                            (Real.log (4 * |ρ.im| + 4) + 1))
                                          1) /
                                      Real.log (8 / 3 : ℝ)) +
                                  2)
                                Krequested ∧
                            K = completedGenusRemoteTailLogCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
                            Krequested ≤ K ∧
                            0 < n ∧
                            n + 1 = m ∧
                            K ≤ m ∧
                            m ≤ K * C ∧
                            1 / (16 * ((C : ℝ) + 1) * (3 : ℝ) ^ m) ≤
                              (η ^ (n + 1) / (n.factorial : ℝ)) *
                                ‖iteratedDeriv n (fun z : ℂ ↦ logDeriv χ.LFunction z) c‖ := by
  obtain ⟨G, hG, hgamma⟩ := exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative_all
  refine ⟨G, hG, ?_⟩
  intro q _ χ hq hχ hp hinv η hη hηsmall Krequested hKrequested c ρ hcre hcim hρre hzero hc
  let C₀ :=
    Nat.ceil
      (completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3))))
  let H := Real.log (4 * |ρ.im| + 4) + 1
  let J := Nat.ceil (Real.log (max (48 * ((C₀ : ℝ) + 1) * η * G * H) 1) / Real.log (8 / 3 : ℝ))
  let Kmin := max (J + 2) Krequested
  have hKmin : 2 ≤ Kmin := (Nat.le_add_left 2 J).trans (le_max_left _ _)
  obtain ⟨C, K, m, n, hC, hK, hKmin', _, hn, hnm, hmK, hmKC, hcompleted⟩ :=
    exists_completedLFunction_normalized_detector_log_cutoff hq hχ hp hinv hη hηsmall Kmin hKmin
      hcre hcim hρre hzero hc
  have hCC : C = C₀ := hC
  rw [hCC] at hK hmKC hcompleted
  have hJn : J ≤ n := by
    have h := (le_max_left (J + 2) Krequested).trans (hKmin'.trans hmK)
    rw [← hnm] at h
    exact (Nat.le_add_right J 1).trans (Nat.le_of_succ_le_succ h)
  have hN : 0 < (C₀ : ℝ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg C₀) zero_lt_one
  have hH : 0 ≤ H :=
    add_nonneg
      (Real.log_nonneg
        (by
          have h := abs_nonneg ρ.im
          linarith only [h]))
      zero_le_one
  have hbudget :=
    normalized_gamma_le_half_variable_cap_signal η ((C₀ : ℝ) + 1) G H n hη.le
      (by linarith only [hηsmall]) hN hG hH hJn
  have hcRight : 1 < c.re := by
    rw [hcre]; linarith only [hη]
  have hcHi : c.re ≤ 5 / 4 := by
    rw [hcre]; linarith only [hηsmall]
  have hordinary :=
    hgamma n hχ hcRight hcRight.le hcHi (abs_nonneg ρ.im) (by rw [hcim]) (A :=
      ‖iteratedDeriv n (logDeriv χ.completedLFunction) c‖) (le_refl _)
  have hscaled :=
    mul_le_mul_of_nonneg_left hordinary
      (div_nonneg (pow_nonneg hη.le (n + 1)) (Nat.cast_nonneg n.factorial))
  rw [mul_sub, factorial_normalized_gamma_correction] at hscaled
  have hsignal :
    (1 / (8 * ((C₀ : ℝ) + 1))) * (1 / 3 : ℝ) ^ m =
      2 * (1 / (16 * ((C₀ : ℝ) + 1) * (3 : ℝ) ^ m)) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, one_mul]
    norm_num only
    ring
  rw [hsignal] at hcompleted
  rw [hnm] at hbudget
  refine ⟨C₀, Kmin, K, m, n, rfl, rfl, hK, (le_max_right _ _).trans hKmin', hn, hnm, hmK, hmKC, ?_⟩
  change _ ≤ (η ^ (n + 1) / (n.factorial : ℝ)) * ‖iteratedDeriv n (logDeriv χ.LFunction) c‖
  change _ - η * G * H * (4 * η) ^ n ≤ _ at hscaled
  linarith only [hcompleted, hbudget, hscaled]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
