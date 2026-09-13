/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.DigammaBallBound

/-!
# the left-vertical bound: quarter-lattice separation and the small-`|t|` finite digamma bound

The left-vertical line `s_A(t) = -A - 1/2 + i t` (`A : ℕ`) feeds four digamma arguments into the
gamma factor's log-derivative (even/odd parity × direct/reflected point): `-A/2 - 1/4`,
`-A/2 + 1/4`, `A/2 + 3/4`, `A/2 + 5/4` (all as the *real part*, the imaginary part is `± t/2`).
The first two are always of the form `(odd integer)/4`, hence never an integer themselves — this
holds for *every* `A` and is entirely independent of `t`, so it covers `t = 0` uniformly without
needing any `|Im z|`-based separation. The reflected two are positive once `A ≥ 2`, hence trivially
avoid every nonpositive-integer pole.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### The two left-side quarter-lattice separation facts -/

/-- `j ↦ j + 4k` preserves oddness (`4k` is always even). -/
theorem odd_add_four_mul_nat (j : ℤ) (hj : Odd j) (k : ℕ) : Odd (j + 4 * (k : ℤ)) := by
  obtain ⟨m, hm⟩ := hj
  exact ⟨m + 2 * (k : ℤ), by omega⟩

/-- An odd integer's absolute value is at least `1`, so `(odd)/4` is at least `1/4` in absolute
value. -/
theorem abs_odd_div_four_ge_quarter {j : ℤ} (hj : Odd j) : (1 : ℝ) / 4 ≤ |(j : ℝ) / 4| := by
  have hjne : j ≠ 0 := by
    obtain ⟨m, hm⟩ := hj; omega
  have h1 : (1 : ℤ) ≤ |j| := Int.one_le_abs hjne
  have h1' : (1 : ℝ) ≤ |(j : ℝ)| := by exact_mod_cast h1
  rw [abs_div]
  have h4 : |(4 : ℝ)| = 4 := by norm_num only
  rw [h4, le_div_iff₀ (by norm_num only : (0 : ℝ) < 4)]
  linarith

/-! ### The small-`|t|` finite bound at a quarter-lattice point, `O((A+5)²)` -/

/-- Quadratic absorption for the small-imaginary-part bound, with a small real context. -/
private theorem smallIm_absorb {B M : ℝ} (hB : 5 ≤ B) (hM : 0 ≤ M) :
    (32 * B ^ 2 + 8 * M + 80 * Real.pi * B + 8) + 4 * B ≤
      (8 * M + 32 + 80 * Real.pi + 24) * B ^ 2 := by
  have hBnonneg : 0 ≤ B := by linarith only [hB]
  have hBone : 1 ≤ B := by linarith only [hB]
  have hB1 : 1 ≤ B ^ 2 := (one_le_sq_iff₀ hBnonneg).2 hBone
  have hB2 : B ≤ B ^ 2 := by
    calc
      B = B * 1 := by rw [mul_one]
      _ ≤ B * B := mul_le_mul_of_nonneg_left hBone hBnonneg
      _ = B ^ 2 := by ring
  have hMB : M ≤ M * B ^ 2 := by
    calc
      M = M * 1 := by rw [mul_one]
      _ ≤ M * B ^ 2 := mul_le_mul_of_nonneg_left hB1 hM
  have h80pi : (0 : ℝ) ≤ 80 * Real.pi := by positivity
  have hpiB : 80 * Real.pi * B ≤ 80 * Real.pi * B ^ 2 := by
    exact mul_le_mul_of_nonneg_left hB2 h80pi
  have hsmall : 8 + 4 * B ≤ 24 * B ^ 2 := by
    have h8 : (8 : ℝ) ≤ 8 * B ^ 2 := by
      simpa only [mul_one] using (mul_le_mul_of_nonneg_left hB1 (by norm_num only : (0 : ℝ) ≤ 8))
    have h4B : 4 * B ≤ 4 * B ^ 2 := mul_le_mul_of_nonneg_left hB2 (by norm_num only : (0 : ℝ) ≤ 4)
    linarith only [h8, h4B]
  linarith only [hMB, hpiB, hsmall]

/-! ### The generic small-`|t|` finite bound, `O((A+5)²)`, from a `1/4`-separation hypothesis -/

/--
Input/assumptions: none (existence statement, `A`-uniform: the witness `C` is chosen before `A`).
Conclusion: there is `C ≥ 0` such that for every `A : ℕ` with `2 ≤ A`, every `a u : ℝ` with
`|a| ≤ A + 2` and `∀ q : ℕ, 1/4 ≤ |a + q|`, and every `u` with `|u| ≤ 4(A + 5)`,
`‖digamma (a + u i)‖ ≤ C (A + 5)²`.
Content: shifts `z := a + u i` by `n := A + 5` to `z + n` (real part `≥ 3`, so `r := (z + n).re - 1
≥ 2`); bounds `‖digamma (z + n)‖` via `RiemannZeta.norm_digamma_shift_add_mul_I_le` (valid at any
`u`), using
`Real.Gamma_strictMonoOn_Ici` directly (no `Icc`-convexity needed since `r + 1/2, r + 3/2 ≥ 2`
already) to get `Γ (r + 1/2), Γ (r + 3/2) ≤ Γ (X)` for `X := 2(A + 5) ≥ r + 3/2`, then the crude
`log Γ (X) ≤ X log X ≤ X² = 4(A + 5)²`; undoes the shift via
`norm_digamma_sub_shift_nat_le_of_re_sep` with `δ := 1/4`, where pole-avoidance is derived
*directly from the separation hypothesis itself*
(if `z + k = -m` then `a + (k + m) = 0`, contradicting `1/4 ≤ |a + (k + m)|` — no need for a
separate quarter-lattice argument at this level of generality).
Role: the left-vertical step small-`|t|` half of the left-vertical digamma bound, generic in `a` so
it applies
uniformly to all four gamma-factor arguments (`exists_C_forall_norm_digamma_explicit_le`).
-/
theorem exists_C_forall_norm_digamma_small_im_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ A : ℕ,
          2 ≤ A →
            ∀ a u : ℝ,
              |a| ≤ (A : ℝ) + 2 →
                (∀ q : ℕ, (1 : ℝ) / 4 ≤ |a + (q : ℝ)|) →
                |u| ≤ 4 * ((A : ℝ) + 5) →
                ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ C * ((A : ℝ) + 5) ^ 2 := by
  obtain ⟨C₁, hC₁⟩ :=
    RiemannZeta.exists_neg_log_norm_Gamma_one_add_add_mul_I_le_uniform
  set C : ℝ := 8 * max C₁ 0 + 32 + 80 * Real.pi + 24 with hC_def
  have hCnonneg : 0 ≤ C := by
    have h1 : (0 : ℝ) ≤ max C₁ 0 := le_max_right _ _
    linarith only [Real.pi_pos, h1]
  refine ⟨C, hCnonneg, fun A _hA2 a u ha hsepQ hu => ?_⟩
  set z : ℂ := (a : ℂ) + (u : ℂ) * Complex.I with hz_def
  set n : ℕ := A + 5 with hn_def
  have hA5pos : (5 : ℝ) ≤ (A : ℝ) + 5 := by
    have := Nat.cast_nonneg (α := ℝ) A; linarith
  have ha_ge : -(A : ℝ) - 2 ≤ a := by linarith [abs_le.mp ha]
  have ha_le : a ≤ (A : ℝ) + 2 := by linarith [abs_le.mp ha]
  have han : (3 : ℝ) ≤ a + n := by
    rw [hn_def]; push_cast; linarith [ha_ge]
  set r : ℝ := a + n - 1 with hr_def
  have hr2 : (2 : ℝ) ≤ r := by linarith [han]
  have hrle : r ≤ 2 * (A : ℝ) + 6 := by
    rw [hr_def, hn_def]; push_cast; linarith [ha_le]
  have hzn_eq : z + (n : ℂ) = (1 + r : ℝ) + (u : ℂ) * Complex.I := by
    rw [hz_def]; apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.natCast_re, hr_def,
        add_sub_cancel, Complex.ofReal_add, Complex.ofReal_natCast]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.natCast_im, Complex.ofReal_add,
        Complex.ofReal_one, Complex.one_im]
  have hshift_bound :=
    RiemannZeta.norm_digamma_shift_add_mul_I_le r
      (by linarith [hr2]) u
  set X : ℝ := 2 * (A : ℝ) + 10 with hX_def
  have hX2 : (2 : ℝ) ≤ X := by
    rw [hX_def]; have := Nat.cast_nonneg (α := ℝ) A; linarith
  have hr12ge2 : (2 : ℝ) ≤ r + 1 / 2 := by linarith [hr2]
  have hr32ge2 : (2 : ℝ) ≤ r + 3 / 2 := by linarith [hr2]
  have hr12leX : r + 1 / 2 ≤ X := by
    rw [hX_def]; linarith [hrle]
  have hr32leX : r + 3 / 2 ≤ X := by
    rw [hX_def]; linarith [hrle]
  have hΓr12 : Real.Gamma (r + 1 / 2) ≤ Real.Gamma X :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hr12ge2) (Set.mem_Ici.mpr hX2) hr12leX
  have hΓr32 : Real.Gamma (r + 3 / 2) ≤ Real.Gamma X :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hr32ge2) (Set.mem_Ici.mpr hX2) hr32leX
  have hΓX_ge1 : (1 : ℝ) ≤ Real.Gamma X := by
    rw [← Real.Gamma_two]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hX2) hX2
  have hmax_le : max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1 ≤ 2 * Real.Gamma X := by
    have := max_le hΓr12 hΓr32; linarith [hΓX_ge1]
  have hrrpos : (0 : ℝ) < max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1 := by
    have hΓr12pos : (0 : ℝ) < Real.Gamma (r + 1 / 2) := Real.Gamma_pos_of_pos (by linarith)
    have := le_max_left (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2))
    linarith [hΓr12pos]
  have hlogX : Real.log X ≤ X := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < X by linarith); linarith
  have hXlogX_le : X * Real.log X ≤ X ^ 2 := by nlinarith only [hlogX, hX2]
  have hlogΓX_le : Real.log (Real.Gamma X) ≤ X ^ 2 :=
    le_trans (Gamma.log_Gamma_le_of_one_le (by linarith)) hXlogX_le
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num only); linarith
  have hlog_rr_le :
    Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) ≤ 1 + X ^ 2 := by
    calc
      Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) ≤
          Real.log (2 * Real.Gamma X) :=
        Real.log_le_log hrrpos hmax_le
      _ = Real.log 2 + Real.log (Real.Gamma X) := by
        rw [Real.log_mul (by norm_num only) (by linarith [hΓX_ge1])]
      _ ≤ 1 + X ^ 2 := by linarith [hlog2, hlogΓX_le]
  have hneg_log_le := hC₁ r u (by linarith [hr2])
  have hcast_eq : (1 : ℂ) + (r : ℂ) + (u : ℂ) * Complex.I = (1 + r : ℝ) + (u : ℂ) * Complex.I := by
    push_cast; ring
  rw [hcast_eq] at hneg_log_le
  have hC1_le : C₁ ≤ max C₁ 0 := le_max_left _ _
  have hXsq_le : X ^ 2 = 4 * ((A : ℝ) + 5) ^ 2 := by
    rw [hX_def]; ring
  have hdigamma_zn_le :
    ‖Complex.digamma (z + (n : ℂ))‖ ≤
      32 * ((A : ℝ) + 5) ^ 2 + 8 * max C₁ 0 + 80 * Real.pi * ((A : ℝ) + 5) + 8 := by
    have hπu : 20 * Real.pi * |u| ≤ 20 * Real.pi * (4 * ((A : ℝ) + 5)) := by
      apply mul_le_mul_of_nonneg_left hu; linarith [Real.pi_pos]
    calc
      ‖Complex.digamma (z + (n : ℂ))‖ = ‖Complex.digamma ((1 + r : ℝ) + (u : ℂ) * Complex.I)‖ := by
        rw [hzn_eq]
      _ ≤
          8 *
            (Real.log (max (Real.Gamma (r + 1 / 2)) (Real.Gamma (r + 3 / 2)) + 1) -
              Real.log ‖Complex.Gamma ((1 + r : ℝ) + (u : ℂ) * Complex.I)‖) :=
        hshift_bound
      _ ≤ 32 * ((A : ℝ) + 5) ^ 2 + 8 * max C₁ 0 + 80 * Real.pi * ((A : ℝ) + 5) + 8 := by
        nlinarith only [hlog_rr_le, hneg_log_le, hC1_le, hXsq_le, hπu]
  have hpole : ∀ k < n, ∀ m : ℕ, z + (k : ℂ) ≠ -(m : ℂ) := by
    intro k _ m h
    have him : (z + (k : ℂ)).re = (-(m : ℂ)).re := congrArg Complex.re h
    have hre_eq : (z + (k : ℂ)).re = a + (k : ℝ) := by
      simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.natCast_re]
    rw [hre_eq] at him
    simp only [Complex.neg_re, Complex.natCast_re] at him
    have hkm := hsepQ (k + m)
    push_cast at hkm
    have hzero : a + ((k : ℝ) + (m : ℝ)) = 0 := by linarith [him]
    rw [hzero] at hkm
    norm_num only at hkm
  have hsep : ∀ k < n, (1 : ℝ) / 4 ≤ |(z + (k : ℂ)).re| := by
    intro k _
    have hre_eq : (z + (k : ℂ)).re = a + (k : ℝ) := by
      simp only [hz_def, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.natCast_re]
    rw [hre_eq]; exact hsepQ k
  have hshiftback :=
    norm_digamma_sub_shift_nat_le_of_re_sep n (by norm_num only : (0 : ℝ) < 1 / 4) hpole hsep
  have hshiftback_le : (n : ℝ) / (1 / 4) ≤ 4 * ((A : ℝ) + 5) := by
    rw [hn_def]; push_cast; linarith
  have htri :
    ‖Complex.digamma z‖ ≤
      ‖Complex.digamma (z + (n : ℂ))‖ + ‖Complex.digamma (z + (n : ℂ)) - Complex.digamma z‖ := by
    have heq :
      Complex.digamma z =
        Complex.digamma (z + (n : ℂ)) - (Complex.digamma (z + (n : ℂ)) - Complex.digamma z) := by
      ring
    calc
      ‖Complex.digamma z‖ =
          ‖Complex.digamma (z + (n : ℂ)) - (Complex.digamma (z + (n : ℂ)) - Complex.digamma z)‖ :=
        by rw [← heq]
      _ ≤ ‖Complex.digamma (z + (n : ℂ))‖ + ‖Complex.digamma (z + (n : ℂ)) - Complex.digamma z‖ :=
        norm_sub_le _ _
  calc
    ‖Complex.digamma z‖ ≤
        ‖Complex.digamma (z + (n : ℂ))‖ + ‖Complex.digamma (z + (n : ℂ)) - Complex.digamma z‖ :=
      htri
    _ ≤
        (32 * ((A : ℝ) + 5) ^ 2 + 8 * max C₁ 0 + 80 * Real.pi * ((A : ℝ) + 5) + 8) +
          4 * ((A : ℝ) + 5) :=
      by linarith [hdigamma_zn_le, hshiftback, hshiftback_le]
    _ ≤ C * ((A : ℝ) + 5) ^ 2 := by
      rw [hC_def]
      exact smallIm_absorb hA5pos (le_max_right C₁ 0)

/-! ### Quarter-lattice separation facts, and the large/small unification -/

/-- The even-parity left digamma real part `-A/2 - 1/4`, shifted by any `q : ℕ`, is `≥ 1/4` in
absolute value (reusing `odd_add_four_mul_nat`/`abs_odd_div_four_ge_quarter`). -/
theorem leftEven_quarterSep (A q : ℕ) : (1 : ℝ) / 4 ≤ |(-(A : ℝ) / 2 - 1 / 4) + (q : ℝ)| := by
  have hodd : Odd (-(2 * (A : ℤ) + 1)) := ⟨-(A : ℤ) - 1, by ring⟩
  have hoddq : Odd (-(2 * (A : ℤ) + 1) + 4 * (q : ℤ)) := odd_add_four_mul_nat _ hodd q
  have heq :
    (-(A : ℝ) / 2 - 1 / 4) + (q : ℝ) = ((-(2 * (A : ℤ) + 1) + 4 * (q : ℤ) : ℤ) : ℝ) / 4 := by
    push_cast; ring
  rw [heq]; exact abs_odd_div_four_ge_quarter hoddq

/-- The odd-parity left digamma real part `-A/2 + 1/4`, shifted by any `q : ℕ`, is `≥ 1/4` in
absolute value. -/
theorem leftOdd_quarterSep (A q : ℕ) : (1 : ℝ) / 4 ≤ |(-(A : ℝ) / 2 + 1 / 4) + (q : ℝ)| := by
  have hodd : Odd (1 - 2 * (A : ℤ)) := ⟨-(A : ℤ), by ring⟩
  have hoddq : Odd (1 - 2 * (A : ℤ) + 4 * (q : ℤ)) := odd_add_four_mul_nat _ hodd q
  have heq : (-(A : ℝ) / 2 + 1 / 4) + (q : ℝ) = ((1 - 2 * (A : ℤ) + 4 * (q : ℤ) : ℤ) : ℝ) / 4 := by
    push_cast; ring
  rw [heq]; exact abs_odd_div_four_ge_quarter hoddq

/-- A real number `≥ 1/4` stays `≥ 1/4` in absolute value after adding any `q : ℕ` — the trivial
separation fact for the (positive) reflected-point real parts. -/
theorem quarterSep_of_pos {a : ℝ} (ha : (1 : ℝ) / 4 ≤ a) (q : ℕ) : (1 : ℝ) / 4 ≤ |a + (q : ℝ)| := by
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  rw [abs_of_pos (by linarith)]; linarith

/--
Input/assumptions: none (existence statement, `A`-uniform).
Conclusion: there is `C ≥ 0` such that for every `A ≥ 2`, every `a u : ℝ` with `|a| ≤ A + 2` and
`∀ q : ℕ, 1/4 ≤ |a + q|`, `‖digamma (a + u i)‖ ≤ C ((A + 5)² + 1 + log (2|u| + 2))`.
Content: splits on `4(A + 5) ≤ |u|` (large, via `exists_C_forall_norm_digamma_large_im_le`, noting
`4(|a| + 3) ≤ 4(A + 5) ≤ |u|` and `log(|u| + 2) ≤ log(2|u| + 2)`) vs `|u| < 4(A + 5)` (small, via
`exists_C_forall_norm_digamma_small_im_le`).
Role: the left-vertical step checkpoint — a single explicit-`A` digamma bound covering all `u : ℝ`,
ready to
feed the gamma-factor log-derivative at both the left-vertical point and its reflection.
-/
theorem exists_C_forall_norm_digamma_explicit_le :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ A : ℕ,
          2 ≤ A →
            ∀ a u : ℝ,
              |a| ≤ (A : ℝ) + 2 →
                (∀ q : ℕ, (1 : ℝ) / 4 ≤ |a + (q : ℝ)|) →
                ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤
                  C * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (2 * |u| + 2)) := by
  obtain ⟨CL, hCLnn, hCL⟩ := exists_C_forall_norm_digamma_large_im_le
  obtain ⟨CS, hCSnn, hCS⟩ := exists_C_forall_norm_digamma_small_im_le
  set C : ℝ := CL + CS + 10 with hC_def
  have hCnn : (0 : ℝ) ≤ C := by linarith [hCLnn, hCSnn]
  refine ⟨C, hCnn, fun A hA2 a u ha hsepQ => ?_⟩
  have hA2' : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA2
  have hAsq1 : (1 : ℝ) ≤ ((A : ℝ) + 5) ^ 2 := by nlinarith [hA2']
  by_cases hbig : 4 * ((A : ℝ) + 5) ≤ |u|
  · have h4a3 : 4 * (|a| + 3) ≤ |u| := by linarith [ha]
    have hbound := hCL a u h4a3
    have h1 : Real.log (|u| + 2) ≤ Real.log (2 * |u| + 2) :=
      Real.log_le_log (by linarith [abs_nonneg u]) (by linarith [abs_nonneg u])
    have h2 : (0 : ℝ) ≤ Real.log (2 * |u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
    calc
      ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ CL * (1 + Real.log (|u| + 2)) := hbound
      _ ≤ C * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (2 * |u| + 2)) := by
        nlinarith [h1, h2, hCLnn, hCSnn, hAsq1]
  · push Not at hbig
    have hbound := hCS A hA2 a u ha hsepQ hbig.le
    have h2 : (0 : ℝ) ≤ Real.log (2 * |u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
    calc
      ‖Complex.digamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ ≤ CS * ((A : ℝ) + 5) ^ 2 := hbound
      _ ≤ C * (((A : ℝ) + 5) ^ 2 + 1 + Real.log (2 * |u| + 2)) := by
        nlinarith [h2, hCLnn, hCSnn, hAsq1]

/-! ### the left-vertical step: connecting quarter-lattice separation to Gamma's pole-avoidance
hypothesis -/

/--
Input/assumptions: `z : ℂ` with `∀ q : ℕ, 1/4 ≤ |z.re + q|`.
Conclusion: `z ≠ -m` for every `m : ℕ`.
Content: if `z = -m` then `z.re = -m`, so `z.re + m = 0`, contradicting `hsep m : 1/4 ≤ |z.re + m|
= 0`.
Role: the bridge from the left-vertical step's quarter-lattice/positivity separation facts
(`leftEven_quarterSep`,
`leftOdd_quarterSep`, `quarterSep_of_pos`) to the `hhalf`-shaped pole-avoidance hypothesis the
regular-point gamma-factor API in `GammaFactorLogDeriv` needs.
-/
theorem ne_neg_nat_of_re_quarterSep {z : ℂ} (hsep : ∀ q : ℕ, (1 : ℝ) / 4 ≤ |z.re + (q : ℝ)|)
    (m : ℕ) : z ≠ -(m : ℂ) := by
  intro hm
  have hre : z.re = (-(m : ℂ)).re := congrArg Complex.re hm
  simp only [Complex.neg_re, Complex.natCast_re] at hre
  have h := hsep m
  rw [show z.re + (m : ℝ) = 0 from by linarith [hre]] at h
  norm_num only at h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
