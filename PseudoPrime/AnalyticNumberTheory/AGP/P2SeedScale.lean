/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import PseudoPrime.AnalyticNumberTheory.AGP.ProgressionAuxiliaryData

/-! # P2SeedScale

Finite parameter estimates and scale selection for the second AGP progression stage.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a real coefficient `A`.

Claim: some natural number `u ≥ 10` satisfies `A * u ^ 2 ≤ 2 ^ u`.

Proof: the quotient `exp (u * log 2) / u ^ 2` tends to infinity; convert its eventual lower
bound back to natural powers.

Role: provides the explicit growth margin used to choose the primorial seed scale.
-/
theorem exists_nat_pow_two_dominates_square (A : ℝ) :
    ∃ u : ℕ, 10 ≤ u ∧ A * (u : ℝ) ^ 2 ≤ (2 : ℝ) ^ u := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hlim := (tendsto_exp_mul_div_rpow_atTop 2 (Real.log 2) hlog).comp tendsto_natCast_atTop_atTop
  have htarget : ∀ᶠ x : ℝ in Filter.atTop, A ≤ x := Filter.eventually_atTop.2 ⟨A, fun _ hx => hx⟩
  have hevent : ∀ᶠ u : ℕ in Filter.atTop, A ≤ Real.exp (Real.log 2 * (u : ℝ)) / (u : ℝ) ^ (2 : ℝ) :=
    hlim.eventually htarget
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let u := max N 10
  have huN : N ≤ u := le_max_left _ _
  have hu10 : 10 ≤ u := le_max_right _ _
  have hratio := hN u huN
  refine ⟨u, hu10, ?_⟩
  have hpow : Real.exp (Real.log 2 * (u : ℝ)) = (2 : ℝ) ^ u := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 2)]
  have hden : (u : ℝ) ^ (2 : ℝ) = (u : ℝ) ^ 2 := Real.rpow_natCast _ _
  rw [hpow, hden] at hratio
  apply (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast (by omega : 0 < u)))).1
  exact hratio

/--
Inputs: a real coefficient `A` and a natural lower cutoff `U`.

Claim: some `u ≥ U` satisfies `A * u ^ 2 ≤ 2 ^ u`.

Proof: use the eventual lower bound for `exp (u * log 2) / u ^ 2` and choose the maximum
of its threshold and `U`.

Role: lets the seed scale satisfy growth and arithmetic cutoff conditions simultaneously.
-/
theorem exists_nat_pow_two_dominates_square_from (A : ℝ) (U : ℕ) (hU : 10 ≤ U) :
    ∃ u : ℕ, U ≤ u ∧ A * (u : ℝ) ^ 2 ≤ (2 : ℝ) ^ u := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hlim := (tendsto_exp_mul_div_rpow_atTop 2 (Real.log 2) hlog).comp tendsto_natCast_atTop_atTop
  have htarget : ∀ᶠ x : ℝ in Filter.atTop, A ≤ x := Filter.eventually_atTop.2 ⟨A, fun _ hx => hx⟩
  have hevent : ∀ᶠ u : ℕ in Filter.atTop, A ≤ Real.exp (Real.log 2 * (u : ℝ)) / (u : ℝ) ^ (2 : ℝ) :=
    hlim.eventually htarget
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let u := max N U
  have huN : N ≤ u := le_max_left _ _
  have huU : U ≤ u := le_max_right _ _
  have hratio := hN u huN
  refine ⟨u, huU, ?_⟩
  have hpow : Real.exp (Real.log 2 * (u : ℝ)) = (2 : ℝ) ^ u := by
    rw [← Real.rpow_natCast]
    rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 2)]
  have hden : (u : ℝ) ^ (2 : ℝ) = (u : ℝ) ^ 2 := Real.rpow_natCast _ _
  rw [hpow, hden] at hratio
  have huPos : 0 < u := lt_of_lt_of_le (by omega) (le_trans hU huU)
  apply (le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast huPos))).1
  exact hratio

/--
Inputs: positive parameters `c₀`, `J`, `u`, and `z`, together with the floor-defined
seed count `T`.

Claim: `T + 1` lies strictly above the real quantity whose floor defines `T`, and at most
one above it.

Proof: use the defining inequalities for the natural floor after proving its argument
nonnegative.

Role: supplies the two-sided parameter estimate needed in the full-divisor P2 comparison.
-/
theorem p2_floor_parameter_bounds {c₀ : ℝ} {J u z T : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J) (hu : 0 < u)
    (hz : 0 < z) (hT : T = Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2))) :
    c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) < ((T + 1 : ℕ) : ℝ) ∧
      ((T + 1 : ℕ) : ℝ) ≤ c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) + 1 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hzR : (0 : ℝ) < (z : ℝ) := by exact_mod_cast hz
  have hJR : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have h20J : (0 : ℝ) < 20 * (J : ℝ) := mul_pos (by norm_num only : (0 : ℝ) < 20) hJR
  have hden : (0 : ℝ) < 20 * (J : ℝ) * (u : ℝ) * Real.log 2 := mul_pos (mul_pos h20J huR) hlog2
  have harg : 0 ≤ c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
    le_of_lt (div_pos (mul_pos hc₀ (sq_pos_of_pos hzR)) hden)
  rw [hT]
  simp only [Nat.cast_add, Nat.cast_one]
  constructor
  · exact Nat.lt_floor_add_one _
  · exact add_le_add_left (Nat.floor_le harg) 1

/--
Inputs: a primorial cutoff `z ≥ 2` and a natural exponent `J`.

Claim: the logarithm of the `J`th power of the fifth power of the primorial up to `z` is
at most `5 J (z + 1) log z`.

Proof: multiply the existing fifth-power primorial logarithm bound by the nonnegative
coefficient `J`, then rewrite the logarithm of a natural power.

Role: provides the logarithmic estimate for the full-divisor seed modulus `q = N^(5J)`.
-/
theorem log_primorial_fifth_power_pow_le {z J : ℕ} (hz : 2 ≤ z) :
    Real.log
        (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id : ℕ) ^ 5) ^ J : ℕ) : ℝ) ≤
      5 * (J : ℝ) * ((z + 1 : ℕ) : ℝ) * Real.log (z : ℝ) := by
  let N : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE z).prod id
  have hbase := log_primeProductLE_fifth_power_le hz
  have hJ : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg J
  have hmul := mul_le_mul_of_nonneg_left hbase hJ
  change Real.log (((N ^ 5) ^ J : ℕ) : ℝ) ≤ _
  rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow]
  calc
    (J : ℝ) * (5 * Real.log (N : ℝ)) ≤ (J : ℝ) * (5 * ((z + 1 : ℕ) : ℝ) * Real.log (z : ℝ)) := by
      simpa only [N, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat] using hmul
    _ = 5 * (J : ℝ) * ((z + 1 : ℕ) : ℝ) * Real.log (z : ℝ) := by ring

/--
Inputs: a seed exponent `u ≥ 1` and a natural power `J`.

Claim: for the primorial cutoff `z = 2 ^ u`, the logarithm of its fifth-power `J`th power
is at most `10 J 2 ^ u u log 2`.

Proof: apply the general primorial estimate, use `2 ^ u + 1 ≤ 2 * 2 ^ u`, and evaluate
`log (2 ^ u)`.

Role: gives the explicit logarithmic upper bound for the seed modulus in the P2 comparison.
-/
theorem log_primorial_fifth_power_pow_two_le {u J : ℕ} (hu : 1 ≤ u) :
    Real.log
        (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J : ℕ) :
          ℝ) ≤
      10 * (J : ℝ) * ((2 ^ u : ℕ) : ℝ) * (u : ℝ) * Real.log (2 : ℝ) := by
  have hz : 2 ≤ 2 ^ u := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hu
  have hbase := log_primorial_fifth_power_pow_le (J := J) hz
  have hzR2 : (2 : ℝ) ≤ ((2 ^ u : ℕ) : ℝ) := by exact_mod_cast hz
  have hlogzpos : 0 < Real.log ((2 ^ u : ℕ) : ℝ) := Real.log_pos (by linarith only [hzR2])
  have hzp : ((2 ^ u : ℕ) : ℝ) + 1 ≤ 2 * ((2 ^ u : ℕ) : ℝ) := by nlinarith only [hzR2]
  have hlogz : Real.log ((2 ^ u : ℕ) : ℝ) = (u : ℝ) * Real.log (2 : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hmul : 5 * (J : ℝ) * ((2 ^ u + 1 : ℕ) : ℝ) ≤ 10 * (J : ℝ) * ((2 ^ u : ℕ) : ℝ) := by
    have hJ : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
    have hplus : ((2 ^ u + 1 : ℕ) : ℝ) ≤ 2 * ((2 ^ u : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hzp
    nlinarith only [hplus, hJ]
  have hfinal := mul_le_mul_of_nonneg_right hmul (le_of_lt hlogzpos)
  calc
    Real.log
          (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J :
              ℕ) :
            ℝ) ≤
        5 * (J : ℝ) * ((2 ^ u + 1 : ℕ) : ℝ) * Real.log ((2 ^ u : ℕ) : ℝ) :=
      by simpa only [mul_assoc, mul_left_comm, mul_comm] using hbase
    _ ≤ 10 * (J : ℝ) * ((2 ^ u : ℕ) : ℝ) * ((u : ℝ) * Real.log (2 : ℝ)) := by
      rw [← hlogz]
      exact hfinal
    _ = 10 * (J : ℝ) * ((2 ^ u : ℕ) : ℝ) * (u : ℝ) * Real.log (2 : ℝ) := by ring

/--
Inputs: positive real coefficients `c₀`, `K`, a positive natural exponent `J`, and a
lower cutoff `U₀ ≥ 10`.

Claim: for some `u ≥ U₀`, the floor-defined seed count exceeds `K * 2 ^ u * u`.

Proof: choose `u` beyond both the analytic growth threshold and `U₀`, then apply the
strict floor inequality to the resulting lower bound for the floor argument.

Role: lets P2 scale selection meet fixed lower bounds as well as its growth conditions.
-/
theorem exists_p2_floor_count_gt_linear_scale_from {c₀ K : ℝ} {J : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J)
    (hK : 0 < K) (U₀ : ℕ) (hU₀ : 10 ≤ U₀) :
    ∃ u : ℕ,
      U₀ ≤ u ∧
        c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4 ∧
        K * (2 ^ u : ℝ) * (u : ℝ) <
          (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log (2 : ℝ))) + 1 :
              ℕ) :
            ℝ)) := by
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  let A : ℝ := 40 * (J : ℝ) * K * Real.log 2 / c₀
  have hA : 0 < A := by
    dsimp only [A]
    exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 40) hJr) hK) hlog2) hc₀
  have hdenU : 0 < 20 * Real.log 2 := mul_pos (by norm_num only : (0 : ℝ) < 20) hlog2
  let R : ℝ := max (U₀ : ℝ) (c₀ / (20 * Real.log 2))
  obtain ⟨U, hU⟩ := exists_nat_gt R
  have hUR : R < (U : ℝ) := by exact_mod_cast hU
  have hU₀lt : (U₀ : ℝ) < (U : ℝ) := lt_of_le_of_lt (le_max_left _ _) hUR
  have hU₀Nat : U₀ < U := by exact_mod_cast hU₀lt
  have hU₀U : U₀ ≤ U := Nat.le_of_lt hU₀Nat
  have hU10 : 10 ≤ U := by exact le_trans hU₀ hU₀U
  have hUparam : c₀ / (20 * Real.log 2) < (U : ℝ) := lt_of_le_of_lt (le_max_right _ _) hUR
  obtain ⟨u, huU, hgrowth⟩ := exists_nat_pow_two_dominates_square_from A U hU10
  have hu10 : 10 ≤ u := le_trans hU10 huU
  have hU₀u : U₀ ≤ u := le_trans hU₀U huU
  have hUu : (U : ℝ) ≤ (u : ℝ) := by exact_mod_cast huU
  have huR : (0 : ℝ) < (u : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 10) hu10)
  have hparamSmall : c₀ < 20 * Real.log 2 * (u : ℝ) := by
    have hbase : c₀ < (U : ℝ) * (20 * Real.log 2) := (div_lt_iff₀ hdenU).mp hUparam
    have hmul := mul_le_mul_of_nonneg_right hUu (le_of_lt hdenU)
    nlinarith only [hbase, hmul]
  have hu4 : (u : ℝ) ≤ (u : ℝ) ^ 4 := by exact_mod_cast Nat.le_self_pow (by norm_num only : 4 ≠ 0) u
  have hparam : c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4 :=
    lt_of_lt_of_le hparamSmall (mul_le_mul_of_nonneg_left hu4 (le_of_lt hdenU))
  have hpow : (2 : ℝ) ^ u = ((2 ^ u : ℕ) : ℝ) := by norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have hzR : 0 < (2 ^ u : ℝ) := by positivity
  have hhalf : A / 2 * (u : ℝ) ^ 2 < (2 ^ u : ℝ) := by
    have hsquare : 0 ≤ (u : ℝ) ^ 2 := sq_nonneg _
    nlinarith only [hgrowth, hsquare, hzR]
  have hden : 0 < 20 * (J : ℝ) * (u : ℝ) * Real.log 2 :=
    mul_pos (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 20) hJr) huR) hlog2
  have hlinear :
    K * (2 ^ u : ℝ) * (u : ℝ) < c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) := by
    apply (lt_div_iff₀ hden).2
    calc
      (K * (2 ^ u : ℝ) * (u : ℝ)) * (20 * (J : ℝ) * (u : ℝ) * Real.log 2) =
          c₀ * (2 ^ u : ℝ) * (A / 2 * (u : ℝ) ^ 2) :=
        by
        dsimp only [A]
        field_simp
        ring
      _ < c₀ * (2 ^ u : ℝ) * (2 ^ u : ℝ) := mul_lt_mul_of_pos_left hhalf (mul_pos hc₀ hzR)
      _ = c₀ * (2 ^ u : ℝ) ^ 2 := by ring
  have hfloor :=
    p2_floor_parameter_bounds (J := J) (u := u) (z := 2 ^ u) hc₀ hJ (by omega) (by positivity) rfl
  rw [← hpow] at hfloor
  refine ⟨u, hU₀u, hparam, ?_⟩
  exact lt_trans hlinear hfloor.1

/--
Inputs: positive real coefficients `c₀`, `K`, and a positive natural exponent `J`.

Claim: for some `u ≥ 10`, the floor-defined seed count exceeds `K * 2 ^ u * u`.

Proof: specialize the lower-cutoff form to `U₀ = 10`.

Role: keeps the standard P2 scale-selection interface.
-/
theorem exists_p2_floor_count_gt_linear_scale {c₀ K : ℝ} {J : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J)
    (hK : 0 < K) :
    ∃ u : ℕ,
      10 ≤ u ∧
        c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4 ∧
        K * (2 ^ u : ℝ) * (u : ℝ) <
          (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log (2 : ℝ))) + 1 :
              ℕ) :
            ℝ)) := by
  obtain ⟨u, hu, hparam, hlinear⟩ :=
    exists_p2_floor_count_gt_linear_scale_from hc₀ hJ hK 10 (by norm_num only)
  exact ⟨u, hu, hparam, hlinear⟩

/--
Inputs: positive `c₀` and `J`, a seed exponent `u ≥ 1`, and `z = 2 ^ u` with `u ^ 3 ≤ z`.

Claim: if `c₀ < 20 log 2 * u ^ 4`, then the full-divisor seed count
`floor (c₀ z ^ 2 / (20 J u log 2)) + 1` is at most `z ^ 3`.

Proof: use `J ≥ 1` to compare the floor argument with `u ^ 3 * z ^ 2`, then apply the
natural floor upper bound.

Role: supplies the seed-count cutoff needed to compare `t` with the primorial modulus.
-/
theorem p2_full_divisor_seed_count_succ_le_cube {c₀ : ℝ} {J u z T : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J)
    (hu : 1 ≤ u) (hz : z = 2 ^ u) (hcubic : u ^ 3 ≤ z) (hparam : c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4)
    (hT : T = Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2))) :
    T + 1 ≤ z ^ 3 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hJR : (1 : ℝ) ≤ (J : ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt hJ))
  have huR : 0 < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hzR : 0 < (z : ℝ) := by
    rw [hz]
    exact_mod_cast Nat.pow_pos (by norm_num only : 0 < 2)
  have hden : 0 < 20 * (J : ℝ) * (u : ℝ) * Real.log 2 :=
    mul_pos (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 20) (by exact_mod_cast hJ)) huR) hlog2
  have hJfactor :
    20 * Real.log 2 * (u : ℝ) ^ 4 ≤ (u : ℝ) ^ 3 * (20 * (J : ℝ) * (u : ℝ) * Real.log 2) := by
    calc
      20 * Real.log 2 * (u : ℝ) ^ 4 = (20 * Real.log 2 * (u : ℝ) ^ 4) * 1 := by ring
      _ ≤ (20 * Real.log 2 * (u : ℝ) ^ 4) * (J : ℝ) :=
        mul_le_mul_of_nonneg_left hJR
          (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 20) (le_of_lt hlog2))
            (pow_nonneg (le_of_lt huR) 4))
      _ = (u : ℝ) ^ 3 * (20 * (J : ℝ) * (u : ℝ) * Real.log 2) := by ring
  have hcoef : c₀ / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) < (u : ℝ) ^ 3 := by
    apply (div_lt_iff₀ hden).2
    exact lt_of_lt_of_le hparam hJfactor
  have harg : c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) < ((z ^ 3 : ℕ) : ℝ) := by
    have hcubicR : (u : ℝ) ^ 3 ≤ (z : ℝ) := by exact_mod_cast hcubic
    calc
      c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) =
          (c₀ / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) * (z : ℝ) ^ 2 :=
        by ring
      _ < (u : ℝ) ^ 3 * (z : ℝ) ^ 2 := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hzR)
      _ ≤ (z : ℝ) ^ 3 := by
        calc
          (u : ℝ) ^ 3 * (z : ℝ) ^ 2 ≤ (z : ℝ) * (z : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hcubicR (sq_nonneg (z : ℝ))
          _ = (z : ℝ) ^ 3 := by ring
      _ = ((z ^ 3 : ℕ) : ℝ) := by rw [Nat.cast_pow]
  have hargpos : 0 < c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
    div_pos (mul_pos hc₀ (sq_pos_of_pos hzR)) hden
  have hfloor : Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) < z ^ 3 := by
    rw [Nat.floor_lt (le_of_lt hargpos)]
    exact harg
  rw [hT]
  omega

/--
Inputs: positive coefficients `c₀` and `D`, a positive exponent `J`, and a lower cutoff
`U₀ ≥ 10`.

Claim: for some seed exponent `u ≥ U₀`, `D * log q` is strictly below
`floor(t / 2) * log 2`, where `q` is the primorial seed power and `t` is the floor-defined
seed count.

Proof: make `t` exceed `(40 D J + 1) * 2 ^ u * u`; the primorial logarithm is at most
`10 J 2 ^ u * u * log 2`, and the natural floor of `t / 2` absorbs the scaled bound.

Role: establishes exponential room for the right side of the boxed P2 concentration bound
while satisfying an externally chosen lower scale.
-/
theorem exists_p2_seed_log_multiple_below_floor_half_from {c₀ D H : ℝ} {J : ℕ} (hc₀ : 0 < c₀)
    (hD : 0 < D) (hJ : 0 < J) (U₀ : ℕ) (hU₀ : 10 ≤ U₀) :
    ∃ u : ℕ,
      U₀ ≤ u ∧
        c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4 ∧
        H ≤ Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        D *
            Real.log
              (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^
                    J :
                  ℕ) :
                ℝ) <
          (Nat.floor
                (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 :
                      ℕ) :
                    ℝ) /
                  2) :
              ℝ) *
            Real.log 2 := by
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hDJ : 0 ≤ D * (J : ℝ) := mul_nonneg (le_of_lt hD) (Nat.cast_nonneg J)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  let K : ℝ := max (40 * D * (J : ℝ) + 1) H
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  obtain ⟨u, huU, hparam, hlinear⟩ := exists_p2_floor_count_gt_linear_scale_from hc₀ hJ hK U₀ hU₀
  have hu10 : 10 ≤ u := le_trans hU₀ huU
  have hpow : (2 : ℝ) ^ u = ((2 ^ u : ℕ) : ℝ) := by norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  have huR : (10 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu10
  have hzbig : (1024 : ℝ) ≤ (2 : ℝ) ^ u := by
    have hnat : 2 ^ 10 ≤ 2 ^ u := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hu10
    exact_mod_cast hnat
  have hzu : (10240 : ℝ) ≤ (2 : ℝ) ^ u * (u : ℝ) := by nlinarith only [hzbig, huR]
  have hgap : 10 * D * (J : ℝ) * (2 : ℝ) ^ u * (u : ℝ) + 1 < K * (2 : ℝ) ^ u * (u : ℝ) / 2 := by
    have hKleft : 40 * D * (J : ℝ) + 1 ≤ K := le_max_left _ _
    dsimp only [K]
    nlinarith only [hzu, hDJ, hKleft]
  have ht :
    K * (2 ^ u : ℝ) * (u : ℝ) <
      (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 : ℕ) : ℝ)) :=
    hlinear
  have ht' :
    K * (2 : ℝ) ^ u * (u : ℝ) <
      (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 : ℕ) : ℝ)) :=
    ht
  have hHK : H ≤ K := le_max_right _ _
  have hzuone : (1 : ℝ) ≤ (2 : ℝ) ^ u * (u : ℝ) := by nlinarith only [hzbig, huR]
  have hthreshold :
    H ≤ Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 := by
    have hKzu : H ≤ K * (2 : ℝ) ^ u * (u : ℝ) := by
      calc
        H = H * 1 := by ring
        _ ≤ K * ((2 : ℝ) ^ u * (u : ℝ)) := by
          exact mul_le_mul hHK hzuone (by positivity) (by positivity)
        _ = K * (2 : ℝ) ^ u * (u : ℝ) := by ring
    exact_mod_cast le_of_lt (lt_of_le_of_lt hKzu ht')
  let t : ℕ := Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
  have hfloorHalf : (t : ℝ) / 2 - 1 < (Nat.floor ((t : ℝ) / 2) : ℝ) := by
    have hh := Nat.lt_floor_add_one ((t : ℝ) / 2)
    linarith
  have hsmall : 10 * D * (J : ℝ) * (2 : ℝ) ^ u * (u : ℝ) + 1 < (t : ℝ) / 2 := by
    have hhalf := div_lt_div_of_pos_right ht' (by norm_num only : (0 : ℝ) < 2)
    dsimp only [t]
    nlinarith only [hgap, hhalf]
  have hltfloor : 10 * D * (J : ℝ) * (2 : ℝ) ^ u * (u : ℝ) < (Nat.floor ((t : ℝ) / 2) : ℝ) := by
    linarith only [hsmall, hfloorHalf]
  have hlog := log_primorial_fifth_power_pow_two_le (u := u) (J := J) (by omega)
  refine ⟨u, huU, hparam, hthreshold, ?_⟩
  have hmul := mul_lt_mul_of_pos_right hltfloor hlog2
  have hlogscaled := mul_le_mul_of_nonneg_left hlog (le_of_lt hD)
  calc
    D *
          Real.log
            (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J :
                ℕ) :
              ℝ) ≤
        10 * D * (J : ℝ) * ((2 ^ u : ℕ) : ℝ) * (u : ℝ) * Real.log 2 :=
      by simpa only [mul_assoc, mul_left_comm, mul_comm] using hlogscaled
    _ <
        (Nat.floor
              (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 : ℕ) :
                  ℝ) /
                2) :
            ℝ) *
          Real.log 2 :=
      by simpa only [t, hpow, mul_assoc, mul_left_comm, mul_comm] using hmul

/--
Inputs: positive coefficients `c₀` and `D`, and a positive natural exponent `J`.

Claim: at some seed exponent `u ≥ 10`, `D * log q` is strictly below
`floor(t / 2) * log 2`, where `q` is the primorial seed power and `t` is the floor-defined
seed count.

Proof: specialize the lower-cutoff result to `U₀ = 10`.

Role: keeps the standard P2 exponential-room interface.
-/
theorem exists_p2_seed_log_multiple_below_floor_half {c₀ D H : ℝ} {J : ℕ} (hc₀ : 0 < c₀)
    (hD : 0 < D) (hJ : 0 < J) :
    ∃ u : ℕ,
      10 ≤ u ∧
        c₀ < 20 * Real.log 2 * (u : ℝ) ^ 4 ∧
        H ≤ Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        D *
            Real.log
              (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^
                    J :
                  ℕ) :
                ℝ) <
          (Nat.floor
                (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 :
                      ℕ) :
                    ℝ) /
                  2) :
              ℝ) *
            Real.log 2 := by
  obtain ⟨u, hu, hparam, hthreshold, hlog⟩ :=
    exists_p2_seed_log_multiple_below_floor_half_from hc₀ hD hJ 10 (by norm_num only)
  exact ⟨u, hu, hparam, hthreshold, hlog⟩

/--
Inputs: a real seed bound `q ≥ 1`, a count `0 ≤ t ≤ q`, and a logarithmic factor
`0 ≤ L ≤ q`, together with natural exponents `J` and `w`.

Claim: the polynomial side of the P2 concentration inequality is at most
`40 J (2 ^ w + 1) q ^ 6` after replacing `log q` by `L`.

Proof: bound `t + 3` by `4 q`, the inner sum by `(2 ^ w + 1) q ^ 4`, and multiply
the two estimates using nonnegativity.

Role: reduces the remaining P2 concentration estimate to absorbing a fixed coefficient
and a sixth power of `q` into the half-exponential floor term.
-/
theorem p2_concentration_left_le_q_six {q t L : ℝ} {J w : ℕ} (hq : 1 ≤ q) (ht : 0 ≤ t) (htq : t ≤ q)
    (hL : 0 ≤ L) (hLq : L ≤ q) :
    10 * (J : ℝ) * ((t + 3) * L) * ((2 : ℝ) ^ w * q ^ 2 * t * L + q) ≤
      40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * q ^ 6 := by
  have hq0 : 0 ≤ q := le_trans (by norm_num only : (0 : ℝ) ≤ 1) hq
  have ht3 : t + 3 ≤ 4 * q := by nlinarith only [hq, htq]
  have hfactor : (t + 3) * L ≤ 4 * q ^ 2 := by
    calc
      (t + 3) * L ≤ (4 * q) * q :=
        mul_le_mul ht3 hLq hL (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) hq0)
      _ = 4 * q ^ 2 := by ring
  have hq2 : q ≤ q ^ 2 := by
    calc
      q = 1 * q := by ring
      _ ≤ q * q := mul_le_mul_of_nonneg_right hq hq0
      _ = q ^ 2 := by ring
  have hq4 : q ^ 2 ≤ q ^ 4 := by
    calc
      q ^ 2 = 1 * q ^ 2 := by ring
      _ ≤ q ^ 2 * q ^ 2 := mul_le_mul_of_nonneg_right (le_trans hq hq2) (sq_nonneg q)
      _ = q ^ 4 := by ring
  have hqle : q ≤ q ^ 4 := le_trans hq2 hq4
  have hq3 : 0 ≤ q ^ 3 := mul_nonneg (sq_nonneg q) hq0
  have hprod : q ^ 2 * t * L ≤ q ^ 4 := by
    calc
      q ^ 2 * t * L ≤ q ^ 3 * L := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htq (sq_nonneg q)) hL
      _ ≤ q ^ 3 * q := mul_le_mul_of_nonneg_left hLq hq3
      _ = q ^ 4 := by ring
  have hH : 0 ≤ (2 : ℝ) ^ w := pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) w
  have hmulprod := mul_le_mul_of_nonneg_left hprod hH
  have hinside : (2 : ℝ) ^ w * q ^ 2 * t * L + q ≤ ((2 : ℝ) ^ w + 1) * q ^ 4 := by
    calc
      (2 : ℝ) ^ w * q ^ 2 * t * L + q ≤ (2 : ℝ) ^ w * q ^ 4 + q := by nlinarith only [hmulprod]
      _ ≤ (2 : ℝ) ^ w * q ^ 4 + q ^ 4 := by nlinarith only [hqle]
      _ = ((2 : ℝ) ^ w + 1) * q ^ 4 := by ring
  have hterm0 : 0 ≤ (2 : ℝ) ^ w * q ^ 2 * t * L := by
    exact mul_nonneg (mul_nonneg (mul_nonneg hH (sq_nonneg q)) ht) hL
  have hinside0 : 0 ≤ (2 : ℝ) ^ w * q ^ 2 * t * L + q := add_nonneg hterm0 hq0
  have hfactorR0 : 0 ≤ 4 * q ^ 2 := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (sq_nonneg q)
  have hcombined := mul_le_mul hfactor hinside hinside0 hfactorR0
  calc
    10 * (J : ℝ) * ((t + 3) * L) * ((2 : ℝ) ^ w * q ^ 2 * t * L + q) =
        10 * (J : ℝ) * (((t + 3) * L) * ((2 : ℝ) ^ w * q ^ 2 * t * L + q)) :=
      by ring
    _ ≤ 10 * (J : ℝ) * ((4 * q ^ 2) * (((2 : ℝ) ^ w + 1) * q ^ 4)) :=
      mul_le_mul_of_nonneg_left hcombined
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 10) (Nat.cast_nonneg J))
    _ = 40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * q ^ 6 := by ring

/--
Inputs: natural bounds `q ≥ 2` and `t ≤ q`, together with natural exponents `J` and `w`.

Claim: the P2 concentration left side with `L = log q` is at most
`40 J (2 ^ w + 1) q ^ 6`.

Proof: use positivity and the elementary upper bound `log q ≤ q`, then apply
`p2_concentration_left_le_q_six`.

Role: converts the original left side to a fixed coefficient times a fixed power of `q`.
-/
theorem p2_concentration_log_left_le_q_six {q t : ℕ} {J w : ℕ} (hq : 2 ≤ q) (ht : t ≤ q) :
    10 * (J : ℝ) * (((t + 3 : ℕ) : ℝ) * Real.log (q : ℝ)) *
        ((2 : ℝ) ^ w * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) ≤
      40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * (q : ℝ) ^ 6 := by
  have hqR2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqR1 : (1 : ℝ) ≤ (q : ℝ) := le_trans (by norm_num only : (1 : ℝ) ≤ 2) hqR2
  have htR : (t : ℝ) ≤ (q : ℝ) := by exact_mod_cast ht
  have hlogpos : 0 < Real.log (q : ℝ) := Real.log_pos (by linarith only [hqR2])
  have hlogle : Real.log (q : ℝ) ≤ (q : ℝ) := Real.log_le_self (by linarith only [hqR2])
  have hmain :=
    p2_concentration_left_le_q_six (J := J) (w := w) hqR1 (by exact_mod_cast Nat.zero_le t) htR
      (le_of_lt hlogpos) hlogle
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hmain

/--
Inputs: positive `c₀`, `q ≥ 2`, and natural exponents `J`, `w`, and `n`.

Claim: if the logarithm of the coefficient ratio plus `6 log q` is below `n log 2`, then
`40 J (2 ^ w + 1) q ^ 6 < c₀ 2 ^ n`.

Proof: combine the logarithms on the left, apply strict monotonicity of the exponential,
then multiply by `c₀`.

Role: turns the logarithmic margin from the seed scale into the required P2 concentration
majorant.
-/
theorem p2_q_six_absorbed_by_exp {c₀ q : ℝ} {J w n : ℕ} (hc₀ : 0 < c₀) (hq : 2 ≤ q) (hJ : 0 < J)
    (hlog :
      Real.log (40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) / c₀) + 6 * Real.log q < (n : ℝ) * Real.log 2) :
    40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * q ^ 6 < c₀ * (2 : ℝ) ^ n := by
  let C : ℝ := 40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) / c₀
  have hqpos : 0 < q := by linarith only [hq]
  have hJpos : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hbasepos : 0 < (2 : ℝ) ^ w + 1 := by
    have hpow0 : 0 ≤ (2 : ℝ) ^ w := pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) w
    linarith only [hpow0]
  have hCpos : 0 < C := by
    dsimp only [C]
    exact div_pos (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 40) hJpos) hbasepos) hc₀
  have hprodpos : 0 < C * q ^ 6 := mul_pos hCpos (pow_pos hqpos 6)
  have hlogprod : Real.log (C * q ^ 6) = Real.log C + 6 * Real.log q := by
    rw [Real.log_mul (ne_of_gt hCpos) (pow_ne_zero _ (ne_of_gt hqpos)), Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlogpow : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := by rw [Real.log_pow]
  have hloglt : Real.log (C * q ^ 6) < Real.log ((2 : ℝ) ^ n) := by
    rw [hlogprod, hlogpow]
    simpa only [C] using hlog
  have hexp := Real.exp_lt_exp.mpr hloglt
  rw [Real.exp_log hprodpos, Real.exp_log (pow_pos (by norm_num only : (0 : ℝ) < 2) n)] at hexp
  have hCeq : c₀ * C = 40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) := by
    dsimp only [C]
    field_simp
  calc
    40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * q ^ 6 = c₀ * (C * q ^ 6) := by
      rw [← hCeq]
      ring
    _ < c₀ * (2 : ℝ) ^ n := mul_lt_mul_of_pos_left hexp hc₀

/--
Inputs: a positive scale `c₀`, a positive exponent `J`, a factor count `w`, and a lower
cutoff `U₀ ≥ 10`.

Claim: at some `u ≥ U₀`, the coefficient logarithm plus `6 log q` lies below the
half-exponential floor margin, for `q` equal to the primorial seed power; its floor count is
at least two.

Proof: choose a logarithmic multiplier that absorbs the fixed coefficient and sixth power,
apply the lower-cutoff seed log comparison, and use `q ≥ 2` to absorb its constant.

Role: supplies the logarithmic hypothesis needed to absorb the `q ^ 6` P2 left-side bound
at any required minimum scale.
-/
theorem exists_p2_seed_q_six_loggap_from {c₀ : ℝ} {J w : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J) (U₀ : ℕ)
    (hU₀ : 10 ≤ U₀) :
    ∃ u : ℕ,
      U₀ ≤ u ∧
        2 ≤ ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ^ 5) ^ J ∧
        Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ≤
          ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ^ 5) ^ J ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤
          Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        2 ≤ Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        Real.log (40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) / c₀) +
            6 *
              Real.log
                (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^
                      J :
                    ℕ) :
                  ℝ) <
          (Nat.floor
                (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 :
                      ℕ) :
                    ℝ) /
                  2) :
              ℝ) *
            Real.log 2 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  let C : ℝ := 40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) / c₀
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hbasepos : 0 < (2 : ℝ) ^ w + 1 := by
    have hpow0 : 0 ≤ (2 : ℝ) ^ w := pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) w
    linarith only [hpow0]
  have hCpos : 0 < C := by
    dsimp only [C]
    exact div_pos (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 40) hJr) hbasepos) hc₀
  let D : ℝ := 7 + |Real.log C| / Real.log 2
  have hD : 0 < D := by
    dsimp only [D]
    have hratio : 0 ≤ |Real.log C| / Real.log 2 := div_nonneg (abs_nonneg _) (le_of_lt hlog2)
    linarith only [hratio]
  obtain ⟨u, huU, hparam, hthresholdMax, hDlog⟩ :=
    exists_p2_seed_log_multiple_below_floor_half_from hc₀ hD hJ U₀ hU₀ (H :=
      max (PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 : ℝ) 2)
  have hu10 : 10 ≤ u := le_trans hU₀ huU
  let N : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id
  let q : ℕ := (N ^ 5) ^ J
  let t : ℕ := Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
  have hthreshold : PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤ t := by
    change
      PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤
        Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
    exact_mod_cast le_trans (le_max_left _ _) hthresholdMax
  have htTwo : 2 ≤ t := by
    change 2 ≤ Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
    exact_mod_cast le_trans (le_max_right _ _) hthresholdMax
  have hcount := primeCounting_two_pow_lower hu10
  have hNlower : 2 ^ (3 * u) ≤ N := by
    calc
      2 ^ (3 * u) ≤ 2 ^ Nat.primeCounting (2 ^ u) := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hcount
      _ ≤ N := by
        dsimp only [N]
        exact primeProductLE_ge_two_pow_primeCounting _
  have hNge2 : 2 ≤ N := le_trans (Nat.le_self_pow (by omega : 3 * u ≠ 0) 2) hNlower
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num only : 0 < 2) hNge2
  have hqNat : 2 ≤ q := by
    dsimp only [q]
    calc
      2 ≤ N := hNge2
      _ ≤ N ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
      _ ≤ (N ^ 5) ^ J := Nat.le_self_pow (Nat.ne_of_gt hJ) (N ^ 5)
  have hcube := powTwo_ge_cube hu10
  have hTupper :=
    p2_full_divisor_seed_count_succ_le_cube hc₀ hJ (by omega : 1 ≤ u) rfl hcube hparam rfl
  have hTupper' :
    Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ≤ (2 ^ u) ^ 3 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hTupper
  have hpow3 : 2 ^ (3 * u) = (2 ^ u) ^ 3 := by rw [Nat.mul_comm 3 u, pow_mul]
  have htN : Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ≤ N := by
    calc
      Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ≤ (2 ^ u) ^ 3 :=
        hTupper'
      _ ≤ N := by
        rw [← hpow3]; exact hNlower
  have hNq : N ≤ q := by
    dsimp only [q]
    calc
      N ≤ N ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
      _ ≤ (N ^ 5) ^ J := Nat.le_self_pow (Nat.ne_of_gt hJ) (N ^ 5)
  have htq := le_trans htN hNq
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat
  have hlogqlo : Real.log 2 ≤ Real.log (q : ℝ) :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 2) hqR
  have hDlog' : D * Real.log (q : ℝ) < (Nat.floor ((t : ℝ) / 2) : ℝ) * Real.log 2 := by
    simpa only [N, q, t] using hDlog
  have habs : |Real.log C| ≤ |Real.log C| / Real.log 2 * Real.log (q : ℝ) := by
    have habs0 := abs_nonneg (Real.log C)
    have hmul := mul_le_mul_of_nonneg_left hlogqlo habs0
    calc
      |Real.log C| = (|Real.log C| * Real.log 2) / Real.log 2 := by field_simp
      _ ≤ (|Real.log C| * Real.log (q : ℝ)) / Real.log 2 :=
        div_le_div_of_nonneg_right hmul (le_of_lt hlog2)
      _ = |Real.log C| / Real.log 2 * Real.log (q : ℝ) := by ring
  have hlogqnonneg : 0 ≤ Real.log (q : ℝ) := le_of_lt (Real.log_pos (by linarith only [hqR]))
  have h6 : 6 * Real.log (q : ℝ) ≤ 7 * Real.log (q : ℝ) := by nlinarith only [hlogqnonneg]
  have hlogbound : Real.log C + 6 * Real.log (q : ℝ) ≤ D * Real.log (q : ℝ) := by
    calc
      Real.log C + 6 * Real.log (q : ℝ) ≤ |Real.log C| + 7 * Real.log (q : ℝ) :=
        add_le_add (le_abs_self _) h6
      _ ≤ |Real.log C| / Real.log 2 * Real.log (q : ℝ) + 7 * Real.log (q : ℝ) := by
        nlinarith only [habs]
      _ = D * Real.log (q : ℝ) := by
        dsimp only [D]; ring
  refine ⟨u, huU, hqNat, htq, hthreshold, htTwo, ?_⟩
  have hfinal := lt_of_le_of_lt hlogbound hDlog'
  simpa only [C] using hfinal

/--
Inputs: a positive scale `c₀` and a positive natural exponent `J`.

Claim: at some `u ≥ 10`, the coefficient logarithm plus `6 log q` lies below the
half-exponential floor margin, for `q` equal to the primorial seed power.

Proof: specialize the lower-cutoff result to `U₀ = 10` and discard its additional floor
count lower bound.

Role: keeps the standard P2 logarithmic-gap interface.
-/
theorem exists_p2_seed_q_six_loggap {c₀ : ℝ} {J w : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J) :
    ∃ u : ℕ,
      10 ≤ u ∧
        2 ≤ ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ^ 5) ^ J ∧
        Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ≤
          ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ^ 5) ^ J ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤
          Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        Real.log (40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) / c₀) +
            6 *
              Real.log
                (((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^
                      J :
                    ℕ) :
                  ℝ) <
          (Nat.floor
                (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 :
                      ℕ) :
                    ℝ) /
                  2) :
              ℝ) *
            Real.log 2 := by
  obtain ⟨u, hu, hq, htq, hthreshold, _, hlog⟩ :=
    exists_p2_seed_q_six_loggap_from hc₀ hJ 10 (by norm_num only)
  exact ⟨u, hu, hq, htq, hthreshold, hlog⟩

/--
Inputs: positive `c₀` and a positive natural exponent `J`.

Claim: for some `u ≥ 10`, the sixth-power polynomial majorant in `q` is strictly below
`c₀ * 2 ^ floor(t / 2)` for the primorial seed power.

Proof: apply the logarithmic margin from `exists_p2_seed_q_six_loggap` and exponentiate.

Role: supplies the right-side numerical bound for the P2 concentration comparison.
-/
theorem exists_p2_seed_q_six_absorption {c₀ : ℝ} {J w : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J) :
    ∃ u : ℕ,
      10 ≤ u ∧
        2 ≤ ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ^ 5) ^ J ∧
        Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ≤
          ((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id ^ 5) ^ J ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤
          Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) *
            ((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J :
                ℝ) ^
              6 <
          c₀ *
            (2 : ℝ) ^
              (Nat.floor
                (((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 :
                      ℕ) :
                    ℝ) /
                  2)) := by
  obtain ⟨u, hu10, hq, htq, hthreshold, hlog⟩ := exists_p2_seed_q_six_loggap (w := w) hc₀ hJ
  let N : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id
  let q : ℕ := (N ^ 5) ^ J
  let t : ℕ := Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 2 ≤ q by simpa only [N, q] using hq)
  have hAbs :=
    p2_q_six_absorbed_by_exp (q := (q : ℝ)) (J := J) (w := w) (n := Nat.floor ((t : ℝ) / 2)) hc₀ hqR
      hJ (by simpa only [N, q, t] using hlog)
  refine ⟨u, hu10, hq, htq, hthreshold, ?_⟩
  simpa only [Nat.cast_pow, N, q, t] using hAbs

/--
Inputs: positive `c₀`, a positive natural exponent `J`, and a natural factor count `w`.

Claim: for some `u ≥ 10`, the seed parameters `q` and `t` satisfy the boxed P2 concentration
inequality.

Proof: bound its left side by `40 J (2 ^ w + 1) q ^ 6`, then use the half-exponential
absorption theorem for the same seed scale.

Role: closes the numerical P2 concentration gate for the full-divisor seed construction.
-/
theorem exists_p2_full_divisor_concentration_bound {c₀ : ℝ} {J w : ℕ} (hc₀ : 0 < c₀) (hJ : 0 < J) :
    ∃ u q t : ℕ,
      10 ≤ u ∧
        q = (((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J ∧
        t = Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤ t ∧
        2 * Nat.primeCounting (1024 * t) ≤ t ∧
        ((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℕ) : ℝ) <
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) ∧
        10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
            ((2 : ℝ) ^ w * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
          c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := by
  obtain ⟨u, hu10, hqNat, htq, hthreshold, hAbs⟩ := exists_p2_seed_q_six_absorption (w := w) hc₀ hJ
  let N : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id
  let q : ℕ := (N ^ 5) ^ J
  let t : ℕ := Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
  have hleft := p2_concentration_log_left_le_q_six (q := q) (t := t) (J := J) (w := w) hqNat htq
  refine ⟨u, q, t, hu10, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · simpa only [t] using
      (show
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤
          Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
        by exact_mod_cast hthreshold)
  · exact
      PseudoPrime.AnalyticNumberTheory.AGP.primeCounting_bound_of_primeTailCountThreshold1024
        (by simpa only [t] using hthreshold)
  · have hseedCount :=
      PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_count_lower_bound_of_two_pow_power hc₀
        hu10 hJ
    have hApos : 0 < c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) := by positivity
    have hfloor :
      (Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℝ) ≤
        c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
      Nat.floor_le (le_of_lt hApos)
    have hdouble :
      2 * (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) ≤
        PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
          ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) := by
      calc
        2 * (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) =
            c₀ * (2 ^ u : ℝ) ^ 2 / (10 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
          by
          field_simp
          norm_num only
        _ ≤
            PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
              ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) :=
          by simpa only [q, N, Nat.cast_pow, Nat.cast_ofNat] using hseedCount
    have hAstrict :
      c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) <
        2 * (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) := by
      nlinarith only [hApos]
    exact lt_of_le_of_lt hfloor (lt_of_lt_of_le hAstrict hdouble)
  have hAbs' :
    40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * (q : ℝ) ^ 6 < c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := by
    simpa only [Nat.cast_pow, N, q, t] using hAbs
  have hcombine := lt_of_le_of_lt hleft hAbs'
  simpa only [Nat.cast_add, Nat.cast_ofNat, mul_assoc] using hcombine

/--
Inputs: a positive seed coefficient, a positive exponent, a factor-count parameter, and a
required lower bound for the seed modulus.

Claim: the full-divisor seed scale can satisfy the P2 concentration inequality while also making
its primorial modulus at least the requested bound.

Proof: choose the seed exponent beyond the requested bound, preserve the logarithmic absorption
estimate, and derive the same cutoff and count margins as the base concentration theorem.

Role: lets the primorial seed scale dominate the prescribed base and finite-base cutoffs before
the full-divisor modulus is constructed.
-/
theorem exists_p2_full_divisor_concentration_bound_above {c₀ : ℝ} {J w : ℕ} (hc₀ : 0 < c₀)
    (hJ : 0 < J) (q₀ : ℕ) :
    ∃ u q t : ℕ,
      10 ≤ u ∧
        q₀ ≤ q ∧
        q₀ ≤ u ∧
        q = (((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J ∧
        t = Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤ t ∧
        2 * Nat.primeCounting (1024 * t) ≤ t ∧
        ((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℕ) : ℝ) <
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) ∧
        10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
            ((2 : ℝ) ^ w * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
          c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := by
  let U₀ := max 10 q₀
  obtain ⟨u, huU₀, hqNat, htq, hthreshold, htTwo, hlog⟩ :=
    exists_p2_seed_q_six_loggap_from (w := w) hc₀ hJ U₀
      (by
        dsimp only [U₀]; omega)
  have hu10 : 10 ≤ u :=
    le_trans
      (by
        dsimp only [U₀]; omega)
      huU₀
  let N : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id
  let q : ℕ := (N ^ 5) ^ J
  let t : ℕ := Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
  have hqNat' : 2 ≤ q := by simpa only [N, q] using hqNat
  have hcube := powTwo_ge_cube hu10
  have huCube : u ≤ u ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) u
  have huTwo : u ≤ 2 ^ u := le_trans huCube hcube
  have hNlower : 2 ^ (3 * u) ≤ N := by
    calc
      2 ^ (3 * u) ≤ 2 ^ Nat.primeCounting (2 ^ u) :=
        Nat.pow_le_pow_right (by omega : 1 ≤ 2) (primeCounting_two_pow_lower hu10)
      _ ≤ N := by
        dsimp only [N]
        exact PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_ge_two_pow_primeCounting _
  have hNq : N ≤ q := by
    dsimp only [q]
    calc
      N ≤ N ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
      _ ≤ (N ^ 5) ^ J := Nat.le_self_pow (Nat.ne_of_gt hJ) (N ^ 5)
  have hq₀u : q₀ ≤ u := by
    have hU₀q : q₀ ≤ U₀ := by
      dsimp only [U₀]; exact le_max_right _ _
    exact le_trans hU₀q huU₀
  have hq₀ : q₀ ≤ q := by
    have huN : u ≤ N := by
      have hpow : 2 ^ u ≤ 2 ^ (3 * u) := Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega)
      exact le_trans huTwo (le_trans hpow hNlower)
    exact le_trans hq₀u (le_trans huN hNq)
  have hqR : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqNat'
  have hAbs :=
    PseudoPrime.AnalyticNumberTheory.AGP.p2_q_six_absorbed_by_exp (q := (q : ℝ)) (J := J) (w := w)
      (n := Nat.floor ((t : ℝ) / 2)) hc₀ hqR hJ (by simpa only [N, q, t] using hlog)
  have hleft :=
    PseudoPrime.AnalyticNumberTheory.AGP.p2_concentration_log_left_le_q_six (q := q) (t := t) (J :=
      J) (w := w) hqNat' htq
  have hseedCount :=
    PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_count_lower_bound_of_two_pow_power hc₀ hu10
      hJ
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast hJ
  have huPos : 0 < (u : ℝ) := by exact_mod_cast (by omega : 0 < u)
  have hzPos : 0 < (2 ^ u : ℝ) := by exact_mod_cast Nat.pow_pos (by norm_num only : 0 < 2)
  have hApos : 0 < c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
    div_pos (mul_pos hc₀ (sq_pos_of_pos hzPos))
      (mul_pos (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 20) hJpos) huPos) hlog2)
  have hfloor :
    (Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℝ) ≤
      c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
    Nat.floor_le (le_of_lt hApos)
  have hdouble :
    2 * (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) ≤
      PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
        ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) := by
    calc
      2 * (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) =
          c₀ * (2 ^ u : ℝ) ^ 2 / (10 * (J : ℝ) * (u : ℝ) * Real.log 2) :=
        by ring
      _ ≤
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) :=
        by simpa only [q, N, Nat.cast_pow, Nat.cast_ofNat] using hseedCount
  have hAstrict :
    c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2) <
      2 * (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) := by
    nlinarith only [hApos]
  have hseed :
    (Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℝ) <
      PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
        ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) :=
    lt_of_le_of_lt hfloor (lt_of_lt_of_le hAstrict hdouble)
  have hAbs' :
    40 * (J : ℝ) * ((2 : ℝ) ^ w + 1) * (q : ℝ) ^ 6 < c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := by
    simpa only [Nat.cast_pow, N, q, t] using hAbs
  have hcombine := lt_of_le_of_lt hleft hAbs'
  refine ⟨u, q, t, hu10, hq₀, hq₀u, ?_, ?_, ?_, ?_, hseed, ?_⟩
  · rfl
  · rfl
  · simpa only [t] using
      (show
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤
          Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1
        by exact_mod_cast hthreshold)
  · exact
      PseudoPrime.AnalyticNumberTheory.AGP.primeCounting_bound_of_primeTailCountThreshold1024
        (by simpa only [t] using hthreshold)
  · simpa only [Nat.cast_add, Nat.cast_ofNat, mul_assoc] using hcombine

/--
Inputs: a positive seed coefficient, a positive exponent, and a factor-count
parameter for the P2 concentration bound.

Claim: the selected primorial scale satisfies all existing P2 and cutoff
conditions, together with the stronger initial-count margin
`c₀ z^2 / (10 J u log 2) ≤ coefficient * 2^π(z)`.

Proof: retain `exists_p2_full_divisor_concentration_bound` and expose the
prime-product estimate already used in its seed-count proof.

Role: provides enough strict margin to account for both exceptional-factor
removal and exclusion of the divisor `1` in the initial seed average.
-/
theorem exists_p2_full_divisor_concentration_bound_with_seed_margin {c₀ : ℝ} {J w : ℕ}
    (hc₀ : 0 < c₀) (hJ : 0 < J) :
    ∃ u q t : ℕ,
      10 ≤ u ∧
        q = (((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J ∧
        t = Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤ t ∧
        2 * Nat.primeCounting (1024 * t) ≤ t ∧
        ((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℕ) : ℝ) <
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) ∧
        c₀ * (2 ^ u : ℝ) ^ 2 / (10 * (J : ℝ) * (u : ℝ) * Real.log 2) ≤
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) ∧
        10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
            ((2 : ℝ) ^ w * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
          c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := by
  obtain ⟨u, q, t, hu, hq, ht, hthreshold, htail, hseed, hbox⟩ :=
    exists_p2_full_divisor_concentration_bound hc₀ hJ
  have hmargin :=
    PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_count_lower_bound_of_two_pow_power hc₀ hu hJ
  refine ⟨u, q, t, hu, hq, ht, hthreshold, htail, hseed, ?_, hbox⟩
  simpa only [hq, Nat.cast_pow, Nat.cast_ofNat] using hmargin

/--
Inputs: a positive seed coefficient, a positive exponent, a factor-count parameter, and a lower
bound required for the primorial seed modulus.

Claim: one scale meets the lower-bound, cutoff-1024, initial-count-margin, and full-divisor P2
concentration conditions simultaneously.

Proof: apply the lower-bounded concentration theorem, then expose the primorial count estimate
that supplies the stronger initial-count margin.

Role: gives the seed-selection stage a single output that can dominate prescribed base cutoffs and
feed both initial counting and the later P2 construction.
-/
theorem exists_p2_full_divisor_concentration_bound_above_with_seed_margin {c₀ : ℝ} {J w : ℕ}
    (hc₀ : 0 < c₀) (hJ : 0 < J) (q₀ : ℕ) :
    ∃ u q t : ℕ,
      10 ≤ u ∧
        q₀ ≤ q ∧
        q₀ ≤ u ∧
        q = (((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ u)).prod id : ℕ) ^ 5) ^ J ∧
        t = Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) + 1 ∧
        PseudoPrime.AnalyticNumberTheory.AGP.primeTailCountThreshold1024 ≤ t ∧
        2 * Nat.primeCounting (1024 * t) ≤ t ∧
        ((Nat.floor (c₀ * (2 ^ u : ℝ) ^ 2 / (20 * (J : ℝ) * (u : ℝ) * Real.log 2)) : ℕ) : ℝ) <
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) ∧
        c₀ * (2 ^ u : ℝ) ^ 2 / (10 * (J : ℝ) * (u : ℝ) * Real.log 2) ≤
          PseudoPrime.AnalyticNumberTheory.AGP.reliableProp15Coefficient c₀ 1 q *
            ((2 ^ Nat.primeCounting (2 ^ u) : ℕ) : ℝ) ∧
        10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
            ((2 : ℝ) ^ w * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
          c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := by
  obtain ⟨u, q, t, hu, hq₀, hq₀u, hq, ht, hthreshold, htail, hseed, hbox⟩ :=
    exists_p2_full_divisor_concentration_bound_above hc₀ hJ q₀
  have hmargin :=
    PseudoPrime.AnalyticNumberTheory.AGP.primeProductLE_count_lower_bound_of_two_pow_power hc₀ hu hJ
  refine ⟨u, q, t, hu, hq₀, hq₀u, hq, ht, hthreshold, htail, hseed, ?_, hbox⟩
  simpa only [hq, Nat.cast_pow, Nat.cast_ofNat] using hmargin

/--
Inputs: a positive prime bound `q` and a factor count `s`.

Claim: choosing the second-stage prime bound as `(q ^ s) ^ 5` places every
product of `s` factors bounded by `q` below the Proposition 1.5 divisor cutoff.

Proof: apply the fifth-power cutoff lemma to `q ^ s` and rewrite the chosen
bound as its fifth power.

Role: this gives an explicit second-stage cutoff choice for the fixed-size
factor products used in the P2 construction.
-/
theorem pow_le_reliableProp15DivisorCutoff_fifth_power {q s : ℕ} (hq : 0 < q) :
    q ^ s ≤ reliableProp15DivisorCutoff (q ^ (5 * s)) := by
  have hqpow : 0 < q ^ s := Nat.pow_pos hq
  have hcut := le_reliableProp15DivisorCutoff_fifth_power (q ^ s) hqpow
  have hexp : q ^ (5 * s) = (q ^ s) ^ 5 := by rw [show 5 * s = s * 5 by omega, Nat.pow_mul]
  rw [hexp]
  exact hcut

/--
Inputs: a nonnegative main term `B`, its majorant `M`, the boxed P2 inequality,
and a lower bound on the divisor exponent `h`.

Claim: if `log x` is bounded by the scale used in the boxed inequality and
`floor(t / 2) ≤ h`, then `B` is below the Proposition 1.5 coefficient mass
`c₀ 2^h / (2 log x)`.

Proof: multiply by the positive denominator, compare it with the boxed scale,
and then increase the exponential exponent from `floor(t / 2)` to `h`.

Role: converts the explicit P2 concentration estimate into the full-divisor
lower bound required by `AGPProgressionAuxiliaryData`.
-/
theorem p2_full_divisor_coefficient_bound_of_boxed {B M c₀ x : ℝ} {q t J h : ℕ} (hc₀ : 0 < c₀)
    (hx : 1 < x) (hM : 0 ≤ M) (hBM : B ≤ M)
    (hscale : 2 * Real.log x ≤ 10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ))
    (hbox :
      10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) * M <
        c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)))
    (hhalf : Nat.floor ((t : ℝ) / 2) ≤ h) : B < c₀ * (2 : ℝ) ^ h / (2 * Real.log x) := by
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hpow : (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) ≤ 2 ^ h := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hhalf)
  apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 2) hlogx)).2
  calc
    B * (2 * Real.log x) = (2 * Real.log x) * B := by ring
    _ ≤ (2 * Real.log x) * M :=
      mul_le_mul_of_nonneg_left hBM (le_of_lt (mul_pos (by norm_num only : (0 : ℝ) < 2) hlogx))
    _ ≤ (10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ)) * M :=
      mul_le_mul_of_nonneg_right hscale hM
    _ < c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)) := hbox
    _ ≤ c₀ * (2 : ℝ) ^ h := mul_le_mul_of_nonneg_left hpow (le_of_lt hc₀)

/--
Inputs: a squarefree auxiliary modulus `L`, a seed upper bound `q`, the scale
`X = (4 * q * L) ^ J`, and the boxed P2 concentration estimate.

Claim: if the floor term is bounded by `q ^ 2 * t * log q` and
`floor(t / 2)` is at most the number of prime factors of `L`, then the P2
left side is strictly below the Proposition 1.5 coefficient times all
restricted divisors of `L` at the cutoff for `X ^ 5`.

Proof: apply `p2_full_divisor_coefficient_bound_of_boxed`, then identify the
restricted-divisor count with the full squarefree divisor count.

Role: supplies the `hlower` field for the new full-divisor auxiliary-data
construction once the seed estimates are available.
-/
theorem p2_full_divisor_hlower_of_boxed {W : Finset ℕ} {L q X t J : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hq : 2 ≤ q) (hx : 2 ≤ X ^ 5) (hL : 0 < L) (hSquarefree : Squarefree L) (hLbound : L ≤ X ^ 2)
    (hfloor :
      (Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) : ℝ) ≤
        (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ))
    (hscale : 2 * Real.log ((X ^ 5 : ℕ) : ℝ) ≤ 10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ))
    (hbox :
      10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
          ((2 : ℝ) ^ W.card * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
        c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2)))
    (hhalf : Nat.floor ((t : ℝ) / 2) ≤ L.primeFactors.card) :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
        ℝ) <
      reliableProp15Coefficient c₀ 4 (X ^ 5) *
        ((restrictedDivisors L (reliableProp15DivisorCutoff (X ^ 5))).card : ℝ) := by
  have hfloorCast := hfloor
  have hBmajorant :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
        ℝ) ≤
      (2 : ℝ) ^ W.card * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc] using
      add_le_add
        (mul_le_mul_of_nonneg_left hfloorCast (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) W.card))
        (show (q : ℝ) ≤ (q : ℝ) from le_rfl)
  have hXpos : 0 < X := by
    by_contra hX
    have hXzero : X = 0 := Nat.eq_zero_of_not_pos hX
    subst X
    norm_num at hx
  have hxNat : 1 < X ^ 5 := by omega
  have hxReal : (1 : ℝ) < ((X ^ 5 : ℕ) : ℝ) := by exact_mod_cast hxNat
  have hnumeric :=
    p2_full_divisor_coefficient_bound_of_boxed hc₀ hxReal
      (by positivity : 0 ≤ (2 : ℝ) ^ W.card * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ))
      hBmajorant hscale hbox hhalf
  have hLne : L ≠ 0 := Nat.ne_of_gt hL
  have hfull :=
    restrictedDivisors_card_eq_full_at_fifth_power (X := X) (L := L) hXpos hLne hSquarefree hLbound
  have hlogx : 0 < Real.log ((X ^ 5 : ℕ) : ℝ) := Real.log_pos hxReal
  have htotient : Nat.totient 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only,
      Nat.totient_prime_pow Nat.prime_two (by norm_num only : 0 < (2 : ℕ))]
    norm_num only
  have hcoeff : reliableProp15Coefficient c₀ 4 (X ^ 5) = c₀ / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) := by
    unfold reliableProp15Coefficient
    rw [htotient]
    norm_num only [Nat.cast_ofNat]
  rw [hfull, hcoeff]
  calc
    (((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
          ℝ)) <
        c₀ * (2 : ℝ) ^ L.primeFactors.card / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) :=
      hnumeric
    _ = c₀ / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) * ((2 ^ L.primeFactors.card : ℕ) : ℝ) := by
      calc
        _ = c₀ / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) * (2 : ℝ) ^ L.primeFactors.card := by ring
        _ = c₀ / (2 * Real.log ((X ^ 5 : ℕ) : ℝ)) * ((2 ^ L.primeFactors.card : ℕ) : ℝ) := by
          congr 1
          simp only [Nat.cast_pow, Nat.cast_ofNat]

/--
Inputs: a prime bound `q ≥ 2`, a modulus `L > 1`, and the seed bounds
`L ≤ q ^ t` and `λ(L) ≤ q ^ 2`.

Claim: the floor term in the P2 threshold is at most `q ^ 2 * t * log q`.

Proof: specialize the existing auxiliary-size floor estimate with the
zero-fold factor `2 ^ 0 = 1` and exponent parameter `t - 1` only through the
equivalent bound `L ≤ q ^ ((t - 1) + 1)`.

Role: supplies the floor-majorant input of
`p2_full_divisor_hlower_of_boxed` directly from the tail modulus estimates.
-/
theorem p2_full_divisor_floor_term_bound {L q t : ℕ} (hq : 2 ≤ q) (hL : 1 < L) (ht : 0 < t)
    (hLbound : L ≤ q ^ t) (hLambda : ArithmeticFunction.carmichael L ≤ q ^ 2) :
    (Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) : ℝ) ≤
      (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) := by
  have hLbound' : L ≤ q ^ ((t - 1) + 1) := by
    rw [Nat.sub_add_cancel ht]
    exact hLbound
  have h := p2_floor_term_upper_bound_of_auxiliary_size_bounds (w := 0) hq hL hLbound' hLambda
  simpa only [pow_zero, Nat.cast_ofNat, one_mul, Nat.cast_pow, Nat.sub_add_cancel ht] using h

/--
Inputs: `q ≥ 2`, a positive modulus `L ≤ q ^ t`, a positive exponent `J`,
and the full-divisor scale `X = (4 * q * L) ^ J`.

Claim: with `x = X ^ 5`, its logarithm satisfies
`2 * log x ≤ 10 * J * (t + 3) * log q`.

Proof: bound `4 * q * L` by `q ^ (t + 3)`, take logarithms, and use the
definition of `X`.

Role: supplies the logarithmic scale comparison used by
`p2_full_divisor_hlower_of_boxed`.
-/
theorem full_divisor_scale_log_bound {q L X t J : ℕ} (hq : 2 ≤ q) (hL : 0 < L) (hLbound : L ≤ q ^ t)
    (hX : X = (4 * q * L) ^ J) :
    2 * Real.log ((X ^ 5 : ℕ) : ℝ) ≤ 10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) := by
  have hqreal : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hq)
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
  have hfour : 4 ≤ q ^ 2 := by nlinarith only [hq]
  have hbase : 4 * q * L ≤ q ^ (t + 3) := by
    have hinner : q * L ≤ q * q ^ t := Nat.mul_le_mul_left q hLbound
    have hprod := Nat.mul_le_mul hfour hinner
    have hexp : t + 3 = 2 + 1 + t := by omega
    rw [hexp, pow_add, pow_add]
    norm_num only [pow_one]
    calc
      4 * q * L ≤ q ^ 2 * (q * q ^ t) := by simpa only [Nat.mul_assoc] using hprod
      _ = q ^ 2 * q * q ^ t := by rw [Nat.mul_assoc]
  have hbasePos : 0 < 4 * q * L := Nat.mul_pos (Nat.mul_pos (by norm_num only) (by omega)) hL
  have hlogbase : Real.log ((4 * q * L : ℕ) : ℝ) ≤ ((t + 3 : ℕ) : ℝ) * Real.log (q : ℝ) := by
    calc
      Real.log ((4 * q * L : ℕ) : ℝ) ≤ Real.log ((q ^ (t + 3) : ℕ) : ℝ) := by
        apply Real.log_le_log (by exact_mod_cast hbasePos)
        exact_mod_cast hbase
      _ = ((t + 3 : ℕ) : ℝ) * Real.log (q : ℝ) := by rw [Nat.cast_pow, Real.log_pow]
  have hxpow : X ^ 5 = (4 * q * L) ^ (5 * J) := by
    rw [hX]
    calc
      ((4 * q * L) ^ J) ^ 5 = (4 * q * L) ^ (J * 5) := by rw [Nat.pow_mul]
      _ = (4 * q * L) ^ (5 * J) := by
        congr 1; omega
  have hlogx : Real.log ((X ^ 5 : ℕ) : ℝ) = (5 * (J : ℝ)) * Real.log ((4 * q * L : ℕ) : ℝ) := by
    rw [hxpow, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  rw [hlogx]
  calc
    2 * ((5 : ℝ) * (J : ℝ) * Real.log ((4 * q * L : ℕ) : ℝ)) ≤
        2 * ((5 : ℝ) * (J : ℝ) * (((t + 3 : ℕ) : ℝ) * Real.log (q : ℝ))) :=
      by
      exact
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hlogbase
            (mul_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le J)))
          (by norm_num only)
    _ = 10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_ofNat]
      ring

/--
Inputs: a finite base set, a squarefree tail modulus `L`, seed parameters
`q,t`, and the tail estimates from the first-stage construction, including
the exact seed size and the surviving tail cardinality.

Claim: these data construct `AGPProgressionAuxiliaryData` using the full
restricted-divisor set at the scale `X = (4 * q * L) ^ J`.

Proof: obtain `L ≤ X ^ 2` and the range bound for prime factors from
`fullDivisorScale_arithmetic_bounds`; derive the tail factor-count bound,
floor and logarithmic majorants, then apply
`p2_full_divisor_hlower_of_boxed`.

Role: this is the separate full-divisor auxiliary-data constructor for the
large-scale AGP route.
-/
noncomputable def progressionAuxiliaryData_of_full_divisor_seed {W S : Finset ℕ}
    {C x₀ L q X t J : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hq : 2 ≤ q) (hL : 2 < L) (ht : 0 < t) (hJ : 0 < J)
    (hX : X = (4 * q * L) ^ J) (hLargeEnough : x₀ ≤ X ^ 5)
    (hProp15Input : ReliableProp15ModFourInput L (X ^ 5))
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ))
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) (hScard : S.card = t)
    (hLprimeFactors : L.primeFactors = S.filter (fun p => C * S.card < p))
    (hTailCard : S.card ≤ 2 * (S.filter (fun p => C * S.card < p)).card) (hLbound : L ≤ q ^ t)
    (hLambdaBound : ArithmeticFunction.carmichael L ≤ q ^ 2)
    (hbox :
      10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
          ((2 : ℝ) ^ W.card * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
        c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2))) :
    AGPProgressionAuxiliaryData W C c₀ x₀ := by
  have hLpos : 0 < L := lt_trans (by norm_num only : 0 < 2) hL
  have hXbounds := fullDivisorScale_arithmetic_bounds q L J (by omega : 0 < q) hLpos hJ
  have hXpos : 0 < X := by
    rw [hX]; positivity
  have hx : 2 ≤ X ^ 5 := by
    calc
      2 ≤ q := hq
      _ ≤ X := by
        rw [hX]; exact hXbounds.1
      _ ≤ X ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) X
  have hfloor := p2_full_divisor_floor_term_bound hq (by omega : 1 < L) ht hLbound hLambdaBound
  have hscale := full_divisor_scale_log_bound hq hLpos hLbound hX
  have hhalf := seed_tail_prime_factor_floor_half hScard hLprimeFactors hTailCard
  have hlower :=
    p2_full_divisor_hlower_of_boxed hc₀ hq hx hLpos hProp15Input.1
      (by simpa only [hX] using hXbounds.2.1) hfloor hscale hbox hhalf
  exact
    { L := L
      q := q
      x := X ^ 5
      hL := hL
      hLargeEnough := hLargeEnough
      hProp15Input := hProp15Input
      hReciprocal1024 := hReciprocal1024
      hCq := hCq
      hfactor := hfactor
      hlambda := hlambda
      hlower := hlower }

/--
Inputs: a finite base set, a squarefree tail modulus, a prime-factor cutoff `R`,
and the P2 scale and count bounds.

Claim: these data construct `AGPProgressionAuxiliaryData W C c₀ x₀`, while the
tail modulus is formed using the independent threshold `R * S.card`.

Proof: use the same full-divisor scale estimates as
`progressionAuxiliaryData_of_full_divisor_seed`; only the tail cardinality
estimate depends on `R`.

Role: decouples the finite-base bound in the output interface from the fixed
cutoff used to make the reciprocal prime-factor sum small.
-/
noncomputable def progressionAuxiliaryData_of_full_divisor_seed_with_cutoff {W S : Finset ℕ}
    {C R x₀ L q X t J : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hq : 2 ≤ q) (hL : 2 < L) (ht : 0 < t)
    (hJ : 0 < J) (hX : X = (4 * q * L) ^ J) (hLargeEnough : x₀ ≤ X ^ 5)
    (hProp15Input : ReliableProp15ModFourInput L (X ^ 5))
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ))
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) (hScard : S.card = t)
    (hLprimeFactors : L.primeFactors = S.filter (fun p => R * S.card < p))
    (hTailCard : S.card ≤ 2 * (S.filter (fun p => R * S.card < p)).card) (hLbound : L ≤ q ^ t)
    (hLambdaBound : ArithmeticFunction.carmichael L ≤ q ^ 2)
    (hbox :
      10 * (J : ℝ) * ((t : ℝ) + 3) * Real.log (q : ℝ) *
          ((2 : ℝ) ^ W.card * (q : ℝ) ^ 2 * (t : ℝ) * Real.log (q : ℝ) + (q : ℝ)) <
        c₀ * (2 : ℝ) ^ (Nat.floor ((t : ℝ) / 2))) :
    AGPProgressionAuxiliaryData W C c₀ x₀ := by
  have hLpos : 0 < L := lt_trans (by norm_num only : 0 < 2) hL
  have hXbounds := fullDivisorScale_arithmetic_bounds q L J (by omega : 0 < q) hLpos hJ
  have hXpos : 0 < X := by
    rw [hX]; positivity
  have hx : 2 ≤ X ^ 5 := by
    calc
      2 ≤ q := hq
      _ ≤ X := by
        rw [hX]; exact hXbounds.1
      _ ≤ X ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) X
  have hfloor := p2_full_divisor_floor_term_bound hq (by omega : 1 < L) ht hLbound hLambdaBound
  have hscale := full_divisor_scale_log_bound hq hLpos hLbound hX
  have hhalf := seed_tail_prime_factor_floor_half hScard hLprimeFactors hTailCard
  have hlower :=
    p2_full_divisor_hlower_of_boxed hc₀ hq hx hLpos hProp15Input.1
      (by simpa only [hX] using hXbounds.2.1) hfloor hscale hbox hhalf
  exact
    { L := L
      q := q
      x := X ^ 5
      hL := hL
      hLargeEnough := hLargeEnough
      hProp15Input := hProp15Input
      hReciprocal1024 := hReciprocal1024
      hCq := hCq
      hfactor := hfactor
      hlambda := hlambda
      hlower := hlower }

/--
Inputs: the seed factor-count bounds, a prime bound `q ≥ 2`, and a P2 count
estimate evaluated at `x = q ^ (5 * s)`.

Claim: these inputs produce the second-stage AGP progression auxiliary data.

Proof: the explicit fifth-power choice gives both `x ≥ 2` and the divisor
cutoff condition; the seed-count constructor then supplies the data.

Role: this packages the cutoff choice with the finite P2 construction so that
the remaining analytic work is concentrated in the displayed count estimate.
-/
noncomputable def progressionAuxiliaryData_of_seed_factor_count_lower_bound_fifth_power
    {W : Finset ℕ} {C x₀ L q s T : ℕ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hq : 2 ≤ q) (hL : 2 < L)
    (hLargeEnough : x₀ ≤ q ^ (5 * s)) (hProp15Input : ReliableProp15ModFourInput L (q ^ (5 * s)))
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ))
    (hCq : max C (W.sup id) ≤ q) (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ q)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L)
    (hFactorCount : (T + 1) / 2 ≤ L.primeFactors.card) (hs : 0 < s) (hscale : 4 * s ≤ T + 1)
    (hlower :
      ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + q : ℕ) :
          ℝ) <
        reliableProp15Coefficient c₀ 4 (q ^ (5 * s)) * ((T : ℝ) / (4 * (s : ℝ))) ^ s) :
    AGPProgressionAuxiliaryData W C c₀ x₀ := by
  let x : ℕ := q ^ (5 * s)
  have hx : 2 ≤ x := by
    dsimp [x]
    exact le_trans hq (Nat.le_self_pow (by omega) q)
  have hcut : q ^ s ≤ reliableProp15DivisorCutoff x := by
    dsimp [x]
    exact pow_le_reliableProp15DivisorCutoff_fifth_power (by omega)
  exact
    progressionAuxiliaryData_of_seed_factor_count_lower_bound hc₀ hx hL hLargeEnough hProp15Input
      hReciprocal1024 hCq hfactor hlambda hcut hFactorCount hs hscale hlower

/--
Inputs: a positive Proposition 1.5 coefficient `c₀`, a prime cutoff `q`, a
fixed-factor size `s`, and a base lower bound `b ≤ T / (4 * s)`.

Claim: for the fifth-power cutoff `x = q ^ (5 * s)`, the reliable coefficient
times the fixed-factor count is at least
`c₀ / (10 * s * log q) * b ^ s`.

Proof: evaluate `φ(4) = 2` and `log(q^(5s)) = 5s log q`, then use monotonicity
of the `s`-th power.

Role: this turns the improved seed ratio into the explicit lower side of the
remaining P2 parameter comparison.
-/
theorem p2_fixed_factor_lower_bound_of_fifth_power_cutoff {c₀ : ℝ} {q s T : ℕ} {b : ℝ}
    (hc₀ : 0 < c₀) (hq : 2 ≤ q) (hs : 0 < s) (hb : 0 < b) (hbase : b ≤ (T : ℝ) / (4 * (s : ℝ))) :
    c₀ / (10 * (s : ℝ) * Real.log (q : ℝ)) * b ^ s ≤
      reliableProp15Coefficient c₀ 4 (q ^ (5 * s)) * ((T : ℝ) / (4 * (s : ℝ))) ^ s := by
  have hqreal : (1 : ℝ) < (q : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : 1 < 2) hq)
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos hqreal
  have htotient : Nat.totient 4 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num only,
      Nat.totient_prime_pow Nat.prime_two (by norm_num only : 0 < (2 : ℕ))]
    norm_num only
  have hlogpow : Real.log ((q ^ (5 * s) : ℕ) : ℝ) = 5 * (s : ℝ) * Real.log (q : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  have hcoef :
    reliableProp15Coefficient c₀ 4 (q ^ (5 * s)) = c₀ / (10 * (s : ℝ) * Real.log (q : ℝ)) := by
    unfold reliableProp15Coefficient
    rw [htotient, hlogpow]
    ring
  have hpow : b ^ s ≤ ((T : ℝ) / (4 * (s : ℝ))) ^ s := pow_le_pow_left₀ hb.le hbase s
  rw [hcoef]
  exact
    mul_le_mul_of_nonneg_left hpow
      (div_nonneg (le_of_lt hc₀)
        (le_of_lt
          (mul_pos
            (mul_pos (by norm_num only : (0 : ℝ) < 10) (by exact_mod_cast Nat.zero_lt_of_lt hs))
            hlog)))

/--
Inputs: a seed scale `z = 2 ^ m`, bounds on the primorial size and seed count,
and the fixed-factor ratio produced by the first construction.

Claim: the explicit P2 upper bound is eventually smaller than the fifth-power
cutoff coefficient times the fixed-factor count.

Proof: bound the primorial and logarithmic factors by powers of two in `z*m`;
the ratio hypothesis gives a base of at least `2 ^ 64` for the matching power.

Role: this closes the finite parameter comparison needed by the second
application of reliable Proposition 1.5.
-/
theorem p2_fixed_factor_seed_scale_comparison {m z T N w : ℕ} {c₀ : ℝ} (hm : 10 ≤ m)
    (hz : z = 2 ^ m) (hNlower : z ^ 3 ≤ N) (hNupper : N ≤ z ^ (z + 1)) (hTupper : T + 1 ≤ z ^ 3)
    (hw : w ≤ z * m) (hcscale : 1 ≤ c₀ * z) (hratio : 2 ^ 64 ≤ (T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) :
    (2 ^ w : ℝ) * (N ^ 5 : ℕ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) + (N ^ 5 : ℕ) <
      c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) *
        ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) := by
  have hcube := powTwo_ge_cube hm
  have hzge10 : 10 ≤ z := by
    rw [hz]
    exact Nat.le_trans hm (Nat.le_trans (Nat.le_self_pow (by norm_num only : 3 ≠ 0) m) hcube)
  have hNfive : N ^ 5 ≤ z ^ (10 * z) := by
    have hexp : 5 * (z + 1) ≤ 10 * z := by omega
    calc
      N ^ 5 ≤ (z ^ (z + 1)) ^ 5 := Nat.pow_le_pow_left hNupper 5
      _ = z ^ (5 * (z + 1)) := by rw [show 5 * (z + 1) = (z + 1) * 5 by omega, ← pow_mul]
      _ ≤ z ^ (10 * z) := Nat.pow_le_pow_right (by omega) hexp
  have hNfiveTwo : N ^ 5 ≤ 2 ^ (10 * z * m) := by
    calc
      N ^ 5 ≤ z ^ (10 * z) := hNfive
      _ = (z ^ 10) ^ z := by rw [pow_mul]
      _ = ((2 ^ m) ^ 10) ^ (2 ^ m) := by rw [hz]
      _ = (2 ^ (m * 10)) ^ (2 ^ m) := (pow_mul 2 m 10).symm ▸ rfl
      _ = 2 ^ ((m * 10) * (2 ^ m)) := (pow_mul 2 (m * 10) (2 ^ m)).symm
      _ = 2 ^ (10 * z * m) := by
        rw [hz]; congr 1; ring
  have hzpos : 0 < z := by omega
  have hNpos : 0 < N := lt_of_lt_of_le (Nat.pow_pos hzpos) hNlower
  have hNge2 : 2 ≤ N := by
    calc
      2 ≤ z := by omega
      _ ≤ z ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) z
      _ ≤ N := hNlower
  have hNleNfive : N ≤ N ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
  have hxge2 : 2 ≤ N ^ 5 := le_trans hNge2 hNleNfive
  have hlogxpos : 0 < Real.log ((N ^ 5 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N ^ 5 by omega))
  have hlogz : Real.log (z : ℝ) ≤ (z : ℝ) := Real.log_le_self (by exact_mod_cast Nat.zero_le z)
  have hlogxupper : Real.log ((N ^ 5 : ℕ) : ℝ) ≤ (z : ℝ) ^ 3 := by
    have hNfivePos : 0 < (N ^ 5 : ℕ) := Nat.pow_pos hNpos
    have hNfivePosR : 0 < ((N ^ 5 : ℕ) : ℝ) := by exact_mod_cast hNfivePos
    have hNfiveR : ((N ^ 5 : ℕ) : ℝ) ≤ ((z ^ (10 * z) : ℕ) : ℝ) := by exact_mod_cast hNfive
    have hlogcomp := Real.log_le_log hNfivePosR hNfiveR
    have hlogcomp' : 5 * Real.log (N : ℝ) ≤ (10 * z : ℕ) * Real.log (z : ℝ) := by
      simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] using hlogcomp
    calc
      Real.log ((N ^ 5 : ℕ) : ℝ) ≤ 10 * (z : ℝ) * Real.log (z : ℝ) := by
        calc
          Real.log ((N ^ 5 : ℕ) : ℝ) = 5 * Real.log (N : ℝ) := by
            rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
          _ ≤ (10 * z : ℕ) * Real.log (z : ℝ) := hlogcomp'
          _ = 10 * (z : ℝ) * Real.log (z : ℝ) := by simp only [Nat.cast_mul, Nat.cast_ofNat]
      _ ≤ 10 * (z : ℝ) ^ 2 :=
        calc
          10 * (z : ℝ) * Real.log (z : ℝ) ≤ 10 * (z : ℝ) * (z : ℝ) :=
            mul_le_mul_of_nonneg_left hlogz (by positivity)
          _ = 10 * (z : ℝ) ^ 2 := by ring
      _ ≤ (z : ℝ) ^ 3 := by
        have hmul :=
          mul_le_mul_of_nonneg_right (show (10 : ℝ) ≤ z by exact_mod_cast hzge10)
            (sq_nonneg (z : ℝ))
        nlinarith only [hmul]
  let s : ℕ := z * m
  have hspos : 0 < s := by
    dsimp [s]
    exact Nat.mul_pos hzpos (Nat.lt_of_lt_of_le (by omega) hm)
  have hmleS : m ≤ s := by
    dsimp [s]
    have hmul := Nat.mul_le_mul_left m (show 1 ≤ z by omega)
    calc
      m = m * 1 := by rw [Nat.mul_one]
      _ ≤ m * z := hmul
      _ = z * m := Nat.mul_comm m z
  have hNexp : N ^ 5 ≤ 2 ^ (10 * s) := by simpa only [s, Nat.mul_assoc] using hNfiveTwo
  have hTexp : T + 1 ≤ 2 ^ (3 * s) := by
    calc
      T + 1 ≤ z ^ 3 := hTupper
      _ = 2 ^ (m * 3) := by
        rw [hz]; exact (pow_mul 2 m 3).symm
      _ ≤ 2 ^ (3 * s) := by
        apply Nat.pow_le_pow_right (by norm_num only : 0 < 2)
        have hmul := Nat.mul_le_mul_left 3 hmleS
        simpa only [s, Nat.mul_comm m 3] using hmul
  have hlogxleX : Real.log ((N ^ 5 : ℕ) : ℝ) ≤ (N ^ 5 : ℕ) :=
    Real.log_le_self (by exact_mod_cast Nat.zero_le (N ^ 5))
  have hsge10 : 10 ≤ s := by
    dsimp [s]
    exact Nat.le_trans (by norm_num only : 10 ≤ 10 * 10) (Nat.mul_le_mul hzge10 hm)
  have hslePow : s ≤ 2 ^ s := Nat.le_of_lt (Nat.lt_two_pow_self (n := s))
  have h10lePow : 10 ≤ 2 ^ s := by
    calc
      10 ≤ 2 ^ 4 := by norm_num only
      _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num only : 0 < 2) (by omega)
  have h10sPow : 10 * s ≤ 2 ^ (2 * s) := by
    calc
      10 * s ≤ 2 ^ s * s := Nat.mul_le_mul_right s h10lePow
      _ ≤ 2 ^ s * 2 ^ s := Nat.mul_le_mul_left (2 ^ s) hslePow
      _ = 2 ^ (s + s) := by rw [← pow_add]
      _ = 2 ^ (2 * s) := by
        congr 1; omega
  have hwS : w ≤ s := by simpa only [s] using hw
  have hWexp : (2 ^ w : ℝ) ≤ 2 ^ s := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num only : 0 < 2) hwS)
  have hNexpR : (N ^ 5 : ℝ) ≤ 2 ^ (10 * s) := by exact_mod_cast hNexp
  have hNexpSq : (N ^ 5 : ℝ) ^ 2 ≤ 2 ^ (20 * s) := by
    have hmul := mul_le_mul hNexpR hNexpR (by positivity) (by positivity)
    calc
      (N ^ 5 : ℝ) ^ 2 ≤ 2 ^ (10 * s) * 2 ^ (10 * s) := by simpa only [pow_two] using hmul
      _ = 2 ^ (20 * s) := by rw [show 20 * s = 10 * s + 10 * s by omega, ← pow_add]
  have hTexpR : ((T + 1 : ℕ) : ℝ) ≤ 2 ^ (3 * s) := by
    have hcast : ((T + 1 : ℕ) : ℝ) ≤ (2 ^ (3 * s) : ℕ) := Nat.cast_le.mpr hTexp
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hcast
  have hNexpCast : ((N ^ 5 : ℕ) : ℝ) ≤ 2 ^ (10 * s) := by simpa only [Nat.cast_pow] using hNexpR
  have hlogxexp : Real.log ((N ^ 5 : ℕ) : ℝ) ≤ 2 ^ (10 * s) := le_trans hlogxleX hNexpCast
  have h10sPowR : 10 * (s : ℝ) ≤ 2 ^ (2 * s) := by exact_mod_cast h10sPow
  have hdenUpper : 10 * (s : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) ≤ 2 ^ (12 * s) := by
    calc
      10 * (s : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) ≤ 10 * (s : ℝ) * 2 ^ (10 * s) :=
        mul_le_mul_of_nonneg_left hlogxexp (by positivity)
      _ ≤ 2 ^ (2 * s) * 2 ^ (10 * s) := mul_le_mul_of_nonneg_right h10sPowR (by positivity)
      _ = 2 ^ (12 * s) := by rw [show 12 * s = 2 * s + 10 * s by omega, ← pow_add]
  have hzlePowS : z ≤ 2 ^ s := by
    rw [hz]
    exact Nat.pow_le_pow_right (by norm_num only : 0 < 2) hmleS
  have hc₀overZ : 1 / (z : ℝ) ≤ c₀ := by
    apply (div_le_iff₀ (by exact_mod_cast hzpos)).2
    simpa only [one_mul] using hcscale
  have hdenPos : 0 < 10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) := by
    exact mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 10) (by exact_mod_cast hspos)) hlogxpos
  have hdenUpper' : 10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) ≤ 2 ^ (12 * s) := by
    simpa only [s] using hdenUpper
  have hdenTimesZ : (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) * z ≤ 2 ^ (13 * s) := by
    calc
      (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) * z ≤ 2 ^ (12 * s) * z :=
        mul_le_mul_of_nonneg_right hdenUpper' (by positivity)
      _ ≤ 2 ^ (12 * s) * 2 ^ s :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hzlePowS) (by positivity)
      _ = 2 ^ (13 * s) := by rw [show 13 * s = 12 * s + s by omega, ← pow_add]
  have hdenScaled : 2 ^ (13 * s) ≤ (c₀ * 2 ^ (13 * s)) * z := by
    calc
      2 ^ (13 * s) = 1 * 2 ^ (13 * s) := by ring
      _ ≤ (c₀ * z) * 2 ^ (13 * s) := mul_le_mul_of_nonneg_right hcscale (by positivity)
      _ = (c₀ * 2 ^ (13 * s)) * z := by ring
  have hdenCross : 10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) ≤ c₀ * 2 ^ (13 * s) := by
    apply (le_of_mul_le_mul_right (le_trans hdenTimesZ hdenScaled))
    exact_mod_cast hzpos
  have hcoefficient :
    1 / (2 ^ (13 * s) : ℝ) ≤ c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) := by
    apply (div_le_div_iff₀ (by positivity) hdenPos).2
    simpa only [one_mul] using hdenCross
  have hratioS : 2 ^ 64 ≤ (T : ℝ) / (4 * (s : ℝ)) := by simpa only [s] using hratio
  have hbasePow : (2 : ℝ) ^ (64 * s) ≤ ((T : ℝ) / (4 * (s : ℝ))) ^ s := by
    calc
      (2 : ℝ) ^ (64 * s) = ((2 : ℝ) ^ 64) ^ s := pow_mul (2 : ℝ) 64 s
      _ ≤ ((T : ℝ) / (4 * (s : ℝ))) ^ s := pow_le_pow_left₀ (by positivity) hratioS s
  have hreciprocalPower' : (2 : ℝ) ^ (50 * s) ≤ 2 ^ (64 * s) / 2 ^ (13 * s) := by
    apply (le_div_iff₀ (by positivity)).2
    calc
      (2 : ℝ) ^ (50 * s) * 2 ^ (13 * s) = 2 ^ (63 * s) := by
        rw [← pow_add, show 50 * s + 13 * s = 63 * s by omega]
      _ ≤ 2 ^ (64 * s) := by
        exact_mod_cast (Nat.pow_le_pow_right (by norm_num only : 0 < 2) (by omega))
  have hreciprocalPower : (2 : ℝ) ^ (50 * s) ≤ 1 / (2 ^ (13 * s) : ℝ) * 2 ^ (64 * s) := by
    calc
      (2 : ℝ) ^ (50 * s) ≤ 2 ^ (64 * s) / 2 ^ (13 * s) := hreciprocalPower'
      _ = 1 / (2 ^ (13 * s) : ℝ) * 2 ^ (64 * s) := by
        rw [div_eq_mul_inv, one_div]; ring
  have hc₀pos : 0 < c₀ := lt_of_lt_of_le (by positivity) hc₀overZ
  have hcoefficientPos : 0 < c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) :=
    div_pos hc₀pos hdenPos
  have hlargeFactor :
    (2 : ℝ) ^ (50 * s) ≤
      c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) *
        ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) := by
    have hproduct := mul_le_mul_of_nonneg_left hbasePow (le_of_lt hcoefficientPos)
    have hproduct' :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity : 0 ≤ (2 : ℝ) ^ (64 * s))
    calc
      (2 : ℝ) ^ (50 * s) ≤ 1 / (2 ^ (13 * s) : ℝ) * 2 ^ (64 * s) := hreciprocalPower
      _ ≤ c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) * 2 ^ (64 * s) := hproduct'
      _ ≤
          c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) *
            ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) :=
        by exact hproduct
  have hpow34 :
    (2 : ℝ) ^ w * (N ^ 5 : ℝ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (34 * s) := by
    have hAB := mul_le_mul hWexp hNexpSq (by positivity) (by positivity)
    have hABC := mul_le_mul hAB hTexpR (by positivity) (by positivity)
    have hABCD := mul_le_mul hABC hlogxexp (by positivity) (by positivity)
    calc
      (2 : ℝ) ^ w * (N ^ 5 : ℝ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) ≤
          (2 : ℝ) ^ s * 2 ^ (20 * s) * 2 ^ (3 * s) * 2 ^ (10 * s) :=
        hABCD
      _ = 2 ^ (34 * s) := by
        calc
          (2 : ℝ) ^ s * 2 ^ (20 * s) * 2 ^ (3 * s) * 2 ^ (10 * s) =
              2 ^ (s + 20 * s + 3 * s + 10 * s) :=
            by rw [← pow_add, ← pow_add, ← pow_add]
          _ = 2 ^ (34 * s) := by
            congr 1; omega
  have hNexp34 : (N ^ 5 : ℕ) ≤ 2 ^ (34 * s) := by
    have hpow : 2 ^ (10 * s) ≤ 2 ^ (34 * s) :=
      Nat.pow_le_pow_right (by norm_num only : 0 < 2) (by omega)
    exact le_trans hNexp (by exact hpow)
  have hNexp34R : ((N ^ 5 : ℕ) : ℝ) ≤ 2 ^ (34 * s) := by exact_mod_cast hNexp34
  have hsumUpper :
    (2 : ℝ) ^ w * (N ^ 5 : ℕ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) + (N ^ 5 : ℕ) ≤
      (2 : ℝ) ^ (35 * s) := by
    have hsum := add_le_add hpow34 hNexp34R
    have hsum' :
      (2 : ℝ) ^ w * (N ^ 5 : ℕ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) + (N ^ 5 : ℕ) ≤
        2 ^ (34 * s) + 2 ^ (34 * s) := by
      simpa only [Nat.cast_pow] using hsum
    have hdouble : (2 : ℝ) ^ (34 * s) + 2 ^ (34 * s) ≤ (2 : ℝ) ^ (35 * s) := by
      calc
        (2 : ℝ) ^ (34 * s) + 2 ^ (34 * s) = 2 ^ (34 * s + 1) := by
          calc
            (2 : ℝ) ^ (34 * s) + 2 ^ (34 * s) = (2 : ℝ) ^ (34 * s) * (2 : ℝ) := by ring
            _ = 2 ^ (34 * s + 1) := by rw [pow_succ]
        _ ≤ 2 ^ (35 * s) := by
          exact_mod_cast (Nat.pow_le_pow_right (by norm_num only : 0 < 2) (by omega))
    exact le_trans hsum' hdouble
  have hstrictPower : (2 : ℝ) ^ (35 * s) < (2 : ℝ) ^ (50 * s) := by
    exact_mod_cast (Nat.pow_lt_pow_right (by norm_num only : 1 < 2) (by omega))
  calc
    (2 ^ w : ℝ) * (N ^ 5 : ℕ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) + (N ^ 5 : ℕ) ≤
        (2 : ℝ) ^ (35 * s) :=
      hsumUpper
    _ < (2 : ℝ) ^ (50 * s) := hstrictPower
    _ ≤
        c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) *
          ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) :=
      hlargeFactor

/-
Inputs: a positive scale `c₀`, an integer `m ≥ 1`, and `m^3 ≤ z`.

Claim: the explicit lower seed scale `c₀ z / (160 m^2 log 2)` is at least
`c₀ m / (160 log 2)`.

Proof: substitute the cubic lower bound for `z` and use positivity of the
common denominator.

Role: this extracts the growth in `m` from the ratio returned by the seed
construction, for the later choice of the P2 comparison threshold.
-/
theorem p2_seed_ratio_lower_bound_of_cubic_scale {c₀ : ℝ} {m z : ℕ} (hc₀ : 0 < c₀) (hm : 1 ≤ m)
    (hz : m ^ 3 ≤ z) :
    c₀ * (m : ℝ) / (160 * Real.log 2) ≤ c₀ * (z : ℝ) / (160 * (m : ℝ) ^ 2 * Real.log 2) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hcubeR : (m : ℝ) ^ 3 ≤ (z : ℝ) := by exact_mod_cast hz
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 1) hm)
  have hden1 : 0 < 160 * Real.log 2 := mul_pos (by norm_num only : (0 : ℝ) < 160) hlog2
  have hden2 : 0 < 160 * (m : ℝ) ^ 2 * Real.log 2 :=
    mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 160) (sq_pos_of_pos hmR)) hlog2
  have hcz : c₀ * (m : ℝ) ^ 3 ≤ c₀ * (z : ℝ) := mul_le_mul_of_nonneg_left hcubeR (le_of_lt hc₀)
  apply (div_le_div_iff₀ hden1 hden2).2
  calc
    c₀ * (m : ℝ) * (160 * (m : ℝ) ^ 2 * Real.log 2) = (c₀ * (m : ℝ) ^ 3) * (160 * Real.log 2) := by
      ring
    _ ≤ (c₀ * (z : ℝ)) * (160 * Real.log 2) := mul_le_mul_of_nonneg_right hcz (le_of_lt hden1)
    _ = c₀ * (z : ℝ) * (160 * Real.log 2) := by ring

/--
Inputs: the seed parameter formula, a cubic lower bound `m ^ 3 ≤ z`, and a strict bound on
`c₀` relative to `m`.

Claim: the seed count satisfies `T + 1 ≤ z ^ 3`.

Content: the parameter bound makes the real number inside the floor strictly less than
`z ^ 3`; `Nat.floor_lt` then gives the required natural-number inequality.

Role: this supplies the size hypothesis for `p2_fixed_factor_seed_scale_comparison`.
-/
theorem p2_seed_count_succ_le_cube_of_parameter_bound {c₀ : ℝ} {m z T : ℕ} (hc₀ : 0 < c₀)
    (hm : 1 ≤ m) (hz : z = 2 ^ m) (hcubic : m ^ 3 ≤ z) (hparam : c₀ < 20 * Real.log 2 * (m : ℝ) ^ 4)
    (hT : T = Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2))) : T + 1 ≤ z ^ 3 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 1) hm)
  have hzR : 0 < (z : ℝ) := by
    rw [hz]
    exact_mod_cast (Nat.pow_pos (by norm_num only : 0 < 2))
  have hden : 0 < 20 * (m : ℝ) * Real.log 2 :=
    mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 20) hmpos) hlog2
  have harg : c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) < ((z ^ 3 : ℕ) : ℝ) := by
    have hparam' : c₀ / (20 * (m : ℝ) * Real.log 2) < (m : ℝ) ^ 3 := by
      apply (div_lt_iff₀ hden).2
      calc
        c₀ < 20 * Real.log 2 * (m : ℝ) ^ 4 := hparam
        _ = (m : ℝ) ^ 3 * (20 * (m : ℝ) * Real.log 2) := by ring
    have hcubicR : (m : ℝ) ^ 3 ≤ (z : ℝ) := by exact_mod_cast hcubic
    have hmul : (c₀ / (20 * (m : ℝ) * Real.log 2)) * (z : ℝ) ^ 2 < (m : ℝ) ^ 3 * (z : ℝ) ^ 2 :=
      mul_lt_mul_of_pos_right hparam' (sq_pos_of_pos hzR)
    calc
      c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) =
          (c₀ / (20 * (m : ℝ) * Real.log 2)) * (z : ℝ) ^ 2 :=
        by ring
      _ < (m : ℝ) ^ 3 * (z : ℝ) ^ 2 := hmul
      _ ≤ (z : ℝ) ^ 3 := by
        calc
          (m : ℝ) ^ 3 * (z : ℝ) ^ 2 ≤ (z : ℝ) * (z : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hcubicR (sq_nonneg (z : ℝ))
          _ = (z : ℝ) ^ 3 := by ring
      _ = ((z ^ 3 : ℕ) : ℝ) := by rw [Nat.cast_pow]
  have hfloor : Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2)) < z ^ 3 := by
    rw [Nat.floor_lt (le_of_lt (div_pos (mul_pos hc₀ (sq_pos_of_pos hzR)) hden))]
    exact harg
  rw [hT]
  omega

/--
Inputs: a positive coefficient, a finite positive-base set `W`, and fixed cutoffs `x₀` and `C`.

Claim: one scale `m` and `z = 2 ^ m` satisfy the seed, P2 comparison, and finite-set cutoffs.

Content: choose `m` beyond the natural cutoffs and the real thresholds for the seed ratio,
the floor bound, and `c₀ z ≥ 1`; the cubic power estimate then controls `W.card` and `C`.

Role: this common scale supplies the numerical hypotheses needed to apply the seed constructor
and the fixed-factor P2 comparison to the same parameters.
-/
theorem exists_p2_seed_common_scale {c₀ : ℝ} (hc₀ : 0 < c₀) (x₀ C : ℕ) (W : Finset ℕ) :
    ∃ m z : ℕ,
      10 ≤ m ∧
        x₀ ≤ m ∧
        z = 2 ^ m ∧
        m ^ 3 ≤ z ∧
        W.card ≤ m ∧
        max C (W.sup id) ≤ m ∧
        W.card ≤ z * m ∧
        max C (W.sup id) ≤ z ∧
        1 ≤ c₀ * z ∧ 2 ^ 64 * (160 * Real.log 2) ≤ c₀ * m ∧ c₀ < 20 * Real.log 2 * (m : ℝ) ^ 4 := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  let M : ℕ := max (max 10 x₀) (max W.card (max C (W.sup id)))
  have hM10 : 10 ≤ M := le_trans (le_max_left 10 x₀) (le_max_left (max 10 x₀) _)
  have hMx₀ : x₀ ≤ M := le_trans (le_max_right 10 x₀) (le_max_left (max 10 x₀) _)
  have hMW : W.card ≤ M := le_trans (le_max_left W.card _) (le_max_right (max 10 x₀) _)
  have hMC : C ≤ M :=
    le_trans (le_max_left C _) (le_trans (le_max_right W.card _) (le_max_right (max 10 x₀) _))
  have hMWsup : W.sup id ≤ M :=
    le_trans (le_max_right C _) (le_trans (le_max_right W.card _) (le_max_right (max 10 x₀) _))
  have hlogden : 0 < 20 * Real.log 2 := mul_pos (by norm_num only : (0 : ℝ) < 20) hlog2
  let K : ℝ := (2 : ℝ) ^ 64 * (160 * Real.log 2)
  let R : ℝ := max (max (M : ℝ) (K / c₀)) (max (c₀ / (20 * Real.log 2)) (1 / c₀))
  obtain ⟨m, hmR⟩ := exists_nat_gt R
  have hmR' : R < (m : ℝ) := by exact_mod_cast hmR
  have hMm : (M : ℝ) < (m : ℝ) :=
    lt_of_le_of_lt (le_trans (le_max_left (M : ℝ) (K / c₀)) (le_max_left _ _)) hmR'
  have hM10R : (10 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM10
  have hMx₀R : (x₀ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMx₀
  have hMWR : (W.card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMW
  have hMCR : (C : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMC
  have hMWsupR : ((W.sup id : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMWsup
  have hm10 : 10 ≤ m := by exact Nat.le_of_lt (by exact_mod_cast (lt_of_le_of_lt hM10R hMm))
  have hmx₀ : x₀ ≤ m := by exact Nat.le_of_lt (by exact_mod_cast (lt_of_le_of_lt hMx₀R hMm))
  have hmW : W.card ≤ m := by exact Nat.le_of_lt (by exact_mod_cast (lt_of_le_of_lt hMWR hMm))
  have hmC : C ≤ m := by exact Nat.le_of_lt (by exact_mod_cast (lt_of_le_of_lt hMCR hMm))
  have hmWsup : W.sup id ≤ m := by
    exact Nat.le_of_lt (by exact_mod_cast (lt_of_le_of_lt hMWsupR hMm))
  have hlinearR : K / c₀ < (m : ℝ) := by
    have hle : K / c₀ ≤ R := le_trans (le_max_right (M : ℝ) (K / c₀)) (le_max_left _ _)
    exact lt_of_le_of_lt hle hmR'
  have hlinear : K < c₀ * (m : ℝ) := by simpa only [K, mul_comm] using (div_lt_iff₀ hc₀).mp hlinearR
  have hparamR : c₀ / (20 * Real.log 2) < (m : ℝ) := by
    have hle : c₀ / (20 * Real.log 2) ≤ R := le_trans (le_max_left _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hle hmR'
  have hparamsmall : c₀ < 20 * Real.log 2 * (m : ℝ) := by
    simpa only [mul_comm] using (div_lt_iff₀ hlogden).mp hparamR
  have hmlePow : (m : ℝ) ≤ (m : ℝ) ^ 4 := by
    exact_mod_cast (Nat.le_self_pow (by norm_num only : 4 ≠ 0) m)
  have hparam : c₀ < 20 * Real.log 2 * (m : ℝ) ^ 4 :=
    lt_of_lt_of_le hparamsmall (mul_le_mul_of_nonneg_left hmlePow (le_of_lt hlogden))
  have hinvR : 1 / c₀ < (m : ℝ) := by
    have hle : 1 / c₀ ≤ R := le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hle hmR'
  have hinv : (1 : ℝ) < c₀ * (m : ℝ) := by simpa only [mul_comm] using (div_lt_iff₀ hc₀).mp hinvR
  let z : ℕ := 2 ^ m
  have hz : z = 2 ^ m := rfl
  have hcube := powTwo_ge_cube hm10
  have hmleCube : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) m
  have hmlez : m ≤ z := by
    rw [hz]; exact le_trans hmleCube hcube
  have hzpos : 1 ≤ z := by
    rw [hz]; exact Nat.one_le_pow m 2 (by norm_num only)
  have hmleZm : m ≤ z * m := by
    calc
      m = 1 * m := by rw [Nat.one_mul]
      _ ≤ z * m := Nat.mul_le_mul_right m hzpos
  have hWzm : W.card ≤ z * m := le_trans hmW hmleZm
  have hmaxMz : max C (W.sup id) ≤ z := max_le (le_trans hmC hmlez) (le_trans hmWsup hmlez)
  have hmaxMm : max C (W.sup id) ≤ m := max_le hmC hmWsup
  have hcz : 1 ≤ c₀ * (z : ℝ) := by
    have hmul : c₀ * (m : ℝ) ≤ c₀ * (z : ℝ) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hmlez) (le_of_lt hc₀)
    exact le_trans (le_of_lt hinv) hmul
  have hlinear' : (2 : ℝ) ^ 64 * (160 * Real.log 2) ≤ c₀ * (m : ℝ) := by exact le_of_lt hlinear
  refine ⟨m, z, hm10, hmx₀, hz, ?_, hmW, hmaxMm, hWzm, hmaxMz, hcz, ?_, hparam⟩
  · exact_mod_cast hcube
  · exact_mod_cast hlinear'

/--
Inputs: the P2 scale inequalities and the seed arithmetic bounds for an auxiliary modulus.

Claim: these data construct `AGPProgressionAuxiliaryData` for the finite base set and cutoff.

Content: the explicit P2 comparison dominates the floor-term upper bound; the fifth-power
coefficient estimate then transfers this strict inequality to the Proposition 1.5 coefficient.

Role: this connects the first-stage seed output to the finite P2 auxiliary-data interface.
-/
theorem progressionAuxiliaryData_of_p2_seed_scale {W : Finset ℕ} {C x₀ L N m z T : ℕ} {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hm : 10 ≤ m) (hz : z = 2 ^ m) (hNlower : z ^ 3 ≤ N) (hNupper : N ≤ z ^ (z + 1))
    (hTupper : T + 1 ≤ z ^ 3) (hw : W.card ≤ z * m) (hcscale : 1 ≤ c₀ * z)
    (hratio : 2 ^ 64 ≤ (T : ℝ) / (4 * ((z * m : ℕ) : ℝ)))
    (hLargeEnough : x₀ ≤ (N ^ 5) ^ (5 * (z * m)))
    (hReciprocal1024 : (∑ r ∈ L.primeFactors, (r : ℝ)⁻¹) ≤ (1 / 1024 : ℝ)) (hL : 2 < L)
    (hProp15Input : ReliableProp15ModFourInput L (N ^ 5)) (hCq : max C (W.sup id) ≤ N ^ 5)
    (hfactor : ∀ r, r ∣ L → Nat.Prime r → r ≤ N ^ 5) (hlambda : 3 ≤ ArithmeticFunction.carmichael L)
    (hFactorCount : (T + 1) / 2 ≤ L.primeFactors.card) (hLbound : L ≤ (N ^ 5) ^ (T + 1))
    (hLambdaBound : ArithmeticFunction.carmichael L ≤ (N ^ 5) ^ 2) (hscale : 4 * (z * m) ≤ T + 1) :
    ∃ X : ℕ,
      ∃ aux : AGPProgressionAuxiliaryData W C c₀ x₀, 2 ^ 56 ≤ X ∧ aux.x = X ^ 5 ∧ aux.q ≤ X := by
  have hcube : m ^ 3 ≤ z := by simpa only [hz] using powTwo_ge_cube hm
  have hmleCube : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) m
  have hmlez : m ≤ z := le_trans hmleCube hcube
  have hzge2 : 2 ≤ z := le_trans (by norm_num only : 2 ≤ 10) (le_trans hm hmlez)
  have hNge2 : 2 ≤ N :=
    le_trans hzge2 (le_trans (Nat.le_self_pow (by norm_num only : 3 ≠ 0) z) hNlower)
  have hq : 2 ≤ N ^ 5 := le_trans hNge2 (Nat.le_self_pow (by norm_num only : 5 ≠ 0) N)
  have hzpos : 0 < z := lt_of_lt_of_le (by norm_num only : 0 < 2) hzge2
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only) hm
  have hs : 0 < z * m := Nat.mul_pos hzpos hmpos
  have hbasepos : 0 < (T : ℝ) / (4 * ((z * m : ℕ) : ℝ)) :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2 ^ 64) hratio
  have hP2 := p2_fixed_factor_seed_scale_comparison hm hz hNlower hNupper hTupper hw hcscale hratio
  have hLone : 1 < L := lt_trans (by norm_num only : 1 < 2) hL
  have hfloor :=
    p2_floor_term_upper_bound_of_auxiliary_size_bounds (w := W.card) hq hLone hLbound hLambdaBound
  have hfloorAdd :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + N ^ 5 :
          ℕ) :
        ℝ) ≤
      (2 ^ W.card : ℝ) * ((N ^ 5 : ℕ) : ℝ) ^ 2 * ((T + 1 : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ) +
        ((N ^ 5 : ℕ) : ℝ) := by
    have hcastTwo : ((2 : ℕ) : ℝ) = 2 := by norm_num only
    have h := add_le_add hfloor (le_of_eq (show ((N ^ 5 : ℕ) : ℝ) = ((N ^ 5 : ℕ) : ℝ) from rfl))
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, hcastTwo] using h
  have hleft :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + N ^ 5 :
          ℕ) :
        ℝ) <
      c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) *
        ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) := by
    exact lt_of_le_of_lt hfloorAdd hP2
  have hcoeff :=
    p2_fixed_factor_lower_bound_of_fifth_power_cutoff hc₀ hq hs hbasepos
      (le_rfl : (T : ℝ) / (4 * ((z * m : ℕ) : ℝ)) ≤ (T : ℝ) / (4 * ((z * m : ℕ) : ℝ)))
  have hlower :
    ((2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log (L : ℝ)) + N ^ 5 :
          ℕ) :
        ℝ) <
      reliableProp15Coefficient c₀ 4 ((N ^ 5) ^ (5 * (z * m))) *
        ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) := by
    calc
      _ <
          c₀ / (10 * ((z * m : ℕ) : ℝ) * Real.log ((N ^ 5 : ℕ) : ℝ)) *
            ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) :=
        hleft
      _ ≤
          reliableProp15Coefficient c₀ 4 ((N ^ 5) ^ (5 * (z * m))) *
            ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) :=
        by simpa only [Nat.cast_mul] using hcoeff
  have hqle : N ^ 5 ≤ (N ^ 5) ^ (5 * (z * m)) :=
    Nat.le_self_pow (by exact Nat.ne_of_gt (Nat.mul_pos (by norm_num only) hs)) (N ^ 5)
  have hProp15Input' : ReliableProp15ModFourInput L ((N ^ 5) ^ (5 * (z * m))) := by
    rcases hProp15Input with ⟨hSq, hCoprime, hFactorPower, hReciprocal⟩
    exact ⟨hSq, hCoprime, le_trans hFactorPower hqle, hReciprocal⟩
  have hbase : 2 ^ 5 ≤ N ^ 5 := Nat.pow_le_pow_left hNge2 5
  have hexp : 20 ≤ z * m := Nat.mul_le_mul hzge2 hm
  have hscaleLower : 2 ^ 56 ≤ (N ^ 5) ^ (z * m) := by
    have hpow : (2 ^ 5) ^ 20 ≤ (N ^ 5) ^ (z * m) := by
      calc
        (2 ^ 5) ^ 20 ≤ (N ^ 5) ^ 20 := Nat.pow_le_pow_left hbase 20
        _ ≤ (N ^ 5) ^ (z * m) :=
          Nat.pow_le_pow_right (lt_of_lt_of_le (by norm_num only : 0 < 2 ^ 5) hbase) hexp
    have hsmall : 2 ^ 56 ≤ (2 ^ 5) ^ 20 := by
      calc
        2 ^ 56 ≤ 2 ^ 100 :=
          Nat.pow_le_pow_right (by norm_num only : 0 < 2) (by norm_num only : 56 ≤ 100)
        _ = (2 ^ 5) ^ 20 := by rw [← Nat.pow_mul]
    exact le_trans hsmall hpow
  refine ⟨(N ^ 5) ^ (z * m), ?_, ?_, ?_, ?_⟩
  · exact
      progressionAuxiliaryData_of_seed_factor_count_lower_bound_fifth_power hc₀ hq hL hLargeEnough
        hProp15Input' hReciprocal1024 hCq hfactor hlambda hFactorCount hs hscale hlower
  · exact hscaleLower
  · dsimp only [progressionAuxiliaryData_of_seed_factor_count_lower_bound_fifth_power,
      progressionAuxiliaryData_of_seed_factor_count_lower_bound,
      progressionAuxiliaryData_of_binomial_ratio_lower_bound,
      progressionAuxiliaryData_of_primeFactorCountLowerBound]
    calc
      (N ^ 5) ^ (5 * (z * m)) = (N ^ 5) ^ ((z * m) * 5) := by rw [Nat.mul_comm]
      _ = ((N ^ 5) ^ (z * m)) ^ 5 := by rw [Nat.pow_mul]
  · dsimp only [progressionAuxiliaryData_of_seed_factor_count_lower_bound_fifth_power,
      progressionAuxiliaryData_of_seed_factor_count_lower_bound,
      progressionAuxiliaryData_of_binomial_ratio_lower_bound,
      progressionAuxiliaryData_of_primeFactorCountLowerBound]
    exact Nat.le_self_pow (Nat.ne_of_gt hs) (N ^ 5)

end PseudoPrime.AnalyticNumberTheory.AGP
