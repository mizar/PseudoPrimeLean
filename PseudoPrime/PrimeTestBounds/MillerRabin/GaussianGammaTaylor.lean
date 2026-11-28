/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleContour

/-! # Polynomial moments for weakly decaying Gaussian gamma terms -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integrate a monomial against a power of the distance to the upper
endpoint. Scaling a Bernstein basis integral avoids a binomial expansion. -/
theorem gamma_beta_moment (i j : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ v in (0 : ℝ)..z, v ^ i * (z - v) ^ j) =
      z ^ (i + j + 1) / ((i + j).choose i : ℝ) / ((i + j : ℕ) + 1) := by
  have hi : i ≤ i + j := Nat.le_add_right i j
  let c : ℝ := (i + j).choose i
  have hc : c ≠ 0 := (Nat.cast_pos.mpr (Nat.choose_pos hi)).ne'
  let G := fun v : ℝ ↦ c * (v / z) ^ i * (1 - v / z) ^ j
  have hG : (∫ v in (0 : ℝ)..z, G v) = z / ((i + j : ℕ) + 1) := by
    simpa only [G, c, pow_zero, one_mul, Nat.add_zero, Nat.add_sub_cancel_left, div_self hc,
      Nat.zero_add, pow_one, one_div, div_eq_mul_inv] using
      Analysis.bernstein_scaled_moment hz (i + j) i 0 hi
  have hscale (v : ℝ) : v ^ i * (z - v) ^ j = (z ^ (i + j) / c) * G v := by
    dsimp only [G]
    rw [show 1 - v / z = (z - v) / z by rw [sub_div, div_self hz.ne']]
    rw [div_pow, div_pow, pow_add]
    field_simp [hc, hz.ne', pow_ne_zero i hz.ne', pow_ne_zero j hz.ne']
  simp only [hscale, intervalIntegral.integral_const_mul, hG, pow_succ]
  ring

/-- Integrate a polynomial against a power of the distance to the upper
endpoint, with one beta weight per coefficient. -/
theorem gamma_polynomial_beta_moment (P : Polynomial ℝ) (j : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ v in (0 : ℝ)..z, (z - v) ^ j * P.eval v) =
      ∑ i ∈ Finset.range (P.natDegree + 1),
        P.coeff i * (z ^ (i + j + 1) / ((i + j).choose i : ℝ) / ((i + j : ℕ) + 1)) := by
  let F := fun i v ↦ P.coeff i * (v ^ i * (z - v) ^ j)
  have hF (i : ℕ) : Continuous (F i) :=
    continuous_const.mul ((continuous_id.pow i).mul ((continuous_const.sub continuous_id).pow j))
  have he (v : ℝ) : (z - v) ^ j * P.eval v = ∑ i ∈ Finset.range (P.natDegree + 1), F i v := by
    rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    exact
      Finset.sum_congr rfl fun i _ ↦ by
        dsimp only [F]; ring
  simp only [he]
  rw [intervalIntegral.integral_finsetSum (fun i _ ↦ (hF i).intervalIntegrable 0 z)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  dsimp only [F]
  rw [intervalIntegral.integral_const_mul, gamma_beta_moment i j hz]

/-- Integrate a Taylor truncation of the forward exponential convolution
using beta moments. Each pair of orders contributes to just one power of the height. -/
theorem gamma_forward_taylor_moment (P : Polynomial ℝ) (d : ℝ) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    (∫ v in (0 : ℝ)..z,
        (∑ j ∈ Finset.range (m + 1), ((-d) ^ j / (j.factorial : ℝ)) * (z - v) ^ j) * P.eval v) =
      ∑ j ∈ Finset.range (m + 1),
        ((-d) ^ j / (j.factorial : ℝ)) *
          ∑ i ∈ Finset.range (P.natDegree + 1),
            P.coeff i * (z ^ (i + j + 1) / ((i + j).choose i : ℝ) / ((i + j : ℕ) + 1)) := by
  let F := fun j v ↦ ((-d) ^ j / (j.factorial : ℝ)) * ((z - v) ^ j * P.eval v)
  have hF (j : ℕ) : Continuous (F j) :=
    continuous_const.mul (((continuous_const.sub continuous_id).pow j).mul P.continuous)
  simp only [Finset.sum_mul, mul_assoc,
    ←
      show ∀ j v, F j v = ((-d) ^ j / (j.factorial : ℝ)) * ((z - v) ^ j * P.eval v) from fun _ _ ↦
        rfl]
  rw [intervalIntegral.integral_finsetSum (fun j _ ↦ (hF j).intervalIntegrable 0 z)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  dsimp only [F]
  rw [intervalIntegral.integral_const_mul, gamma_polynomial_beta_moment P j hz]

/-- The rational convolution polynomial whose monomial of order `i+j+1`
receives the beta moment of profile order `i` and Taylor order `j`. -/
noncomputable def gammaTaylorConvolution (P : Polynomial ℚ) (d : ℚ) (m : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    ∑ i ∈ Finset.range (P.natDegree + 1),
      Polynomial.C
          (((-d) ^ j / (j.factorial : ℚ)) * P.coeff i / ((i + j).choose i : ℚ) /
            ((i + j : ℕ) + 1)) *
        Polynomial.X ^ (i + j + 1)

/-- Cancel the Taylor factorial against the binomial weight in the beta
moment. The remaining factorials depend on the input and output orders. -/
private theorem gamma_taylor_factorial (i j : ℕ) (c w : ℚ) :
    w / (j.factorial : ℚ) * c / ((i + j).choose i : ℚ) / ((i + j : ℕ) + 1) =
      w * (c * (i.factorial : ℚ)) / ((i + j + 1).factorial : ℚ) := by
  have h :
    (((i + j).choose i : ℕ) : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ) =
      ((i + j).factorial : ℚ) := by
    have hn := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j)
    rw [Nat.add_sub_cancel_left] at hn
    exact_mod_cast hn
  have h₁ : (((i + j).choose i : ℕ) : ℚ) ≠ 0 :=
    (Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_right i j))).ne'
  have h₂ : (j.factorial : ℚ) ≠ 0 := (Nat.cast_pos.mpr (Nat.factorial_pos j)).ne'
  have h₃ : 0 < ((i + j : ℕ) : ℚ) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  rw [Nat.factorial_succ, Nat.cast_mul, ← h]
  simp only [Nat.cast_add, Nat.cast_one] at h₃ ⊢
  have h₄ : (i.factorial : ℚ) ≠ 0 := (Nat.cast_pos.mpr (Nat.factorial_pos i)).ne'
  field_simp [h₁, h₂, h₃.ne', h₄]

/-- In factorial-scaled coefficients the Taylor moment is a convolution
with a geometric row of length `m+1`. -/
theorem gamma_taylor_factorial_basis (P : Polynomial ℚ) (d : ℚ) (m : ℕ) :
    gammaTaylorConvolution P d m =
      ∑ j ∈ Finset.range (m + 1),
        ∑ i ∈ Finset.range (P.natDegree + 1),
          Polynomial.C ((-d) ^ j * (P.coeff i * (i.factorial : ℚ)) / ((i + j + 1).factorial : ℚ)) *
            Polynomial.X ^ (i + j + 1) := by
  unfold gammaTaylorConvolution
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ ?_
  rw [gamma_taylor_factorial]

/-- Evaluating the rational convolution polynomial gives the real Taylor
moment, so the coefficient computation can be shared across cells. -/
theorem gamma_taylor_convolution_eval (P : Polynomial ℚ) (d : ℚ) (m : ℕ) {z : ℝ} (hz : 0 < z) :
    ((gammaTaylorConvolution P d m).map (Rat.castHom ℝ)).eval z =
      ∫ v in (0 : ℝ)..z,
        (∑ j ∈ Finset.range (m + 1), ((-(d : ℝ)) ^ j / (j.factorial : ℝ)) * (z - v) ^ j) *
          (P.map (Rat.castHom ℝ)).eval v := by
  rw [gamma_forward_taylor_moment _ _ _ hz]
  simp only [gammaTaylorConvolution,
    Polynomial.natDegree_map_eq_of_injective (f := Rat.castHom ℝ) (Rat.cast_injective (α := ℝ)),
    Polynomial.coeff_map, Rat.coe_castHom, Polynomial.eval_map, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_natCast, Rat.cast_add,
    Rat.cast_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The K156 second-pole moment is enclosed by evaluating one rational
polynomial and allowing its uniform Taylor remainder. -/
theorem middle_k156_second_pole_poly (P : Polynomial ℚ) {z M : ℝ} (hz : 0 < z) (hz' : z ≤ 135 / 4)
    (m : ℕ) (hM : ∀ v ∈ Set.Icc 0 z, |(P.map (Rat.castHom ℝ)).eval v| ≤ M) :
    |(∫ v in (0 : ℝ)..z, Real.exp (-(1 / 20 : ℝ) * (z - v)) * (P.map (Rat.castHom ℝ)).eval v) -
          ((gammaTaylorConvolution P (1 / 20) m).map (Rat.castHom ℝ)).eval z| ≤
      ((27 / 16 : ℝ) ^ (m + 1) / ((m + 1).factorial : ℝ)) * M * (135 / 4) := by
  rw [gamma_taylor_convolution_eval _ _ _ hz]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    middle_k156_second_pole_error (P.map (Rat.castHom ℝ)) hz.le hz' hM m

/-- Truncated geometric convolution satisfies a three-term recurrence as
a polynomial identity, with one subtraction for the term leaving the window. -/
theorem gamma_geometric_convolution (A : Polynomial ℚ) (r : ℚ) (m : ℕ) :
    let Xr := Polynomial.C r * Polynomial.X
    let B := A * ∑ j ∈ Finset.range (m + 1), Xr ^ j
    B - B * Xr = A - A * Xr ^ (m + 1) := by
  intro Xr B
  calc
    B - B * Xr = A * ((∑ j ∈ Finset.range (m + 1), Xr ^ j) * (1 - Xr)) := by
      dsimp only [B]
      ring
    _ = A - A * Xr ^ (m + 1) := by rw [geom_sum_mul_neg, mul_sub, mul_one]

/-- The factorial-scaled Taylor coefficients are exactly the coefficients
of the input factorial row multiplied by the truncated geometric row. -/
theorem gamma_taylor_scaled_coeff (P : Polynomial ℚ) (d : ℚ) (m k : ℕ) :
    let A :=
      ∑ i ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff i * (i.factorial : ℚ)) * Polynomial.X ^ i
    let B := A * ∑ j ∈ Finset.range (m + 1), (Polynomial.C (-d) * Polynomial.X) ^ j
    (gammaTaylorConvolution P d m).coeff (k + 1) * ((k + 1).factorial : ℚ) = B.coeff k := by
  intro A B
  rw [gamma_taylor_factorial_basis]
  simp only [B, A, Finset.mul_sum, Finset.sum_mul, mul_pow, ← Polynomial.C_pow,
    Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, mul_assoc, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_left_comm (Polynomial.X ^ i), ← pow_add, ←
    mul_assoc (Polynomial.C _) (Polynomial.C _) (Polynomial.X ^ (i + j)), ← Polynomial.C_mul,
    Polynomial.coeff_C_mul_X_pow]
  by_cases h : k = i + j
  · simp only [h, ite_true]
    rw [div_mul_cancel₀ _ (Nat.cast_pos.mpr (Nat.factorial_pos (i + j + 1))).ne']
    ring
  · simp only [h, Nat.add_right_cancel_iff, ite_false, zero_mul]

/-- The next factorial-scaled coefficient uses the preceding output
coefficient, the new input coefficient, and the expired input coefficient. -/
theorem gamma_geometric_coeff_succ (A : Polynomial ℚ) (r : ℚ) (m k : ℕ) :
    let Xr := Polynomial.C r * Polynomial.X
    let B := A * ∑ j ∈ Finset.range (m + 1), Xr ^ j
    B.coeff (k + 1) =
      A.coeff (k + 1) + B.coeff k * r - (if m ≤ k then A.coeff (k - m) * r ^ (m + 1) else 0) := by
  intro Xr B
  have h := congrArg (fun P : Polynomial ℚ ↦ P.coeff (k + 1)) (gamma_geometric_convolution A r m)
  change (B - B * Xr).coeff (k + 1) = (A - A * Xr ^ (m + 1)).coeff (k + 1) at h
  simp only [Xr, Polynomial.coeff_sub, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
    Polynomial.coeff_mul_X, Polynomial.coeff_mul_X_pow', Polynomial.coeff_mul_C,
    Nat.succ_le_succ_iff, Nat.succ_sub_succ_eq_sub] at h
  linarith only [h]

/-- The constant coefficient of the truncated geometric convolution is
the constant coefficient of its input polynomial. -/
theorem gamma_geometric_coeff_zero (A : Polynomial ℚ) (r : ℚ) (m : ℕ) :
    (A * ∑ j ∈ Finset.range (m + 1), (Polynomial.C r * Polynomial.X) ^ j).coeff 0 = A.coeff 0 := by
  have h := congrArg (fun P : Polynomial ℚ ↦ P.coeff 0) (gamma_geometric_convolution A r m)
  have hn : ¬m + 1 ≤ 0 := Nat.not_succ_le_zero m
  simpa only [Polynomial.coeff_sub, mul_pow, ← Polynomial.C_pow, ← mul_assoc,
    Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_X_pow', hn, ite_false, sub_zero] using h

/-- The initial value and recurrence uniquely determine every coefficient
of the geometric convolution within the checked prefix. -/
theorem gamma_geometric_row_eq (A : Polynomial ℚ) (r : ℚ) (m N : ℕ) (u : ℕ → ℚ)
    (h₀ : u 0 = A.coeff 0)
    (h :
      ∀ k < N,
        u (k + 1) =
          A.coeff (k + 1) + u k * r - (if m ≤ k then A.coeff (k - m) * r ^ (m + 1) else 0)) :
    ∀ k ≤ N,
      u k = (A * ∑ j ∈ Finset.range (m + 1), (Polynomial.C r * Polynomial.X) ^ j).coeff k := by
  intro k
  induction k with
  | zero =>
    intro _
    exact h₀.trans (gamma_geometric_coeff_zero A r m).symm
  | succ k ih =>
    intro hk
    rw [h k hk, ih (Nat.le_of_succ_le hk)]
    exact (gamma_geometric_coeff_succ A r m k).symm

/-- A finite recurrence certificate gives the actual Taylor coefficients
through index `N+1` after undoing the factorial scaling. -/
theorem gamma_taylor_row_eq (P : Polynomial ℚ) (d : ℚ) (m N : ℕ) (u : ℕ → ℚ) :
    let A :=
      ∑ i ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff i * (i.factorial : ℚ)) * Polynomial.X ^ i
    u 0 = A.coeff 0 →
      (∀ k < N,
        u (k + 1) =
          A.coeff (k + 1) + u k * (-d) - (if m ≤ k then A.coeff (k - m) * (-d) ^ (m + 1) else 0)) →
      ∀ k ≤ N, (gammaTaylorConvolution P d m).coeff (k + 1) = u k / ((k + 1).factorial : ℚ) := by
  intro A h₀ h k hk
  apply (eq_div_iff (Nat.cast_pos.mpr (Nat.factorial_pos (k + 1))).ne').mpr
  exact
    (gamma_taylor_scaled_coeff P d m k).trans ((gamma_geometric_row_eq A (-d) m N u h₀ h k hk).symm)

/-- Check a prefix of the factorial-scaled convolution after clearing the
common denominator and the power of the reciprocal rate. -/
@[expose]
def gammaTaylorRowCheck (m N : ℕ) (input output : Array ℤ) : Bool :=
  (output[0]?.getD 0 == input[0]?.getD 0) &&
    (List.range N).all fun k ↦
      output[k + 1]?.getD 0 ==
        input[k + 1]?.getD 0 - output[k]?.getD 0 -
          (if m ≤ k then input[k - m]?.getD 0 * (-1 : ℤ) ^ (m + 1) else 0)

/-- An accepted integer row provides its initial equality and each
adjacent recurrence equality in the checked prefix. -/
theorem gamma_taylor_check_sound {m N : ℕ} {input output : Array ℤ}
    (h : gammaTaylorRowCheck m N input output = true) :
    output[0]?.getD 0 = input[0]?.getD 0 ∧
      ∀ k < N,
        output[k + 1]?.getD 0 =
          input[k + 1]?.getD 0 - output[k]?.getD 0 -
            (if m ≤ k then input[k - m]?.getD 0 * (-1 : ℤ) ^ (m + 1) else 0) := by
  simp only [gammaTaylorRowCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  exact h

/-- Forming the factorial-weighted input polynomial preserves its
coefficient at each order up to the factorial multiplier. -/
theorem gamma_factorial_input_coeff (P : Polynomial ℚ) (k : ℕ) :
    (∑ i ∈ Finset.range (P.natDegree + 1),
            Polynomial.C (P.coeff i * (i.factorial : ℚ)) * Polynomial.X ^ i).coeff
        k =
      P.coeff k * (k.factorial : ℚ) := by
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k ≤ P.natDegree
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))]
    · rw [ite_eq_left rfl]
    · intro i _ hi
      rw [ite_eq_right (Ne.symm hi)]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hk), zero_mul]
    refine Finset.sum_eq_zero fun i hi ↦ ?_
    have hne : k ≠ i := fun he ↦ hk (he.symm ▸ Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    exact ite_eq_right hne

/-- Undo denominator clearing for an accepted Taylor row. The input row
supplies the factorial-scaled coefficients, and the output row supplies
the resulting Taylor coefficients through the checked degree. -/
theorem gamma_taylor_int_row_eq (P : Polynomial ℚ) {q D : ℚ} (m N : ℕ) (input output : Array ℤ)
    (h : gammaTaylorRowCheck m N input output = true) :
    let A :=
      ∑ i ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff i * (i.factorial : ℚ)) * Polynomial.X ^ i
    (∀ k ≤ N, A.coeff k = (input[k]?.getD 0 : ℚ) / (D * q ^ k)) →
      ∀ k ≤ N,
        (gammaTaylorConvolution P (1 / q) m).coeff (k + 1) =
          (output[k]?.getD 0 : ℚ) / (D * q ^ k) / ((k + 1).factorial : ℚ) := by
  intro A hA
  let u := fun k : ℕ ↦ (output[k]?.getD 0 : ℚ) / (D * q ^ k)
  obtain ⟨h₀, hstep⟩ := gamma_taylor_check_sound h
  apply gamma_taylor_row_eq P (1 / q) m N u
  · dsimp only [u]
    rw [h₀, hA 0 (Nat.zero_le N)]
  · intro k hk
    rw [hA (k + 1) hk]
    have he := congrArg (fun n : ℤ ↦ (n : ℚ)) (hstep k hk)
    dsimp only [u]
    simp only [Int.cast_sub] at he
    rw [he, sub_div, sub_div]
    have hp : D * q ^ (k + 1) = (D * q ^ k) * q := by rw [pow_succ, mul_assoc]
    have hs (x : ℚ) : x / (D * q ^ (k + 1)) = x / (D * q ^ k) * (1 / q) := by
      rw [hp, div_mul_eq_div_div, ← mul_one_div]
    rw [hs (output[k]?.getD 0 : ℚ), mul_neg, ← sub_eq_add_neg]
    by_cases hm : m ≤ k
    · simp only [ite_eq_left hm]
      rw [hA (k - m) ((Nat.sub_le _ _).trans hk.le)]
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
      have hi : k + 1 = (k - m) + (m + 1) := by rw [← Nat.add_assoc, Nat.sub_add_cancel hm]
      have hd : D * q ^ (k + 1) = (D * q ^ (k - m)) * q ^ (m + 1) := by rw [hi, pow_add, mul_assoc]
      rw [hd, show -(1 / q) = (-1 : ℚ) / q by rw [neg_div], div_pow]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    · simp only [ite_eq_right hm, Int.cast_zero, zero_div]

end PseudoPrime.PrimeTestBounds.MillerRabin
