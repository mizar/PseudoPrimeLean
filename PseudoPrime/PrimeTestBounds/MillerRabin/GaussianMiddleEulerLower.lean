/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleRemainder
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleCompensationAbel
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectMiddleRange
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleBoundary

/-! # Compensated Euler lower bounds for the direct middle range -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On positive arguments the normalized compensation weight is the principal weight. -/
private theorem middle_comp_eq_principal (P : Polynomial ℚ) (κ s b a : ℝ) {t : ℝ} (ht : 0 < t) :
    κ * middleCompWeight (P.eval₂ (Rat.castHom ℝ) ·) (Real.exp s) b a t =
      middlePrincipalWeight (P.map (Rat.castHom ℝ)) (κ * Real.exp (-a * (s + b))) (s + b)
        (a - 1 / 2) t := by
  simpa only [Polynomial.eval_map] using
    middle_principal_physical (P.map (Rat.castHom ℝ)) κ a b s ht

/-- Subtract the RH compensation charge from the principal sum while passing
the reduced exponential slope and the variation cost separately to the Euler bound. -/
public theorem middle_euler_lower_of_principal (hRH : RiemannHypothesis) (P : Polynomial ℚ) (N : ℕ)
    (hN : P.natDegree ≤ N) (hs : List ℚ) (hw : ∀ w ∈ hs, 0 < w) (a : ℚ) {κ s I V Δ D E : ℝ}
    (hκ : 0 ≤ κ) (hs0 : 20 ≤ s) (h0 : 0 ≤ P.eval₂ (Rat.castHom ℝ) 0)
    (hr : 0 ≤ P.eval₂ (Rat.castHom ℝ) (hs.sum : ℝ))
    (hI :
      (∫ v in (0 : ℝ)..(hs.sum : ℝ), Real.exp (-(a + (1 / 2 : ℝ)) * v) * middleCompOn P N hs 0 v) ≤
        I)
    (hV : middleCompVariation P N a (a - 1 / 2) hs 0 ≤ V) (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp s⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let b := (hs.sum : ℝ)
    let X := Real.exp s
    let Z := Real.exp (s + b)
    let W :=
      middlePrincipalWeight (P.map (Rat.castHom ℝ)) (κ * Real.exp (-(a : ℝ) * (s + b))) (s + b)
        ((a : ℝ) - 1 / 2)
    D ≤ Δ - 4 * (κ * Real.exp (b / 2) * I) →
      Real.exp (s / 2) * Δ + E ≤
        4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * W n) -
          (∑ n ∈ Finset.Ioc 0 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n * W n) →
      Real.exp (s / 2) * D + E - 4 * κ * ((s + b) ^ 2 / 24 * V) ≤
        ∑ n ∈ Finset.Ioc 0 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n) := by
  intro b X Z W hD hmain
  let F := middleCompWeight (P.eval₂ (Rat.castHom ℝ) ·) X b (a : ℝ)
  have h := middle_comp_rh_euler_lower hRH P N hN hs hw a hs0 h0 hr hI hV τ hτ hknown
  change
    4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * F n) -
        (∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * F n) -
        4 * (Real.exp ((s + b) / 2) * I + (s + b) ^ 2 / 24 * V) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊X * Real.exp b⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * F n) at h
  have hz : X * Real.exp b = Z := (Real.exp_add s b).symm
  rw [hz] at h
  have hsum (m : ℕ) (f : ℕ → ℝ) :
    κ * (∑ n ∈ Finset.Ioc 0 m, f n * F n) = ∑ n ∈ Finset.Ioc 0 m, f n * W n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have ht : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
    rw [mul_left_comm, middle_comp_eq_principal P κ s b (a : ℝ) ht]
  have heuler := mul_le_mul_of_nonneg_left h hκ
  simp only [mul_sub, mul_left_comm κ 4, hsum, ← mul_assoc] at heuler ⊢
  have he : Real.exp ((s + b) / 2) = Real.exp (s / 2) * Real.exp (b / 2) := by
    rw [add_div, Real.exp_add]
  rw [he] at heuler
  have hscaled := mul_le_mul_of_nonneg_left hD (Real.exp_nonneg (s / 2))
  linarith only [hmain, heuler, hscaled]

/-- The K141 compensated Euler sum admits the reduced slope and the certified
variation budget throughout its cutoff interval. -/
private theorem k141_euler_raw (hRH : RiemannHypothesis) {x : ℝ} (hl : 20 ≤ x) (hu : x ≤ 25)
    (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let z := x + 7 / 2
    let X := Real.exp x
    let k := (middleK141Norm : ℝ) * Real.exp (-(((2 : ℚ) : ℝ)) * z)
    let W :=
      middlePrincipalWeight (middleK141Profile.map (Rat.castHom ℝ)) k z (((2 : ℚ) : ℝ) - 1 / 2)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let c := Real.log (2 * Real.pi)
    let E :=
      -3 * (k * M.eval z) + 4 * (W X * (Chebyshev.psi X - X + c)) + 3 * (1 - c) * W 1 +
          3 * (gaussianLogZetaConstant - 1) * deriv W 1 -
        76739 / 10 ^ 6
    Real.exp (x / 2) * (7215924929 / 10 ^ 10) + E -
        4 * (middleK141Norm : ℝ) * (z ^ 2 / 24 * (14677708930678733 / 10 ^ 18)) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n) := by
  intro z X k W M c E
  obtain ⟨hs, hw, hb, hI, hV⟩ := middle_k141_comp_budgets
  have hd : ((2 : ℚ) - 1 / 2) = 3 / 2 := by norm_num only
  have hz : (hs.sum : ℝ) = 7 / 2 := by rw [hb, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat]
  have h0 : 0 ≤ middleK141Profile.eval₂ (Rat.castHom ℝ) 0 := by
    rw [← Polynomial.eval_map]
    exact middle_k141_profile_jet.1.ge
  have h :=
    middle_euler_lower_of_principal hRH middleK141Profile 31 middle_k141_comp_profile.1 hs hw (2)
      (κ := (middleK141Norm : ℝ)) (s := x) (I := 864821009060099 / 10 ^ 18) (V :=
      14677708930678733 / 10 ^ 18) (Δ := 72170863822 / 10 ^ 11) (D := 7215924929 / 10 ^ 10) (E := E)
      (Rat.cast_nonneg.mpr (by decide +kernel)) ((by norm_num only : (20 : ℝ) ≤ 20).trans hl) h0
      (by
        rw [hz]; exact middle_k141_comp_profile.2)
      (by rwa [hz]) (by rwa [hd]) τ hτ hknown
  dsimp only at h
  rw [hz] at h
  have he : ((7 / 2 : ℝ) / 2) = 7 / 4 := by norm_num only
  rw [he] at h
  refine h (k141_comp_slope_le le_rfl (Δ := _) le_rfl) ?_
  have hm := middle_k141_principal_sum hRH hl hu
  dsimp only [E, W, M, c, k, z, X] at *
  norm_num only [Rat.cast_ofNat, one_mul]
  simp only [one_mul] at hm
  linarith only [hm]

/-- The K156 compensated Euler sum admits the reduced slope and the certified
variation budget throughout its cutoff interval. -/
private theorem k156_euler_raw (hRH : RiemannHypothesis) {x : ℝ} (hl : 24 ≤ x) (hu : x ≤ 121 / 4)
    (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let z := x + 7 / 2
    let X := Real.exp x
    let k := (middleK156Norm : ℝ) * Real.exp (-(((49 / 20 : ℚ) : ℝ)) * z)
    let W :=
      middlePrincipalWeight (middleK156Profile.map (Rat.castHom ℝ)) k z
        (((49 / 20 : ℚ) : ℝ) - 1 / 2)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let c := Real.log (2 * Real.pi)
    let E :=
      -3 * (k * M.eval z) + 4 * (W X * (Chebyshev.psi X - X + c)) + 3 * (1 - c) * W 1 +
          3 * (gaussianLogZetaConstant - 1) * deriv W 1 -
        94703 / 10 ^ 6
    Real.exp (x / 2) * (721603265 / 10 ^ 9) + E -
        4 * (middleK156Norm : ℝ) * (z ^ 2 / 24 * (12114503414883903 / 10 ^ 18)) ≤
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n) := by
  intro z X k W M c E
  obtain ⟨hs, hw, hb, hI, hV⟩ := middle_k156_comp_budgets
  have hd : ((49 / 20 : ℚ) - 1 / 2) = 39 / 20 := by norm_num only
  have hz : (hs.sum : ℝ) = 7 / 2 := by rw [hb, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofNat]
  have h0 : 0 ≤ middleK156Profile.eval₂ (Rat.castHom ℝ) 0 := by
    rw [← Polynomial.eval_map]
    exact middle_k156_profile_jet.1.ge
  have h :=
    middle_euler_lower_of_principal hRH middleK156Profile 51 middle_k156_comp_profile.1 hs hw
      (49 / 20) (κ := (middleK156Norm : ℝ)) (s := x) (I := 693849645969795 / 10 ^ 18) (V :=
      12114503414883903 / 10 ^ 18) (Δ := 72170932589 / 10 ^ 11) (D := 721603265 / 10 ^ 9) (E := E)
      (Rat.cast_nonneg.mpr (by decide +kernel)) ((by norm_num only : (20 : ℝ) ≤ 24).trans hl) h0
      (by
        rw [hz]; exact middle_k156_comp_profile.2)
      (by rwa [hz]) (by rwa [hd]) τ hτ hknown
  dsimp only at h
  rw [hz] at h
  have he : ((7 / 2 : ℝ) / 2) = 7 / 4 := by norm_num only
  rw [he] at h
  refine h (k156_comp_slope_le le_rfl (Δ := _) le_rfl) ?_
  have hm := middle_k156_principal_sum hRH hl hu
  dsimp only [E, W, M, c, k, z, X] at *
  norm_num only [Rat.cast_div, Rat.cast_ofNat, one_mul]
  simp only [one_mul] at hm
  linarith only [hm]

/-- At the cutoff the physical weight is its scalar coefficient divided
by the square root of the cutoff. -/
private theorem principal_weight_at_cutoff (B : Polynomial ℚ) (κ a b x : ℝ) :
    middlePrincipalWeight (B.map (Rat.castHom ℝ)) (κ * Real.exp (-a * (x + b))) (x + b) (a - 1 / 2)
        (Real.exp x) =
      (κ * Real.exp (-a * b) * B.eval₂ (Rat.castHom ℝ) b) / Real.sqrt (Real.exp x) := by
  rw [← middle_comp_eq_principal B κ x b a (Real.exp_pos x)]
  simp only [middleCompWeight, div_self (Real.exp_pos x).ne', Real.log_one, sub_zero]
  rw [Real.sqrt_eq_rpow, Real.rpow_neg (Real.exp_nonneg x)]
  ring

/-- Collect the three lower-endpoint terms into one polynomial. -/
@[expose]
public noncomputable def middleLowerEndpointPoly (B M : Polynomial ℝ) (d : ℝ) : Polynomial ℝ :=
  Polynomial.C (-3) * M + Polynomial.C (3 * (1 - Real.log (2 * Real.pi))) * B +
    Polynomial.C (3 * (gaussianLogZetaConstant - 1)) * (Polynomial.C d * B - B.derivative)

/-- The endpoint contribution is the normalized polynomial evaluated at the support. -/
private theorem lower_endpoint_group (B M : Polynomial ℝ) (k z d : ℝ) :
    let W := middlePrincipalWeight B k z d
    let c := Real.log (2 * Real.pi)
    (-3 * (k * M.eval z) + 3 * (1 - c) * W 1 + 3 * (gaussianLogZetaConstant - 1) * deriv W 1) =
      k * (middleLowerEndpointPoly B M d).eval z := by
  intro W c
  have h := (middle_principal_weight_deriv B k z d (t := 1) zero_lt_one).deriv
  simp only [Real.one_rpow, Real.log_one, sub_zero, one_mul] at h
  change deriv W 1 = _ at h
  have hW : W 1 = k * B.eval z := by
    simp only [W, middlePrincipalWeight, Real.one_rpow, Real.log_one, sub_zero, one_mul]
  rw [h, hW]
  simp only [middleLowerEndpointPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- On the K141 interval, the cutoff and variation terms cost at most
`61/1000` times the squared half-logarithm in the Euler lower bound. -/
public theorem middle_k141_euler_lower (hRH : RiemannHypothesis) {x : ℝ} (hl : 20 ≤ x) (hu : x ≤ 25)
    (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let z := x + 7 / 2
    let k := (middleK141Norm : ℝ) * Real.exp (-(((2 : ℚ) : ℝ)) * z)
    let W :=
      middlePrincipalWeight (middleK141Profile.map (Rat.castHom ℝ)) k z (((2 : ℚ) : ℝ) - 1 / 2)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let P :=
      middleLowerEndpointPoly (middleK141Profile.map (Rat.castHom ℝ)) M (((2 : ℚ) : ℝ) - 1 / 2)
    Real.exp (x / 2) * (7215924929 / 10 ^ 10) - (61 / 1000) * (x / 2) ^ 2 + k * P.eval z -
        76739 / 10 ^ 6 ≤
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n) := by
  intro z k W M P
  have hκ0 : 0 ≤ (middleK141Norm : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hκ : (middleK141Norm : ℝ) ≤ 7 / 1000 := by
    norm_num only [middleK141Norm, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
  have hx : 20 ≤ x := (by norm_num only : (20 : ℝ) ≤ 20).trans hl
  have hW :=
    principal_weight_at_cutoff middleK141Profile (middleK141Norm : ℝ) (((2 : ℚ) : ℝ)) (7 / 2) x
  have he : (-(((2 : ℚ) : ℝ)) * (7 / 2)) = -(7) := by norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [he] at hW
  have hw0 := mul_nonneg (mul_nonneg hκ0 (Real.exp_nonneg (-(7)))) middle_k141_comp_profile.2
  have hb :=
    middle_signed_boundary hRH hx hw0 middle_k141_cutoff_weight_le hκ0 hκ (v :=
      14677708930678733 / 10 ^ 18) (by norm_num only) (by norm_num only) hW
  have h := k141_euler_raw hRH hl hu τ hτ hknown
  have hg :=
    lower_endpoint_group (middleK141Profile.map (Rat.castHom ℝ)) M k z (((2 : ℚ) : ℝ) - 1 / 2)
  dsimp only [z, k, W, M, P] at *
  linarith only [h, hb, hg]

/-- On the K156 interval, the cutoff and variation terms cost at most
`61/1000` times the squared half-logarithm in the Euler lower bound. -/
public theorem middle_k156_euler_lower (hRH : RiemannHypothesis) {x : ℝ} (hl : 24 ≤ x)
    (hu : x ≤ 121 / 4) (τ : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let z := x + 7 / 2
    let k := (middleK156Norm : ℝ) * Real.exp (-(((49 / 20 : ℚ) : ℝ)) * z)
    let W :=
      middlePrincipalWeight (middleK156Profile.map (Rat.castHom ℝ)) k z
        (((49 / 20 : ℚ) : ℝ) - 1 / 2)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let P :=
      middleLowerEndpointPoly (middleK156Profile.map (Rat.castHom ℝ)) M
        (((49 / 20 : ℚ) : ℝ) - 1 / 2)
    Real.exp (x / 2) * (721603265 / 10 ^ 9) - (61 / 1000) * (x / 2) ^ 2 + k * P.eval z -
        94703 / 10 ^ 6 ≤
      ∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n) := by
  intro z k W M P
  have hκ0 : 0 ≤ (middleK156Norm : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hκ : (middleK156Norm : ℝ) ≤ 7 / 1000 := by
    norm_num only [middleK156Norm, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
  have hx : 20 ≤ x := (by norm_num only : (20 : ℝ) ≤ 24).trans hl
  have hW :=
    principal_weight_at_cutoff middleK156Profile (middleK156Norm : ℝ) (((49 / 20 : ℚ) : ℝ)) (7 / 2)
      x
  have he : (-(((49 / 20 : ℚ) : ℝ)) * (7 / 2)) = -(343 / 40) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [he] at hW
  have hw0 := mul_nonneg (mul_nonneg hκ0 (Real.exp_nonneg (-(343 / 40)))) middle_k156_comp_profile.2
  have hb :=
    middle_signed_boundary hRH hx hw0 middle_k156_cutoff_weight_le hκ0 hκ (v :=
      12114503414883903 / 10 ^ 18) (by norm_num only) (by norm_num only) hW
  have h := k156_euler_raw hRH hl hu τ hτ hknown
  have hg :=
    lower_endpoint_group (middleK156Profile.map (Rat.castHom ℝ)) M k z (((49 / 20 : ℚ) : ℝ) - 1 / 2)
  dsimp only [z, k, W, M, P] at *
  linarith only [h, hb, hg]

/-- The reflected prime-power series with its physical normalization.
The trace is bounded separately when applying its Laplace envelope. -/
@[expose]
public noncomputable def middleReflectedSum (B : Polynomial ℝ) (τ : ℕ → ℝ) (κ a b x : ℝ) : ℝ :=
  κ * Real.exp (-a * (x + b)) *
    ∑' n : ℕ,
      ArithmeticFunction.vonMangoldt n * τ n *
        ((n : ℝ) ^ (-(a + 1 / 2)) * B.eval (x + b + Real.log n))

/-- Subtract the reflected Laplace envelope from the lower endpoint polynomial.
Both terms have the same exponential decay rate. -/
@[expose]
public noncomputable def middleEulerDecay (B P : Polynomial ℝ) (κ a b p : ℝ) : Polynomial ℝ :=
  Polynomial.C (κ * Real.exp (-a * b)) * P.comp (Polynomial.X + Polynomial.C b) -
    Polynomial.C (6 * p) * middleReflectionPoly B (a + 1 / 2) b

/-- Add the absolute reflected-series cost to a forward lower bound. -/
private theorem euler_sub_reflected (B P : Polynomial ℝ) (τ : ℕ → ℝ) {κ a b x p A F : ℝ}
    (ha : 1 / 2 < a) (hκ : 0 ≤ κ) (hp : κ * Real.exp (-a * b) ≤ p) (hτ : ∀ n, |τ n| ≤ 3)
    (hB : ∀ t, b + x ≤ t → 0 ≤ B.eval t) (hD : ∀ t, b + x ≤ t → 0 ≤ B.derivative.eval t)
    (hF : A + κ * Real.exp (-a * (x + b)) * P.eval (x + b) ≤ F) :
    A + Real.exp (-a * x) * (middleEulerDecay B P κ a b p).eval x ≤
      F - |middleReflectedSum B τ κ a b x| := by
  have h := middle_reflection_le_scaled_poly τ hτ B ha hκ hp hB hD
  dsimp only at h
  have he : -a * (x + b) = -a * b - a * x := by ring
  have hbx : x + b = b + x := add_comm _ _
  have hR :
    |middleReflectedSum B τ κ a b x| ≤
      Real.exp (-a * x) * (6 * p * (middleReflectionPoly B (a + 1 / 2) b).eval x) := by
    rw [middleReflectedSum, he, hbx]
    exact h
  have hE : Real.exp (-a * (x + b)) = Real.exp (-a * b) * Real.exp (-a * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hE] at hF
  simp only [middleEulerDecay, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X]
  linarith only [hF, hR]

/-- The K141 Euler lower bound with the reflected series included in the decay
polynomial, on the same cutoff interval under RH. -/
public theorem middle_k141_euler_reflected (hRH : RiemannHypothesis) {x : ℝ} (hl : 20 ≤ x)
    (hu : x ≤ 25) (τ τr : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3) (hτr : ∀ m, |τr m| ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let B := middleK141Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK141Profile (5 / 2) 0).map (Rat.castHom ℝ)
    let a := ((2 : ℚ) : ℝ)
    let κ := (middleK141Norm : ℝ)
    let z := x + 7 / 2
    let W := middlePrincipalWeight B (κ * Real.exp (-a * z)) z (a - 1 / 2)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a (7 / 2) (middleK141Scale : ℝ)
    (Real.exp (x / 2) * (7215924929 / 10 ^ 10) - (61 / 1000) * (x / 2) ^ 2 - 76739 / 10 ^ 6) +
        Real.exp (-a * x) * E.eval x ≤
      (∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n)) -
        |middleReflectedSum B τr κ a (7 / 2) x| := by
  intro B M a κ z W P E
  have ha : 1 / 2 < a := by
    dsimp only [a]; norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hκ : 0 ≤ κ := Rat.cast_nonneg.mpr (by decide +kernel : 0 ≤ middleK141Norm)
  have hz : (20 : ℝ) ≤ 7 / 2 + x := by linarith only [hl]
  have he : -a * (7 / 2) = -(7) := by
    dsimp only [a]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hp : κ * Real.exp (-a * (7 / 2)) ≤ (middleK141Scale : ℝ) := by
    rw [he]
    exact middle_k141_scale_le
  apply euler_sub_reflected B P τr ha hκ hp hτr
  · intro t ht
    exact middle_k141_tail_sign 0 (hz.trans ht)
  · intro t ht
    exact middle_k141_tail_sign 1 (hz.trans ht)
  · have h := middle_k141_euler_lower hRH hl hu τ hτ hknown
    dsimp only [W, P, B, M, κ, z, a] at *
    linarith only [h]

/-- The K156 Euler lower bound with the reflected series included in the decay
polynomial, on the same cutoff interval under RH. -/
public theorem middle_k156_euler_reflected (hRH : RiemannHypothesis) {x : ℝ} (hl : 24 ≤ x)
    (hu : x ≤ 121 / 4) (τ τr : ℕ → ℝ) (hτ : ∀ m, -1 ≤ τ m ∧ τ m ≤ 3) (hτr : ∀ m, |τr m| ≤ 3)
    (hknown : ∀ m ≤ ⌊Real.exp x⌋₊, ArithmeticFunction.vonMangoldt m ≠ 0 → τ m = 3) :
    let B := middleK156Profile.map (Rat.castHom ℝ)
    let M := (middleMomentPoly middleK156Profile (59 / 20) 0).map (Rat.castHom ℝ)
    let a := ((49 / 20 : ℚ) : ℝ)
    let κ := (middleK156Norm : ℝ)
    let z := x + 7 / 2
    let W := middlePrincipalWeight B (κ * Real.exp (-a * z)) z (a - 1 / 2)
    let P := middleLowerEndpointPoly B M (a - 1 / 2)
    let E := middleEulerDecay B P κ a (7 / 2) (middleK156Scale : ℝ)
    (Real.exp (x / 2) * (721603265 / 10 ^ 9) - (61 / 1000) * (x / 2) ^ 2 - 94703 / 10 ^ 6) +
        Real.exp (-a * x) * E.eval x ≤
      (∑ n ∈ Finset.Ioc 0 ⌊Real.exp z⌋₊, ArithmeticFunction.vonMangoldt n * (τ n * W n)) -
        |middleReflectedSum B τr κ a (7 / 2) x| := by
  intro B M a κ z W P E
  have ha : 1 / 2 < a := by
    dsimp only [a]; norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hκ : 0 ≤ κ := Rat.cast_nonneg.mpr (by decide +kernel : 0 ≤ middleK156Norm)
  have hz : (25 : ℝ) ≤ 7 / 2 + x := by linarith only [hl]
  have he : -a * (7 / 2) = -(343 / 40) := by
    dsimp only [a]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hp : κ * Real.exp (-a * (7 / 2)) ≤ (middleK156Scale : ℝ) := by
    rw [he]
    exact middle_k156_scale_le
  apply euler_sub_reflected B P τr ha hκ hp hτr
  · intro t ht
    exact middle_k156_tail_sign 0 (hz.trans ht)
  · intro t ht
    exact middle_k156_tail_sign 1 (hz.trans ht)
  · have h := middle_k156_euler_lower hRH hl hu τ hτ hknown
    dsimp only [W, P, B, M, κ, z, a] at *
    linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
