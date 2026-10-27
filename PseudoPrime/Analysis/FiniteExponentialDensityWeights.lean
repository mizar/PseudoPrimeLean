/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteQuadraticHeightWeights

/-! # Finite exponential weights from density growth and a real-part gap -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a finite set of natural indices all at least `K` and a nonnegative
ratio below one, the geometric sum is bounded by its infinite tail. Subtract `K`
from every index and compare with the full geometric series. This retains the
lower-index decay in finite density bands. -/
theorem sum_geometric_of_lower_index (J : Finset ℕ) (K : ℕ) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hJ : ∀ j ∈ J, K ≤ j) : ∑ j ∈ J, r ^ j ≤ r ^ K / (1 - r) := by
  let D := J.image (fun j ↦ j - K)
  have hinj : Set.InjOn (fun j : ℕ ↦ j - K) (J : Set ℕ) := by
    intro j hj k hk he
    have hj' := Nat.sub_add_cancel (hJ j hj)
    have hk' := Nat.sub_add_cancel (hJ k hk)
    exact hj'.symm.trans ((congrArg (fun n ↦ n + K) he).trans hk')
  have heq : (∑ j ∈ J, r ^ j) = r ^ K * ∑ j ∈ D, r ^ j := by
    rw [Finset.mul_sum, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel (hJ j hj)]
  have hg := hasSum_geometric_of_lt_one hr hr1
  have hs := hg.summable.sum_le_tsum D (fun j _ ↦ pow_nonneg hr j)
  rw [hg.tsum_eq] at hs
  rw [heq, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hs (pow_nonneg hr _)

/-- For finite nonnegative weights with cumulative growth at most `C exp(a(j+1))`
and `a ≤ 1/2`, each unit floor bin of nonnegative deficits has exponentially
weighted mass bounded by `C exp(1/2) exp(-1/2)^j`. Compare the exponential weight
within the bin and use the cumulative bound. This is the discrete density step. -/
theorem sum_exp_weight_in_floor_bin {ι : Type*} (S : Finset ι) (u w : ι → ℝ) {a C : ℝ}
    (ha : a ≤ 1 / 2) (hC : 0 ≤ C) (hu : ∀ i ∈ S, 0 ≤ u i) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hcount :
      ∀ j : ℕ, ∑ i ∈ S.filter (fun i ↦ u i < (j : ℝ) + 1), w i ≤ C * Real.exp (a * ((j : ℝ) + 1)))
    (j : ℕ) :
    ∑ i ∈ S.filter (fun i ↦ ⌊u i⌋₊ = j), w i * Real.exp (-u i) ≤
      C * Real.exp (1 / 2) * (Real.exp (-(1 / 2 : ℝ))) ^ j := by
  classical
  let B := S.filter (fun i ↦ ⌊u i⌋₊ = j)
  have hsub : B ⊆ S.filter (fun i ↦ u i < (j : ℝ) + 1) := by
    intro i hi
    have hb := Nat.lt_floor_add_one (u i)
    rw [(Finset.mem_filter.mp hi).2] at hb
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, hb⟩
  have hc :=
    (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i hi _ ↦ hw i (Finset.mem_filter.mp hi).1)).trans
      (hcount j)
  have hm :=
    mul_le_mul_of_nonneg_right ha
      (by linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)] : (0 : ℝ) ≤ j + 1)
  have hexp : Real.exp (a * ((j : ℝ) + 1) - j) ≤ Real.exp (1 / 2 - (j : ℝ) / 2) :=
    Real.exp_le_exp.mpr (by linarith only [hm])
  calc
    _ ≤ ∑ i ∈ B, Real.exp (-(j : ℝ)) * w i := by
      apply Finset.sum_le_sum
      intro i hi
      have hlow := Nat.floor_le (hu i (Finset.mem_filter.mp hi).1)
      rw [(Finset.mem_filter.mp hi).2] at hlow
      have he := Real.exp_le_exp.mpr (neg_le_neg hlow)
      have hp := mul_le_mul_of_nonneg_left he (hw i (Finset.mem_filter.mp hi).1)
      exact hp.trans_eq (mul_comm _ _)
    _ = Real.exp (-(j : ℝ)) * ∑ i ∈ B, w i := by rw [Finset.mul_sum]
    _ ≤ Real.exp (-(j : ℝ)) * (C * Real.exp (a * ((j : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = C * Real.exp (a * ((j : ℝ) + 1) - j) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ C * Real.exp (1 / 2 - (j : ℝ) / 2) := mul_le_mul_of_nonneg_left hexp hC
    _ = _ := by
      rw [show (1 / 2 - (j : ℝ) / 2) = 1 / 2 + (j : ℝ) * (-(1 / 2 : ℝ)) by ring, Real.exp_add,
        Real.exp_nat_mul]
      ring

/-- The positive absolute constant obtained by summing unit deficit bins with
ratio `exp(-1/2)` and allowing one unit of floor loss. It is independent of the
finite packet, density scale, and zero gap, and is used in exponential density sums. -/
noncomputable def exponentialHalfTailConstant : ℝ :=
  (Real.exp (1 / 2)) ^ 2 / (1 - Real.exp (-(1 / 2 : ℝ)))

/-- The exponential-bin tail constant is positive. Its numerator is positive
and its denominator is positive because `exp(-1/2) < 1`. This permits absorbing
it into the absolute density constant. -/
theorem exponentialHalfTailConstant_pos : 0 < exponentialHalfTailConstant := by
  apply div_pos (pow_pos (Real.exp_pos _) 2)
  have he : Real.exp (-(1 / 2 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num only)
  linarith only [he]

/-- For finite nonnegative weights on nonnegative deficits with a common lower
bound and exponential cumulative growth of rate at most one half, the negatively
exponential weighted sum decays by half that deficit gap. Partition by floors,
retain the lower index, and sum a geometric tail. No integral or multiplicity
separation is required. -/
theorem sum_exp_weight_of_count_growth_and_gap {ι : Type*} (S : Finset ι) (u w : ι → ℝ) {a C u₀ : ℝ}
    (ha : a ≤ 1 / 2) (hC : 0 ≤ C) (hu : ∀ i ∈ S, 0 ≤ u i) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hgap : ∀ i ∈ S, u₀ ≤ u i)
    (hcount :
      ∀ j : ℕ, ∑ i ∈ S.filter (fun i ↦ u i < (j : ℝ) + 1), w i ≤ C * Real.exp (a * ((j : ℝ) + 1))) :
    ∑ i ∈ S, w i * Real.exp (-u i) ≤ C * exponentialHalfTailConstant * Real.exp (-u₀ / 2) := by
  classical
  let J := S.image (fun i ↦ ⌊u i⌋₊)
  let K := ⌊u₀⌋₊
  let r := Real.exp (-(1 / 2 : ℝ))
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num only)
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hJ (j : ℕ) (hj : j ∈ J) : K ≤ j := by
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hj
    rw [← he]
    exact Nat.floor_mono (hgap i hi)
  have hgeo := sum_geometric_of_lower_index J K hr hr1 hJ
  have hfloor : (K : ℝ) + 1 > u₀ := Nat.lt_floor_add_one u₀
  have htail : r ^ K ≤ Real.exp (1 / 2) * Real.exp (-u₀ / 2) := by
    dsimp only [r]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hfloor])
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to (s := S) (t := J) (g := fun i ↦ ⌊u i⌋₊)
      (fun i hi ↦ Finset.mem_image_of_mem _ hi) (fun i ↦ w i * Real.exp (-u i))
  rw [← hfiber]
  calc
    _ ≤ ∑ j ∈ J, C * Real.exp (1 / 2) * r ^ j :=
      Finset.sum_le_sum (fun j _ ↦ sum_exp_weight_in_floor_bin S u w ha hC hu hw hcount j)
    _ = C * Real.exp (1 / 2) * ∑ j ∈ J, r ^ j := by rw [Finset.mul_sum]
    _ ≤ C * Real.exp (1 / 2) * (r ^ K / (1 - r)) :=
      mul_le_mul_of_nonneg_left hgeo (mul_nonneg hC (Real.exp_nonneg _))
    _ ≤ C * Real.exp (1 / 2) * ((Real.exp (1 / 2) * Real.exp (-u₀ / 2)) / (1 - r)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right htail hden.le)
        (mul_nonneg hC (Real.exp_nonneg _))
    _ = _ := by
      dsimp only [exponentialHalfTailConstant, r]
      ring

/-- For a finite nonnegative weighted packet with real parts between a fixed
threshold and `1-η`, an exponential tail-count bound of rate `Z` implies an
`x exp(-η log x/2)` bound when `log x ≥ 2Z` and `x > 1`. Scale deficits by `log x`,
apply the discrete exponential estimate, and keep the lower threshold using a
maximum. This transfers weighted log-free density to real-part power weights
without an additional logarithmic loss. -/
theorem sum_rpow_of_realpart_weighted_density {ι : Type*} (S : Finset ι) (β w : ι → ℝ)
    {x Z C σ₀ η : ℝ} (hx : 1 < x) (hZ : 0 ≤ Z) (hZx : 2 * Z ≤ Real.log x) (hC : 0 ≤ C)
    (hσ₀ : σ₀ ≤ 1) (hη : 0 ≤ η) (hw : ∀ i ∈ S, 0 ≤ w i) (hβlo : ∀ i ∈ S, σ₀ ≤ β i)
    (hβhi : ∀ i ∈ S, β i ≤ 1 - η)
    (hdensity :
      ∀ σ : ℝ,
        σ₀ ≤ σ → σ ≤ 1 → ∑ i ∈ S.filter (fun i ↦ σ ≤ β i), w i ≤ C * Real.exp (Z * (1 - σ))) :
    ∑ i ∈ S, w i * x ^ β i ≤
      C * exponentialHalfTailConstant * x * Real.exp (-η * Real.log x / 2) := by
  classical
  let Y := Real.log x
  let a := Z / Y
  let u := fun i ↦ Y * (1 - β i)
  have hY : 0 < Y := Real.log_pos hx
  have ha : a ≤ 1 / 2 := (div_le_iff₀ hY).mpr (by linarith only [hZx])
  have hu (i : ι) (hi : i ∈ S) : 0 ≤ u i := mul_nonneg hY.le (by linarith only [hβhi i hi, hη])
  have hgap (i : ι) (hi : i ∈ S) : η * Y ≤ u i := by
    have hm := mul_le_mul_of_nonneg_left (by linarith only [hβhi i hi] : η ≤ 1 - β i) hY.le
    simpa only [u, mul_comm] using hm
  have hcount (j : ℕ) :
    ∑ i ∈ S.filter (fun i ↦ u i < (j : ℝ) + 1), w i ≤ C * Real.exp (a * ((j : ℝ) + 1)) := by
    let σ := max σ₀ (1 - ((j : ℝ) + 1) / Y)
    have hj : 0 ≤ (j : ℝ) + 1 := by linarith only [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have hσ : σ ≤ 1 :=
      max_le hσ₀
        (by
          have hp := div_nonneg hj hY.le
          linarith only [hp])
    have hsub : S.filter (fun i ↦ u i < (j : ℝ) + 1) ⊆ S.filter (fun i ↦ σ ≤ β i) := by
      intro i hi
      have hsi := (Finset.mem_filter.mp hi).1
      have hui := (Finset.mem_filter.mp hi).2
      have hb : 1 - β i < ((j : ℝ) + 1) / Y :=
        (lt_div_iff₀ hY).mpr (by simpa only [u, mul_comm] using hui)
      exact Finset.mem_filter.mpr ⟨hsi, max_le (hβlo i hsi) (by linarith only [hb])⟩
    have hc :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun i hi _ ↦ hw i (Finset.mem_filter.mp hi).1)).trans
        (hdensity σ (le_max_left _ _) hσ)
    have hσlo : 1 - ((j : ℝ) + 1) / Y ≤ σ := le_max_right _ _
    have he : Z * (1 - σ) ≤ a * ((j : ℝ) + 1) := by
      have hm := mul_le_mul_of_nonneg_left (by linarith only [hσlo] : 1 - σ ≤ ((j : ℝ) + 1) / Y) hZ
      convert hm using 1
      dsimp only [a]
      ring
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC)
  have hsum := sum_exp_weight_of_count_growth_and_gap S u w ha hC hu hw hgap hcount
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hpower (i : ι) : x ^ β i = x * Real.exp (-u i) := by
    rw [Real.rpow_def_of_pos hxpos]
    calc
      _ = Real.exp (Real.log x) * Real.exp (-u i) := by
        rw [← Real.exp_add]
        congr 1
        dsimp only [u, Y]
        ring
      _ = _ := by rw [Real.exp_log hxpos]
  calc
    _ = x * ∑ i ∈ S, w i * Real.exp (-u i) := by
      rw [Finset.mul_sum]
      exact
        Finset.sum_congr rfl
          (fun i _ ↦ by
            rw [hpower]; ring)
    _ ≤ x * (C * exponentialHalfTailConstant * Real.exp (-(η * Y) / 2)) :=
      mul_le_mul_of_nonneg_left hsum hxpos.le
    _ = _ := by
      dsimp only [Y]
      rw [neg_mul]
      ring

end PseudoPrime.Analysis
