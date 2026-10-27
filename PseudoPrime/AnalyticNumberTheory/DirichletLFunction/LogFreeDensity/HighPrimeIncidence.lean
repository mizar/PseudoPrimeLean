/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerTailLargeSieve

/-! # High-prime detector incidence -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- The Boolean height-window incidence is true exactly when the physical
height distance satisfies its window bound. Unfold the Boolean choice.
This supplies the distance needed to activate a detector event in each fiber. -/
theorem heightWindowGridIncidence_eq_true_iff {α : Type*} (height : α → ℝ) (M W : ℕ) (x : α)
    (m : ℤ) :
    heightWindowGridIncidence height M W x m = true ↔
      |height x - (m : ℝ) / M| ≤ (W + 1 : ℝ) / M := by
  unfold heightWindowGridIncidence
  split
  · rename_i h
    exact iff_of_true rfl h
  · rename_i h
    exact iff_of_false (by decide) h

/-- For a primitive nonprincipal character and a near-one occurrence window,
bound each fiber by its local multiplicity majorant times the number of active order
events at that grid point. A nonempty fiber supplies an active event through its detector.
This applies to high-prime signals without requiring derivative large sets. -/
theorem primitiveCharacter_zero_window_fiber_le_order_event_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1) {σ η : ℝ}
    (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (T nmax M W : ℕ)
    (hwindow : (W + 1 : ℝ) / M ≤ η) (event : ℕ → ℤ → Prop) [∀ n, DecidablePred (event n)]
    (hdetector :
      ∀
        x ∈
          completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
            ((1 : ℂ) + (T : ℝ) * Complex.I),
        ∃ n ≤ nmax, ∀ j : ℤ, |x.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M → event n j)
    (m : ℤ) :
    ((completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I)).filter
          (fun x ↦ heightWindowGridIncidence (fun y ↦ y.1.im) M W x m = true)).card ≤
      Nat.ceil
          (completedZeroLocalLogBoundConstant *
            (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))) *
        (∑ n ∈ Finset.range (nmax + 1), if event n m then 1 else 0) := by
  classical
  let occ :=
    completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
      ((1 : ℂ) + (T : ℝ) * Complex.I)
  let fiber := occ.filter fun x ↦ heightWindowGridIncidence (fun y ↦ y.1.im) M W x m = true
  let weight :=
    completedZeroLocalLogBoundConstant * (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))
  have hlocal :=
    primitiveCharacter_zero_window_fiber_le_local_log_bound hq χ hχ hprim hinv hσ1
      (show 1 - σ ≤ (8 * η) / 8 by nlinarith only [hσeta]) (mul_pos (by norm_num only) hη)
      (show 8 * η ≤ 1 / 2 by nlinarith only [hηsmall]) T M W
      (show (W + 1 : ℝ) / M ≤ (8 * η) / 8 by nlinarith only [hwindow]) m
  have hreal : (fiber.card : ℝ) ≤ weight := by
    simpa only [fiber, occ, weight, mul_assoc] using hlocal
  have hbound : fiber.card ≤ Nat.ceil weight := by exact_mod_cast hreal.trans (Nat.le_ceil weight)
  apply card_le_bound_mul_order_event_sum fiber (Nat.ceil weight) nmax (fun n ↦ event n m) hbound
  intro hnonempty
  obtain ⟨x, hx⟩ := hnonempty
  obtain ⟨n, hn, hgrid⟩ := hdetector x (Finset.mem_filter.mp hx).1
  have hdist :=
    (heightWindowGridIncidence_eq_true_iff (fun y ↦ y.1.im) M W x m).mp (Finset.mem_filter.mp hx).2
  exact ⟨n, hn, hgrid m hdist⟩

/-- For a character's multiplicity-indexed occurrences and a shared window
detector, multiply the count by the grid-incidence gain and bound it by the weighted
order-event sum over the expanded grid. Double-count incidences using the local fiber
estimate. This retains multiplicities and every incident grid point. -/
theorem primitiveCharacter_zero_occurrences_window_mul_le_order_event_sum {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η) (event : ℕ → ℤ → Prop)
    [∀ n, DecidablePred (event n)]
    (hdetector :
      ∀
        x ∈
          completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
            ((1 : ℂ) + (T : ℝ) * Complex.I),
        ∃ n ≤ nmax, ∀ j : ℤ, |x.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M → event n j) :
    (completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
            ((1 : ℂ) + (T : ℝ) * Complex.I)).card *
        (2 * W + 1) ≤
      ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
        Nat.ceil
            (completedZeroLocalLogBoundConstant *
              (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))) *
          (∑ n ∈ Finset.range (nmax + 1), if event n m then 1 else 0) := by
  classical
  let occ :=
    completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
      ((1 : ℂ) + (T : ℝ) * Complex.I)
  let grid := Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ))
  let inc :
    (Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) → ℤ → Bool :=
    heightWindowGridIncidence (fun x ↦ x.1.im) M W
  let bound := fun m : ℤ ↦
    Nat.ceil
        (completedZeroLocalLogBoundConstant *
          (1 + 8 * η * Real.log ((q : ℝ) * (|((m : ℝ) / M)| + 3)))) *
      (∑ n ∈ Finset.range (nmax + 1), if event n m then 1 else 0)
  have hlower :=
    window_grid_incidence_card_lower_bound occ (fun x ↦ x.1.im) T M W hM
      (fun x hx ↦ completedZeroMultiplicityOccurrences_height_mem χ hχ σ T hx)
  have hupper : ∀ m ∈ grid, (occ.filter fun x ↦ inc x m = true).card ≤ bound m := by
    intro m hm
    exact
      primitiveCharacter_zero_window_fiber_le_order_event_sum hq χ hχ hprim hinv hσ1 hσeta hη
        hηsmall T nmax M W hwindow event hdetector m
  exact card_mul_le_sum_window_fiber_bounds occ grid inc (2 * W + 1) bound hlower hupper

/-- A nonprincipal character at a positive successor modulus has modulus at
least two. Modulus one has only the principal character.
This recovers the modulus hypothesis inside finite conductor-family sums. -/
theorem two_le_succ_modulus_of_nonprincipal (k : ℕ) (χ : DirichletCharacter ℂ (k + 1))
    (hχ : χ ≠ 1) : 2 ≤ k + 1 := by
  by_contra hmod
  have hle : k + 1 ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hmod)
  have heq : k + 1 = 1 := Nat.le_antisymm hle (Nat.succ_le_succ (Nat.zero_le k))
  have hsub : Subsingleton (DirichletCharacter ℂ (k + 1)) := by
    rw [heq]
    exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
  exact hχ (hsub.elim χ 1)

open Classical in
/-- For a primitive-family occurrence detector with arbitrary order events,
bound the occurrence count times its window gain by the conductor-character-grid sum
of local multiplicity weights times order-event counts. Inject each character's
occurrences into the family ledger and sum the per-character incidence inequalities.
This is the event-independent family interface for normalized high-prime counting. -/
theorem primitiveFamilyZeroOccurrence_mul_window_le_order_event_sum (Q : ℕ) {σ η : ℝ} (hσ1 : σ ≤ 1)
    (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (T nmax M W : ℕ) (hM : 0 < M)
    (hwindow : (W + 1 : ℝ) / M ≤ η)
    (event : (q : Fin Q) → DirichletCharacter ℂ (q.val + 1) → ℕ → ℤ → Prop)
    [∀ q χ n, DecidablePred (event q χ n)]
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax, ∀ j : ℤ, |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M → event x.1 x.2.1 n j) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) ≤
      ∑ q : Fin Q,
        ∑ χ : DirichletCharacter ℂ (q.val + 1),
          if _hχ : χ ≠ 1 then
            if _hprim : χ.IsPrimitive then
              ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
                (Nat.ceil
                      (completedZeroLocalLogBoundConstant *
                        (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) :
                    ℝ) *
                  (∑ n ∈ Finset.range (nmax + 1), if event q χ n m then (1 : ℝ) else 0)
            else 0
          else 0 := by
  unfold primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hqmem
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim]
      have hq : NeZero (q.val + 1) := ⟨Nat.succ_ne_zero q.val⟩
      have hcharDetector :
        ∀
          x ∈
            completedZeroMultiplicityOccurrences χ hχ ((σ : ℂ) - (T : ℝ) * Complex.I)
              ((1 : ℂ) + (T : ℝ) * Complex.I),
          ∃ n ≤ nmax, ∀ j : ℤ, |x.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M → event q χ n j := by
        intro x hx
        have hxledger :
          (⟨q, ⟨χ, x⟩⟩ :
              Σ q : Fin Q,
                Σ χ : DirichletCharacter ℂ (q.val + 1),
                  Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)) ∈
            primitiveCharacterFamilyZeroOccurrenceLedger Q σ T := by
          simp only [primitiveCharacterFamilyZeroOccurrenceLedger, Finset.mem_sigma,
            Finset.mem_univ, dite_eq_left hχ, dite_eq_left hprim]
          exact ⟨trivial, trivial, hx⟩
        exact hdetector hxledger
      have hchar :=
        @primitiveCharacter_zero_occurrences_window_mul_le_order_event_sum (q.val + 1) hq
          (two_le_succ_modulus_of_nonprincipal q.val χ hχ) χ hχ hprim (fun h ↦ hχ (inv_eq_one.mp h))
          σ η hσ1 hσeta hη hηsmall T nmax M W hM hwindow (event q χ) _ hcharDetector
      exact_mod_cast hchar
    · simp only [dite_eq_left hχ, dite_eq_right hprim, zero_mul]
      exact le_rfl
  · simp only [dite_eq_right hχ, zero_mul]
    exact le_rfl

/-- For a nonnegative normalization and threshold, an active norm event times
the squared threshold is bounded by the squared-normalized energy.
Square the event inequality; the inactive case is nonnegative.
This is the pointwise Markov inequality used without dropping detector normalization. -/
theorem norm_event_mul_sq_threshold_le (A B : ℝ) (z : ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    [Decidable (B ≤ A * ‖z‖)] : (if B ≤ A * ‖z‖ then (1 : ℝ) else 0) * B ^ 2 ≤ A ^ 2 * ‖z‖ ^ 2 := by
  by_cases h : B ≤ A * ‖z‖
  · rw [ite_eq_left h, one_mul, ← mul_pow]
    exact (sq_le_sq₀ hB (mul_nonneg hA (norm_nonneg z))).mpr h
  · rw [ite_eq_right h, zero_mul]
    exact mul_nonneg (sq_nonneg A) (sq_nonneg ‖z‖)

/-- For a finite family of complex values, multiply its large-value event count
by the squared threshold and bound it by squared-normalized energy.
Sum the pointwise norm-event inequality. This supplies the finite mean-square count. -/
theorem sum_norm_events_mul_sq_threshold_le {α : Type*} (s : Finset α) (f : α → ℂ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) [DecidablePred (fun x ↦ B ≤ A * ‖f x‖)] :
    (∑ x ∈ s, if B ≤ A * ‖f x‖ then (1 : ℝ) else 0) * B ^ 2 ≤ A ^ 2 * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_le_sum (fun x hx ↦ norm_event_mul_sq_threshold_le A B (f x) hA hB)

open Classical in
/-- The nonprincipal primitive event sum is at most the same norm-event sum over
all primitive characters. Expand the primitive filter and compare the principal branch.
This passes the occurrence family to the primitive-character mean-square range. -/
theorem nonprincipal_primitive_norm_event_sum_le (q : ℕ) (f : DirichletCharacter ℂ q → ℂ)
    (A B : ℝ) :
    (∑ χ : DirichletCharacter ℂ q,
        if _hχ : χ ≠ 1 then if _hp : χ.IsPrimitive then if B ≤ A * ‖f χ‖ then (1 : ℝ) else 0 else 0
        else 0) ≤
      ∑ χ ∈ primitiveDirichletCharacterSet q, if B ≤ A * ‖f χ‖ then (1 : ℝ) else 0 := by
  rw [primitiveDirichletCharacterSet, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro χ hmem
  by_cases hp : χ.IsPrimitive
  · by_cases hχ : χ ≠ 1
    · simp only [dite_eq_left hχ, dite_eq_left hp, ite_eq_left hp]
      exact le_rfl
    · simp only [dite_eq_right hχ, ite_eq_left hp]
      split <;> norm_num only
  · by_cases hχ : χ ≠ 1
    · simp only [dite_eq_left hχ, dite_eq_right hp, ite_eq_right hp]
      exact le_rfl
    · simp only [dite_eq_right hχ, ite_eq_right hp]
      exact le_rfl

open Classical in
/-- For a modulus greater than one and a finite prime-log polynomial, its
nonprincipal primitive event sum times the squared normalized threshold is bounded by
the squared normalization times the primitive mean square. Combine event inclusion and
finite Markov, then identify the coefficient polynomial.
This retains the exact factorial and near-one rate factors in family counting. -/
theorem primitive_prime_polynomial_event_sum_mul_sq_le (q : ℕ) (hq : 1 < q) (s : Finset ℕ) (r : ℕ)
    (σ t A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (∑ χ : DirichletCharacter ℂ q,
          if _hχ : χ ≠ 1 then
            if _hp : χ.IsPrimitive then
              if B ≤ A * ‖primeLogPowerPolynomial s r σ (fun k ↦ χ (k : ZMod q)) t‖ then (1 : ℝ)
              else 0
            else 0
          else 0) *
        B ^ 2 ≤
      A ^ 2 *
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun p ↦
            (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
              Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) := by
  have hevent :=
    mul_le_mul_of_nonneg_right
      (nonprincipal_primitive_norm_event_sum_le q
        (fun χ ↦ primeLogPowerPolynomial s r σ (fun k ↦ χ (k : ZMod q)) t) A B)
      (sq_nonneg B)
  have hmarkov :=
    sum_norm_events_mul_sq_threshold_le (primitiveDirichletCharacterSet q)
      (fun χ ↦ primeLogPowerPolynomial s r σ (fun k ↦ χ (k : ZMod q)) t) A B hA hB
  exact
    hevent.trans
      (by
        simpa only [primitiveCharacterPolynomialMeanSquare, primeLogPowerPolynomial,
          Complex.normSq_eq_norm_sq] using hmarkov)

open Classical in
/-- For an arbitrary occurrence detector and a globally bounded conductor-height
scale, replace every local multiplicity weight by one absolute ceiling constant.
Apply the family event incidence estimate and the expanded-grid local logarithm bound.
This isolates normalized high-prime event counts from local zero multiplicity. -/
theorem primitiveFamilyZeroOccurrence_mul_window_le_uniform_order_event_sum (Q : ℕ) (hQ : 0 < Q)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3)
    (event : (q : Fin Q) → DirichletCharacter ℂ (q.val + 1) → ℕ → ℤ → Prop)
    [∀ q χ n, DecidablePred (event q χ n)]
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax, ∀ j : ℤ, |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M → event x.1 x.2.1 n j) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) ≤
      (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
        (∑ q : Fin Q,
          ∑ χ : DirichletCharacter ℂ (q.val + 1),
            if _hχ : χ ≠ 1 then
              if _hprim : χ.IsPrimitive then
                ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
                  ∑ n ∈ Finset.range (nmax + 1), if event q χ n m then (1 : ℝ) else 0
              else 0
            else 0) := by
  have hinc :=
    primitiveFamilyZeroOccurrence_mul_window_le_order_event_sum Q hσ1 hσeta hη hηsmall T nmax M W hM
      (show (W + 1 : ℝ) / M ≤ η by nlinarith only [hwindow, hη]) event hdetector
  apply hinc.trans
  simp only [Finset.mul_sum, mul_dite, mul_zero]
  apply Finset.sum_le_sum
  intro q hqmem
  apply Finset.sum_le_sum
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hprim : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hprim]
      apply Finset.sum_le_sum
      intro m hm
      have hc :=
        completedZeroLocalLogBoundCeil_le_uniform_expanded_grid hQ hη hηsmall hM hwindow hglobal q m
          hm
      have hcreal :
        (Nat.ceil
              (completedZeroLocalLogBoundConstant *
                (1 + 8 * η * Real.log (((q.val + 1 : ℕ) : ℝ) * (|((m : ℝ) / M)| + 3)))) :
            ℝ) ≤
          (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) := by
        exact_mod_cast hc
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right hcreal (by split <;> norm_num only)
    · simp only [dite_eq_left hχ, dite_eq_right hprim]
      exact le_rfl
  · simp only [dite_eq_right hχ]
    exact le_rfl

/-- For a conductor-height family, common support, order range, and rational
mesh, sum normalized high-prime large-value indicators over primitive nonprincipal
characters, grid points, and orders. The threshold is shared while the normalization
depends on the order. This is the event sum bounded by primitive mean squares. -/
noncomputable def highPrimeFamilyGridEventSum (Q T nmax M W R cutoff : ℕ) (η B : ℝ) : ℝ := by
  classical
    exact
    ∑ q : Fin Q,
      ∑ χ : DirichletCharacter ℂ (q.val + 1),
        ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
          ∑ n ∈ Finset.range (nmax + 1),
            if _hχ : χ ≠ 1 then
              if _hp : χ.IsPrimitive then
                if
                    B ≤
                      (η ^ (n + 1) / (n.factorial : ℝ)) *
                        ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                            (fun k ↦ χ (k : ZMod (q.val + 1))) ((m : ℝ) / M)‖ then
                  (1 : ℝ)
                else 0
              else 0
            else 0

/-- For the same finite family and mesh, sum squared-normalized primitive prime
polynomial mean squares over admissible moduli, expanded grid points, and orders.
Modulus one contributes zero. This packages the mean-square side of zero incidence. -/
noncomputable def highPrimeFamilyGridMeanSquareSum (Q T nmax M W R cutoff : ℕ) (η : ℝ) : ℝ := by
  classical
    exact
    ∑ q : Fin Q,
      if hq : 1 < q.val + 1 then
        ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
          ∑ n ∈ Finset.range (nmax + 1),
            (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 *
              primitiveCharacterPolynomialMeanSquare (q.val + 1) hq (highPrimeEulerSupport R cutoff)
                (fun p ↦
                  (((Real.log p : ℝ) ^ (n + 1) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                    Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I))
      else 0

/-- Given a shared high-prime window detector on the multiplicity ledger, bound
the zero count times incidence gain by the absolute local constant times its event sum.
Instantiate the generic family-event estimate and distribute the character filters.
This connects actual high-prime signals to finite incidence counting. -/
theorem primitiveFamilyZeroOccurrence_mul_window_le_high_prime_events (Q : ℕ) (hQ : 0 < Q) {σ η : ℝ}
    (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W R cutoff : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) (B : ℝ)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax,
            ∀ j : ℤ,
              |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                B ≤
                  (η ^ (n + 1) / (n.factorial : ℝ)) *
                    ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                        (fun k ↦ x.2.1 (k : ZMod (x.1.val + 1))) ((j : ℝ) / M)‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) ≤
      (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
        highPrimeFamilyGridEventSum Q T nmax M W R cutoff η B := by
  classical
  have hinc :=
    primitiveFamilyZeroOccurrence_mul_window_le_uniform_order_event_sum Q hQ hσ1 hσeta hη hηsmall T
      nmax M W hM hwindow hglobal
      (fun q χ n j ↦
        B ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                (fun k ↦ χ (k : ZMod (q.val + 1))) ((j : ℝ) / M)‖)
      hdetector
  apply hinc.trans_eq
  unfold highPrimeFamilyGridEventSum
  congr 1
  apply Finset.sum_congr rfl
  intro q hqmem
  apply Finset.sum_congr rfl
  intro χ hχmem
  by_cases hχ : χ ≠ 1
  · by_cases hp : χ.IsPrimitive
    · simp only [dite_eq_left hχ, dite_eq_left hp]
    · simp only [dite_eq_left hχ, dite_eq_right hp, Finset.sum_const_zero]
  · simp only [dite_eq_right hχ, Finset.sum_const_zero]

/-- For a nonnegative rate and threshold, the family event sum times squared
threshold is at most the common-support mean-square sum. Interchange finite grid and
character sums, apply normalized Markov at each point, and remove the trivial modulus.
This supplies the large-value-to-hybrid mean-square connection. -/
theorem highPrimeFamilyGridEventSum_mul_sq_le_meanSquareSum (Q T nmax M W R cutoff : ℕ) (η B : ℝ)
    (hη : 0 ≤ η) (hB : 0 ≤ B) :
    highPrimeFamilyGridEventSum Q T nmax M W R cutoff η B * B ^ 2 ≤
      highPrimeFamilyGridMeanSquareSum Q T nmax M W R cutoff η := by
  classical
  simp only [highPrimeFamilyGridEventSum, highPrimeFamilyGridMeanSquareSum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hqmem
  by_cases hq : 1 < q.val + 1
  · rw [dite_eq_left hq, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro m hm
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro n hn
    rw [← Finset.sum_mul]
    exact
      primitive_prime_polynomial_event_sum_mul_sq_le (q.val + 1) hq (highPrimeEulerSupport R cutoff)
        n (1 + η) ((m : ℝ) / M) (η ^ (n + 1) / (n.factorial : ℝ)) B
        (div_nonneg (pow_nonneg hη (n + 1)) (Nat.cast_nonneg _)) hB
  · rw [dite_eq_right hq]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro χ hχmem
    have hqle : q.val + 1 ≤ 1 := Nat.le_of_not_gt hq
    have hqone : q.val + 1 = 1 := Nat.le_antisymm hqle (Nat.succ_le_succ (Nat.zero_le q.val))
    have hsub : Subsingleton (DirichletCharacter ℂ (q.val + 1)) := by
      rw [hqone]
      exact (inferInstance : Subsingleton (DirichletCharacter ℂ 1))
    have hχ : ¬χ ≠ 1 := fun h ↦ h (hsub.elim χ 1)
    simp only [dite_eq_right hχ, zero_mul, Finset.sum_const_zero]

/-- For the shared high-prime occurrence detector, multiply zero count and
incidence gain by squared signal and bound them by the normalized family mean square
times the local multiplicity constant. Combine incidence counting and finite Markov.
This is the multiplicity-preserving finite zero-density inequality. -/
theorem primitiveFamilyZeroOccurrence_mul_window_sq_signal_le_meanSquareSum (Q : ℕ) (hQ : 0 < Q)
    {σ η : ℝ} (hσ1 : σ ≤ 1) (hσeta : 1 - σ ≤ η) (hη : 0 < η) (hηsmall : η ≤ 1 / 1288)
    (T nmax M W R cutoff : ℕ) (hM : 0 < M) (hwindow : (W + 1 : ℝ) / M ≤ η / 8)
    (hglobal : η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3) (B : ℝ) (hB : 0 ≤ B)
    (hdetector :
      ∀
        {x :
          Σ q : Fin Q,
            Σ χ : DirichletCharacter ℂ (q.val + 1),
              Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)},
        x ∈ primitiveCharacterFamilyZeroOccurrenceLedger Q σ T →
          ∃ n ≤ nmax,
            ∀ j : ℤ,
              |x.2.2.1.im - (j : ℝ) / M| ≤ (W + 1 : ℝ) / M →
                B ≤
                  (η ^ (n + 1) / (n.factorial : ℝ)) *
                    ‖primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) n (1 + η)
                        (fun k ↦ x.2.1 (k : ZMod (x.1.val + 1))) ((j : ℝ) / M)‖) :
    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) * B ^ 2 ≤
      (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
        highPrimeFamilyGridMeanSquareSum Q T nmax M W R cutoff η := by
  have hinc :=
    mul_le_mul_of_nonneg_right
      (primitiveFamilyZeroOccurrence_mul_window_le_high_prime_events Q hQ hσ1 hσeta hη hηsmall T
        nmax M W R cutoff hM hwindow hglobal B hdetector)
      (sq_nonneg B)
  have hmean :=
    mul_le_mul_of_nonneg_left
      (highPrimeFamilyGridEventSum_mul_sq_le_meanSquareSum Q T nmax M W R cutoff η B hη.le hB)
      (Nat.cast_nonneg (Nat.ceil (49 * completedZeroLocalLogBoundConstant)))
  nlinarith only [hinc, hmean]

/-- Choose absolute rate and scale thresholds and fixed order envelopes so that
every admissible primitive-family occurrence count satisfies the normalized finite
mean-square inequality on one high-prime support and incidence mesh.
Use the actual completed-zero detector, preserving its support length and physical
incidence gain, then apply the zero-count-to-mean-square estimate.
This discharges detector hypotheses before the hybrid mean-square bound is inserted. -/
theorem exists_uniform_occurrence_prime_meanSquare_bound :
    ∃ η₀ : ℝ,
      0 < η₀ ∧
        ∃ R₀ Kmax nmax : ℕ,
          2 ≤ R₀ ∧
            2 ≤ Kmax ∧
            nmax = Kmax * completedLFunctionNearOneDetectorMultiplicityCap ∧
            ∀ (Q : ℕ) (σ : ℝ) (T : ℕ) (η : ℝ) (R Mmin : ℕ),
              0 < Q →
                σ ≤ 1 →
                1 - σ ≤ η →
                0 < η →
                η ≤ η₀ →
                R₀ ≤ R →
                η * Real.log (R : ℝ) ≤ 3 →
                η * Real.log ((Q : ℝ) * ((T : ℝ) + 3)) ≤ 3 →
                ∃ cutoff M W : ℕ,
                  R ^ 6 ≤ cutoff ∧
                    1 ≤ cutoff ∧
                    Mmin ≤ M ∧
                    0 < M ∧
                    (W + 1 : ℝ) / M ≤ η / 8 ∧
                    η * Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) /
                        (16 * primeLogPowerVariationBound nmax) ≤
                      (2 * W + 1 : ℝ) / M ∧
                    η * Real.log ((cutoff : ℝ) + 1) ≤
                      2 *
                          ((nmax : ℝ) + ordinaryLFunctionNearOneDetectorExponent * Kmax +
                            Real.log (24 * (Real.log 4 + 4))) +
                        η * Real.log ((R ^ 6 : ℕ) : ℝ) +
                        η * Real.log 3 ∧
                    primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight Q σ T * (2 * W + 1 : ℝ) *
                        (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) / 16) ^
                          2 ≤
                      (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
                        highPrimeFamilyGridMeanSquareSum Q T nmax M W R cutoff η := by
  obtain ⟨η₁, hη₁, R₀, Kmax, nmax, hR₀, hKmax, hnmax, hdetector⟩ :=
    exists_uniform_high_prime_mesh_for_family_occurrences
  refine ⟨min η₁ (1 / 1288), lt_min hη₁ (by norm_num only), R₀, Kmax, nmax, hR₀, hKmax, hnmax, ?_⟩
  intro Q σ T η R Mmin hQ hσ hσeta hη hηbound hRbound hRscale hglobal
  obtain ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, hsignal⟩ :=
    hdetector Q σ T η R Mmin hσ hσeta hη (hηbound.trans (min_le_left _ _)) hRbound hRscale hglobal
  refine ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, ?_⟩
  exact
    primitiveFamilyZeroOccurrence_mul_window_sq_signal_le_meanSquareSum Q hQ hσ hσeta hη
      (hηbound.trans (min_le_right _ _)) T nmax M W R cutoff hM hwidth hglobal
      (Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (Kmax : ℝ))) / 16)
      (div_nonneg (Real.exp_pos _).le (by norm_num only)) hsignal

/-- Reindex the first `Q` positive integers by `Fin Q`. The successor map is a
bijection onto `(0,Q]`. This identifies conductor sums with finite intervals. -/
theorem sum_fin_succ_eq_sum_Ioc_zero (Q : ℕ) (f : ℕ → ℝ) :
    (∑ q : Fin Q, f (q.val + 1)) = ∑ k ∈ Finset.Ioc 0 Q, f k := by
  apply Finset.sum_bij (fun q hq ↦ q.val + 1)
  · intro q hq
    exact Finset.mem_Ioc.mpr ⟨Nat.succ_pos q.val, Nat.succ_le_of_lt q.isLt⟩
  · intro a ha b hb hab
    exact Fin.ext (Nat.succ.inj hab)
  · intro k hk
    have hmem := Finset.mem_Ioc.mp hk
    have hlt : k - 1 < Q := (Nat.sub_lt hmem.1 Nat.zero_lt_one).trans_le hmem.2
    refine ⟨⟨k - 1, hlt⟩, Finset.mem_univ _, ?_⟩
    exact Nat.sub_add_cancel (Nat.succ_le_of_lt hmem.1)
  · intro q hq
    rfl

/-- For a positive conductor cap and a summand vanishing at one, remove conductor
one from the successor-indexed sum. Split the interval at one and use its zero term.
This prepares the primitive conductor interval. -/
theorem sum_fin_succ_eq_sum_Ioc_one (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ) (hf : f 1 = 0) :
    (∑ q : Fin Q, f (q.val + 1)) = ∑ k ∈ Finset.Ioc 1 Q, f k := by
  have hsplit :=
    Finset.sum_Ioc_consecutive f (show (0 : ℕ) ≤ 1 from Nat.zero_le 1) (Nat.succ_le_of_lt hQ)
  rw [Finset.sum_Ioc_succ_top (le_refl 0), Finset.Ioc_self, Finset.sum_empty, zero_add, hf,
    zero_add] at hsplit
  exact (sum_fin_succ_eq_sum_Ioc_zero Q f).trans hsplit.symm

/-- Reindex a symmetric integer window by a natural range of the same size.
Translate by the radius, using nonnegativity to invert the map with `Int.toNat`.
This converts physical height samples into the hybrid sieve grid convention. -/
theorem sum_int_Icc_symmetric_eq_sum_range (H : ℕ) (f : ℤ → ℝ) :
    (∑ m ∈ Finset.Icc (-(H : ℤ)) H, f m) = ∑ k ∈ Finset.range (2 * H + 1), f ((k : ℤ) - H) := by
  symm
  apply Finset.sum_bij (fun (k : ℕ) hk ↦ (k : ℤ) - H)
  · intro k hk
    have hkNat : k ≤ 2 * H := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkInt : (k : ℤ) ≤ 2 * H := by exact_mod_cast hkNat
    exact Finset.mem_Icc.mpr ⟨by linarith only [Int.natCast_nonneg k], by linarith only [hkInt]⟩
  · intro a ha b hb hab
    have he : (a : ℤ) = b := by linarith only [hab]
    exact_mod_cast he
  · intro m hm
    have hmem := Finset.mem_Icc.mp hm
    have hnonneg : 0 ≤ m + (H : ℤ) := by linarith only [hmem.1]
    have hcast : ((m + (H : ℤ)).toNat : ℤ) = m + H := Int.toNat_of_nonneg hnonneg
    have hle : (m + (H : ℤ)).toNat ≤ 2 * H := by
      have hInt : ((m + (H : ℤ)).toNat : ℤ) ≤ 2 * H := by
        rw [hcast]
        linarith only [hmem.2]
      exact_mod_cast hInt
    refine ⟨(m + (H : ℤ)).toNat, Finset.mem_range.mpr (Nat.lt_succ_of_le hle), ?_⟩
    rw [hcast]
    ring
  · intro k hk
    rfl

/-- For a positive family cap, write its grid mean square with the order outermost
and conductors in `(1,Q]`. Remove the zero conductor-one term and commute finite sums.
This exposes each fixed-order sum to the normalized hybrid grid estimate. -/
theorem highPrimeFamilyGridMeanSquareSum_eq_order_modulus_grid (Q T nmax M W R cutoff : ℕ)
    (hQ : 0 < Q) (η : ℝ) :
    highPrimeFamilyGridMeanSquareSum Q T nmax M W R cutoff η =
      ∑ n ∈ Finset.range (nmax + 1),
        (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 *
          ∑ q ∈ (Finset.Ioc 1 Q).attach,
            ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
              primitiveCharacterPolynomialMeanSquare q.val (Finset.mem_Ioc.mp q.property).1
                (highPrimeEulerSupport R cutoff)
                (fun p ↦
                  (((Real.log p : ℝ) ^ (n + 1) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                    Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I)) := by
  classical
  let F := fun k : ℕ ↦
    if hq : 1 < k then
      ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
        ∑ n ∈ Finset.range (nmax + 1),
          (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 *
            primitiveCharacterPolynomialMeanSquare k hq (highPrimeEulerSupport R cutoff)
              (fun p ↦
                (((Real.log p : ℝ) ^ (n + 1) : ℂ) *
                    Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                  Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I))
    else 0
  have hF : F 1 = 0 := by
    dsimp only [F]
    rw [dite_eq_right (by decide : ¬(1 : ℕ) < 1)]
  change (∑ q : Fin Q, F (q.val + 1)) = _
  rw [sum_fin_succ_eq_sum_Ioc_one Q hQ F hF, ← Finset.sum_attach (Finset.Ioc 1 Q) F]
  have hrewrite :
    (∑ q ∈ (Finset.Ioc 1 Q).attach, F q.val) =
      ∑ q ∈ (Finset.Ioc 1 Q).attach,
        ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
          ∑ n ∈ Finset.range (nmax + 1),
            (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 *
              primitiveCharacterPolynomialMeanSquare q.val (Finset.mem_Ioc.mp q.property).1
                (highPrimeEulerSupport R cutoff)
                (fun p ↦
                  (((Real.log p : ℝ) ^ (n + 1) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                    Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I)) := by
    apply Finset.sum_congr rfl
    intro q hqmem
    exact dite_eq_left (Finset.mem_Ioc.mp q.property).1
  rw [hrewrite]
  simp only [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext q
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]

/-- Replace conductors in `(1,R]` by the equivalent filtered interval `(1,R^2]`.
The inclusion uses `R ≤ R^2`; a value-preserving bijection handles proof arguments.
This matches the conductor domain of the high-prime hybrid estimate. -/
theorem sum_conductor_interval_eq_filtered_square (R : ℕ) (f : (q : ℕ) → 1 < q → ℝ) :
    (∑ q ∈ (Finset.Ioc 1 R).attach, f q.val (Finset.mem_Ioc.mp q.property).1) =
      ∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q ↦ q.val ≤ R),
        f q.val (Finset.mem_Ioc.mp q.property).1 := by
  classical
  have hR : R ≤ R ^ 2 := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) R
  apply
    Finset.sum_bij
      (fun q hq ↦
        (⟨q.val,
            Finset.mem_Ioc.mpr
              ⟨(Finset.mem_Ioc.mp q.property).1, (Finset.mem_Ioc.mp q.property).2.trans hR⟩⟩ :
          { q // q ∈ Finset.Ioc 1 (R ^ 2) }))
  · intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, (Finset.mem_Ioc.mp q.property).2⟩
  · intro a ha b hb hab
    apply Subtype.ext
    exact congrArg (fun (q : { q // q ∈ Finset.Ioc 1 (R ^ 2) }) ↦ q.val) hab
  · intro q hq
    have hcap := (Finset.mem_filter.mp hq).2
    refine
      ⟨⟨q.val, Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp q.property).1, hcap⟩⟩, Finset.mem_attach _ _,
        ?_⟩
    exact Subtype.ext rfl
  · intro q hq
    rfl

/-- For an integer radius and mesh denominator, express the symmetric height sum
as midpoint samples. Translate the integer indices and normalize the affine centers.
This matches the physical detection mesh to the hybrid grid convention. -/
theorem sum_integer_window_eq_midpoint_grid (H M : ℕ) (f : ℝ → ℝ) :
    (∑ m ∈ Finset.Icc (-(H : ℤ)) H, f ((m : ℝ) / M)) =
      ∑ k ∈ Finset.range (2 * H + 1), f (-((H : ℝ) + 1 / 2) / M + ((k : ℝ) + 1 / 2) * (1 / M)) := by
  rw [sum_int_Icc_symmetric_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  simp only [Int.cast_sub, Int.cast_natCast]
  ring

/-- Convert the expanded detection window to the midpoint grid with its exact
natural radius. Normalize the integer endpoints and apply symmetric reindexing.
This supplies the grid used by each fixed-order mean-square estimate. -/
theorem sum_expanded_height_window_eq_midpoint_grid (T M W : ℕ) (f : ℝ → ℝ) :
    (∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)), f ((m : ℝ) / M)) =
      ∑ k ∈ Finset.range (2 * (T * M + W + 1) + 1),
        f (-((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M + ((k : ℝ) + 1 / 2) * (1 / M)) := by
  have hleft : -(T * M : ℤ) - (W + 1 : ℤ) = -((T * M + W + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  have hright : (T * M : ℤ) + (W + 1 : ℤ) = ((T * M + W + 1 : ℕ) : ℤ) := by
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  rw [hleft, hright]
  exact sum_integer_window_eq_midpoint_grid (T * M + W + 1) M f

/-- For a positive mesh denominator and a window of width at most `η/8`, with
`η ≤ 1`, the midpoint grid stays in the height interval enlarged by one. Bound the
padding after clearing the positive denominator. This discharges the hybrid grid geometry. -/
theorem expanded_height_midpoint_grid_geometry (T M W : ℕ) (η : ℝ) (hM : 0 < M) (hη : η ≤ 1)
    (hwidth : ((W : ℝ) + 1) / M ≤ η / 8) :
    1 / (M : ℝ) ≤ η / 8 ∧
      -((T : ℝ) + 1) ≤ -((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M ∧
      -((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M + (2 * (T * M + W + 1) + 1 : ℕ) * (1 / (M : ℝ)) ≤
        (T : ℝ) + 1 := by
  have hMreal : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hstep : 1 / (M : ℝ) ≤ η / 8 :=
    (div_le_div_of_nonneg_right (le_add_of_nonneg_left (Nat.cast_nonneg W)) hMreal.le).trans hwidth
  have hsmall : ((W : ℝ) + 1) / M ≤ 1 / 8 :=
    hwidth.trans (div_le_div_of_nonneg_right hη (by norm_num only))
  have hmul := (div_le_iff₀ hMreal).mp hsmall
  have hpadding : (W : ℝ) + 1 + 1 / 2 ≤ M := by
    linarith only [hmul, (Nat.cast_nonneg W : (0 : ℝ) ≤ W)]
  have hbound : ((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M ≤ (T : ℝ) + 1 := by
    apply (div_le_iff₀ hMreal).mpr
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    nlinarith only [hpadding]
  refine ⟨hstep, ?_, ?_⟩
  · rw [neg_div]
    exact neg_le_neg hbound
  · have hend :
      -((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M + (2 * (T * M + W + 1) + 1 : ℕ) * (1 / (M : ℝ)) =
        ((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M := by
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hend]
    exact hbound

/-- For an admissible high-prime support, fixed order, and expanded height grid,
bound the normalized conductor mean square by the hybrid sieve. Reindex conductors
and physical samples without changing multiplicity or introducing a conductor factor.
The explicit endpoints are discharged by the mesh geometry lemma. -/
theorem highPrime_order_expanded_grid_hybrid_bound (R cutoff nmax r T M W : ℕ) (hR : 2 ≤ R)
    (hTupper : (T : ℝ) + 1 ≤ 2 * R) (ha : -((T : ℝ) + 1) ≤ -((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M)
    (hb :
      -((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M + (2 * (T * M + W + 1) + 1 : ℕ) * (1 / (M : ℝ)) ≤
        (T : ℝ) + 1)
    (η c₁ : ℝ) (K : ℕ) (hM : 0 < M) (hη : 0 < η) (hηsmall : 2 * η ≤ 1) (hc₁ : 0 ≤ c₁)
    (hhη : 1 / (M : ℝ) ≤ η / 8) (hlogX : η * Real.log ((cutoff : ℝ) + 1) ≤ c₁ * K) (hr : r ≤ nmax)
    (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ)) :
    (η ^ (r + 1) / (r.factorial : ℝ)) ^ 2 * ((1 / (M : ℝ)) / 2) *
        (∑ q ∈ (Finset.Ioc 1 R).attach,
          ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
            primitiveCharacterPolynomialMeanSquare q.val (Finset.mem_Ioc.mp q.property).1
              (highPrimeEulerSupport R cutoff)
              (fun p ↦
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                    Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                  Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I))) ≤
      (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) *
        (((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) *
          ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log ((R ^ 6 : ℕ) : ℝ))))) := by
  have hgrid :=
    highPrimeEulerSupport_grid_hybrid_normalized_bound R cutoff nmax r hR ((T : ℝ) + 1)
      (le_add_of_nonneg_left (Nat.cast_nonneg T)) hTupper (-((T * M + W + 1 : ℕ) + (1 / 2 : ℝ)) / M)
      (1 / M) (2 * (T * M + W + 1) + 1) (one_div_pos.mpr (Nat.cast_pos.mpr hM)) ha hb η c₁ K hη
      hηsmall hc₁ hhη hlogX hr hlarge
  rw [sum_conductor_interval_eq_filtered_square R
      (fun q hq ↦
        ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
          primitiveCharacterPolynomialMeanSquare q hq (highPrimeEulerSupport R cutoff)
            (fun p ↦
              (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                  Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I)))]
  conv_lhs =>
    arg 2
    arg 2
    ext q
    rw [sum_expanded_height_window_eq_midpoint_grid T M W
        (fun t ↦
          primitiveCharacterPolynomialMeanSquare q.val (Finset.mem_Ioc.mp q.property).1
            (highPrimeEulerSupport R cutoff)
            (fun p ↦
              (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                  Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)))]
  exact hgrid

/-- For an admissible near-one scale and physical mesh, bound the actual family
grid mean square after multiplying by half the mesh step. Apply the fixed-order
hybrid estimate and sum over the shared order envelope. This supplies the upper
bound paired with the multiplicity-preserving zero-incidence lower bound. -/
theorem highPrimeFamilyGridMeanSquareSum_hybrid_bound (R cutoff nmax T M W : ℕ) (hR : 2 ≤ R)
    (hT : T ≤ R) (η c₁ : ℝ) (K : ℕ) (hM : 0 < M) (hη : 0 < η) (hηsmall : 2 * η ≤ 1) (hc₁ : 0 ≤ c₁)
    (hwidth : ((W : ℝ) + 1) / M ≤ η / 8) (hlogX : η * Real.log ((cutoff : ℝ) + 1) ≤ c₁ * K)
    (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ)) :
    highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η * ((1 / (M : ℝ)) / 2) ≤
      (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) *
        ∑ r ∈ Finset.range (nmax + 1),
          (((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) *
            ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log ((R ^ 6 : ℕ) : ℝ))))) := by
  have hηone : η ≤ 1 := by linarith only [hηsmall, hη]
  obtain ⟨hstep, ha, hb⟩ := expanded_height_midpoint_grid_geometry T M W η hM hηone hwidth
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast ((by decide : 1 ≤ 2).trans hR)
  have hTreal : (T : ℝ) ≤ R := by exact_mod_cast hT
  have hTupper : (T : ℝ) + 1 ≤ 2 * R := by linarith only [hTreal, hRreal]
  rw [highPrimeFamilyGridMeanSquareSum_eq_order_modulus_grid R T nmax M W R cutoff
      (Nat.zero_lt_of_lt hR) η,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r hr
  have hrle := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hbound :=
    highPrime_order_expanded_grid_hybrid_bound R cutoff nmax r T M W hR hTupper ha hb η c₁ K hM hη
      hηsmall hc₁ hstep hlogX hrle hlarge
  calc
    _ =
        (η ^ (r + 1) / (r.factorial : ℝ)) ^ 2 * ((1 / (M : ℝ)) / 2) *
          (∑ q ∈ (Finset.Ioc 1 R).attach,
            ∑ m ∈ Finset.Icc (-(T * M : ℤ) - (W + 1 : ℤ)) ((T * M : ℤ) + (W + 1 : ℤ)),
              primitiveCharacterPolynomialMeanSquare q.val (Finset.mem_Ioc.mp q.property).1
                (highPrimeEulerSupport R cutoff)
                (fun p ↦
                  (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                    Complex.exp ((-(((m : ℝ) / M) * Real.log p) : ℝ) * Complex.I))) :=
      by ring
    _ ≤ _ := hbound

/-- For a shared order cap, collect the fixed nonnegative coefficient-energy factors
of the high-prime hybrid bound. The finite sum is independent of conductor and height.
This constant controls the summed-order detector. -/
noncomputable def highPrimeOrderEnvelopeEnergy (nmax : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (nmax + 1),
    ((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) * ((3 / 2 : ℝ) * (Real.log 4 + 4))

/-- Each order-energy summand is nonnegative. Apply positivity termwise; this
allows multiplication of subsequent sampling estimates by the envelope energy. -/
theorem highPrimeOrderEnvelopeEnergy_nonneg (nmax : ℕ) : 0 ≤ highPrimeOrderEnvelopeEnergy nmax := by
  apply Finset.sum_nonneg
  intro r hr
  exact
    mul_nonneg
      (mul_nonneg (add_nonneg (Nat.cast_nonneg r) zero_le_one) (pow_nonneg (by norm_num only) _))
      (mul_nonneg (by norm_num only)
        (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)))

/-- For a nonnegative rate and positive conductor scale, discard the decaying
Chernoff exponential from the order sum. Bound each term by its fixed energy factor.
This makes the hybrid energy independent of the conductor scale. -/
theorem highPrime_grid_energy_sum_le (nmax R : ℕ) (η : ℝ) (hη : 0 ≤ η) (hR : 1 ≤ R) :
    (∑ r ∈ Finset.range (nmax + 1),
        (((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) *
          ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log ((R ^ 6 : ℕ) : ℝ)))))) ≤
      highPrimeOrderEnvelopeEnergy nmax := by
  have hexp : Real.exp (-(η * Real.log ((R ^ 6 : ℕ) : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (mul_nonneg hη (Real.log_nonneg (by exact_mod_cast Nat.one_le_pow 6 R hR))))
  apply Finset.sum_le_sum
  intro r hr
  have hnonneg : 0 ≤ ((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) * ((3 / 2 : ℝ) * (Real.log 4 + 4)) :=
    mul_nonneg
      (mul_nonneg (add_nonneg (Nat.cast_nonneg r) zero_le_one) (pow_nonneg (by norm_num only) _))
      (mul_nonneg (by norm_num only)
        (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)))
  simpa only [mul_assoc, mul_one] using mul_le_mul_of_nonneg_left hexp hnonneg

/-- Given a zero-incidence lower bound and a mesh-scaled mean-square upper bound,
solve for the count using the positive signal and window factors. Explicit division
isolates the sampling loss. This prepares cancellation at the boundary scale. -/
theorem count_le_sampling_loss_of_meanSquare (N w B L S H M logR : ℝ) (hw : 0 < w) (hB : 0 < B)
    (hL : 0 ≤ L) (hM : 0 < M) (hcount : N * w * B ^ 2 ≤ L * S)
    (hmean : S * ((1 / M) / 2) ≤ H / logR) : N ≤ (L * H / B ^ 2) * (2 * M / (w * logR)) := by
  have hmean' : S / (2 * M) ≤ H / logR := by
    convert hmean using 1
    ring
  have hS : S ≤ H / logR * (2 * M) := (div_le_iff₀ (mul_pos (by norm_num only) hM)).mp hmean'
  have hNS : N * w * B ^ 2 ≤ L * (H / logR * (2 * M)) :=
    hcount.trans (mul_le_mul_of_nonneg_left hS hL)
  have hN : N ≤ L * (H / logR * (2 * M)) / (w * B ^ 2) :=
    (le_div_iff₀ (mul_pos hw (sq_pos_of_pos hB))).mpr (by simpa only [mul_assoc] using hNS)
  calc
    N ≤ _ := hN
    _ = _ := by ring

/-- At the boundary scale, a multiplicity-preserving detector mean-square lower
bound implies an absolute count bound. Apply the actual hybrid family estimate,
discard the decaying energy tail, and cancel mesh density and the logarithm using
the physical incidence gain. This closes the fixed-envelope counting inequality. -/
theorem highPrime_boundary_count_le_of_meanSquare (N η D c₁ : ℝ) (Kmax nmax R cutoff T M W : ℕ)
    (hR : 2 ≤ R) (hT : T ≤ R) (hM : 0 < M) (hη : 0 < η) (hηsmall : 2 * η ≤ 1) (hc₁ : 0 ≤ c₁)
    (hwidth : ((W : ℝ) + 1) / M ≤ η / 8) (hboundary : η * Real.log (R : ℝ) = 1)
    (hgain :
      η * Real.exp (-(D * (Kmax : ℝ))) / (16 * primeLogPowerVariationBound nmax) ≤
        (2 * W + 1 : ℝ) / M)
    (hlogX : η * Real.log ((cutoff : ℝ) + 1) ≤ c₁ * Kmax)
    (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ))
    (hcount :
      N * (2 * W + 1 : ℝ) * (Real.exp (-(D * Kmax)) / 16) ^ 2 ≤
        (Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
          highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η) :
    N ≤
      ((Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
            (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) /
          (Real.exp (-(D * Kmax)) / 16) ^ 2) *
        (32 * primeLogPowerVariationBound nmax * Real.exp (D * Kmax)) := by
  have hlog : 0 < Real.log (R : ℝ) := Real.log_pos (by exact_mod_cast hR)
  have hH : 0 ≤ 4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax :=
    mul_nonneg
      (mul_nonneg (by norm_num only)
        (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only))))
      (highPrimeOrderEnvelopeEnergy_nonneg nmax)
  have hhybrid :=
    highPrimeFamilyGridMeanSquareSum_hybrid_bound R cutoff nmax T M W hR hT η c₁ Kmax hM hη hηsmall
      hc₁ hwidth hlogX hlarge
  have hfactor : 0 ≤ (4096 : ℝ) / Real.log R * (1 + (c₁ * Kmax / 8) ^ 2 / 2) :=
    mul_nonneg (div_nonneg (by norm_num only) hlog.le)
      (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only)))
  have henergy :=
    mul_le_mul_of_nonneg_left
      (highPrime_grid_energy_sum_le nmax R η hη.le ((by decide : 1 ≤ 2).trans hR)) hfactor
  have hmean :
    highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η * ((1 / (M : ℝ)) / 2) ≤
      (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) / Real.log R := by
    convert hhybrid.trans henergy using 1
    ring
  have hraw :=
    count_le_sampling_loss_of_meanSquare N (2 * W + 1) (Real.exp (-(D * Kmax)) / 16)
      (Nat.ceil (49 * completedZeroLocalLogBoundConstant))
      (highPrimeFamilyGridMeanSquareSum R T nmax M W R cutoff η)
      (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) M (Real.log R)
      (add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg W))
        zero_lt_one)
      (div_pos (Real.exp_pos _) (by norm_num only)) (Nat.cast_nonneg _) (Nat.cast_pos.mpr hM) hcount
      hmean
  exact
    hraw.trans
      (mul_le_mul_of_nonneg_left
        (mesh_hybrid_sampling_loss_le_at_boundary_scale η D Kmax nmax R M W hη hM hboundary hgain)
        (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) (sq_nonneg _)))

/-- At the boundary scale and for heights at most the conductor cap, the global
near-one detector budget is automatic once `R ≥ 3`. Compare the height product with
`R^3` and multiply logarithms by the nonnegative scale. This removes the global
scale hypothesis from the final boundary-count theorem. -/
theorem boundary_scale_global_height_bound (R T : ℕ) (hR : 3 ≤ R) (hT : T ≤ R) (η : ℝ) (hη : 0 ≤ η)
    (hboundary : η * Real.log (R : ℝ) = 1) : η * Real.log ((R : ℝ) * ((T : ℝ) + 3)) ≤ 3 := by
  have hRreal : (3 : ℝ) ≤ R := by exact_mod_cast hR
  have hTreal : (T : ℝ) ≤ R := by exact_mod_cast hT
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num only) hRreal
  have harg : (R : ℝ) * ((T : ℝ) + 3) ≤ (R : ℝ) ^ 3 := by
    nlinarith only [hRreal, hTreal, sq_nonneg ((R : ℝ) - 3)]
  have hlog :=
    Real.log_le_log
      (mul_pos hRpos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg T) (by norm_num only))) harg
  rw [Real.log_pow] at hlog
  have hscaled := mul_le_mul_of_nonneg_left hlog hη
  norm_num only [Nat.cast_ofNat] at hscaled
  nlinarith only [hscaled, hboundary]

/-- There are absolute constants bounding the actual multiplicity-indexed primitive
family count in every boundary strip `1-σ ≤ η`, `η log R = 1`, for all sufficiently
large conductor caps and heights at most the cap. Choose the common detector mesh,
apply the hybrid sieve, and cancel the physical-window sampling loss. All detector,
cutoff, order, and small-scale budgets are discharged. This is the critical-strip
part of the log-free density argument, rather than the full-width density estimate. -/
theorem exists_primitiveFamily_boundary_scale_count_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ (R T : ℕ) (σ η : ℝ),
              R₀ ≤ R →
                T ≤ R →
                σ ≤ 1 →
                1 - σ ≤ η →
                0 < η →
                η * Real.log (R : ℝ) = 1 →
                primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight R σ T ≤ C := by
  obtain ⟨η₀, hη₀, R₁, Kmax, nmax, hR₁, hKmax, hnmax, hdetector⟩ :=
    exists_uniform_occurrence_prime_meanSquare_bound
  let D := ordinaryLFunctionNearOneDetectorExponent
  let c₁ :=
    2 *
        ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + D +
          Real.log (24 * (Real.log 4 + 4))) +
      18 +
      Real.log 3
  let B :=
    ((Nat.ceil (49 * completedZeroLocalLogBoundConstant) : ℝ) *
          (4096 * (1 + (c₁ * Kmax / 8) ^ 2 / 2) * highPrimeOrderEnvelopeEnergy nmax) /
        (Real.exp (-(D * Kmax)) / 16) ^ 2) *
      (32 * primeLogPowerVariationBound nmax * Real.exp (D * Kmax))
  have hc₁ : 0 ≤ c₁ := by
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
    have hL : 0 ≤ Real.log (24 * (Real.log 4 + 4)) := Real.log_nonneg (by nlinarith only [hlog4])
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num only)
    dsimp only [c₁, D]
    linarith only [hL, hlog3, ordinaryLFunctionNearOneDetectorExponent_nonneg,
      (Nat.cast_nonneg completedLFunctionNearOneDetectorMultiplicityCap :
        (0 : ℝ) ≤ completedLFunctionNearOneDetectorMultiplicityCap)]
  have hlogdiv : Filter.Tendsto (fun R : ℕ ↦ Real.log (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨R₂, hR₂⟩ :=
    Filter.eventually_atTop.mp
      (hlogdiv.eventually
        (Filter.eventually_ge_atTop (max (1 / min η₀ (1 / 1288)) (((2 * nmax + 1 : ℕ) : ℝ) / 6))))
  refine
    ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), max 3 (max R₁ R₂), le_max_left _ _, ?_⟩
  intro R T σ η hR hT hσ hση hη hboundary
  have hRthree : 3 ≤ R := (le_max_left _ _).trans hR
  have hRone : R₁ ≤ R := (le_max_left R₁ R₂).trans ((le_max_right _ _).trans hR)
  have hRtwo : R₂ ≤ R := (le_max_right R₁ R₂).trans ((le_max_right _ _).trans hR)
  have hlogbound := hR₂ R hRtwo
  have hηcap : η ≤ min η₀ (1 / 1288) := by
    have hcap : 0 < min η₀ (1 / 1288) := lt_min hη₀ (by norm_num only)
    have hscaled := mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hlogbound) hη.le
    have hquot : η / min η₀ (1 / 1288) ≤ 1 := by simpa only [mul_one_div, hboundary] using hscaled
    exact (div_le_iff₀ hcap).mp hquot |>.trans_eq (one_mul _)
  have hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ) := by
    have h := (le_max_right _ _).trans hlogbound
    linarith only [h]
  have hscale : η * Real.log (R : ℝ) ≤ 3 := by
    rw [hboundary]
    norm_num only
  have hglobal := boundary_scale_global_height_bound R T hRthree hT η hη.le hboundary
  obtain ⟨cutoff, M, W, hcutoff, hcutpos, hMmin, hM, hwidth, hgain, hlog, hcount⟩ :=
    hdetector R σ T η R 1 (lt_of_lt_of_le (by decide : 0 < 3) hRthree) hσ hση hη
      (hηcap.trans (min_le_left _ _)) hRone hscale hglobal
  have hlogX :=
    cutoff_log_le_uniform_detector_order η D Kmax nmax R cutoff
      completedLFunctionNearOneDetectorMultiplicityCap ((by decide : 1 ≤ 2).trans hKmax)
      (le_of_eq hnmax) ((hηcap.trans (min_le_right _ _)).trans (by norm_num only)) hscale hlog
  have hηsmall : 2 * η ≤ 1 := by
    have h := hηcap.trans (min_le_right _ _)
    linarith only [h]
  have hbound :=
    highPrime_boundary_count_le_of_meanSquare
      (primitiveCharacterFamilyZeroOccurrenceCountAtNatHeight R σ T) η D c₁ Kmax nmax R cutoff T M W
      ((by decide : 2 ≤ 3).trans hRthree) hT hM hη hηsmall hc₁ hwidth hboundary hgain hlogX hlarge
      hcount
  exact hbound.trans (le_max_left _ _)

/-- The existing primitive-family zero count satisfies the absolute boundary-strip
bound. Rewrite it as the occurrence count and apply the multiplicity-preserving
counting theorem. This transfers the analytic result to the established counting API. -/
theorem exists_primitiveCharacterFamily_boundary_scale_count_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ (R T : ℕ) (σ η : ℝ),
              R₀ ≤ R →
                T ≤ R →
                σ ≤ 1 →
                1 - σ ≤ η →
                0 < η →
                η * Real.log (R : ℝ) = 1 →
                primitiveCharacterFamilyZeroCountAtNatHeight R σ T ≤ C := by
  obtain ⟨C, hC, R₀, hR₀, hcount⟩ := exists_primitiveFamily_boundary_scale_count_bound
  refine ⟨C, hC, R₀, hR₀, ?_⟩
  intro R T σ η hR hT hσ hση hη hboundary
  rw [primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceCount]
  exact hcount R T σ η hR hT hσ hση hη hboundary

/-- For all sufficiently large diagonal cutoffs, the existing primitive-family
zero count is uniformly bounded throughout the critical strip of width `1/log R`.
Set the detector scale to the reciprocal logarithm and use the boundary-count
theorem. This supplies the narrow-strip part of the full log-free density target. -/
theorem exists_primitiveCharacterFamily_critical_strip_count_bound :
    ∃ C : ℝ,
      0 < C ∧
        ∃ R₀ : ℕ,
          3 ≤ R₀ ∧
            ∀ (R : ℕ) (σ : ℝ),
              R₀ ≤ R →
                1 - 1 / Real.log (R : ℝ) ≤ σ →
                σ ≤ 1 → primitiveCharacterFamilyZeroCount R σ ≤ C := by
  obtain ⟨C, hC, R₀, hR₀, hcount⟩ := exists_primitiveCharacterFamily_boundary_scale_count_bound
  refine ⟨C, hC, R₀, hR₀, ?_⟩
  intro R σ hR hσlower hσupper
  have hlog : 0 < Real.log (R : ℝ) :=
    Real.log_pos
      (by
        have hthree := hR₀.trans hR
        exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 3) hthree))
  have hση : 1 - σ ≤ 1 / Real.log (R : ℝ) := by linarith only [hσlower]
  have hboundary : (1 / Real.log (R : ℝ)) * Real.log R = 1 := one_div_mul_cancel (ne_of_gt hlog)
  have h :=
    hcount R R σ (1 / Real.log R) hR (le_refl R) hσupper hση (one_div_pos.mpr hlog) hboundary
  exact h

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
