/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ShiftedZeros
public import PseudoPrime.LLS.MellinKernelZeta
public import PseudoPrime.Analysis.FiniteSumExhaustion

/-!
# Concrete xi ledgers for principal Mellin contours

Compact zero finiteness supplies the finite shifted singularity ledger.
Diverging heights exhaust the singularities and identify the infinite residue limit.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- In a closed rectangle, shifted xi zeros together with the kernel pole form a
finite set. Compact shifted-zero finiteness and a singleton union give the ledger.
This certifies the concrete finite contour without additional finiteness assumptions. -/
theorem finite_xiKernelSingularities (z w : ℂ) :
    {s ∈ Rectangle.rectangleClosedBox z w | s = -1 / 2 ∨ riemannXi (s + 1 / 2) = 0}.Finite := by
  have hf := finite_shifted_zeros (Rectangle.isCompact_rectangleClosedBox z w)
  apply (hf.union (Set.finite_singleton (-1 / 2 : ℂ))).subset
  intro s hs
  rcases hs.2 with hp | hz
  · exact Or.inr hp
  · exact Or.inl ⟨hs.1, hz⟩

/-- The finite ledger of shifted xi zeros and the possible kernel pole in a closed
rectangle. Its membership records both the geometric bounds and singularity condition.
This ledger indexes principal-character Mellin residues. -/
noncomputable def xiKernelSingularities (z w : ℂ) : Finset ℂ :=
  (finite_xiKernelSingularities z w).toFinset

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- Membership in the xi kernel ledger is closed rectangle membership together
with the kernel-pole or shifted-xi-zero condition. Unfold the finite-set conversion.
This supplies the covering and geometric conditions in the finite contour theorem. -/
theorem mem_xiKernelSingularities {z w s : ℂ} :
    s ∈ xiKernelSingularities z w ↔
      s ∈ Rectangle.rectangleClosedBox z w ∧ (s = -1 / 2 ∨ riemannXi (s + 1 / 2) = 0) := by
  simp only [xiKernelSingularities, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- For a positive scale, an ordered rectangle in the kernel strip, and an interior
xi kernel ledger, the weighted xi boundary integral equals its finite residue sum.
The concrete ledger automatically supplies closed membership and covers singularities.
This prepares the finite principal contour for good-height exhaustion. -/
theorem xiKernelFiniteContourIdentity (K : MellinKernel) {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hregion : Rectangle.rectangleClosedBox z w ⊆ K.region)
    (hopen : ∀ s ∈ xiKernelSingularities z w, s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral
        (fun s => -logDeriv riemannXi (s + 1 / 2) * (K.function s * (x : ℂ) ^ s)) z w =
      ∑ s ∈ xiKernelSingularities z w,
        2 * Real.pi * Complex.I * weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s := by
  apply xiFiniteContourIdentity K hx hre him hregion (xiKernelSingularities z w)
  · exact fun s hs => (mem_xiKernelSingularities.mp hs).1
  · exact hopen
  · exact fun s hs hz => mem_xiKernelSingularities.mpr ⟨hs, hz⟩

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, every shifted xi zero and the kernel pole eventually belongs to
symmetric rectangle ledgers along any height sequence tending to infinity, with
left edge below minus one half and positive right edge. RH fixes real coordinates;
the diverging height eventually exceeds the absolute ordinate. No monotonicity is
required. This supplies residue-ledger exhaustion. -/
theorem eventually_mem_xiKernelSingularities (hRH : RiemannHypothesis) {T : ℕ → ℝ}
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) {a b : ℝ} (ha : a < -1 / 2) (hb : 0 < b)
    {s : ℂ} (hs : s = -1 / 2 ∨ riemannXi (s + 1 / 2) = 0) :
    ∀ᶠ n in Filter.atTop,
      s ∈ xiKernelSingularities ((a : ℂ) - T n * Complex.I) ((b : ℂ) + T n * Complex.I) := by
  have hsr : s.re = -1 / 2 ∨ s.re = 0 := by
    rcases hs with he | hz
    · exact
        Or.inl
          (by
            rw [he]; norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re])
    · have hr := riemannXi_zero_re_eq_half_of_riemannHypothesis hRH hz
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re] at hr
      exact Or.inr (by linarith only [hr])
  filter_upwards [hT.eventually_gt_atTop |s.im|] with n hn
  apply mem_xiKernelSingularities.mpr
  refine ⟨?_, hs⟩
  have ht : 0 ≤ T n := (abs_nonneg s.im).trans hn.le
  change s.re ∈ Set.uIcc _ _ ∧ s.im ∈ Set.uIcc _ _
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, zero_add, sub_zero, zero_sub]
  rw [Set.uIcc_of_le (by linarith only [ha, hb]), Set.uIcc_of_le (neg_le_self ht)]
  constructor
  · rcases hsr with he | he <;> rw [he] <;> constructor <;> linarith only [ha, hb]
  · exact ⟨by linarith only [neg_abs_le s.im, hn], (le_abs_self s.im).trans hn.le⟩

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- Xi zeros whose shifted coordinates lie in a closed rectangle form a finite set.
The coordinate map is injective, and its image lies in the finite kernel ledger.
This supplies zero-subtype finite sums matching the absolutely convergent series. -/
theorem finite_xiZerosInRectangle (z w : ℂ) :
    {ρ : Zero | (ρ : ℂ) - 1 / 2 ∈ Rectangle.rectangleClosedBox z w}.Finite := by
  have hi : Function.Injective (fun ρ : Zero => (ρ : ℂ) - 1 / 2) := by
    intro ρ τ h
    exact Subtype.ext (sub_left_injective h)
  have hf := (finite_xiKernelSingularities z w).preimage hi.injOn
  apply hf.subset
  intro ρ hρ
  exact ⟨hρ, Or.inr (by simpa only [sub_add_cancel] using ρ.property)⟩

open AnalyticNumberTheory.RiemannXi in
/-- The finite set of xi zeros with shifted coordinates in the closed rectangle.
These zero-subtype indices retain multiplicities through the kernel zero term.
The finite sets exhaust the principal-character zero series as heights grow. -/
noncomputable def xiZerosInRectangle (z w : ℂ) : Finset Zero :=
  (finite_xiZerosInRectangle z w).toFinset

open AnalyticNumberTheory AnalyticNumberTheory.RiemannXi in
/-- Membership in the finite xi zero set is closed rectangle membership of its
shifted coordinate. Unfold the certified finite-set conversion. This connects
singularity-ledger exhaustion to the zero-subtype series. -/
theorem mem_xiZerosInRectangle {z w : ℂ} {ρ : Zero} :
    ρ ∈ xiZerosInRectangle z w ↔ (ρ : ℂ) - 1 / 2 ∈ Rectangle.rectangleClosedBox z w := by
  simp only [xiZerosInRectangle, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, each xi zero eventually enters the zero-subtype finite rectangles
along any height sequence tending to infinity. Translate the zero, apply the proved
singularity-ledger exhaustion, and retain its closed membership. This discharges the
support condition in the finite zero-sum limit. -/
theorem eventually_mem_xiZerosInRectangle (hRH : RiemannHypothesis) {T : ℕ → ℝ}
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) {a b : ℝ} (ha : a < -1 / 2) (hb : 0 < b)
    (ρ : Zero) :
    ∀ᶠ n in Filter.atTop,
      ρ ∈ xiZerosInRectangle ((a : ℂ) - T n * Complex.I) ((b : ℂ) + T n * Complex.I) := by
  have hz : riemannXi (((ρ : ℂ) - 1 / 2) + 1 / 2) = 0 := by
    simpa only [sub_add_cancel] using ρ.property
  filter_upwards [eventually_mem_xiKernelSingularities hRH hT ha hb (Or.inr hz)] with n hn
  exact mem_xiZerosInRectangle.mpr (mem_xiKernelSingularities.mp hn).1

/-- Under RH and at positive scale, finite oscillatory xi zero sums over symmetric
rectangles converge to the full zero series as heights tend to infinity. The left
edge is below minus one half and the right edge is positive. Absolute convergence
and eventual inclusion of every zero prove the limit without monotone ledgers.
This identifies the zero-series part of the infinite principal contour. -/
theorem tendsto_xiZerosInRectangle_oscillatingSum (K : MellinKernel) (hRH : RiemannHypothesis)
    {T : ℕ → ℝ} (hT : Filter.Tendsto T Filter.atTop Filter.atTop) {a b x : ℝ} (ha : a < -1 / 2)
    (hb : 0 < b) (hx : 0 < x) :
    Filter.Tendsto
      (fun n =>
        ∑ ρ ∈ xiZerosInRectangle ((a : ℂ) - T n * Complex.I) ((b : ℂ) + T n * Complex.I),
          K.zetaOscillatingZeroTerm x ρ)
      Filter.atTop (nhds (∑' ρ, K.zetaOscillatingZeroTerm x ρ)) := by
  apply
    PseudoPrime.Analysis.tendsto_sum_of_eventually_mem_support (K.zetaOscillatingZeroTerm x)
      (summable_zetaOscillatingZeroTerm K hRH hx).norm
  intro ρ _
  exact eventually_mem_xiZerosInRectangle hRH hT ha hb ρ

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, the finite xi residue sum with the kernel pole removed equals the
negative oscillatory zero sum over the corresponding zero-subtype rectangle.
Translation gives a bijection of indices and the proved local residue identity
matches the weights. This is the reindexing needed for infinite contour limits. -/
theorem sum_xiKernelResidues_erase_pole (K : MellinKernel) (hRH : RiemannHypothesis) (x : ℝ)
    (z w : ℂ) :
    ∑ s ∈ (xiKernelSingularities z w).erase (-1 / 2),
        weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s =
      -∑ ρ ∈ xiZerosInRectangle z w, K.zetaOscillatingZeroTerm x ρ := by
  classical
  rw [← Finset.sum_neg_distrib]
  symm
  apply Finset.sum_bij (fun (ρ : Zero) _ => (ρ : ℂ) - 1 / 2)
  · intro ρ hρ
    have hclosed := mem_xiZerosInRectangle.mp hρ
    have hz : riemannXi (((ρ : ℂ) - 1 / 2) + 1 / 2) = 0 := by
      simpa only [sub_add_cancel] using ρ.property
    have hne : (ρ : ℂ) - 1 / 2 ≠ -1 / 2 := by
      intro he
      have hzero := ρ.property
      have he' : (ρ : ℂ) = 0 := by linear_combination he
      rw [he', riemannXi_zero] at hzero
      norm_num only at hzero
    exact Finset.mem_erase.mpr ⟨hne, mem_xiKernelSingularities.mpr ⟨hclosed, Or.inr hz⟩⟩
  · intro ρ _ τ _ h
    exact Subtype.ext (sub_left_injective h)
  · intro s hs
    have hm := Finset.mem_erase.mp hs
    have hmem := mem_xiKernelSingularities.mp hm.2
    have hz : riemannXi (s + 1 / 2) = 0 := hmem.2.resolve_left hm.1
    let ρ : Zero := ⟨s + 1 / 2, hz⟩
    refine ⟨ρ, ?_, ?_⟩
    · apply mem_xiZerosInRectangle.mpr
      simpa only [ρ, add_sub_cancel_right] using hmem.1
    · exact add_sub_cancel_right s (1 / 2)
  · intro ρ _
    exact (weightedResidue_xi_zero_eq_neg_zetaOscillatingZeroTerm K hRH x ρ).symm

open AnalyticNumberTheory.RiemannXi in
/-- Under RH, if the rectangle ledger contains the kernel pole, its complete residue
sum is the pole residue minus the finite oscillatory xi zero sum. Separate one pole
from the ledger and apply the zero reindexing identity. This identifies both parts
of the finite principal-character contour. -/
theorem sum_xiKernelResidues (K : MellinKernel) (hRH : RiemannHypothesis) (x : ℝ) {z w : ℂ}
    (hp : (-1 / 2 : ℂ) ∈ xiKernelSingularities z w) :
    ∑ s ∈ xiKernelSingularities z w, weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s =
      weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x (-1 / 2) -
        ∑ ρ ∈ xiZerosInRectangle z w, K.zetaOscillatingZeroTerm x ρ := by
  classical
  have he :=
    Finset.sum_erase_add (xiKernelSingularities z w)
      (weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x) hp
  rw [sum_xiKernelResidues_erase_pole K hRH x z w] at he
  rw [← he]
  ring

open AnalyticNumberTheory.RiemannXi in
/-- Under RH and at positive scale, finite xi residue sums over symmetric rectangles
converge to the kernel-pole residue minus the infinite oscillatory xi zero sum.
Heights need only tend to infinity, with left edge below minus one half and positive
right edge. Zero-sum convergence and eventual pole membership identify the limit.
This removes the finite residue ledger in the principal Mellin contour. -/
theorem tendsto_xiKernelResidueSum (K : MellinKernel) (hRH : RiemannHypothesis) {T : ℕ → ℝ}
    (hT : Filter.Tendsto T Filter.atTop Filter.atTop) {a b x : ℝ} (ha : a < -1 / 2) (hb : 0 < b)
    (hx : 0 < x) :
    Filter.Tendsto
      (fun n =>
        ∑ s ∈ xiKernelSingularities ((a : ℂ) - T n * Complex.I) ((b : ℂ) + T n * Complex.I),
          weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x s)
      Filter.atTop
      (nhds
        (weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x (-1 / 2) -
          ∑' ρ, K.zetaOscillatingZeroTerm x ρ)) := by
  have hz := tendsto_xiZerosInRectangle_oscillatingSum K hRH hT ha hb hx
  have h := hz.const_sub (weightedResidue K (fun t : ℂ => riemannXi (t + 1 / 2)) x (-1 / 2))
  apply h.congr'
  filter_upwards [eventually_mem_xiKernelSingularities hRH hT ha hb (Or.inl rfl)] with n hn
  exact (sum_xiKernelResidues K hRH x hn).symm

end PseudoPrime.LLS.PaperStatements.MellinKernel
