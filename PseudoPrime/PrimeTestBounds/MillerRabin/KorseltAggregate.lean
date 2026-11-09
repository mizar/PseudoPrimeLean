/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltCases
public import PseudoPrime.PrimeTestBounds.MillerRabin.KorseltSmall
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt20to40
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt40to50
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt50to60
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt60to70
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt70to80
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt80to90
public import PseudoPrime.PrimeTestBounds.MillerRabin.Korselt90to100

/-! # Combined uniform Korselt search below smallest factor 100 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A bounded uniform Korselt triple with ordered prime factors and smallest
factor below 20 belongs to one of four explicit products. The parameter list
is exhaustive, and exact division reconstructs the other factors. -/
theorem uniformKorselt_below20_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 20) :
    n = 8911 ∨ n = 29341 ∨ n = 314821 ∨ n = 1024651 := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ korseltCandidateRows 20 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  rw [korselt_candidates_below20] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  rcases hm with h | h | h | h
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 19 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inl (by linarith only [hn, hrform])
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 61 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inr (Or.inr (Or.inl (by linarith only [hn, hrform])))
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 37 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inr (Or.inl (by linarith only [hn, hrform]))
  · obtain ⟨rfl, rfl, hd⟩ := h
    have hq' : q = 199 := by linarith only [hd, hqsub]
    subst q
    norm_num only at hrform hn
    exact Or.inr (Or.inr (Or.inr (by linarith only [hn, hrform])))

/-- The two certified factor ranges give exactly four candidate parameters
below 40. The range-splitting identity combines their independent checks. -/
theorem korselt_candidates_below40 :
    korseltCandidateRows 40 = [(7, 2, 18), (13, 2, 60), (13, 8, 36), (19, 14, 198)] := by
  have hsplit := korseltCandidateRows_split 20 20
  norm_num only at hsplit
  have hzero : korseltCandidateRange 0 20 = korseltCandidateRows 20 := by
    simp only [korseltCandidateRange, korseltCandidateRows, List.range_eq_range']
  rw [hzero, korselt_candidates_20to40, List.append_nil, korselt_candidates_below20] at hsplit
  exact hsplit

/-- A bounded uniform Korselt triple with ordered smallest factor below 40 is
one of the four products from the first search block. The second block has no
candidates, so the earlier classification applies. -/
theorem uniformKorselt_below40_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 40) :
    n = 8911 ∨ n = 29341 ∨ n = 314821 ∨ n = 1024651 := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ korseltCandidateRows 40 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [korselt_candidates_below40] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hp20 : p < 20 := by
    rcases hm with h | h | h | h
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
  exact uniformKorselt_below20_cases hu hbound hn hp hq hrp hpq hqr hp20

/-- The independently checked factor ranges below 40 and from 40 to 49 give
exactly the six listed parameter triples below smallest factor 50. -/
theorem korselt_candidates_below50 :
    korseltCandidateRows 50 =
      [(7, 2, 18), (13, 2, 60), (13, 8, 36), (19, 14, 198), (41, 22, 72), (43, 26, 126)] := by
  have hsplit := korseltCandidateRows_split 40 10
  norm_num only at hsplit
  have hzero : korseltCandidateRange 0 40 = korseltCandidateRows 40 := by
    simp only [korseltCandidateRange, korseltCandidateRows, List.range_eq_range']
  rw [hzero, korselt_candidates_below40, korselt_candidates_40to50] at hsplit
  exact hsplit

/-- A bounded uniform Korselt triple with ordered smallest factor below 50 is
one of six explicit products. Map each checked parameter tuple to the input
reconstructed from its three factors. -/
theorem uniformKorselt_below50_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 50) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ korseltCandidateRows 50 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [korselt_candidates_below50] at hm
  let f : ℕ × ℕ × ℕ → ℕ := fun x ↦ x.1 * (x.2.2 + 1) * ((x.1 * (x.2.2 + 1) - 1) / x.2.1 + 1)
  have hqsub : q - 1 + 1 = q := Nat.sub_add_cancel hq.one_lt.le
  have heq : f (p, a, q - 1) = n := by
    dsimp only [f]
    rw [hqsub, ← hrform, ← hn]
  have hh := List.mem_map.mpr ⟨(p, a, q - 1), hm, heq⟩
  norm_num only [List.map_cons, List.map_nil, f] at hh
  exact hh

/-- Whenever a checked search bound adds no new candidate beyond 50, every
bounded uniform Korselt triple below that factor bound is one of the six known
products. This allows subsequent empty blocks to reuse the classification. -/
theorem uniformKorselt_cases_of_rows {N n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < N)
    (hrows : korseltCandidateRows N = korseltCandidateRows 50) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ korseltCandidateRows N :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [hrows, korselt_candidates_below50] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hp50 : p < 50 := by
    rcases hm with h | h | h | h | h | h
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
  exact uniformKorselt_below50_cases hu hbound hn hp hq hrp hpq hqr hp50

/-- The empty block from 50 to 59 adds no candidate to the search below 50. -/
theorem korselt_candidates_below60 : korseltCandidateRows 60 = korseltCandidateRows 50 := by
  simpa only using korselt_rows_add_empty 50 10 korselt_candidates_50to60

/-- A bounded uniform Korselt triple with ordered smallest factor below 60 is
one of the six explicit products already found below 50. -/
theorem uniformKorselt_below60_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 60) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] := by
  obtain ⟨hpb, a, ha, hap, hdiv, hadiv, hrform⟩ :=
    uniformKorselt_finite_parameters hn hp hq hrp hpq hqr hu hbound
  have hm : (p, a, q - 1) ∈ korseltCandidateRows 60 :=
    uniformKorselt_candidate_mem hu hn hp hq hrp hpq hqr hbound hsmall ha hap hdiv hadiv hrform
  rw [korselt_candidates_below60, korselt_candidates_below50] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
  have hp50 : p < 50 := by
    rcases hm with h | h | h | h | h | h
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
    · linarith only [h.1]
  exact uniformKorselt_below50_cases hu hbound hn hp hq hrp hpq hqr hp50

/-- The empty factor range from 60 to 69 leaves the six-candidate list unchanged. -/
theorem korselt_candidates_below70 : korseltCandidateRows 70 = korseltCandidateRows 50 := by
  have h := korselt_rows_add_empty 60 10 korselt_candidates_60to70
  norm_num only at h
  exact h.trans korselt_candidates_below60

/-- A bounded uniform Korselt triple with ordered smallest factor below 70 is
one of the six explicit products from the completed smaller-factor blocks. -/
theorem uniformKorselt_below70_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 70) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] :=
  uniformKorselt_cases_of_rows hu hbound hn hp hq hrp hpq hqr hsmall korselt_candidates_below70

/-- The empty factor range from 70 to 79 adds no candidates to the six already
found below 50. -/
theorem korselt_candidates_below80 : korseltCandidateRows 80 = korseltCandidateRows 50 := by
  have h := korselt_rows_add_empty 70 10 korselt_candidates_70to80
  norm_num only at h
  exact h.trans korselt_candidates_below70

/-- A bounded uniform Korselt triple with ordered smallest factor below 80 is
one of the six explicit products from the checked candidate list. -/
theorem uniformKorselt_below80_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 80) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] :=
  uniformKorselt_cases_of_rows hu hbound hn hp hq hrp hpq hqr hsmall korselt_candidates_below80

/-- The empty factor range from 80 to 89 adds no candidates to the six already
found below 50. -/
theorem korselt_candidates_below90 : korseltCandidateRows 90 = korseltCandidateRows 50 := by
  have h := korselt_rows_add_empty 80 10 korselt_candidates_80to90
  norm_num only at h
  exact h.trans korselt_candidates_below80

/-- A bounded uniform Korselt triple with ordered smallest factor below 90 is
one of the six explicit products from the checked candidate list. -/
theorem uniformKorselt_below90_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 90) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] :=
  uniformKorselt_cases_of_rows hu hbound hn hp hq hrp hpq hqr hsmall korselt_candidates_below90

/-- The empty factor range from 90 to 99 adds no candidates to the six already
found below 50. -/
theorem korselt_candidates_below100 : korseltCandidateRows 100 = korseltCandidateRows 50 := by
  have h := korselt_rows_add_empty 90 10 korselt_candidates_90to100
  norm_num only at h
  exact h.trans korselt_candidates_below90

/-- A bounded uniform Korselt triple with ordered smallest factor below 100 is
one of the six explicit products from the checked candidate list. -/
theorem uniformKorselt_below100_cases {n p q r : ℕ} (hu : UniformKorseltTriple n)
    (hbound : n ≤ 2 ^ 22) (hn : n = p * q * r) (hp : p.Prime) (hq : q.Prime) (hrp : r.Prime)
    (hpq : p < q) (hqr : q < r) (hsmall : p < 100) :
    n ∈ [8911, 314821, 29341, 1024651, 410041, 1152271] :=
  uniformKorselt_cases_of_rows hu hbound hn hp hq hrp hpq hqr hsmall korselt_candidates_below100

end PseudoPrime.PrimeTestBounds.MillerRabin
