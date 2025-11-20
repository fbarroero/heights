/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Polynomial.ContentIdeal
import Mathlib.RingTheory.Polynomial.GaussNorm

/-!
## Gauss's Lemma for Dedekind Domains

This file contains Gauss's Lemma for Dedekind Domains, which states that the content ideal of a
polynomial is the whole ring if and only if the `v`-adic Gauss norms of the polynomial are equal to
1 for all `v`.
-/

namespace Polynomial

open IsDedekindDomain HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] {b : NNReal} (hb : 1 < b)
(v : HeightOneSpectrum R) [Field K] [Algebra R K] [IsFractionRing R K] (p : R[X])

/-- Given a polynomial `p` in `R[X]`, the `v`-adic Gauss norm of `p` is different from 1 if and only
if the content ideal of `p` is contained in the prime ideal corresponding to `v`. -/
theorem gaussNorm_ne_one_iff_contentIdeal_le :
    (p.map (algebraMap R K)).gaussNorm (v.adicAbv hb) 1 ≠ 1 ↔ p.contentIdeal ≤ v.asIdeal := by
  by_cases hp0 : p = 0
  · simp [hp0]
  have h_supp : (p.map (algebraMap R K)).support = p.support := support_map_of_injective p
    <| FaithfulSMul.algebraMap_injective R K
  have hsupp_nonempty : (p.map (algebraMap R K)).support.Nonempty := by grind [support_nonempty]
  simp only [gaussNorm, hsupp_nonempty, ↓reduceDIte, coeff_map, one_pow, mul_one, ne_eq,
    contentIdeal, Ideal.span_le, Set.subset_def, SetLike.mem_coe,
    ← v.adicAbv_coe_lt_one_iff (K := K) hb]
  constructor
  · contrapose!
    simp only [mem_coeffs_iff, mem_support_iff, ne_eq, ↓existsAndEq, and_true, forall_exists_index,
      and_imp]
    intro _ h1 h2
    have hcoeffle := v.adicAbv_coe_le_one (K := K) hb
    apply le_antisymm <| Finset.sup'_le _ _ fun b _ ↦ hcoeffle (p.coeff b)
    apply Finset.le_sup'_of_le (fun b ↦ (v.adicAbv hb) ((algebraMap R K) (p.coeff b))) _ h2
    simp [h1]
  · intro h
    apply ne_of_lt
    rw [Finset.sup'_lt_iff]
    intro n hn
    rw [h_supp, mem_support_iff] at hn
    exact h _ <| p.coeff_mem_coeffs hn

theorem contentIdeal_eq_top_iff_forall_gaussNorm_eq_one [Nontrivial R] (hR : ¬IsField R) :
    p.contentIdeal = ⊤ ↔
    ∀ v : HeightOneSpectrum R, (p.map (algebraMap R K)).gaussNorm (v.adicAbv hb) 1 = 1 := by
  simp [← not_iff_not, gaussNorm_ne_one_iff_contentIdeal_le, ideal_ne_top_iff_exists hR]

theorem isPrimitive_iff_forall_gaussNorm_eq_one [Nontrivial R] [IsBezout R] (hR : ¬IsField R) :
    p.IsPrimitive ↔ ∀ (v : HeightOneSpectrum R),
    (p.map (algebraMap R K)).gaussNorm (v.adicAbv hb) 1 = 1 := by
  rw [isPrimitive_iff_contentIdeal_eq_top,
    p.contentIdeal_eq_top_iff_forall_gaussNorm_eq_one (K := K) hb hR]


end Polynomial
