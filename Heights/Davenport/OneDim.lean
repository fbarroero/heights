import Heights.Davenport.Defs

/-!
# Davenport's lemma: the one-dimensional case

We introduce the counting measure `Davenport.intCount` of the integers inside `ℝ` and compare it
with the Lebesgue measure on unions of at most `h` bounded intervals:
the two measures differ by at most `h`.
-/

open MeasureTheory Set Function Bornology
open scoped ENNReal

namespace Davenport

/-- The counting measure of `ℤ` seen as a measure on `ℝ`. -/
noncomputable def intCount : Measure ℝ := Measure.map ((↑) : ℤ → ℝ) Measure.count

lemma measurableEmbedding_intCast : MeasurableEmbedding ((↑) : ℤ → ℝ) :=
  Int.isClosedEmbedding_coe_real.measurableEmbedding

lemma intCount_apply (S : Set ℝ) : intCount S = (((↑) : ℤ → ℝ) ⁻¹' S).encard := by
  rw [intCount, measurableEmbedding_intCast.map_apply, Measure.count_apply .of_discrete]

instance : SigmaFinite intCount := measurableEmbedding_intCast.sigmaFinite_map

lemma intCount_Icc (a b : ℝ) : intCount (Icc a b) = ((⌊b⌋ + 1 - ⌈a⌉).toNat : ℝ≥0∞) := by
  rw [intCount_apply, Int.preimage_Icc, ← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard,
    Int.card_Icc]
  rfl

lemma intCount_Ioo (a b : ℝ) : intCount (Ioo a b) = ((⌈b⌉ - ⌊a⌋ - 1).toNat : ℝ≥0∞) := by
  rw [intCount_apply, Int.preimage_Ioo, ← Finset.coe_Ioo, Set.encard_coe_eq_coe_finsetCard,
    Int.card_Ioo]
  rfl

private lemma sandwich {I : Set ℝ} (hI : I.OrdConnected) (hb : IsBounded I) (hne : I.Nonempty) :
    sInf I ≤ sSup I ∧ Ioo (sInf I) (sSup I) ⊆ I ∧ I ⊆ Icc (sInf I) (sSup I) := by
  have hbb := hb.bddBelow
  have hba := hb.bddAbove
  exact ⟨Real.sInf_le_sSup I hbb hba,
    IsConnected.Ioo_csInf_csSup_subset ⟨hne, hI.isPreconnected⟩ hbb hba,
    subset_Icc_csInf_csSup hbb hba⟩

/-- A bounded interval contains at most `1` more integers than its length. -/
lemma intCount_le_volume_add_one {I : Set ℝ} (hI : I.OrdConnected) (hb : IsBounded I) :
    intCount I ≤ volume I + 1 := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨hab, h₁, h₂⟩ := sandwich hI hb hne
  set a := sInf I
  set b := sSup I
  calc intCount I ≤ intCount (Icc a b) := measure_mono h₂
    _ = ((⌊b⌋ + 1 - ⌈a⌉).toNat : ℝ≥0∞) := intCount_Icc a b
    _ ≤ ENNReal.ofReal (b - a) + 1 := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by linarith) zero_le_one,
        ← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      have h1 : (⌊b⌋ : ℝ) ≤ b := Int.floor_le b
      have h2 : a ≤ (⌈a⌉ : ℝ) := Int.le_ceil a
      rcases le_total 0 (⌊b⌋ + 1 - ⌈a⌉) with h0 | h0
      · have : (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℤ) : ℝ) = ((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ) := by
          rw [Int.toNat_of_nonneg h0]
        push_cast at this
        rw [this]
        linarith
      · rw [Int.toNat_of_nonpos h0]
        simp only [Nat.cast_zero]
        linarith
    _ = volume (Ioo a b) + 1 := by rw [Real.volume_Ioo]
    _ ≤ volume I + 1 := by gcongr

/-- The length of a bounded interval is at most `1` more than the number of integers in it. -/
lemma volume_le_intCount_add_one {I : Set ℝ} (hI : I.OrdConnected) (hb : IsBounded I) :
    volume I ≤ intCount I + 1 := by
  rcases I.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨hab, h₁, h₂⟩ := sandwich hI hb hne
  set a := sInf I
  set b := sSup I
  calc volume I ≤ volume (Icc a b) := measure_mono h₂
    _ = ENNReal.ofReal (b - a) := Real.volume_Icc
    _ ≤ ((⌈b⌉ - ⌊a⌋ - 1).toNat : ℝ≥0∞) + 1 := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_add (by positivity) zero_le_one]
      apply ENNReal.ofReal_le_ofReal
      have h1 : b ≤ (⌈b⌉ : ℝ) := Int.le_ceil b
      have h2 : (⌊a⌋ : ℝ) ≤ a := Int.floor_le a
      have h3 : ((⌈b⌉ - ⌊a⌋ - 1 : ℤ) : ℝ) ≤ (((⌈b⌉ - ⌊a⌋ - 1).toNat : ℤ) : ℝ) := by
        exact_mod_cast Int.self_le_toNat _
      push_cast at h3
      linarith
    _ = intCount (Ioo a b) + 1 := by rw [intCount_Ioo]
    _ ≤ intCount I + 1 := by gcongr

/-- The union of two intersecting intervals is an interval. -/
lemma ordConnected_union {I J : Set ℝ} (hI : I.OrdConnected) (hJ : J.OrdConnected)
    (h : ¬ Disjoint I J) : (I ∪ J).OrdConnected :=
  isPreconnected_iff_ordConnected.mp <|
    IsPreconnected.union' (Set.not_disjoint_iff_nonempty_inter.mp h) hI.isPreconnected
      hJ.isPreconnected

lemma intCount_sUnion_finset (F : Finset (Set ℝ))
    (hF : ∀ I ∈ F, I.OrdConnected ∧ IsBounded I) :
    intCount (⋃₀ (F : Set (Set ℝ))) ≤ volume (⋃₀ (F : Set (Set ℝ))) + F.card ∧
      volume (⋃₀ (F : Set (Set ℝ))) ≤ intCount (⋃₀ (F : Set (Set ℝ))) + F.card := by
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
  subst hn
  by_cases hdisj : (F : Set (Set ℝ)).PairwiseDisjoint id
  · -- the intervals are pairwise disjoint: we sum the inequalities for the single intervals
    have hmeas : ∀ I ∈ F, MeasurableSet (id I) := fun I hI ↦ (hF I hI).1.measurableSet
    simp only [sUnion_eq_biUnion]
    have e₁ := measure_biUnion_finset (μ := intCount) hdisj hmeas
    have e₂ := measure_biUnion_finset (μ := volume) hdisj hmeas
    simp only [id, Finset.mem_coe] at e₁ e₂ ⊢
    rw [e₁, e₂]
    have hcard : (F.card : ℝ≥0∞) = ∑ I ∈ F, 1 := by simp
    rw [hcard, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact ⟨Finset.sum_le_sum fun I hI ↦ intCount_le_volume_add_one (hF I hI).1 (hF I hI).2,
      Finset.sum_le_sum fun I hI ↦ volume_le_intCount_add_one (hF I hI).1 (hF I hI).2⟩
  · -- two of the intervals intersect: we replace them by their union
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, onFun, id, not_forall] at hdisj
    obtain ⟨I, hI, J, hJ, hIJ, hnd⟩ := hdisj
    let F' : Finset (Set ℝ) := insert (I ∪ J) ((F.erase I).erase J)
    have hF' : ∀ K ∈ F', K.OrdConnected ∧ IsBounded K := by
      intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · exact ⟨ordConnected_union (hF I hI).1 (hF J hJ).1 hnd, (hF I hI).2.union (hF J hJ).2⟩
      · exact hF K (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hK))
    have hcard : F'.card < F.card := by
      change (insert (I ∪ J) ((F.erase I).erase J)).card < F.card
      have hJ' : J ∈ F.erase I := Finset.mem_erase.mpr ⟨Ne.symm hIJ, hJ⟩
      have h1 := Finset.card_erase_of_mem hJ'
      have h2 := Finset.card_erase_of_mem hI
      have h3 := Finset.card_insert_le (I ∪ J) ((F.erase I).erase J)
      have h4 : 0 < (F.erase I).card := Finset.card_pos.mpr ⟨J, hJ'⟩
      omega
    have hU : ⋃₀ (F' : Set (Set ℝ)) = ⋃₀ (F : Set (Set ℝ)) := by
      ext x
      simp only [F', mem_sUnion, Finset.mem_coe, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro ⟨K, rfl | ⟨-, -, hK⟩, hx⟩
        · rcases hx with hx | hx
          exacts [⟨I, hI, hx⟩, ⟨J, hJ, hx⟩]
        · exact ⟨K, hK, hx⟩
      · rintro ⟨K, hK, hx⟩
        by_cases hKI : K = I
        · exact ⟨I ∪ J, .inl rfl, .inl (hKI ▸ hx)⟩
        by_cases hKJ : K = J
        · exact ⟨I ∪ J, .inl rfl, .inr (hKJ ▸ hx)⟩
        · exact ⟨K, .inr ⟨hKJ, hKI, hK⟩, hx⟩
    obtain ⟨ih₁, ih₂⟩ := ih F'.card hcard F' hF' rfl
    rw [hU] at ih₁ ih₂
    have hle : (F'.card : ℝ≥0∞) ≤ F.card := by exact_mod_cast hcard.le
    exact ⟨ih₁.trans (by gcongr), ih₂.trans (by gcongr)⟩

private lemma IsUnionOfIntervals.exists_finset {h : ℕ} {S : Set ℝ} (hS : IsUnionOfIntervals h S)
    (hb : IsBounded S) : ∃ F : Finset (Set ℝ), F.card ≤ h ∧
      (∀ I ∈ F, I.OrdConnected ∧ IsBounded I) ∧ S = ⋃₀ (F : Set (Set ℝ)) := by
  obtain ⟨I, hI, rfl⟩ := hS
  refine ⟨Finset.univ.image I, ?_, ?_, ?_⟩
  · simpa using Finset.card_image_le (s := Finset.univ) (f := I)
  · intro J hJ
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨hI k, hb.subset (subset_iUnion I k)⟩
  · simp [sUnion_range]

/-- **Davenport's lemma in dimension one**, first inequality: a bounded union of at most `h`
intervals contains at most `h` more integers than its Lebesgue measure. -/
theorem IsUnionOfIntervals.intCount_le {h : ℕ} {S : Set ℝ} (hS : IsUnionOfIntervals h S)
    (hb : IsBounded S) : intCount S ≤ volume S + h := by
  obtain ⟨F, hcard, hF, rfl⟩ := hS.exists_finset hb
  have hle : (F.card : ℝ≥0∞) ≤ h := by exact_mod_cast hcard
  exact (intCount_sUnion_finset F hF).1.trans (by gcongr)

/-- **Davenport's lemma in dimension one**, second inequality: the Lebesgue measure of a bounded
union of at most `h` intervals is at most `h` more than the number of integers in it. -/
theorem IsUnionOfIntervals.volume_le {h : ℕ} {S : Set ℝ} (hS : IsUnionOfIntervals h S)
    (hb : IsBounded S) : volume S ≤ intCount S + h := by
  obtain ⟨F, hcard, hF, rfl⟩ := hS.exists_finset hb
  have hle : (F.card : ℝ≥0∞) ≤ h := by exact_mod_cast hcard
  exact (intCount_sUnion_finset F hF).2.trans (by gcongr)

end Davenport
