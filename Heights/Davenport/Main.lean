import Heights.Davenport.Mixed

/-!
# Davenport's lemma

We prove the main theorem of

* H. Davenport, *On a principle of Lipschitz*, J. London Math. Soc. 26 (1951), 179–183.

## Main results

* `Davenport.abs_latticeCount_sub_volume_le`: if `R` is a compact subset of `ι → ℝ` satisfying
  the conditions I and II for `h`, then
  `|N(R) - V(R)| ≤ ∑ m ∈ range n, h ^ (n - m) * V_m`, where `n` is the cardinality of `ι`.
* `Davenport.abs_latticeCount_sub_volume_le'`: the same statement, literally as in the paper,
  with the convention `V_0 = 1`.
* `Davenport.abs_latticeCount_sub_volume_le_sum_finset`: the same statement, with the right-hand
  side written as a sum over the proper subsets of the set of coordinates.

## Strategy of the proof

Davenport argues by induction on the dimension, treating one coordinate at a time. We organize
the same argument as follows. For disjoint sets of coordinates `A` and `L` we consider the
measure `mixed A L` which counts integer points in the coordinates in `A`, is the Lebesgue
measure in the coordinates in `L` and ignores the remaining coordinates. By the one-dimensional
case, moving a coordinate `a` from `A` to `L` changes the measure of the projection of `R` on
the coordinates in `A ∪ L` by at most `h` times the `mixed (A \ {a}) L`-measure of the
projection of `R` on the coordinates in `(A ∪ L) \ {a}`. An induction on `A` gives the result.
-/

open MeasureTheory Set Function Bornology
open scoped ENNReal

namespace Davenport

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ℕ} {R : Set (ι → ℝ)}

/-! ### The induction -/

variable (h R) in
/-- The summand corresponding to `B` in the bounds for the projection of `R` on the coordinates
in `T`: it is `h ^ #B` times the volume of the projection of `R` on the coordinates
in `T \ B`. -/
private noncomputable def term (T B : Finset ι) : ℝ≥0∞ :=
  (h : ℝ≥0∞) ^ B.card * mixed ∅ (T \ B) (cyl (T \ B) R)

private lemma term_insert {T B : Finset ι} {a : ι} (haT : a ∉ T) (haB : a ∉ B) :
    term h R (insert a T) (insert a B) = h * term h R T B := by
  have : insert a T \ insert a B = T \ B := by
    ext i
    rcases eq_or_ne i a with rfl | hi
    · simp [haT]
    · simp [hi]
  rw [term, term, this, Finset.card_insert_of_notMem haB, pow_succ']
  ring

private lemma sum_term_insert {A L : Finset ι} {a : ι} (haA : a ∉ A) (haL : a ∉ L) :
    ∑ B ∈ (insert a A).powerset, term h R (insert a (A ∪ L)) B =
      ∑ B ∈ A.powerset, term h R (insert a (A ∪ L)) B +
        h * ∑ B ∈ A.powerset, term h R (A ∪ L) B := by
  have ha : a ∉ A ∪ L := by simp [haA, haL]
  rw [Finset.sum_powerset_insert haA, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun B hB ↦
    term_insert ha fun haB ↦ haA (Finset.mem_powerset.mp hB haB)

/-- The upper bound in the induction. -/
private lemma mixed_le_sum_term (hR : IsCompact R) (hc : Conditions h R) (A L : Finset ι)
    (hAL : Disjoint A L) :
    mixed A L (cyl (A ∪ L) R) ≤ ∑ B ∈ A.powerset, term h R (A ∪ L) B := by
  induction A using Finset.induction_on generalizing L with
  | empty => simp [term]
  | insert a A ha ih =>
    obtain ⟨haL, hAL⟩ := Finset.disjoint_insert_left.mp hAL
    have ih₁ := ih (insert a L) (Finset.disjoint_insert_right.mpr ⟨ha, hAL⟩)
    have ih₂ := ih L hAL
    rw [Finset.union_insert] at ih₁
    rw [Finset.insert_union, sum_term_insert ha haL]
    exact (mixed_insert_left_le hR hc ha haL).trans (by gcongr)

/-- The lower bound in the induction. -/
private lemma mixed_empty_add_le_sum_term (hR : IsCompact R) (hc : Conditions h R)
    (A L : Finset ι) (hAL : Disjoint A L) :
    mixed ∅ (A ∪ L) (cyl (A ∪ L) R) + mixed ∅ (A ∪ L) (cyl (A ∪ L) R) ≤
      mixed A L (cyl (A ∪ L) R) + ∑ B ∈ A.powerset, term h R (A ∪ L) B := by
  induction A using Finset.induction_on generalizing L with
  | empty => simp [term]
  | insert a A ha ih =>
    obtain ⟨haL, hAL⟩ := Finset.disjoint_insert_left.mp hAL
    have ih₁ := ih (insert a L) (Finset.disjoint_insert_right.mpr ⟨ha, hAL⟩)
    have ih₂ := mixed_le_sum_term hR hc A L hAL
    rw [Finset.union_insert] at ih₁
    rw [Finset.insert_union, sum_term_insert ha haL]
    calc _ ≤ _ := ih₁
      _ ≤ (mixed (insert a A) L (cyl (insert a (A ∪ L)) R) +
            h * ∑ B ∈ A.powerset, term h R (A ∪ L) B) +
            ∑ B ∈ A.powerset, term h R (insert a (A ∪ L)) B := by
        gcongr
        exact (mixed_insert_right_le hR hc ha haL).trans (by gcongr)
      _ = _ := by ring

/-- The upper bound in the induction: the measure of the projection of `R` on the coordinates in
`A ∪ L`, counting integer points in the coordinates in `A`, is bounded in terms of the volumes
of the projections of `R` on the coordinates in `(A ∪ L) \ B`, for `B ⊆ A`. -/
lemma mixed_le_sum (hR : IsCompact R) (hc : Conditions h R) (A L : Finset ι)
    (hAL : Disjoint A L) :
    mixed A L (cyl (A ∪ L) R) ≤
      ∑ B ∈ A.powerset, (h : ℝ≥0∞) ^ B.card * volume (((A ∪ L) \ B).restrict '' R) := by
  simpa only [term, mixed_empty_cyl _ hR] using mixed_le_sum_term hR hc A L hAL

/-- The lower bound in the induction: twice the volume of the projection of `R` on the
coordinates in `A ∪ L` is at most its measure counting integer points in the coordinates in `A`
plus the right-hand side of `Davenport.mixed_le_sum`. -/
lemma two_mul_volume_le_mixed_add_sum (hR : IsCompact R) (hc : Conditions h R) (A L : Finset ι)
    (hAL : Disjoint A L) :
    volume ((A ∪ L).restrict '' R) + volume ((A ∪ L).restrict '' R) ≤
      mixed A L (cyl (A ∪ L) R) +
        ∑ B ∈ A.powerset, (h : ℝ≥0∞) ^ B.card * volume (((A ∪ L) \ B).restrict '' R) := by
  simpa only [term, mixed_empty_cyl _ hR] using mixed_empty_add_le_sum_term hR hc A L hAL

/-! ### The main theorem -/

omit [DecidableEq ι] in
/-- A compact set contains finitely many integer points. -/
lemma finite_latticePoints (hR : IsCompact R) :
    ((fun (z : ι → ℤ) (i : ι) ↦ (z i : ℝ)) ⁻¹' R).Finite := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hR.isBounded
  refine (Set.Finite.pi' fun _ : ι ↦ Set.finite_Icc (-⌈C⌉) ⌈C⌉).subset fun z hz i ↦ ?_
  have h₁ : |(z i : ℝ)| ≤ C := (norm_le_pi_norm (fun i ↦ (z i : ℝ)) i).trans (hC _ hz)
  have h₂ : C ≤ (⌈C⌉ : ℝ) := Int.le_ceil C
  rw [abs_le] at h₁
  constructor
  · have : (-(⌈C⌉ : ℤ) : ℝ) ≤ (z i : ℝ) := by linarith
    exact_mod_cast this
  · have : (z i : ℝ) ≤ (⌈C⌉ : ℝ) := by linarith
    exact_mod_cast this

omit [Fintype ι] [DecidableEq ι] in
lemma volume_restrict_image_ne_top (hR : IsCompact R) (s : Finset ι) :
    volume (s.restrict '' R) ≠ ∞ :=
  (hR.image (Finset.continuous_restrict s)).measure_lt_top.ne

/-- The volume of `R` is the volume of its projection on all the coordinates. -/
lemma volume_univ_restrict_image (hR : IsCompact R) :
    volume ((Finset.univ : Finset ι).restrict '' R) = volume R := by
  rw [← mixed_empty_cyl _ hR, cyl_univ, mixed_empty_univ]

/-- **Davenport's lemma**, with the right-hand side written as a sum over the proper subsets `s`
of the set of coordinates: here `s.restrict '' R` is the projection of `R` on the coordinates
in `s`. -/
theorem abs_latticeCount_sub_volume_le_sum_finset (hR : IsCompact R) (hc : Conditions h R) :
    |(latticeCount R : ℝ) - volume.real R| ≤
      ∑ s : Finset ι with s ≠ Finset.univ,
        (h : ℝ) ^ (Fintype.card ι - s.card) * volume.real (s.restrict '' R) := by
  -- the two inequalities given by the induction, in `ℝ≥0∞`
  have hU := mixed_le_sum_term hR hc Finset.univ ∅ (Finset.disjoint_empty_right _)
  have hL := mixed_empty_add_le_sum_term hR hc Finset.univ ∅ (Finset.disjoint_empty_right _)
  have hN : mixed Finset.univ ∅ R = (latticeCount R : ℝ≥0∞) := by
    rw [mixed_univ_empty hR.measurableSet, latticeCount,
      ← (finite_latticePoints hR).cast_ncard_eq]
    rfl
  rw [Finset.union_empty, cyl_univ, hN, Finset.powerset_univ] at hU hL
  rw [mixed_empty_univ] at hL
  simp only [term, ← Finset.compl_eq_univ_sdiff] at hU hL
  simp only [mixed_empty_cyl _ hR] at hU hL
  -- we move to the real numbers
  have hfin : ∀ B : Finset ι, (h : ℝ≥0∞) ^ B.card * volume (Bᶜ.restrict '' R) ≠ ∞ := fun B ↦
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top h))
      (volume_restrict_image_ne_top hR _)
  have hsum : (∑ B : Finset ι, (h : ℝ≥0∞) ^ B.card * volume (Bᶜ.restrict '' R)).toReal =
      ∑ B : Finset ι, (h : ℝ) ^ B.card * volume.real (Bᶜ.restrict '' R) := by
    rw [ENNReal.toReal_sum fun B _ ↦ hfin B]
    simp [ENNReal.toReal_mul, measureReal_def]
  have hsumfin : ∑ B : Finset ι, (h : ℝ≥0∞) ^ B.card * volume (Bᶜ.restrict '' R) ≠ ∞ :=
    ENNReal.sum_ne_top.mpr fun B _ ↦ hfin B
  have hV : volume R ≠ ∞ := hR.measure_lt_top.ne
  have hU' : (latticeCount R : ℝ) ≤
      ∑ B : Finset ι, (h : ℝ) ^ B.card * volume.real (Bᶜ.restrict '' R) := by
    have := ENNReal.toReal_mono hsumfin hU
    rwa [hsum, ENNReal.toReal_natCast] at this
  have hL' : volume.real R + volume.real R ≤ latticeCount R +
      ∑ B : Finset ι, (h : ℝ) ^ B.card * volume.real (Bᶜ.restrict '' R) := by
    have := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, hsumfin⟩) hL
    rwa [ENNReal.toReal_add hV hV, ENNReal.toReal_add (ENNReal.natCast_ne_top _) hsumfin, hsum,
      ENNReal.toReal_natCast] at this
  -- we rewrite the sum in terms of the complement of `B`
  have hcompl : ∑ B : Finset ι, (h : ℝ) ^ B.card * volume.real (Bᶜ.restrict '' R) =
      ∑ s : Finset ι, (h : ℝ) ^ (Fintype.card ι - s.card) * volume.real (s.restrict '' R) := by
    refine Fintype.sum_bijective compl compl_bijective _ _ fun B ↦ ?_
    rw [Finset.card_compl, Nat.sub_sub_self (Finset.card_le_univ B)]
  have hsplit : ∑ s : Finset ι,
      (h : ℝ) ^ (Fintype.card ι - s.card) * volume.real (s.restrict '' R) =
      volume.real R + ∑ s : Finset ι with s ≠ Finset.univ,
        (h : ℝ) ^ (Fintype.card ι - s.card) * volume.real (s.restrict '' R) := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· = Finset.univ),
      Finset.filter_eq' Finset.univ Finset.univ]
    simp [measureReal_def, volume_univ_restrict_image hR]
  rw [hcompl, hsplit] at hU' hL'
  rw [abs_le]
  constructor <;> linarith

/-- **Davenport's lemma** (H. Davenport, *On a principle of Lipschitz*): let `R` be a compact
subset of `ℝⁿ` such that every line parallel to a coordinate axis meets `R`, and each of its
projections on the coordinate subspaces, in at most `h` intervals. Then the number `N(R)` of
points with integer coordinates in `R` and the volume `V(R)` of `R` satisfy
`|N(R) - V(R)| ≤ ∑ m ∈ range n, h ^ (n - m) * V_m`, where `V_m` is the sum of the `m`-dimensional
volumes of the projections of `R` on the `m`-dimensional coordinate subspaces.

In this statement `V_0` is `1` if `R` is nonempty and `0` otherwise, see
`Davenport.abs_latticeCount_sub_volume_le'` for the version with the convention `V_0 = 1`. -/
theorem abs_latticeCount_sub_volume_le (hR : IsCompact R) (hc : Conditions h R) :
    |(latticeCount R : ℝ) - volume.real R| ≤
      ∑ m ∈ Finset.range (Fintype.card ι), (h : ℝ) ^ (Fintype.card ι - m) * projVolume R m := by
  refine (abs_latticeCount_sub_volume_le_sum_finset hR hc).trans_eq ?_
  have hmaps : ∀ s ∈ Finset.univ.filter (fun s : Finset ι ↦ s ≠ Finset.univ),
      s.card ∈ Finset.range (Fintype.card ι) := fun s hs ↦ by
    rw [Finset.mem_range, ← Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr (Finset.mem_filter.mp hs).2)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [projVolume, Finset.mul_sum]
  refine Finset.sum_congr ?_ fun s hs ↦ by
    rw [(Finset.mem_powersetCard.mp hs).2]
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
    Finset.subset_univ]
  refine and_iff_right_of_imp fun hs hs' ↦ ?_
  rw [hs', Finset.card_univ] at hs
  exact (Finset.mem_range.mp hm).ne' hs

omit [DecidableEq ι] in
lemma projVolume_zero_le_one (R : Set (ι → ℝ)) : projVolume R 0 ≤ 1 := by
  have : volume ((∅ : Finset ι).restrict '' R) ≤ 1 := by
    refine (measure_mono (subset_univ _)).trans_eq ?_
    rw [volume_pi, Measure.pi_univ]
    simp
  simpa [projVolume, measureReal_def] using ENNReal.toReal_mono ENNReal.one_ne_top this

/-- **Davenport's lemma**, with the convention `V_0 = 1` as in the paper. -/
theorem abs_latticeCount_sub_volume_le' (hR : IsCompact R) (hc : Conditions h R) :
    |(latticeCount R : ℝ) - volume.real R| ≤
      ∑ m ∈ Finset.range (Fintype.card ι),
        (h : ℝ) ^ (Fintype.card ι - m) * if m = 0 then 1 else projVolume R m := by
  refine (abs_latticeCount_sub_volume_le hR hc).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  split_ifs with hm
  · subst hm
    gcongr
    exact projVolume_zero_le_one R
  · exact le_rfl

end Davenport
