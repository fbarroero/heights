import Heights.Davenport.Main

/-!
# Davenport's lemma for convex sets

As a sanity check, and a first application, we show that convex sets satisfy the conditions I
and II of Davenport's lemma with `h = 1`.
-/

open MeasureTheory Set Function

namespace Davenport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An interval is a union of at most one interval. -/
lemma IsUnionOfIntervals.of_ordConnected {S : Set ℝ} (hS : S.OrdConnected) :
    IsUnionOfIntervals 1 S :=
  ⟨fun _ ↦ S, fun _ ↦ hS, (iUnion_const S).symm⟩

omit [Fintype ι] in
/-- A line parallel to a coordinate axis meets a convex set in an interval. -/
lemma ordConnected_section_of_convex {κ : Type*} [DecidableEq κ] {R : Set (κ → ℝ)}
    (hR : Convex ℝ R) (i : κ) (x : κ → ℝ) : {t : ℝ | update x i t ∈ R}.OrdConnected := by
  refine Convex.ordConnected fun t₁ ht₁ t₂ ht₂ a b ha hb hab ↦ ?_
  have : update x i (a • t₁ + b • t₂) = a • update x i t₁ + b • update x i t₂ := by
    funext j
    rcases eq_or_ne j i with rfl | hj
    · simp
    · simp only [update_of_ne hj, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [← add_mul, hab, one_mul]
  simpa only [mem_ofPred_eq, this] using hR ht₁ ht₂ ha hb hab

/-- Convex sets satisfy the conditions I and II of Davenport's lemma with `h = 1`. -/
theorem Conditions.of_convex {R : Set (ι → ℝ)} (hR : Convex ℝ R) : Conditions 1 R where
  line i x := .of_ordConnected (ordConnected_section_of_convex hR i x)
  proj_line s _ i x := by
    have hs : Convex ℝ (s.restrict '' R) :=
      hR.is_linear_image ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩
    exact .of_ordConnected (ordConnected_section_of_convex hs i x)

/-- **Davenport's lemma for compact convex sets**: the difference between the number of integer
points and the volume is bounded by the sum of the volumes of the projections on the proper
coordinate subspaces. -/
theorem abs_latticeCount_sub_volume_le_of_convex {R : Set (ι → ℝ)} (hR : IsCompact R)
    (hR' : Convex ℝ R) :
    |(latticeCount R : ℝ) - volume.real R| ≤
      ∑ m ∈ Finset.range (Fintype.card ι), projVolume R m := by
  simpa using abs_latticeCount_sub_volume_le hR (.of_convex hR')

end Davenport

#print axioms Davenport.abs_latticeCount_sub_volume_le
#print axioms Davenport.abs_latticeCount_sub_volume_le'
#print axioms Davenport.abs_latticeCount_sub_volume_le_sum_finset
#print axioms Davenport.abs_latticeCount_sub_volume_le_of_convex
