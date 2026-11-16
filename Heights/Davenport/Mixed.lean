import Heights.Davenport.OneDim

/-!
# Davenport's lemma: mixed measures

To prove Davenport's theorem we interpolate between the number of integer points and the volume
by changing one coordinate at a time. To do so we consider, for disjoint `A L : Finset ι`, the
product measure `Davenport.mixed A L` on `ι → ℝ` whose `i`-th factor is

* the counting measure of the integers if `i ∈ A`;
* the Lebesgue measure if `i ∈ L`;
* the Dirac mass at `0` otherwise.

The projection of `R` on the coordinates in `S` is replaced by the cylinder `Davenport.cyl S R`
of the points of `ι → ℝ` whose coordinates in `S` agree with those of a point of `R`.
In this way all the measures and sets live on the same space `ι → ℝ`.
-/

open MeasureTheory Set Function Bornology
open scoped ENNReal

namespace Davenport

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### A Fubini-type formula for one coordinate of a product measure -/

/-- Integrating with respect to a product measure can be done by first integrating over the
`a`-th coordinate. -/
lemma pi_apply_eq_lintegral_update (m : ι → Measure ℝ) [∀ i, SigmaFinite (m i)] (a : ι)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E) :
    Measure.pi m E =
      ∫⁻ x, m a {t | update x a t ∈ E} ∂(Measure.pi (update m a (Measure.dirac 0))) := by
  have : ∀ i, SigmaFinite (update m a (Measure.dirac 0) i) := by
    intro i
    rcases eq_or_ne i a with rfl | hi
    · rw [update_self]; infer_instance
    · rw [update_of_ne hi]; infer_instance
  have hf : Measurable fun p : (ι → ℝ) × ℝ ↦ update p.1 a p.2 := measurable_update'
  have key : Measure.pi m = Measure.map (fun p : (ι → ℝ) × ℝ ↦ update p.1 a p.2)
      ((Measure.pi (update m a (Measure.dirac 0))).prod (m a)) := by
    refine Measure.pi_eq fun s hs ↦ ?_
    have hpre : (fun p : (ι → ℝ) × ℝ ↦ update p.1 a p.2) ⁻¹' (univ.pi s) =
        (univ.pi (update s a univ)) ×ˢ (s a) := by
      ext ⟨x, t⟩
      simp only [mem_preimage, mem_pi, mem_univ, true_imp_iff, mem_prod]
      constructor
      · intro H
        refine ⟨fun i ↦ ?_, by simpa using H a⟩
        rcases eq_or_ne i a with rfl | hi
        · simp
        · simpa [hi] using H i
      · rintro ⟨H₁, H₂⟩ i
        rcases eq_or_ne i a with rfl | hi
        · simpa using H₂
        · simpa [hi] using H₁ i
    rw [Measure.map_apply hf (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod, Measure.pi_pi,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
      ← Finset.mul_prod_erase Finset.univ (fun i ↦ m i (s i)) (Finset.mem_univ a)]
    simp only [update_self, measure_univ, one_mul]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [update_of_ne (Finset.ne_of_mem_erase hi), update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [key, Measure.map_apply hf hE, Measure.prod_apply (hf hE)]
  rfl

/-! ### Cylinders -/

/-- The cylinder over the projection of `R` on the coordinates in `S`: the set of points whose
coordinates in `S` agree with those of a point of `R`. -/
def cyl (S : Finset ι) (R : Set (ι → ℝ)) : Set (ι → ℝ) := S.restrict ⁻¹' (S.restrict '' R)

omit [Fintype ι] [DecidableEq ι] in
lemma mem_cyl {S : Finset ι} {R : Set (ι → ℝ)} {x : ι → ℝ} :
    x ∈ cyl S R ↔ ∃ y ∈ R, ∀ i ∈ S, y i = x i := by
  simp only [cyl, mem_preimage, mem_image, funext_iff, Finset.restrict, Subtype.forall]

omit [Fintype ι] [DecidableEq ι] in
lemma isClosed_cyl (S : Finset ι) {R : Set (ι → ℝ)} (hR : IsCompact R) : IsClosed (cyl S R) :=
  (hR.image (Finset.continuous_restrict S)).isClosed.preimage (Finset.continuous_restrict S)

omit [DecidableEq ι] in
lemma measurableSet_cyl (S : Finset ι) {R : Set (ι → ℝ)} (hR : IsCompact R) :
    MeasurableSet (cyl S R) :=
  (isClosed_cyl S hR).measurableSet

omit [DecidableEq ι] in
lemma cyl_univ (R : Set (ι → ℝ)) : cyl Finset.univ R = R := by
  ext x
  rw [mem_cyl]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have : y = x := funext fun i ↦ hxy i (Finset.mem_univ i)
    exact this ▸ hy
  · exact fun hx ↦ ⟨x, hx, fun _ _ ↦ rfl⟩

omit [Fintype ι] in
/-- A line parallel to the `a`-th axis meets `cyl S R` only if it passes through
`cyl (S.erase a) R`. -/
lemma mem_cyl_erase_of_update_mem {S : Finset ι} {R : Set (ι → ℝ)} {x : ι → ℝ} {a : ι} {t : ℝ}
    (h : update x a t ∈ cyl S R) : x ∈ cyl (S.erase a) R := by
  rw [mem_cyl] at h ⊢
  obtain ⟨y, hy, hxy⟩ := h
  refine ⟨y, hy, fun i hi ↦ ?_⟩
  rw [hxy i (Finset.mem_of_mem_erase hi), update_of_ne (Finset.ne_of_mem_erase hi)]

/-- The sections of a cylinder over a bounded set along a coordinate of `S` are bounded. -/
lemma isBounded_section_cyl {S : Finset ι} {R : Set (ι → ℝ)} (hR : IsBounded R) {a : ι}
    (ha : a ∈ S) (x : ι → ℝ) : IsBounded {t : ℝ | update x a t ∈ cyl S R} := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hR
  refine isBounded_iff_forall_norm_le.mpr ⟨C, fun t ht ↦ ?_⟩
  obtain ⟨y, hy, hxy⟩ := mem_cyl.mp ht
  have : y a = t := by rw [hxy a ha, update_self]
  exact this ▸ (norm_le_pi_norm y a).trans (hC y hy)

/-- Davenport's conditions I and II, expressed in terms of cylinders. -/
lemma Conditions.isUnionOfIntervals_section_cyl {h : ℕ} {R : Set (ι → ℝ)} (hc : Conditions h R)
    {S : Finset ι} {a : ι} (ha : a ∈ S) (x : ι → ℝ) :
    IsUnionOfIntervals h {t : ℝ | update x a t ∈ cyl S R} := by
  by_cases hS : S = Finset.univ
  · subst hS
    simpa only [cyl_univ] using hc.line a x
  · convert hc.proj_line S hS ⟨a, ha⟩ (S.restrict x) using 3 with t
    change S.restrict (update x a t) ∈ S.restrict '' R ↔ _
    have : S.restrict (update x a t) = update (S.restrict x) ⟨a, ha⟩ t := by
      funext ⟨i, hi⟩
      rcases eq_or_ne i a with rfl | hia
      · simp [Finset.restrict]
      · have hia' : (⟨i, hi⟩ : S) ≠ ⟨a, ha⟩ := fun H ↦ hia (congrArg Subtype.val H)
        simp [Finset.restrict, update_of_ne hia, update_of_ne hia']
    rw [this]

/-! ### Mixed measures -/

/-- The family of measures on `ℝ` given by the counting measure of the integers for the indices
in `A`, the Lebesgue measure for the indices in `L` (and not in `A`) and the Dirac mass at `0`
for the other indices. -/
noncomputable def mixedFamily (A L : Finset ι) (i : ι) : Measure ℝ :=
  if i ∈ A then intCount else if i ∈ L then volume else Measure.dirac 0

instance (A L : Finset ι) (i : ι) : SigmaFinite (mixedFamily A L i) := by
  unfold mixedFamily; split_ifs <;> infer_instance

/-- The product of the measures `mixedFamily A L`. -/
noncomputable def mixed (A L : Finset ι) : Measure (ι → ℝ) := Measure.pi (mixedFamily A L)

omit [Fintype ι] in
lemma update_mixedFamily_insert_left {A L : Finset ι} {a : ι} (haA : a ∉ A) (haL : a ∉ L) :
    update (mixedFamily (insert a A) L) a (Measure.dirac 0) = mixedFamily A L := by
  funext i
  rcases eq_or_ne i a with rfl | hi
  · simp [mixedFamily, haA, haL]
  · simp [mixedFamily, hi]

omit [Fintype ι] in
lemma update_mixedFamily_insert_right {A L : Finset ι} {a : ι} (haA : a ∉ A) (haL : a ∉ L) :
    update (mixedFamily A (insert a L)) a (Measure.dirac 0) = mixedFamily A L := by
  funext i
  rcases eq_or_ne i a with rfl | hi
  · simp [mixedFamily, haA, haL]
  · simp [mixedFamily, hi]

lemma mixed_insert_left_apply {A L : Finset ι} {a : ι} (haA : a ∉ A) (haL : a ∉ L)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E) :
    mixed (insert a A) L E = ∫⁻ x, intCount {t | update x a t ∈ E} ∂(mixed A L) := by
  rw [mixed, pi_apply_eq_lintegral_update _ a hE, update_mixedFamily_insert_left haA haL, mixed]
  simp [mixedFamily]

lemma mixed_insert_right_apply {A L : Finset ι} {a : ι} (haA : a ∉ A) (haL : a ∉ L)
    {E : Set (ι → ℝ)} (hE : MeasurableSet E) :
    mixed A (insert a L) E = ∫⁻ x, volume {t | update x a t ∈ E} ∂(mixed A L) := by
  rw [mixed, pi_apply_eq_lintegral_update _ a hE, update_mixedFamily_insert_right haA haL, mixed]
  simp [mixedFamily, haA]

/-- The mixed measure with all coordinates counted is the number of integer points. -/
lemma mixed_univ_empty {R : Set (ι → ℝ)} (hR : MeasurableSet R) :
    mixed Finset.univ ∅ R = ((fun (z : ι → ℤ) (i : ι) ↦ (z i : ℝ)) ⁻¹' R).encard := by
  have h₁ : mixedFamily (Finset.univ : Finset ι) ∅ = fun _ ↦ intCount := by
    funext i; simp [mixedFamily]
  have h₂ : Measure.pi (fun _ : ι ↦ (Measure.count : Measure ℤ)) = Measure.count :=
    Measure.ext_of_singleton fun z ↦ by simp [Measure.pi_singleton]
  have h₃ : Measurable fun (z : ι → ℤ) (i : ι) ↦ (z i : ℝ) :=
    measurable_pi_iff.mpr fun i ↦
      (measurable_from_top (f := ((↑) : ℤ → ℝ))).comp (measurable_pi_apply i)
  have h₄ : Measure.pi (fun _ : ι ↦ intCount) =
      Measure.map (fun (z : ι → ℤ) (i : ι) ↦ (z i : ℝ)) (Measure.pi fun _ ↦ Measure.count) := by
    exact (Measure.pi_map_pi (μ := fun _ : ι ↦ (Measure.count : Measure ℤ))
      (f := fun _ ↦ ((↑) : ℤ → ℝ)) (hμ := fun _ ↦ measurableEmbedding_intCast.sigmaFinite_map)
      fun _ ↦ measurable_from_top.aemeasurable).symm
  rw [mixed, h₁, h₄, h₂, Measure.map_apply h₃ hR, Measure.count_apply .of_discrete]

/-- The mixed measure with Lebesgue measure on the coordinates in `T` computes the volume of
the projection on the coordinates in `T`. -/
lemma mixed_empty_cyl (T : Finset ι) {R : Set (ι → ℝ)} (hR : IsCompact R) :
    mixed ∅ T (cyl T R) = volume (T.restrict '' R) := by
  have key : Measure.map T.restrict (mixed ∅ T) = (volume : Measure (T → ℝ)) := by
    rw [volume_pi]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have hpre : T.restrict ⁻¹' (univ.pi s) =
        univ.pi fun i : ι ↦ if hi : i ∈ T then s ⟨i, hi⟩ else univ := by
      ext x
      simp only [mem_preimage, mem_pi, mem_univ, true_imp_iff, Finset.restrict, Subtype.forall]
      refine forall_congr' fun i ↦ ?_
      by_cases hi : i ∈ T <;> simp [hi]
    rw [Measure.map_apply (Finset.measurable_restrict T) (MeasurableSet.univ_pi hs), hpre, mixed,
      Measure.pi_pi, Finset.univ_eq_attach]
    calc ∏ i, mixedFamily ∅ T i (if hi : i ∈ T then s ⟨i, hi⟩ else univ)
        = ∏ i ∈ T, mixedFamily ∅ T i (if hi : i ∈ T then s ⟨i, hi⟩ else univ) :=
          (Finset.prod_subset (Finset.subset_univ T) fun i _ hi ↦ by simp [mixedFamily, hi]).symm
      _ = ∏ i ∈ T.attach, mixedFamily ∅ T i (if hi : (i : ι) ∈ T then s ⟨i, hi⟩ else univ) :=
          (Finset.prod_attach T _).symm
      _ = ∏ i ∈ T.attach, volume (s i) :=
          Finset.prod_congr rfl fun i _ ↦ by simp [mixedFamily]
  rw [← key, Measure.map_apply (Finset.measurable_restrict T)
    (hR.image (Finset.continuous_restrict T)).measurableSet]
  rfl

/-- The mixed measure with Lebesgue measure on all the coordinates is the Lebesgue measure. -/
lemma mixed_empty_univ : mixed ∅ (Finset.univ : Finset ι) = volume := by
  have : mixedFamily ∅ (Finset.univ : Finset ι) = fun _ ↦ volume := by
    funext i; simp [mixedFamily]
  rw [mixed, this, volume_pi]

/-! ### Changing one coordinate -/

section step

variable {h : ℕ} {R : Set (ι → ℝ)} {A L : Finset ι} {a : ι}

/-- The one-dimensional case of Davenport's lemma applied to the sections of a cylinder. -/
lemma section_cyl_bounds (hR : IsCompact R) (hc : Conditions h R) {S : Finset ι} (ha : a ∈ S)
    (x : ι → ℝ) :
    intCount {t | update x a t ∈ cyl S R} ≤
        volume {t | update x a t ∈ cyl S R} + h * (cyl (S.erase a) R).indicator 1 x ∧
      volume {t | update x a t ∈ cyl S R} ≤
        intCount {t | update x a t ∈ cyl S R} + h * (cyl (S.erase a) R).indicator 1 x := by
  rcases eq_empty_or_nonempty {t | update x a t ∈ cyl S R} with he | ⟨t, ht⟩
  · simp [he]
  · have hx : x ∈ cyl (S.erase a) R := mem_cyl_erase_of_update_mem ht
    have hI := hc.isUnionOfIntervals_section_cyl ha x
    have hb := isBounded_section_cyl hR.isBounded ha x
    simp only [indicator_of_mem hx, Pi.one_apply, mul_one]
    exact ⟨hI.intCount_le hb, hI.volume_le hb⟩

omit [DecidableEq ι] in
lemma lintegral_const_mul_indicator_cyl (hR : IsCompact R) (μ : Measure (ι → ℝ)) (S : Finset ι) :
    ∫⁻ x, h * (cyl S R).indicator 1 x ∂μ = h * μ (cyl S R) := by
  have hm := measurableSet_cyl S hR
  rw [lintegral_const_mul _ (measurable_one.indicator hm), lintegral_indicator_one hm]

/-- Replacing the counting measure by the Lebesgue measure in the coordinate `a` changes the
measure of the cylinder by at most `h` times the measure of the projection along `a`. -/
lemma mixed_insert_left_le (hR : IsCompact R) (hc : Conditions h R) (haA : a ∉ A) (haL : a ∉ L) :
    mixed (insert a A) L (cyl (insert a (A ∪ L)) R) ≤
      mixed A (insert a L) (cyl (insert a (A ∪ L)) R) + h * mixed A L (cyl (A ∪ L) R) := by
  have hE := measurableSet_cyl (insert a (A ∪ L)) hR
  have ha : a ∉ A ∪ L := by simp [haA, haL]
  rw [mixed_insert_left_apply haA haL hE, mixed_insert_right_apply haA haL hE,
    ← lintegral_const_mul_indicator_cyl hR, ← lintegral_add_right _
      ((measurable_one.indicator (measurableSet_cyl (A ∪ L) hR)).const_mul _)]
  refine lintegral_mono fun x ↦ ?_
  simpa only [Finset.erase_insert ha] using
    (section_cyl_bounds hR hc (Finset.mem_insert_self a (A ∪ L)) x).1

/-- Replacing the Lebesgue measure by the counting measure in the coordinate `a` changes the
measure of the cylinder by at most `h` times the measure of the projection along `a`. -/
lemma mixed_insert_right_le (hR : IsCompact R) (hc : Conditions h R) (haA : a ∉ A) (haL : a ∉ L) :
    mixed A (insert a L) (cyl (insert a (A ∪ L)) R) ≤
      mixed (insert a A) L (cyl (insert a (A ∪ L)) R) + h * mixed A L (cyl (A ∪ L) R) := by
  have hE := measurableSet_cyl (insert a (A ∪ L)) hR
  have ha : a ∉ A ∪ L := by simp [haA, haL]
  rw [mixed_insert_left_apply haA haL hE, mixed_insert_right_apply haA haL hE,
    ← lintegral_const_mul_indicator_cyl hR, ← lintegral_add_right _
      ((measurable_one.indicator (measurableSet_cyl (A ∪ L) hR)).const_mul _)]
  refine lintegral_mono fun x ↦ ?_
  simpa only [Finset.erase_insert ha] using
    (section_cyl_bounds hR hc (Finset.mem_insert_self a (A ∪ L)) x).2

end step

end Davenport
