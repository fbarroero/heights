import Mathlib

namespace Polynomial

variable {p : ℤ[X]}

lemma cyclotomic_int_mahlerMeasure (n : ℕ) :
    ((cyclotomic n ℤ).map (Int.castRingHom ℂ)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  simp only [map_cyclotomic, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n ℂ,
    Monic.leadingCoeff, one_mem, CStarRing.norm_of_mem_unitary, one_mul]
  apply Multiset.prod_eq_one
  have : NeZero n := {out := hn}
  have : NeZero (n : ℂ) := NeZero.charZero
  rw [Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  simp only [Multiset.mem_map, Finset.mem_val, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, sup_eq_left]
  exact fun _ hz ↦ le_of_eq <|
    IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn

lemma cyclotomic_mahlerMeasure {R : Type*} [CommRing R] [Algebra R ℂ] (n : ℕ) :
    ((cyclotomic n R).map (algebraMap R ℂ)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  rw [map_cyclotomic, ← map_cyclotomic_int]
  exact cyclotomic_int_mahlerMeasure n



lemma norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) :
    ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ = 1 := by
  rcases eq_or_ne p 0 with hp | hp
  · have : (map (Int.castRingHom ℂ) p) = 0 := by simp [hp]
    simp [this] at h
  have h_ineq := leading_coeff_le_mahlerMeasure <| p.map (Int.castRingHom ℂ)
  rw [leadingCoeff_map_of_injective <| RingHom.injective_int (Int.castRingHom ℂ)] at h_ineq ⊢
  simp only [h, eq_intCast, Complex.norm_intCast] at h_ineq ⊢
  norm_cast at h_ineq
  have : 0 < |p.leadingCoeff| := by simp_all
  exact_mod_cast (Int.le_antisymm this h_ineq).symm

--useless?
lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one
    (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : |p.leadingCoeff| = 1 := by
  rcases eq_or_ne p 0 with hp | hp
  · have : (map (Int.castRingHom ℂ) p) = 0 := by simp [hp]
    simp [this] at h
  have h_ineq := leading_coeff_le_mahlerMeasure <| p.map (Int.castRingHom ℂ)
  rw [h, leadingCoeff_map_of_injective <| RingHom.injective_int (Int.castRingHom ℂ)] at h_ineq
  simp only [eq_intCast, Complex.norm_intCast] at h_ineq
  norm_cast at h_ineq
  have : 0 < |p.leadingCoeff| := by simp_all
  exact (Int.le_antisymm this h_ineq).symm


lemma miao (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) (hpx : ¬ X ∣ p) {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    ∃ n, 0 < n ∧ z ^ n = 1 := by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  simp [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, this] at h
  wlog hirr : Irreducible p
  ·
    sorry

  let K := SplittingField (p.map (Int.castRingHom ℚ))
  have : NumberField K := by
    exact
      { to_charZero := SplittingField.instCharZero (p.map (Int.castRingHom ℚ)),
        to_finiteDimensional :=
          IsSplittingField.instFiniteDimensionalSplittingField (p.map (Int.castRingHom ℚ))}
  let roots := (map (Int.castRingHom ℚ) p).aroots K
  --Embeddings.range_eval_eq_rootSet_minpoly K ℂ x,

  --have := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ
  sorry

lemma bb (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) (hpx : ¬ X ∣ p) : ∃ n, 0 < n ∧ cyclotomic n ℤ ∣ p := by
  --refine int_cyclotomic_unique ?_
  have {z : ℂ} (hz : z ∈ p.aroots ℂ) := miao h hpx hz

  /- rw [(IsAlgClosed.splits (map (Int.castRingHom ℂ) p)).eq_prod_roots,
   (IsAlgClosed.splits (cyclotomic' p.natDegree ℂ)).eq_prod_roots]
  have hlc : ‖(map (Int.castRingHom ℂ) p).leadingCoeff‖ = 1 := by
    rw [leadingCoeff_map_of_injective <| RingHom.injective_int (Int.castRingHom ℂ), eq_intCast,
      Complex.norm_intCast]
    exact_mod_cast abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  simp [this] -/
  sorry

lemma cc (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) (hp : Irreducible p) :
    p = cyclotomic p.natDegree ℤ := by
  sorry

end Polynomial
