import Mathlib

namespace Polynomial

variable {p : ℤ[X]}

/-- The Mahler measure of a cyclotomic polynomial is 1. -/
theorem cyclotomic_mahlerMeasure_eq_one' {R : Type*} [CommRing R] [Algebra R ℂ] (n : ℕ) :
    ((cyclotomic n R).map (algebraMap R ℂ)).mahlerMeasure = 1 := by
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  simp only [map_cyclotomic, mahlerMeasure_eq_leadingCoeff_mul_prod_roots, cyclotomic.monic n ℂ,
    Monic.leadingCoeff, one_mem, CStarRing.norm_of_mem_unitary, one_mul]
  apply Multiset.prod_eq_one
  have : NeZero (n : ℂ) := @NeZero.charZero _ _ {out := hn} _ _
  simpa [Polynomial.cyclotomic.roots_eq_primitiveRoots_val] using fun _ hz ↦ le_of_eq <|
    IsPrimitiveRoot.norm'_eq_one (isPrimitiveRoot_of_mem_primitiveRoots hz) hn

example : ((cyclotomic n ℝ).map (algebraMap ℝ ℂ)).mahlerMeasure = 1 := by exact cyclotomic_mahlerMeasure_eq_one' n

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


lemma Multiset.mem_le_prod_of_one_le {α : Type u_1} {β : Type u_2} [CommMonoid α]
    [CommMonoidWithZero β] [PartialOrder β] [PosMulMono β] [ZeroLEOneClass β]
    (f : α → β) (h1 : ∀ (a : α), 1 ≤ f a) (s : Multiset α) (a : α) (ha : a ∈ s) :
    f a ≤ (Multiset.map f s).prod := by
  obtain ⟨s', rfl⟩ := Multiset.exists_cons_of_mem ha
  rw [Multiset.map_cons, Multiset.prod_cons]
  calc f a = f a * 1 := (mul_one (f a)).symm
    _ ≤ f a * (Multiset.map f s').prod := by
      gcongr
      · exact le_trans (zero_le_one' β) <| MulOpposite.one_le_op.mp (h1 a)
      · refine Multiset.one_le_prod ?_
        simp_all


/-
If the product of max(1, |root|) for all roots is 1, then every root has absolute value at most 1.
-/
lemma roots_le_one {p : ℤ[X]} (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)
    (z : ℂ) (hz : z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots) : ‖z‖ ≤ 1 := by
  have hroots :
      (Multiset.map (fun a ↦ max 1 ‖a‖) (Polynomial.map (Int.castRingHom ℂ) p).roots).prod = 1 := by
    simp_all [mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
      norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h]
  contrapose! hroots
  apply ne_of_gt <| lt_of_lt_of_le (lt_sup_of_lt_right (a := 1) hroots) _
  exact Multiset.mem_le_prod_of_one_le (fun a => max 1 ‖a‖) (fun a => le_max_left 1 ‖a‖)
    (Polynomial.map (Int.castRingHom ℂ) p).roots z hz

variable (K : Type u_1) [Field K] [NumberField K] (A : Type u_2)
  [NormedField A] [IsAlgClosed A] [NormedAlgebra ℚ A]

theorem pow_eq_one_of_norm_le_one {x : K} (hx₀ : x ≠ 0) (hxi : IsIntegral ℤ x)
    (hx : ∀ φ : K →+* A, ‖φ x‖ ≤ 1) : ∃ (n : ℕ) (_ : 0 < n), x ^ n = 1 := by sorry


open IntermediateField in
lemma pow_eq_one_of_isIntegral_of_norm_le_one {x : ℂ} (h_alg_int : IsIntegral ℤ x)
    (h_MM : ∀ w : ℂ, (minpoly ℤ x).aeval w = 0 → ‖w‖ ≤ 1) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by sorry

/-
If a complex number is an algebraic integer and all its conjugates have absolute value 1, then it is a root of unity.
-/
open IntermediateField in
lemma complex_pow_eq_one_of_isIntegral_of_norm_eq_one {x : ℂ} (h_alg_int : IsIntegral ℤ x)
    (h_conj : ∀ w : ℂ, (minpoly ℤ x).aeval w = 0 → ‖w‖ = 1) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by
  -- Apply the theorem `NumberField.Embeddings.pow_eq_one_of_norm_eq_one` to conclude that $x$ is a root of unity.
  let y : adjoin ℚ {x} := ⟨x, mem_adjoin_simple_self ℚ x⟩
  letI : NumberField (adjoin ℚ {x}) := by
    refine { to_charZero := IntermediateField.charZero ℚ⟮x⟯,
             to_finiteDimensional := adjoin.finiteDimensional h_alg_int.tower_top }
  letI : Nonempty (adjoin ℚ {x} →+* ℂ) := by
    apply NumberField.Embeddings.instNonemptyRingHom ↥ℚ⟮x⟯ ℂ

  have h_values (φ : (adjoin ℚ {x}) →+* ℂ) : ‖φ y‖ = 1 := by
    have h_poly : aeval y (minpoly ℤ x) = 0 := by
        convert minpoly.aeval ℤ x
        simp [aeval_def, eval₂_eq_sum_range, ← Subtype.coe_inj, y]
    apply h_conj
    simpa [aeval_def] using congr_arg φ h_poly
  suffices ∃ n : ℕ, (0 < n ∧ y ^ n = 1) by simp_all [y, Subtype.ext_iff]
  -- By `NumberField.Embeddings.pow_eq_one_of_norm_eq_one`, $x$ is a root of unity.
  convert NumberField.Embeddings.pow_eq_one_of_norm_eq_one (x := y) (adjoin ℚ {x}) ℂ
  · simp_all only [exists_prop, forall_const, Classical.imp_iff_left_iff, y]
    obtain ⟨p, hp⟩ := h_alg_int;
    rw [algebraMap_int_eq] at hp;
    refine Or.inl ⟨p, hp.1, ?_⟩;
    simp_all only [algebraMap_int_eq, eval₂_eq_sum_range, eq_intCast, SubmonoidClass.mk_pow,
      ← Subtype.coe_inj, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
      SubringClass.coe_intCast, ZeroMemClass.coe_zero]




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
