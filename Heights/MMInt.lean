import Mathlib
import Heights.MMIntAux

namespace Polynomial

variable {p : ℤ[X]}

--PRd
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


variable {p : ℤ[X]} (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)

include h in
lemma norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one :
    ‖(p.map (Int.castRingHom ℂ)).leadingCoeff‖ = 1 := by
  rcases eq_or_ne p 0 with _ | hp
  · simp_all
  have h_ineq := leading_coeff_le_mahlerMeasure <| p.map (Int.castRingHom ℂ)
  rw [h] at h_ineq
  rw [leadingCoeff_map_of_injective <| RingHom.injective_int (Int.castRingHom ℂ), eq_intCast]
    at ⊢ h_ineq
  norm_cast at ⊢ h_ineq
  grind [leadingCoeff_eq_zero]

include h in
lemma abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one : |p.leadingCoeff| = 1 := by
  have := norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  rw [leadingCoeff_map_of_injective <| RingHom.injective_int (Int.castRingHom ℂ), eq_intCast]
    at this
  norm_cast at this

variable {z : ℂ} (hz₀ : z ≠ 0) (hz : z ∈ p.aroots ℂ)

include hz h in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex roots are integral
over ℤ. -/
theorem isIntegral_of_mahlerMeasure_eq_one : IsIntegral ℤ z := by
  have : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp
    <| abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have : (C (1 / p.leadingCoeff) * p).Monic := by aesop (add safe (by simp [Monic.def]))
  grind [IsIntegral, RingHom.IsIntegralElem, mem_roots', IsRoot.def, eval₂_mul, eval_map]

open Multiset in
include h hz in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex roots have norm at
most 1. -/
lemma norm_root_le_one_of_mahlerMeasure_eq_one : ‖z‖ ≤ 1 := by
  calc
  ‖z‖ ≤ max 1 ‖z‖ := le_max_right 1 ‖z‖
  _   ≤ ((p.map (Int.castRingHom ℂ)).roots.map (fun a ↦ max 1 ‖a‖)).prod :=
        sorry
  _   ≤ 1 := by grind [prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff,
        norm_leadingCoeff_eq_one_of_mahlerMeasure_eq_one]




open IntermediateField in
include hz₀ hz h in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex nonzero roots are
roots of unity. -/
theorem pow_eq_one_of_mahlerMeasure_eq_one : ∃ n, 0 < n ∧ z ^ n = 1 := by
/- We want to use NumberField.Embeddings.pow_eq_one_of_norm_le_one but it can only be applied to
elements of number fields. We thus first construct the number field K obtained by adjoining z to ℚ.
-/
  let K := ℚ⟮z⟯
  letI : NumberField K := {
    to_charZero := ℚ⟮z⟯.charZero,
    to_finiteDimensional := adjoin.finiteDimensional
      (isIntegral_of_mahlerMeasure_eq_one h hz).tower_top}
-- y is z as an element of K
  let y : K := ⟨z, mem_adjoin_simple_self ℚ z⟩
-- the conjugates of y are inside the closed unit disk
  have (φ : K →+* ℂ) : ‖φ y‖ ≤ 1 := by
    apply norm_root_le_one_of_mahlerMeasure_eq_one h
    convert hz using 0
    have (n : ℕ) : p.coeff n = φ (p.coeff n) := by simp
    simp_rw [mem_roots', ne_eq, Polynomial.map_eq_zero_iff
      <| RingHom.injective_int (algebraMap ℤ ℂ), and_congr_right_iff, algebraMap_int_eq,
      IsRoot.def, eval_map, eval₂_eq_sum_range, eq_intCast, ← map_pow, this, ← map_mul, ← map_sum,
      map_eq_zero_iff φ <| RingHom.injective φ]
    simp [y, ← Subtype.coe_injective.eq_iff]
  convert NumberField.Embeddings.pow_eq_one_of_norm_le_one (x := y) K ℂ (Subtype.coe_ne_coe.mp hz₀)
    (coe_isIntegral_iff.mp <| isIntegral_of_mahlerMeasure_eq_one h hz)
  simp_all [Submonoid.mk_eq_one K.toSubfield.toSubmonoid, y]

include h hz₀ hz in
/-- If an integer polynomial has Mahler measure equal to 1, then all its complex nonzero roots are
roots of unity. -/
theorem isPrimitiveRoot_of_mahlerMeasure_eq_one : ∃ n, 0 < n ∧ IsPrimitiveRoot z n := by
  obtain ⟨_, _, hz_pow⟩ := pow_eq_one_of_mahlerMeasure_eq_one h hz₀ hz
  exact IsPrimitiveRoot.exists_pos hz_pow (by omega)

theorem cyclotomomic_dvd_of_mahlerMeasure_eq_one (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1)
    (hX : ¬ X ∣ p) (hpdeg : p.degree ≠ 0) : ∃ n, 0 < n ∧ cyclotomic n ℤ ∣ p := by
  have hpdegC : (map (Int.castRingHom ℂ) p).degree ≠ 0 := by
    contrapose! hpdeg
    rw [← hpdeg]
    refine (degree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)) p).symm
  obtain ⟨z, hz⟩ := Polynomial.Splits.exists_eval_eq_zero
    (IsAlgClosed.splits (map (Int.castRingHom ℂ) p)) hpdegC
  have hz₀ : z ≠ 0 := by
    contrapose! hX
    simp_all [X_dvd_iff, coeff_zero_eq_aeval_zero]
  have h_z_root : z ∈ p.aroots ℂ := by aesop
  obtain ⟨m, h_m_pos, h_prim⟩ := isPrimitiveRoot_of_mahlerMeasure_eq_one h hz₀ h_z_root
  use m, h_m_pos
  rw [Polynomial.cyclotomic_eq_minpoly h_prim h_m_pos]
  apply minpoly.isIntegrallyClosed_dvd <| isIntegral_of_mahlerMeasure_eq_one h h_z_root
  simp_all [aeval_def, eval_map]

theorem mahlerMeasure_eq_one_iff (h_irr : Irreducible p) :
    (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1 ↔ p = X ∨ ∃ n, 0 < n ∧ p = cyclotomic n ℤ := by
  constructor
  · sorry
  · intro h
    cases h with
    | inl hX => sorry
    | inr h =>
      have := cyclotomic_mahlerMeasure_eq_one (R := ℂ)
      aesop

---UNTIL HERE

/-
If a complex number is an algebraic integer and all its conjugates have absolute value 1, then it is a root of unity.
-/
/- open IntermediateField in
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
  simp_all only [exists_prop, forall_const, Classical.imp_iff_left_iff, y]
  obtain ⟨p, hp⟩ := h_alg_int;
  rw [algebraMap_int_eq] at hp;
  refine Or.inl ⟨p, hp.1, ?_⟩;
  simp_all only [algebraMap_int_eq, eval₂_eq_sum_range, eq_intCast, SubmonoidClass.mk_pow,
    ← Subtype.coe_inj, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
    SubringClass.coe_intCast, ZeroMemClass.coe_zero]


/-
If a complex number is an algebraic integer and all its conjugates have absolute value 1, then it is a root of unity.
-/
open IntermediateField in
lemma complex_pow_eq_one_of_isIntegral_of_norm_le_one {x : ℂ} (hx₀ : x ≠ 0) (h_alg_int : IsIntegral ℤ x)
    (h_conj : ∀ w : ℂ, (minpoly ℤ x).aeval w = 0 → ‖w‖ ≤ 1) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by
  let y : ℚ⟮x⟯ := ⟨x, mem_adjoin_simple_self ℚ x⟩
  letI : NumberField ℚ⟮x⟯ := {
    to_charZero := IntermediateField.charZero ℚ⟮x⟯,
    to_finiteDimensional := adjoin.finiteDimensional h_alg_int.tower_top}
  letI : Nonempty (ℚ⟮x⟯ →+* ℂ) := NumberField.Embeddings.instNonemptyRingHom ℚ⟮x⟯ ℂ
  have h_values (φ : ℚ⟮x⟯ →+* ℂ) : ‖φ y‖ ≤ 1 := by
    have h_poly : aeval y (minpoly ℤ x) = 0 := by
        convert minpoly.aeval ℤ x
        simp [aeval_def, eval₂_eq_sum_range, ← Subtype.coe_inj, y]
    apply h_conj
    simpa [aeval_def] using congr_arg φ h_poly
  have hy₀ : y ≠ 0 := Subtype.coe_ne_coe.mp hx₀
  suffices ∃ n : ℕ, (0 < n ∧ y ^ n = 1) by simp_all [y, Subtype.ext_iff]
  -- By `NumberField.Embeddings.pow_eq_one_of_norm_le_one`, $x$ is a root of unity.
  convert NumberField.Embeddings.pow_eq_one_of_norm_le_one (x := y) (adjoin ℚ {x}) ℂ hy₀
  simp_all [exists_prop, forall_const, Classical.imp_iff_left_iff, y]
  obtain ⟨p, hp⟩ := h_alg_int;
  rw [algebraMap_int_eq] at hp;
  refine Or.inl ⟨p, hp.1, ?_⟩;
  simp_all only [algebraMap_int_eq, eval₂_eq_sum_range, eq_intCast, SubmonoidClass.mk_pow,
    ← Subtype.coe_inj, AddSubmonoidClass.coe_finset_sum, MulMemClass.coe_mul,
    SubringClass.coe_intCast, ZeroMemClass.coe_zero]


lemma miao (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) {z : ℂ} (hz₀ : z ≠ 0)
    (hz : z ∈ p.aroots ℂ) : ∃ n, 0 < n ∧ z ^ n = 1 := by
  -- By `roots_le_one`, every root of $p$ has absolute value at most 1.
  have h_le_one : ∀ z ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots, ‖z‖ ≤ 1 :=
    norm_le_one_of_mahlerMeasure_eq_one h;
  have hplc : p.leadingCoeff = 1 ∨ p.leadingCoeff = -1 := abs_eq_abs.mp
    <| abs_leadingCoeff_eq_one_of_mahlerMeasure_eq_one h
  have hp₀ : p ≠ 0 := fun h0 ↦ by simp [h0] at h
  let a := 1 / p.leadingCoeff
  let p' := C a * p
  have hp'Monic : p'.Monic := by aesop (add safe (by simp [Monic.def]))
  have h_p'_deg : p'.natDegree ≠ 0 := by
    simp only [mem_roots',  IsRoot.def] at hz
    rw [Nat.ne_zero_iff_zero_lt, Monic.natDegree_pos hp'Monic]
    have hroot := hz.2
    intro h1
    have : p = p.leadingCoeff := by
      cases hplc with
      | inl h_1 => simp_all [p', a]
      | inr h_2 =>
        simp_all only [p', a]
        grind
    rw [this, Polynomial.map_intCast, eval_intCast, Int.cast_eq_zero] at hroot
    grind
  have h_ev_p : (aeval z p) = 0 := by
    simp_all [aeval_def, eval_map]
/-   have h_ev_p' : (aeval z p') = 0 := by
    simp_all [p', a] -/
  apply complex_pow_eq_one_of_isIntegral_of_norm_le_one hz₀
    <| IsIntegral.of_aeval_monic hp'Monic h_p'_deg (by simp_all [p', a, isIntegral_zero])
  intro w hw
  have hw' : w ∈ (Polynomial.map (Int.castRingHom ℂ) p).roots := by
    have hmp : w ∈ (map (Int.castRingHom ℂ) (minpoly ℤ z)).roots := by
      rw [mem_roots', IsRoot.def, eval_map]

      sorry
    have : (map (Int.castRingHom ℂ) (minpoly ℤ z)).roots ⊆ (map (Int.castRingHom ℂ) p).roots := by
      apply Multiset.subset_of_le <| Polynomial.roots.le_of_dvd (by simp_all) _
      refine map_dvd (Int.castRingHom ℂ) ?_
      rw [← minpoly.isIntegrallyClosed_dvd_iff, h_ev_p]


      sorry
    exact this hmp
/-
    rw [aeval_def, ← eval_map] at hw
    simp [mem_roots',  IsRoot.def]
    refine ⟨ne_zero_of_mem_roots hz, ?_⟩
    convert_to (aeval w) p = 0
    · simp [aeval_def, eval_map]

    sorry -/
  exact norm_le_one_of_mahlerMeasure_eq_one h w hw'



lemma miao' (h : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) (hpx : ¬ X ∣ p) {z : ℂ} (hz : z ∈ p.aroots ℂ) :
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
  have {z : ℂ} (hz : z ∈ p.aroots ℂ) := miao' h hpx hz

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
  sorry -/

end Polynomial
