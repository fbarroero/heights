module

public import Heights.SubspaceTheorem.Defs

/-!
# Successive minima of parallelepipeds

We state the consequence of Minkowski's second theorem on successive minima that is needed in
the proof of the Subspace Theorem ([evertse1993], Lemma 3.3.4): if `λ₁ ≤ ⋯ ≤ λₙ` are the
successive minima of the parallelepiped `Π(a) = {x : |Lᵢ(x)| ≤ aᵢ}` with respect to the
lattice `ℤⁿ`, then `λ₁ ⋯ λₙ * vol (Π(a)) ≤ 2 ^ n`. Since the volume of `Π(a)` is
`2 ^ n * a₁ ⋯ aₙ / |det L|`, this reads `λ₁ ⋯ λₙ * a₁ ⋯ aₙ ≤ |det L|`.

The sharp constant is not needed for the Subspace Theorem, so we only state the weaker bound
`λ₁ ⋯ λₙ * a₁ ⋯ aₙ ≤ n ^ n * |det L|`. This follows from Minkowski's *first* theorem as in
W. M. Schmidt, *Diophantine Approximation* (LNM 785), Ch. IV, Lemmas 1D and 1E (which give the
constant `n!`, or `n ^ (n / 2)` if the volume of the unit ball is bounded below by that of the
inscribed cube).
-/

@[expose] public section

open Matrix

namespace Schmidt

variable {ι : Type*} [Fintype ι]

/-! ### Auxiliary lemmas -/

/-- The inclusion `ℤⁿ → ℝⁿ` as a `ℤ`-linear map. -/
noncomputable def castLin : (ι → ℤ) →ₗ[ℤ] (ι → ℝ) :=
  ((Int.castAddHom ℝ).compLeft ι).toIntLinearMap

omit [Fintype ι] in
@[simp]
lemma castLin_apply (x : ι → ℤ) (i : ι) : castLin x i = (x i : ℝ) := rfl

omit [Fintype ι] in
lemma castLin_injective : Function.Injective (castLin : (ι → ℤ) → (ι → ℝ)) := by
  intro x y h
  ext i
  simpa using congrFun h i

lemma castLin_mem_span (x : ι → ℤ) :
    castLin x ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) := by
  classical
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨x, ?_⟩
  ext i
  simp [Finset.sum_apply, Pi.single_apply]

/-- If the real points of a set `S` of integer points lie in a real subspace `V`, then the rank of
`S` is at most the dimension of `V`. -/
lemma setFinrank_le_finrank (S : Set (ι → ℤ)) (V : Submodule ℝ (ι → ℝ))
    (h : ∀ x ∈ S, castLin x ∈ V) : Set.finrank ℤ S ≤ Module.finrank ℝ V := by
  have hdisc : DiscreteTopology (Submodule.span ℤ (castLin '' S)) := by
    have hle : Submodule.span ℤ (castLin '' S) ≤
        Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι)) :=
      Submodule.span_le.mpr (by rintro _ ⟨x, -, rfl⟩; exact castLin_mem_span x)
    exact DiscreteTopology.of_continuous_injective (f := Submodule.inclusion hle)
      (continuous_subtype_val.subtype_mk _) (Submodule.inclusion_injective hle)
  have h1 : Set.finrank ℤ S = Set.finrank ℤ (castLin '' S) := by
    rw [Set.finrank, Set.finrank, Submodule.span_image]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ castLin_injective _)
  rw [h1, ← Real.finrank_eq_int_finrank_of_discrete hdisc, Set.finrank]
  exact Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨x, hx, rfl⟩; exact h x hx))

/-- **Greedy successive minima.** For a gauge function `F` on `ℤⁿ` that is positive away from `0`
and has finite sublevel sets, there are linearly independent integer points `g₀, …, gₙ₋₁` with
`F (g₀) ≤ ⋯ ≤ F (gₙ₋₁)` such that every `x` with `F x < F (gⱼ)` lies in the real span of
`g₀, …, gⱼ₋₁`. -/
lemma exists_greedy (F : (ι → ℤ) → ℝ) (hfin : ∀ R, {x | F x ≤ R}.Finite) :
    ∃ g : Fin (Fintype.card ι) → ι → ℤ, Monotone (F ∘ g) ∧ LinearIndependent ℝ (castLin ∘ g) ∧
      ∀ j x, F x < F (g j) → castLin x ∈ Submodule.span ℝ (castLin ∘ g '' Set.Iio j) := by
  classical
  have himg : ∀ (g : ℕ → ι → ℤ) (m : ℕ),
      (castLin ∘ g) '' Set.Iio m = Set.range fun i : Fin m ↦ castLin (g i) := by
    intro g m
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, rfl⟩
  have key : ∀ m, m ≤ Fintype.card ι → ∃ g : ℕ → ι → ℤ,
      (∀ i j, i ≤ j → j < m → F (g i) ≤ F (g j)) ∧
      LinearIndependent ℝ (fun i : Fin m ↦ castLin (g i)) ∧
      ∀ j < m, ∀ x, F x < F (g j) → castLin x ∈ Submodule.span ℝ (castLin ∘ g '' Set.Iio j) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨fun _ ↦ 0, fun _ _ _ h ↦ absurd h (Nat.not_lt_zero _), linearIndependent_empty_type,
        fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨g, h1, h2, h3⟩ := ih (by omega)
      set V := Submodule.span ℝ (Set.range fun i : Fin m ↦ castLin (g i)) with hV
      have hex : ∃ x : ι → ℤ, castLin x ∉ V := by
        by_contra! h
        have htop : V = ⊤ := by
          rw [eq_top_iff, ← (Pi.basisFun ℝ ι).span_eq, Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          have : (Pi.basisFun ℝ ι) i = castLin (Pi.single i 1) := by
            ext k
            simp [Pi.single_apply]
          rw [SetLike.mem_coe, this]
          exact h _
        have hle : Module.finrank ℝ V ≤ m := by
          have := finrank_range_le_card (R := ℝ) fun i : Fin m ↦ castLin (g i)
          rwa [Set.finrank, Fintype.card_fin] at this
        rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hle
        omega
      obtain ⟨x₀, hx₀⟩ := hex
      obtain ⟨a, ⟨haC, -⟩, hamin⟩ := Set.exists_min_image
        ({x | castLin x ∉ V} ∩ {x | F x ≤ F x₀}) F ((hfin _).subset Set.inter_subset_right)
        ⟨x₀, hx₀, show F x₀ ≤ F x₀ from le_refl _⟩
      have hmin : ∀ y, castLin y ∉ V → F a ≤ F y := fun y hy ↦ by
        by_cases hy' : F y ≤ F x₀
        · exact hamin y ⟨hy, hy'⟩
        · exact (hamin x₀ ⟨hx₀, show F x₀ ≤ F x₀ from le_refl _⟩).trans (le_of_not_ge hy')
      have hVi : ∀ i ≤ m, Submodule.span ℝ (castLin ∘ g '' Set.Iio i) ≤ V := fun i hi ↦ by
        rw [hV, ← himg]
        exact Submodule.span_mono (Set.image_mono (Set.Iio_subset_Iio hi))
      have hga : ∀ i < m, F (g i) ≤ F a := fun i hi ↦ by
        by_contra! hlt
        exact haC (hVi i hi.le (h3 i hi a hlt))
      let g' : ℕ → ι → ℤ := fun i ↦ if i < m then g i else a
      have hg'm : g' m = a := by simp [g']
      have hg'lt : ∀ i < m, g' i = g i := fun i hi ↦ by simp [g', hi]
      have hspan : ∀ j ≤ m, castLin ∘ g' '' Set.Iio j = castLin ∘ g '' Set.Iio j := fun j hj ↦
        Set.image_congr fun i hi ↦ by simp [hg'lt i (lt_of_lt_of_le hi hj)]
      refine ⟨g', fun i j hij hj ↦ ?_, ?_, fun j hj x hx ↦ ?_⟩
      · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [hg'lt i (by omega), hg'lt j hj]
          exact h1 i j hij hj
        · rcases eq_or_lt_of_le hij with rfl | hi
          · exact le_refl _
          · rw [hg'lt i hi, hg'm]
            exact hga i hi
      · have : (fun i : Fin (m + 1) ↦ castLin (g' i)) =
            Fin.snoc (fun i : Fin m ↦ castLin (g i)) (castLin a) := by
          funext i
          refine Fin.lastCases ?_ (fun i ↦ ?_) i
          · simp [hg'm]
          · simp [hg'lt i i.2]
        rw [this]
        exact h2.finSnoc haC
      · rw [hspan j (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [hg'lt j hj] at hx
          exact h3 j hj x hx
        · rw [hg'm] at hx
          rw [himg, ← hV]
          by_contra hxV
          exact absurd (hmin x hxV) (not_le.mpr hx)
  obtain ⟨g, h1, h2, h3⟩ := key _ le_rfl
  refine ⟨fun j ↦ g j, fun i j hij ↦ h1 i j hij j.2, h2, fun j x hx ↦ ?_⟩
  have : castLin ∘ (fun j : Fin (Fintype.card ι) ↦ g j) '' Set.Iio j =
      castLin ∘ g '' Set.Iio (j : ℕ) := by
    ext v
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, lt_trans hi j.2⟩, hi, rfl⟩
  rw [this]
  exact h3 j j.2 x hx

/-- **Gram–Schmidt step** ([schmidt1980], Ch. IV, Lemma 1D). -/
lemma exists_linearMap_one_le (b : Fin (Fintype.card ι) → ι → ℝ) (lam : Fin (Fintype.card ι) → ℝ)
    (hmono : Monotone lam) (hpos : ∀ j, 0 < lam j) (W : Set (ι → ℝ))
    (hW : ∀ v ∈ W, ∀ k, v ∉ Submodule.span ℝ (b '' Set.Iio k) → lam k ≤ ‖v‖) :
    ∃ T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ), LinearMap.det T = (∏ j, lam j)⁻¹ ∧
      ∀ v ∈ W, v ≠ 0 → 1 ≤ ∑ i, T v i ^ 2 := by
  classical
  let P : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ ι) = Fintype.card (Fin (Fintype.card ι)) := by
    simp
  let e := InnerProductSpace.gramSchmidtOrthonormalBasis hfin (fun j ↦ P (b j))
  let D : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι :=
    e.toBasis.constr ℝ fun j ↦ (lam j)⁻¹ • e j
  have hD : ∀ u j, e.repr (D u) j = (lam j)⁻¹ * e.repr u j := by
    intro u j
    simp [D, Module.Basis.constr_apply_fintype, map_sum, map_smul, OrthonormalBasis.repr_self,
      Pi.single_apply, mul_comm]
  refine ⟨P.symm.toLinearMap ∘ₗ D ∘ₗ P.symm.symm.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.det_conj, ← LinearMap.det_toMatrix e.toBasis, ← Finset.prod_inv_distrib]
    have : LinearMap.toMatrix e.toBasis e.toBasis D = Matrix.diagonal fun j ↦ (lam j)⁻¹ := by
      ext i j
      simp [LinearMap.toMatrix_apply, hD, Matrix.diagonal_apply]
    rw [this, Matrix.det_diagonal]
  · intro v hv hv0
    set w := e.repr (P v) with hw
    have hnorm : ∀ u : EuclideanSpace ℝ ι, ‖u‖ ^ 2 = ∑ j, (e.repr u j) ^ 2 := fun u ↦ by
      rw [← EuclideanSpace.real_norm_sq_eq, LinearIsometryEquiv.norm_map]
    have hsum : ∑ i, (P.symm (D (P v))) i ^ 2 = ∑ j, ((lam j)⁻¹ * w j) ^ 2 := by
      have : ∑ i, (P.symm (D (P v))) i ^ 2 = ‖D (P v)‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]; rfl
      rw [this, hnorm]
      simp_rw [hD, hw]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_symm]
    rw [hsum]
    have hw0 : w ≠ 0 := by
      intro h
      apply hv0
      have : P v = 0 := e.repr.injective (by rw [← hw, h, map_zero])
      simpa using congrArg P.symm this
    obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
      by_contra! h
      exact hw0 (by ext j; simpa using h j)
    set K := Finset.univ.filter fun j ↦ w j ≠ 0
    have hK : K.Nonempty := ⟨j₀, by simp [K, hj₀]⟩
    set k := K.max' hK
    have hwk : w k ≠ 0 := by simpa [K] using K.max'_mem hK
    have hwj : ∀ j, k < j → w j = 0 := fun j hj ↦ by
      by_contra h
      exact absurd (K.le_max' j (by simp [K, h])) (not_le.mpr hj)
    have hnot : v ∉ Submodule.span ℝ (b '' Set.Iio k) := by
      intro hmem
      have h1 := Submodule.apply_mem_span_image_of_mem_span P.toLinearMap hmem
      rw [← Set.image_comp] at h1
      have h2 : Submodule.span ℝ ((P.toLinearMap ∘ b) '' Set.Iio k) ≤
          LinearMap.ker (innerₛₗ ℝ (e k)) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, hi, rfl⟩
        exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular hfin (fun j ↦ P (b j)) hi
      have h3 := h2 h1
      rw [LinearMap.mem_ker, innerₛₗ_apply_apply] at h3
      exact hwk (by rw [hw, OrthonormalBasis.repr_apply_apply]; exact h3)
    have hlam : lam k ≤ ‖P v‖ := by
      refine (hW v hv k hnot).trans ?_
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
      exact PiLp.norm_apply_le (P v) i
    have hk0 := hpos k
    calc (1 : ℝ) ≤ (lam k)⁻¹ ^ 2 * ‖P v‖ ^ 2 := by
          rw [← mul_pow]
          refine one_le_pow₀ ?_
          rw [inv_mul_eq_div, one_le_div hk0]
          exact hlam
      _ = ∑ j, ((lam k)⁻¹ * w j) ^ 2 := by
          rw [hnorm, Finset.mul_sum, ← hw]
          simp_rw [mul_pow]
      _ ≤ ∑ j, ((lam j)⁻¹ * w j) ^ 2 := by
          refine Finset.sum_le_sum fun j _ ↦ ?_
          by_cases hjk : j ≤ k
          · rw [mul_pow, mul_pow]
            gcongr
            · exact hpos j
            · exact hmono hjk
          · simp [hwj j (not_le.mp hjk)]

/-- **Minkowski's first theorem**, in the form needed here: if the image of `ℤⁿ` under `T` has
no nonzero point in the open unit ball, then `1 ≤ n ^ n * |det T|`. -/
lemma one_le_det_of_forall [Nonempty ι] (T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (hT : LinearMap.det T ≠ 0)
    (h : ∀ x : ι → ℤ, x ≠ 0 → 1 ≤ ∑ i, T (castLin x) i ^ 2) :
    1 ≤ (Fintype.card ι : ℝ) ^ Fintype.card ι * |LinearMap.det T| := by
  classical
  set n := Fintype.card ι with hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos
  have hnR : (0 : ℝ) < n := by linarith
  by_contra hlt
  push Not at hlt
  have hbij : Function.Bijective T :=
    (Module.End.isUnit_iff _).mp ((LinearMap.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hT))
  let e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) := LinearEquiv.ofBijective T hbij
  let B : Module.Basis ι ℝ (ι → ℝ) := (Pi.basisFun ℝ ι).map e
  have hB : ∀ i, B i = T (Pi.single i 1) := fun i ↦ by
    simp [B, e, LinearEquiv.ofBijective_apply]
  have hdetB : (Matrix.of B).det = LinearMap.det T := by
    rw [← LinearMap.det_toMatrix', ← Matrix.det_transpose]
    congr 1
  set r : ℝ := (n : ℝ)⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hnR
  let s : Set (ι → ℝ) := Set.pi Set.univ fun _ ↦ Set.Ioo (-r) r
  have : Countable (Submodule.span ℤ (Set.range B)).toAddSubgroup :=
    inferInstanceAs (Countable (Submodule.span ℤ (Set.range B)))
  have hvol : MeasureTheory.volume (ZSpan.fundamentalDomain B) * 2 ^ Module.finrank ℝ (ι → ℝ) <
      MeasureTheory.volume s := by
    rw [ZSpan.volume_fundamentalDomain, hdetB, Real.volume_pi_Ioo,
      Module.finrank_fintype_fun_eq_card, Finset.prod_const, Finset.card_univ, ← hn,
      ← ENNReal.ofReal_pow (by linarith), ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num),
      ← ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_lt_ofReal_iff (pow_pos (by linarith) _)]
    have h1 : |LinearMap.det T| < r ^ n := by
      rw [hr, inv_pow, ← one_div, lt_div_iff₀ (by positivity)]
      linarith
    calc |LinearMap.det T| * 2 ^ n < r ^ n * 2 ^ n := by gcongr
      _ = (r - -r) ^ n := by rw [← mul_pow]; ring_nf
  obtain ⟨z, hz0, hzs⟩ := MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
    (ZSpan.isAddFundamentalDomain' B MeasureTheory.volume)
    (s := s) (fun x hx ↦ by
      simp only [s, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies, Pi.neg_apply] at hx ⊢
      exact fun i ↦ ⟨by linarith [(hx i).2], by linarith [(hx i).1]⟩)
    (convex_pi fun i _ ↦ convex_Ioo _ _) hvol
  have hzmem : (z : ι → ℝ) ∈ Submodule.span ℤ (Set.range B) := z.2
  rw [Submodule.mem_span_range_iff_exists_fun] at hzmem
  obtain ⟨k, hk⟩ := hzmem
  have hkz : T (castLin k) = z := by
    rw [← hk]
    have : castLin k = ∑ i, (k i : ℝ) • Pi.single i (1 : ℝ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, hB, Int.cast_smul_eq_zsmul]
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hz0
    ext1
    rw [← hkz]
    simp
  have h1 := h k hk0
  rw [hkz] at h1
  have h2 : ∑ i, (z : ι → ℝ) i ^ 2 < ∑ _i : ι, r ^ 2 := by
    refine Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ ↦ ?_
    simp only [s, Set.mem_pi, Set.mem_univ, Set.mem_Ioo, true_implies] at hzs
    exact sq_lt_sq' (hzs i).1 (hzs i).2
  have h3 : ∑ _i : ι, r ^ 2 ≤ 1 := by
    rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul, hr]
    field_simp
    exact hn1
  linarith

/-- The linear map `v ↦ (Lᵢ(v) / aᵢ)ᵢ`. -/
noncomputable def scaleMap  [DecidableEq ι] (L : Matrix ι ι ℝ) (a : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  Matrix.toLin' (diagonal (fun i ↦ (a i)⁻¹) * L)

lemma scaleMap_castLin  [DecidableEq ι] (L : Matrix ι ι ℝ) (a : ι → ℝ) (x : ι → ℤ) (i : ι) :
    scaleMap L a (castLin x) i = eval L x i / a i := by
  simp only [scaleMap, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, mulVec_diagonal, eval]
  rw [div_eq_inv_mul]
  rfl

lemma det_scaleMap  [DecidableEq ι] (L : Matrix ι ι ℝ) (a : ι → ℝ) :
    LinearMap.det (scaleMap L a) = (∏ i, a i)⁻¹ * L.det := by
  rw [scaleMap, LinearMap.det_toLin', det_mul, det_diagonal, Finset.prod_inv_distrib]

lemma mem_box_smul_iff [DecidableEq ι] [Nonempty ι] (L : Matrix ι ι ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (x : ι → ℤ) (t : ℝ) : x ∈ box L (t • a) ↔ ‖scaleMap L a (castLin x)‖ ≤ t := by
  have hiff : ∀ i, |eval L x i| ≤ (t • a) i ↔ ‖scaleMap L a (castLin x) i‖ ≤ t := fun i ↦ by
    rw [scaleMap_castLin, Real.norm_eq_abs, abs_div, abs_of_pos (ha i), div_le_iff₀ (ha i),
      Pi.smul_apply, smul_eq_mul]
  rw [mem_box]
  simp_rw [hiff]
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (h i))).mpr h
  · exact fun h i ↦ (norm_le_pi_norm _ i).trans h

lemma finite_setOf_norm_scaleMap_le  [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0) {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (R : ℝ) : {x | ‖scaleMap L a (castLin x)‖ ≤ R}.Finite := by
  have hdet : LinearMap.det (scaleMap L a) ≠ 0 := by
    rw [det_scaleMap]
    exact mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (ha i).ne')) hL
  have hinj : Function.Injective (scaleMap L a) :=
    ((Module.End.isUnit_iff _).mp
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (Ne.isUnit hdet))).injective
  obtain ⟨K, -, hK⟩ := (scaleMap L a).injective_iff_antilipschitz.mp hinj
  refine ((isCompact_closedBall (0 : ι → ℤ) (K * R)).finite_of_discrete).subset fun x hx ↦ ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  have h1 : ‖x‖ ≤ ‖castLin x‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
    have := norm_le_pi_norm (castLin x) i
    simpa [Int.norm_eq_abs, Real.norm_eq_abs] using this
  have h2 := ZeroHomClass.bound_of_antilipschitz (scaleMap L a) hK (castLin x)
  calc ‖x‖ ≤ ‖castLin x‖ := h1
    _ ≤ K * ‖scaleMap L a (castLin x)‖ := h2
    _ ≤ K * R := by gcongr; exact hx

lemma finrank_span_image_Iio_le {n : ℕ} (f : Fin n → ι → ℝ) (j : Fin n) :
    Module.finrank ℝ (Submodule.span ℝ (f '' Set.Iio j)) ≤ j := by
  classical
  rw [← Finset.coe_Iio, ← Finset.coe_image]
  refine (finrank_span_finset_le_card _).trans (Finset.card_image_le.trans ?_)
  simp

/-- **Minkowski's second theorem for parallelepipeds.** Let `L₁, …, Lₙ` be linearly independent
linear forms in `n` variables with real coefficients and let `a₁, …, aₙ` be positive real numbers.
Then there are positive real numbers `λ₁ ≤ ⋯ ≤ λₙ` (the successive minima of the parallelepiped
`Π(a) = {x : |Lᵢ(x)| ≤ aᵢ}`) and linearly independent integer points `g₁, …, gₙ` such that

* `gⱼ ∈ λⱼ Π(a)`;
* for `t < λⱼ` the integer points of `t Π(a)` span a module of rank less than `j`;
* `λ₁ ⋯ λₙ * a₁ ⋯ aₙ ≤ n ^ n * |det L|`.

(The indices are shifted by one in the formal statement.) -/
theorem exists_successive_minima [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∃ (lam : Fin (Fintype.card ι) → ℝ) (g : Fin (Fintype.card ι) → ι → ℤ),
      Monotone lam ∧ (∀ j, 0 < lam j) ∧ LinearIndependent ℤ g ∧
      (∀ j, g j ∈ box L (lam j • a)) ∧
      (∀ j, ∀ t < lam j, Set.finrank ℤ (box L (t • a)) ≤ j) ∧
      (∏ j, lam j) * ∏ i, a i ≤ (Fintype.card ι : ℝ) ^ Fintype.card ι * |L.det| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨fun _ ↦ 1, fun _ ↦ 0, fun _ _ _ ↦ le_rfl, fun _ ↦ one_pos, ?_, ?_, ?_, ?_⟩
    · have : IsEmpty (Fin (Fintype.card ι)) := by rw [Fintype.card_eq_zero]; infer_instance
      exact linearIndependent_empty_type
    · intro j; exact (Fin.elim0 (Fintype.card_eq_zero (α := ι) ▸ j))
    · intro j; exact (Fin.elim0 (Fintype.card_eq_zero (α := ι) ▸ j))
    · simp [Matrix.det_isEmpty]
  set A := scaleMap L a
  set F : (ι → ℤ) → ℝ := fun x ↦ ‖A (castLin x)‖ with hFdef
  have hdetA : LinearMap.det A ≠ 0 := by
    rw [det_scaleMap]
    exact mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ ↦ (ha i).ne')) hL
  have hAinj : Function.Injective A := by
    have := LinearMap.isUnit_iff_isUnit_det A |>.mpr (Ne.isUnit hdetA)
    exact (Module.End.isUnit_iff A).mp this |>.injective
  have hF : ∀ x, x ≠ 0 → 0 < F x := fun x hx ↦ norm_pos_iff.mpr fun h ↦
    hx (castLin_injective (hAinj (h.trans (map_zero A).symm) |>.trans (map_zero _).symm))
  obtain ⟨g, hmono, hind, hgreedy⟩ :=
    exists_greedy F (finite_setOf_norm_scaleMap_le L hL ha)
  have hgpos : ∀ j, 0 < F (g j) := fun j ↦ hF _ fun h ↦ hind.ne_zero j (by simp [h])
  obtain ⟨T, hTdet, hT⟩ := exists_linearMap_one_le (fun j ↦ A (castLin (g j))) (F ∘ g) hmono
    hgpos (Set.range fun x ↦ A (castLin x)) (by
      rintro _ ⟨x, rfl⟩ k hk
      by_contra hlt
      refine hk ?_
      have := Submodule.apply_mem_span_image_of_mem_span A (hgreedy k x (not_le.mp hlt))
      rwa [← Set.image_comp] at this)
  have hdet : LinearMap.det (T ∘ₗ A) ≠ 0 := by
    rw [LinearMap.det_comp, hTdet]
    exact mul_ne_zero (inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ ↦ (hgpos j).ne')) hdetA
  have key := one_le_det_of_forall (T ∘ₗ A) hdet fun x hx ↦ hT _ ⟨x, rfl⟩ fun h ↦
    (hF x hx).ne' (by simp [hFdef, h])
  refine ⟨F ∘ g, g, hmono, hgpos, LinearIndependent.of_comp castLin (hind.restrict_scalars' ℤ),
    fun j ↦ (mem_box_smul_iff L ha _ _).mpr le_rfl, fun j t ht ↦ ?_, ?_⟩
  · refine le_trans (setFinrank_le_finrank _ _ fun x hx ↦ hgreedy j x ?_)
      (finrank_span_image_Iio_le _ j)
    exact ((mem_box_smul_iff L ha x t).mp hx).trans_lt ht
  · rw [LinearMap.det_comp, hTdet, det_scaleMap] at key
    have hP : 0 < ∏ j, (F ∘ g) j := Finset.prod_pos fun j _ ↦ hgpos j
    have hQ : 0 < ∏ i, a i := Finset.prod_pos fun i _ ↦ ha i
    rw [abs_mul, abs_mul, abs_inv, abs_inv, abs_of_pos hP, abs_of_pos hQ] at key
    have : (∏ j, (F ∘ g) j) * (∏ i, a i) * 1 ≤
        (∏ j, (F ∘ g) j) * (∏ i, a i) * ((Fintype.card ι : ℝ) ^ Fintype.card ι *
          ((∏ j, (F ∘ g) j)⁻¹ * ((∏ i, a i)⁻¹ * |L.det|))) := by gcongr
    convert this using 1
    · ring
    · field_simp

end Schmidt
