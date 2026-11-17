module

public import Heights.SubspaceTheorem.Index
public import Heights.SubspaceTheorem.LinearForms
public import Heights.SubspaceTheorem.HasseTaylor
public import Heights.SubspaceTheorem.PolynomialTheorem
public import Heights.SubspaceTheorem.GeneralizedRothLemma

/-!
# Step 2 of the proof: parallelepipeds of rank `n - 1`

This file contains the proof of the Subspace Theorem for parallelepipeds whose integer points
span a module of rank `n - 1` ([evertse1993], Section 3.4), assuming the Roth machinery (the
polynomial theorem `Schmidt.polynomial_theorem` and the generalisation of Roth's lemma
`Schmidt.generalized_roth_lemma`).

The main result is `Schmidt.parallelepiped_theorem_of_rank`. It is deduced from the fact that the
heights of the hyperplanes spanned by the integer points of the parallelepipeds under
consideration are bounded (`Schmidt.norm_normal_le`), which in turn is proved, after rounding the
exponents `log a_k / log Q(a)` (`Schmidt.exists_exponents`), by the argument of [evertse1993],
Section 3.4 (`Schmidt.norm_normal_le_of_exponents`).
-/

@[expose] public section

open Matrix

namespace Schmidt

variable {ι : Type*} [Fintype ι]

/-! ### Integer vectors orthogonal to a module of rank `n - 1` -/

/-- If the entries of the integer vector `c` are coprime and `d` divides `t * c j` for every `j`,
then `d` divides `t`. -/
lemma dvd_of_forall_dvd_mul {c : ι → ℤ} (hc : Finset.univ.gcd c = 1) {d t : ℤ}
    (h : ∀ j, d ∣ t * c j) : d ∣ t := by
  have h1 : d ∣ Finset.univ.gcd fun j ↦ t * c j := Finset.dvd_gcd fun j _ ↦ h j
  rw [Finset.gcd_mul_left, hc, mul_one] at h1
  exact dvd_normalize_iff.mp h1

lemma dotProduct_self_pos {c : ι → ℤ} (hc : c ≠ 0) : 0 < c ⬝ᵥ c :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (c i))
    (Ne.symm (dotProduct_self_eq_zero.not.mpr hc))

lemma ne_zero_of_gcd_eq_one {c : ι → ℤ} (hc : Finset.univ.gcd c = 1) : c ≠ 0 := by
  rintro rfl
  have h0 : Finset.univ.gcd (0 : ι → ℤ) = 0 := Finset.gcd_eq_zero_iff.mpr fun _ _ ↦ rfl
  rw [h0] at hc
  exact zero_ne_one hc

/-- If the integer points of `S` span a module of rank `n - 1` and `c ≠ 0` is orthogonal to `S`,
then for every index `k` there is a nonsingular integer matrix whose `k`-th column is `c` and whose
other columns belong to `S`. -/
lemma exists_matrix_of_finrank [DecidableEq ι] {S : Set (ι → ℤ)}
    (hS : Set.finrank ℤ S + 1 = Fintype.card ι) {c : ι → ℤ} (hc : c ≠ 0)
    (hcS : ∀ x ∈ S, c ⬝ᵥ x = 0) (k : ι) :
    ∃ T : Matrix ι ι ℤ, T.det ≠ 0 ∧ (∀ i, T i k = c i) ∧ ∀ j ≠ k, (fun i ↦ T i j) ∈ S := by
  let φ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
    { toFun := fun x i ↦ (x i : ℚ)
      map_add' := fun x y ↦ by ext; simp
      map_smul' := fun r x ↦ by ext; simp }
  have hφ : ∀ x i, φ x i = (x i : ℚ) := fun _ _ ↦ rfl
  have hφinj : Function.Injective φ := fun x y h ↦ by
    ext i
    have := congrFun h i
    rw [hφ, hφ] at this
    exact_mod_cast this
  have hdot : ∀ x y : ι → ℤ, φ x ⬝ᵥ φ y = ((x ⬝ᵥ y : ℤ) : ℚ) := fun x y ↦ by
    simp [dotProduct, hφ]
  obtain ⟨m, f, hfS, hfli, hm⟩ : ∃ (m : ℕ) (f : Fin m → ι → ℚ), (∀ i, f i ∈ φ '' S) ∧
      LinearIndependent ℚ f ∧ m = Module.finrank ℚ (Submodule.span ℚ (φ '' S)) := by
    obtain ⟨f, hfS, -, hfli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ (φ '' S)
    exact ⟨_, f, hfS, hfli, rfl⟩
  choose g hgS hg using hfS
  -- `m + 1 ≤ n`
  have hcf : φ c ∉ Submodule.span ℚ (Set.range f) := by
    intro hmem
    have key : ∀ u ∈ Submodule.span ℚ (Set.range f), φ c ⬝ᵥ u = 0 := by
      intro u hu
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        rw [← hg i, hdot, hcS _ (hgS i)]
        simp
      | zero => simp
      | add u v _ _ hu hv => rw [dotProduct_add, hu, hv, add_zero]
      | smul r u _ hu => rw [dotProduct_smul, hu, smul_zero]
    have h0 := key _ hmem
    rw [dotProduct_self_eq_zero] at h0
    exact hc (hφinj (by simpa using h0))
  have hli : LinearIndependent ℚ (Fin.cons (φ c) f : Fin (m + 1) → ι → ℚ) :=
    linearIndependent_finCons.mpr ⟨hfli, hcf⟩
  have h1 : m + 1 ≤ Fintype.card ι := by
    simpa using hli.fintype_card_le_finrank
  -- `n - 1 ≤ m`
  have hmap : ∀ w ∈ Submodule.span ℤ S, φ w ∈ Submodule.span ℚ (φ '' S) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact Submodule.subset_span (Set.mem_image_of_mem _ hw)
    | zero => simp
    | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
    | smul r u _ hu => rw [map_smul]; exact zsmul_mem hu r
  have h2 : Set.finrank ℤ S ≤ m := by
    let b := Module.finBasis ℤ (Submodule.span ℤ S)
    have hb : LinearIndependent ℚ fun i ↦ φ (b i : ι → ℤ) := by
      have := (b.linearIndependent.map' (Submodule.span ℤ S).subtype
        (Submodule.ker_subtype _)).map' φ (LinearMap.ker_eq_bot.mpr hφinj)
      exact this.localization ℚ (nonZeroDivisors ℤ)
    have hsub : Submodule.span ℚ (Set.range fun i ↦ φ (b i : ι → ℤ)) ≤
        Submodule.span ℚ (φ '' S) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hmap _ (b i).2
    have := Submodule.finrank_mono hsub
    rwa [finrank_span_eq_card hb, Fintype.card_fin, ← hm] at this
  have hcard : Fintype.card ι = Fintype.card (Fin (m + 1)) := by
    rw [Fintype.card_fin]
    omega
  let e₀ : ι ≃ Fin (m + 1) := Fintype.equivOfCardEq hcard
  let e : ι ≃ Fin (m + 1) := (Equiv.swap k (e₀.symm 0)).trans e₀
  have hek : e k = 0 := by simp [e]
  let col : Fin (m + 1) → ι → ℤ := Fin.cons c g
  have hcol : ∀ p, φ (col p) = (Fin.cons (φ c) f : Fin (m + 1) → ι → ℚ) p := by
    intro p
    refine Fin.cases ?_ (fun i ↦ ?_) p
    · simp [col]
    · simp [col, hg]
  refine ⟨Matrix.of fun i j ↦ col (e j) i, ?_, fun i ↦ by simp [hek, col], fun j hj ↦ ?_⟩
  · have hT : LinearIndependent ℚ
        ((Matrix.of fun i j ↦ col (e j) i).map (Int.cast : ℤ → ℚ)).col := by
      have : ((Matrix.of fun i j ↦ col (e j) i).map (Int.cast : ℤ → ℚ)).col =
          (Fin.cons (φ c) f : Fin (m + 1) → ι → ℚ) ∘ e := by
        ext j i
        simp [Matrix.col, ← hcol, hφ]
      rw [this]
      exact hli.comp _ e.injective
    rw [Matrix.linearIndependent_col_iff_isUnit, Matrix.isUnit_iff_isUnit_det] at hT
    have h0 := hT.ne_zero
    intro hdet
    apply h0
    have := congrArg (Int.cast : ℤ → ℚ) hdet
    rw [Int.cast_det] at this
    simpa using this
  · have he : e j ≠ 0 := fun h ↦ hj (e.injective (h.trans hek.symm))
    obtain ⟨p, hp⟩ := Fin.exists_succ_eq_of_ne_zero he
    change col (e j) ∈ S
    rw [← hp]
    simpa [col] using hgS p

/-- If the `k`-th column of `T` is `c` and `y` is orthogonal to the other columns of `T`, then
`yᵀ T = (y ⬝ᵥ c) eₖᵀ`. -/
lemma vecMul_eq_of_cols [DecidableEq ι] {T : Matrix ι ι ℤ} {c y : ι → ℤ} {k : ι}
    (hTk : ∀ i, T i k = c i) (hT : ∀ j ≠ k, y ⬝ᵥ (fun i ↦ T i j) = 0) :
    y ᵥ* T = (y ⬝ᵥ c) • Pi.single k 1 := by
  ext j
  by_cases hj : j = k
  · subst hj
    simp [vecMul, funext hTk]
  · simpa [hj, vecMul] using hT j hj

lemma dotProduct_self_dvd_det [DecidableEq ι] {T : Matrix ι ι ℤ} {c : ι → ℤ} {k : ι}
    (hc : Finset.univ.gcd c = 1) (hTk : ∀ i, T i k = c i)
    (hT : ∀ j ≠ k, c ⬝ᵥ (fun i ↦ T i j) = 0) : c ⬝ᵥ c ∣ T.det := by
  have h := congrArg (· ᵥ* T.adjugate) (vecMul_eq_of_cols hTk hT)
  simp only [vecMul_vecMul, mul_adjugate, vecMul_smul, vecMul_one, smul_vecMul,
    single_one_vecMul] at h
  refine dvd_of_forall_dvd_mul hc fun j ↦ ⟨T.adjugate k j, ?_⟩
  simpa using congrFun h j

/-- If the integer points of `S` span a module of rank `n - 1` and the primitive vector `c` is
orthogonal to `S`, then every integer vector orthogonal to `S` is an integer multiple of `c`. -/
lemma exists_eq_smul_of_finrank [DecidableEq ι] {S : Set (ι → ℤ)}
    (hS : Set.finrank ℤ S + 1 = Fintype.card ι) {c : ι → ℤ} (hc : Finset.univ.gcd c = 1)
    (hcS : ∀ x ∈ S, c ⬝ᵥ x = 0) {y : ι → ℤ} (hyS : ∀ x ∈ S, y ⬝ᵥ x = 0) :
    ∃ μ : ℤ, y = μ • c := by
  have hc0 := ne_zero_of_gcd_eq_one hc
  obtain ⟨k, -⟩ := Function.ne_iff.mp hc0
  obtain ⟨T, hdet, hTk, hTS⟩ := exists_matrix_of_finrank hS hc0 hcS k
  have hcT := vecMul_eq_of_cols (y := c) hTk fun j hj ↦ hcS _ (hTS j hj)
  have hyT := vecMul_eq_of_cols (y := y) hTk fun j hj ↦ hyS _ (hTS j hj)
  have hcc := (dotProduct_self_pos hc0).ne'
  have h0 : ((c ⬝ᵥ c) • y - (y ⬝ᵥ c) • c) ᵥ* T = 0 := by
    rw [sub_vecMul, smul_vecMul, smul_vecMul, hcT, hyT, smul_comm, sub_self]
  have heq := sub_eq_zero.mp (eq_zero_of_vecMul_eq_zero hdet h0)
  have hdvd : c ⬝ᵥ c ∣ y ⬝ᵥ c := dvd_of_forall_dvd_mul hc fun j ↦ ⟨y j, by
    simpa using (congrFun heq j).symm⟩
  obtain ⟨μ, hμ⟩ := hdvd
  refine ⟨μ, funext fun j ↦ mul_left_cancel₀ hcc ?_⟩
  have := congrFun heq j
  simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
  rw [this, hμ, mul_assoc]

/-- The linear form `M_k(y) = ∑ⱼ adj(L)ⱼₖ yⱼ`, the `k`-th coordinate of `adj(L)ᵀ y`. -/
noncomputable def adjForm [DecidableEq ι] (L : Matrix ι ι ℝ) (y : ι → ℤ) (k : ι) : ℝ :=
  ∑ j, L.adjugate j k * y j

lemma adjForm_eq_det [DecidableEq ι] (L : Matrix ι ι ℝ) (y : ι → ℤ) (k : ι) :
    adjForm L y k = (L.updateRow k fun j ↦ (y j : ℝ)).det := by
  rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose]
  simp [adjForm, mulVec, dotProduct]

/-- The identity `det(L) (y ⬝ x) = ∑ₖ M_k(y) L_k(x)`. -/
lemma det_mul_dotProduct [DecidableEq ι] (L : Matrix ι ι ℝ) (y x : ι → ℤ) :
    L.det * ((y ⬝ᵥ x : ℤ) : ℝ) = ∑ k, adjForm L y k * eval L x k := by
  have h1 : ∑ k, adjForm L y k * eval L x k =
      ((fun j ↦ (y j : ℝ)) ᵥ* L.adjugate) ⬝ᵥ (L *ᵥ fun j ↦ (x j : ℝ)) := by
    simp [dotProduct, vecMul, adjForm, eval, mul_comm]
  rw [h1, dotProduct_mulVec, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one, smul_dotProduct]
  simp [dotProduct]

/-- The entries of the adjugate of a real matrix with algebraic entries are algebraic. -/
lemma isAlgebraic_adjugate [DecidableEq ι] (L : Matrix ι ι ℝ)
    (hL : ∀ i j, IsAlgebraic ℚ (L i j)) (i j : ι) : IsAlgebraic ℚ (L.adjugate i j) := by
  rw [isAlgebraic_iff_isIntegral, ← mem_integralClosure_iff, adjugate_apply, Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ ↦ ?_
  rw [Units.smul_def]
  refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun l _ ↦ ?_) _
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  · rw [mem_integralClosure_iff, ← isAlgebraic_iff_isIntegral]
    exact hL _ _

/-- The key bound: if the integer points of `Π(a)` span a module of rank `n - 1` and `c` is a
primitive normal vector, then `|M_k(c)| ≤ n! ∏_{i ≠ k} aᵢ`. -/
lemma abs_adjForm_le [DecidableEq ι] (L : Matrix ι ι ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hrank : Set.finrank ℤ (box L a) + 1 = Fintype.card ι) {c : ι → ℤ}
    (hc : Finset.univ.gcd c = 1) (hcbox : ∀ x ∈ box L a, c ⬝ᵥ x = 0) (k : ι) :
    |adjForm L c k| ≤ (Fintype.card ι).factorial * ∏ i ∈ Finset.univ.erase k, a i := by
  have hc0 := ne_zero_of_gcd_eq_one hc
  obtain ⟨T, hdet, hTk, hTS⟩ := exists_matrix_of_finrank hrank hc0 hcbox k
  have hdvd : c ⬝ᵥ c ∣ T.det := dotProduct_self_dvd_det hc hTk fun j hj ↦ hcbox _ (hTS j hj)
  have hcc : 0 < c ⬝ᵥ c := dotProduct_self_pos hc0
  have hccR : (0 : ℝ) < ((c ⬝ᵥ c : ℤ) : ℝ) := by exact_mod_cast hcc
  have hle : ((c ⬝ᵥ c : ℤ) : ℝ) ≤ |(T.det : ℝ)| := by
    have := Int.le_of_dvd (abs_pos.mpr hdet) ((dvd_abs _ _).mpr hdvd)
    exact_mod_cast this
  set P : ℝ := ∏ i ∈ Finset.univ.erase k, a i with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun i _ ↦ (ha i).le
  set N : Matrix ι ι ℝ := L.updateRow k (fun j ↦ (c j : ℝ)) * T.map (Int.cast : ℤ → ℝ) with hN
  have hNdet : N.det = adjForm L c k * (T.det : ℝ) := by
    rw [hN, det_mul, adjForm_eq_det, Int.cast_det]
  have hNk : ∀ j, N k j = ((c ⬝ᵥ (fun i ↦ T i j) : ℤ) : ℝ) := by
    intro j
    simp [hN, Matrix.mul_apply, dotProduct]
  have hNi : ∀ i ≠ k, ∀ j, N i j = eval L (fun l ↦ T l j) i := by
    intro i hi j
    simp [hN, Matrix.mul_apply, eval_apply, Matrix.updateRow_ne hi]
  have hterm : ∀ σ : Equiv.Perm ι, ∏ i, |N i (σ i)| ≤ ((c ⬝ᵥ c : ℤ) : ℝ) * P := by
    intro σ
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
    by_cases hσ : σ k = k
    · rw [hσ, hNk k, funext hTk, abs_of_pos hccR]
      refine mul_le_mul_of_nonneg_left ?_ hccR.le
      refine Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) fun i hi ↦ ?_
      have hik := Finset.ne_of_mem_erase hi
      have hσi : σ i ≠ k := fun h ↦ hik (σ.injective (h.trans hσ.symm))
      rw [hNi i hik]
      exact hTS _ hσi i
    · rw [hNk, hcbox _ (hTS _ hσ)]
      simpa using mul_nonneg hccR.le hP0
  have hdetN : |N.det| ≤ (Fintype.card ι).factorial * (((c ⬝ᵥ c : ℤ) : ℝ) * P) := by
    rw [← det_transpose, det_apply']
    calc |∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Nᵀ (σ i) i|
        ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, Nᵀ (σ i) i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _σ : Equiv.Perm ι, ((c ⬝ᵥ c : ℤ) : ℝ) * P := by
          refine Finset.sum_le_sum fun σ _ ↦ ?_
          have hs : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
          rw [abs_mul, hs, one_mul, Finset.abs_prod]
          simpa using hterm σ
      _ = (Fintype.card ι).factorial * (((c ⬝ᵥ c : ℤ) : ℝ) * P) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]
  have h1 : |adjForm L c k| * ((c ⬝ᵥ c : ℤ) : ℝ) ≤
      (Fintype.card ι).factorial * P * ((c ⬝ᵥ c : ℤ) : ℝ) := calc
    |adjForm L c k| * ((c ⬝ᵥ c : ℤ) : ℝ) ≤ |adjForm L c k| * |(T.det : ℝ)| :=
      mul_le_mul_of_nonneg_left hle (abs_nonneg _)
    _ = |N.det| := by rw [hNdet, abs_mul]
    _ ≤ (Fintype.card ι).factorial * (((c ⬝ᵥ c : ℤ) : ℝ) * P) := hdetN
    _ = (Fintype.card ι).factorial * P * ((c ⬝ᵥ c : ℤ) : ℝ) := by ring
  exact le_of_mul_le_mul_right h1 hccR

/-- [evertse1993], Lemma 3.4.5 (essentially [schmidt1980], Chapter VI, Lemma 11A). Let `Π(a)` be a
parallelepiped with `a₁ ⋯ aₙ < Q(a) ^ (-ε)` whose integer points span a hyperplane `V_a`, and let
`c` be a primitive normal vector of this hyperplane, so that `H(V_a) = ‖c‖`. If `H(V_a)` is large
enough, then `Q(a) ^ C₈ ≤ H(V_a) ≤ Q(a) ^ C₉`. -/
theorem size_rpow_le_norm_normal [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ C₇ C₈ C₉ : ℝ, 0 < C₈ ∧ 0 < C₉ ∧ ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∏ i, a i < size a ^ (-ε) → Set.finrank ℤ (box L a) + 1 = Fintype.card ι →
      ∀ c : ι → ℤ, Finset.univ.gcd c = 1 → (∀ x ∈ box L a, c ⬝ᵥ x = 0) → C₇ ≤ ‖c‖ →
        size a ^ C₈ ≤ ‖c‖ ∧ ‖c‖ ≤ size a ^ C₉ := by
  classical
  set F : ℝ := ((Fintype.card ι).factorial : ℝ) with hF
  have hF0 : 0 < F := by
    rw [hF]
    exact_mod_cast Nat.factorial_pos _
  -- Liouville's inequality for the forms `M_k`
  have hLiou : ∀ k, ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ D : ℕ, ∀ x : ι → ℤ, adjForm L x k ≠ 0 →
      c₀ * ‖x‖ ^ (-(D : ℝ)) ≤ |adjForm L x k| := fun k ↦
    exists_le_abs_linearForm (fun j ↦ L.adjugate j k) fun j ↦ isAlgebraic_adjugate L halg j k
  choose c₀ hc₀ D₀ hD₀ using hLiou
  set D : ℕ := ∑ k, (D₀ k + 1) + 1 with hD
  have hDk : ∀ k, D₀ k + 1 ≤ D := fun k ↦ by
    have := Finset.single_le_sum (f := fun k ↦ D₀ k + 1) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ k)
    omega
  have hD0 : (D : ℝ) ≠ 0 := by
    rw [hD]
    positivity
  -- for every set `E` of indices, a nonzero integer vector annihilated by the `M_k`, `k ∈ E`
  have hy : ∀ E : Finset ι, ∃ y : ι → ℤ,
      (∃ y' : ι → ℤ, y' ≠ 0 ∧ ∀ k ∈ E, adjForm L y' k = 0) →
        y ≠ 0 ∧ ∀ k ∈ E, adjForm L y k = 0 := by
    intro E
    by_cases h : ∃ y' : ι → ℤ, y' ≠ 0 ∧ ∀ k ∈ E, adjForm L y' k = 0
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose y hy using hy
  set Y : ℝ := ∑ E : Finset ι, ‖y E‖ with hY
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  set B : ℝ := ∑ E : Finset ι, |L.det|⁻¹ * ∑ k, |adjForm L (y E) k| with hB
  have hBterm : ∀ E : Finset ι, 0 ≤ |L.det|⁻¹ * ∑ k, |adjForm L (y E) k| := fun E ↦
    mul_nonneg (inv_nonneg.mpr (abs_nonneg _)) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun E _ ↦ hBterm E
  set S : ℝ := ∑ k, ∑ j, |L k j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  have hdetpos : 0 < |L.det| := abs_pos.mpr hL
  set Cb : ℝ := |L.det|⁻¹ * S * F + 1 with hCb
  have hCb1 : 1 ≤ Cb := by
    have : 0 ≤ |L.det|⁻¹ * S * F := by positivity
    linarith
  have hCb0 : 0 < Cb := zero_lt_one.trans_le hCb1
  have hsum0 : 0 ≤ ∑ k, F / c₀ k := Finset.sum_nonneg fun k _ ↦ (div_pos hF0 (hc₀ k)).le
  have hBpow0 : 0 ≤ Cb * (B + 1) ^ (2 / ε) :=
    mul_nonneg hCb0.le (Real.rpow_nonneg (by linarith) _)
  set C₇ : ℝ := 1 + Cb ^ 2 + ∑ k, F / c₀ k + Y + Cb * (B + 1) ^ (2 / ε) with hC₇def
  refine ⟨C₇, ε / (2 * D), 2, by positivity, by norm_num,
    fun a ha hprod hrank c hc hcbox hC₇ ↦ ?_⟩
  have hc0 := ne_zero_of_gcd_eq_one hc
  obtain ⟨k₀, -⟩ := Function.ne_iff.mp hc0
  have : Nonempty ι := ⟨k₀⟩
  have hQ1 : 1 ≤ size a := one_le_size ha
  set Q : ℝ := size a with hQ
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hnorm1 : 1 ≤ ‖c‖ := by
    have : 0 ≤ Cb ^ 2 := sq_nonneg _
    linarith
  -- the key bound
  have hM : ∀ k, |adjForm L c k| ≤ F * ∏ i ∈ Finset.univ.erase k, a i := fun k ↦
    abs_adjForm_le L ha hrank hc hcbox k
  have hprodk : ∀ k, ∏ i ∈ Finset.univ.erase k, a i = (∏ i, a i) / a k := by
    intro k
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), mul_div_cancel_left₀ _ (ha k).ne']
  have hQε : Q ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1 (by linarith)
  -- the upper bound `‖c‖ ≤ Cb * Q`
  have hMQ : ∀ k, |adjForm L c k| ≤ F * Q := by
    intro k
    refine (hM k).trans (mul_le_mul_of_nonneg_left ?_ hF0.le)
    rw [hprodk, div_eq_mul_inv]
    calc (∏ i, a i) * (a k)⁻¹ ≤ 1 * Q :=
          mul_le_mul (hprod.le.trans hQε) (inv_le_size a k) (inv_nonneg.mpr (ha k).le)
            zero_le_one
      _ = Q := one_mul _
  have hupper : ‖c‖ ≤ Cb * Q := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hCb0.le hQ0.le)).mpr fun j ↦ ?_
    rw [Int.norm_eq_abs]
    have hI := det_mul_dotProduct L c (Pi.single j 1)
    have hcj : ((c ⬝ᵥ Pi.single j 1 : ℤ) : ℝ) = c j := by simp
    have hev : ∀ k, eval L (Pi.single j 1) k = L k j := by
      intro k
      simp [eval_apply, Pi.single_apply]
    simp only [hev, hcj] at hI
    have h1 : |L.det| * |(c j : ℝ)| ≤ F * Q * S := by
      rw [← abs_mul, hI]
      calc |∑ k, adjForm L c k * L k j| ≤ ∑ k, |adjForm L c k| * |L k j| :=
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun k _ ↦ (abs_mul _ _).le)
        _ ≤ ∑ k, F * Q * ∑ j, |L k j| := by
            refine Finset.sum_le_sum fun k _ ↦ ?_
            exact mul_le_mul (hMQ k) (Finset.single_le_sum (f := fun j ↦ |L k j|)
              (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)) (abs_nonneg _)
              (mul_nonneg hF0.le hQ0.le)
        _ = F * Q * S := by rw [Finset.mul_sum]
    calc |(c j : ℝ)| = |L.det|⁻¹ * (|L.det| * |(c j : ℝ)|) := by
          rw [inv_mul_cancel_left₀ hdetpos.ne']
      _ ≤ |L.det|⁻¹ * (F * Q * S) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hdetpos.le)
      _ = (|L.det|⁻¹ * S * F) * Q := by ring
      _ ≤ Cb * Q := mul_le_mul_of_nonneg_right (by linarith) hQ0.le
  have hCbQ : Cb ≤ Q := by
    have h1 : Cb * Cb ≤ Cb * Q := by
      have : Cb * Cb = Cb ^ 2 := (sq Cb).symm
      linarith
    exact le_of_mul_le_mul_left h1 hCb0
  refine ⟨?_, ?_⟩
  swap
  · calc ‖c‖ ≤ Cb * Q := hupper
      _ ≤ Q * Q := mul_le_mul_of_nonneg_right hCbQ hQ0.le
      _ = Q ^ (2 : ℝ) := by rw [Real.rpow_two, sq]
  -- the lower bound
  by_cases hcase : ∃ k, Q ^ (-(ε / 2)) ≤ a k ∧ adjForm L c k ≠ 0
  · obtain ⟨k, hak, hMk⟩ := hcase
    have h1 := hD₀ k c hMk
    have hp2 : 0 < Q ^ (ε / 2) := Real.rpow_pos_of_pos hQ0 _
    have hp1 : 0 < ‖c‖ ^ D₀ k := pow_pos (zero_lt_one.trans_le hnorm1) _
    have h2 : |adjForm L c k| ≤ F * Q ^ (-(ε / 2)) := by
      refine (hM k).trans (mul_le_mul_of_nonneg_left ?_ hF0.le)
      rw [hprodk, div_le_iff₀ (ha k)]
      calc ∏ i, a i ≤ Q ^ (-ε) := hprod.le
        _ = Q ^ (-(ε / 2)) * Q ^ (-(ε / 2)) := by
            rw [← Real.rpow_add hQ0]
            congr 1
            ring
        _ ≤ Q ^ (-(ε / 2)) * a k :=
            mul_le_mul_of_nonneg_left hak (Real.rpow_nonneg hQ0.le _)
    have h3 : Q ^ (ε / 2) ≤ F / c₀ k * ‖c‖ ^ D₀ k := by
      have h12 := h1.trans h2
      rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast, Real.rpow_neg hQ0.le] at h12
      have h13 := mul_le_mul_of_nonneg_right h12 (mul_pos hp1 hp2).le
      have e1 : c₀ k * (‖c‖ ^ D₀ k)⁻¹ * (‖c‖ ^ D₀ k * Q ^ (ε / 2)) = c₀ k * Q ^ (ε / 2) := by
        field_simp
      have e2 : F * (Q ^ (ε / 2))⁻¹ * (‖c‖ ^ D₀ k * Q ^ (ε / 2)) = F * ‖c‖ ^ D₀ k := by
        field_simp
      rw [e1, e2] at h13
      rw [div_mul_eq_mul_div, le_div_iff₀ (hc₀ k)]
      linarith
    have h4 : F / c₀ k ≤ ‖c‖ := by
      have := Finset.single_le_sum (f := fun k ↦ F / c₀ k)
        (fun k _ ↦ (div_pos hF0 (hc₀ k)).le) (Finset.mem_univ k)
      have h0 : 0 ≤ Cb ^ 2 := sq_nonneg _
      linarith
    have h5 : Q ^ (ε / 2) ≤ ‖c‖ ^ D := calc
      Q ^ (ε / 2) ≤ F / c₀ k * ‖c‖ ^ D₀ k := h3
      _ ≤ ‖c‖ * ‖c‖ ^ D₀ k := mul_le_mul_of_nonneg_right h4 hp1.le
      _ = ‖c‖ ^ (D₀ k + 1) := (pow_succ' _ _).symm
      _ ≤ ‖c‖ ^ D := pow_le_pow_right₀ hnorm1 (hDk k)
    calc Q ^ (ε / (2 * D)) = (Q ^ (ε / 2)) ^ ((D : ℝ)⁻¹) := by
          rw [← Real.rpow_mul hQ0.le]
          congr 1
          field_simp
      _ ≤ (‖c‖ ^ D) ^ ((D : ℝ)⁻¹) :=
          Real.rpow_le_rpow hp2.le h5 (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = ‖c‖ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), mul_inv_cancel₀ hD0,
            Real.rpow_one]
  · exfalso
    push Not at hcase
    set E : Finset ι := Finset.univ.filter fun k ↦ Q ^ (-(ε / 2)) ≤ a k with hE
    obtain ⟨hy0, hyE⟩ := hy E ⟨c, hc0, fun k hk ↦ hcase k (Finset.mem_filter.mp hk).2⟩
    have hyle : ‖y E‖ ≤ Y :=
      Finset.single_le_sum (f := fun E ↦ ‖y E‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ E)
    have hBE : |L.det|⁻¹ * ∑ k, |adjForm L (y E) k| ≤ B :=
      Finset.single_le_sum (f := fun E ↦ |L.det|⁻¹ * ∑ k, |adjForm L (y E) k|)
        (fun E _ ↦ hBterm E) (Finset.mem_univ E)
    have hQneg0 : 0 ≤ Q ^ (-(ε / 2)) := Real.rpow_nonneg hQ0.le _
    have hdot : ∀ x ∈ box L a, |((y E ⬝ᵥ x : ℤ) : ℝ)| ≤ B * Q ^ (-(ε / 2)) := by
      intro x hx
      have hI := det_mul_dotProduct L (y E) x
      have h1 : |L.det| * |((y E ⬝ᵥ x : ℤ) : ℝ)| ≤
          (∑ k, |adjForm L (y E) k|) * Q ^ (-(ε / 2)) := by
        rw [← abs_mul, hI, Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
        rw [abs_mul]
        by_cases hk : k ∈ E
        · rw [hyE k hk]
          simp
        · have hlt : a k < Q ^ (-(ε / 2)) := by simpa [hE] using hk
          exact mul_le_mul_of_nonneg_left ((hx k).trans hlt.le) (abs_nonneg _)
      calc |((y E ⬝ᵥ x : ℤ) : ℝ)| = |L.det|⁻¹ * (|L.det| * |((y E ⬝ᵥ x : ℤ) : ℝ)|) := by
            rw [inv_mul_cancel_left₀ hdetpos.ne']
        _ ≤ |L.det|⁻¹ * ((∑ k, |adjForm L (y E) k|) * Q ^ (-(ε / 2))) :=
            mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hdetpos.le)
        _ = (|L.det|⁻¹ * ∑ k, |adjForm L (y E) k|) * Q ^ (-(ε / 2)) := by ring
        _ ≤ B * Q ^ (-(ε / 2)) := mul_le_mul_of_nonneg_right hBE hQneg0
    have hCb2 : 0 ≤ Cb ^ 2 := sq_nonneg _
    by_cases hBQ : B < Q ^ (ε / 2)
    · have hzero : ∀ x ∈ box L a, y E ⬝ᵥ x = 0 := by
        intro x hx
        have h1 : |((y E ⬝ᵥ x : ℤ) : ℝ)| < 1 := by
          refine (hdot x hx).trans_lt ?_
          rw [Real.rpow_neg hQ0.le, ← div_eq_mul_inv, div_lt_one (Real.rpow_pos_of_pos hQ0 _)]
          exact hBQ
        have h2 : |y E ⬝ᵥ x| < 1 := by exact_mod_cast h1
        exact Int.abs_lt_one_iff.mp h2
      obtain ⟨μ, hμ⟩ := exists_eq_smul_of_finrank hrank hc hcbox hzero
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        exact hy0 (by simpa using hμ)
      have hcy : ‖c‖ ≤ ‖y E‖ := by
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ ?_
        refine le_trans ?_ (norm_le_pi_norm (y E) i)
        rw [hμ, Pi.smul_apply, smul_eq_mul, Int.norm_eq_abs, Int.norm_eq_abs, Int.cast_mul,
          abs_mul]
        have h1 : (1 : ℝ) ≤ |(μ : ℝ)| := by exact_mod_cast Int.one_le_abs hμ0
        exact le_mul_of_one_le_left (abs_nonneg _) h1
      linarith
    · push Not at hBQ
      have hQB : Q ≤ (B + 1) ^ (2 / ε) := by
        calc Q = (Q ^ (ε / 2)) ^ (2 / ε) := by
              rw [← Real.rpow_mul hQ0.le]
              have : ε / 2 * (2 / ε) = 1 := by field_simp
              rw [this, Real.rpow_one]
          _ ≤ (B + 1) ^ (2 / ε) :=
              Real.rpow_le_rpow (Real.rpow_nonneg hQ0.le _) (by linarith)
                (div_nonneg zero_le_two hε.le)
      have hfin : ‖c‖ ≤ Cb * (B + 1) ^ (2 / ε) :=
        hupper.trans (mul_le_mul_of_nonneg_left hQB hCb0.le)
      linarith

/-! ### Step 2: reduction to a bound for the height of the hyperplane -/

/-- If the integer points of `S` span a module of rank `n - 1`, then there is a primitive integer
vector orthogonal to `S`. -/
lemma exists_primitive_normal [DecidableEq ι] {S : Set (ι → ℤ)}
    (hS : Set.finrank ℤ S + 1 = Fintype.card ι) :
    ∃ c : ι → ℤ, Finset.univ.gcd c = 1 ∧ ∀ x ∈ S, c ⬝ᵥ x = 0 := by
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let b := Module.finBasis ℤ (Submodule.span ℤ S)
  set r := Module.finrank ℤ (Submodule.span ℤ S) with hr
  have hrS : Set.finrank ℤ S = r := rfl
  -- a nonzero rational vector orthogonal to the basis vectors
  let f : (ι → ℚ) →ₗ[ℚ] (Fin r → ℚ) :=
    { toFun := fun v i ↦ ∑ l, ((b i : ι → ℤ) l : ℚ) * v l
      map_add' := fun v w ↦ by
        ext i
        simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun q v ↦ by
        ext i
        simp [Finset.mul_sum, mul_left_comm] }
  have hker : LinearMap.ker f ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker] at hv
  -- clearing the denominators
  set N : ℤ := ∏ l, ((v l).den : ℤ) with hN
  have hN0 : N ≠ 0 := Finset.prod_ne_zero_iff.mpr fun l _ ↦ Nat.cast_ne_zero.mpr (v l).den_nz
  let w : ι → ℤ := fun l ↦ (v l).num * ∏ l' ∈ Finset.univ.erase l, ((v l').den : ℤ)
  have hw : ∀ l, (w l : ℚ) = N * v l := fun l ↦ by
    have h1 : N = (v l).den * ∏ l' ∈ Finset.univ.erase l, ((v l').den : ℤ) :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ l)).symm
    have h2 : v l * (v l).den = (v l).num := Rat.mul_den_eq_num (v l)
    have h3 : w l = (v l).num * ∏ l' ∈ Finset.univ.erase l, ((v l').den : ℤ) := rfl
    rw [h3, h1]
    push_cast
    rw [← h2]
    ring
  have hw0 : w ≠ 0 := by
    intro h0
    apply hv0
    funext l
    have h1 : (N : ℚ) * v l = 0 := by
      rw [← hw l, h0]
      simp
    exact (mul_eq_zero.mp h1).resolve_left (by exact_mod_cast hN0)
  have hwb : ∀ i, w ⬝ᵥ (b i : ι → ℤ) = 0 := fun i ↦ by
    have h1 : ∑ l, ((b i : ι → ℤ) l : ℚ) * v l = 0 := congrFun hv i
    have h2 : ((w ⬝ᵥ (b i : ι → ℤ) : ℤ) : ℚ) = N * ∑ l, ((b i : ι → ℤ) l : ℚ) * v l := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, hw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ ↦ by ring
    rw [h1, mul_zero] at h2
    exact_mod_cast h2
  have hwS : ∀ x ∈ S, w ⬝ᵥ x = 0 := by
    intro x hx
    let g : Submodule.span ℤ S →ₗ[ℤ] ℤ :=
      { toFun := fun u ↦ w ⬝ᵥ (u : ι → ℤ)
        map_add' := fun u u' ↦ by simp [dotProduct_add]
        map_smul' := fun q u ↦ by
          show w ⬝ᵥ ((q • u : Submodule.span ℤ S) : ι → ℤ) = q • (w ⬝ᵥ (u : ι → ℤ))
          rw [Submodule.coe_smul, dotProduct_smul] }
    have hg : g = 0 := b.ext fun i ↦ hwb i
    exact congrArg (fun g' : Submodule.span ℤ S →ₗ[ℤ] ℤ ↦ g' ⟨x, Submodule.subset_span hx⟩) hg
  -- dividing by the gcd
  obtain ⟨c, hc1, hc2⟩ := Finset.extract_gcd w (Finset.univ_nonempty (α := ι))
  have hg0 : Finset.univ.gcd w ≠ 0 := fun h0 ↦
    hw0 (funext fun l ↦ Finset.gcd_eq_zero_iff.mp h0 l (Finset.mem_univ l))
  refine ⟨c, hc2, fun x hx ↦ ?_⟩
  have h1 := hwS x hx
  have h2 : w ⬝ᵥ x = Finset.univ.gcd w * (c ⬝ᵥ x) := by
    simp only [dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [hc1 l (Finset.mem_univ l)]
      ring
  rw [h2] at h1
  exact (mul_eq_zero.mp h1).resolve_left hg0

/-- Rounding of the exponents: there is a finite set `E` of exponent tuples `e` with `|e_k| ≤ 2`
and `∑ e_k < -ε / 2` such that for every tuple `a` of positive reals with
`a₁ ⋯ aₙ < Q(a) ^ (-ε)` there is `e ∈ E` with `a_k ≤ Q(a) ^ e_k` for all `k`. -/
lemma exists_exponents [Nonempty ι] {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ E : Finset (ι → ℝ), (∀ e ∈ E, (∀ k, |e k| ≤ 2) ∧ ∑ k, e k < -(ε / 2)) ∧
      ∀ a : ι → ℝ, (∀ i, 0 < a i) → ∏ i, a i < size a ^ (-ε) →
        ∃ e ∈ E, ∀ k, a k ≤ size a ^ e k := by
  classical
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  set δ : ℝ := ε / (2 * n) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]
    linarith
  have hnδ : n * δ = ε / 2 := by
    rw [hδ]
    field_simp
  set N : ℤ := ⌈1 / δ⌉ with hN
  refine ⟨((Fintype.piFinset fun _ : ι ↦ Finset.Icc (-N) N).image
    fun z k ↦ δ * (z k : ℝ)).filter fun e ↦ (∀ k, |e k| ≤ 2) ∧ ∑ k, e k < -(ε / 2),
    fun e he ↦ (Finset.mem_filter.mp he).2, fun a ha hprod ↦ ?_⟩
  set Q := size a with hQ
  have hQ1 : 1 ≤ Q := one_le_size ha
  have hQ0 : 0 < Q := zero_lt_one.trans_le hQ1
  have hQgt : 1 < Q := by
    by_contra hle
    have hQeq : Q = 1 := le_antisymm (not_lt.mp hle) hQ1
    have h1 : ∀ i, a i = 1 := fun i ↦ by
      have h2 : a i ≤ 1 := hQeq ▸ le_size a i
      have h3 : (a i)⁻¹ ≤ 1 := hQeq ▸ inv_le_size a i
      exact le_antisymm h2 ((inv_le_one₀ (ha i)).mp h3)
    rw [hQeq, Real.one_rpow] at hprod
    simp [h1] at hprod
  have hlQ : 0 < Real.log Q := Real.log_pos hQgt
  set φ : ι → ℝ := fun k ↦ Real.log (a k) / Real.log Q with hφ
  have hφ1 : ∀ k, -1 ≤ φ k ∧ φ k ≤ 1 := fun k ↦ by
    constructor
    · have h1 := Real.log_le_log (inv_pos.mpr hQ0) (inv_size_le ha k)
      rw [Real.log_inv] at h1
      rw [hφ, le_div_iff₀ hlQ]
      linarith
    · rw [hφ, div_le_one hlQ]
      exact Real.log_le_log (ha k) (le_size a k)
  have hφsum : ∑ k, φ k < -ε := by
    have h1 : Real.log (∏ i, a i) < Real.log (Q ^ (-ε)) :=
      Real.log_lt_log (Finset.prod_pos fun i _ ↦ ha i) hprod
    rw [Real.log_prod (fun i _ ↦ (ha i).ne'), Real.log_rpow hQ0] at h1
    rw [hφ, ← Finset.sum_div, div_lt_iff₀ hlQ]
    exact h1
  set z : ι → ℤ := fun k ↦ ⌈φ k / δ⌉ with hz
  have hz1 : ∀ k, φ k ≤ δ * z k := fun k ↦ by
    have h1 := Int.le_ceil (φ k / δ)
    rw [div_le_iff₀ hδ0] at h1
    linarith
  have hz2 : ∀ k, δ * z k < φ k + δ := fun k ↦ by
    have h1 := Int.ceil_lt_add_one (φ k / δ)
    have h2 := mul_lt_mul_of_pos_left h1 hδ0
    have h3 : δ * (φ k / δ + 1) = φ k + δ := by
      field_simp
    rw [h3] at h2
    exact h2
  refine ⟨fun k ↦ δ * (z k : ℝ), Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨z,
    Fintype.mem_piFinset.mpr fun k ↦ Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩, fun k ↦ ?_, ?_⟩,
    fun k ↦ ?_⟩
  · have h1 : (1 : ℝ) / δ ≤ N := Int.le_ceil _
    have h2 : -(1 / δ) ≤ φ k / δ := by
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (hφ1 k).1 hδ0.le
    have h3 : φ k / δ ≤ z k := Int.le_ceil _
    have h4 : (-(N : ℝ)) ≤ z k := by linarith
    exact_mod_cast h4
  · exact Int.ceil_mono (div_le_div_of_nonneg_right (hφ1 k).2 hδ0.le)
  · exact abs_le.mpr ⟨by linarith [(hφ1 k).1, hz1 k], by linarith [(hφ1 k).2, hz2 k]⟩
  · calc ∑ k, δ * (z k : ℝ) < ∑ k, (φ k + δ) :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun k _ ↦ hz2 k
      _ = ∑ k, φ k + n * δ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ < -(ε / 2) := by
          rw [hnδ]
          linarith
  · have h1 : a k = Q ^ φ k := by
      have h2 : Real.log Q * φ k = Real.log (a k) := by
        rw [hφ]
        field_simp
      rw [Real.rpow_def_of_pos hQ0, h2, Real.exp_log (ha k)]
    calc a k = Q ^ φ k := h1
      _ ≤ Q ^ (δ * (z k : ℝ)) := Real.rpow_le_rpow_of_exponent_le hQ1 (hz1 k)

/-- If the integer points of `Π(a)` span a module of rank `n - 1` and `c ≠ 0` is orthogonal to
them, then there is an integer matrix `G` whose columns belong to `Π(a)` and span over `ℚ` the
hyperplane `c ⬝ x = 0`. -/
lemma exists_box_matrix [DecidableEq ι] (L : Matrix ι ι ℝ) {a : ι → ℝ} (ha : ∀ i, 0 < a i)
    (hrank : Set.finrank ℤ (box L a) + 1 = Fintype.card ι) {c : ι → ℤ} (hc : c ≠ 0)
    (hcbox : ∀ x ∈ box L a, c ⬝ᵥ x = 0) :
    ∃ G : Matrix ι ι ℤ, (∀ k, (fun i ↦ G i k) ∈ box L a) ∧
      ∀ x : ι → ℚ, ∑ k, (c k : ℚ) * x k = 0 → ∃ y : ι → ℚ, ∀ l, x l = ∑ k, (G l k : ℚ) * y k := by
  obtain ⟨k₀, -⟩ := Function.ne_iff.mp hc
  obtain ⟨T, hdet, hTk, hTS⟩ := exists_matrix_of_finrank hrank hc hcbox k₀
  refine ⟨Matrix.of fun i k ↦ if k = k₀ then 0 else T i k, fun k ↦ ?_, fun x hx ↦ ?_⟩
  · by_cases hk : k = k₀
    · have h1 : (fun i ↦ (Matrix.of fun i k ↦ if k = k₀ then 0 else T i k) i k) =
          (0 : ι → ℤ) := by
        funext i
        simp [hk]
      rw [h1]
      exact zero_mem_box fun i ↦ (ha i).le
    · have h1 : (fun i ↦ (Matrix.of fun i k ↦ if k = k₀ then 0 else T i k) i k) =
          fun i ↦ T i k := by
        funext i
        simp [hk]
      rw [h1]
      exact hTS k hk
  · set Tq : Matrix ι ι ℚ := T.map (Int.cast : ℤ → ℚ) with hTq
    have hdetq : Tq.det ≠ 0 := by
      rw [hTq, ← Int.cast_det]
      exact_mod_cast hdet
    set y : ι → ℚ := Tq⁻¹ *ᵥ x with hy
    have hTy : Tq *ᵥ y = x := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetq),
        Matrix.one_mulVec]
    have hxl : ∀ l, x l = ∑ k, (T l k : ℚ) * y k := fun l ↦ by
      have h1 := congrFun hTy l
      rw [← h1]
      simp [Matrix.mulVec, dotProduct, hTq]
    have hcol : ∀ k, k ≠ k₀ → ∑ l, (c l : ℚ) * (T l k : ℚ) = 0 := fun k hk ↦ by
      have h1 := hcbox _ (hTS k hk)
      have h2 : ((c ⬝ᵥ (fun i ↦ T i k) : ℤ) : ℚ) = 0 := by
        rw [h1]
        simp
      simpa [dotProduct] using h2
    have hy0 : y k₀ = 0 := by
      have h1 : ∑ l, (c l : ℚ) * x l = ∑ k, (∑ l, (c l : ℚ) * (T l k : ℚ)) * y k := by
        calc ∑ l, (c l : ℚ) * x l = ∑ l, ∑ k, (c l : ℚ) * (T l k : ℚ) * y k :=
              Finset.sum_congr rfl fun l _ ↦ by
                rw [hxl l, Finset.mul_sum]
                exact Finset.sum_congr rfl fun k _ ↦ by ring
          _ = ∑ k, (∑ l, (c l : ℚ) * (T l k : ℚ)) * y k := by
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun k _ ↦ (Finset.sum_mul _ _ _).symm
      rw [hx, Finset.sum_eq_single k₀ (fun k _ hk ↦ by rw [hcol k hk, zero_mul]) (by simp)] at h1
      have h2 : ∑ l, (c l : ℚ) * (T l k₀ : ℚ) ≠ 0 := by
        have h3 : ∑ l, (c l : ℚ) * (T l k₀ : ℚ) = ((c ⬝ᵥ c : ℤ) : ℚ) := by
          simp [dotProduct, hTk]
        rw [h3]
        exact_mod_cast (dotProduct_self_pos hc).ne'
      exact (mul_eq_zero.mp h1.symm).resolve_left h2
    refine ⟨y, fun l ↦ ?_⟩
    rw [hxl l]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    by_cases hk : k = k₀
    · simp [hk, hy0]
    · simp [hk]

/-- If the columns of `G` belong to `Π(a)` and `|z_k| ≤ B`, then `|L_i(G z)| ≤ n B a_i`. -/
lemma abs_eval_sum_le (L : Matrix ι ι ℝ) {a : ι → ℝ} {G : Matrix ι ι ℤ}
    (hG : ∀ k, (fun i ↦ G i k) ∈ box L a) {z : ι → ℤ} {B : ℝ} (hz : ∀ k, |(z k : ℝ)| ≤ B)
    (i : ι) : |eval L (fun l ↦ ∑ k, G l k * z k) i| ≤ Fintype.card ι * B * a i := by
  have h1 : eval L (fun l ↦ ∑ k, G l k * z k) i = ∑ k, (z k : ℝ) * eval L (fun l ↦ G l k) i := by
    simp only [eval_apply, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring
  rw [h1]
  calc |∑ k, (z k : ℝ) * eval L (fun l ↦ G l k) i|
      ≤ ∑ k, |(z k : ℝ) * eval L (fun l ↦ G l k) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : ι, B * a i := Finset.sum_le_sum fun k _ ↦ by
        rw [abs_mul]
        exact mul_le_mul (hz k) (hG k i) (abs_nonneg _) ((abs_nonneg _).trans (hz k))
    _ = Fintype.card ι * B * a i := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- A sequence of elements with property `p` along which `N` grows as fast as we want. -/
lemma exists_seq_of_unbounded {α : Type*} (p : α → Prop) (N F : α → ℝ) (K : ℝ)
    (h : ∀ H : ℝ, ∃ x, p x ∧ H < N x) :
    ∃ x : ℕ → α, (∀ h, p (x h)) ∧ (∀ h, K < N (x h)) ∧ ∀ h, F (x h) < N (x (h + 1)) := by
  choose g hg hgN using h
  let x : ℕ → α := fun n ↦ Nat.rec (g K) (fun _ y ↦ g (max K (F y))) n
  refine ⟨x, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ (le_max_right _ _).trans_lt (hgN _)⟩
  · cases h <;> exact hg _
  · cases h with
    | zero => exact hgN K
    | succ n => exact (le_max_left _ _).trans_lt (hgN _)

/-- The choice of the degrees: given positive real numbers `lam₁, …, lamₘ` and `σ > 0`, there are
positive integers `d₁, …, dₘ` and `Λ > 0` with `Λ ≤ d_h lam_h ≤ (1 + σ) Λ` for all `h`. -/
lemma exists_degrees {m : ℕ} (lam : Fin m → ℝ) (hlam : ∀ h, 0 < lam h) {σ : ℝ} (hσ : 0 < σ) :
    ∃ (d : Fin m → ℕ) (Λ : ℝ), 0 < Λ ∧
      ∀ h, 0 < d h ∧ Λ ≤ d h * lam h ∧ d h * lam h ≤ (1 + σ) * Λ := by
  set Λ : ℝ := (∑ h, lam h + 1) / σ with hΛ
  have hsum : 0 ≤ ∑ h, lam h := Finset.sum_nonneg fun h _ ↦ (hlam h).le
  have hΛ0 : 0 < Λ := div_pos (by linarith) hσ
  have hle : ∀ h, lam h ≤ σ * Λ := fun h ↦ by
    have h1 : σ * Λ = ∑ h, lam h + 1 := by
      rw [hΛ]
      field_simp
    have h2 := Finset.single_le_sum (f := lam) (fun h _ ↦ (hlam h).le) (Finset.mem_univ h)
    linarith
  refine ⟨fun h ↦ ⌈Λ / lam h⌉₊, Λ, hΛ0, fun h ↦
    ⟨Nat.ceil_pos.mpr (div_pos hΛ0 (hlam h)), ?_, ?_⟩⟩
  · have h1 := Nat.le_ceil (Λ / lam h)
    rwa [div_le_iff₀ (hlam h)] at h1
  · have h1 := Nat.ceil_lt_add_one (div_pos hΛ0 (hlam h)).le
    have h2 : (⌈Λ / lam h⌉₊ : ℝ) * lam h ≤ (Λ / lam h + 1) * lam h :=
      mul_le_mul_of_nonneg_right h1.le (hlam h).le
    rw [add_mul, div_mul_cancel₀ _ (hlam h).ne', one_mul] at h2
    linarith [hle h]

/-- The estimate for a monomial in the proof of Step 2. Let `e` be an exponent tuple with
`|e_k| ≤ 2` and `∑ e_k < -ε / 2`, let `Q_h > 1` and let `d_h` be positive integers with
`Λ ≤ d_h log Q_h ≤ (1 + σ) Λ`, where `42 n³ σ ≤ ε`. If `|U_{h k}| ≤ B Q_h ^ e_k` and `j` is a
multi-index with `∑ k, j_{h k} ≤ d_h` and `|∑ h, j_{h k} / d_h - m / n| ≤ 3 n m σ`, then
`|U ^ j| ≤ B ^ (d₁ + ⋯ + dₘ) exp (- (m / n) Λ ε / 6)`. -/
lemma prod_abs_pow_le [Nonempty ι] {ε σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσε : 42 * (Fintype.card ι : ℝ) ^ 3 * σ ≤ ε) (e : ι → ℝ) (he : ∀ k, |e k| ≤ 2)
    (hesum : ∑ k, e k < -(ε / 2)) {m : ℕ} {B : ℝ} (hB : 1 ≤ B) (Q : Fin m → ℝ)
    (hQ : ∀ h, 1 < Q h) (d : Fin m → ℕ) (hd : ∀ h, 0 < d h) {Λ : ℝ} (hΛ : 0 < Λ)
    (hdΛ : ∀ h, Λ ≤ d h * Real.log (Q h) ∧ d h * Real.log (Q h) ≤ (1 + σ) * Λ)
    (j : Fin m × ι →₀ ℕ) (hjdeg : ∀ h, ∑ k, j (h, k) ≤ d h)
    (hjβ : ∀ k, |∑ h, (j (h, k) : ℝ) / d h - m / Fintype.card ι| ≤
      3 * Fintype.card ι * m * σ)
    (U : Fin m × ι → ℝ) (hU : ∀ h k, |U (h, k)| ≤ B * Q h ^ e k) :
    ∏ p, |U p| ^ j p ≤
      B ^ (∑ h, d h) * Real.exp (-(m / Fintype.card ι * Λ * (ε / 6))) := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  set μ : ℝ := m / n with hμ
  have hμ0 : 0 ≤ μ := by positivity
  have hB0 : 0 < B := by linarith
  have hQ0 : ∀ h, 0 < Q h := fun h ↦ by linarith [hQ h]
  set t : ℝ := n ^ 2 * σ with ht
  have ht0 : 0 ≤ t := by positivity
  have hσt : σ ≤ t := by
    have h0 : 1 ≤ n ^ 2 := one_le_pow₀ hn1
    calc σ = 1 * σ := (one_mul _).symm
      _ ≤ n ^ 2 * σ := mul_le_mul_of_nonneg_right h0 hσ.le
  have hmn : (m : ℝ) = μ * n := by
    rw [hμ]
    field_simp
  -- step 1
  have h1 : ∏ p, |U p| ^ j p ≤ ∏ p : Fin m × ι, (B * Q p.1 ^ e p.2) ^ j p :=
    Finset.prod_le_prod₀ (fun p _ ↦ by positivity) fun p _ ↦
      pow_le_pow_left₀ (abs_nonneg _) (hU p.1 p.2) _
  -- step 2
  have h2 : ∏ p : Fin m × ι, (B * Q p.1 ^ e p.2) ^ j p = B ^ (∑ p, j p) *
      Real.exp (∑ k, e k * ∑ h, (j (h, k) : ℝ) * Real.log (Q h)) := by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Real.exp_sum]
    congr 1
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun h _ ↦ ?_
    rw [Real.rpow_def_of_pos (hQ0 h), ← Real.exp_nat_mul]
    congr 1
    ring
  have h3 : B ^ (∑ p, j p) ≤ B ^ (∑ h, d h) := by
    refine pow_le_pow_right₀ hB ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun h _ ↦ hjdeg h
  -- step 4
  have hS : ∀ k, |∑ h, (j (h, k) : ℝ) * Real.log (Q h) - Λ * μ| ≤ Λ * μ * (7 * t) := by
    intro k
    set s : ℝ := ∑ h, (j (h, k) : ℝ) / d h with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun h _ ↦ by positivity
    have hterm : ∀ h, (j (h, k) : ℝ) * Real.log (Q h) =
        (j (h, k) : ℝ) / d h * (d h * Real.log (Q h)) := fun h ↦ by
      have : (d h : ℝ) ≠ 0 := by exact_mod_cast (hd h).ne'
      field_simp
    have hlow : Λ * s ≤ ∑ h, (j (h, k) : ℝ) * Real.log (Q h) := by
      rw [hs, Finset.mul_sum]
      refine Finset.sum_le_sum fun h _ ↦ ?_
      rw [hterm, mul_comm]
      exact mul_le_mul_of_nonneg_left (hdΛ h).1 (by positivity)
    have hup : ∑ h, (j (h, k) : ℝ) * Real.log (Q h) ≤ (1 + σ) * Λ * s := by
      rw [hs, Finset.mul_sum]
      refine Finset.sum_le_sum fun h _ ↦ ?_
      rw [hterm, mul_comm ((1 + σ) * Λ)]
      exact mul_le_mul_of_nonneg_left (hdΛ h).2 (by positivity)
    have hβ := abs_le.mp (hjβ k)
    have e3 : 3 * n * (m : ℝ) * σ = μ * (3 * t) := by
      rw [hmn, ht]
      ring
    rw [e3] at hβ
    have hΛμ : 0 ≤ Λ * μ := by positivity
    have hprod : (1 + σ) * (1 + 3 * t) ≤ 1 + 7 * t := by
      nlinarith [mul_le_mul_of_nonneg_right hσ1 ht0]
    rw [abs_le]
    constructor
    · have : Λ * (μ - μ * (3 * t)) ≤ Λ * s := mul_le_mul_of_nonneg_left (by linarith) hΛ.le
      nlinarith
    · have h4 : (1 + σ) * Λ * s ≤ (1 + σ) * Λ * (μ + μ * (3 * t)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h5 : (1 + σ) * Λ * (μ + μ * (3 * t)) = Λ * μ * ((1 + σ) * (1 + 3 * t)) := by ring
      have h6 := mul_le_mul_of_nonneg_left hprod hΛμ
      linarith
  have h4 : ∑ k, e k * ∑ h, (j (h, k) : ℝ) * Real.log (Q h) ≤ -(μ * Λ * (ε / 6)) := by
    have hΛμ : 0 ≤ Λ * μ := by positivity
    have hk : ∀ k, e k * ∑ h, (j (h, k) : ℝ) * Real.log (Q h) ≤
        e k * (Λ * μ) + 2 * (Λ * μ * (7 * t)) := by
      intro k
      have h5 : e k * (∑ h, (j (h, k) : ℝ) * Real.log (Q h) - Λ * μ) ≤
          2 * (Λ * μ * (7 * t)) := by
        calc e k * (∑ h, (j (h, k) : ℝ) * Real.log (Q h) - Λ * μ)
            ≤ |e k * (∑ h, (j (h, k) : ℝ) * Real.log (Q h) - Λ * μ)| := le_abs_self _
          _ = |e k| * |∑ h, (j (h, k) : ℝ) * Real.log (Q h) - Λ * μ| := abs_mul _ _
          _ ≤ 2 * (Λ * μ * (7 * t)) :=
              mul_le_mul (he k) (hS k) (abs_nonneg _) zero_le_two
      linarith
    calc ∑ k, e k * ∑ h, (j (h, k) : ℝ) * Real.log (Q h)
        ≤ ∑ k, (e k * (Λ * μ) + 2 * (Λ * μ * (7 * t))) := Finset.sum_le_sum fun k _ ↦ hk k
      _ = (Λ * μ) * (∑ k, e k) + n * (2 * (Λ * μ * (7 * t))) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          ring
      _ ≤ (Λ * μ) * (-(ε / 2)) + (Λ * μ) * (ε / 3) := by
          have h6 : n * (2 * (Λ * μ * (7 * t))) = (Λ * μ) * (14 * n ^ 3 * σ) := by
            rw [ht]
            ring
          rw [h6]
          have h7 : 14 * n ^ 3 * σ ≤ ε / 3 := by linarith
          exact add_le_add (mul_le_mul_of_nonneg_left hesum.le hΛμ)
            (mul_le_mul_of_nonneg_left h7 hΛμ)
      _ = -(μ * Λ * (ε / 6)) := by ring
  calc ∏ p, |U p| ^ j p ≤ ∏ p : Fin m × ι, (B * Q p.1 ^ e p.2) ^ j p := h1
    _ = B ^ (∑ p, j p) * Real.exp (∑ k, e k * ∑ h, (j (h, k) : ℝ) * Real.log (Q h)) := h2
    _ ≤ B ^ (∑ h, d h) * Real.exp (-(μ * Λ * (ε / 6))) :=
        mul_le_mul h3 (Real.exp_le_exp.mpr h4) (Real.exp_pos _).le (by positivity)

/-- The final estimate in the proof of Step 2: under the assumptions of `prod_abs_pow_le`, if
`F` is a polynomial whose monomials `U ^ j` have degree at most `d_h` in the block `U_h` and
satisfy `|∑ h, j_{h k} / d_h - m / n| ≤ 3 n m σ`, whose coefficients are at most
`C₅ ^ (d₁ + ⋯ + dₘ)` in absolute value, and if `log Q_h` is large enough, then `|F(U)| < 1`. -/
lemma abs_eval_lt_one [Nonempty ι] {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσε : 42 * (Fintype.card ι : ℝ) ^ 3 * σ ≤ ε) (e : ι → ℝ) (he : ∀ k, |e k| ≤ 2)
    (hesum : ∑ k, e k < -(ε / 2)) {m : ℕ} (hm : 0 < m) {C₅ B : ℝ} (hC₅ : 1 ≤ C₅) (hB : 1 ≤ B)
    (Q : Fin m → ℝ) (hQ : ∀ h, 1 < Q h) (d : Fin m → ℕ) (hd : ∀ h, 0 < d h) {Λ lam : ℝ}
    (hΛ : 0 < Λ)
    (hlam : 12 * Fintype.card ι * Real.log (2 ^ Fintype.card ι * C₅ * B) / ε < lam)
    (hQlam : ∀ h, lam ≤ Real.log (Q h))
    (hdΛ : ∀ h, Λ ≤ d h * Real.log (Q h) ∧ d h * Real.log (Q h) ≤ (1 + σ) * Λ)
    (F : MvPolynomial (Fin m × ι) ℝ) (hFdeg : ∀ j ∈ F.support, ∀ h, ∑ k, j (h, k) ≤ d h)
    (hFcoeff : ∀ j, |F.coeff j| ≤ C₅ ^ (∑ h, d h))
    (hFβ : ∀ j, F.coeff j ≠ 0 → ∀ k, |∑ h, (j (h, k) : ℝ) / d h - m / Fintype.card ι| ≤
      3 * Fintype.card ι * m * σ)
    (U : Fin m × ι → ℝ) (hU : ∀ h k, |U (h, k)| ≤ B * Q h ^ e k) :
    |MvPolynomial.eval U F| < 1 := by
  set n : ℝ := (Fintype.card ι : ℝ) with hn
  have hn1 : 1 ≤ n := by
    rw [hn]
    exact_mod_cast Fintype.card_pos
  set A : ℝ := 2 ^ Fintype.card ι * C₅ * B with hA
  have hA1 : 1 ≤ A := by
    have h2 : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ one_le_two
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h2 hC₅) hB
  have hA0 : 0 < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hlam0 : 0 < lam := lt_of_le_of_lt (by positivity) hlam
  set D : ℕ := ∑ h, d h with hD
  set E : ℝ := Real.exp (-(m / n * Λ * (ε / 6))) with hE
  have hC₅0 : 0 < C₅ := by linarith
  have hB0 : 0 < B := by linarith
  have hmono : ∀ j ∈ F.support, |F.coeff j * ∏ p, U p ^ j p| ≤ C₅ ^ D * (B ^ D * E) := by
    intro j hj
    rw [abs_mul, Finset.abs_prod]
    simp_rw [abs_pow]
    exact mul_le_mul (hFcoeff j) (prod_abs_pow_le hσ hσ1 hσε e he hesum hB Q hQ d hd hΛ hdΛ j
      (hFdeg j hj) (hFβ j (MvPolynomial.mem_support_iff.mp hj)) U hU)
      (Finset.prod_nonneg fun p _ ↦ by positivity) (by positivity)
  have h1 := abs_eval_le_of_block F d hFdeg U (by positivity) hmono
  have h2 : (2 : ℝ) ^ (Fintype.card ι * ∑ h, d h) * (C₅ ^ D * (B ^ D * E)) = A ^ D * E := by
    rw [hA, mul_pow, mul_pow, ← pow_mul]
    ring
  rw [h2] at h1
  refine h1.trans_lt ?_
  have h3 : A ^ D = Real.exp (D * Real.log A) := by
    rw [Real.exp_nat_mul, Real.exp_log hA0]
  rw [h3, hE, ← Real.exp_add, Real.exp_lt_one_iff]
  have hDle : (D : ℝ) ≤ m * (2 * Λ / lam) := by
    rw [hD, Nat.cast_sum]
    calc ∑ h, (d h : ℝ) ≤ ∑ _h : Fin m, 2 * Λ / lam := Finset.sum_le_sum fun h _ ↦ by
          rw [le_div_iff₀ hlam0]
          have h4 : (d h : ℝ) * lam ≤ d h * Real.log (Q h) :=
            mul_le_mul_of_nonneg_left (hQlam h) (Nat.cast_nonneg _)
          have h5 := (hdΛ h).2
          nlinarith
      _ = m * (2 * Λ / lam) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have key : 2 * Real.log A / lam < ε / (6 * n) := by
    rw [div_lt_div_iff₀ hlam0 (by positivity)]
    have h6 : 12 * n * Real.log A < lam * ε := by rwa [div_lt_iff₀ hε] at hlam
    linarith
  have hmΛ : 0 < (m : ℝ) * Λ := by positivity
  calc (D : ℝ) * Real.log A + -(m / n * Λ * (ε / 6))
      ≤ m * (2 * Λ / lam) * Real.log A + -(m / n * Λ * (ε / 6)) := by
        have := mul_le_mul_of_nonneg_right hDle hlogA
        linarith
    _ = (m * Λ) * (2 * Real.log A / lam) - (m * Λ) * (ε / (6 * n)) := by
        field_simp
        ring
    _ < 0 := by
        have := mul_lt_mul_of_pos_left key hmΛ
        linarith

/-- The pairs `(a, c)` considered in the proof of Step 2: `a` is a tuple of positive real numbers
with `a₁ ⋯ aₙ < Q(a) ^ (-ε)` and `a_k ≤ Q(a) ^ e_k` such that the integer points of `Π(a)` span a
module of rank `n - 1`, and `c` is a primitive integer vector orthogonal to these points. -/
def IsGoodPair (L : Matrix ι ι ℝ) (ε : ℝ) (e : ι → ℝ) (x : (ι → ℝ) × (ι → ℤ)) : Prop :=
  (∀ i, 0 < x.1 i) ∧ ∏ i, x.1 i < size x.1 ^ (-ε) ∧
    Set.finrank ℤ (box L x.1) + 1 = Fintype.card ι ∧ (∀ k, x.1 k ≤ size x.1 ^ e k) ∧
    Finset.univ.gcd x.2 = 1 ∧ ∀ y ∈ box L x.1, x.2 ⬝ᵥ y = 0

/-- The heart of Step 2: for a fixed exponent tuple `e` with `∑ e_k < -ε / 2`, the heights of the
hyperplanes spanned by the integer points of the parallelepipeds `Π(a)` of rank `n - 1` with
`a₁ ⋯ aₙ < Q(a) ^ (-ε)` and `a_k ≤ Q(a) ^ e_k` are bounded. This is where Roth's lemma and the
polynomial theorem are used. -/
theorem norm_normal_le_of_exponents [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hn : 2 ≤ Fintype.card ι) (e : ι → ℝ) (he : ∀ k, |e k| ≤ 2) (hesum : ∑ k, e k < -(ε / 2)) :
    ∃ H : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) → ∏ i, a i < size a ^ (-ε) →
      Set.finrank ℤ (box L a) + 1 = Fintype.card ι → (∀ k, a k ≤ size a ^ e k) →
      ∀ c : ι → ℤ, Finset.univ.gcd c = 1 → (∀ x ∈ box L a, c ⬝ᵥ x = 0) → ‖c‖ ≤ H := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  set n : ℝ := (Fintype.card ι : ℝ) with hn_def
  have hn2 : (2 : ℝ) ≤ n := by
    rw [hn_def]
    exact_mod_cast hn
  have hn12 : 0 < (n - 1) ^ 2 := by
    have : 0 < n - 1 := by linarith
    positivity
  -- the constants
  obtain ⟨C₇, C₈, C₉, hC₈, hC₉, hsize⟩ := size_rpow_le_norm_normal L hL halg hε
  set σ : ℝ := ε / (42 * n ^ 3) with hσ_def
  have hn3 : (8 : ℝ) ≤ n ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hn2 3
    norm_num at this
    exact this
  have hσ : 0 < σ := by positivity
  have hσε : 42 * n ^ 3 * σ ≤ ε := by
    rw [hσ_def]
    field_simp
    exact le_refl _
  have hσ1 : σ < 1 := by
    rw [hσ_def, div_lt_one (by positivity)]
    linarith
  obtain ⟨C₄, hpoly⟩ := polynomial_theorem L hL halg hσ
  set m : ℕ := ⌊C₄⌋₊ + 1 with hm_def
  have hmC : C₄ < m := by
    rw [hm_def]
    push_cast
    exact Nat.lt_floor_add_one C₄
  have hm0 : 0 < m := Nat.succ_pos _
  have : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨C₅, hC₅, hpoly⟩ := hpoly m hmC
  obtain ⟨C₁, C₂, C₃, hC₁, hC₂, hC₃, hroth⟩ := generalized_roth_lemma ι hn m hσ hσ1
  set γ : ℝ := min 1 (C₈ / (2 * C₉)) with hγ_def
  have hγ0 : 0 < γ := lt_min one_pos (by positivity)
  have hγ1 : γ ≤ n - 1 := (min_le_left _ _).trans (by linarith)
  have hγC : γ * (2 * C₉) ≤ C₈ := by
    have h1 : γ ≤ C₈ / (2 * C₉) := min_le_right _ _
    rwa [le_div_iff₀ (by positivity)] at h1
  set B : ℝ := n ^ 2 / σ with hB_def
  have hB1 : 1 ≤ B := by
    rw [hB_def, one_le_div hσ]
    nlinarith
  set A : ℝ := 2 ^ Fintype.card ι * C₅ * B with hA_def
  have hA1 : 1 ≤ A := by
    have h2 : (1 : ℝ) ≤ 2 ^ Fintype.card ι := one_le_pow₀ one_le_two
    have h3 : 1 ≤ 2 ^ Fintype.card ι * C₅ := one_le_mul_of_one_le_of_one_le h2 hC₅
    exact one_le_mul_of_one_le_of_one_le h3 hB1
  have hC₅0 : 0 < C₅ := by linarith
  have hlogC₅ : 0 ≤ Real.log C₅ := Real.log_nonneg hC₅
  set lam : ℝ := max (12 * n * Real.log A / ε)
    (2 * m * Real.log C₅ * (n - 1) ^ 2 / (C₈ * C₃ * γ)) + 1 with hlam_def
  have hlamA : 12 * n * Real.log A / ε < lam := by
    rw [hlam_def]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  have hlamC : 2 * m * Real.log C₅ * (n - 1) ^ 2 / (C₈ * C₃ * γ) < lam := by
    rw [hlam_def]
    exact (le_max_right _ _).trans_lt (lt_add_one _)
  have hlam0 : 0 < lam := by
    have h1 : 0 ≤ 12 * n * Real.log A / ε := by
      have := Real.log_nonneg hA1
      positivity
    linarith
  set C₁' : ℝ := max C₁ 1 with hC₁'_def
  have hC₁' : 1 ≤ C₁' := le_max_right _ _
  set K : ℝ := max C₇ (max (C₂ ^ ((n - 1) ^ 2 / γ)) (Real.exp (lam * C₉))) with hK_def
  -- the argument by contradiction
  by_contra hcon
  have hunb : ∀ H : ℝ, ∃ x, IsGoodPair L ε e x ∧ H < ‖x.2‖ := by
    intro H
    by_contra h
    refine hcon ⟨H, fun a ha hprod hrank hea c hc hcbox ↦ ?_⟩
    by_contra hlt
    exact h ⟨(a, c), ⟨ha, hprod, hrank, hea, hc, hcbox⟩, not_le.mp hlt⟩
  obtain ⟨xs, hxs, hxK, hxF⟩ := exists_seq_of_unbounded (IsGoodPair L ε e) (fun x ↦ ‖x.2‖)
    (fun x ↦ size x.1 ^ (2 * C₁' * C₉)) K hunb
  set a : Fin m → ι → ℝ := fun h ↦ (xs h).1 with ha_def
  set c : Fin m → ι → ℤ := fun h ↦ (xs h).2 with hc_def
  set Q : Fin m → ℝ := fun h ↦ size (a h) with hQ_def
  have hapos : ∀ h i, 0 < a h i := fun h ↦ (hxs h).1
  have hQ1 : ∀ h, 1 ≤ Q h := fun h ↦ one_le_size (hapos h)
  have hQ0 : ∀ h, 0 < Q h := fun h ↦ zero_lt_one.trans_le (hQ1 h)
  have hcK : ∀ h, K < ‖c h‖ := fun h ↦ hxK h
  have hnorm : ∀ h, Q h ^ C₈ ≤ ‖c h‖ ∧ ‖c h‖ ≤ Q h ^ C₉ := fun h ↦ by
    obtain ⟨h1, h2, h3, -, h5, h6⟩ := hxs h
    exact hsize _ h1 h2 h3 _ h5 h6 ((le_max_left _ _).trans (hcK h).le)
  have hrpow : ∀ h (t : ℝ), Q h ^ t = Real.exp (Real.log (Q h) * t) := fun h t ↦
    Real.rpow_def_of_pos (hQ0 h) t
  have hlamQ : ∀ h, lam < Real.log (Q h) := fun h ↦ by
    have h1 : Real.exp (lam * C₉) < Q h ^ C₉ :=
      ((le_max_right _ _).trans (le_max_right _ _)).trans_lt ((hcK h).trans_le (hnorm h).2)
    rw [hrpow, Real.exp_lt_exp] at h1
    exact lt_of_mul_lt_mul_right h1 hC₉.le
  set lq : Fin m → ℝ := fun h ↦ Real.log (Q h) with hlq_def
  have hlq0 : ∀ h, 0 < lq h := fun h ↦ hlam0.trans (hlamQ h)
  have hQgt : ∀ h, 1 < Q h := fun h ↦ by
    by_contra hle
    have h1 : Q h = 1 := le_antisymm (not_lt.mp hle) (hQ1 h)
    have h0 : 0 < Real.log (Q h) := hlq0 h
    rw [h1, Real.log_one] at h0
    exact lt_irrefl _ h0
  have hstep : ∀ h h' : Fin m, (h : ℕ) + 1 = h' → 2 * C₁' * lq h ≤ lq h' := by
    intro h h' hh'
    have h1 : Q h ^ (2 * C₁' * C₉) < ‖c h'‖ := by
      have h2 : size (xs h).1 ^ (2 * C₁' * C₉) < ‖(xs ((h : ℕ) + 1)).2‖ := hxF h
      rw [hh'] at h2
      exact h2
    have h3 := h1.trans_le (hnorm h').2
    rw [hrpow, hrpow, Real.exp_lt_exp] at h3
    have h4 : 2 * C₁' * lq h * C₉ < lq h' * C₉ := by
      calc 2 * C₁' * lq h * C₉ = Real.log (Q h) * (2 * C₁' * C₉) := by ring
        _ < lq h' * C₉ := h3
    exact (lt_of_mul_lt_mul_right h4 hC₉.le).le
  -- the degrees and the auxiliary polynomial
  obtain ⟨d, Λ, hΛ, hd⟩ := exists_degrees lq hlq0 hσ
  have hd0 : ∀ h, 0 < d h := fun h ↦ (hd h).1
  have hdΛ : ∀ h, Λ ≤ d h * lq h ∧ d h * lq h ≤ (1 + σ) * Λ := fun h ↦ (hd h).2
  have hdΛ2 : ∀ h, d h * lq h ≤ 2 * Λ := fun h ↦ (hdΛ h).2.trans (by nlinarith)
  obtain ⟨P, hP0, hPhom, hPht, hPi⟩ := hpoly d hd0
  have hDle : ((∑ h, d h : ℕ) : ℝ) * lam ≤ 2 * m * Λ := by
    rw [Nat.cast_sum, Finset.sum_mul]
    calc ∑ h, (d h : ℝ) * lam ≤ ∑ _h : Fin m, 2 * Λ := Finset.sum_le_sum fun h _ ↦
          (mul_le_mul_of_nonneg_left (hlamQ h).le (Nat.cast_nonneg _)).trans (hdΛ2 h)
      _ = 2 * m * Λ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- the hypotheses of Roth's lemma
  have hr1 : ∀ h h' : Fin m, (h : ℕ) + 1 = h' → C₁ * d h' ≤ d h := by
    intro h h' hh'
    have h4 : C₁' * d h' * (2 * lq h) ≤ d h * (2 * lq h) := by
      calc C₁' * d h' * (2 * lq h) = d h' * (2 * C₁' * lq h) := by ring
        _ ≤ d h' * lq h' := mul_le_mul_of_nonneg_left (hstep h h' hh') (Nat.cast_nonneg _)
        _ ≤ 2 * Λ := hdΛ2 h'
        _ ≤ d h * (2 * lq h) := by linarith [(hdΛ h).1]
    have h5 := le_of_mul_le_mul_right h4 (by linarith [hlq0 h])
    calc C₁ * d h' ≤ C₁' * d h' := mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _)
      _ ≤ d h := h5
  have hgcd : ∀ h, Finset.univ.gcd (c h) = 1 := fun h ↦ (hxs h).2.2.2.2.1
  have hr2 : ∀ h : Fin m, h ≠ 0 → ‖c 0‖ ^ (γ * d 0) ≤ ‖c h‖ ^ (d h : ℝ) := by
    intro h _
    calc ‖c 0‖ ^ (γ * d 0) ≤ (Q 0 ^ C₉) ^ (γ * d 0) :=
          Real.rpow_le_rpow (norm_nonneg _) (hnorm 0).2 (by positivity)
      _ = Real.exp (lq 0 * (C₉ * (γ * d 0))) := by
          rw [← Real.rpow_mul (hQ0 0).le, hrpow]
      _ ≤ Real.exp (lq h * (C₈ * d h)) := by
          rw [Real.exp_le_exp]
          have h1 := hdΛ2 0
          have h2 := (hdΛ h).1
          calc lq 0 * (C₉ * (γ * d 0)) = (d 0 * lq 0) * (γ * C₉) := by ring
            _ ≤ (2 * Λ) * (γ * C₉) := mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = Λ * (γ * (2 * C₉)) := by ring
            _ ≤ Λ * C₈ := mul_le_mul_of_nonneg_left hγC hΛ.le
            _ ≤ (d h * lq h) * C₈ := mul_le_mul_of_nonneg_right h2 hC₈.le
            _ = lq h * (C₈ * d h) := by ring
      _ = (Q h ^ C₈) ^ (d h : ℝ) := by
          rw [← Real.rpow_mul (hQ0 h).le, hrpow]
      _ ≤ ‖c h‖ ^ (d h : ℝ) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (hQ0 h).le _) (hnorm h).1 (Nat.cast_nonneg _)
  have hr3 : ∀ h, C₂ ^ ((n - 1) ^ 2 / γ) ≤ ‖c h‖ := fun h ↦
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hcK h).le
  have hr4 : (height P : ℝ) ≤ ‖c 0‖ ^ (C₃ * γ * d 0 / (n - 1) ^ 2) := by
    have hkey : ((∑ h, d h : ℕ) : ℝ) * Real.log C₅ ≤
        lq 0 * (C₈ * (C₃ * γ * d 0 / (n - 1) ^ 2)) := by
      have e1 : lq 0 * (C₈ * (C₃ * γ * d 0 / (n - 1) ^ 2)) =
          d 0 * lq 0 * (C₈ * C₃ * γ) / (n - 1) ^ 2 := by ring
      rw [e1, le_div_iff₀ hn12]
      have hlamC' : 2 * m * Real.log C₅ * (n - 1) ^ 2 < lam * (C₈ * C₃ * γ) := by
        rwa [div_lt_iff₀ (by positivity)] at hlamC
      have h0 : 0 ≤ (d 0 : ℝ) * lq 0 := mul_nonneg (Nat.cast_nonneg _) (hlq0 0).le
      have e2 : ((∑ h, d h : ℕ) : ℝ) * Real.log C₅ * (n - 1) ^ 2 * lam ≤
          d 0 * lq 0 * (C₈ * C₃ * γ) * lam := by
        calc ((∑ h, d h : ℕ) : ℝ) * Real.log C₅ * (n - 1) ^ 2 * lam
            = (((∑ h, d h : ℕ) : ℝ) * lam) * (Real.log C₅ * (n - 1) ^ 2) := by ring
          _ ≤ (2 * m * Λ) * (Real.log C₅ * (n - 1) ^ 2) :=
              mul_le_mul_of_nonneg_right hDle (by positivity)
          _ ≤ (2 * m * (d 0 * lq 0)) * (Real.log C₅ * (n - 1) ^ 2) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              exact mul_le_mul_of_nonneg_left (hdΛ 0).1 (by positivity)
          _ = (d 0 * lq 0) * (2 * m * Real.log C₅ * (n - 1) ^ 2) := by ring
          _ ≤ (d 0 * lq 0) * (lam * (C₈ * C₃ * γ)) := mul_le_mul_of_nonneg_left hlamC'.le h0
          _ = d 0 * lq 0 * (C₈ * C₃ * γ) * lam := by ring
      exact le_of_mul_le_mul_right e2 hlam0
    calc (height P : ℝ) ≤ C₅ ^ (∑ h, d h) := hPht
      _ = Real.exp ((∑ h, d h : ℕ) * Real.log C₅) := by
          rw [Real.exp_nat_mul, Real.exp_log hC₅0]
      _ ≤ Real.exp (lq 0 * (C₈ * (C₃ * γ * d 0 / (n - 1) ^ 2))) := Real.exp_le_exp.mpr hkey
      _ = (Q 0 ^ C₈) ^ (C₃ * γ * d 0 / (n - 1) ^ 2) := by
          rw [← Real.rpow_mul (hQ0 0).le, hrpow]
      _ ≤ ‖c 0‖ ^ (C₃ * γ * d 0 / (n - 1) ^ 2) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (hQ0 0).le _) (hnorm 0).1 (by positivity)
  obtain ⟨x, hx, i, hi, hxi⟩ := hroth γ hγ0 hγ1 d hd0 hr1 c hgcd hr2 hr3 P hP0 hPhom hr4
  -- an integer point at which a divided derivative of small order does not vanish
  have hG : ∀ h, ∃ G : Matrix ι ι ℤ, (∀ k, (fun i ↦ G i k) ∈ box L (a h)) ∧
      ∀ x : ι → ℚ, ∑ k, (c h k : ℚ) * x k = 0 →
        ∃ y : ι → ℚ, ∀ l, x l = ∑ k, (G l k : ℚ) * y k := fun h ↦
    exists_box_matrix L (hapos h) (hxs h).2.2.1 (ne_zero_of_gcd_eq_one (hgcd h))
      (hxs h).2.2.2.2.2
  choose G hGbox hGspan using hG
  choose y hy using fun h ↦ hGspan h (x h) (hx h)
  have hxi' : MvPolynomial.eval
      (fun p : Fin m × ι ↦ ∑ k, (G p.1 p.2 k : ℚ) * (fun q : Fin m × ι ↦ y q.1 q.2) (p.1, k))
      (MvPolynomial.map (Int.castRingHom ℚ) (hasseDeriv i P)) ≠ 0 := by
    have h1 : (fun p : Fin m × ι ↦ x p.1 p.2) =
        fun p ↦ ∑ k, (G p.1 p.2 k : ℚ) * y p.1 k := funext fun p ↦ hy p.1 p.2
    rwa [h1] at hxi
  obtain ⟨z, i', hz, hi', hzne⟩ := exists_int_point P d hd0 hPhom G i
    (fun q : Fin m × ι ↦ y q.1 q.2) hxi' (B := n / σ) (by positivity)
  have hi'2 : blockWeight d i' < 2 * m * σ := by
    have h1 : (Fintype.card ι : ℝ) / (n / σ) = σ := by
      rw [← hn_def]
      field_simp
    rw [h1] at hi'
    linarith
  set x' : Fin m → ι → ℤ := fun h l ↦ ∑ k, G h l k * z (h, k) with hx'_def
  obtain ⟨hα, hβ⟩ := hPi i'
  set F : MvPolynomial (Fin m × ι) ℝ := linExpand L (hasseDeriv i' P) with hF_def
  set U : Fin m × ι → ℝ := fun p ↦ eval L (x' p.1) p.2 with hU_def
  have hUF : MvPolynomial.eval U F =
      ((MvPolynomial.eval (fun p : Fin m × ι ↦ x' p.1 p.2) (hasseDeriv i' P) : ℤ) : ℝ) :=
    eval_linExpand L hL _ x'
  have hge : 1 ≤ |MvPolynomial.eval U F| := by
    rw [hUF, ← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hzne
  have hFdeg : ∀ j ∈ F.support, ∀ h, ∑ k, j (h, k) ≤ d h := by
    intro j hj h
    have h1 := ((hPhom.hasseDeriv i').aeval_blockLin (A := ℝ) fun _ ↦ L⁻¹).sum_eq
      (MvPolynomial.mem_support_iff.mp hj) h
    rw [h1]
    exact Nat.sub_le _ _
  have hU : ∀ h k, |U (h, k)| ≤ B * Q h ^ e k := by
    intro h k
    have h1 := abs_eval_sum_le L (hGbox h) (z := fun k' ↦ z (h, k')) (B := n / σ)
      (fun k' ↦ hz (h, k')) k
    have h2 : (Fintype.card ι : ℝ) * (n / σ) = B := by
      rw [hB_def, ← hn_def]
      ring
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left ((hxs h).2.2.2.1 k) (by linarith))
  have hlt : |MvPolynomial.eval U F| < 1 :=
    abs_eval_lt_one hε hσ hσ1.le hσε e he hesum hm0 hC₅ hB1 Q hQgt d hd0 hΛ hlamA
      (fun h ↦ (hlamQ h).le) hdΛ F hFdeg hα (hβ hi'2) U hU
  linarith

/-- The heights of the hyperplanes spanned by the integer points of the parallelepipeds `Π(a)` of
rank `n - 1` with `a₁ ⋯ aₙ < Q(a) ^ (-ε)` are bounded. -/
theorem norm_normal_le [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) → ∏ i, a i < size a ^ (-ε) →
      Set.finrank ℤ (box L a) + 1 = Fintype.card ι →
      ∀ c : ι → ℤ, Finset.univ.gcd c = 1 → (∀ x ∈ box L a, c ⬝ᵥ x = 0) → ‖c‖ ≤ H := by
  classical
  by_cases hn : 2 ≤ Fintype.card ι
  · have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
    have hε' : 0 < min ε 1 := lt_min hε one_pos
    obtain ⟨E, hE, hEa⟩ := exists_exponents (ι := ι) hε' (min_le_right _ _)
    have key : ∀ e, e ∈ E → ∃ H : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) →
        ∏ i, a i < size a ^ (-(min ε 1)) →
        Set.finrank ℤ (box L a) + 1 = Fintype.card ι → (∀ k, a k ≤ size a ^ e k) →
        ∀ c : ι → ℤ, Finset.univ.gcd c = 1 → (∀ x ∈ box L a, c ⬝ᵥ x = 0) → ‖c‖ ≤ H :=
      fun e heE ↦ norm_normal_le_of_exponents L hL halg hε' (min_le_right _ _) hn e (hE e heE).1
        (hE e heE).2
    choose! Hf hHf using key
    obtain ⟨M, hM⟩ := (E.image Hf).exists_le
    refine ⟨M, fun a ha hprod hrank c hc hcbox ↦ ?_⟩
    have hprod' : ∏ i, a i < size a ^ (-(min ε 1)) :=
      hprod.trans_le (Real.rpow_le_rpow_of_exponent_le (one_le_size ha)
        (neg_le_neg (min_le_left _ _)))
    obtain ⟨e, heE, hea⟩ := hEa a ha hprod'
    exact (hHf e heE a ha hprod' hrank hea c hc hcbox).trans
      (hM _ (Finset.mem_image_of_mem _ heE))
  · refine ⟨1, fun a _ _ _ c hc _ ↦ ?_⟩
    have : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp (by omega)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i ↦ ?_
    have huniv : (Finset.univ : Finset ι) = {i} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, fun j _ ↦ Subsingleton.elim j i⟩
    rw [huniv, Finset.gcd_singleton, ← Int.abs_eq_normalize] at hc
    rw [Int.norm_eq_abs]
    exact_mod_cast hc.le

/-- **Step 2** ([evertse1993], Theorem 3.2.1 for parallelepipeds of rank `n - 1`). Let
`L₁, …, Lₙ` be linearly independent linear forms with real algebraic coefficients and let `ε > 0`.
There are finitely many hyperplanes `T₁, …, Tₜ` of `ℚⁿ` such that, for every tuple `a` of positive
real numbers with `a₁ ⋯ aₙ < Q(a) ^ (-ε)` and `Q(a)` large enough for which the integer points of
`Π(a)` span a module of rank `n - 1`, the integer points of `Π(a)` lie in one of `T₁, …, Tₜ`. -/
theorem parallelepiped_theorem_of_rank [DecidableEq ι] (L : Matrix ι ι ℝ) (hL : L.det ≠ 0)
    (halg : ∀ i j, IsAlgebraic ℚ (L i j)) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (ι → ℤ), (∀ c ∈ T, c ≠ 0) ∧ ∃ Q₀ : ℝ, ∀ a : ι → ℝ, (∀ i, 0 < a i) →
      ∏ i, a i < size a ^ (-ε) → Q₀ ≤ size a → Set.finrank ℤ (box L a) + 1 = Fintype.card ι →
      ∃ c ∈ T, ∀ x ∈ box L a, c ⬝ᵥ x = 0 := by
  classical
  obtain ⟨H, hH⟩ := norm_normal_le L hL halg hε
  refine ⟨(Fintype.piFinset fun _ : ι ↦ Finset.Icc (-⌊H⌋) ⌊H⌋).filter (· ≠ 0), fun c hc ↦
    (Finset.mem_filter.mp hc).2, 0, fun a ha hprod _ hrank ↦ ?_⟩
  obtain ⟨c, hc, hcbox⟩ := exists_primitive_normal hrank
  refine ⟨c, Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun i ↦ ?_,
    ne_zero_of_gcd_eq_one hc⟩, hcbox⟩
  have h1 : |(c i : ℝ)| ≤ H := by
    rw [← Int.norm_eq_abs]
    exact (norm_le_pi_norm c i).trans (hH a ha hprod hrank c hc hcbox)
  rw [abs_le] at h1
  rw [Finset.mem_Icc]
  refine ⟨?_, Int.le_floor.mpr h1.2⟩
  have h2 : -c i ≤ ⌊H⌋ := Int.le_floor.mpr (by push_cast; linarith)
  linarith

end Schmidt
